namespace LeanSudo.Nsswitch

/-!
The sudoers source gate, checked before opening any sudoers policy file.

Syntax follows sudo 1.9.17p2's plugins/sudoers/sudo_nss.c and
lib/util/parseln.c: the first case-insensitive `sudoers:` logical line wins;
comments, space/tab trimming, CRLF and single-backslash continuations are
handled before space/tab tokenization. Only `[SUCCESS=return]` and
`[NOTFOUND=return]` are action tokens upstream. They cannot change the result
with the sole supported backend, files (duplicate files entries are ignored
upstream). Other action syntax is refused rather than interpreted as a source
or silently discarded. Every source is checked, even after a return action.

No sudoers line (including a missing nsswitch.conf supplied as empty text)
defaults to files. Unlike upstream's fallback when *no recognized backend*
remains, an explicit line without files is refused. Unsupported sources must
never cause the local policy to be consulted instead of the configured one.
Diagnostics omit the `sudo: ` prefix, which belongs to the IO shell.
-/

private def blank (c : Char) : Bool := c == ' ' || c == '\t'

private def trimStart (s : String) : String :=
  String.ofList (s.toList.dropWhile blank)

private def trimEnd (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile blank).reverse)

private def physicalLine (s : String) : String × Bool := Id.run do
  let s := String.ofList ((s.toList.reverse.dropWhile (· == '\r')).reverse)
  let pieces := s.splitOn "#"
  let body := pieces.headD ""
  let continued := pieces.length == 1 && body.endsWith "\\" && !body.endsWith "\\\\"
  let body := if continued then String.ofList (body.toList.dropLast) else trimEnd body
  return (trimStart body, continued)

private def joinLines : List String → String → List String
  | [], pending => if pending.isEmpty then [] else [pending]
  | line :: rest, pending =>
    let (body, continued) := physicalLine line
    if continued then joinLines rest (pending ++ body)
    else (pending ++ body) :: joinLines rest ""

/-- Normalized source tokens. Recognized actions are not sources. Unknown action
clauses are diagnosed separately; in particular they never swallow later sources. -/
private def sourceTokens : List String → Except String (List String)
  | [] => .ok []
  | token :: rest => do
    let token := token.toLower
    if token == "[success=return]" || token == "[notfound=return]" then
      sourceTokens rest
    else if token.startsWith "[" || token.endsWith "]" then
      throw ("/etc/nsswitch.conf: unsupported sudoers action: " ++ token)
    else
      return token :: (← sourceTokens rest)

private def firstEntry : List String → Except String (List String)
  | [] => .ok ["files"]
  | line :: rest =>
    if line.toLower.startsWith "sudoers:" then
      sourceTokens ((String.ofList (line.toList.drop 8)).splitOn " "
        |>.flatMap (·.splitOn "\t") |>.filter (!·.isEmpty))
    else firstEntry rest

/-- Parse the first sudoers entry, preserving every configured source. The
absence of an entry is distinct from an explicit entry with no sources. -/
def parse (text : String) : Except String (List String) :=
  if text.toList.contains '\x00' then
    .error "/etc/nsswitch.conf: invalid NUL in configuration"
  else firstEntry (joinLines (text.splitOn "\n") "")

private def checkSources : List String → Except String Unit
  | [] => .ok ()
  | source :: rest =>
    if source = "files" then checkSources rest
    else .error ("/etc/nsswitch.conf: unsupported sudoers source: " ++ source)

/-- Approval requires an explicitly present files backend, and nothing else. -/
def approveSources : List String → Except String Unit
  | [] => .error "/etc/nsswitch.conf: sudoers entry has no files source"
  | source :: rest => checkSources (source :: rest)

/-- The shell must call this before Sudoers.load, and must not load policy after
an error. Only a missing nsswitch.conf may be supplied as empty text; other IO
errors must not silently select the files backend. -/
def approve (text : String) : Except String Unit := do
  approveSources (← parse text)

private theorem checkSources_supported_only (sources : List String)
    (h : checkSources sources = .ok ()) :
    ∀ source ∈ sources, source = "files" := by
  induction sources with
  | nil => simp
  | cons source rest ih =>
    by_cases hs : source = "files"
    · have hr : checkSources rest = .ok () := by
        simpa [checkSources, hs] using h
      intro candidate hc
      rcases List.mem_cons.mp hc with hc | hc
      · exact hc.trans hs
      · exact ih hr candidate hc
    · simp [checkSources, hs] at h

/-- Approval cannot silently ignore a configured backend or approve an empty
source list. This is the condition needed before consulting local sudoers. -/
theorem approveSources_supported_only (sources : List String)
    (h : approveSources sources = .ok ()) :
    sources ≠ [] ∧ ∀ source ∈ sources, source = "files" := by
  cases sources with
  | nil => simp [approveSources] at h
  | cons source rest =>
    exact ⟨by simp, checkSources_supported_only _ h⟩

/-- End-to-end source safety: successful textual approval implies that every
parsed backend is files and at least one backend exists. -/
theorem approve_supported_only (text : String) (sources : List String)
    (parsed : parse text = .ok sources) (h : approve text = .ok ()) :
    sources ≠ [] ∧ ∀ source ∈ sources, source = "files" := by
  unfold approve at h
  rw [parsed] at h
  exact approveSources_supported_only sources h

end LeanSudo.Nsswitch
