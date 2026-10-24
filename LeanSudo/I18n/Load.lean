import LeanSudo.I18n
import LeanSudo.I18n.Render
import LeanSudo.Sys.Core

/-! Gettext's IO boundary. Catalogs and locale data are accepted only beneath
root-owned, non-writable directories. No user-selected path is opened as root. -/
namespace LeanSudo.I18n

structure Catalogs where
  sudo : Catalog := {}
  sudoers : Catalog := {}
  diagnostics : Catalog := {}
  frontend : Catalog := {}
  deriving Inhabited

private def safeName (s : String) : Bool :=
  !s.isEmpty && s != "." && s != ".." &&
    s.toList.all (fun c => c.isAlphanum || "_-.@".contains c)

/-- Resolve first, then validate every ancestor of the path actually opened.
An unprivileged process cannot replace either that file or any directory in its
path between validation and opening. Symlinks in the original spelling cannot
redirect the subsequent read. -/
private def trustedPath (path : String) : IO (Option String) := do
  let some path ← Sys.realpath path | return none
  if !path.startsWith "/" then return none
  let some root ← Sys.lstat "/" | return none
  if root.uid != 0 || root.mode &&& 0o022 != 0 || !root.isDir then return none
  let mut current := ""
  for part in path.splitOn "/" do
    if !part.isEmpty then
      current := current ++ "/" ++ part
      let some st ← Sys.lstat current | return none
      if st.uid != 0 || st.mode &&& 0o022 != 0 || st.isLnk then return none
  return some path

private def trustedBytes (path : String) : IO (Option ByteArray) := do
  try
    let some path ← trustedPath path | return none
    let some st ← Sys.lstat path | return none
    if !st.isReg || st.size > 64 * 1024 * 1024 then return none
    return some (← IO.FS.readBinFile path)
  catch _ => return none

private def word (b : ByteArray) (o : Nat) : Nat :=
  b[o]!.toNat + b[o+1]!.toNat * 256 + b[o+2]!.toNat * 65536 +
    b[o+3]!.toNat * 16777216

private def normalized (name : String) : String :=
  let parts := name.splitOn "."
  match parts with
  | [base, suffix] =>
    let fields := suffix.splitOn "@"
    let code := String.ofList ((fields.headD "").toList.filter Char.isAlphanum) |>.toLower
    base ++ "." ++ code ++ (if fields.length > 1 then "@" ++ fields[1]! else "")
  | _ => name

private def archiveNames (bytes : ByteArray) : List String := Id.run do
  if bytes.size < 56 || word bytes 0 != 0xde020109 then return []
  let offset := word bytes 8
  let count := word bytes 16
  if offset > bytes.size || count > (bytes.size - offset) / 12 then return []
  let mut result := []
  for i in List.range count do
    let entry := offset + i * 12
    let start := word bytes (entry + 4)
    let record := word bytes (entry + 8)
    if start < bytes.size && record != 0 && record + 4 + 13 * 8 ≤ bytes.size then
      let nameBytes := (bytes.extract start (min bytes.size (start + 256))).data.toList.takeWhile (· != 0)
      if let some name := String.fromUTF8? ⟨nameBytes.toArray⟩ then
        result := name :: result
  return result

private def categoryExists (archive : List String) (name category : String) : IO Bool := do
  if name == "C" || name == "POSIX" then return true
  if !safeName name then return false
  if archive.contains name || archive.contains (normalized name) then return true
  for variant in [name, normalized name] do
    let suffix := if category == "LC_MESSAGES" then category ++ "/SYS_LC_MESSAGES" else category
    if let some path ← trustedPath ("/usr/lib/locale/" ++ variant ++ "/" ++ suffix) then
      if let some st ← Sys.lstat path then
        if st.isReg && st.size > 0 then return true
  return false

private def selected (env : List (String × String)) (category : String) : String :=
  ((env.lookup "LC_ALL").filter (!·.isEmpty)).or
    ((env.lookup category).filter (!·.isEmpty)) |>.getD
      (((env.lookup "LANG").filter (!·.isEmpty)).getD "C")

/-- setlocale(LC_ALL, "") is atomic: one invalid category leaves the initial C
locale in place. LANGUAGE is consulted by gettext only after locale activation. -/
def messageLocale (env : List (String × String)) : IO String := do
  let messages := selected env "LC_MESSAGES"
  if messages == "C" || messages == "POSIX" || messages.startsWith "C." then return "C"
  let archive := archiveNames ((← trustedBytes "/usr/lib/locale/locale-archive").getD {})
  for category in ["LC_CTYPE", "LC_NUMERIC", "LC_TIME", "LC_COLLATE", "LC_MONETARY",
      "LC_MESSAGES", "LC_PAPER", "LC_NAME", "LC_ADDRESS", "LC_TELEPHONE",
      "LC_MEASUREMENT", "LC_IDENTIFICATION"] do
    if !(← categoryExists archive (selected env category) category) then return "C"
  return selected env "LC_MESSAGES"

/-- gettext's locale specificity order, including normalized codesets. -/
def localeVariants (name : String) : List String := Id.run do
  if !safeName name then return []
  let modifier := (name.splitOn "@").drop 1 |>.head?
  let main := (name.splitOn "@").headD name
  let code := (main.splitOn ".").drop 1 |>.head?
  let base := (main.splitOn ".").headD main
  let language := (base.splitOn "_").headD base
  let mut out := []
  for m in (if modifier.isSome then [modifier, none] else [none]) do
    for b in (if language == base then [base] else [base, language]) do
      for c in (if code.isSome then [code, code.map (fun s =>
          String.ofList (s.toList.filter Char.isAlphanum) |>.toLower), none] else [none]) do
        out := out ++ [b ++ (c.map ("." ++ ·)).getD "" ++ (m.map ("@" ++ ·)).getD ""]
  return out.eraseDups

private def loadDomain (languages : List String) (domain : String) : IO Catalog := do
  let mut catalogs : List Catalog := []
  for language in languages do
    if language == "C" || language == "POSIX" || language.startsWith "C." then break
    -- Ubuntu's local-altlocaledir.diff appends the langpack tree *after all*
    -- specificity variants in the bound /usr/share/locale tree.
    for root in ["/usr/share/locale", "/usr/share/locale-langpack"] do
      for variant in localeVariants language do
        if let some bytes ← trustedBytes (root ++ "/" ++ variant ++ "/LC_MESSAGES/" ++ domain ++ ".mo") then
          if let some catalog := parseMo bytes then catalogs := catalogs ++ [catalog]
  -- Retain the highest-priority entry for each msgid, including its metadata.
  let mut result : Catalog := catalogs.headD {}
  for catalog in catalogs.drop 1 do
    result := merge result catalog
  return result

def loadCatalogs (env : List (String × String)) : IO Catalogs := do
  let locale ← messageLocale env
  if locale == "C" || locale == "POSIX" || locale.startsWith "C." then return {}
  let languages := ((env.lookup "LANGUAGE").filter (!·.isEmpty)).map (·.splitOn ":") |>.getD [locale]
  let sudo ← loadDomain languages "sudo"
  let sudoers ← loadDomain languages "sudoers"
  return ⟨sudo, sudoers, presentation (merge sudoers sudo), presentation sudo⟩

private initialize active : IO.Ref Catalogs ← IO.mkRef {}

def initializeLocale : IO Unit := do
  active.set (← loadCatalogs (← Sys.environ))

def catalogs : IO Catalogs := active.get

def gettext (msgid : String) (policy : Bool := true) : IO String := do
  let cats ← catalogs
  return lookup (if policy then cats.sudoers else cats.sudo) msgid

/-- Translate only at the terminal boundary, never while constructing log data. -/
def translate (text : String) (policy : Bool := true) : IO String := do
  let cats ← catalogs
  return render (if policy then cats.diagnostics else cats.frontend) text

private initialize logCatalog : IO.Ref (String × Catalog) ← IO.mkRef ("C", {})

/-- Logs use sudoers_locale, not the invoking user's LANGUAGE or message locale. -/
def translateLog (locale text : String) : IO String := do
  if locale == "C" || locale == "POSIX" || locale.startsWith "C." then return text
  let (cached, catalog) ← logCatalog.get
  let catalog ← if cached == locale then pure catalog else do
    let loaded ← loadCatalogs [("LC_ALL", locale)]
    logCatalog.set (locale, loaded.sudoers)
    pure loaded.sudoers
  return render catalog text

end LeanSudo.I18n
