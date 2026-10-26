import LeanSudo.Policy.Defaults
import LeanSudo.Sudoers.Parser

namespace LeanSudo.Visudo

open LeanSudo.Sudoers LeanSudo.Policy

structure Options where
  check : Bool := false
  file : Option String := none
  exportFile : Option String := none
  quiet : Bool := false
  strict : Bool := false
  noIncludes : Bool := false
  owner : Bool := false
  perms : Bool := false
  help : Bool := false
  version : Bool := false
  deriving Repr, BEq, Inhabited

def usageLine : String := "usage: visudo [-chqsV] [[-f] sudoers ]"

def helpText : String :=
  "visudo - safely edit the sudoers file\n\n" ++ usageLine ++ "\n\nOptions:\n" ++
  "  -c, --check              check-only mode\n" ++
  "  -f, --file=sudoers       specify sudoers file location\n" ++
  "  -h, --help               display help message and exit\n" ++
  "  -I, --no-includes        do not edit include files\n" ++
  "  -q, --quiet              less verbose (quiet) syntax error messages\n" ++
  "  -s, --strict             strict syntax checking\n" ++
  "  -V, --version            display version information and exit\n\n"

def versionText : String :=
  "visudo version 1.9.17p2\nvisudo grammar version 50\n"

def flagOf : Char → Option (Options → Options)
  | 'c' => some fun o => { o with check := true }
  | 'h' => some fun o => { o with help := true }
  | 'I' => some fun o => { o with noIncludes := true }
  | 'O' => some fun o => { o with owner := true }
  | 'P' => some fun o => { o with perms := true }
  | 'q' => some fun o => { o with quiet := true }
  | 's' => some fun o => { o with strict := true }
  | 'V' => some fun o => { o with version := true }
  | _ => none

def longOptions : List (String × Char) :=
  [("check", 'c'), ("export", 'x'), ("file", 'f'), ("help", 'h'),
   ("no-includes", 'I'), ("owner", 'O'), ("perms", 'P'), ("quiet", 'q'),
   ("strict", 's'), ("version", 'V')]

def lookupLong (name : String) : Except String Char :=
  match longOptions.find? (·.1 == name) with
  | some (_, c) => .ok c
  | none =>
    match longOptions.filter (fun (n, _) => !name.isEmpty && n.startsWith name) with
    | [(_, c)] => .ok c
    | [] => .error s!"unrecognized option '--{name}'"
    | _ => .error s!"option '--{name}' is ambiguous"

def shortBundle : List Char → Options → Except String (Options × Option (Char × String))
  | [], o => .ok (o, none)
  | 'f' :: rest, o => .ok (o, some ('f', String.ofList rest))
  | 'x' :: rest, o => .ok (o, some ('x', String.ofList rest))
  | c :: rest, o =>
    match flagOf c with
    | some f =>
      if c == 'h' || c == 'V' then .ok (f o, none) else shortBundle rest (f o)
    | none => .error s!"invalid option -- '{c}'"

def finishArgs (o : Options) : List String → Except String Options
  | [] => .ok o
  | [f] => .ok (if o.file.isSome then o else { o with file := some f })
  | _ => .error ""

def setArgument (o : Options) (c : Char) (v : String) : Options :=
  if c == 'x' then { o with exportFile := some v } else { o with file := some v }

def parseArgs (args : List String) : Except String Options :=
  go args {} [] none
where
  go : List String → Options → List String → Option (Char × String) → Except String Options
  | [], _, _, some (_, msg) => .error msg
  | [], o, ops, none => finishArgs o ops.reverse
  | a :: rest, o, ops, some (c, _) => go rest (setArgument o c a) ops none
  | "--" :: rest, o, ops, none => finishArgs o (ops.reverse ++ rest)
  | a :: rest, o, ops, none =>
    match a.toList with
    | '-' :: '-' :: body =>
      let (name, val?) : List Char × Option (List Char) :=
        match body.span (· != '=') with
        | (n, []) => (n, none)
        | (n, _ :: v) => (n, some v)
      let name := String.ofList name
      match lookupLong name with
      | .error e => .error e
      | .ok c =>
        if c == 'f' || c == 'x' then
          match val? with
          | some v => go rest (setArgument o c (String.ofList v)) ops none
          | none => go rest o ops (some (c, s!"option '--{name}' requires an argument"))
        else
          match val?, flagOf c with
          | some _, _ =>
            let full := ((longOptions.find? (·.2 == c)).map (·.1)).getD name
            .error s!"option '--{full}' doesn't allow an argument"
          | none, some f =>
            if c == 'h' || c == 'V' then .ok (f o) else go rest (f o) ops none
          | none, none => .error s!"unrecognized option '--{name}'"
    | '-' :: c :: cs =>
      match shortBundle (c :: cs) o with
      | .error e => .error e
      | .ok (o', none) => if o'.help || o'.version then .ok o' else go rest o' ops none
      | .ok (o', some (c, "")) =>
        go rest o' ops (some (c, s!"option requires an argument -- '{c}'"))
      | .ok (o', some (c, v)) => go rest (setArgument o' c v) ops none
    | _ => go rest o (a :: ops) none

def locPos (l : Located) : String := s!"{l.file}:{l.line}"

def renderSyntaxError (e : ParseError) (text : String) : String :=
  if let some rendered := e.rendered then rendered else
  let message := if e.plain then e.msg
    else if e.msg.startsWith "expected a fully-qualified path name" then
      "expected a fully-qualified path name" else "syntax error"
  let header := s!"{e.file}:{e.line}:{e.col}: {message}"
  match (text.splitOn "\n")[e.line - 1]? with
  | some ln =>
    let ln := (ln.splitOn "\x00").head!
    if e.line == 0 || ln.isEmpty then header
    else
      let chars := ln.toList
      let pad := (chars.take (e.col - 1)).map fun c => if c == '\t' then '\t' else ' '
      let pad := pad ++ List.replicate (e.col - 1 - chars.length) ' '
      let token := (chars.drop (e.col - 1)).takeWhile fun c =>
        !c.isWhitespace && !(",=:()!" : String).contains c
      let underline := String.ofList (List.replicate (token.length - 1) '~')
      s!"{header}\n{ln}\n{String.ofList pad}^{underline}"
  | none => header

def aliasDefs (es : List Located) : List (String × String × Located) :=
  es.filterMap fun l =>
    match l.entry with
    | .userAlias n _ => some ("User_Alias", n, l)
    | .runasAlias n _ => some ("Runas_Alias", n, l)
    | .hostAlias n _ => some ("Host_Alias", n, l)
    | .cmndAlias n _ => some ("Cmnd_Alias", n, l)
    | _ => none

def refsByKind (r : Refs) : List (String × List String) :=
  [("User_Alias", r.user), ("Runas_Alias", r.runas), ("Host_Alias", r.host),
   ("Cmnd_Alias", r.cmnd)]

structure AliasScan where
  errors : List String := []
  used : List (String × String) := []
  warned : List String := []

def scanAlias (defs : List (String × String × Located)) :
    Nat → List (String × String) → String → String → Located → AliasScan → AliasScan
  | 0, _, _, _, _, state => state
  | fuel + 1, active, kind, name, loc, state =>
    let key := (kind, name)
    let cycle := active.contains key
    match defs.find? (fun (k, n, _) => k == kind && n == name) with
    | some (_, _, defn) =>
      if cycle then
        if state.warned.contains name then state else
          { state with errors := state.errors ++ [s!"{locPos loc}: cycle in {kind} \"{name}\""]
                       warned := name :: state.warned }
      else if state.used.contains key then state
      else
        let refs := ((refsByKind (entryRefs defn.entry)).find? (·.1 == kind)).map (·.2)
        (refs.getD []).foldl
          (fun s n => scanAlias defs fuel (key :: active) kind n defn s)
          { state with used := key :: state.used }
    | none =>
      if state.warned.contains name then state else
        { state with errors := state.errors ++
            [s!"{locPos loc}: {kind} \"{name}\" referenced but not defined"]
                     warned := name :: state.warned }

def scanAliases (es : List Located) : AliasScan :=
  let defs := aliasDefs es
  es.foldl (fun state loc =>
    match loc.entry with
    | .userSpec _ =>
      (refsByKind (entryRefs loc.entry)).foldl (fun state (kind, names) =>
        names.foldl (fun state name =>
          scanAlias defs (defs.length + 1) [] kind name loc state) state) state
    | _ => state) {}

def runtimeAliasErrors (es : List Located) : List String :=
  let defs := aliasDefs es
  let state := defs.foldl (fun state (kind, name, loc) =>
    scanAlias defs (defs.length + 1) [] kind name loc state) (scanAliases es)
  let state := es.foldl (fun state loc =>
    match loc.entry with
    | .defaults _ _ =>
      (refsByKind (entryRefs loc.entry)).foldl (fun state (kind, names) =>
        names.foldl (fun state name =>
          scanAlias defs (defs.length + 1) [] kind name loc state) state) state
    | _ => state) state
  state.errors

def defaultsErrors (es : List Located) : List String :=
  es.flatMap fun l =>
    match l.entry with
    | .defaults _ ss => ss.filterMap fun d =>
      let error := match applySetting {} d false with
        | .error e => some e
        | .ok (_, warning) => warning
      error.map fun m => s!"{locPos l}: {m}"
    | _ => []

def semanticErrors (es : List Located) (_strict : Bool := false) : List String :=
  let errors := defaultsErrors es
  match validate (es.map (·.entry)) with
  | .ok () => errors
  | .error message =>
    let errors := errors ++ runtimeAliasErrors es
    if !errors.isEmpty then errors
    else [s!"{es.head?.map locPos |>.getD "visudo"}: {message}"]

def unusedWarnings (es : List Located) : List String :=
  let used := (scanAliases es).used
  ((aliasDefs es).mergeSort (fun a b => a.2.1 ≤ b.2.1)).filterMap fun (k, n, l) =>
    if used.contains (k, n) then none else some s!"Warning: {locPos l}: unused {k} \"{n}\""

def semanticWarnings (es : List Located) (_strict : Bool := false) : List String :=
  unusedWarnings es

def envEditorValues (env : List (String × String)) : List String :=
  ["SUDO_EDITOR", "VISUAL", "EDITOR"].filterMap fun k =>
    match env.lookup k with
    | some v => if (splitWords v).isEmpty then none else some v
    | none => none

def whatNowChoice (line : String) : Option Char :=
  match line.toList with
  | c :: _ => if c == 'e' || c == 'x' || c == 'Q' then some c else none
  | [] => none

def whatNowHelp : String :=
  "Options are:\n" ++
  "  (e)dit sudoers file again\n" ++
  "  e(x)it without saving changes to sudoers file\n" ++
  "  (Q)uit and save changes to sudoers file (DANGER!)\n\n"

def withFinalNewline (s : String) : String :=
  if s.isEmpty || s.endsWith "\n" then s else s ++ "\n"

end LeanSudo.Visudo
