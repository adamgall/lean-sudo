import LeanSudo.Policy.Types
import Lean.Data.Json

namespace LeanSudo.IoLog
open Lean

structure Plan where
  dir : String
  file : String
  user : String
  group : String
  mode : Nat
  maxseq : Nat
  compress : Bool
  flush : Bool
  ignoreErrors : Bool
  logPasswords : Bool
  passpromptRegex : Array String
  stdin : Bool
  stdout : Bool
  stderr : Bool
  ttyin : Bool
  ttyout : Bool
  deriving Repr, BEq

structure Metadata where
  user : String
  group : String
  runasUser : String
  runasGroup : String
  hostname : String
  command : String
  cwd : Option String
  tty : String
  argv : Array String
  rows : Nat := 24
  cols : Nat := 80
  deriving Repr, BEq

def enabled (s : Settings) (t : Sudoers.Tags) : Bool :=
  t.logInput.getD s.logStdin || t.logInput.getD s.logTtyin ||
  t.logOutput.getD s.logStdout || t.logOutput.getD s.logStderr || t.logOutput.getD s.logTtyout

def plan (s : Settings) (t : Sudoers.Tags) : Option Plan :=
  if enabled s t then some {
    dir := s.iologDir, file := s.iologFile
    user := s.iologUser.getD "root", group := s.iologGroup.getD ""
    mode := s.iologMode, maxseq := min (s.maxseq.toNat?.getD 2176782335) 2176782335
    compress := s.compressIo, flush := s.iologFlush
    ignoreErrors := s.ignoreIologErrors, logPasswords := s.logPasswords
    passpromptRegex := s.passpromptRegex.toArray
    stdin := t.logInput.getD s.logStdin
    stdout := t.logOutput.getD s.logStdout
    stderr := t.logOutput.getD s.logStderr
    ttyin := t.logInput.getD s.logTtyin
    ttyout := t.logOutput.getD s.logTtyout }
  else none

theorem plan_enabled (s : Settings) (t : Sudoers.Tags) :
    (plan s t).isSome = enabled s t := by
  simp only [plan]
  split <;> simp_all

def digit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 65 + n - 10)

def sequence (n : Nat) : String :=
  String.ofList (([5, 4, 3, 2, 1, 0] : List Nat).map fun p => digit (n / 36 ^ p % 36))

def sequencePath (n : Nat) : String :=
  let ds := (sequence n).toList
  String.ofList (ds.take 2) ++ "/" ++ String.ofList ((ds.drop 2).take 2) ++
    "/" ++ String.ofList (ds.drop 4)

def nextSequence (n maxseq : Nat) : Nat := if n ≥ maxseq then 1 else n + 1

def pathValue (s : String) : String := s.replace "/" "_"

def namedValue (m : Metadata) (seq name : String) : Option String :=
  match name with
  | "seq" => some seq
  | "user" => some (pathValue m.user)
  | "group" => some (pathValue m.group)
  | "runas_user" => some (pathValue m.runasUser)
  | "runas_group" => some (pathValue m.runasGroup)
  | "hostname" => some (pathValue m.hostname)
  | "command" => some (pathValue ((m.command.splitOn "/").getLast!))
  | _ => none

@[specialize] private def foldEscapes {α : Type} (literal : Char → α → α)
    (named : List Char → α → α) (time : String → α → α) (empty : α) : List Char → α
  | [] => empty
  | '%' :: '%' :: cs => literal '%' (foldEscapes literal named time empty cs)
  | '%' :: '{' :: cs =>
    let name := cs.takeWhile (· != '}')
    named name (foldEscapes literal named time empty (cs.drop (name.length + 1)))
  | '%' :: modifier :: rest@(c :: cs) =>
    if modifier == 'E' || modifier == 'O' then
      time (String.ofList [modifier, c]) (foldEscapes literal named time empty cs)
    else time (String.singleton modifier) (foldEscapes literal named time empty rest)
  | '%' :: c :: cs => time (String.singleton c) (foldEscapes literal named time empty cs)
  | c :: cs => literal c (foldEscapes literal named time empty cs)
termination_by cs => cs.length

def timeKeys (cs : List Char) : List String :=
  foldEscapes (fun _ rest => rest) (fun _ rest => rest) List.cons [] cs

def expandChars (m : Metadata) (seq : String) (time : List (String × String))
    (cs : List Char) : String :=
  foldEscapes (fun c rest => String.singleton c ++ rest)
    (fun chars rest =>
      let name := String.ofList chars
      (namedValue m seq name).getD ("%{" ++ name ++ "}") ++ rest)
    (fun key rest => (time.lookup key).getD ("%" ++ key) ++ rest) "" cs

def expandPath (m : Metadata) (seq : String) (time : List (String × String))
    (pattern : String) : String := expandChars m seq time pattern.toList

private def cleanLegacy (s : String) : String :=
  s.replace "\n" " " |>.replace "\r" " " |>.replace ":" "_"

def legacyLog (m : Metadata) (seconds : Nat) : String :=
  s!"{seconds}:{cleanLegacy m.user}:{cleanLegacy m.runasUser}:{cleanLegacy m.runasGroup}:{cleanLegacy m.tty}:{m.rows}:{m.cols}\n" ++
  (m.cwd.getD "unknown").replace "\n" " " ++ "\n" ++
  (String.intercalate " " m.argv.toList).replace "\n" " " ++ "\n"

def jsonLog (m : Metadata) (seconds nanoseconds : Nat) : String :=
  let field (key : String) (value : Lean.Json) :=
    "  \"" ++ key ++ "\": " ++ value.compress ++ ",\n"
  "{\n  \"submit_time\": {\n" ++
    s!"    \"seconds\": {seconds},\n    \"nanoseconds\": {nanoseconds}\n" ++ "  },\n" ++
    field "submituser" (toJson m.user) ++ field "submitgroup" (toJson m.group) ++
    field "runuser" (toJson m.runasUser) ++ field "rungroup" (toJson m.runasGroup) ++
    field "submithost" (toJson m.hostname) ++
    ((m.cwd.map fun cwd => field "submitcwd" (toJson cwd)).getD "") ++
    field "ttyname" (toJson m.tty) ++ field "command" (toJson m.command) ++
    "  \"runargv\": [\n" ++
    String.intercalate ",\n" (m.argv.toList.map fun arg => "    " ++ (toJson arg).compress) ++
    "\n  ],\n" ++ field "lines" (toJson m.rows) ++
    s!"  \"columns\": {m.cols}\n" ++ "}\n"

def timingRecord (event seconds nanoseconds : Nat) (detail : String) : String :=
  let ns := toString (nanoseconds % 1000000000)
  s!"{event} {seconds}." ++ String.ofList (List.replicate (9 - ns.length) '0') ++ ns ++ " " ++ detail ++ "\n"

end LeanSudo.IoLog
