import LeanSudo.Policy.Types
import Lean.Data.Json

namespace LeanSudo.IoLog
open Lean

/-- The policy-selected streams; C only writes streams selected here. -/
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
  cwd : String
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

/-- Expanded values cannot inject directories (the sequence deliberately can). -/
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

/-- Only the time escapes actually requested need an operating-system oracle. -/
def timeKeys : List Char → List String
  | [] => []
  | '%' :: '%' :: cs => timeKeys cs
  | '%' :: '{' :: cs => timeKeys (cs.drop ((cs.takeWhile (· != '}')).length + 1))
  | '%' :: 'E' :: c :: cs => String.ofList ['E', c] :: timeKeys cs
  | '%' :: 'O' :: c :: cs => String.ofList ['O', c] :: timeKeys cs
  | '%' :: c :: cs => String.singleton c :: timeKeys cs
  | _ :: cs => timeKeys cs
termination_by cs => cs.length

/-- Expand sudo's named escapes and strftime escapes. The shell supplies a snapshot
of the local-time strftime table, so the path construction remains pure. -/
def expandChars (m : Metadata) (seq : String) (time : List (String × String)) :
    List Char → String
  | [] => ""
  | '%' :: '%' :: cs => "%" ++ expandChars m seq time cs
  | '%' :: '{' :: cs =>
    let name := cs.takeWhile (· != '}')
    let rest := cs.drop (name.length + 1)
    (namedValue m seq (String.ofList name)).getD ("%{" ++ String.ofList name ++ "}") ++
      expandChars m seq time rest
  | '%' :: 'E' :: c :: cs =>
    (time.lookup (String.ofList ['E', c])).getD (String.ofList ['%', 'E', c]) ++
      expandChars m seq time cs
  | '%' :: 'O' :: c :: cs =>
    (time.lookup (String.ofList ['O', c])).getD (String.ofList ['%', 'O', c]) ++
      expandChars m seq time cs
  | '%' :: c :: cs =>
    (time.lookup (String.singleton c)).getD (String.ofList ['%', c]) ++ expandChars m seq time cs
  | c :: cs => String.singleton c ++ expandChars m seq time cs
termination_by cs => cs.length

def expandPath (m : Metadata) (seq : String) (time : List (String × String))
    (pattern : String) : String := expandChars m seq time pattern.toList

private def cleanLegacy (s : String) : String :=
  s.replace "\n" " " |>.replace "\r" " " |>.replace ":" "_"

def legacyLog (m : Metadata) (seconds : Nat) : String :=
  s!"{seconds}:{cleanLegacy m.user}:{cleanLegacy m.runasUser}:{cleanLegacy m.runasGroup}:{cleanLegacy m.tty}:{m.rows}:{m.cols}\n" ++
  m.cwd.replace "\n" " " ++ "\n" ++
  (String.intercalate " " m.argv.toList).replace "\n" " " ++ "\n"

/-- sudoreplay's JSON reader is line-oriented: nested object/array delimiters must
occupy their own lines, even when a conventional JSON pretty-printer would fit them. -/
def jsonLog (m : Metadata) (seconds nanoseconds : Nat) : String :=
  let field (key : String) (value : Lean.Json) :=
    "  \"" ++ key ++ "\": " ++ value.compress ++ ",\n"
  "{\n  \"submit_time\": {\n" ++
    s!"    \"seconds\": {seconds},\n    \"nanoseconds\": {nanoseconds}\n" ++ "  },\n" ++
    field "submituser" (toJson m.user) ++ field "submitgroup" (toJson m.group) ++
    field "runuser" (toJson m.runasUser) ++ field "rungroup" (toJson m.runasGroup) ++
    field "submithost" (toJson m.hostname) ++ field "submitcwd" (toJson m.cwd) ++
    field "ttyname" (toJson m.tty) ++ field "command" (toJson m.command) ++
    "  \"runargv\": [\n" ++
    String.intercalate ",\n" (m.argv.toList.map fun arg => "    " ++ (toJson arg).compress) ++
    "\n  ],\n" ++ field "lines" (toJson m.rows) ++
    s!"  \"columns\": {m.cols}\n" ++ "}\n"

def timingRecord (event seconds nanoseconds : Nat) (detail : String) : String :=
  let ns := toString (nanoseconds % 1000000000)
  s!"{event} {seconds}." ++ String.ofList (List.replicate (9 - ns.length) '0') ++ ns ++ " " ++ detail ++ "\n"

end LeanSudo.IoLog
