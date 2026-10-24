/-
SPDX-License-Identifier: ISC

Copyright (c) 1994-1996, 1998-2023 Todd C. Miller <Todd.Miller@sudo.ws>
Copyright (c) 2011, 2014-2020 Todd C. Miller <Todd.Miller@sudo.ws>
Copyright (c) 2020-2021 Todd C. Miller <Todd.Miller@sudo.ws>

Permission to use, copy, modify, and distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

Sponsored in part by the Defense Advanced Research Projects
Agency (DARPA) and Air Force Research Laboratory, Air Force
Materiel Command, USAF, under agreement number F39502-99-1-0512.
-/
import Init

/-!
Pure sudo-format event output, ported from sudo 1.9.17p2:
* https://github.com/sudo-project/sudo/blob/v1.9.17p2/lib/eventlog/eventlog.c
* https://github.com/sudo-project/sudo/blob/v1.9.17p2/lib/eventlog/logwrap.c
* https://github.com/sudo-project/sudo/blob/v1.9.17p2/include/sudo_eventlog.h
* https://github.com/sudo-project/sudo/blob/v1.9.17p2/lib/util/json.c

`message` arguments are the already-escaped event body, **without** the submitting
user and ` : ` prefix. `messageBody` adapts `Core.LogLine.msg` to that contract.
Inputs are NUL-free. Sudo-format helpers consume escaped bodies; JSON helpers
consume raw fields and preserve upstream field order, including repeated exit keys.

Syslog may split inside a UTF-8 character, so its exact interface returns bytes,
not Lean strings. File output splits only at ASCII spaces and remains UTF-8.
-/
namespace LeanSudo.EventLog

/-- Remove exactly the submitting user's prefix from a `Core.LogLine.msg`.
Messages without that prefix are unchanged; no whitespace is trimmed. -/
def messageBody (user message : String) : String :=
  let hdr := user ++ " : "
  if message.startsWith hdr then (message.drop hdr.length).toString else message

/-- Last ASCII space in the half-open byte interval `[start, stop)`. -/
private def lastSpace (bytes : ByteArray) (start stop : Nat) : Option Nat := Id.run do
  for offset in [:stop - start] do
    let i := stop - 1 - offset
    if bytes[i]! == 32 then return some i
  return none

private def skipSpaces (bytes : ByteArray) (start : Nat) : Nat := Id.run do
  for i in [start:bytes.size] do
    if bytes[i]! != 32 then return i
  return bytes.size

private def nextSpace (bytes : ByteArray) (start : Nat) : Option Nat := Id.run do
  for i in [start:bytes.size] do
    if bytes[i]! == 32 then return some i
  return none

/-- Split an event body exactly as `do_syslog_sudo`, including `%8s : ` and
`%8s : (command continued) ` prefixes, with no trailing newlines.

Lengths and padding count UTF-8 **bytes**, not characters. Upstream subtracts
`userByteLength + 3` (then `+ 23`) from `maxlen`, ignoring the extra padding for
users shorter than eight bytes; this quirk is deliberately preserved. Only
ASCII spaces are word breaks, and spaces at a split are skipped. Long words
are split at the byte limit, even inside UTF-8 characters. An empty body emits
no records.

Use `maxlen > user.toUTF8.size + 23` for upstream's normal, positive budgets.
If a budget is too small for its prefix, the remaining body is emitted unsplit:
this agrees with upstream's unsigned underflow for smaller limits and makes
its zero-budget infinite-loop case total without discarding any content. -/
def splitSyslogBytes (user message : String) (maxlen : Nat) : List ByteArray := Id.run do
  let bytes := message.toUTF8
  let userLen := user.toUTF8.size
  let padding := String.ofList (List.replicate (8 - userLen) ' ')
  let firstPrefix := (padding ++ user ++ " : ").toUTF8
  let nextPrefix := (padding ++ user ++ " : (command continued) ").toUTF8
  let mut hdr := firstPrefix
  let mut overhead := userLen + 3
  let mut pos := 0
  let mut result : List ByteArray := []
  -- Every iteration consumes a byte or finishes, even for leading spaces.
  for _ in [:bytes.size] do
    if pos >= bytes.size then break
    let available := maxlen - overhead
    if available == 0 || bytes.size - pos <= available then
      result := bytes.copySlice pos hdr hdr.size (bytes.size - pos) :: result
      break
    let stop := (lastSpace bytes pos (pos + available)).getD (pos + available)
    result := bytes.copySlice pos hdr hdr.size (stop - pos) :: result
    pos := skipSpaces bytes stop
    hdr := nextPrefix
    overhead := userLen + 23
  return result.reverse

/-- Wrap an already assembled file log line as `eventlog_writeln` does.
`lineLen < 5` disables wrapping. Continuations have four leading spaces;
long words are never split, and only spaces consumed at a wrap are removed.
A nonempty final line gets a newline. With wrapping disabled even an empty
input gets a newline; with wrapping enabled an empty input produces nothing. -/
def wrapFileLine (line : String) (lineLen : Nat) : String := Id.run do
  if lineLen < 5 then return line ++ "\n"
  let bytes := line.toUTF8
  let indent := "    ".toUTF8
  let mut output := ByteArray.empty
  let mut pos := 0
  let mut available := lineLen
  let mut continued := false
  for _ in [:bytes.size] do
    if bytes.size - pos <= available then break
    -- Unlike syslog, file wrapping includes the byte at the width boundary.
    let backward := lastSpace bytes pos (pos + available + 1)
    let stop := match backward with
      | some i => if i == pos then nextSpace bytes (pos + available) else some i
      | none => nextSpace bytes (pos + available)
    let some stop := stop | break
    if continued then output := output ++ indent
    output := bytes.copySlice pos output output.size (stop - pos)
    output := output.push 10
    pos := skipSpaces bytes stop
    if !continued then
      continued := true
      available := lineLen - 4
  if pos < bytes.size then
    if continued then output := output ++ indent
    output := bytes.copySlice pos output output.size (bytes.size - pos)
    output := output.push 10
  -- Every slice ends at an ASCII space or the original string's end.
  return String.fromUTF8! output

/-- Assemble and wrap a sudo logfile record. `timestamp` is already formatted
(e.g. `Oct 24 12:34:56`, or upstream's `invalid date` on conversion failure).
The unpadded user is followed by ` : ` and the already-escaped event body.
When `logHost` is true, `HOST=host ; ` is prepended to that body, matching
`new_logline`; it is not a separate field between timestamp and user.
The caller must not already have added `HOST=` to the supplied body. -/
def formatFile (timestamp host user message : String) (logHost : Bool)
    (lineLen : Nat) : String :=
  let body := if logHost then "HOST=" ++ host ++ " ; " ++ message else message
  wrapFileLine (timestamp ++ " : " ++ user ++ " : " ++ body) lineLen

/-- JSON strings use sudo_json's control escaping (including DEL, unlike many
JSON encoders); UTF-8 and forward slashes pass through unchanged. -/
def jsonQuote (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c => match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\x08' => "\\b"
    | '\x0c' => "\\f"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c => if c.toNat < 32 || c.toNat == 127 then
        let hex := "0123456789abcdef".toList
        "\\u00" ++ (hex[c.toNat / 16]!).toString ++ (hex[c.toNat % 16]!).toString
      else c.toString) ++ "\""

/-- Ordered JSON values, deliberately retaining duplicate object members.
sudo 1.9.17p2 emits the exit status fields twice. -/
inductive JsonValue where
  | string (s : String)
  | number (n : Int)
  | bool (b : Bool)
  | object (fields : List (String × JsonValue))
  | array (values : List JsonValue)
  deriving Inhabited

def JsonValue.render (compact : Bool) (depth : Nat) : JsonValue → String
  | .string s => jsonQuote s
  | .number n => toString n
  | .bool b => if b then "true" else "false"
  | .object fields =>
    let indent := if compact then "" else "\n" ++ String.ofList (List.replicate (4 * (depth + 1)) ' ')
    let close := if compact then "" else "\n" ++ String.ofList (List.replicate (4 * depth) ' ')
    "{" ++ String.intercalate "," (fields.attach.map fun ⟨(k, v), _⟩ =>
      indent ++ jsonQuote k ++ (if compact then ":" else ": ") ++ v.render compact (depth + 1)) ++ close ++ "}"
  | .array values =>
    let indent := if compact then "" else "\n" ++ String.ofList (List.replicate (4 * (depth + 1)) ' ')
    let close := if compact then "" else "\n" ++ String.ofList (List.replicate (4 * depth) ' ')
    "[" ++ String.intercalate "," (values.attach.map fun ⟨v, _⟩ =>
      indent ++ v.render compact (depth + 1)) ++ close ++ "]"
termination_by v => sizeOf v
decreasing_by
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
    simp_all +arith
    omega

structure Time where
  seconds : Nat := 0
  nanoseconds : Nat := 0
  iso8601 : String := ""
  localtime : String := ""
  deriving Inhabited

def Time.json (t : Time) (formatted : Bool := true) : JsonValue :=
  .object ([("seconds", .number t.seconds), ("nanoseconds", .number t.nanoseconds)] ++
    if formatted then
      (if t.iso8601.isEmpty then [] else [("iso8601", .string t.iso8601)]) ++
      (if t.localtime.isEmpty then [] else [("localtime", .string t.localtime)])
    else [])

inductive EventType where
  | accept | reject | alert | exit
  deriving BEq, Inhabited

def EventType.name : EventType → String
  | .accept => "accept" | .reject => "reject" | .alert => "alert" | .exit => "exit"

def EventType.timeName : EventType → String
  | .accept | .reject => "submit_time" | .alert => "alert_time" | .exit => "exit_time"

/-- Raw eventlog_store_json fields. Absent pointers must be omitted, not encoded
as null; empty vectors, when present, remain arrays. -/
structure Details where
  submituser : String
  command : Option String := none
  runuser : Option String := none
  rungroup : Option String := none
  runchroot : Option String := none
  runcwd : Option String := none
  source : Option String := none
  ttyname : Option String := none
  submithost : Option String := none
  submitcwd : Option String := none
  rungid : Option Nat := none
  runuid : Option Nat := none
  columns : Nat := 80
  lines : Nat := 24
  runargv : Option (List String) := none
  runenv : Option (List String) := none
  submitenv : Option (List String) := none
  deriving Inhabited

private def stringField (k : String) (v : Option String) : List (String × JsonValue) :=
  v.toList.map fun s => (k, .string s)

private def numberField (k : String) (v : Option Nat) : List (String × JsonValue) :=
  v.toList.map fun n => (k, .number (Int.ofNat n))

private def arrayField (k : String) (v : Option (List String)) : List (String × JsonValue) :=
  v.toList.map fun ss => (k, .array (ss.map .string))

def Details.fields (d : Details) : List (String × JsonValue) :=
  [("submituser", .string d.submituser)] ++
  stringField "command" d.command ++ stringField "runuser" d.runuser ++
  stringField "rungroup" d.rungroup ++ stringField "runchroot" d.runchroot ++
  stringField "runcwd" d.runcwd ++ stringField "source" d.source ++
  stringField "ttyname" d.ttyname ++ stringField "submithost" d.submithost ++
  stringField "submitcwd" d.submitcwd ++
  (if d.rungroup.isSome then numberField "rungid" d.rungid else []) ++
  numberField "runuid" d.runuid ++
  [("columns", .number d.columns), ("lines", .number d.lines)] ++
  arrayField "runargv" d.runargv ++ arrayField "runenv" d.runenv ++
  arrayField "submitenv" d.submitenv

structure Event where
  kind : EventType
  uuid : String := ""
  reason : Option String := none
  error : Option String := none
  serverTime : Time
  eventTime : Option Time := none
  runTime : Option Time := none
  signal : Option String := none
  dumpedCore : Bool := false
  exitValue : Int := -1
  peeraddr : Option String := none
  iologPath : Option String := none
  iologOffset : Option Time := none
  details : Option Details := none
  deriving Inhabited

private def Event.exitFields (e : Event) : List (String × JsonValue) :=
  if e.kind != .exit then [] else
    (e.runTime.toList.map fun t => ("run_time", t.json false)) ++
    (e.signal.toList.flatMap fun s => [("signal", .string s), ("dumped_core", .bool e.dumpedCore)]) ++
    [("exit_value", .number e.exitValue)]

def Event.fields (e : Event) : List (String × JsonValue) :=
  (if e.uuid.isEmpty then [] else [("uuid", .string e.uuid)]) ++
  stringField "reason" (e.reason.map fun r => r ++ (e.error.map (": " ++ ·)).getD "") ++
  [("server_time", e.serverTime.json)] ++
  (e.eventTime.toList.map fun t => (e.kind.timeName, t.json)) ++
  e.exitFields ++ stringField "peeraddr" e.peeraddr ++
  stringField "iolog_path" e.iologPath ++
  (if e.iologPath.isSome then e.iologOffset.toList.map fun t => ("iolog_offset", t.json false) else []) ++
  e.exitFields ++
  (if e.kind == .exit && !e.uuid.isEmpty then [] else e.details.toList.flatMap Details.fields)

/-- The member fragment used by sudo's seek-and-append pretty log writer. -/
def formatJsonMember (e : Event) (compact : Bool) : String :=
  (if compact then "" else "\n    ") ++ jsonQuote e.kind.name ++
    (if compact then ":" else ": ") ++ (JsonValue.object e.fields).render compact 1

/-- JSON syslog is never split, even when syslog_maxlen is small. -/
def formatJsonSyslog (e : Event) : String :=
  "@cee:{\"sudo\":{" ++ formatJsonMember e true ++ "}}"

def formatJsonLine (e : Event) : String :=
  "{" ++ formatJsonMember e true ++ "}\n"

/-- Authentication disposition, separate from conversation diagnostics. An EOF
does not count as a bad password; completed failed verifications do. -/
structure AuthFailure where
  attempts : Nat := 0
  noInput : Bool := false
  /-- PAM errors/noninteractive refusal do not subsequently log a policy denial. -/
  error : Bool := false
  /-- Caught terminal signal, re-raised only after logging and PAM cleanup. -/
  signal : Nat := 0
  deriving Repr, Inhabited

/-- sudoers/logging.c log_auth_failure syslog disposition: denied commands log
the denial instead; noninteractive list/validate and zero-attempt reads are quiet. -/
def logAuthFailure (allowed logDenied listOrValidate : Bool) (f : AuthFailure) : Bool :=
  allowed && logDenied && (if f.noInput then !listOrValidate else f.attempts != 0)

/-- The file backend retains auth failure events even when syslog is suppressed.
Noninteractive list/validate are excluded from both backends (Ubuntu differential tests). -/
def fileAuthFailure (listOrValidate : Bool) (f : AuthFailure) : Bool :=
  !(f.noInput && listOrValidate)

def mailAuthFailure (allowed mailBadpass mailAlways denialMail listOrValidate : Bool)
    (f : AuthFailure) : Bool :=
  !(f.noInput && listOrValidate) &&
    (if allowed then mailBadpass || mailAlways else mailBadpass && !denialMail)

theorem denied_auth_failure_not_logged (logDenied listOrValidate : Bool) (f : AuthFailure) :
    logAuthFailure false logDenied listOrValidate f = false := by
  simp [logAuthFailure]

theorem disabled_auth_failure_not_logged (allowed listOrValidate : Bool) (f : AuthFailure) :
    logAuthFailure allowed false listOrValidate f = false := by
  simp [logAuthFailure]

theorem noninteractive_list_auth_failure_not_logged (allowed logDenied : Bool) (n : Nat) (e : Bool) :
    logAuthFailure allowed logDenied true { attempts := n, noInput := true, error := e } = false := by
  simp [logAuthFailure]

end LeanSudo.EventLog
