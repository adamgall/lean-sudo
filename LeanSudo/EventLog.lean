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

`message` arguments are the already-escaped event body, **without** the submitting
user and ` : ` prefix. `messageBody` adapts `Core.LogLine.msg` to that contract.
Inputs are NUL-free, as are upstream's escaped event fields. These functions do
not escape fields, format dates, perform I/O, or encode JSON.

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

end LeanSudo.EventLog
