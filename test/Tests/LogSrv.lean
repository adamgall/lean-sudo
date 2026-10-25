import LeanSudo.LogSrv
import LeanSudo.Sys.LogSrv

/-! sudo v1.9.17p2 protobuf body vectors (no transport frame prefix).
Known-answer tags come from the upstream schema, independently of roundtrips. -/
namespace Tests.LogSrv
open LeanSudo.LogSrv

private def bytes (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩
private def zero : TimeSpec := ⟨0, 0⟩
private def clock : TimeSpec := ⟨1712345678, 123456789⟩
private def info : List InfoMessage := [
  ⟨"uid", .number 1000⟩,
  ⟨"command", .string "/usr/bin/id"⟩,
  ⟨"argv", .strings ["id", "-u", "λ"]⟩,
  ⟨"groups", .numbers [0, 127, 128, 1000, -1, -9223372036854775808]⟩,
  ⟨"empty strings", .strings []⟩,
  ⟨"empty numbers", .numbers []⟩]

#guard Wire.encNat 0 = [0]
#guard Wire.encNat 127 = [127]
#guard Wire.encNat 128 = [128, 1]
#guard Wire.encNat 300 = [172, 2]
#guard Wire.encNat (2 ^ 64 - 1) = [255,255,255,255,255,255,255,255,255,1]
#guard Wire.varint [255,255,255,255,255,255,255,255,255,1] = some (2 ^ 64 - 1, [])
#guard Wire.varint [255,255,255,255,255,255,255,255,255,2] = none
#guard Wire.varint [128,128,128,128,128,128,128,128,128,128,0] = none
#guard Wire.varint [128] = none
#guard Wire.unsigned 32 (-1) = 2 ^ 64 - 1
#guard Wire.signed 32 (2 ^ 64 - 1) = -1
#guard Wire.unsigned 64 (-9223372036854775808) = 2 ^ 63

-- ClientHello is top-level field 13, not field 1.
#guard encodeClient (.hello "sudo") = bytes [106,6,10,4,115,117,100,111]
#guard decodeClient (bytes [106,6,10,4,115,117,100,111]) = some (.hello "sudo")
#guard decodeClient (bytes [106,0]) = some (.hello "")
-- Proto3 omitted fields acquire defaults; nested time is not required on wire.
#guard decodeClient (bytes [10,0]) = some (.accept zero [] false)
#guard decodeClient (bytes [26,0]) = some (.exit zero 0 false "" "")
#guard encodeServer (.logId "abc") = bytes [26,3,97,98,99]
#guard encodeServer (.error "bad") = bytes [34,3,98,97,100]
#guard encodeServer (.abort "bye") = bytes [42,3,98,121,101]
#guard decodeServer (bytes [18,4,8,1,16,2]) = some (.commit ⟨1,2⟩)
#guard decodeServer (bytes [10,0]) = some (.hello ⟨"", "", [], false⟩)
#guard decodeServer (bytes [10,2,32,2]) = some (.hello ⟨"", "", [], true⟩)

private def clientCases : List ClientMessage := [
  .hello "lean-sudo λ",
  .accept clock info true,
  .accept zero [] false,
  .reject clock "denied" info,
  .exit ⟨12,345⟩ 255 true "SIGSEGV" "terminated",
  .exit ⟨-9223372036854775808,-2147483648⟩ (-2147483648) false "" "",
  .exit ⟨9223372036854775807,2147483647⟩ 2147483647 false "" "",
  .restart "00/00/01" clock,
  .alert clock "audit failed" info,
  .io 0 clock (bytes [0,1,128,255]),
  .io 1 clock (bytes [0,1,128,255]),
  .io 2 clock (bytes [0,1,128,255]),
  .io 3 clock (bytes [0,1,128,255]),
  .io 4 clock (bytes [0,1,128,255]),
  .winsize clock 24 80,
  .winsize zero 2147483647 2147483647,
  .suspend clock "SIGTSTP"]

private def serverCases : List ServerMessage := [
  .hello ⟨"sudo_logsrvd", "next.example:30343", ["a:30343", "b:30343"], true⟩,
  .hello ⟨"", "", [], false⟩,
  .commit clock,
  .commit ⟨-9223372036854775808,-2147483648⟩,
  .commit ⟨9223372036854775807,2147483647⟩,
  .logId "00/00/01", .error "unavailable", .abort "stop λ"]

#guard clientCases.all fun m => decodeClient (encodeClient m) == some m
#guard serverCases.all fun m => decodeServer (encodeServer m) == some m
#guard (encodeClient (.io 0 zero (bytes []))).data[0]! = 66
#guard (encodeClient (.io 1 zero (bytes []))).data[0]! = 74
#guard (encodeClient (.io 2 zero (bytes []))).data[0]! = 82
#guard (encodeClient (.io 3 zero (bytes []))).data[0]! = 50
#guard (encodeClient (.io 4 zero (bytes []))).data[0]! = 58
#guard decodeClient (encodeClient (.io 5 zero (bytes []))) = none
#guard decodeClient (encodeClient (.winsize zero (2 ^ 31) 80)) = none

-- Unknown varint, fixed64, length-delimited, fixed32 and balanced group fields.
#guard decodeServer (bytes [120,1,26,1,120]) = some (.logId "x")
#guard decodeServer (bytes [121,0,0,0,0,0,0,0,0,26,1,120]) = some (.logId "x")
#guard decodeServer (bytes [122,2,255,255,26,1,120]) = some (.logId "x")
#guard decodeServer (bytes [125,0,0,0,0,26,1,120]) = some (.logId "x")
#guard decodeServer (bytes [123,8,1,124,26,1,120]) = some (.logId "x")
#guard decodeServer (bytes [123,115,8,1,116,124,26,1,120]) = some (.logId "x")
-- Unknown fields within known messages are skipped too.
#guard decodeServer (bytes [18,6,8,1,120,9,16,2]) = some (.commit ⟨1,2⟩)
-- Scalar last-wins and embedded-message merge semantics.
#guard decodeServer (bytes [18,6,8,1,8,2,16,3]) = some (.commit ⟨2,3⟩)
#guard decodeServer (bytes [18,2,8,1,18,2,16,2]) = some (.commit ⟨1,2⟩)
#guard decodeServer (bytes [26,1,120,34,1,121]) = some (.error "y")
#guard decodeServer (bytes [26,1,120,26,1,121]) = some (.logId "y")
#guard decodeClient (bytes [106,3,10,1,120,106,3,10,1,121]) = some (.hello "y")
-- Repeated number lists accept both protobuf representations, including mixed.
#guard decodeClient (bytes [10,12,18,10,10,1,107,42,5,8,1,10,1,2]) =
  some (.accept zero [⟨"k", .numbers [1,2]⟩] false)
#guard decodeClient (bytes [10,11,18,9,10,1,107,34,4,10,0,10,0]) =
  some (.accept zero [⟨"k", .strings ["", ""]⟩] false)

-- Malformed framing-independent protobuf bodies fail closed.
#guard decodeClient (bytes []) = none
#guard decodeServer (bytes []) = none
#guard decodeServer (bytes [0]) = none
#guard decodeServer (bytes [26,2,120]) = none
#guard decodeServer (bytes [26,1,255]) = none
#guard decodeServer (bytes [26,2,192,128]) = none
#guard decodeServer (bytes [26,1,120,0]) = none
#guard decodeServer (bytes [24,1]) = none
#guard decodeServer (bytes [18,2,10,0]) = none
#guard decodeServer (bytes [122,4,0]) = none
#guard decodeServer (bytes [121,0]) = none
#guard decodeServer (bytes [125,0]) = none
#guard decodeServer (bytes [123,8,1]) = none
#guard decodeServer (bytes [123,8,1,116]) = none
#guard decodeServer (bytes [124]) = none
#guard decodeServer (bytes [126]) = none
#guard decodeServer (bytes [127]) = none
#guard decodeServer (bytes [128,128,128,128,16,0]) = none
#guard decodeServer (bytes [120,0]) = none
#guard decodeClient (bytes [106,3,10,1,255]) = none
#guard decodeClient (bytes [90,6,16,255,255,255,255,15]) = none
-- Invalid earlier oneof alternatives are not hidden by later valid alternatives.
#guard decodeServer (bytes [26,1,255,34,1,120]) = none

-- Production-size I/O chunks exercise the direct ByteArray append path and
-- multi-byte lengths without converting payload bytes into encoder list cells.
private def largeIo : ByteArray := ⟨Array.replicate 65536 255⟩
#guard decodeClient (encodeClient (.io 1 clock largeIo)) = some (.io 1 clock largeIo)

example (n : Nat) (rest : List UInt8) (bound : n < 2 ^ 64) :
    Wire.varint (Wire.encNat n ++ rest) = some (n, rest) := Wire.varint_uint64 n rest bound
example (s : String) : Wire.asString (.bytes s.toUTF8.data.toList) = some s :=
  Wire.asString_utf8 s

example (s : String) (bound : s.toUTF8.size + 11 < 2 ^ 64) :
    decodeClient (encodeClient (.hello s)) = some (.hello s) :=
  clientHello_roundtrip s bound
example (s : String) (bound : s.toUTF8.size < 2 ^ 64) :
    decodeServer (encodeServer (.abort s)) = some (.abort s) :=
  abort_roundtrip s bound
example (t : TimeSpec) (slo : -(2 ^ 63) ≤ t.seconds) (shi : t.seconds < 2 ^ 63)
    (nlo : -(2 ^ 31) ≤ t.nanoseconds) (nhi : t.nanoseconds < 2 ^ 31) :
    decodeServer (encodeServer (.commit t)) = some (.commit t) :=
  commit_roundtrip t slo shi nlo nhi

example (n : Nat) (rest : List UInt8) :
    Wire.decNat (Wire.encNat n ++ rest) = some (n, rest) := Wire.decNat_encNat n rest
example (expect : Bool) : decodeClient (encodeClient (.accept zero [] expect)) =
    some (.accept zero [] expect) := accept_zero_roundtrip expect
example (stream : Fin 5) :
    decodeClient (encodeClient (.io stream.val zero ⟨#[0,128,255]⟩)) =
      some (.io stream.val zero ⟨#[0,128,255]⟩) := io_stream_roundtrip stream

-- Endpoint syntax and service defaults used by the real transport client.
#guard LeanSudo.Sys.LogSrv.endpoint "logs.example" = some ("logs.example", "30343", false)
#guard LeanSudo.Sys.LogSrv.endpoint "logs.example(tls)" = some ("logs.example", "30344", true)
#guard LeanSudo.Sys.LogSrv.endpoint "logs.example:1234" = some ("logs.example", "1234", false)
#guard LeanSudo.Sys.LogSrv.endpoint "[2001:db8::1]:1234(tls)" =
  some ("2001:db8::1", "1234", true)
#guard LeanSudo.Sys.LogSrv.endpoint "[::1]" = some ("::1", "30343", false)
#guard LeanSudo.Sys.LogSrv.endpoint "[::1](tls)" = some ("::1", "30344", true)
#guard LeanSudo.Sys.LogSrv.endpoint "logs.example:0" = none
#guard LeanSudo.Sys.LogSrv.endpoint "logs.example:65536" = none
#guard LeanSudo.Sys.LogSrv.endpoint "2001:db8::1" = none
#guard LeanSudo.Sys.LogSrv.endpoint ":30343" = none
#guard LeanSudo.Sys.LogSrv.endpoint "[::1" = none

end Tests.LogSrv
