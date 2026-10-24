import LeanSudo.IoLog

open LeanSudo LeanSudo.IoLog

private def fixture : Metadata := {
  user := "alice", group := "users", runasUser := "root", runasGroup := "root"
  hostname := "host", command := "/usr/bin/echo", cwd := "/home/alice"
  tty := "/dev/pts/0", argv := #["/usr/bin/echo", "hi"] }

#guard sequence 0 == "000000"
#guard sequence 1 == "000001"
#guard sequence 35 == "00000Z"
#guard sequence 36 == "000010"
#guard sequence 2176782335 == "ZZZZZZ"
#guard sequencePath 1 == "00/00/01"
#guard sequencePath 1296 == "00/01/00"
#guard nextSequence 99 100 == 100
#guard nextSequence 100 100 == 1
#guard nextSequence 0 0 == 1
#guard expandPath fixture "00/00/01" [] "%{seq}/%{user}/%{group}/%{runas_user}/%{runas_group}/%{hostname}/%{command}" ==
  "00/00/01/alice/users/root/root/host/echo"
#guard pathValue "foo/bar" == "foo_bar"
#guard expandPath fixture "" [("Y", "2026"), ("m", "10")] "%Y/%m/%%" == "2026/10/%"
#guard expandPath fixture "" [("EY", "2026"), ("Od", "24")] "%EY/%Od" == "2026/24"
#guard timingRecord 1 2 42 "3" == "1 2.000000042 3\n"
#guard timingRecord 5 0 0 "24 80" == "5 0.000000000 24 80\n"
#guard legacyLog fixture 123 == "123:alice:root:root:/dev/pts/0:24:80\n/home/alice\n/usr/bin/echo hi\n"
#guard (Lean.Json.parse (jsonLog fixture 123 456)).isOk
#guard ((jsonLog fixture 123 456).splitOn "\"nanoseconds\": 456\n").length == 2
#guard ((jsonLog fixture 123 456).splitOn "    \"/usr/bin/echo\",\n").length == 2
#guard (plan {} {}).isNone
#guard (plan {} { logOutput := some true }).isSome
#guard (plan { logOutput := true } { logOutput := some false }).isNone
#guard (plan { logStdin := true } {}).isSome
#guard ((plan {} { logInput := some true }).map (·.stdin)) == some true
#guard ((plan {} { logInput := some true }).map (·.stdout)) == some false
