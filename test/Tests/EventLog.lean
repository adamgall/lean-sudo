import LeanSudo.EventLog

/-! Pure regression guards for sudo 1.9.17p2 event formatting.
The long logfile fixtures are from upstream lib/eventlog/regress/logwrap.
No syslog/file I/O or locale-dependent timestamp conversion is performed. -/
namespace Tests.EventLog

open LeanSudo.EventLog

private def textRecords (user message : String) (maxlen : Nat) : List (Option String) :=
  (splitSyslogBytes user message maxlen).map String.fromUTF8?

#guard messageBody "alice" "alice : TTY=pts/1 ; COMMAND=/bin/id" ==
  "TTY=pts/1 ; COMMAND=/bin/id"
#guard messageBody "alice" "bob : COMMAND=/bin/id" == "bob : COMMAND=/bin/id"
#guard messageBody "alice" "alice :  COMMAND=x " == " COMMAND=x "
#guard messageBody "é" "é : COMMAND=x" == "COMMAND=x"

#guard splitSyslogBytes "alice" "" 960 == []
#guard textRecords "alice" "TTY=pts/1 ; COMMAND=/bin/id" 960 ==
  [some "   alice : TTY=pts/1 ; COMMAND=/bin/id"]
#guard textRecords "longusername" "COMMAND=x" 960 ==
  [some "longusername : COMMAND=x"]
-- printf's width counts bytes, including UTF-8 bytes in the user name.
#guard textRecords "é" "COMMAND=x" 960 == [some "      é : COMMAND=x"]

-- Upstream does not subtract the padding of a short username from its budget.
#guard textRecords "alice" "abcdefghijklmnopqrstuvwxYZ" 32 ==
  [some "   alice : abcdefghijklmnopqrstuvwx", some "   alice : (command continued) YZ"]
#guard (splitSyslogBytes "alice" "abcdefghijklmnopqrstuvwxYZ" 32).map (·.size) == [35, 33]

#guard textRecords "abcdefgh" "one two three four five six seven eight nine" 40 ==
  [some "abcdefgh : one two three four five six",
   some "abcdefgh : (command continued) seven",
   some "abcdefgh : (command continued) eight",
   some "abcdefgh : (command continued) nine"]
-- Spaces at a split are skipped, but spaces elsewhere are left unchanged.
#guard textRecords "abcdefgh" "one  two three four five six   seven" 41 ==
  [some "abcdefgh : one  two three four five six ",
   some "abcdefgh : (command continued) seven"]
-- The space at the byte limit is excluded from syslog's backward search.
#guard textRecords "abcdefgh" "abcdefghijklmno abcdefghijklm tail" 40 ==
  [some "abcdefgh : abcdefghijklmno",
   some "abcdefgh : (command continued) abcdefghi",
   some "abcdefgh : (command continued) jklm tail"]
#guard textRecords "abcdefgh" "abc\tdef" 40 == [some "abcdefgh : abc\tdef"]

-- Hard splitting a multibyte character must retain both bytes, not U+FFFD.
private def multibyteWord : String := String.ofList (List.replicate 23 'a') ++ "é"
private def firstBytes : ByteArray :=
  ("   alice : " ++ String.ofList (List.replicate 23 'a')).toUTF8.push 0xc3
private def continuedBytes : ByteArray := "   alice : (command continued) ".toUTF8.push 0xa9
#guard splitSyslogBytes "alice" multibyteWord 32 == [firstBytes, continuedBytes]
#guard textRecords "alice" multibyteWord 32 == [none, none]
#guard firstBytes.extract 11 firstBytes.size ++ continuedBytes.extract 31 continuedBytes.size ==
  multibyteWord.toUTF8

-- A tiny budget must not loop forever or silently lose the message.
#guard textRecords "alice" "COMMAND=x" 8 == [some "   alice : COMMAND=x"]
#guard textRecords "alice" "COMMAND=x" 0 == [some "   alice : COMMAND=x"]

#guard formatFile "Oct 24 12:34:56" "host" "alice" "COMMAND=/bin/id" false 0 ==
  "Oct 24 12:34:56 : alice : COMMAND=/bin/id\n"
#guard formatFile "Oct 24 12:34:56" "host" "alice" "COMMAND=/bin/id" true 0 ==
  "Oct 24 12:34:56 : alice : HOST=host ; COMMAND=/bin/id\n"
#guard formatFile "invalid date" "ignored" "alice" "denied ; COMMAND=x" false 0 ==
  "invalid date : alice : denied ; COMMAND=x\n"

#guard wrapFileLine "" 0 == "\n"
#guard wrapFileLine "" 5 == ""
#guard wrapFileLine "abcde f" 4 == "abcde f\n"
#guard wrapFileLine "abcde f" 5 == "abcde\n    f\n"
#guard wrapFileLine "abcdef gh" 5 == "abcdef\n    gh\n"
#guard wrapFileLine " abcdef gh" 5 == " abcdef\n    gh\n"
#guard wrapFileLine "abcde   " 5 == "abcde\n"
#guard wrapFileLine "abc\tdef ghi" 5 == "abc\tdef\n    ghi\n"
#guard wrapFileLine "abc  def" 80 == "abc  def\n"
#guard wrapFileLine "éé a" 5 == "éé\n    a\n"
#guard wrapFileLine "éé a" 6 == "éé a\n"
#guard wrapFileLine "ééé a" 5 == "ééé\n    a\n"
#guard wrapFileLine "COMMAND=/a/very/long/unbroken/path" 5 ==
  "COMMAND=/a/very/long/unbroken/path\n"

private def deniedBody : String :=
  "command not allowed ; TTY=pts/1 ; PWD=/home/tu2sp3-a ; USER=root ; COMMAND=/opt/quest/bin/vastool list users"

#guard formatFile "Jul 11 11:30:17" "" "tu2sp3-a" deniedBody false 60 ==
  "Jul 11 11:30:17 : tu2sp3-a : command not allowed ; TTY=pts/1\n    ; PWD=/home/tu2sp3-a ; USER=root ;\n    COMMAND=/opt/quest/bin/vastool list users\n"
#guard formatFile "Jul 11 11:30:17" "" "tu2sp3-a" deniedBody false 67 ==
  "Jul 11 11:30:17 : tu2sp3-a : command not allowed ; TTY=pts/1 ;\n    PWD=/home/tu2sp3-a ; USER=root ; COMMAND=/opt/quest/bin/vastool\n    list users\n"
#guard formatFile "Jul 11 11:30:17" "" "tu2sp3-a" deniedBody false 140 ==
  "Jul 11 11:30:17 : tu2sp3-a : command not allowed ; TTY=pts/1 ; PWD=/home/tu2sp3-a ; USER=root ; COMMAND=/opt/quest/bin/vastool list users\n"

private def acceptedBody : String :=
  "TTY=ttypm ; PWD=/usr/src/local/millert/hg/sudo/build ; USER=root ; TSID=0004KT ; COMMAND=/bin/rm /root/.bash_profile"

#guard formatFile "Jun 26 18:00:06" "" "millert" acceptedBody false 60 ==
  "Jun 26 18:00:06 : millert : TTY=ttypm ;\n    PWD=/usr/src/local/millert/hg/sudo/build ; USER=root ;\n    TSID=0004KT ; COMMAND=/bin/rm /root/.bash_profile\n"
#guard formatFile "Jun 26 18:00:06" "" "millert" acceptedBody false 80 ==
  "Jun 26 18:00:06 : millert : TTY=ttypm ; PWD=/usr/src/local/millert/hg/sudo/build\n    ; USER=root ; TSID=0004KT ; COMMAND=/bin/rm /root/.bash_profile\n"

#guard jsonQuote "\"\\/\x08\x0c\n\r\t\x01\x1f\x7fé" ==
  "\"\\\"\\\\/\\b\\f\\n\\r\\t\\u0001\\u001f\\u007fé\""

private def clock : Time := { seconds := 1, nanoseconds := 2, iso8601 := "19700101000001Z", localtime := "Jan  1 00:00:01" }
private def accepted : Event := {
  kind := .accept, uuid := "id", serverTime := clock, eventTime := some clock,
  details := some {
    submituser := "alice", command := some "/bin/echo",
    runuser := some "root", runuid := some 0, runargv := some ["/bin/echo", "a\n\"b"],
    submitenv := some [] } }

#guard formatJsonLine accepted ==
  "{\"accept\":{\"uuid\":\"id\",\"server_time\":{\"seconds\":1,\"nanoseconds\":2,\"iso8601\":\"19700101000001Z\",\"localtime\":\"Jan  1 00:00:01\"},\"submit_time\":{\"seconds\":1,\"nanoseconds\":2,\"iso8601\":\"19700101000001Z\",\"localtime\":\"Jan  1 00:00:01\"},\"submituser\":\"alice\",\"command\":\"/bin/echo\",\"runuser\":\"root\",\"runuid\":0,\"columns\":80,\"lines\":24,\"runargv\":[\"/bin/echo\",\"a\\n\\\"b\"],\"submitenv\":[]}}\n"
#guard formatJsonSyslog accepted ==
  "@cee:{\"sudo\":{" ++ formatJsonMember accepted true ++ "}}"
#guard formatJsonMember {
    kind := .alert, reason := some "failure", error := some "error",
    serverTime := {}, eventTime := some {} } false ==
  "\n    \"alert\": {\n        \"reason\": \"failure: error\",\n        \"server_time\": {\n            \"seconds\": 0,\n            \"nanoseconds\": 0\n        },\n        \"alert_time\": {\n            \"seconds\": 0,\n            \"nanoseconds\": 0\n        }\n    }"
#guard (Event.fields { accepted with kind := .reject, reason := some "command not allowed" }).map (·.1) ==
  ["uuid", "reason", "server_time", "submit_time", "submituser", "command", "runuser",
   "runuid", "columns", "lines", "runargv", "submitenv"]
#guard (Event.fields { accepted with
    kind := .exit, exitValue := 143, signal := some "TERM",
    runTime := some { seconds := 3 } }).map (·.1) ==
  ["uuid", "server_time", "exit_time", "run_time", "signal", "dumped_core", "exit_value",
   "run_time", "signal", "dumped_core", "exit_value"]
#guard formatJsonLine { kind := .exit, serverTime := {}, exitValue := 1 } ==
  "{\"exit\":{\"server_time\":{\"seconds\":0,\"nanoseconds\":0},\"exit_value\":1,\"exit_value\":1}}\n"
#guard (Details.fields { submituser := "a", rungid := some 5 }).map (·.1) ==
  ["submituser", "columns", "lines"]
#guard (Details.fields {
    submituser := "a", rungroup := some "g", rungid := some 5,
    runuid := some 6, runchroot := some "/", runcwd := some "/tmp", source := some "p:1:2",
    ttyname := some "/dev/pts/1", submithost := some "h", submitcwd := some "/home/a",
    runenv := some [], runargv := some [], submitenv := some [] }).map (·.1) ==
  ["submituser", "rungroup", "runchroot", "runcwd", "source", "ttyname", "submithost",
   "submitcwd", "rungid", "runuid", "columns", "lines", "runargv", "runenv", "submitenv"]

#guard logAuthFailure true true false { attempts := 1 }
#guard !(logAuthFailure true true false {})
#guard !(logAuthFailure false true false { attempts := 3 })
#guard !(logAuthFailure true false false { attempts := 3 })
#guard logAuthFailure true true false { noInput := true }
#guard !(logAuthFailure true true true { noInput := true })
#guard mailAuthFailure true true false false false {}
#guard !(mailAuthFailure true true true false true { noInput := true })
#guard !(mailAuthFailure false true true true false { attempts := 3 })
#guard mailAuthFailure false true false false false { attempts := 3 }
#guard fileAuthFailure false {}
#guard !(fileAuthFailure true { noInput := true })

end Tests.EventLog
