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

end Tests.EventLog
