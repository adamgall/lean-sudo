import LeanSudo.Sudoedit.Check

open LeanSudo.Sudoedit

#guard pathParts "/etc/henryfile" == some (["etc"], "henryfile")
#guard pathParts "/newfile" == some ([], "newfile")
#guard pathParts "relative" == none
#guard pathParts "/etc/../shadow" == some (["etc", ".."], "shadow")
#guard pathParts "/etc/./shadow" == some (["etc", "."], "shadow")
#guard pathParts "/etc/" == some (["etc"], ".")
#guard pathParts "/etc/a\x00b" == none
#guard editorArgsSafe ["/usr/bin/vi", "-n"]
#guard !editorArgsSafe []
#guard !editorArgsSafe ["/usr/bin/vi", "--", "/etc/shadow"]
#guard !editorArgsSafe ["/usr/bin/vi\x00evil"]
#guard selectEditor [(["bad"], none), (["good", "-n"], some "/usr/bin/good"),
  (["later"], some "/bin/later")] == some ("/usr/bin/good", ["good", "-n"])
#guard selectEditor [(["bad"], none)] == none
#guard selectEditor [] == none
#guard writeBack true true
#guard !writeBack false true
#guard !writeBack true false
#guard !writeBack false false
#guard tempSafe true true true
#guard !tempSafe false true true
#guard !tempSafe true false true
#guard !tempSafe true true false
#guard tempName "nginx.conf" == "nginxXXXXXXXX.conf"
#guard tempName "archive.tar.gz" == "archive.tarXXXXXXXX.gz"
#guard tempName ".profile" == "XXXXXXXX.profile"
#guard tempName "file" == "file.XXXXXXXX"
#guard tempName "file." == "fileXXXXXXXX."
#guard editorWords "  vi\t-n " == ["vi", "-n"]
#guard editorWords "'/home/a b/editor' \"two words\" a\\ b" ==
  ["/home/a b/editor", "two words", "a b"]
#guard editorWords "vi 'a\\'b' a\"b x\\\\y" == ["vi", "a'b", "a\"b", "x\\y"]
#guard editorWords "vi 'unclosed word" == ["vi", "'unclosed", "word"]
#guard editorWords "vi 'first'second ''" == ["vi", "first", "second", ""]
#guard editorWords "vi '\\-\\-' /etc/shadow" == ["vi", "--", "/etc/shadow"]
#guard !editorArgsSafe (editorWords "vi '\\-\\-' /etc/shadow")
#guard !fileChanged #[0, 0, 0, 3, 12, 34] #[0, 0, 0, 3, 12, 34] true
#guard fileChanged #[0, 0, 0, 3, 12, 34] #[0, 0, 0, 4, 12, 34] true
#guard fileChanged #[0, 0, 0, 3, 12, 34] #[0, 0, 0, 3, 12, 35] true
#guard fileChanged #[0, 0, 0, 3, 12, 34] #[0, 0, 0, 3, 13, 34] true
#guard fileChanged #[0, 0, 0, 3, 12, 34] #[0, 0, 0, 3, 12, 34] false
