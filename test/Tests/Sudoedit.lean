import LeanSudo.Sudoedit.Check

open LeanSudo.Sudoedit

#guard pathParts "/etc/henryfile" == some (["etc"], "henryfile")
#guard pathParts "/newfile" == some ([], "newfile")
#guard pathParts "relative" == none
#guard pathParts "/etc/../shadow" == none
#guard pathParts "/etc/./shadow" == none
#guard pathParts "/etc/" == none
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
