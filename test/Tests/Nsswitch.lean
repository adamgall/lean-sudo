import LeanSudo.Nsswitch

open LeanSudo.Nsswitch

private def diagnostic : Except String Unit → String
  | .error message => message
  | .ok () => ""

-- Missing configuration / missing entry defaults to the local backend.
#guard (parse "").toOption == some ["files"]
#guard (approve "").isOk
#guard (approve "passwd: files sss\ngroup: files ldap\n# sudoers: sss\n").isOk
#guard (approve "sudoers: files\n").isOk
#guard (parse " \tSuDoErS:\tFiLeS  # local policy\r\n").toOption == some ["files"]
#guard (approve "sudoers: files files FILES").isOk

-- Never consult files when the explicit entry omits it, or drop a remote source.
#guard !(approve "sudoers:").isOk
#guard !(approve "sudoers: # no sources").isOk
#guard !(approve "sudoers: sss").isOk
#guard !(approve "sudoers: ldap").isOk
#guard !(approve "sudoers: custom_backend").isOk
#guard !(approve "sudoers: files sss").isOk
#guard !(approve "sudoers: sss files").isOk
#guard !(approve "sudoers: files ldap").isOk
#guard !(approve "sudoers: files custom_backend").isOk
#guard diagnostic (approve "sudoers: SSS") ==
  "/etc/nsswitch.conf: unsupported sudoers source: sss"
#guard diagnostic (approve "sudoers:") ==
  "/etc/nsswitch.conf: sudoers entry has no files source"

-- Upstream only considers the first exact, case-insensitive sudoers: entry.
#guard (approve "sudoers: files\nsudoers: sss\n").isOk
#guard !(approve "sudoers: sss\nsudoers: files\n").isOk
#guard (approve "sudoers : sss\nsudoers: files").isOk
#guard (approve "sudoers_extra: sss\n").isOk

-- Return clauses are not sources; no return clause hides an unsupported source.
#guard (parse "sudoers: files [SUCCESS=return]").toOption == some ["files"]
#guard (approve "sudoers: files [NOTFOUND=return]").isOk
#guard (approve "sudoers: files [success=RETURN]").isOk
#guard (approve "sudoers: files [SUCCESS=return] [NOTFOUND=return]").isOk
#guard (approve "sudoers: [SUCCESS=return] files").isOk
#guard !(approve "sudoers: [SUCCESS=return]").isOk
#guard !(approve "sudoers: files [SUCCESS=return] sss").isOk
#guard !(approve "sudoers: files [NOTFOUND=return] ldap").isOk
#guard !(approve "sudoers: sss [SUCCESS=return] files").isOk
#guard !(approve "sudoers: files [SUCCESS=return sss]").isOk
#guard !(approve "sudoers: files [SUCCESS=return").isOk
#guard !(approve "sudoers: files [SUCCESS=continue]").isOk
#guard !(approve "sudoers: files [UNAVAIL=return]").isOk
#guard diagnostic (approve "sudoers: files [SUCCESS=continue]") ==
  "/etc/nsswitch.conf: unsupported sudoers action: [success=continue]"

-- sudo_parseln strips leading space/tab on every continued physical line,
-- preserves whitespace before the backslash, and does not continue comments.
#guard (parse "sudoers: fi\\\n  les\n").toOption == some ["files"]
#guard !(approve "sudoers: files \\\n \tsss\n").isOk
#guard !(approve "sudoers: files \\\r\n ldap\r\n").isOk
#guard (approve "sudoers: files # ignored \\\nsudoers: sss\n").isOk
#guard (approve "sudoers: files # sss").isOk
#guard !(approve "sudoers: files \\\\\n").isOk
#guard (approve "sudoers: files\\\n").isOk
#guard !(approve "sudoers: files\x00 sss").isOk
#guard !(approve "sudoers:\x0bfiles").isOk

example (text : String) (sources : List String)
    (parsed : parse text = .ok sources) (approved : approve text = .ok ()) :
    ∀ source ∈ sources, source = "files" :=
  (approve_supported_only text sources parsed approved).2

example (text : String) (sources : List String)
    (parsed : parse text = .ok sources) (remote : "sss" ∈ sources) :
    approve text ≠ .ok () := by
  intro approved
  have h := (approve_supported_only text sources parsed approved).2 "sss" remote
  exact (by decide : ("sss" : String) ≠ "files") h
