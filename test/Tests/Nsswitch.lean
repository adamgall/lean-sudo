import LeanSudo.Nsswitch

open LeanSudo.Nsswitch

private def names (text : String) : Option (List String) :=
  (configure text).toOption.map (List.map (·.name))

-- Missing, empty, and unsupported-only configurations all default to files.
#guard names "" == some ["files"]
#guard names "passwd: files sss\ngroup: files ldap\n# sudoers: sss\n" == some ["files"]
#guard names " \tSuDoErS:\tFiLeS  # local policy\r\n" == some ["files"]
#guard names "sudoers: files files FILES" == some ["files"]
#guard names "sudoers:" == some ["files"]
#guard names "sudoers: # no sources" == some ["files"]
#guard names "sudoers: ldap" == some ["files"]
#guard names "sudoers: custom_backend ldap" == some ["files"]
#guard names "sudoers: files ldap" == some ["files"]
#guard names "sudoers: ldap files custom_backend" == some ["files"]

-- A supported but unavailable source never causes a local-policy fallback.
#guard names "sudoers: sss" == some ["sss"]
#guard names "sudoers: LDAP SSS custom_backend" == some ["sss"]
#guard names "sudoers: files sss" == some ["files", "sss"]
#guard names "sudoers: sss files" == some ["sss", "files"]

-- Only the first exact, case-insensitive sudoers: entry is considered.
#guard names "sudoers: files\nsudoers: sss\n" == some ["files"]
#guard names "sudoers: sss\nsudoers: files\n" == some ["sss"]
#guard names "sudoers: ldap\nsudoers: sss\n" == some ["files"]
#guard names "sudoers : sss\nsudoers: files" == some ["files"]
#guard names "sudoers_extra: sss\n" == some ["files"]

-- Only the next recognized return action attaches to a newly added source.
#guard (configure "sudoers: files [success=RETURN]").toOption ==
  some [{ name := "files", returnIfFound := true }]
#guard (configure "sudoers: files [NOTFOUND=return]").toOption ==
  some [{ name := "files", returnIfNotFound := true }]
#guard (configure "sudoers: files [SUCCESS=return] [NOTFOUND=return]").toOption ==
  some [{ name := "files", returnIfFound := true }]
#guard names "sudoers: [SUCCESS=return]" == some ["files"]
#guard (configure "sudoers: files ldap [NOTFOUND=return] sss").toOption ==
  some [{ name := "files" }, { name := "sss" }]
#guard (configure "sudoers: files files [SUCCESS=return] sss").toOption ==
  some [{ name := "files" }, { name := "sss" }]
#guard (configure "sudoers: sss [SUCCESS=return] ldap files").toOption ==
  some [{ name := "sss", returnIfFound := true }, { name := "files" }]
#guard names "sudoers: files [SUCCESS=return sss]" == some ["files"]
#guard names "sudoers: files [SUCCESS=return" == some ["files"]
#guard (configure "sudoers: files [SUCCESS=continue] [NOTFOUND=return]").toOption ==
  some [{ name := "files" }]
#guard names "sudoers: files [UNAVAIL=return]" == some ["files"]

-- sudo_parseln strips indentation on continued lines, not token boundaries.
#guard names "sudoers: fi\\\n  les\n" == some ["files"]
#guard names "sudoers: files \\\n \tsss\n" == some ["files", "sss"]
#guard names "sudoers: files \\\r\n ldap\r\n" == some ["files"]
#guard names "sudoers: files # ignored \\\nsudoers: sss\n" == some ["files"]
#guard names "sudoers: files # sss" == some ["files"]
#guard names "sudoers: files \\\\\n" == some ["files"]
#guard names "sudoers: files\\\n" == some ["files"]
#guard !(configure "sudoers: files\x00 sss").isOk
#guard names "sudoers:\x0bfiles" == some ["files"]

example (text : String) (sources : List Source)
    (configured : configure text = .ok sources) :
    sources ≠ [] ∧ ∀ source ∈ sources, source.name = "files" ∨ source.name = "sss" :=
  approve_supported_only text sources configured

example (text : String) (sources : List Source)
    (configured : configure text = .ok sources) :
    ∀ source ∈ sources, source.name ≠ "ldap" := by
  intro source hs ldap
  have supported := (approve_supported_only text sources configured).2 source hs
  rcases supported with h | h <;> simp_all

#guard approveSources ["ldap", "sss", "unknown"] == [{ name := "sss" }]
