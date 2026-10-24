import LeanSudo.Util.Glob

/-! Compile-time tests for `LeanSudo.Glob.fnmatch`. -/

namespace Tests.Glob
open LeanSudo.Glob

-- literals
#guard fnmatch "" "" false
#guard !fnmatch "" "a" false
#guard fnmatch "/usr/bin/ls" "/usr/bin/ls" true
#guard !fnmatch "/usr/bin/ls" "/usr/bin/lsx" true
#guard !fnmatch "abc" "ABC" false
#guard fnmatch "abc" "ABC" false true

-- `*`
#guard fnmatch "*" "" false
#guard fnmatch "*" "a/b" false
#guard !fnmatch "*" "a/b" true
#guard fnmatch "/usr/bin/*" "/usr/bin/ls" true
#guard !fnmatch "/usr/bin/*" "/usr/bin/x/ls" true
#guard fnmatch "/usr/bin/*" "/usr/bin/x/ls" false
#guard fnmatch "/usr/*/ls" "/usr/bin/ls" true
#guard !fnmatch "/usr/*/ls" "/usr/a/b/ls" true
#guard fnmatch "a*b*c" "axxbyyc" false
#guard !fnmatch "a*b*c" "axxbyy" false
#guard fnmatch "*.txt" "a.txt" false
#guard fnmatch "**" "abc" false

-- `?`
#guard fnmatch "a?c" "abc" false
#guard !fnmatch "a?c" "ac" false
#guard fnmatch "a?c" "a/c" false
#guard !fnmatch "a?c" "a/c" true

-- brackets
#guard fnmatch "[abc]x" "bx" false
#guard !fnmatch "[abc]x" "dx" false
#guard !fnmatch "[!abc]x" "bx" false
#guard fnmatch "[^abc]x" "dx" false
#guard fnmatch "[a-z]*" "hello" false
#guard !fnmatch "[a-z]" "H" false
#guard fnmatch "[a-z]" "H" false true
#guard fnmatch "[]]" "]" false
#guard fnmatch "[!]]" "a" false
#guard !fnmatch "[!]]" "]" false
#guard fnmatch "[a\\]]" "]" false
#guard fnmatch "[a-]" "-" false
#guard fnmatch "[[:digit:]]*" "1abc" false
#guard !fnmatch "[[:digit:]]*" "abc" false
#guard fnmatch "[[:alpha:][:digit:]]" "7" false
#guard !fnmatch "[/]" "/" true
#guard fnmatch "[/]" "/" false
#guard !fnmatch "[!a]" "/" true
-- unterminated bracket is a literal `[`
#guard fnmatch "[" "[" false
#guard fnmatch "a[b" "a[b" false
#guard !fnmatch "a[b" "ab" false

-- escapes
#guard fnmatch "\\*" "*" false
#guard !fnmatch "\\*" "a" false
#guard fnmatch "a\\?" "a?" false
#guard fnmatch "trailing\\" "trailing\\" false

-- case-insensitive (host names)
#guard fnmatch "HOST*" "host1.example.com" false true
#guard fnmatch "web[0-9]" "WEB7" false true

-- `hasGlob`/`hasMeta`
#guard hasGlob "/usr/bin/*"
#guard !hasGlob "/usr/bin/ls"
#guard hasMeta "a\\b"

-- theorems applied
example : fnmatch "/usr/bin/ls" "/usr/bin/ls" true = true := by
  rw [fnmatch_literal _ _ _ (by decide)]; decide
example (s : String) : fnmatch "*" s false = true := fnmatch_star s
example : fnmatch "/usr/bin/*" "/usr/bin/a/b" true = false := by
  cases h : fnmatch "/usr/bin/*" "/usr/bin/a/b" true
  · rfl
  · have := (fnmatch_prefix_star_pathname "/usr/bin/" "/usr/bin/a/b" (by decide)).mp
      (by simpa using h)
    obtain ⟨t, ht, hslash⟩ := this
    have := congrArg String.toList ht
    simp only [String.toList_append] at this
    have ht' : t.toList = ['a', '/', 'b'] := by
      have e : "/usr/bin/a/b".toList = "/usr/bin/".toList ++ ['a', '/', 'b'] := by decide
      rw [e] at this
      exact (List.append_cancel_left this).symm
    simp [ht'] at hslash

end Tests.Glob
