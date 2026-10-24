import LeanSudo.Timestamp

/-! Compile-time tests for `LeanSudo.Timestamp`. -/

namespace Tests.Timestamp
open LeanSudo LeanSudo.Timestamp

def sec : Nat := 10 ^ 9

def ttyS : Scope := .tty 34817 4242 99887
def ppidS : Scope := .ppid 4243 99890

def r1 : Record := { scope := ttyS, authUid := 1000, time := 500 * sec, disabled := false }
def r2 : Record := { scope := ppidS, authUid := 1000, time := 10 * sec, disabled := true }
def r3 : Record := { scope := .global, authUid := 0, time := 2 ^ 70, disabled := false }

/-! ### scopeFor -/
#guard scopeFor .tty (some 7) 1 2 3 4 = .tty 7 1 2
#guard scopeFor .tty none 1 2 3 4 = .ppid 3 4
#guard scopeFor .kernel (some 7) 1 2 3 4 = .tty 7 1 2
#guard scopeFor .kernel none 1 2 3 4 = .ppid 3 4
#guard scopeFor .ppid (some 7) 1 2 3 4 = .ppid 3 4
#guard scopeFor .global (some 7) 1 2 3 4 = .global
#guard scopeFor .kernel (some 7) 1 2 3 4 = scopeFor .kernel (some 7) 1 2 5 6

/-! ### validity -/
-- exactly at the timeout boundary: valid; one nanosecond later: expired
#guard lookup (500 * sec + 900 * sec) (some 900) ttyS 1000 [r1]
#guard !lookup (500 * sec + 900 * sec + 1) (some 900) ttyS 1000 [r1]
-- never expires
#guard lookup (10 ^ 30) none ttyS 1000 [r1]
-- timeout 0: never cached
#guard !lookup (500 * sec) (some 0) ttyS 1000 [r1]
-- future record
#guard !lookup (500 * sec - 1) (some 900) ttyS 1000 [r1]
#guard !lookup (500 * sec - 1) none ttyS 1000 [r1]
-- wrong uid / scope / start time / tty
#guard !lookup (501 * sec) (some 900) ttyS 0 [r1]
#guard !lookup (501 * sec) (some 900) ppidS 1000 [r1]
#guard !lookup (501 * sec) (some 900) (.tty 34817 4242 99888) 1000 [r1]
#guard !lookup (501 * sec) (some 900) (.tty 34818 4242 99887) 1000 [r1]
#guard !lookup (501 * sec) (some 900) .global 1000 [r1]
-- disabled
#guard !lookup (11 * sec) none ppidS 1000 [r2]
#guard !lookup (11 * sec) none ppidS 1000 []

/-! ### update / invalidate -/
#guard lookup (20 * sec) (some 5) ppidS 1000 (update (20 * sec) ppidS 1000 [r1, r2, r3])
#guard (update (20 * sec) ppidS 1000 [r1, r2, r3]).length = 3
#guard (update (20 * sec) ppidS 1000 [r1, r2, r3]).head? =
  some { scope := ppidS, authUid := 1000, time := 20 * sec, disabled := false }
-- updating another uid in the same scope does not grant this uid
#guard !lookup (20 * sec) none ppidS 1000 (update (20 * sec) ppidS 0 [r2])
#guard lookup (501 * sec) (some 900) ttyS 1000 (update (501 * sec) ppidS 1000 [r1])
#guard !lookup (501 * sec) none ttyS 1000 (invalidate [r1, r2, r3])
#guard !lookup (2 ^ 70) none .global 0 (invalidate [r1, r2, r3])
#guard !lookup (501 * sec) none ttyS 1000 (invalidateScope ttyS [r1, r2, r3])
#guard lookup (501 * sec) none ttyS 1000 (invalidateScope ppidS [r1, r2, r3])
-- the record count is bounded
#guard (update 0 .global 0 ((List.range 300).map fun i =>
  { scope := .ppid i 0, authUid := 0, time := 0, disabled := false })).length = maxRecords

example (rs : List Record) (now : Nat) : lookup now none .global 0 (invalidate rs) = false :=
  lookup_invalidate _ _ _ _ _

/-! ### encoding -/
#guard decode (encode []) = some []
#guard decode (encode [r1, r2, r3]) = some [r1, r2, r3]
#guard load (encode [r1, r2, r3]) = [r1, r2, r3]
#guard encodeList [] = [0x4C, 0x53, 0x54, 0x53, 0x01, 0x00]
#guard encNat 300 = [0xAC, 0x02]
#guard decode ByteArray.empty = none
#guard load ByteArray.empty = []
-- bad magic / version
#guard decode ⟨#[0x4C, 0x53, 0x54, 0x53, 0x02, 0x00]⟩ = none
-- trailing garbage
#guard decode ⟨#[0x4C, 0x53, 0x54, 0x53, 0x01, 0x00, 0x00]⟩ = none
-- truncated record
#guard decode ⟨(encodeList [r1]).dropLast.toArray⟩ = none
-- count larger than the records present
#guard decode ⟨#[0x4C, 0x53, 0x54, 0x53, 0x01, 0x05]⟩ = none
-- invalid disabled byte / scope tag
#guard decodeList (magic ++ [1, 2, 0, 0, 7]) = none
#guard decodeList (magic ++ [1, 9, 0, 0, 0]) = none
#guard decodeList (magic ++ [1, 2, 0, 0, 1]) =
  some [{ scope := .global, authUid := 0, time := 0, disabled := true }]

example : ∀ rs, decode (encode rs) = some rs := decode_encode

/-! ### /proc/<pid>/stat parsing -/
def statLine (comm : String) : List UInt8 :=
  (s!"1234 ({comm}) S 1 1234 1234 34817 1234 4194560 100 0 0 0 1 2 0 0 20 0 1 0 " ++
    "987654 1000 200 18446744073709551615").toUTF8.data.toList

#guard statField (statLine "bash") 22 = some 987654
#guard statField (statLine "bash") 7 = some 34817
#guard statField (statLine "bash") 4 = some 1
#guard statField (statLine "evil) S 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1") 22 = some 987654
#guard statField (statLine "a b (c)") 22 = some 987654
#guard statField (statLine "x") 3 = none   -- state is not numeric
#guard statField (statLine "x") 99 = none
#guard statField "no paren here".toUTF8.data.toList 22 = none

/-! ### tty_nr → dev_t -/
#guard ttyNrToDev 34817 = 34817            -- pts/1 (136, 1)
#guard ttyNrToDev 1083436 = 1083436        -- pts/300
#guard ttyNrToDev 1025 = 1025              -- tty1 (4, 1)

end Tests.Timestamp
