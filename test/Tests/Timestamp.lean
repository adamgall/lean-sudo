import LeanSudo.Timestamp

/-! Compile-time tests for `LeanSudo.Timestamp`. -/

namespace Tests.Timestamp
open LeanSudo LeanSudo.Timestamp

def sec : Nat := 10 ^ 9

def ttyS : Scope := .tty 34817 4242 (99887 * 10000000)
def ppidS : Scope := .ppid 4243 (99890 * 10000000)

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
-- sudo expires at the exact timeout boundary.
#guard lookup (500 * sec + 900 * sec - 1) (some 900) ttyS 1000 [r1]
#guard !lookup (500 * sec + 900 * sec) (some 900) ttyS 1000 [r1]
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
#guard !lookup (501 * sec) (some 900) (.tty 34817 4242 (99888 * 10000000)) 1000 [r1]
#guard !lookup (501 * sec) (some 900) (.tty 34818 4242 (99887 * 10000000)) 1000 [r1]
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

/-! ### sudo 1.9.17p2 Ubuntu64 timestamp v2 encoding -/
#guard decode (encode []) = some []
#guard decode (encode [r1, r2, r3]) = some [r1, r2, r3]
#guard load (encode [r1, r2, r3]) = [r1, r2, r3]
#guard (encode []).size = 56
#guard (encode [r1, r2, r3]).size = 224
#guard encodeList [] = [2, 0, 56, 0, 4, 0] ++ List.replicate 50 0
#guard encNat 4 300 = [0x2c, 0x01, 0, 0]
#guard decode ByteArray.empty = none
#guard load ByteArray.empty = []
#guard decode ⟨(encodeList [r1] ++ [0]).toArray⟩ = none
#guard decode ⟨(encodeList [r1]).dropLast.toArray⟩ = none

-- Literal Linux LP64 struct fixture: uid=1000, sid=4242, ttydev=34817,
-- start={3,7}, timestamp={500,9}. No host ABI or encoder generates these bytes.
def ttyFixture : List UInt8 :=
  [2, 0, 56, 0, 2, 0, 0, 0, 232, 3, 0, 0, 146, 16, 0, 0,
   3, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0,
   244, 1, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0,
   1, 136, 0, 0, 0, 0, 0, 0]
def fixtureEntry : DiskEntry := ⟨2, 0, 1000, 4242, 3 * sec + 7, 500 * sec + 9, 34817⟩
#guard encEntry fixtureEntry = ttyFixture
#guard decodeEntry ⟨ttyFixture.toArray⟩ = some fixtureEntry
#guard decodeEntry (encodeEntry lockEntry) = some lockEntry
#guard decodeEntry ⟨(ttyFixture ++ [0]).toArray⟩ = none
#guard decodeEntry ⟨ttyFixture.dropLast.toArray⟩ = none
-- Bad version, wrong size, signed-negative seconds, nonnormalized nanoseconds.
#guard decodeEntry ⟨(ttyFixture.set 0 1).toArray⟩ = none
#guard decodeEntry ⟨(ttyFixture.set 2 48).toArray⟩ = none
#guard decodeEntry ⟨(ttyFixture.set 23 128).toArray⟩ = none
#guard decodeEntry ⟨(ttyFixture.set 39 128).toArray⟩ = none
#guard decodeEntry ⟨(ttyFixture.take 24 ++ encNat 8 sec ++ ttyFixture.drop 32).toArray⟩ = none
#guard decodeEntry ⟨(ttyFixture.take 40 ++ encNat 8 sec ++ ttyFixture.drop 48).toArray⟩ = none
#guard decodeEntry ⟨(ttyFixture.set 15 128).toArray⟩ = none

-- ANYUID is a property of the search key, not of an untrusted stored entry.
#guard fixtureEntry.matches (.tty 34817 9999 (3 * sec + 7)) 1000
#guard !fixtureEntry.matches (.tty 34817 4242 (3 * sec + 8)) 1000
#guard !fixtureEntry.matches (.tty 34818 4242 (3 * sec + 7)) 1000
#guard !fixtureEntry.matches (.ppid 34817 (3 * sec + 7)) 1000
#guard !({ fixtureEntry with flags := 2 }).matches (.tty 34817 4242 (3 * sec + 7)) 0
#guard fixtureEntry.matches (.tty 34817 4242 (3 * sec + 7)) 0 true
#guard ({ fixtureEntry with flags := 3 }).toRecord =
  some ⟨.tty 34817 4242 (3 * sec + 7), 1000, 500 * sec + 9, true⟩
#guard lockEntry.toRecord = none

-- Foreign records do not move the byte offsets used by POSIX record locks.
def foreignRecord : List UInt8 := [9, 0, 8, 0, 255, 255, 255, 255]
def mixedFile : ByteArray :=
  ⟨(encEntry lockEntry ++ foreignRecord ++ ttyFixture ++
    encEntry { fixtureEntry with kind := 99 } ++ encEntry (DiskEntry.ofRecord 4242 r2)).toArray⟩
#guard (scan mixedFile).map (·.offset) = [0, 64, 176]
#guard (scan mixedFile).map (·.entry.kind) = [4, 2, 3]
#guard (scan ⟨(foreignRecord ++ ttyFixture).toArray⟩).map (·.offset) = [8]
#guard (scan ⟨((foreignRecord.set 0 2) ++ ttyFixture).toArray⟩).map (·.offset) = [8]
#guard (scan ⟨((ttyFixture.set 0 1) ++ ttyFixture).toArray⟩).map (·.offset) = [56]
#guard (scan ⟨((ttyFixture.set 4 99) ++ ttyFixture).toArray⟩).map (·.offset) = [56]
#guard scan ⟨#[2, 0, 0, 0]⟩ = []
#guard scan ⟨#[2, 0, 3, 0]⟩ = []
#guard scan ⟨#[2, 0, 56, 0]⟩ = []
#guard scan ⟨(foreignRecord ++ ttyFixture.dropLast).toArray⟩ = []
#guard scan ⟨((ttyFixture.set 23 128) ++ ttyFixture).toArray⟩ = []
#guard loadFor 4242 mixedFile =
  [⟨.tty 34817 4242 (3 * sec + 7), 1000, 500 * sec + 9, false⟩, r2]
#guard loadFor 4243 mixedFile = []
#guard loadFor 999 (encode [r3]) = [r3]
#guard loadFor 0 (encode [r1, r2, r3]) = [r2, r3]

-- The real finite-width boundary is seconds (signed 64), not nanoseconds.
def largestTime : Nat := (2 ^ 63 - 1) * sec + (sec - 1)
#guard decodeEntry (encodeEntry { lockEntry with time := largestTime }) =
  some { lockEntry with time := largestTime }
#guard decodeEntry (encodeEntry { lockEntry with time := 2 ^ 63 * sec }) = none
#guard decodeEntry (encodeEntry { lockEntry with kind := 3, key := 2 ^ 31 }) = none
-- A pid_t uses only the low half of the eight-byte union.
#guard decodeEntry ⟨((ttyFixture.set 4 3).set 55 255).toArray⟩ =
  some { fixtureEntry with kind := 3 }
#guard decodeEntry (encodeEntry { fixtureEntry with key := 2 ^ 64 - 1 }) =
  some { fixtureEntry with key := 2 ^ 64 - 1 }
#guard decodeEntry (encodeEntry { fixtureEntry with authUid := 2 ^ 32 - 1 }) =
  some { fixtureEntry with authUid := 2 ^ 32 - 1 }

example (rs : List Record) (h : ∀ r ∈ rs, r.Representable) :
    decode (encode rs) = some rs := decode_encode rs h
example (e : DiskEntry) (h : e.Representable) :
    decodeEntry (encodeEntry e) = some e := decodeEntry_encodeEntry e h

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
