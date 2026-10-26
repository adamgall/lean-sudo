namespace LeanSudo.Sudoers

structure ParseError where
  file : String
  line : Nat
  col : Nat
  msg : String
  plain : Bool := false
  rendered : Option String := none
  deriving Repr, BEq, Inhabited

def ParseError.toString (e : ParseError) : String :=
  if e.plain then s!"{e.file}:{e.line}:{e.col}: {e.msg}" else
  s!"{e.file}:{e.line}:{e.col}: syntax error" ++ (if e.msg.isEmpty then "" else s!": {e.msg}")

instance : ToString ParseError := ⟨ParseError.toString⟩

namespace Gram

private def yypact : Array Int := #[
  174, -29, -116, -116, -116, -116, 35, 38, 11, 239, 150, 150, 8, -116, 32, 76, 88, 114, 254,
  -116, 58, 218, -116, -116, -116, 70, -116, -116, -116, 12, 13, 136, 73, 14, -116, -116, -116,
  -116, -116, -116, 276, -116, -116, 4, 10, 10, -116, -116, -116, -116, 190, 42, 81, 85, 97,
  -116, 64, -116, -116, -116, 52, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116,
  -116, -116, -116, 57, 2, -116, -116, 111, 9, -116, -116, 112, 56, -116, -116, 123, 61, -116,
  -116, -116, -116, 150, 62, -116, 75, 90, -116, 130, -116, 188, 204, 205, -116, 11, -116, -116,
  239, 55, 66, 108, -116, 207, 210, 213, 228, 143, -116, 8, 155, 175, 239, 32, -116, 209, 8, 76,
  -116, 211, 150, 88, -116, 217, 150, 114, -116, -116, 194, -116, 202, -116, -116, -116, -116,
  -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, 239, 225, -116,
  8, 227, -116, 150, 229, -116, 150, 229, -116, -116, -116, 233, 230, -116, -116, 225, 227, 229,
  229, 235, 232, 121, 202, 240, -116, -116, -116, 255, 238, -116, -116, -116, 235, -116, 234,
  236, 244, 246, 247, 260, 261, 262, 263, 264, -116, -116, -116, -116, -116, -116, -116, -116,
  -116, -116, 1, -116, 235, 238, 241, 296, 297, 298, 299, 300, 302, 303, 304, 305, -116, -116,
  -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116,
  -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116]

private def yydefact : Array Int := #[
  0, 0, 144, 146, 147, 148, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 6, 0, 0, 4, 8, 9, 0, 140,
  142, 7, 0, 0, 26, 0, 0, 24, 37, 40, 39, 41, 38, 0, 121, 35, 0, 0, 0, 114, 113, 115, 112, 0, 0,
  0, 0, 0, 49, 0, 128, 51, 53, 0, 118, 72, 73, 74, 79, 78, 82, 80, 81, 75, 76, 77, 83, 0, 0,
  116, 125, 0, 0, 123, 137, 0, 0, 135, 132, 0, 0, 130, 143, 1, 5, 0, 0, 31, 0, 0, 20, 0, 22, 0,
  0, 0, 27, 0, 15, 36, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 12, 0, 0, 0, 13, 0, 0,
  0, 11, 0, 0, 0, 14, 141, 0, 10, 65, 21, 23, 28, 29, 30, 25, 122, 18, 16, 17, 45, 46, 47, 48,
  50, 129, 19, 0, 120, 117, 0, 127, 124, 0, 139, 136, 0, 134, 131, 33, 32, 67, 34, 42, 84, 119,
  126, 138, 133, 71, 0, 68, 65, 95, 153, 155, 154, 0, 70, 149, 151, 66, 0, 43, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 85, 86, 89, 87, 88, 90, 91, 92, 93, 94, 0, 152, 0, 69, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 96, 97, 98, 99, 102, 103, 104, 105, 106, 107, 110, 111, 108, 109, 100, 101, 44, 150, 56,
  55, 61, 60, 62, 63, 64, 57, 58, 59]

private def yypgoto : Array Int := #[
  -116, -116, -116, 294, -116, -116, -6, 212, -116, 180, 214, 278, -116, 137, 206, -116, -115,
  267, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -116, -9, -116,
  -116, 270, -116, 203, -116, -7, -116, 198, -116, -85, -116, 192, -116, -116, 197, -116, -10,
  237, 310, 138, 115, 145]

private def yydefgoto : Array Int := #[
  0, 20, 21, 22, 23, 24, 33, 34, 93, 94, 41, 42, 172, 173, 55, 56, 57, 58, 204, 205, 206, 207,
  208, 209, 210, 211, 212, 213, 174, 180, 73, 74, 183, 214, 59, 75, 76, 120, 95, 79, 80, 124,
  60, 87, 88, 132, 83, 84, 128, 25, 26, 27, 188, 189, 190]

private def yytable : Array Int := #[
  44, 45, 43, 155, 46, 47, 78, 82, 86, 31, 48, 46, 47, 96, 98, 31, 31, 48, 28, 228, 229, 230,
  231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 49, 61, 108, 109, 110, 161,
  122, 49, 50, 29, 107, 32, 30, 126, 123, 50, 92, 32, 32, 119, 104, 127, 31, 90, 97, 99, 105,
  51, 52, 53, 54, 62, 46, 47, 51, 52, 53, 54, 48, 35, 176, 36, 37, 103, 38, 77, 112, 63, 64, 65,
  66, 67, 68, 69, 70, 71, 72, 81, 118, 32, 130, 104, 121, 49, 244, 134, 137, 147, 131, 39, 116,
  50, 104, 135, 138, 62, 92, 40, 148, 158, 139, 107, 78, 85, 164, 113, 82, 62, 167, 114, 86, 63,
  64, 65, 66, 67, 68, 69, 70, 71, 72, 115, 140, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 62, 104,
  175, 125, 129, 177, 2, 149, 178, 3, 4, 5, 192, 181, 92, 133, 63, 64, 65, 66, 67, 68, 69, 70,
  71, 72, -2, 1, 100, 141, 2, 101, 102, 3, 4, 5, 13, 6, 7, 8, 9, 10, 11, 12, 18, 46, 47, 169,
  104, 142, 35, 48, 36, 37, 156, 38, 51, 52, 53, 54, 13, 14, 15, 16, 17, 143, 144, 157, 18, 150,
  -3, 1, 151, 19, 2, 152, 49, 3, 4, 5, 39, 6, 7, 8, 9, 10, 11, 12, 40, 2, 153, 184, 3, 4, 5, 35,
  185, 36, 37, 171, 38, 160, 246, 163, 13, 14, 15, 16, 17, 166, 2, 184, 18, 3, 4, 5, 185, 19,
  107, 13, 118, 186, 92, 182, 179, 39, 218, 18, 219, 187, 191, 216, 35, 40, 36, 37, 220, 38,
  221, 222, 13, 186, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 223, 224, 225, 226, 227,
  247, 248, 249, 250, 251, 39, 252, 253, 254, 255, 91, 145, 170, 106, 193, 111, 146, 154, 117,
  162, 159, 168, 165, 89, 136, 217, 245, 215]

private def yycheck : Array Int := #[
  10, 11, 9, 118, 3, 4, 15, 16, 17, 5, 9, 3, 4, 1, 1, 5, 5, 9, 47, 18, 19, 20, 21, 22, 23, 24,
  25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 4, 43, 44, 45, 125, 39, 34, 42, 9, 41, 42, 9, 39, 47,
  42, 41, 42, 42, 60, 41, 47, 5, 0, 47, 47, 47, 61, 62, 63, 64, 34, 3, 4, 61, 62, 63, 64, 9, 4,
  160, 6, 7, 5, 9, 4, 39, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 4, 41, 42, 39, 41, 40, 34,
  214, 39, 39, 47, 47, 34, 41, 42, 41, 47, 47, 34, 41, 42, 47, 121, 40, 41, 126, 4, 129, 39,
  130, 34, 133, 39, 134, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 39, 47, 50, 51, 52, 53, 54, 55,
  56, 57, 58, 59, 34, 41, 157, 40, 40, 163, 4, 47, 166, 7, 8, 9, 39, 171, 41, 40, 50, 51, 52,
  53, 54, 55, 56, 57, 58, 59, 0, 1, 40, 47, 4, 43, 44, 7, 8, 9, 34, 11, 12, 13, 14, 15, 16, 17,
  42, 3, 4, 1, 41, 9, 4, 9, 6, 7, 47, 9, 61, 62, 63, 64, 34, 35, 36, 37, 38, 9, 9, 40, 42, 10,
  0, 1, 10, 47, 4, 10, 34, 7, 8, 9, 34, 11, 12, 13, 14, 15, 16, 17, 42, 4, 10, 4, 7, 8, 9, 4, 9,
  6, 7, 45, 9, 40, 9, 40, 34, 35, 36, 37, 38, 40, 4, 4, 42, 7, 8, 9, 9, 47, 41, 34, 41, 34, 41,
  41, 39, 34, 40, 42, 40, 42, 46, 41, 4, 42, 6, 7, 40, 9, 40, 40, 34, 34, 50, 51, 52, 53, 54,
  55, 56, 57, 58, 59, 40, 40, 40, 40, 40, 9, 9, 9, 9, 9, 34, 9, 9, 9, 9, 21, 104, 137, 40, 182,
  50, 107, 116, 56, 126, 122, 134, 130, 18, 92, 192, 216, 187]

private def yyr1 : Array Int := #[
  0, 65, 66, 66, 67, 67, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 69, 69, 70, 70,
  71, 71, 72, 72, 72, 72, 72, 73, 73, 73, 74, 75, 75, 76, 76, 76, 76, 76, 77, 77, 78, 79, 79,
  79, 79, 80, 80, 81, 81, 82, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 93, 94, 94, 94,
  94, 94, 95, 95, 95, 95, 95, 95, 95, 95, 95, 95, 95, 96, 97, 97, 97, 97, 97, 97, 97, 97, 97,
  97, 97, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 99, 99, 99, 99,
  100, 100, 102, 101, 101, 103, 103, 104, 104, 106, 105, 105, 107, 107, 108, 108, 110, 109, 109,
  111, 111, 113, 112, 112, 114, 114, 115, 115, 116, 116, 116, 116, 116, 117, 117, 118, 118, 119,
  119, 119]

private def yyr2 : Array Int := #[
  0, 2, 0, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 3, 4, 3, 4, 1, 3, 1, 2, 3, 3, 3,
  1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3, 3, 1, 3, 1, 2, 1, 2, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 0, 3, 0, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 3, 0, 4, 3, 1, 3, 1,
  3, 0, 4, 3, 1, 3, 1, 3, 0, 4, 3, 1, 3, 0, 4, 3, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1,
  1]

private def tbl (a : Array Int) (i : Int) : Int :=
  if i < 0 then 0 else a.getD i.toNat 0

def kEOF : Nat := 0
def kCOMMAND : Nat := 3
def kALIAS : Nat := 4
def kDEFVAR : Nat := 5
def kNTWKADDR : Nat := 6
def kNETGROUP : Nat := 7
def kUSERGROUP : Nat := 8
def kWORD : Nat := 9
def kDIGEST : Nat := 10
def kINCLUDE : Nat := 11
def kINCLUDEDIR : Nat := 12
def kDEFAULTS : Nat := 13
def kDEFAULTS_HOST : Nat := 14
def kDEFAULTS_USER : Nat := 15
def kDEFAULTS_RUNAS : Nat := 16
def kDEFAULTS_CMND : Nat := 17
def kALL : Nat := 34
def kHOSTALIAS : Nat := 35
def kCMNDALIAS : Nat := 36
def kUSERALIAS : Nat := 37
def kRUNASALIAS : Nat := 38
def kNL : Nat := 47
def kERROR : Nat := 48
def kNOMATCH : Nat := 49

def u (c : Char) : UInt8 := c.toNat.toUInt8

def byteAt? (s : ByteArray) (i : Nat) : Option UInt8 :=
  if h : i < s.size then some s[i] else none

structure Pat where
  first : UInt8 → Bool
  nullable : Bool
  run : ByteArray → Nat → List Nat

def eps : Pat := ⟨fun _ => false, true, fun _ i => [i]⟩

def cls (p : UInt8 → Bool) : Pat := ⟨p, false, fun s i =>
  match byteAt? s i with
  | some c => if p c then [i + 1] else []
  | none => []⟩

def seq (a b : Pat) : Pat :=
  ⟨fun c => a.first c || (a.nullable && b.first c), a.nullable && b.nullable,
   fun s i => ((a.run s i).flatMap (b.run s)).eraseDups⟩

def alt (a b : Pat) : Pat :=
  ⟨fun c => a.first c || b.first c, a.nullable || b.nullable,
   fun s i => (a.run s i ++ b.run s i).eraseDups⟩

def opt (a : Pat) : Pat := ⟨a.first, true, fun s i => (i :: a.run s i).eraseDups⟩

def star (a : Pat) : Pat := ⟨a.first, true, fun s i => Id.run do
  let mut seen := (Array.replicate (s.size + 2) false).set! i true
  let mut all := #[i]
  let mut frontier := [i]
  for _ in [0:s.size + 1] do
    let mut next := []
    for j in frontier.flatMap (a.run s) do
      if !seen.getD j true then
        seen := seen.set! j true
        all := all.push j
        next := j :: next
    if next.isEmpty then break
    frontier := next
  return all.toList⟩

def plus (a : Pat) : Pat := seq a (star a)

def chr (c : Char) : Pat := cls (· == u c)

def lit (t : String) : Pat := t.toList.foldr (fun c p => seq (chr c) p) eps

def oneOf (t : String) (c : UInt8) : Bool := t.toList.any (fun d => u d == c)

def anyOf (t : String) : Pat := cls (oneOf t)

def noneOf (t : String) : Pat := cls (fun c => !oneOf t c)

def inRange (a b : Char) (c : UInt8) : Bool := u a ≤ c && c ≤ u b

def isBlank (c : UInt8) : Bool := c == 32 || c == 9

def isSpace (c : UInt8) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

def isDigit (c : UInt8) : Bool := inRange '0' '9' c

def isUpper (c : UInt8) : Bool := inRange 'A' 'Z' c

def isXdigit (c : UInt8) : Bool := isDigit c || inRange 'a' 'f' c || inRange 'A' 'F' c

def rep (p : Pat) : Nat → Nat → Pat
  | 0, 0 => eps
  | 0, n + 1 => opt (seq p (rep p 0 n))
  | m + 1, n => seq p (rep p m (n - 1))

def blankP : Pat := cls isBlank
def digitP : Pat := cls isDigit
def dotStar : Pat := star (noneOf "\n")
def eol : Pat := alt (lit "\r\n") (chr '\n')
def wordP : Pat := plus (alt (noneOf "#>!=:,() \t\r\n\\\"") (seq (chr '\\') (noneOf "\t\n")))
def idP : Pat := seq (chr '#') (seq (opt (chr '-')) (plus digitP))
def pathP : Pat :=
  seq (chr '/') (plus (alt (seq (chr '\\') (anyOf ",:= \t#")) (noneOf ",:=\\ \t\r\n#")))
def regexP : Pat :=
  seq (chr '^') (seq (star (alt (noneOf "#\r\n$") (seq (chr '\\') (anyOf "#$")))) (chr '$'))
def envEsc : Pat := seq (chr '\\') (noneOf "\r\n")
def envarP : Pat :=
  seq (alt (noneOf "#!=, \t\r\n\\\"") envEsc) (star (alt (noneOf "#=, \t\r\n\\\"") envEsc))
def octetP : Pat :=
  alt (seq (opt (chr '1')) (seq digitP (opt digitP)))
    (alt (seq (chr '2') (seq (cls (inRange '0' '4')) digitP))
      (seq (lit "25") (cls (inRange '0' '5'))))
def ipv4P : Pat :=
  seq octetP (seq (chr '.') (seq octetP (seq (chr '.') (seq octetP (seq (chr '.') octetP)))))
def hex16P : Pat := rep (cls isXdigit) 1 4
def v6unit : Pat := seq (opt hex16P) (chr ':')
def ipv6P : Pat :=
  alt (seq (rep v6unit 2 7) (opt hex16P)) (seq (rep v6unit 2 6) (seq (chr ':') ipv4P))
def mask4P : Pat :=
  seq (chr '/') (alt (seq (opt (anyOf "12")) digitP) (seq (chr '3') (cls (inRange '0' '2'))))
def mask6P : Pat :=
  seq (chr '/') (alt digitP (alt (seq (cls (inRange '1' '9')) digitP)
    (alt (seq (chr '1') (seq (anyOf "01") digitP)) (seq (lit "12") (cls (inRange '0' '8'))))))
def commentP : Pat :=
  seq (chr '#') (seq (opt (alt (seq (chr '-') (seq (noneOf "\r\n0123456789") dotStar))
    (seq (noneOf "\r\n0123456789-") dotStar))) (opt eol))
def contP : Pat := seq (chr '\\') (seq (star blankP) (seq (opt (chr '\r')) (chr '\n')))

inductive SC where
  | initial | gotdefs | gotcmnd | gotregex | startdefs | indefs | instr | wantdigest | gotinc
  | expectpath
  deriving BEq, Inhabited, Repr

def SC.inclusive : SC → Bool
  | .initial | .gotdefs | .wantdigest | .expectpath => true
  | _ => false

inductive Act where
  | defsComma | defsBlank | defvar | indefsComma | indefsTok (t : Nat) | indefsQuote | envar
  | strEnd | strBackslash | strBody
  | cmndQuoted | cmndEnd | cmndArg
  | rxQuoted | rxEnd | rxDollar | rxBody
  | digestHex | digestB64
  | include (t : Nat) | hashInclude (t : Nat) (n : Nat) | defaults | aliasKw
  | token (t : Nat) | emptyGroup | value (t : Nat) | ntwk6 | pathKw (t : Nat)
  | defsCommand | sha (t : Nat) (len : Nat) | sudoedit | expectPath | path | regex
  | quote | word | incWord | incQuote | bang | newline | blank | cont | comment | nomatch

structure Rule where
  act : Act
  active : SC → Bool
  bol : Bool := false
  pat : Pat

def only (scs : List SC) : SC → Bool := fun sc => scs.contains sc

def tags : List (String × Nat) :=
  [("NOPASSWD", 18), ("PASSWD", 19), ("NOEXEC", 20), ("EXEC", 21), ("INTERCEPT", 32),
   ("NOINTERCEPT", 33), ("SETENV", 22), ("NOSETENV", 23), ("LOG_OUTPUT", 26),
   ("NOLOG_OUTPUT", 27), ("LOG_INPUT", 24), ("NOLOG_INPUT", 25), ("MAIL", 28), ("NOMAIL", 29),
   ("FOLLOW", 30), ("NOFOLLOW", 31)]

def keywords : List (String × Nat) :=
  [("TIMEOUT", 57), ("NOTBEFORE", 58), ("NOTAFTER", 59), ("CWD", 51), ("CHROOT", 50),
   ("ROLE", 53), ("TYPE", 52), ("APPARMOR_PROFILE", 54), ("PRIVS", 55), ("LIMITPRIVS", 56)]

def rules : Array Rule :=
  let ini := only [.initial]
  let incl := SC.inclusive
  let all : SC → Bool := fun _ => true
  #[{ act := .defsComma, active := only [.gotdefs],
      pat := seq (star blankP) (seq (chr ',') (star blankP)) },
    { act := .defsBlank, active := only [.gotdefs], pat := plus blankP },
    { act := .defvar, active := only [.startdefs],
      pat := plus (cls fun c => inRange 'a' 'z' c || c == u '_') },
    { act := .indefsComma, active := only [.indefs], pat := chr ',' },
    { act := .indefsTok 40, active := only [.indefs], pat := chr '=' },
    { act := .indefsTok 43, active := only [.indefs], pat := lit "+=" },
    { act := .indefsTok 44, active := only [.indefs], pat := lit "-=" },
    { act := .indefsQuote, active := only [.indefs], pat := chr '"' },
    { act := .envar, active := only [.indefs], pat := envarP },
    { act := .strEnd, active := only [.instr], pat := chr '"' },
    { act := .strBackslash, active := only [.instr], pat := chr '\\' },
    { act := .strBody, active := only [.instr],
      pat := plus (alt (noneOf "\"\r\n\\") (lit "\\\"")) },
    { act := .cmndQuoted, active := only [.gotcmnd], pat := seq (chr '\\') (anyOf "*?[]!^") },
    { act := .cmndQuoted, active := only [.gotcmnd], pat := seq (chr '\\') (anyOf ":\\,= \t#") },
    { act := .cmndEnd, active := only [.gotcmnd], pat := anyOf "#:,=\r\n" },
    { act := .cmndArg, active := only [.gotcmnd], pat := plus (noneOf "#\\:, \t\r\n") },
    { act := .rxQuoted, active := only [.gotregex], pat := seq (chr '\\') (noneOf "\r\n") },
    { act := .rxEnd, active := only [.gotregex], pat := anyOf "#\r\n" },
    { act := .rxDollar, active := only [.gotregex], pat := chr '$' },
    { act := .rxBody, active := only [.gotregex], pat := plus (noneOf "#\\\r\n$") },
    { act := .digestHex, active := only [.wantdigest], pat := plus (cls isXdigit) },
    { act := .digestB64, active := only [.wantdigest],
      pat := plus (cls fun c => isDigit c || isUpper c || inRange 'a' 'z' c || oneOf "+/=" c) },
    { act := .include kINCLUDE, active := ini, pat := lit "@include" },
    { act := .include kINCLUDEDIR, active := ini, pat := lit "@includedir" },
    { act := .hashInclude kINCLUDE 8, active := ini, bol := true,
      pat := seq (lit "#include") (seq (plus blankP) (seq dotStar (opt eol))) },
    { act := .hashInclude kINCLUDEDIR 11, active := ini, bol := true,
      pat := seq (lit "#includedir") (seq (plus blankP) (seq dotStar (opt eol))) },
    { act := .defaults, active := ini, bol := true,
      pat := seq (star blankP) (seq (lit "Defaults") (opt (seq (anyOf ":@>!") (seq (star blankP)
        (seq (star (chr '!')) (seq (opt (chr '"')) (alt idP wordP))))))) },
    { act := .aliasKw, active := ini, bol := true,
      pat := seq (star blankP) (seq (alt (lit "Host") (alt (lit "Cmnd") (alt (lit "Cmd")
        (alt (lit "User") (lit "Runas"))))) (lit "_Alias")) }] ++
  (tags.map fun (name, t) =>
    { act := .token t, active := incl,
      pat := seq (lit name) (seq (star blankP) (chr ':')) }).toArray ++
  #[{ act := .emptyGroup, active := only [.initial, .gotdefs],
      pat := alt (chr '+') (alt (chr '%') (lit "%:")) },
    { act := .value kNETGROUP, active := incl, pat := seq (chr '+') wordP },
    { act := .value kUSERGROUP, active := incl,
      pat := seq (chr '%') (seq (opt (chr ':')) (alt wordP idP)) },
    { act := .value kNTWKADDR, active := incl, pat := seq ipv4P (opt (seq (chr '/') ipv4P)) },
    { act := .value kNTWKADDR, active := incl, pat := seq ipv4P mask4P },
    { act := .ntwk6, active := incl, pat := seq ipv6P (opt (seq (chr '/') ipv6P)) },
    { act := .ntwk6, active := incl, pat := seq ipv6P mask6P },
    { act := .token kALL, active := incl, pat := lit "ALL" }] ++
  (keywords.map fun (name, t) =>
    { act := if t == 50 || t == 51 then .pathKw t else .token t, active := ini,
      pat := lit name }).toArray ++
  #[{ act := .value kALIAS, active := incl,
      pat := seq (cls isUpper) (star (cls fun c => isUpper c || isDigit c || c == u '_')) },
    { act := .defsCommand, active := only [.gotdefs],
      pat := alt pathP (alt regexP (lit "sudoedit")) },
    { act := .sha 61 28, active := incl, pat := lit "sha224" },
    { act := .sha 62 32, active := incl, pat := lit "sha256" },
    { act := .sha 63 48, active := incl, pat := lit "sha384" },
    { act := .sha 64 64, active := incl, pat := lit "sha512" },
    { act := .sudoedit, active := incl, pat := lit "sudoedit" },
    { act := .expectPath, active := only [.expectpath], pat := alt pathP wordP },
    { act := .path, active := incl, pat := pathP },
    { act := .regex, active := incl, pat := regexP },
    { act := .quote, active := only [.initial, .expectpath, .gotdefs], pat := chr '"' },
    { act := .word, active := only [.initial, .gotdefs], pat := alt idP wordP },
    { act := .incWord, active := only [.gotinc],
      pat := seq (cls fun c => c != u '"' && !isSpace c)
        (star (alt (cls fun c => !isSpace c) (seq (chr '\\') blankP))) },
    { act := .incQuote, active := only [.gotinc], pat := chr '"' },
    { act := .token 45, active := incl, pat := chr '(' },
    { act := .token 46, active := incl, pat := chr ')' },
    { act := .token 41, active := incl, pat := chr ',' },
    { act := .token 40, active := incl, pat := chr '=' },
    { act := .token 39, active := incl, pat := chr ':' },
    { act := .bang, active := all, pat := plus (chr '!') },
    { act := .newline, active := all, pat := seq (opt (chr '\r')) (chr '\n') },
    { act := .blank, active := all, pat := plus blankP },
    { act := .cont, active := all, pat := contP },
    { act := .comment, active := only [.initial, .startdefs, .indefs], pat := commentP },
    { act := .nomatch, active := all, pat := noneOf "\n" }]

def longest (line : ByteArray) (off : Nat) (sc : SC) (bol : Bool) : Option (Act × Nat) :=
  let c := (byteAt? line off).getD 0
  rules.foldl (init := none) fun best r =>
    if !r.active sc || (r.bol && !bol) || !r.pat.first c then best else
      let len := ((r.pat.run line off).foldl max off) - off
      match best with
      | some (_, l) => if len > l then some (r.act, len) else best
      | none => if len > 0 then some (r.act, len) else none

def hexValue (c : UInt8) : Option Nat :=
  if isDigit c then some (c.toNat - 48)
  else if inRange 'a' 'f' c then some (c.toNat - 87)
  else if inRange 'A' 'F' c then some (c.toNat - 55)
  else none

def copyString (b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut i := 0
  for _ in [0:b.size] do
    if i ≥ b.size then break
    let c := b.get! i
    i := i + 1
    if c == u '\\' && i < b.size then
      match (if b.get! i == u 'x' && i + 3 ≤ b.size then
          (hexValue (b.get! (i + 1))).bind fun h => (hexValue (b.get! (i + 2))).map (h * 16 + ·)
        else none) with
      | some v =>
        out := out.push v.toUInt8
        i := i + 3
      | none =>
        out := out.push (b.get! i)
        i := i + 1
    else out := out.push c
  return out

def cstr (b : ByteArray) : ByteArray :=
  match (List.range b.size).find? (fun i => b.get! i == 0) with
  | some i => b.extract 0 i
  | none => b

def special (c : UInt8) : Bool := oneOf ",:= \t#" c

def fillCmnd (b : ByteArray) : ByteArray := Id.run do
  if b.size > 0 && b.get! 0 == u '^' then return b
  let mut out := ByteArray.empty
  let mut i := 0
  for _ in [0:b.size] do
    if i ≥ b.size then break
    if b.get! i == u '\\' && i + 1 != b.size && special (b.get! (i + 1)) then
      out := out.push (b.get! (i + 1))
      i := i + 2
    else
      out := out.push (b.get! i)
      i := i + 1
  let s := cstr out
  let slash := ((List.range s.size).filter (fun i => s.get! i == u '/')).getLast?
  match slash with
  | some j => if s.extract j s.size == "/sudoedit".toUTF8 then "sudoedit".toUTF8 else s
  | none => s

def ipv6Valid (b : ByteArray) : Bool := Id.run do
  let mut n := 0
  for i in [0:b.size] do
    if b.get! i == u ':' && i + 1 < b.size && b.get! (i + 1) == u ':' then
      n := n + 1
      if n > 1 then return false
    if b.get! i == u '/' then n := 0
  return true

structure Lex where
  lines : Array ByteArray
  eof : Bool := false
  fuel : Nat := 0
  li : Nat := 0
  loaded : Bool := false
  off : Nat := 0
  tokeStart : Nat := 0
  tokeEnd : Nat := 0
  lineno : Nat := 1
  sc : SC := .initial
  prev : SC := .initial
  continued : Bool := false
  bol : Bool := true
  digestLen : Nat := 0
  args : Bool := false
  str : Option ByteArray := none
  errstr : Option String := none
  value : ByteArray := .empty

def Lex.line (lx : Lex) : ByteArray := if lx.loaded then lx.lines.getD lx.li .empty else .empty

def Lex.refill (lx : Lex) : Option Lex :=
  if lx.loaded && lx.off < lx.line.size then some lx else
    let next := if lx.loaded then lx.li + 1 else 0
    if next < lx.lines.size then
      some { lx with li := next, loaded := true, off := 0, tokeStart := 0, tokeEnd := 0 }
    else none

def Lex.less (lx : Lex) (start n : Nat) : Lex :=
  { lx with tokeEnd := lx.tokeStart + n, off := start + n }

def Lex.error (lx : Lex) (msg : String) : Option Nat × Lex :=
  (some kERROR, { lx with errstr := some msg })

def Lex.append (lx : Lex) (b : ByteArray) : Lex :=
  { lx with str := some ((lx.str.getD .empty) ++ copyString b) }

def Lex.act (lx : Lex) (a : Act) (text : ByteArray) (start : Nat) : Option Nat × Lex :=
  let len := text.size
  let first := if len > 0 then text.get! 0 else 0
  match a with
  | .defsComma => (some 41, lx)
  | .defsBlank => (none, { lx with sc := .startdefs })
  | .defvar => (some kDEFVAR, { lx with sc := .indefs, value := copyString text })
  | .indefsComma => (some 41, { lx with sc := .startdefs })
  | .indefsTok t => (some t, lx)
  | .indefsQuote => (none, { lx with str := none, prev := lx.sc, sc := .instr })
  | .envar => (some kWORD, { lx with value := copyString text })
  | .strEnd =>
    let lx := { lx with sc := lx.prev }
    match lx.str with
    | none => lx.error "empty string"
    | some s =>
      let lx := { lx with value := s }
      let s := cstr s
      if lx.prev == .initial || lx.prev == .gotdefs then
        if s.size > 0 && s.get! 0 == u '%' then
          if s.size == 1 || (s.size == 2 && s.get! 1 == u ':') then lx.error "empty group"
          else (some kUSERGROUP, lx)
        else if s.size > 0 && s.get! 0 == u '+' then
          if s.size == 1 then lx.error "empty netgroup" else (some kNETGROUP, lx)
        else (some kWORD, lx)
      else (some kWORD, lx)
  | .strBackslash => (none, lx.append text)
  | .strBody => (none, lx.append text)
  | .cmndQuoted => (none, { lx with args := true })
  | .cmndEnd => (some kCOMMAND, { (lx.less start 0) with sc := .initial, bol := false })
  | .cmndArg =>
    if !lx.args && first == u '^' then
      (none, { (lx.less start 0) with sc := .gotregex, bol := false })
    else (none, { lx with args := true })
  | .rxQuoted => (none, { lx with args := true })
  | .rxEnd =>
    Lex.error { (lx.less start 0) with bol := false, sc := .initial }
      "unterminated regular expression"
  | .rxDollar => (some kCOMMAND, { lx with sc := .initial, continued := false })
  | .rxBody => (none, lx)
  | .digestHex =>
    if len == lx.digestLen * 2 then (some kDIGEST, { lx with sc := .initial, value := text })
    else (none, { lx with sc := .initial })
  | .digestB64 =>
    let need := if text.get! (len - 1) == u '=' then 4 * ((lx.digestLen + 2) / 3)
      else (4 * lx.digestLen + 2) / 3
    if len == need then (some kDIGEST, { lx with sc := .initial, value := text })
    else (none, { lx with sc := .initial })
  | .include t =>
    if lx.continued then lx.error "invalid line continuation"
    else (some t, { lx with sc := .gotinc })
  | .hashInclude t n =>
    if lx.continued then lx.error "invalid line continuation"
    else (some t, { (lx.less start n) with bol := false, sc := .gotinc })
  | .defaults =>
    if lx.continued then lx.error "invalid line continuation" else
    let blanks := (text.toList.takeWhile isBlank).length
    let n := blanks + 8
    let deftype := if n < len then text.get! n else 0
    let n := n + 1
    let n := if deftype != 0 then n + ((text.toList.drop n).takeWhile isBlank).length else n
    let lx := { lx with sc := .gotdefs }
    if deftype == u ':' then (some kDEFAULTS_USER, lx.less start n)
    else if deftype == u '>' then (some kDEFAULTS_RUNAS, lx.less start n)
    else if deftype == u '@' then (some kDEFAULTS_HOST, lx.less start n)
    else if deftype == u '!' then (some kDEFAULTS_CMND, lx.less start n)
    else (some kDEFAULTS, lx)
  | .aliasKw =>
    if lx.continued then lx.error "invalid line continuation" else
    let c := (text.toList.dropWhile isBlank).headD 0
    if c == u 'H' then (some kHOSTALIAS, lx)
    else if c == u 'C' then (some kCMNDALIAS, lx)
    else if c == u 'U' then (some kUSERALIAS, lx)
    else (some kRUNASALIAS, lx)
  | .token t => (some t, lx)
  | .emptyGroup => lx.error (if first == u '+' then "empty netgroup" else "empty group")
  | .value t => (some t, { lx with value := copyString text })
  | .ntwk6 =>
    if ipv6Valid text then (some kNTWKADDR, { lx with value := text })
    else lx.error "invalid IPv6 address"
  | .pathKw t => (some t, { lx with prev := lx.sc, sc := .expectpath })
  | .defsCommand => (some kCOMMAND, { lx with value := fillCmnd text, args := false })
  | .sha t n => (some t, { lx with digestLen := n, sc := .wantdigest })
  | .sudoedit => (none, { lx with sc := .gotcmnd, value := text, args := false })
  | .expectPath => (some kWORD, { lx with sc := lx.prev, value := copyString text })
  | .path =>
    if text.get! (len - 1) == u '/' then
      (some kCOMMAND, { lx with value := fillCmnd text, args := false })
    else (none, { lx with sc := .gotcmnd, value := fillCmnd text, args := false })
  | .regex => (none, { lx with sc := .gotcmnd, value := text, args := false })
  | .quote =>
    let prev := if lx.sc == .expectpath then lx.prev else lx.sc
    (none, { lx with str := none, prev, sc := .instr })
  | .word => (some kWORD, { lx with value := copyString text })
  | .incWord => (some kWORD, { lx with value := copyString text, sc := .initial })
  | .incQuote => (none, { lx with str := none, prev := .initial, sc := .instr })
  | .bang => if len % 2 == 1 then (some 42, lx) else (none, lx)
  | .newline =>
    if lx.sc == .instr then
      Lex.error { (lx.less start 0) with sc := .initial } "unexpected line break in string"
    else (some kNL, { lx with sc := .initial, lineno := lx.lineno + 1, continued := false })
  | .blank => (none, lx)
  | .cont => (none, { lx with lineno := lx.lineno + 1, continued := true })
  | .comment =>
    if text.get! (len - 1) == u '\n' then
      (some kNL, { lx with sc := .initial, lineno := lx.lineno + 1, continued := false })
    else if lx.eof && lx.li + 1 == lx.lines.size then (some kNL, lx)
    else lx.error "Success"
  | .nomatch => (some kNOMATCH, lx)

def Lex.next (lx : Lex) : Nat × Lex := Id.run do
  let mut lx := lx
  for _ in [0:lx.fuel] do
    let some l := lx.refill | return (kEOF, lx)
    lx := l
    let line := lx.line
    let start := lx.off
    if lx.sc == .instr then
      let e := (contP.run line start).foldl max start
      if e > start then
        let first := e - start
        let lx' := { lx with lineno := lx.lineno + 1, continued := true }
        match lx.lines[lx.li + 1]? with
        | some nl =>
          let blanks := (nl.toList.takeWhile isBlank).length
          lx := { lx' with
            li := lx.li + 1, off := blanks, tokeStart := 0
            tokeEnd := first + blanks, bol := blanks == 0 }
        | none =>
          lx := { lx' with
            off := e, tokeStart := lx.tokeEnd, tokeEnd := lx.tokeEnd + first, bol := true }
        continue
    let some (a, len) := longest line start lx.sc lx.bol | return (kEOF, lx)
    let text := line.extract start (start + len)
    lx := { lx with
      tokeStart := lx.tokeEnd, tokeEnd := lx.tokeEnd + len, off := start + len
      bol := text.get! (len - 1) == u '\n' }
    let (t, l) := lx.act a text start
    lx := l
    if let some t := t then return (t, lx)
  return (kEOF, lx)

def splitLines (b : ByteArray) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := #[]
  let mut cur := ByteArray.empty
  for c in b.toList do
    cur := cur.push c
    if c == u '\n' then
      out := out.push cur
      cur := .empty
  if cur.size > 0 then out := out.push (cur.push (u '\n'))
  return out.map fun l =>
    match (List.range l.size).find? (fun i => l.get! i == 0) with
    | some i => (l.extract 0 i).push (u '\n')
    | none => l

inductive Val where
  | none
  | text (b : ByteArray)
  | kind (k : Nat)
  deriving Inhabited

def Val.bytes : Val → ByteArray
  | .text b => cstr b
  | _ => .empty

inductive Event where
  | error (e : ParseError)
  | warning (line : Nat) (message : String)
  | include (dir : Bool) (path : String) (line col : Nat)
  deriving Inhabited

structure Alias where
  kind : String
  name : String
  file : String
  line : Nat
  col : Nat
  deriving Inhabited

structure Scan where
  events : Array Event := #[]
  defaults : Array (Nat × Nat) := #[]
  aliases : Array Alias := #[]
  spans : Array (Nat × Nat) := #[]
  definesAliases : Bool := false
  deriving Inhabited

def Scan.errors (s : Scan) : List ParseError :=
  s.events.toList.filterMap fun | .error e => some e | _ => none

def escapeBase : Nat := 0x10FF00

def utf8Length (b : ByteArray) (i : Nat) : Option Nat :=
  let c := b.get! i
  let cont (k : Nat) : Bool := i + k < b.size && (b.get! (i + k)) &&& 0xC0 == 0x80
  let decoded (n : Nat) : Option Nat :=
    match String.fromUTF8? (b.extract i (i + n)) with
    | some _ => some n
    | none => none
  if c < 0x80 then some 1
  else if c &&& 0xE0 == 0xC0 && cont 1 then decoded 2
  else if c &&& 0xF0 == 0xE0 && cont 1 && cont 2 then decoded 3
  else if c &&& 0xF8 == 0xF0 && cont 1 && cont 2 && cont 3 then decoded 4
  else none

def utf8 (b : ByteArray) : String := Id.run do
  if let some s := String.fromUTF8? b then return s
  let mut out := ""
  let mut i := 0
  for _ in [0:b.size] do
    if i ≥ b.size then break
    match utf8Length b i with
    | some n =>
      out := out ++ ((String.fromUTF8? (b.extract i (i + n))).getD "")
      i := i + n
    | none =>
      out := out.push (Char.ofNat (escapeBase + (b.get! i).toNat))
      i := i + 1
  return out

def rawBytes (s : String) : ByteArray :=
  s.toList.foldl (fun acc c =>
    if c.toNat ≥ escapeBase then acc.push (c.toNat - escapeBase).toUInt8
    else acc ++ (String.singleton c).toUTF8) .empty

def parseTimeoutC (b : ByteArray) : Option String := Id.run do
  let s := b.toList
  let mut i := 0
  let mut idx := 0
  let mut total : Nat := 0
  for _ in [0:s.length + 1] do
    let mut j := i + ((s.drop i).takeWhile isSpace).length
    let neg := s.getD j 0 == u '-'
    if s.getD j 0 == u '-' || s.getD j 0 == u '+' then j := j + 1
    let digits := ((s.drop j).takeWhile isDigit)
    if digits.isEmpty then return some "invalid timeout value"
    let l := digits.foldl (fun n c => n * 10 + (c.toNat - 48)) 0
    j := j + digits.length
    if (neg && l != 0) || l > 2147483647 then return some "timeout value too large"
    let mut v := l
    if j < s.length then
      let ch := s.getD j 0
      let ch := if isUpper ch then ch + 32 else ch
      j := j + 1
      let suffixes := "dhms".toList.map u
      let mut found := false
      for k in [idx:4] do
        if suffixes.getD k 0 == ch then
          idx := k
          found := true
          break
      if !found then return some "invalid timeout value"
      let mult := if ch == u 'd' then 86400 else if ch == u 'h' then 3600
        else if ch == u 'm' then 60 else 1
      if l > 2147483647 / mult then return some "timeout value too large"
      v := l * mult
    if v > 2147483647 - total then return some "timeout value too large"
    total := total + v
    i := j
    if i ≥ s.length then return none
  return some "invalid timeout value"

def gentimeOk (b : ByteArray) : Bool := Id.run do
  let s := b.toList
  let len := (s.takeWhile isDigit).length
  if len ≥ 15 || len < 10 || len % 2 == 1 then return false
  let mut cp := len
  if (s.getD cp 0 == u '.' || s.getD cp 0 == u ',') && isDigit (s.getD (cp + 1) 0) then
    cp := cp + 2
  let c := s.getD cp 0
  if c == u '-' || c == u '+' then
    let n := ((s.drop (cp + 1)).takeWhile isDigit).length
    if n != 2 && n != 4 then return false
    cp := cp + 1 + n
  else if c == u 'Z' then cp := cp + 1
  else if cp < s.length then return false
  return cp ≥ s.length

def dirValueError (name : String) (b : ByteArray) : Option String :=
  let c := if b.size > 0 then b.get! 0 else 0
  if c != u '/' && c != u '~' && b != "*".toUTF8 then
    some s!"values for \"{name}\" must start with a '/', '~', or '*'"
  else if b.size ≥ 4096 then some s!"\"{name}\" path too long"
  else none

def reservedNames : List (Nat × String) :=
  [(72, "ALL"), (73, "CHROOT"), (74, "CWD"), (75, "CMND_TIMEOUT"), (76, "NOTBEFORE"),
   (77, "NOTAFTER"), (78, "ROLE"), (79, "TYPE"), (80, "PRIVS"), (81, "LIMITPRIVS"),
   (82, "APPARMOR_PROFILE")]

structure St where
  file : String
  lx : Lex
  stack : List Nat := [0]
  vals : List Val := [.none]
  yychar : Option Nat := none
  yylval : Val := .none
  errStatus : Nat := 0
  aliasPos : Nat × Nat := (0, 0)
  yyline : Nat := 0
  entryStart : Option Nat := none
  entryBad : Bool := false
  out : Scan := {}

def St.lineno (st : St) : Nat :=
  if st.yychar == some kNL then st.lx.lineno - 1 else st.lx.lineno

def St.errorf (st : St) (msg : Option String) : St :=
  let lx := st.lx
  let line := lx.line
  let header := s!"{st.file}:{st.lineno}:{lx.tokeStart + 1}: {msg.getD ""}"
  let shown := if line.size == 0 then header else
    let text := if line.size > 0 && line.get! (line.size - 1) == u '\n' then
      line.extract 0 (line.size - 1) else line
    let tildes := if lx.tokeEnd > lx.tokeStart then min (lx.tokeEnd - lx.tokeStart - 1) 127
      else 0
    header ++ "\n" ++ utf8 text ++ "\n" ++ String.ofList (List.replicate lx.tokeStart ' ') ++
      "^" ++ String.ofList (List.replicate tildes '~')
  let e : ParseError := {
    file := st.file, line := st.lineno, col := lx.tokeStart + 1
    msg := msg.getD "syntax error", plain := true
    rendered := some (if msg.isSome then shown else "") }
  { st with out := { st.out with events := st.out.events.push (.error e) }, entryBad := true }

def St.yyerror (st : St) (msg : String) : St :=
  if st.yychar == some kERROR then
    ({ st with lx := { st.lx with errstr := none } }).errorf st.lx.errstr
  else st.errorf (some msg)

def St.action (st : St) (rule : Nat) (rhs : Array Val) : St × Except Unit Val :=
  let arg (i : Nat) : Val := rhs.getD i .none
  let fail (msg : String) : St × Except Unit Val := (st.yyerror msg, .error ())
  let push (e : Event) : St := { st with out := { st.out with events := st.out.events.push e } }
  let pathOf (v : Val) : String :=
    let b := v.bytes
    let b := if b.size > 1 && b.get! 0 == u '"' && b.get! (b.size - 1) == u '"' then
      b.extract 1 (b.size - 1) else b
    utf8 b
  match rule with
  | 7 | 33 => ({ st with errStatus := 0 }, .ok (arg 0))
  | 118 | 125 | 132 | 137 => ({ st with aliasPos := (st.lineno, st.lx.tokeStart + 1) }, .ok .none)
  | 119 | 126 | 133 | 138 =>
    let st := { st with out := { st.out with definesAliases := true } }
    let kind := if rule == 119 then "Host_Alias" else if rule == 126 then "Cmnd_Alias"
      else if rule == 133 then "Runas_Alias" else "User_Alias"
    let name := utf8 (arg 0).bytes
    match st.out.aliases.find? (fun a => a.kind == kind && a.name == name) with
    | some a =>
      (st.errorf (some (s!"duplicate {kind} \"{name}\", previously defined at " ++
        s!"{a.file}:{a.line}:{a.col}")), .error ())
    | none =>
      let entry : Alias :=
        { kind, name, file := st.file, line := st.aliasPos.1, col := st.aliasPos.2 }
      ({ st with out := { st.out with aliases := st.out.aliases.push entry } }, .ok .none)
  | 8 | 9 =>
    (push (.include (rule == 9) (pathOf (arg 0)) st.lineno (st.lx.tokeStart + 1)), .ok .none)
  | 20 | 22 => (st, .ok (arg 1))
  | 21 | 23 => ({ st with errStatus := 0 }, .ok (arg 1))
  | 26 | 27 | 28 | 29 | 30 =>
    let defaults := st.out.defaults.push (st.lineno, st.lx.tokeStart + 1)
    ({ st with out := { st.out with defaults } }, .ok .none)
  | 52 =>
    match arg 1 with
    | .kind k => if k != kCOMMAND && k != kALL then fail "a digest requires a path name"
      else (st, .ok (arg 1))
    | v => (st, .ok v)
  | 54 => (st, .ok (arg 1))
  | 55 => match dirValueError "CWD" (arg 2).bytes with
    | some m => fail m
    | none => (st, .ok (arg 2))
  | 56 => match dirValueError "CHROOT" (arg 2).bytes with
    | some m => fail m
    | none =>
      let message := s!"{st.file}:{st.lineno}:{st.lx.tokeStart + 1}: \"CHROOT\" is deprecated"
      (push (.warning st.lineno message), .ok (arg 2))
  | 57 | 58 | 59 | 60 | 61 | 62 | 63 | 64 => (st, .ok (arg 2))
  | 83 =>
    let name := match arg 0 with | .text b => utf8 b | _ => ""
    (st.errorf (some s!"syntax error, reserved word {name} used as an alias name"), .error ())
  | 87 => if gentimeOk (arg 1).bytes then (st, .ok .none) else fail "invalid notbefore value"
  | 88 => if gentimeOk (arg 1).bytes then (st, .ok .none) else fail "invalid notafter value"
  | 89 => match parseTimeoutC (arg 1).bytes with
    | some m => fail m
    | none => (st, .ok .none)
  | 112 => (st, .ok (.kind kALL))
  | 113 => (st, .ok (.kind kALIAS))
  | 114 =>
    if (arg 0).bytes.size ≥ 4096 then fail "command too long" else (st, .ok (.kind kCOMMAND))
  | 115 => if (arg 0).bytes == "list".toUTF8 then (st, .ok (.kind kCOMMAND))
    else fail "expected a fully-qualified path name"
  | _ =>
    match reservedNames.lookup rule with
    | some n => (st, .ok (.text n.toUTF8))
    | none => (st, .ok (if rhs.isEmpty then .none else arg 0))

inductive Lbl where
  | newstate | backup | dflt | reduce (rule : Nat) | errlab | errlab1

def yyfinal : Nat := 90
def yylast : Int := 332
def yyntokens : Nat := 65
def yypactNinf : Int := -116

def run (file : String) (lines : Array ByteArray) (eof : Bool) (aliases : Array Alias) : Scan :=
    Id.run do
  let size := lines.foldl (fun n l => n + l.size) 0
  let mut st : St := { file, lx := { lines, eof, fuel := 4 * size + 8 }, out := { aliases } }
  let mut lbl := Lbl.newstate
  let fuel := 64 * size + 256
  for _ in [0:fuel] do
    match lbl with
    | .newstate =>
      if st.stack.headD 0 == yyfinal then return st.out
      lbl := .backup
    | .backup =>
      let state := st.stack.headD 0
      let base := tbl yypact state
      if base == yypactNinf then
        lbl := .dflt
        continue
      if st.yychar.isNone then
        let (t, lx) := st.lx.next
        st := { st with lx, yychar := some t, yylval := .text lx.value, yyline := lx.li }
      let tok := st.yychar.getD 0
      let n := base + tok
      if n < 0 || yylast < n || tbl yycheck n != tok then
        lbl := .dflt
        continue
      let act := tbl yytable n
      if act ≤ 0 then
        lbl := .reduce (-act).toNat
        continue
      st := { st with
        errStatus := st.errStatus - 1, stack := act.toNat :: st.stack
        vals := st.yylval :: st.vals, yychar := none
        entryStart := some (st.entryStart.getD st.yyline) }
      lbl := .newstate
    | .dflt =>
      let r := tbl yydefact (st.stack.headD 0)
      lbl := if r == 0 then .errlab else .reduce r.toNat
    | .reduce rule =>
      let len := (tbl yyr2 rule).toNat
      let rhs := (st.vals.take len).reverse.toArray
      let (st', res) := st.action rule rhs
      st := st'
      match res with
      | .error () =>
        st := { st with stack := st.stack.drop len, vals := st.vals.drop len }
        lbl := .errlab1
      | .ok v =>
        let stack := st.stack.drop len
        let top := stack.headD 0
        let lhs := (tbl yyr1 rule).toNat - yyntokens
        let i := tbl yypgoto lhs + top
        let next := if 0 ≤ i && i ≤ yylast && tbl yycheck i == top then tbl yytable i
          else tbl yydefgoto lhs
        st := { st with stack := next.toNat :: stack, vals := v :: st.vals.drop len }
        if 6 ≤ rule && rule ≤ 19 then
          let spans := if rule == 7 || st.entryBad then st.out.spans
            else st.out.spans.push (st.entryStart.getD st.lx.li, st.lx.li)
          st := { st with out := { st.out with spans }, entryStart := none, entryBad := false }
        lbl := .newstate
    | .errlab =>
      if st.errStatus == 0 then st := st.yyerror "syntax error"
      if st.errStatus == 3 then
        if st.yychar == some kEOF then return st.out
        st := { st with yychar := none }
      lbl := .errlab1
    | .errlab1 =>
      st := { st with errStatus := 3 }
      let mut found : Option Nat := none
      for _ in [0:st.stack.length + 1] do
        let state := st.stack.headD 0
        let base := tbl yypact state
        if base != yypactNinf then
          let n := base + 1
          if 0 ≤ n && n ≤ yylast && tbl yycheck n == 1 then
            let t := tbl yytable n
            if 0 < t then
              found := some t.toNat
              break
        if st.stack.length ≤ 1 then break
        st := { st with stack := st.stack.tail, vals := st.vals.tail }
      match found with
      | none => return st.out
      | some t =>
        st := { st with stack := t :: st.stack, vals := st.yylval :: st.vals }
        lbl := .newstate
  return (st.errorf (some "syntax error")).out

def scanBytes (file : String) (bytes : ByteArray) (aliases : Array Alias := #[]) : Scan :=
  run file (splitLines bytes) (bytes.size > 0 && bytes.get! (bytes.size - 1) != u '\n') aliases

def scan (file text : String) (aliases : Array Alias := #[]) : Scan :=
  scanBytes file text.toUTF8 aliases

end Gram

end LeanSudo.Sudoers
