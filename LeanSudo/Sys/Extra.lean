import LeanSudo.Sys.Core
import LeanSudo.Sys.Prim.Extra

namespace LeanSudo.Sys

private def cString (value : String) : String :=
  if value.contains '\x00' then String.ofList (value.toList.takeWhile (· != '\x00'))
  else value

def validDomainName (name : String) : Bool :=
  !name.isEmpty && !name.toList.any (fun c => " \t\r\n,()".contains c)

def domainName : IO (Option String) := do
  let (status, name) ← Prim.Extra.domain
  return if status == 0 && validDomainName name then some name else none

def usableInterface (c : Prim.Extra.Constants) (flags family : UInt32) : Bool :=
  flags &&& c.iffUp != 0 && flags &&& c.iffLoopback == 0 &&
    (family == c.afInet || family == c.afInet6)

theorem usableInterface_requires_family (c : Prim.Extra.Constants) (flags family : UInt32)
    (h : usableInterface c flags family = true) :
    family = c.afInet ∨ family = c.afInet6 := by
  simp only [usableInterface, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h.2

def interfaceAddresses : IO (Array (String × String)) := do
  let c := Prim.Extra.constants ()
  let (status, head) ← Prim.Extra.interfaces
  if status != 0 then throw (IO.userError "unable to read network interfaces")
  try
    let mut current := head
    let mut out := #[]
    while current != 0 do
      let address ← Prim.Extra.interfaceAddress current
      let mask ← Prim.Extra.interfaceMask current
      let flags ← Prim.Extra.interfaceFlags current
      if address != 0 && mask != 0 then
        let family ← Prim.Extra.addressFamily address
        if usableInterface c flags family then
          let addressBytes ←
            if family == c.afInet then Prim.Extra.addressV4 address
            else Prim.Extra.addressV6 address
          let maskBytes ←
            if family == c.afInet then Prim.Extra.addressV4 mask else Prim.Extra.addressV6 mask
          if let some addressText ← Prim.Extra.addressText family addressBytes then
            if let some maskText ← Prim.Extra.addressText family maskBytes then
              out := out.push (addressText, maskText)
      current ← Prim.Extra.interfaceNext current
    return out
  finally
    Prim.Extra.interfacesFree head

@[extern "leansudo_sys_netgroup"]
opaque inNetgroup (group : @& String) (host user domain : @& Option String) : IO Bool

private def regexNumber (limit : Nat) : List Char → Nat → Nat × List Char
  | [], n => (n, [])
  | '\\' :: c :: rest, n =>
    if c >= '0' && c <= '9' then
      let next := n * 10 + c.toNat - '0'.toNat
      if next > limit then (limit + 1, c :: rest)
      else regexNumber limit rest next
    else (n, '\\' :: c :: rest)
  | c :: rest, n =>
    if c >= '0' && c <= '9' then
      let next := n * 10 + c.toNat - '0'.toNat
      if next > limit then (limit + 1, c :: rest)
      else regexNumber limit rest next
    else (n, c :: rest)

private def regexRepetition (c : Char) : Bool :=
  c == '?' || c == '*' || c == '+' || c == '{'

private def regexCheckLoop (c : Prim.Extra.Constants) :
    Nat → List Char → Char → Nat → UInt32
  | 0, _, _, _ => 0
  | _ + 1, [], _, _ => 0
  | fuel + 1, '\\' :: _ :: rest, _, upper => regexCheckLoop c fuel rest '\x00' upper
  | fuel + 1, token :: rest, previous, upper =>
    if token == '?' || token == '*' || token == '+' then
      if regexRepetition previous then c.regBadrpt else regexCheckLoop c fuel rest token upper
    else if token == '{' then
      let (lower, afterLower) := regexNumber c.intMax.toNat rest 0
      let afterLower := match afterLower with
        | '\\' :: ',' :: rest => ',' :: rest
        | rest => rest
      let (upper, afterUpper) := match afterLower with
        | ',' :: rest => regexNumber c.intMax.toNat rest 0
        | rest => (upper, rest)
      match afterUpper with
      | '}' :: rest =>
        if lower > 255 || upper > 255 then c.regBadbr
        else if regexRepetition previous then c.regBadrpt
        else regexCheckLoop c fuel rest token upper
      | rest => regexCheckLoop c fuel rest '\x00' upper
    else regexCheckLoop c fuel rest token upper

def regexCheck (c : Prim.Extra.Constants) (pattern : String) : UInt32 :=
  let chars := pattern.toList
  regexCheckLoop c (chars.length + 1) chars '\x00' 0

def regexBaseFlags (c : Prim.Extra.Constants) : UInt32 :=
  c.regExtended ||| c.regNosub

def regexCaseAdjustment (c : Prim.Extra.Constants) (pattern : String) : String × UInt32 :=
  let flags := regexBaseFlags c
  if pattern.startsWith "^(?i)" then
    ("^" ++ String.ofList (pattern.toList.drop 5), flags ||| c.regIcase)
  else if pattern.startsWith "(?i)" then
    (String.ofList (pattern.toList.drop 4), flags ||| c.regIcase)
  else (pattern, flags)

theorem regexCaseAdjustment_plain (c : Prim.Extra.Constants) (pattern : String)
    (anchored : pattern.startsWith "^(?i)" = false)
    (plain : pattern.startsWith "(?i)" = false) :
    regexCaseAdjustment c pattern = (pattern, regexBaseFlags c) := by
  simp [regexCaseAdjustment, anchored, plain]

theorem regexCheck_repeated_star (c : Prim.Extra.Constants) (fuel : Nat)
    (rest : List Char) (previous : Char) (upper : Nat)
    (repeated : regexRepetition previous = true) :
    regexCheckLoop c (fuel + 1) ('*' :: rest) previous upper = c.regBadrpt := by
  simp [regexCheckLoop, repeated]

theorem regexCaseAdjustment_flags (c : Prim.Extra.Constants) (pattern : String) :
    (regexCaseAdjustment c pattern).2 = regexBaseFlags c ∨
    (regexCaseAdjustment c pattern).2 = regexBaseFlags c ||| c.regIcase := by
  unfold regexCaseAdjustment
  split
  · exact Or.inr rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

def regexMatches (pattern text : String) (locale : String := "C") : IO Bool := do
  let c := Prim.Extra.constants ()
  let pattern := cString pattern
  if pattern.toUTF8.size > 1024 then throw (IO.userError "regular expression too large")
  let (pattern, flags) := regexCaseAdjustment c pattern
  Prim.Extra.withLocale (cString locale) "unable to initialize matching locale" do
    let value ← Prim.Extra.regexAlloc
    try
      let checked := regexCheck c pattern
      let status ←
        if checked == 0 then Prim.Extra.regexCompile value pattern flags else pure checked
      if status != 0 then throw (IO.userError (← Prim.Extra.regexError status value))
      let status ← try Prim.Extra.regexExec value text finally Prim.Extra.regexFree value
      if status != 0 && status != c.regNomatch then
        throw (IO.userError "unable to match regular expression")
      return status == 0
    finally
      Prim.Extra.free value

def globPaths (pattern : String) (locale : String := "C") : IO (List String) :=
  Prim.Extra.withLocale (cString locale) "unable to initialize matching locale" do
    let value ← Prim.Extra.globAlloc
    try
      try
        let status ← Prim.Extra.glob value pattern
        if status == (Prim.Extra.constants ()).globNomatch then return []
        if status != 0 then throw (IO.userError "unable to expand command glob")
        let count ← Prim.Extra.globCount value
        let mut out := []
        for i in [:count.toNat] do
          let path ← Prim.Extra.globPath value (USize.ofNat (count.toNat - i - 1))
          out := path :: out
        return out
      finally
        Prim.Extra.globFree value
    finally
      Prim.Extra.free value

def canonicalHostname (host : String) : IO (Except String String) := do
  let (status, value) ← Prim.Extra.hostname host
  if status != 0 then return .error (← Prim.Extra.hostnameError status)
  try
    return .ok ((← Prim.Extra.hostnameName value).getD (cString host))
  finally
    Prim.Extra.hostnameFree value

def auditValue (bytes : List UInt8) : String :=
  if bytes.any (fun c => c < 0x21 || c > 0x7e || c == 0x22) then
    String.ofList (bytes.flatMap fun c =>
      let digit := fun n => Char.ofNat (if n < 10 then n + 48 else n + 55)
      [digit (c.toNat / 16), digit (c.toNat % 16)])
  else "\"" ++ String.ofList (bytes.map (fun c => Char.ofNat c.toNat)) ++ "\""

def auditTerminal (tty : String) : String :=
  let tty := cString tty
  if tty.toList.any (fun c => " \t\n\r\"'".contains c) then "(unknown)" else
    let tty := if tty.startsWith "/dev/" then String.ofList (tty.toList.drop 5) else tty
    if tty.isEmpty then "?" else tty

def auditCommandBytes (command : String) : List UInt8 :=
  let bytes := (cString command).toUTF8.data.toList
  (((bytes.dropWhile (· == 32)).reverse.dropWhile (fun c => c == 32 || c == 10)).reverse).take 4095

theorem auditCommandBytes_bounded (command : String) :
    (auditCommandBytes command).length ≤ 4095 := by
  simp only [auditCommandBytes, List.length_take]
  omega

def nativeBytes (little : Bool) (width value : Nat) : List UInt8 :=
  let bytes := (List.range width).map (fun i => UInt8.ofNat (value / 256 ^ i % 256))
  if little then bytes else bytes.reverse

def nativeValue (little : Bool) (bytes : List UInt8) : Nat :=
  let bytes := if little then bytes.reverse else bytes
  bytes.foldl (fun value byte => value * 256 + byte.toNat) 0

def setNative (bytes : ByteArray) (little : Bool) (offset width value : Nat) : ByteArray := Id.run do
  let mut bytes := bytes
  let mut index := offset
  for byte in nativeBytes little width value do
    bytes := bytes.set! index byte
    index := index + 1
  return bytes

def auditPacket (c : Prim.Extra.Constants) (little : Bool) (command tty : String)
    (cwd exe : ByteArray) (success : Bool) : ByteArray :=
  let payload := "cwd=" ++ auditValue cwd.data.toList ++
    " cmd=" ++ auditValue (auditCommandBytes command) ++
    " exe=" ++ auditValue exe.data.toList ++ " terminal=" ++ auditTerminal tty ++
    " res=" ++ (if success then "success" else "failed")
  let payload := payload.toUTF8.data.toList.take 8969 ++ [0]
  let header : ByteArray := ⟨Array.replicate c.nlHeaderSize.toNat 0⟩
  let header := setNative header little c.nlLengthOffset.toNat c.nlLengthWidth.toNat
    (c.nlHeaderSize.toNat + payload.length)
  let header := setNative header little c.nlTypeOffset.toNat c.nlTypeWidth.toNat
    c.auditUserCmd.toNat
  let header := setNative header little c.nlFlagsOffset.toNat c.nlFlagsWidth.toNat
    (c.nlmRequest ||| c.nlmAck).toNat
  let header := setNative header little c.nlSequenceOffset.toNat c.nlSequenceWidth.toNat 1
  let header := setNative header little c.nlPidOffset.toNat c.nlPidWidth.toNat 0
  header ++ ⟨payload.toArray⟩

def auditAcknowledged (c : Prim.Extra.Constants) (little : Bool) (sender : UInt32)
    (bytes : ByteArray) : Bool :=
  let data := bytes.data.toList
  let field := fun (offset width : UInt32) =>
    UInt32.ofNat (nativeValue little ((data.drop offset.toNat).take width.toNat))
  let length := (field c.nlLengthOffset c.nlLengthWidth).toNat
  let error := field c.nlErrorOffset c.nlErrorWidth
  sender == 0 && bytes.size >= c.nlErrorSize.toNat &&
    field c.nlTypeOffset c.nlTypeWidth == c.nlmsgError &&
    field c.nlSequenceOffset c.nlSequenceWidth == 1 &&
    length <= bytes.size && length >= c.nlErrorSize.toNat &&
    (error == 0 || error == 0 - c.econnrefused || error == 0 - c.eprotonosupport)

theorem auditAcknowledged_kernel_only (c : Prim.Extra.Constants) (little : Bool)
    (sender : UInt32) (bytes : ByteArray)
    (h : auditAcknowledged c little sender bytes = true) : sender = 0 := by
  simp only [auditAcknowledged, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1

theorem auditValue_quoted (bytes : List UInt8)
    (safe : bytes.any (fun c => c < 0x21 || c > 0x7e || c == 0x22) = false) :
    auditValue bytes = "\"" ++ String.ofList (bytes.map (fun c => Char.ofNat c.toNat)) ++ "\"" := by
  simp [auditValue, safe]

theorem auditTerminal_sanitized (tty : String)
    (rejected : (cString tty).toList.any (fun c => " \t\n\r\"'".contains c) = true) :
    auditTerminal tty = "(unknown)" := by
  simp only [auditTerminal, rejected, ↓reduceIte]

def auditCommand (command tty : String) (success : Bool) : IO Bool := do
  let c := Prim.Extra.constants ()
  let (status, fd) ← Prim.Extra.socket c.afNetlink (c.sockRaw ||| c.sockCloexec) c.netlinkAudit
  if status != 0 then
    return status == c.eafnosupport || status == c.eprotonosupport || status == c.einval
  try
    let cwd := (← Prim.Extra.cwd).getD "?".toUTF8
    let exe := (← Prim.Extra.readlink "/proc/self/exe").getD "?".toUTF8
    let little := Prim.Extra.littleEndian ()
    let status ← Prim.Extra.netlinkSend fd (auditPacket c little command tty cwd exe success)
    if status != 0 then return status == c.econnrefused || status == c.eprotonosupport
    let (ready, error) ← Prim.Extra.poll fd 1000
    if error != 0 || ready <= 0 then return false
    let some (sender, bytes) ← Prim.Extra.netlinkReceive fd | return false
    return auditAcknowledged c little sender bytes
  finally
    let _ ← Prim.Extra.close fd
    pure ()

def commandLookupRoot (root : Option String) : Option String :=
  root.filter (· != "*")

theorem commandLookupRoot_wildcard : commandLookupRoot (some "*") = none := by
  rfl

theorem wildcard_lookup_path (path : String) :
    ((commandLookupRoot (some "*")).map (· ++ path)).getD path = path := by
  rfl

def withinRoot (root path : String) : Bool :=
  root == "/" || path == root || path.startsWith (root ++ "/")

theorem withinRoot_boundary (root path : String) (hr : root ≠ "/")
    (hp : path ≠ root) (h : withinRoot root path = true) :
    path.startsWith (root ++ "/") = true := by
  simpa [withinRoot, hr, hp] using h

def rootPathEscapes (root path : String) : IO Bool := do
  let canonical := (← realpath root).getD root
  let some resolved ← realpath (root ++ path) | return false
  return !withinRoot canonical resolved

end LeanSudo.Sys
