import LeanSudo.Sudoers.Ast

namespace LeanSudo.Sha2

private def paddedByte (m : ByteArray) (total lengthBytes i : Nat) : UInt8 :=
  if i < m.size then m[i]!
  else if i == m.size then 0x80
  else if i < total - lengthBytes then 0
  else UInt8.ofNat ((m.size * 8) >>> (8 * (total - 1 - i)))

private def k32 : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

local macro "sha2Impl " word:ident ofByte:ident ofNat:ident toByte:ident
    rotr:ident compress:ident hash:ident bytes:ident
    bits:num wordBytes:num lengthBytes:num blockBytes:num rounds:num constants:ident
    "(" s00:num "," s01:num "," s02:num ")" "(" s10:num "," s11:num "," s12:num ")"
    "(" b00:num "," b01:num "," b02:num ")" "(" b10:num "," b11:num "," b12:num ")"
    : command => `(
  @[inline] private def $rotr (x n : $word) : $word :=
    (x >>> n) ||| (x <<< ($bits - n))

  private def $compress (m : ByteArray) (total offset : Nat)
      (state : Array $word) : Array $word := Id.run do
    let mut w : Array $word := Array.replicate $rounds 0
    for i in [:16] do
      let mut v : $word := 0
      for j in [:$wordBytes] do
        v := (v <<< 8) ||| $ofByte (paddedByte m total $lengthBytes
          (offset + i * $wordBytes + j))
      w := w.set! i v
    for i in [16:$rounds] do
      let x := w[i - 15]!
      let y := w[i - 2]!
      let s0 := $rotr x $s00 ^^^ $rotr x $s01 ^^^ (x >>> $s02)
      let s1 := $rotr y $s10 ^^^ $rotr y $s11 ^^^ (y >>> $s12)
      w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
    let mut a := state[0]!
    let mut b := state[1]!
    let mut c := state[2]!
    let mut d := state[3]!
    let mut e := state[4]!
    let mut f := state[5]!
    let mut g := state[6]!
    let mut h := state[7]!
    for i in [:$rounds] do
      let sum1 := $rotr e $b10 ^^^ $rotr e $b11 ^^^ $rotr e $b12
      let ch := (e &&& f) ^^^ (~~~e &&& g)
      let temp1 := h + sum1 + ch + $constants[i]! + w[i]!
      let sum0 := $rotr a $b00 ^^^ $rotr a $b01 ^^^ $rotr a $b02
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let temp2 := sum0 + maj
      h := g
      g := f
      f := e
      e := d + temp1
      d := c
      c := b
      b := a
      a := temp1 + temp2
    return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
      state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

  private def $hash (m : ByteArray) (initial : Array $word) : Array $word := Id.run do
    let blocks := (m.size + $lengthBytes + $blockBytes) / $blockBytes
    let mut state := initial
    for i in [:blocks] do
      state := $compress m (blocks * $blockBytes) (i * $blockBytes) state
    return state

  private def $bytes (state : Array $word) (size : Nat) : ByteArray :=
    ⟨Array.ofFn (fun (i : Fin size) =>
      $toByte (state[i.val / $wordBytes]! >>>
        $ofNat (8 * ($wordBytes - 1 - i.val % $wordBytes))))⟩)

sha2Impl UInt32 UInt8.toUInt32 UInt32.ofNat UInt32.toUInt8
  rotr32 compress32 hash32 bytes32 32 4 8 64 64 k32
  (7, 18, 3) (17, 19, 10) (2, 13, 22) (6, 11, 25)

private def k64 : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

sha2Impl UInt64 UInt8.toUInt64 UInt64.ofNat UInt64.toUInt8
  rotr64 compress64 hash64 bytes64 64 8 16 128 80 k64
  (1, 8, 7) (19, 61, 6) (28, 34, 39) (14, 18, 41)

def sha224 (m : ByteArray) : ByteArray :=
  bytes32 (hash32 m #[ 0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4 ]) 28

@[simp] theorem sha224_size (m : ByteArray) : (sha224 m).size = 28 := by
  simp [sha224, bytes32, ByteArray.size]

def sha256 (m : ByteArray) : ByteArray :=
  bytes32 (hash32 m #[ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]) 32

@[simp] theorem sha256_size (m : ByteArray) : (sha256 m).size = 32 := by
  simp [sha256, bytes32, ByteArray.size]

def sha384 (m : ByteArray) : ByteArray :=
  bytes64 (hash64 m #[ 0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939, 0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4 ]) 48

@[simp] theorem sha384_size (m : ByteArray) : (sha384 m).size = 48 := by
  simp [sha384, bytes64, ByteArray.size]

def sha512 (m : ByteArray) : ByteArray :=
  bytes64 (hash64 m #[ 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179 ]) 64

@[simp] theorem sha512_size (m : ByteArray) : (sha512 m).size = 64 := by
  simp [sha512, bytes64, ByteArray.size]

def digest (algo : Sudoers.DigestAlgo) (m : ByteArray) : ByteArray :=
  match algo with
  | .sha224 => sha224 m
  | .sha256 => sha256 m
  | .sha384 => sha384 m
  | .sha512 => sha512 m

end LeanSudo.Sha2
