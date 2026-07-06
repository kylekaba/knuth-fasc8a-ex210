/-!
# SHA-256

A small SHA-256 implementation used by the certificate checker to verify the
upstream release hashes without calling an external hashing program.
-/

namespace KnuthFasc8aEx210

def rotr32 (x : UInt32) (n : Nat) : UInt32 :=
  (x >>> UInt32.ofNat n) ||| (x <<< UInt32.ofNat (32 - n))

def ch32 (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

def maj32 (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bigSigma0 (x : UInt32) : UInt32 :=
  rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22

def bigSigma1 (x : UInt32) : UInt32 :=
  rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25

def smallSigma0 (x : UInt32) : UInt32 :=
  rotr32 x 7 ^^^ rotr32 x 18 ^^^ (x >>> (3 : UInt32))

def smallSigma1 (x : UInt32) : UInt32 :=
  rotr32 x 17 ^^^ rotr32 x 19 ^^^ (x >>> (10 : UInt32))

def sha256K : Array UInt32 := #[
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
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

def sha256Initial : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

def u32BEAt (bytes : ByteArray) (offset : Nat) : UInt32 :=
  UInt32.ofNat <|
    bytes[offset]!.toNat * 16777216 +
    bytes[offset + 1]!.toNat * 65536 +
    bytes[offset + 2]!.toNat * 256 +
    bytes[offset + 3]!.toNat

def appendLength64BE (bytes : ByteArray) (bitLength : Nat) : ByteArray :=
  Id.run do
    let mut out := bytes
    for i in [0:8] do
      let shift := 8 * (7 - i)
      out := out.push (UInt8.ofNat ((bitLength / (2 ^ shift)) % 256))
    pure out

def sha256Pad (msg : ByteArray) : ByteArray :=
  Id.run do
    let bitLength := msg.size * 8
    let mut out := msg.push 0x80
    for _ in [0:64] do
      if out.size % 64 != 56 then
        out := out.push 0
    pure (appendLength64BE out bitLength)

def sha256Schedule (block : ByteArray) (offset : Nat) : Array UInt32 :=
  Id.run do
    let mut w := Array.replicate 64 (0 : UInt32)
    for t in [0:16] do
      w := w.set! t (u32BEAt block (offset + 4 * t))
    for t in [16:64] do
      let x :=
        smallSigma1 w[t - 2]! + w[t - 7]! +
        smallSigma0 w[t - 15]! + w[t - 16]!
      w := w.set! t x
    pure w

def sha256Compress (state : Array UInt32) (block : ByteArray) (offset : Nat) :
    Array UInt32 :=
  Id.run do
    let w := sha256Schedule block offset
    let mut a := state[0]!
    let mut b := state[1]!
    let mut c := state[2]!
    let mut d := state[3]!
    let mut e := state[4]!
    let mut f := state[5]!
    let mut g := state[6]!
    let mut h := state[7]!
    for t in [0:64] do
      let t1 := h + bigSigma1 e + ch32 e f g + sha256K[t]! + w[t]!
      let t2 := bigSigma0 a + maj32 a b c
      h := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    #[
      state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
      state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h
    ]

def sha256DigestWords (msg : ByteArray) : Array UInt32 :=
  Id.run do
    let padded := sha256Pad msg
    let mut state := sha256Initial
    for block in [0:padded.size / 64] do
      state := sha256Compress state padded (64 * block)
    pure state

def hexDigits : Array Char :=
  "0123456789abcdef".toList.toArray

def hexByte (n : Nat) : String :=
  String.singleton hexDigits[((n / 16) % 16)]! ++
    String.singleton hexDigits[n % 16]!

def hexWordBE (w : UInt32) : String :=
  let n := w.toNat
  hexByte ((n / 16777216) % 256) ++
  hexByte ((n / 65536) % 256) ++
  hexByte ((n / 256) % 256) ++
  hexByte (n % 256)

def sha256Hex (msg : ByteArray) : String :=
  (sha256DigestWords msg).foldl (init := "") fun acc w => acc ++ hexWordBE w

end KnuthFasc8aEx210
