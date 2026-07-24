import Std

/-!
# Parsers for the checked-in certificate files

These definitions parse the binary formats used by
`kylekaba/knuth-fasc8a-ex210`:

* `KMC201` sparse matrices modulo 101;
* `KMV101` eigenvectors;
* `KMP101` visible-factor polynomials;
* `KMW2CERT` Wiedemann/Berlekamp--Massey rank certificates.

The parsers are intentionally small and fail closed on malformed or trailing
data.
-/

namespace KnuthFasc8aEx210

structure Cursor where
  bytes : ByteArray
  offset : Nat

abbrev ParseM := Except String

def Cursor.remaining (c : Cursor) : Nat :=
  c.bytes.size - c.offset

def Cursor.need (c : Cursor) (n : Nat) (what : String) : ParseM Unit :=
  if c.offset + n <= c.bytes.size then
    .ok ()
  else
    .error s!"truncated while reading {what}"

def Cursor.readU8 (c : Cursor) (what : String) : ParseM (UInt8 × Cursor) := do
  c.need 1 what
  pure (c.bytes[c.offset]!, { c with offset := c.offset + 1 })

def Cursor.readU32LE (c : Cursor) (what : String) : ParseM (Nat × Cursor) := do
  c.need 4 what
  let b0 := c.bytes[c.offset]!.toNat
  let b1 := c.bytes[c.offset + 1]!.toNat
  let b2 := c.bytes[c.offset + 2]!.toNat
  let b3 := c.bytes[c.offset + 3]!.toNat
  pure (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3,
    { c with offset := c.offset + 4 })

def Cursor.readU64LE (c : Cursor) (what : String) : ParseM (UInt64 × Cursor) := do
  c.need 8 what
  let mut n : Nat := 0
  for i in [0:8] do
    n := n + c.bytes[c.offset + i]!.toNat * (256 ^ i)
  pure (UInt64.ofNat n, { c with offset := c.offset + 8 })

def Cursor.readBytes (c : Cursor) (n : Nat) (what : String) :
    ParseM (ByteArray × Cursor) := do
  c.need n what
  let mut out := ByteArray.empty
  for i in [0:n] do
    out := out.push c.bytes[c.offset + i]!
  pure (out, { c with offset := c.offset + n })

def ByteArray.hasAsciiPrefix (bytes : ByteArray) (s : String) : Bool :=
  let target := s.toUTF8
  if target.size <= bytes.size then
    Id.run do
      let mut ok := true
      for i in [0:target.size] do
        if bytes[i]! != target[i]! then
          ok := false
      pure ok
  else
    false

def ByteArray.asciiEquals (bytes : ByteArray) (s : String) : Bool :=
  bytes.size == s.toUTF8.size && ByteArray.hasAsciiPrefix bytes s

def require (p : Bool) (msg : String) : ParseM Unit :=
  if p then .ok () else .error msg

def requireNoTrailing (c : Cursor) : ParseM Unit :=
  require (c.offset == c.bytes.size) s!"trailing bytes: {c.bytes.size - c.offset}"

def p101 : Nat := 101

def u8Mod101 (n : Nat) : UInt8 :=
  UInt8.ofNat (n % p101)

/-- Every byte is a canonical representative of an element of `ZMod 101`. -/
def byteArrayIsCanonicalMod101 (bytes : ByteArray) : Bool :=
  Id.run do
    let mut canonical := true
    for b in bytes do
      if 101 <= b.toNat then
        canonical := false
    pure canonical

def readMagicPrefix (c : Cursor) (expected : String) : ParseM Cursor := do
  let (m, c) ← c.readBytes 8 "magic"
  require (ByteArray.hasAsciiPrefix m expected) s!"bad magic, expected prefix {expected}"
  pure c

def readMagicExact (c : Cursor) (expected : String) : ParseM Cursor := do
  let (m, c) ← c.readBytes 8 "magic"
  require (ByteArray.asciiEquals m expected) s!"bad magic, expected {expected}"
  pure c

structure MatrixHeader where
  n : Nat
  prime : Nat
  entries : Nat
  rowPtrOffset : Nat
  colIndexOffset : Nat
  valueOffset : Nat
  rowPtrBytes : Nat
  colIndexBytes : Nat
  valueBytes : Nat
  trailingBytes : Nat
deriving Repr

def parseMatrixHeader (bytes : ByteArray) : ParseM MatrixHeader := do
  let mut c : Cursor := { bytes, offset := 0 }
  c ← readMagicPrefix c "KMC201"
  let (n, c1) ← c.readU32LE "matrix dimension"
  c := c1
  let (prime, c1) ← c.readU32LE "matrix prime"
  c := c1
  let (entries64, c1) ← c.readU64LE "matrix entry count"
  c := c1
  let entries := entries64.toNat
  let (_, c1) ← c.readU32LE "matrix reserved word 1"
  c := c1
  let (_, c1) ← c.readU32LE "matrix reserved word 2"
  c := c1
  let rowPtrBytes := 8 * (n + 1)
  let colIndexBytes := 4 * entries
  let valueBytes := entries
  let rowPtrOffset := c.offset
  let colIndexOffset := rowPtrOffset + rowPtrBytes
  let valueOffset := colIndexOffset + colIndexBytes
  let minimumSize := c.offset + rowPtrBytes + colIndexBytes + valueBytes
  require (minimumSize <= bytes.size) "matrix file is too short for header counts"
  pure {
    n, prime, entries,
    rowPtrOffset, colIndexOffset, valueOffset,
    rowPtrBytes, colIndexBytes, valueBytes,
    trailingBytes := bytes.size - minimumSize
  }

def u32LEAt (bytes : ByteArray) (offset : Nat) : Nat :=
  bytes[offset]!.toNat +
    256 * bytes[offset + 1]!.toNat +
    65536 * bytes[offset + 2]!.toNat +
    16777216 * bytes[offset + 3]!.toNat

def u64LEAtNat (bytes : ByteArray) (offset : Nat) : Nat :=
  Id.run do
    let mut n := 0
    for i in [0:8] do
      n := n + bytes[offset + i]!.toNat * (256 ^ i)
    pure n

structure MatrixValidation where
  rows : Nat
  entries : Nat
  trailingBytes : Nat
  stateLabelBytes : Nat
deriving Repr

def validateMatrixCSR (bytes : ByteArray) (header : MatrixHeader) :
    ParseM MatrixValidation := do
  require (header.prime == 101) "matrix prime is not 101"
  let mut previous := u64LEAtNat bytes header.rowPtrOffset
  require (previous == 0) "first row pointer is not zero"
  for i in [1:header.n + 1] do
    let current := u64LEAtNat bytes (header.rowPtrOffset + 8 * i)
    require (previous <= current) s!"row pointers decrease at row {i}"
    require (current <= header.entries) s!"row pointer exceeds entry count at row {i}"
    previous := current
  require (previous == header.entries) "final row pointer does not equal entry count"
  for k in [0:header.entries] do
    let col := u32LEAt bytes (header.colIndexOffset + 4 * k)
    require (col < header.n) s!"column index out of range at entry {k}"
  for k in [0:header.entries] do
    let value := bytes[header.valueOffset + k]!.toNat
    require (value < 101) s!"matrix value is not reduced modulo 101 at entry {k}"
  require (header.trailingBytes == 8 * header.n)
    s!"matrix state-label tail has {header.trailingBytes} bytes, expected {8 * header.n}"
  pure {
    rows := header.n,
    entries := header.entries,
    trailingBytes := header.trailingBytes
    stateLabelBytes := header.trailingBytes
  }

def matrixValueAt (bytes : ByteArray) (header : MatrixHeader) (entry : Nat) : Nat :=
  bytes[header.valueOffset + entry]!.toNat

def matrixColumnAt (bytes : ByteArray) (header : MatrixHeader) (entry : Nat) : Nat :=
  u32LEAt bytes (header.colIndexOffset + 4 * entry)

def matrixRowStart (bytes : ByteArray) (header : MatrixHeader) (row : Nat) : Nat :=
  u64LEAtNat bytes (header.rowPtrOffset + 8 * row)

def matrixRowStop (bytes : ByteArray) (header : MatrixHeader) (row : Nat) : Nat :=
  u64LEAtNat bytes (header.rowPtrOffset + 8 * (row + 1))

def matrixStateLabelOffset (header : MatrixHeader) : Nat :=
  header.valueOffset + header.valueBytes

def matrixStateLabelAt (bytes : ByteArray) (header : MatrixHeader) (row : Nat) : Nat :=
  u64LEAtNat bytes (matrixStateLabelOffset header + 8 * row)

structure EigenvectorFile where
  n : Nat
  pivot : Nat
  pivotValue : UInt8
  values : ByteArray
  length : Nat

def EigenvectorFile.summary (e : EigenvectorFile) : String :=
  s!"n={e.n}, pivot={e.pivot}, pivotValue={e.pivotValue.toNat}"

def parseEigenvector (bytes : ByteArray) : ParseM EigenvectorFile := do
  let mut c : Cursor := { bytes, offset := 0 }
  c ← readMagicPrefix c "KMV101"
  let (n, c1) ← c.readU32LE "eigenvector dimension"
  c := c1
  let (pivot, c1) ← c.readU32LE "eigenvector pivot"
  c := c1
  require (pivot < n) "eigenvector pivot out of range"
  let (v, c1) ← c.readBytes n "eigenvector entries"
  c := c1
  requireNoTrailing c
  pure {
    n,
    pivot,
    pivotValue := v[pivot]!,
    values := v,
    length := n
  }

def eigenValueAt (eig : EigenvectorFile) (i : Nat) : Nat :=
  eig.values[i]!.toNat

/-- Count nonzero rows of `(A - 50I) v` over `F_101`. -/
def eigenResidualBadRows (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) : ParseM Nat := do
  require (eig.n == header.n) "eigenvector dimension does not match matrix"
  let mut bad := 0
  for row in [0:header.n] do
    let start := matrixRowStart matrixBytes header row
    let stop := matrixRowStop matrixBytes header row
    let mut sum := 0
    for entry in [start:stop] do
      let col := matrixColumnAt matrixBytes header entry
      sum := sum + matrixValueAt matrixBytes header entry * eigenValueAt eig col
    let residual := (sum + 101 - (50 * eigenValueAt eig row) % 101) % 101
    if residual != 0 then
      bad := bad + 1
  pure bad

structure PolynomialFile where
  length : Nat
  degree : Nat
  coefficients : ByteArray

def parsePolynomial (bytes : ByteArray) : ParseM PolynomialFile := do
  let mut c : Cursor := { bytes, offset := 0 }
  c ← readMagicPrefix c "KMP101"
  let (length, c1) ← c.readU32LE "polynomial length"
  c := c1
  let (coefficients, c1) ← c.readBytes length "polynomial coefficients"
  c := c1
  requireNoTrailing c
  require (0 < length) "empty polynomial"
  for i in [0:length] do
    require (coefficients[i]!.toNat < 101)
      s!"polynomial coefficient is not reduced modulo 101 at index {i}"
  require (coefficients[length - 1]!.toNat != 0) "zero leading polynomial coefficient"
  pure { length, degree := length - 1, coefficients }

structure FinishVectorFile where
  n : Nat
  values : ByteArray

def parseFinishVector (bytes : ByteArray) : ParseM FinishVectorFile := do
  let mut c : Cursor := { bytes, offset := 0 }
  let (n, c1) ← c.readU32LE "finish vector dimension"
  c := c1
  let (values, c1) ← c.readBytes n "finish vector entries"
  c := c1
  requireNoTrailing c
  for i in [0:n] do
    require (values[i]!.toNat < 101)
      s!"finish vector entry is not reduced modulo 101 at index {i}"
  pure { n, values }

def byteVectorAt (v : Array UInt8) (i : Nat) : Nat :=
  v[i]!.toNat

def byteArrayToVector (bytes : ByteArray) : Array UInt8 :=
  Id.run do
    let mut out := Array.emptyWithCapacity bytes.size
    for i in [0:bytes.size] do
      out := out.push bytes[i]!
    pure out

def zeroByteVector (n : Nat) : Array UInt8 :=
  Array.replicate n 0

def addScaledByteVector (v : Array UInt8) (c : UInt8) (b : Array UInt8) :
    Array UInt8 :=
  Id.run do
    let n := Nat.min v.size b.size
    let mut out := Array.emptyWithCapacity n
    for i in [0:n] do
      out := out.push <| u8Mod101 (v[i]!.toNat + c.toNat * b[i]!.toNat)
    pure out

def matrixApplyByteVector (matrixBytes : ByteArray) (header : MatrixHeader)
    (x : Array UInt8) : ParseM (Array UInt8) := do
  require (x.size == header.n) "byte vector has wrong dimension"
  let mut y := Array.emptyWithCapacity header.n
  for row in [0:header.n] do
    let start := matrixRowStart matrixBytes header row
    let stop := matrixRowStop matrixBytes header row
    let mut sum := 0
    for entry in [start:stop] do
      let col := matrixColumnAt matrixBytes header entry
      sum := sum + matrixValueAt matrixBytes header entry * byteVectorAt x col
    y := y.push (u8Mod101 sum)
  pure y

def matrixApplyByteVectorTwice (matrixBytes : ByteArray) (header : MatrixHeader)
    (x : Array UInt8) : ParseM (Array UInt8) := do
  let t ← matrixApplyByteVector matrixBytes header x
  matrixApplyByteVector matrixBytes header t

def scaledVectorMismatchCount (lhs : Array UInt8) (scalar : Nat)
    (rhs : Array UInt8) : ParseM Nat := do
  require (lhs.size == rhs.size) "scaled-vector comparison dimension mismatch"
  let mut bad := 0
  for i in [0:lhs.size] do
    if lhs[i]! != u8Mod101 (scalar * rhs[i]!.toNat) then
      bad := bad + 1
  pure bad

def matrixStateIndexMap (bytes : ByteArray) (header : MatrixHeader) :
    Std.HashMap Nat Nat :=
  Id.run do
    let mut pos : Std.HashMap Nat Nat := {}
    for i in [0:header.n] do
      pos := pos.insert (matrixStateLabelAt bytes header i) i
    pure pos

def restrictedEigenMismatchCount (tallBytes : ByteArray) (tall : MatrixHeader)
    (relBytes : ByteArray) (rel : MatrixHeader) (eig : EigenvectorFile)
    (v : Array UInt8) : ParseM Nat := do
  require (v.size == tall.n) "visible vector dimension does not match Tall_plus"
  require (eig.n == rel.n) "restricted eigenvector dimension does not match Trel_plus"
  let pos := matrixStateIndexMap tallBytes tall
  let mut bad := 0
  for i in [0:rel.n] do
    match pos.get? (matrixStateLabelAt relBytes rel i) with
    | none => bad := bad + 1
    | some j =>
        if eig.values[i]! != v[j]! then
          bad := bad + 1
  pure bad

/--
Runs the first `steps` Horner iterations of `g(A^2) beta`, starting from the
highest-degree coefficient of `g`.
-/
def visiblePolynomialHornerPrefix (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile) (steps : Nat) :
    ParseM (Array UInt8) := do
  require (finish.n == header.n) "finish vector dimension does not match matrix"
  let beta := byteArrayToVector finish.values
  let mut v := zeroByteVector header.n
  let limit := Nat.min steps poly.length
  for s in [0:limit] do
    v ← matrixApplyByteVectorTwice matrixBytes header v
    let coeff := poly.coefficients[poly.length - 1 - s]!
    if coeff != 0 then
      v := addScaledByteVector v coeff beta
  pure v

structure VisibleFactorCheck where
  rBare : UInt8
  vBare : UInt8
  eigen76Bad : Nat
  eigen50Bad : Nat
  restrictedMismatch : Nat

def visibleFactorFullCheck (tallBytes : ByteArray) (tall : MatrixHeader)
    (relBytes : ByteArray) (rel : MatrixHeader) (poly : PolynomialFile)
    (finish : FinishVectorFile) (eig : EigenvectorFile) :
    ParseM VisibleFactorCheck := do
  let r ← visiblePolynomialHornerPrefix tallBytes tall poly finish poly.length
  require (0 < r.size) "empty visible vector"
  let ar2 ← matrixApplyByteVectorTwice tallBytes tall r
  let eigen76Bad ← scaledVectorMismatchCount ar2 76 r
  let ar ← matrixApplyByteVector tallBytes tall r
  let v := addScaledByteVector r 99 ar
  require (v.size == tall.n) "derived 50-eigenvector has wrong dimension"
  let av ← matrixApplyByteVector tallBytes tall v
  let eigen50Bad ← scaledVectorMismatchCount av 50 v
  let restrictedMismatch ← restrictedEigenMismatchCount tallBytes tall relBytes rel eig v
  pure {
    rBare := r[0]!,
    vBare := v[0]!,
    eigen76Bad,
    eigen50Bad,
    restrictedMismatch
  }

structure RankCertificateFile where
  version : Nat
  prime : Nat
  nonresidue : Nat
  n : Nat
  lambda : Nat
  border : Bool
  pivot : Nat
  terms : Nat
  bmTerms : Nat
  degree : Nat
  seed : UInt64
  matrixHash : UInt64
  eigenHash : UInt64
  constantA : UInt8
  constantB : UInt8
  moments : ByteArray
  coefficients : ByteArray

def parseRankCertificate (bytes : ByteArray) : ParseM RankCertificateFile := do
  let mut c : Cursor := { bytes, offset := 0 }
  c ← readMagicExact c "KMW2CERT"
  let (version, c1) ← c.readU32LE "certificate version"
  c := c1
  let (prime, c1) ← c.readU32LE "certificate prime"
  c := c1
  let (nonresidue, c1) ← c.readU32LE "certificate nonresidue"
  c := c1
  let (n, c1) ← c.readU32LE "certificate order"
  c := c1
  let (lambda, c1) ← c.readU32LE "certificate lambda"
  c := c1
  let (borderRaw, c1) ← c.readU32LE "certificate border flag"
  c := c1
  let (pivot, c1) ← c.readU32LE "certificate pivot"
  c := c1
  let (terms, c1) ← c.readU32LE "certificate terms"
  c := c1
  let (bmTerms, c1) ← c.readU32LE "certificate BM terms"
  c := c1
  let (degree, c1) ← c.readU32LE "certificate degree"
  c := c1
  let (seed, c1) ← c.readU64LE "certificate seed"
  c := c1
  let (matrixHash, c1) ← c.readU64LE "certificate matrix hash"
  c := c1
  let (eigenHash, c1) ← c.readU64LE "certificate eigen hash"
  c := c1
  require (version == 2) "unsupported certificate version"
  require (prime == 101) "certificate prime is not 101"
  require (nonresidue == 2) "certificate nonresidue is not 2"
  require (lambda == 50) "certificate lambda is not 50"
  require (borderRaw == 0 || borderRaw == 1) "bad border flag"
  require (terms == bmTerms + 32) "term count does not equal BM terms plus 32"
  require (bmTerms == 2 * n) "BM term count is not twice the order"
  require (degree == n) "BM degree is not full order"
  let momentBytes := 2 * terms
  let coefficientBytes := 2 * (degree + 1)
  let (moments, c1) ← c.readBytes momentBytes "stored moments"
  c := c1
  let (coefficients, c1) ← c.readBytes coefficientBytes "stored BM coefficients"
  c := c1
  requireNoTrailing c
  require (byteArrayIsCanonicalMod101 moments)
    "stored moment byte is not reduced modulo 101"
  require (byteArrayIsCanonicalMod101 coefficients)
    "stored connection-polynomial byte is not reduced modulo 101"
  let constantA := coefficients[coefficientBytes - 2]!
  let constantB := coefficients[coefficientBytes - 1]!
  require (constantA != 0 || constantB != 0) "zero constant coefficient"
  pure {
    version, prime, nonresidue, n, lambda,
    border := borderRaw == 1,
    pivot, terms, bmTerms, degree, seed, matrixHash, eigenHash,
    constantA, constantB, moments, coefficients
  }

structure ExtElt where
  a : UInt8
  b : UInt8
deriving DecidableEq, Repr, Inhabited

def ExtElt.add (x y : ExtElt) : ExtElt where
  a := u8Mod101 (x.a.toNat + y.a.toNat)
  b := u8Mod101 (x.b.toNat + y.b.toNat)

def ExtElt.mul (x y : ExtElt) : ExtElt where
  a := u8Mod101 (x.a.toNat * y.a.toNat + 2 * x.b.toNat * y.b.toNat)
  b := u8Mod101 (x.a.toNat * y.b.toNat + x.b.toNat * y.a.toNat)

def u8SubMod101 (x y : UInt8) : UInt8 :=
  if y.toNat <= x.toNat then
    UInt8.ofNat (x.toNat - y.toNat)
  else
    UInt8.ofNat (x.toNat + 101 - y.toNat)

def ExtElt.sub (x y : ExtElt) : ExtElt where
  a := u8SubMod101 x.a y.a
  b := u8SubMod101 x.b y.b

def ExtElt.scale (c : Nat) (x : ExtElt) : ExtElt where
  a := u8Mod101 (c * x.a.toNat)
  b := u8Mod101 (c * x.b.toNat)

def ExtElt.isZero (x : ExtElt) : Bool :=
  x.a == 0 && x.b == 0

def inverseMod101? (a : Nat) : Option UInt8 :=
  Id.run do
    let mut out : Option UInt8 := none
    for b in [1:101] do
      if (a * b) % 101 == 1 then
        out := some (UInt8.ofNat b)
    pure out

def ExtElt.inv (x : ExtElt) : ParseM ExtElt := do
  let denom :=
    (x.a.toNat * x.a.toNat + 101 -
      (2 * x.b.toNat * x.b.toNat) % 101) % 101
  match inverseMod101? denom with
  | none => .error "attempted to invert zero extension-field element"
  | some q =>
      pure {
        a := u8Mod101 (x.a.toNat * q.toNat),
        b := u8Mod101 ((if x.b == 0 then 0 else 101 - x.b.toNat) * q.toNat)
      }

def ExtElt.div (x y : ExtElt) : ParseM ExtElt := do
  pure (x.mul (← y.inv))

def pairAt (bytes : ByteArray) (i : Nat) : ExtElt where
  a := bytes[2 * i]!
  b := bytes[2 * i + 1]!

structure BMResult where
  degree : Nat
  coefficients : Array ExtElt

def berlekampMassey (moments : ByteArray) (used : Nat) : ParseM BMResult := do
  require (2 * used <= moments.size) "not enough moments for BM replay"
  let capacity := used + 1
  let zero : ExtElt := { a := 0, b := 0 }
  let one : ExtElt := { a := 1, b := 0 }
  let mut connection := Array.replicate capacity zero
  let mut previous := Array.replicate capacity zero
  let mut saved := Array.replicate capacity zero
  connection := connection.set! 0 one
  previous := previous.set! 0 one
  let mut clen := 1
  let mut blen := 1
  let mut degree := 0
  let mut shift := 1
  let mut discrepancyBase := one
  for n in [0:used] do
    let mut discrepancy := pairAt moments n
    for i in [1:degree + 1] do
      let q := pairAt moments (n - i)
      discrepancy := discrepancy.add (connection[i]!.mul q)
    if discrepancy.isZero then
      shift := shift + 1
    else
      let jump := 2 * degree <= n
      let oldLength := clen
      if jump then
        for i in [0:clen] do
          saved := saved.set! i connection[i]!
      let coef ← discrepancy.div discrepancyBase
      let need := blen + shift
      if clen < need then
        clen := need
      for j in [0:blen] do
        let k := j + shift
        connection := connection.set! k
          (connection[k]!.sub (coef.mul previous[j]!))
      if jump then
        degree := n + 1 - degree
        for i in [0:oldLength] do
          previous := previous.set! i saved[i]!
        blen := oldLength
        discrepancyBase := discrepancy
        shift := 1
      else
        shift := shift + 1
  let mut coefficients := Array.emptyWithCapacity (degree + 1)
  for i in [0:degree + 1] do
    coefficients := coefficients.push (if i < clen then connection[i]! else zero)
  pure { degree, coefficients }

structure BMReplayCheck where
  degree : Nat
  coefficientBad : Nat

def RankCertificateFile.bmReplayCheck (cert : RankCertificateFile) :
    ParseM BMReplayCheck := do
  let bm ← berlekampMassey cert.moments cert.bmTerms
  let limit := Nat.min bm.coefficients.size (cert.degree + 1)
  let mut bad := 0
  for i in [0:limit] do
    if bm.coefficients[i]! != pairAt cert.coefficients i then
      bad := bad + 1
  bad := bad + (bm.coefficients.size - limit) + (cert.degree + 1 - limit)
  pure { degree := bm.degree, coefficientBad := bad }

def splitmix64Step (state : UInt64) : UInt64 × UInt64 :=
  let state := state + (11400714819323198485 : UInt64)
  let z := state
  let z := (z ^^^ (z >>> 30)) * (13787848793156543929 : UInt64)
  let z := (z ^^^ (z >>> 27)) * (10723151780598845931 : UInt64)
  (z ^^^ (z >>> 31), state)

def drawMod101 (state : UInt64) : UInt8 × UInt64 :=
  let (x, state) := splitmix64Step state
  (u8Mod101 x.toNat, state)

def drawPairMod101 (state : UInt64) : ExtElt × UInt64 :=
  let (a, state) := drawMod101 state
  let (b, state) := drawMod101 state
  ({ a, b }, state)

partial def drawNonzeroPairMod101 (state : UInt64) (rejections : Nat := 0) :
    ExtElt × UInt64 × Nat :=
  let (x, state) := drawPairMod101 state
  if x.isZero then
    drawNonzeroPairMod101 state (rejections + 1)
  else
    (x, state, rejections)

structure SeedExpansionSummary where
  order : Nat
  diagonalRejections : Nat
  finalState : UInt64
deriving Repr

structure KrylovSeedData where
  dR : Array ExtElt
  dL : Array ExtElt
  u : Array ExtElt
  x : Array ExtElt
  diagonalRejections : Nat
  finalState : UInt64

/--
Replays the random object generation used by the rank verifier:
nonzero `dR`, nonzero `dL`, then one unrestricted `u` and `x` pair.
-/
def rankSeedData (order : Nat) (seed : UInt64) : KrylovSeedData :=
  Id.run do
    let mut state := seed
    let mut diagonalRejections := 0
    let mut dR := Array.emptyWithCapacity order
    let mut dL := Array.emptyWithCapacity order
    let mut u := Array.emptyWithCapacity order
    let mut x := Array.emptyWithCapacity order
    for _ in [0:order] do
      let (dr, stateAfterDR, rejectedDR) := drawNonzeroPairMod101 state
      state := stateAfterDR
      diagonalRejections := diagonalRejections + rejectedDR
      dR := dR.push dr
      let (dl, stateAfterDL, rejectedDL) := drawNonzeroPairMod101 state
      state := stateAfterDL
      diagonalRejections := diagonalRejections + rejectedDL
      dL := dL.push dl
      let (ui, stateAfterU) := drawPairMod101 state
      state := stateAfterU
      u := u.push ui
      let (xi, stateAfterX) := drawPairMod101 state
      state := stateAfterX
      x := x.push xi
    pure { dR, dL, u, x, diagonalRejections, finalState := state }

def pushExtByteArray (bytes : ByteArray) (x : ExtElt) : ByteArray :=
  (bytes.push x.a).push x.b

structure KrylovSeedByteData where
  dR : ByteArray
  dL : ByteArray
  u : ByteArray
  x : ByteArray
  diagonalRejections : Nat
  finalState : UInt64

def rankSeedByteData (order : Nat) (seed : UInt64) : KrylovSeedByteData :=
  Id.run do
    let mut state := seed
    let mut diagonalRejections := 0
    let mut dR := ByteArray.emptyWithCapacity (2 * order)
    let mut dL := ByteArray.emptyWithCapacity (2 * order)
    let mut u := ByteArray.emptyWithCapacity (2 * order)
    let mut x := ByteArray.emptyWithCapacity (2 * order)
    for _ in [0:order] do
      let (dr, stateAfterDR, rejectedDR) := drawNonzeroPairMod101 state
      state := stateAfterDR
      diagonalRejections := diagonalRejections + rejectedDR
      dR := pushExtByteArray dR dr
      let (dl, stateAfterDL, rejectedDL) := drawNonzeroPairMod101 state
      state := stateAfterDL
      diagonalRejections := diagonalRejections + rejectedDL
      dL := pushExtByteArray dL dl
      let (ui, stateAfterU) := drawPairMod101 state
      state := stateAfterU
      u := pushExtByteArray u ui
      let (xi, stateAfterX) := drawPairMod101 state
      state := stateAfterX
      x := pushExtByteArray x xi
    pure { dR, dL, u, x, diagonalRejections, finalState := state }

def rankSeedExpansionSummary (order : Nat) (seed : UInt64) :
    SeedExpansionSummary :=
  let data := rankSeedData order seed
  { order, diagonalRejections := data.diagonalRejections, finalState := data.finalState }

def extDot (u x : Array ExtElt) (n : Nat) : ExtElt :=
  Id.run do
    let mut ar := 0
    let mut ai := 0
    for i in [0:n] do
      let p := u[i]!.mul x[i]!
      ar := ar + p.a.toNat
      ai := ai + p.b.toNat
    pure { a := u8Mod101 ar, b := u8Mod101 ai }

def extDotBytes (u x : ByteArray) (n : Nat) : ExtElt :=
  Id.run do
    let mut ar := 0
    let mut ai := 0
    for i in [0:n] do
      let j := 2 * i
      let ua := u[j]!.toNat
      let ub := u[j + 1]!.toNat
      let xa := x[j]!.toNat
      let xb := x[j + 1]!.toNat
      ar := ar + ua * xa + 2 * ub * xb
      ai := ai + ua * xb + ub * xa
    pure { a := u8Mod101 ar, b := u8Mod101 ai }

def matrixApplyShifted (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig? : Option EigenvectorFile) (x : Array ExtElt) : ParseM (Array ExtElt) := do
  let n := header.n
  match eig? with
  | none =>
      require (x.size == n) "operator vector has wrong dimension"
  | some eig =>
      require (x.size == n + 1) "border operator vector has wrong dimension"
      require (eig.n == n) "border eigenvector dimension does not match matrix"
      require (eig.pivot < n) "border eigenvector pivot out of range"
  let mut y := Array.emptyWithCapacity (n + if eig?.isSome then 1 else 0)
  for row in [0:n] do
    let start := matrixRowStart matrixBytes header row
    let stop := matrixRowStop matrixBytes header row
    let mut ar := 0
    let mut ai := 0
    for entry in [start:stop] do
      let col := matrixColumnAt matrixBytes header entry
      let value := matrixValueAt matrixBytes header entry
      let term := ExtElt.scale value x[col]!
      ar := ar + term.a.toNat
      ai := ai + term.b.toNat
    match eig? with
    | none => pure ()
    | some eig =>
        let borderValue := eigenValueAt eig row
        let borderTerm := ExtElt.scale borderValue x[n]!
        ar := ar + borderTerm.a.toNat
        ai := ai + borderTerm.b.toNat
    let shifted : ExtElt := {
      a := u8Mod101 (ar + 101 - (50 * x[row]!.a.toNat) % 101),
      b := u8Mod101 (ai + 101 - (50 * x[row]!.b.toNat) % 101)
    }
    y := y.push shifted
  match eig? with
  | none => pure y
  | some eig => pure (y.push x[eig.pivot]!)

def mulArrays (a b : Array ExtElt) : Array ExtElt :=
  Id.run do
    let n := Nat.min a.size b.size
    let mut out := Array.emptyWithCapacity n
    for i in [0:n] do
      out := out.push (a[i]!.mul b[i]!)
    pure out

def mulByteVectors (a b : ByteArray) (n : Nat) : ParseM ByteArray := do
  require (a.size == 2 * n) "left byte vector has wrong dimension"
  require (b.size == 2 * n) "right byte vector has wrong dimension"
  let mut out := ByteArray.emptyWithCapacity (2 * n)
  for i in [0:n] do
    out := pushExtByteArray out ((pairAt a i).mul (pairAt b i))
  pure out

def matrixApplyShiftedBytes (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig? : Option EigenvectorFile) (x : ByteArray) : ParseM ByteArray := do
  let n := header.n
  let order := n + if eig?.isSome then 1 else 0
  require (x.size == 2 * order) "byte operator vector has wrong dimension"
  match eig? with
  | none => pure ()
  | some eig =>
      require (eig.n == n) "border eigenvector dimension does not match matrix"
      require (eig.pivot < n) "border eigenvector pivot out of range"
  let mut y := ByteArray.emptyWithCapacity (2 * order)
  for row in [0:n] do
    let start := matrixRowStart matrixBytes header row
    let stop := matrixRowStop matrixBytes header row
    let mut ar := 0
    let mut ai := 0
    for entry in [start:stop] do
      let col := matrixColumnAt matrixBytes header entry
      let j := 2 * col
      let value := matrixValueAt matrixBytes header entry
      ar := ar + value * x[j]!.toNat
      ai := ai + value * x[j + 1]!.toNat
    match eig? with
    | none => pure ()
    | some eig =>
        let borderValue := eigenValueAt eig row
        ar := ar + borderValue * x[2 * n]!.toNat
        ai := ai + borderValue * x[2 * n + 1]!.toNat
    let rowPair := 2 * row
    y := y.push (u8Mod101 (ar + 101 - (50 * x[rowPair]!.toNat) % 101))
    y := y.push (u8Mod101 (ai + 101 - (50 * x[rowPair + 1]!.toNat) % 101))
  match eig? with
  | none => pure y
  | some eig =>
      let pivotPair := 2 * eig.pivot
      pure ((y.push x[pivotPair]!).push x[pivotPair + 1]!)

def krylovStepBytes (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig? : Option EigenvectorFile) (dR dL x : ByteArray) (order : Nat) :
    ParseM ByteArray := do
  let dx ← mulByteVectors dR x order
  let y ← matrixApplyShiftedBytes matrixBytes header eig? dx
  mulByteVectors dL y order

def krylovStep (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig? : Option EigenvectorFile) (dR dL x : Array ExtElt) :
    ParseM (Array ExtElt) := do
  let dx := mulArrays dR x
  let y ← matrixApplyShifted matrixBytes header eig? dx
  pure (mulArrays dL y)

def RankCertificateFile.krylovPrefixBad (cert : RankCertificateFile)
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig? : Option EigenvectorFile) (count : Nat) : ParseM Nat := do
  let expectedOrder := header.n + if eig?.isSome then 1 else 0
  require (cert.n == expectedOrder) "certificate order does not match operator dimension"
  let seedData := rankSeedData cert.n cert.seed
  let mut x := seedData.x
  let mut bad := 0
  let limit := Nat.min count cert.terms
  for k in [0:limit] do
    let actual := extDot seedData.u x cert.n
    let expected := pairAt cert.moments k
    if actual != expected then
      bad := bad + 1
    if k + 1 < limit then
      x ← krylovStep matrixBytes header eig? seedData.dR seedData.dL x
  pure bad

def RankCertificateFile.krylovPrefixBadFast (cert : RankCertificateFile)
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig? : Option EigenvectorFile) (count : Nat) : ParseM Nat := do
  let expectedOrder := header.n + if eig?.isSome then 1 else 0
  require (cert.n == expectedOrder) "certificate order does not match operator dimension"
  let seedData := rankSeedByteData cert.n cert.seed
  let mut x := seedData.x
  let mut bad := 0
  let limit := Nat.min count cert.terms
  for k in [0:limit] do
    let actual := extDotBytes seedData.u x cert.n
    let expected := pairAt cert.moments k
    if actual != expected then
      bad := bad + 1
    if k + 1 < limit then
      x ← krylovStepBytes matrixBytes header eig? seedData.dR seedData.dL x cert.n
  pure bad

/-- Checks a range of stored moments against the stored connection polynomial. -/
def RankCertificateFile.recurrenceBadInRange (cert : RankCertificateFile)
    (start stop : Nat) : Nat :=
  Id.run do
    let mut bad := 0
    for n in [start:stop] do
      let mut acc := pairAt cert.moments n
      for i in [1:cert.degree + 1] do
        acc := acc.add ((pairAt cert.coefficients i).mul (pairAt cert.moments (n - i)))
      if !acc.isZero then
        bad := bad + 1
    pure bad

def RankCertificateFile.initialRecurrenceBad (cert : RankCertificateFile) : Nat :=
  cert.recurrenceBadInRange cert.degree (Nat.min cert.terms (cert.degree + 32))

/--
Checks the 32 certificate moments that lie beyond the `2N` BM input.

The upstream verifier recomputes all moments and reruns Berlekamp--Massey. This
check is cheaper but still uses actual certificate contents: every extra stored
moment must satisfy the stored full-degree connection polynomial.
-/
def RankCertificateFile.extraRecurrenceBad (cert : RankCertificateFile) : Nat :=
  cert.recurrenceBadInRange cert.bmTerms cert.terms

def RankCertificateFile.connectionLeadingCoefficient (cert : RankCertificateFile) :
    ExtElt :=
  pairAt cert.coefficients 0

/-- The BM array is stored in descending recurrence order, so entry `degree`
is the polynomial's constant coefficient.  This is the coefficient whose
nonvanishing certifies nonsingularity. -/
def RankCertificateFile.connectionConstantCoefficient (cert : RankCertificateFile) :
    ExtElt :=
  pairAt cert.coefficients cert.degree

def fnv64Bytes (bytes : ByteArray) : UInt64 :=
  let offsetBasis : UInt64 := 1469598103934665603
  let prime : UInt64 := 1099511628211
  Id.run do
    let mut h := offsetBasis
    for b in bytes do
      h := (h ^^^ UInt64.ofNat b.toNat) * prime
    pure h

end KnuthFasc8aEx210
