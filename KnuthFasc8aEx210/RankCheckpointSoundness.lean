import KnuthFasc8aEx210.CertificateMatrixSoundness

/-!
# Bounded rank-certificate checkpoint replay

The full rank certificates contain tens of thousands of sparse Krylov steps.
This module splits that replay at checked vector checkpoints.  Each bounded
counter verifies every stored scalar moment in its interval and also verifies
the exact transition to the next checkpoint.  The logical definitions remain
explicit finite mismatch counts; native implementations use compact CSR and
byte-vector loops.
-/

namespace KnuthFasc8aEx210

noncomputable section

/-- Stored-moment mismatches along one explicit byte orbit interval. -/
def rankMomentSegmentBad (cert : RankCertificateFile) (probe : ByteArray)
    (orbit : Nat → ByteArray) (order first steps : Nat) : Nat :=
  ((List.range steps).filter fun offset =>
    pairAt cert.moments (first + offset) !=
      extDotBytes probe (orbit offset) order).length

/-- One precisely when two byte vectors differ. -/
def byteVectorMismatchBad (v w : ByteArray) : Nat :=
  if v = w then 0 else 1

theorem byteVectorMismatchBad_eq_zero_iff (v w : ByteArray) :
    byteVectorMismatchBad v w = 0 ↔ v = w := by
  simp [byteVectorMismatchBad]

theorem rankMomentSegmentBad_eq_zero_iff
    (cert : RankCertificateFile) (probe : ByteArray)
    (orbit : Nat → ByteArray) (order first steps : Nat) :
    rankMomentSegmentBad cert probe orbit order first steps = 0 ↔
      ∀ offset < steps, pairAt cert.moments (first + offset) =
        extDotBytes probe (orbit offset) order := by
  constructor
  · intro no_bad offset offset_lt
    by_contra mismatch
    have offset_mem : offset ∈ List.range steps := by simpa using offset_lt
    have bad_mem : offset ∈ (List.range steps).filter (fun i =>
        pairAt cert.moments (first + i) !=
          extDotBytes probe (orbit i) order) := by
      simp [offset_mem, mismatch]
    have bad_pos : 0 < rankMomentSegmentBad cert probe orbit order first steps := by
      rw [rankMomentSegmentBad]
      exact List.length_pos_of_ne_nil (List.ne_nil_of_mem bad_mem)
    omega
  · intro hmatches
    rw [rankMomentSegmentBad, List.length_eq_zero_iff]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro offset bad_mem
    simp only [List.mem_filter, List.mem_range] at bad_mem
    have equal := hmatches offset bad_mem.1
    simp [equal] at bad_mem

/-- Proof-shaped counter for one normal-certificate checkpoint segment. -/
def normalRankCheckpointSegmentBad (cert : RankCertificateFile)
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (seedData : KrylovSeedByteData) (checkpoints : RankCheckpointFile)
    (segment : Nat) : Nat :=
  let first := segment * checkpoints.chunk
  let steps := Nat.min checkpoints.chunk (checkpoints.steps - first)
  let initial := rankCheckpointVector checkpoints segment
  let orbit := normalKrylovOrbitBytes matrixBytes header seedData.dR seedData.dL
    initial
  rankMomentSegmentBad cert seedData.u orbit header.n first steps +
    byteVectorMismatchBad (orbit steps)
      (rankCheckpointVector checkpoints (segment + 1))

/-- Proof-shaped counter for one bordered-certificate checkpoint segment. -/
def borderRankCheckpointSegmentBad (cert : RankCertificateFile)
    (matrixBytes : ByteArray) (header : MatrixHeader) (eig : EigenvectorFile)
    (seedData : KrylovSeedByteData) (checkpoints : RankCheckpointFile)
    (segment : Nat) : Nat :=
  let first := segment * checkpoints.chunk
  let steps := Nat.min checkpoints.chunk (checkpoints.steps - first)
  let initial := rankCheckpointVector checkpoints segment
  let orbit := borderKrylovOrbitBytes matrixBytes header eig seedData.dR seedData.dL
    initial
  rankMomentSegmentBad cert seedData.u orbit (header.n + 1) first steps +
    byteVectorMismatchBad (orbit steps)
      (rankCheckpointVector checkpoints (segment + 1))

private structure RankNativeCSR where
  rowPointers : Array UInt64
  columns : Array UInt32
  values : ByteArray

private unsafe def decodeRankNativeCSR (matrixBytes : ByteArray)
    (header : MatrixHeader) : RankNativeCSR := Id.run do
  let mut rowPointers := Array.emptyWithCapacity (header.n + 1)
  for row in [0 : header.n + 1] do
    rowPointers := rowPointers.push (UInt64.ofNat <|
      matrixRowStart matrixBytes header row)
  let mut columns := Array.emptyWithCapacity header.entries
  for entry in [0 : header.entries] do
    columns := columns.push (UInt32.ofNat <| u32LEAt matrixBytes
      (header.colIndexOffset + 4 * entry))
  let values := matrixBytes.extract header.valueOffset
    (header.valueOffset + header.entries)
  pure { rowPointers, columns, values }

private unsafe def nativeExtMulAt (left right : ByteArray) (coordinate : USize) :
    UInt8 × UInt8 :=
  let byte := 2 * coordinate
  let ar := (left.uget byte lcProof).toUInt64
  let ai := (left.uget (byte + 1) lcProof).toUInt64
  let br := (right.uget byte lcProof).toUInt64
  let bi := (right.uget (byte + 1) lcProof).toUInt64
  (UInt8.ofNat ((ar * br + 2 * ai * bi) % 101).toNat,
    UInt8.ofNat ((ar * bi + ai * br) % 101).toNat)

private unsafe def nativePointwiseExtMul (left right : ByteArray)
    (order : Nat) : ByteArray := Id.run do
  let mut output := ByteArray.emptyWithCapacity (2 * order)
  let mut i : USize := 0
  let stop := USize.ofNat order
  while i < stop do
    let value := nativeExtMulAt left right i
    output := (output.push value.1).push value.2
    i := i + 1
  pure output

private unsafe def nativeRankApply (matrix : RankNativeCSR) (x : ByteArray)
    (eig? : Option EigenvectorFile) : ByteArray := Id.run do
  let rowCount := matrix.rowPointers.size - 1
  let order := rowCount + if eig?.isSome then 1 else 0
  let mut output := ByteArray.emptyWithCapacity (2 * order)
  let mut row : USize := 0
  let stopRow := USize.ofNat rowCount
  while row < stopRow do
    let mut entry := (matrix.rowPointers.uget row lcProof).toUSize
    let stop := (matrix.rowPointers.uget (row + 1) lcProof).toUSize
    let mut real : UInt64 := 0
    let mut imag : UInt64 := 0
    while entry < stop do
      let column := (matrix.columns.uget entry lcProof).toUSize
      let value := (matrix.values.uget entry lcProof).toUInt64
      real := real + value * (x.uget (2 * column) lcProof).toUInt64
      imag := imag + value * (x.uget (2 * column + 1) lcProof).toUInt64
      entry := entry + 1
    let xr := (x.uget (2 * row) lcProof).toUInt64
    let xi := (x.uget (2 * row + 1) lcProof).toUInt64
    let mut outReal := real % 101 + 5050 - 50 * xr
    let mut outImag := imag % 101 + 5050 - 50 * xi
    match eig? with
    | none => pure ()
    | some eig =>
        let scale := (eig.values.uget row lcProof).toUInt64
        let extra := USize.ofNat rowCount
        outReal := outReal + scale * (x.uget (2 * extra) lcProof).toUInt64
        outImag := outImag + scale * (x.uget (2 * extra + 1) lcProof).toUInt64
    output := output.push (UInt8.ofNat (outReal % 101).toNat)
    output := output.push (UInt8.ofNat (outImag % 101).toNat)
    row := row + 1
  match eig? with
  | none => pure output
  | some eig =>
      let pivot := USize.ofNat eig.pivot
      pure ((output.push (x.uget (2 * pivot) lcProof)).push
        (x.uget (2 * pivot + 1) lcProof))

private unsafe def nativeRankStep (matrix : RankNativeCSR)
    (eig? : Option EigenvectorFile) (dR dL x : ByteArray)
    (order : Nat) : ByteArray :=
  let right := nativePointwiseExtMul dR x order
  let applied := nativeRankApply matrix right eig?
  nativePointwiseExtMul dL applied order

private unsafe def nativeRankDot (probe x : ByteArray) (order : Nat) :
    UInt8 × UInt8 := Id.run do
  let mut real : UInt64 := 0
  let mut imag : UInt64 := 0
  let mut i : USize := 0
  let stop := USize.ofNat order
  while i < stop do
    let byte := 2 * i
    let ar := (probe.uget byte lcProof).toUInt64
    let ai := (probe.uget (byte + 1) lcProof).toUInt64
    let br := (x.uget byte lcProof).toUInt64
    let bi := (x.uget (byte + 1) lcProof).toUInt64
    real := real + ar * br + 2 * ai * bi
    imag := imag + ar * bi + ai * br
    i := i + 1
  pure (UInt8.ofNat (real % 101).toNat, UInt8.ofNat (imag % 101).toNat)

private unsafe def nativeByteMismatch (left right : ByteArray) : Nat := Id.run do
  if left.size != right.size then return 1
  let mut bad : UInt64 := 0
  let mut i : USize := 0
  while i < left.usize do
    if left.uget i lcProof != right.uget i lcProof then bad := bad + 1
    i := i + 1
  pure bad.toNat

private unsafe def rankCheckpointSegmentBadFast
    (cert : RankCertificateFile) (matrixBytes : ByteArray)
    (header : MatrixHeader) (eig? : Option EigenvectorFile)
    (seedData : KrylovSeedByteData) (checkpoints : RankCheckpointFile)
    (segment : Nat) : Nat :=
  if checkpoints.order != cert.n || checkpoints.steps != 2 * cert.degree ||
      checkpoints.seed != cert.seed || checkpoints.matrixHash != cert.matrixHash ||
      checkpoints.eigenHash != cert.eigenHash ||
      segment + 1 >= checkpoints.count then 1
  else Id.run do
    let order := header.n + if eig?.isSome then 1 else 0
    if order != cert.n then return 1
    let matrix := decodeRankNativeCSR matrixBytes header
    let first := segment * checkpoints.chunk
    let steps := Nat.min checkpoints.chunk (checkpoints.steps - first)
    let mut x := rankCheckpointVector checkpoints segment
    let mut bad : UInt64 := 0
    for offset in [0 : steps] do
      let actual := nativeRankDot seedData.u x order
      let expected := pairAt cert.moments (first + offset)
      if actual.1 != expected.a || actual.2 != expected.b then bad := bad + 1
      x := nativeRankStep matrix eig? seedData.dR seedData.dL x order
    pure (bad.toNat + nativeByteMismatch x
      (rankCheckpointVector checkpoints (segment + 1)))

private unsafe def normalRankCheckpointSegmentBadFast
    (cert : RankCertificateFile) (matrixBytes : ByteArray)
    (header : MatrixHeader) (seedData : KrylovSeedByteData)
    (checkpoints : RankCheckpointFile) (segment : Nat) : Nat :=
  rankCheckpointSegmentBadFast cert matrixBytes header none seedData checkpoints
    segment

private unsafe def borderRankCheckpointSegmentBadFast
    (cert : RankCertificateFile) (matrixBytes : ByteArray)
    (header : MatrixHeader) (eig : EigenvectorFile)
    (seedData : KrylovSeedByteData) (checkpoints : RankCheckpointFile)
    (segment : Nat) : Nat :=
  rankCheckpointSegmentBadFast cert matrixBytes header (some eig) seedData
    checkpoints segment

@[implemented_by normalRankCheckpointSegmentBadFast]
def checkedNormalRankCheckpointSegmentBad (cert : RankCertificateFile)
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (seedData : KrylovSeedByteData) (checkpoints : RankCheckpointFile)
    (segment : Nat) : Nat :=
  normalRankCheckpointSegmentBad cert matrixBytes header seedData checkpoints segment

@[implemented_by borderRankCheckpointSegmentBadFast]
def checkedBorderRankCheckpointSegmentBad (cert : RankCertificateFile)
    (matrixBytes : ByteArray) (header : MatrixHeader) (eig : EigenvectorFile)
    (seedData : KrylovSeedByteData) (checkpoints : RankCheckpointFile)
    (segment : Nat) : Nat :=
  borderRankCheckpointSegmentBad cert matrixBytes header eig seedData checkpoints
    segment

theorem checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    (cert : RankCertificateFile) (matrixBytes : ByteArray)
    (header : MatrixHeader) (seedData : KrylovSeedByteData)
    (checkpoints : RankCheckpointFile) (segment : Nat) :
    checkedNormalRankCheckpointSegmentBad cert matrixBytes header seedData
        checkpoints segment = 0 ↔
      let first := segment * checkpoints.chunk
      let steps := Nat.min checkpoints.chunk (checkpoints.steps - first)
      let initial := rankCheckpointVector checkpoints segment
      let orbit := normalKrylovOrbitBytes matrixBytes header seedData.dR
        seedData.dL initial
      (∀ offset < steps, pairAt cert.moments (first + offset) =
        extDotBytes seedData.u (orbit offset) header.n) ∧
      orbit steps = rankCheckpointVector checkpoints (segment + 1) := by
  rw [checkedNormalRankCheckpointSegmentBad, normalRankCheckpointSegmentBad,
    Nat.add_eq_zero_iff, rankMomentSegmentBad_eq_zero_iff,
    byteVectorMismatchBad_eq_zero_iff]

theorem checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    (cert : RankCertificateFile) (matrixBytes : ByteArray)
    (header : MatrixHeader) (eig : EigenvectorFile)
    (seedData : KrylovSeedByteData) (checkpoints : RankCheckpointFile)
    (segment : Nat) :
    checkedBorderRankCheckpointSegmentBad cert matrixBytes header eig seedData
        checkpoints segment = 0 ↔
      let first := segment * checkpoints.chunk
      let steps := Nat.min checkpoints.chunk (checkpoints.steps - first)
      let initial := rankCheckpointVector checkpoints segment
      let orbit := borderKrylovOrbitBytes matrixBytes header eig seedData.dR
        seedData.dL initial
      (∀ offset < steps, pairAt cert.moments (first + offset) =
        extDotBytes seedData.u (orbit offset) (header.n + 1)) ∧
      orbit steps = rankCheckpointVector checkpoints (segment + 1) := by
  rw [checkedBorderRankCheckpointSegmentBad, borderRankCheckpointSegmentBad,
    Nat.add_eq_zero_iff, rankMomentSegmentBad_eq_zero_iff,
    byteVectorMismatchBad_eq_zero_iff]

end

end KnuthFasc8aEx210
