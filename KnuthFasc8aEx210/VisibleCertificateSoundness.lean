import KnuthFasc8aEx210.TransferDenominator

/-!
# Soundness interface for the closed visible-factor certificate

This file gives mathematical meanings to the parsed closed CSR matrix,
terminal vector, and polynomial certificate.  Its single bad-count predicate
is deliberately proof-shaped: zero residuals and a nonzero observed
coordinate feed the generic recurrence/Krylov-span theorem directly.
-/

namespace KnuthFasc8aEx210

open Matrix Polynomial

noncomputable section

/-- Matrix over `F₁₀₁` denoted by the parsed CSR operator. -/
def csrMatrixBase (matrixBytes : ByteArray) (header : MatrixHeader) :
    Matrix (Fin header.n) (Fin header.n) F101 :=
  LinearMap.toMatrix' (csrLinearMapBase matrixBytes header)

@[simp] theorem csrMatrixBase_mulVec
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (v : Fin header.n → F101) :
    csrMatrixBase matrixBytes header *ᵥ v =
      csrLinearMapBase matrixBytes header v := by
  rw [← Matrix.toLin'_apply, csrMatrixBase, Matrix.toLin'_toMatrix']

/-- Native-field interpretation of the terminal/startup vector file. -/
def finishVectorBase (finish : FinishVectorFile) (n : ℕ) : Fin n → F101 :=
  fun i ↦ finish.values[i]!.toNat

/-- Native-field polynomial represented by the visible polynomial file. -/
def polynomialFileBase (poly : PolynomialFile) : ModPolynomial :=
  ∑ i ∈ Finset.range poly.length,
    monomial i (poly.coefficients[i]!.toNat : F101)

/-- Coordinate observation vector; dotting with it selects `bare`. -/
def coordinateObservation {n : ℕ} (bare : Fin n) : Fin n → F101 :=
  Pi.single bare 1

@[simp] theorem dotProduct_coordinateObservation
    {n : ℕ} (bare : Fin n) (v : Fin n → F101) :
    dotProduct (coordinateObservation bare) v = v bare := by
  classical
  simp [coordinateObservation, dotProduct, Pi.single_apply]

/-- The exact `r = g(M²) beta` vector denoted by the visible certificate. -/
def visibleCertificateR (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile) :
    Fin header.n → F101 :=
  evenPolynomialKrylovVector (csrMatrixBase matrixBytes header)
    (finishVectorBase finish header.n) (polynomialFileBase poly)

/-- The derived `50`-eigenvector candidate `r + 99 M r`. -/
def visibleCertificateV (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile) :
    Fin header.n → F101 :=
  let M := csrMatrixBase matrixBytes header
  let r := visibleCertificateR matrixBytes header poly finish
  r + (99 : F101) • (M *ᵥ r)

/-- Number of mathematically nonzero rows in the checked `M²r-76r`
residual. -/
def visibleSquareResidualBad (matrixBytes : ByteArray)
    (header : MatrixHeader) (poly : PolynomialFile)
    (finish : FinishVectorFile) : ℕ :=
  let M := csrMatrixBase matrixBytes header
  let r := visibleCertificateR matrixBytes header poly finish
  (Finset.univ.filter fun i ↦ (M ^ 2 *ᵥ r) i ≠ (76 : F101) * r i).card

/-- One precisely when the certificate's observed coordinate is zero. -/
def visibleCoordinateZeroBad (matrixBytes : ByteArray)
    (header : MatrixHeader) (poly : PolynomialFile)
    (finish : FinishVectorFile) (bare : Fin header.n) : ℕ :=
  if visibleCertificateV matrixBytes header poly finish bare = 0 then 1 else 0

/-- Mathematical vector denoted by one stored Horner checkpoint. -/
def hornerCheckpointBase (checkpoints : HornerCheckpointFile)
    (checkpoint n : Nat) : Fin n → F101 :=
  fun i ↦ hornerCheckpointValueAt checkpoints checkpoint i

/-- One mathematical Horner update for `g(M²) beta`, numbered from the
highest-degree coefficient downward. -/
def visibleHornerStep {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n F101) (beta : n → F101)
    (poly : PolynomialFile) (step : Nat) (v : n → F101) : n → F101 :=
  M ^ 2 *ᵥ v +
    (poly.coefficients[poly.length - 1 - step]!.toNat : F101) • beta

/-- A bounded consecutive segment of the mathematical Horner evaluation. -/
def visibleHornerSegment {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n F101) (beta : n → F101)
    (poly : PolynomialFile) (first : Nat) : Nat → (n → F101) → (n → F101)
  | 0, v => v
  | steps + 1, v =>
      visibleHornerStep M beta poly (first + steps)
        (visibleHornerSegment M beta poly first steps v)

/-- Coordinate mismatch count between two mathematical vectors. -/
def vectorMismatchBad {n : Nat} (v w : Fin n → F101) : Nat :=
  (Finset.univ.filter fun i ↦ v i ≠ w i).card

theorem vectorMismatchBad_eq_zero_iff {n : Nat} (v w : Fin n → F101) :
    vectorMismatchBad v w = 0 ↔ v = w := by
  classical
  unfold vectorMismatchBad
  rw [Finset.card_eq_zero]
  constructor
  · intro empty
    funext i
    by_contra unequal
    have mem : i ∈ Finset.univ.filter fun j ↦ v j ≠ w j := by
      simp [unequal]
    rw [empty] at mem
    simp at mem
  · rintro rfl
    simp

/-- Proof-shaped mismatch counter for one bounded Horner segment. -/
def visibleHornerSegmentBad (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (checkpoints : HornerCheckpointFile) (segment : Nat) : Nat :=
  let first := segment * checkpoints.chunk
  let steps := Nat.min checkpoints.chunk (checkpoints.steps - first)
  vectorMismatchBad
    (visibleHornerSegment (csrMatrixBase matrixBytes header)
      (finishVectorBase finish header.n) poly first steps
      (hornerCheckpointBase checkpoints segment header.n))
    (hornerCheckpointBase checkpoints (segment + 1) header.n)

/-- The first checkpoint must be the zero vector used to start Horner. -/
def visibleHornerInitialBad (checkpoints : HornerCheckpointFile) : Nat :=
  vectorMismatchBad (hornerCheckpointBase checkpoints 0 checkpoints.n) 0

/-- The final checkpoint must satisfy the square-eigenvector relation and
produce a visible derived `50`-eigenvector. -/
def visibleCheckpointFinalBad (matrixBytes : ByteArray) (header : MatrixHeader)
    (checkpoints : HornerCheckpointFile) (final : Nat)
    (bare : Fin header.n) : Nat :=
  let M := csrMatrixBase matrixBytes header
  let r : Fin header.n → F101 := fun i ↦
    hornerCheckpointValueAt checkpoints final i
  vectorMismatchBad (M ^ 2 *ᵥ r) ((76 : F101) • r) +
    if (r + (99 : F101) • (M *ᵥ r)) bare = 0 then 1 else 0

/-- Proof-shaped aggregate for the closed visibility certificate. -/
private structure NativeCSR where
  rowPointers : Array UInt64
  columns : Array UInt32
  values : ByteArray

private unsafe def decodeNativeCSR (matrixBytes : ByteArray)
    (header : MatrixHeader) : NativeCSR := Id.run do
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

private unsafe def nativeCSRApply (matrix : NativeCSR)
    (x : ByteArray) : ByteArray := Id.run do
  let mut y := ByteArray.emptyWithCapacity (matrix.rowPointers.size - 1)
  let mut row : USize := 0
  let rowCount := matrix.rowPointers.usize - 1
  while row < rowCount do
    let mut entry := (matrix.rowPointers.uget row lcProof).toUSize
    let stop := (matrix.rowPointers.uget (row + 1) lcProof).toUSize
    let mut sum : UInt64 := 0
    while entry < stop do
      let column := (matrix.columns.uget entry lcProof).toUSize
      sum := sum + (matrix.values.uget entry lcProof).toUInt64 *
        (x.uget column lcProof).toUInt64
      entry := entry + 1
    y := y.push (UInt8.ofNat (sum % 101).toNat)
    row := row + 1
  pure y

private unsafe def nativeCSRApplyTwice (matrix : NativeCSR)
    (x : ByteArray) : ByteArray :=
  nativeCSRApply matrix (nativeCSRApply matrix x)

private unsafe def nativeZeroByteVector (n : Nat) : ByteArray := Id.run do
  let mut output := ByteArray.emptyWithCapacity n
  let mut i : USize := 0
  let stop := USize.ofNat n
  while i < stop do
    output := output.push 0
    i := i + 1
  pure output

private unsafe def nativeAddScaledByteVector (v : ByteArray) (c : UInt8)
    (b : ByteArray) : ByteArray := Id.run do
  let mut output := ByteArray.emptyWithCapacity v.size
  let mut i : USize := 0
  while i < v.usize do
    let value := (v.uget i lcProof).toUInt64 + c.toUInt64 *
      (b.uget i lcProof).toUInt64
    output := output.push (UInt8.ofNat (value % 101).toNat)
    i := i + 1
  pure output

private unsafe def nativeScaledVectorMismatchCount (lhs : ByteArray)
    (scalar : UInt64) (rhs : ByteArray) : Nat := Id.run do
  let mut bad : UInt64 := 0
  let mut i : USize := 0
  while i < lhs.usize do
    if lhs.uget i lcProof !=
        UInt8.ofNat ((scalar * (rhs.uget i lcProof).toUInt64) % 101).toNat then
      bad := bad + 1
    i := i + 1
  pure bad.toNat

private unsafe def nativeVectorMismatchCount (lhs rhs : ByteArray) : Nat :=
  Id.run do
    let mut bad : UInt64 := 0
    let mut i : USize := 0
    while i < lhs.usize do
      if lhs.uget i lcProof != rhs.uget i lcProof then
        bad := bad + 1
      i := i + 1
    pure bad.toNat

private unsafe def nativeCheckpointVector (checkpoints : HornerCheckpointFile)
    (checkpoint : Nat) : ByteArray :=
  checkpoints.values.extract (checkpoint * checkpoints.n)
    ((checkpoint + 1) * checkpoints.n)

private unsafe def visibleHornerSegmentBadFast (matrixBytes : ByteArray)
    (header : MatrixHeader) (poly : PolynomialFile)
    (finish : FinishVectorFile) (checkpoints : HornerCheckpointFile)
    (segment : Nat) : Nat :=
  let result : ParseM Nat := do
    require (finish.n == header.n) "finish vector dimension does not match matrix"
    require (checkpoints.n == header.n) "checkpoint dimension does not match matrix"
    require (checkpoints.steps == poly.length) "checkpoint steps do not match polynomial"
    require (0 < checkpoints.chunk) "zero checkpoint chunk"
    require (segment + 1 < checkpoints.count) "checkpoint segment out of range"
    let matrix := decodeNativeCSR matrixBytes header
    let first := segment * checkpoints.chunk
    let steps := Nat.min checkpoints.chunk (checkpoints.steps - first)
    let mut v := nativeCheckpointVector checkpoints segment
    for offset in [0 : steps] do
      v := nativeCSRApplyTwice matrix v
      let coefficient := poly.coefficients[poly.length - 1 - first - offset]!
      if coefficient != 0 then
        v := nativeAddScaledByteVector v coefficient finish.values
    pure (nativeVectorMismatchCount v
      (nativeCheckpointVector checkpoints (segment + 1)))
  match result with
  | .ok bad => bad
  | .error _ => 1

@[implemented_by visibleHornerSegmentBadFast]
def checkedVisibleHornerSegmentBad (matrixBytes : ByteArray)
    (header : MatrixHeader) (poly : PolynomialFile)
    (finish : FinishVectorFile) (checkpoints : HornerCheckpointFile)
    (segment : Nat) : Nat :=
  visibleHornerSegmentBad matrixBytes header poly finish checkpoints segment

private unsafe def visibleHornerInitialBadFast
    (checkpoints : HornerCheckpointFile) : Nat := Id.run do
  let first := nativeCheckpointVector checkpoints 0
  let mut bad : UInt64 := 0
  let mut i : USize := 0
  while i < first.usize do
    if first.uget i lcProof != 0 then
      bad := bad + 1
    i := i + 1
  pure bad.toNat

@[implemented_by visibleHornerInitialBadFast]
def checkedVisibleHornerInitialBad (checkpoints : HornerCheckpointFile) : Nat :=
  visibleHornerInitialBad checkpoints

private unsafe def visibleCheckpointFinalBadFast (matrixBytes : ByteArray)
    (header : MatrixHeader) (checkpoints : HornerCheckpointFile)
    (final : Nat) (bare : Fin header.n) : Nat :=
  if checkpoints.n != header.n || checkpoints.count ≤ final then 1
  else
    let matrix := decodeNativeCSR matrixBytes header
    let r := nativeCheckpointVector checkpoints final
    let square := nativeCSRApplyTwice matrix r
    let squareBad := nativeScaledVectorMismatchCount square 76 r
    let mr := nativeCSRApply matrix r
    let v := nativeAddScaledByteVector r 99 mr
    squareBad + if v[bare.val]! = 0 then 1 else 0

@[implemented_by visibleCheckpointFinalBadFast]
def checkedVisibleCheckpointFinalBad (matrixBytes : ByteArray)
    (header : MatrixHeader) (checkpoints : HornerCheckpointFile)
    (final : Nat) (bare : Fin header.n) : Nat :=
  visibleCheckpointFinalBad matrixBytes header checkpoints final bare

theorem checkedVisibleHornerSegmentBad_eq_zero_iff
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (checkpoints : HornerCheckpointFile) (segment : Nat) :
    checkedVisibleHornerSegmentBad matrixBytes header poly finish
        checkpoints segment = 0 ↔
      let first := segment * checkpoints.chunk
      let steps := Nat.min checkpoints.chunk (checkpoints.steps - first)
      visibleHornerSegment (csrMatrixBase matrixBytes header)
          (finishVectorBase finish header.n) poly first steps
          (hornerCheckpointBase checkpoints segment header.n) =
        hornerCheckpointBase checkpoints (segment + 1) header.n := by
  rw [checkedVisibleHornerSegmentBad, visibleHornerSegmentBad,
    vectorMismatchBad_eq_zero_iff]

theorem checkedVisibleHornerInitialBad_eq_zero_iff
    (checkpoints : HornerCheckpointFile) :
    checkedVisibleHornerInitialBad checkpoints = 0 ↔
      hornerCheckpointBase checkpoints 0 checkpoints.n = 0 := by
  rw [checkedVisibleHornerInitialBad, visibleHornerInitialBad,
    vectorMismatchBad_eq_zero_iff]

theorem checkedVisibleCheckpointFinalBad_eq_zero_iff
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (checkpoints : HornerCheckpointFile) (final : Nat)
    (bare : Fin header.n) :
    checkedVisibleCheckpointFinalBad matrixBytes header checkpoints final bare = 0 ↔
      (let M := csrMatrixBase matrixBytes header
       let r : Fin header.n → F101 := fun i ↦
         hornerCheckpointValueAt checkpoints final i
       M ^ 2 *ᵥ r = (76 : F101) • r) ∧
      (let M := csrMatrixBase matrixBytes header
       let r : Fin header.n → F101 := fun i ↦
         hornerCheckpointValueAt checkpoints final i
       (r + (99 : F101) • (M *ᵥ r)) bare ≠ 0) := by
  simp [checkedVisibleCheckpointFinalBad, visibleCheckpointFinalBad,
    vectorMismatchBad_eq_zero_iff]

/-- One Horner update preserves membership in the startup Krylov span. -/
theorem visibleHornerStep_mem_krylovSpan
    {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n F101) (beta v : n → F101)
    (poly : PolynomialFile) (step : Nat)
    (v_mem : v ∈ Submodule.span F101
      (Set.range fun j : Nat ↦ M ^ j *ᵥ beta)) :
    visibleHornerStep M beta poly step v ∈ Submodule.span F101
      (Set.range fun j : Nat ↦ M ^ j *ᵥ beta) := by
  apply Submodule.add_mem
  · have once := mulVec_mem_krylovSpan M beta v v_mem
    have twice := mulVec_mem_krylovSpan M beta (M *ᵥ v) once
    simpa [visibleHornerStep, pow_two, mulVec_mulVec] using twice
  · apply Submodule.smul_mem
    simpa using (Submodule.subset_span
      (s := Set.range fun j : Nat ↦ M ^ j *ᵥ beta)
      (Set.mem_range_self 0))

/-- Every bounded Horner segment preserves startup Krylov-span membership. -/
theorem visibleHornerSegment_mem_krylovSpan
    {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n F101) (beta v : n → F101)
    (poly : PolynomialFile) (first steps : Nat)
    (v_mem : v ∈ Submodule.span F101
      (Set.range fun j : Nat ↦ M ^ j *ᵥ beta)) :
    visibleHornerSegment M beta poly first steps v ∈ Submodule.span F101
      (Set.range fun j : Nat ↦ M ^ j *ᵥ beta) := by
  induction steps with
  | zero => exact v_mem
  | succ steps ih =>
      exact visibleHornerStep_mem_krylovSpan M beta _ poly (first + steps) ih

/-- A checked final checkpoint in the startup Krylov span proves the visible
factor in the actual normalized reduced scalar transfer denominator. -/
theorem visibleFactor_dvd_normalizedTransferDenominator_of_checkpoint
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (finish : FinishVectorFile) (checkpoints : HornerCheckpointFile)
    (final : Nat) (bare : Fin header.n)
    (r_mem : (fun i : Fin header.n ↦
        (hornerCheckpointValueAt checkpoints final i : F101)) ∈
      Submodule.span F101 (Set.range fun j : Nat ↦
        csrMatrixBase matrixBytes header ^ j *ᵥ
          finishVectorBase finish header.n))
    (no_bad : checkedVisibleCheckpointFinalBad matrixBytes header checkpoints
      final bare = 0) :
    visibleFactor ∣
      normalizedTransferDenominator (csrMatrixBase matrixBytes header)
        (finishVectorBase finish header.n) (coordinateObservation bare) := by
  have facts := (checkedVisibleCheckpointFinalBad_eq_zero_iff
    matrixBytes header checkpoints final bare).mp no_bad
  let M := csrMatrixBase matrixBytes header
  let beta := finishVectorBase finish header.n
  let observe := coordinateObservation bare
  let r : Fin header.n → F101 := fun i ↦
    hornerCheckpointValueAt checkpoints final i
  let v := r + (99 : F101) • (M *ᵥ r)
  have v_mem : v ∈ Submodule.span F101
      (Set.range fun j : Nat ↦ M ^ j *ᵥ beta) := by
    apply Submodule.add_mem
    · exact r_mem
    · exact Submodule.smul_mem _ _
        (mulVec_mem_krylovSpan M beta r r_mem)
  have v_eigenvector : M *ᵥ v = (50 : F101) • v :=
    derived_fifty_eigenvector_of_square_seventySix M r facts.1
  have v_visible : dotProduct observe v ≠ 0 := by
    simpa [observe, v, r, M] using facts.2
  have transfer_factor : visibleFactor ∣ transferDenominator M beta observe := by
    apply visibleFactor_dvd_of_eventual_reverse_recurrence_of_mem_krylovSpan
      M observe beta v (transferDenominator M beta observe)
    · exact transferDenominator_reverse_isEventuallyForwardRecurrence M beta observe
    · exact v_mem
    · exact v_eigenvector
    · exact v_visible
  apply (normalizedTransferDenominator_associated M beta observe).dvd_iff_dvd_right.mpr
  exact transfer_factor

private unsafe def visibleCertificateBadFast (matrixBytes : ByteArray)
    (header : MatrixHeader) (poly : PolynomialFile)
    (finish : FinishVectorFile) (bare : Fin header.n) : ℕ :=
  let result : ParseM ℕ := do
    require (finish.n == header.n) "finish vector dimension does not match matrix"
    let matrix := decodeNativeCSR matrixBytes header
    let beta := finish.values
    let mut r := nativeZeroByteVector header.n
    for s in [0 : poly.length] do
      r := nativeCSRApplyTwice matrix r
      let coeff := poly.coefficients[poly.length - 1 - s]!
      if coeff != 0 then
        r := nativeAddScaledByteVector r coeff beta
    let square := nativeCSRApplyTwice matrix r
    let squareBad := nativeScaledVectorMismatchCount square 76 r
    let mr := nativeCSRApply matrix r
    let v := nativeAddScaledByteVector r 99 mr
    let coordinateBad := if v[bare.val]! = 0 then 1 else 0
    pure (squareBad + coordinateBad)
  match result with
  | .ok bad => bad
  | .error _ => 1

@[implemented_by visibleCertificateBadFast]
def visibleCertificateBad (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n) : ℕ :=
  visibleSquareResidualBad matrixBytes header poly finish +
    visibleCoordinateZeroBad matrixBytes header poly finish bare

theorem visibleSquareResidualBad_eq_zero_iff
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile) :
    visibleSquareResidualBad matrixBytes header poly finish = 0 ↔
      let M := csrMatrixBase matrixBytes header
      let r := visibleCertificateR matrixBytes header poly finish
      M ^ 2 *ᵥ r = (76 : F101) • r := by
  unfold visibleSquareResidualBad
  rw [Finset.card_eq_zero]
  constructor
  · intro empty
    funext i
    have coordinate : (csrMatrixBase matrixBytes header ^ 2 *ᵥ
        visibleCertificateR matrixBytes header poly finish) i =
        (76 : F101) *
          visibleCertificateR matrixBytes header poly finish i := by
      by_contra unequal
      have mem : i ∈ Finset.univ.filter fun j ↦
          (csrMatrixBase matrixBytes header ^ 2 *ᵥ
            visibleCertificateR matrixBytes header poly finish) j ≠
              (76 : F101) *
                visibleCertificateR matrixBytes header poly finish j := by
        simp [unequal]
      rw [empty] at mem
      simp at mem
    simpa using coordinate
  · intro vector_eq
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ unequal
    apply unequal
    have coordinate := congrFun vector_eq i
    simpa using coordinate

theorem visibleCoordinateZeroBad_eq_zero_iff
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n) :
    visibleCoordinateZeroBad matrixBytes header poly finish bare = 0 ↔
      visibleCertificateV matrixBytes header poly finish bare ≠ 0 := by
  simp [visibleCoordinateZeroBad]

/-- Zero mathematical bad count gives exactly the square-eigenvector and
visibility facts consumed by the closed denominator theorem. -/
theorem visibleCertificateBad_eq_zero_iff
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n) :
    visibleCertificateBad matrixBytes header poly finish bare = 0 ↔
      (let M := csrMatrixBase matrixBytes header
       let r := visibleCertificateR matrixBytes header poly finish
       M ^ 2 *ᵥ r = (76 : F101) • r) ∧
      visibleCertificateV matrixBytes header poly finish bare ≠ 0 := by
  rw [visibleCertificateBad, Nat.add_eq_zero_iff,
    visibleSquareResidualBad_eq_zero_iff,
    visibleCoordinateZeroBad_eq_zero_iff]

/-- End-to-end mathematical consequence of a zero closed visible-certificate
counter, leaving only the denominator-recurrence premise to its rational
generating-function bridge. -/
theorem visibleFactor_dvd_of_visibleCertificateBad_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n) (q : ModPolynomial)
    (recurrence : IsEventuallyForwardRecurrence (csrMatrixBase matrixBytes header)
      (coordinateObservation bare) (finishVectorBase finish header.n)
      q.reverse)
    (no_bad : visibleCertificateBad matrixBytes header poly finish bare = 0) :
    visibleFactor ∣ q := by
  have facts := (visibleCertificateBad_eq_zero_iff
    matrixBytes header poly finish bare).mp no_bad
  apply visibleFactor_dvd_of_visibleCandidate_eventual_recurrence
    (csrMatrixBase matrixBytes header) (coordinateObservation bare)
    (finishVectorBase finish header.n) (polynomialFileBase poly) q recurrence
  · exact facts.1
  · simpa [visibleCertificateV, visibleCertificateR] using facts.2

/-- A passing closed certificate proves visibility in the actual canonical
reduced scalar transfer denominator; no recurrence premise remains. -/
theorem visibleFactor_dvd_transferDenominator_of_visibleCertificateBad_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n)
    (no_bad : visibleCertificateBad matrixBytes header poly finish bare = 0) :
    visibleFactor ∣ transferDenominator (csrMatrixBase matrixBytes header)
      (finishVectorBase finish header.n) (coordinateObservation bare) := by
  apply visibleFactor_dvd_of_visibleCertificateBad_eq_zero
    matrixBytes header poly finish bare _
  · exact transferDenominator_reverse_isEventuallyForwardRecurrence
      (csrMatrixBase matrixBytes header)
      (finishVectorBase finish header.n) (coordinateObservation bare)
  · exact no_bad

/-- Constant-term-one normalization preserves the certificate's visible
factor. -/
theorem visibleFactor_dvd_normalizedTransferDenominator_of_visibleCertificateBad_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n)
    (no_bad : visibleCertificateBad matrixBytes header poly finish bare = 0) :
    visibleFactor ∣
      normalizedTransferDenominator (csrMatrixBase matrixBytes header)
        (finishVectorBase finish header.n) (coordinateObservation bare) := by
  apply (normalizedTransferDenominator_associated
    (csrMatrixBase matrixBytes header)
    (finishVectorBase finish header.n)
    (coordinateObservation bare)).dvd_iff_dvd_right.mpr
  exact visibleFactor_dvd_transferDenominator_of_visibleCertificateBad_eq_zero
    matrixBytes header poly finish bare no_bad

end

end KnuthFasc8aEx210
