import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import KnuthFasc8aEx210.CertificateFieldEncoding
import KnuthFasc8aEx210.CertificatePadeSoundness

/-!
# Soundness of encoded matrix-certificate operations

This file begins the bridge from executable Krylov replay to a mathematical
linear operator over `CertificateField`.
-/

namespace KnuthFasc8aEx210

noncomputable section

/-- Interpret `n` consecutive byte pairs as a vector over the certificate
field. -/
def encodedVector (bytes : ByteArray) (n : ℕ) : Fin n → CertificateField :=
  fun i => (pairAt bytes i).toCertificateField

private theorem extDotByteSums_eq (u x : ByteArray) (n : ℕ) :
    extDotByteSums u x n =
      (∑ i ∈ Finset.range n, (
          (pairAt u i).a.toNat * (pairAt x i).a.toNat +
            2 * (pairAt u i).b.toNat * (pairAt x i).b.toNat),
        ∑ i ∈ Finset.range n, (
          (pairAt u i).a.toNat * (pairAt x i).b.toNat +
            (pairAt u i).b.toNat * (pairAt x i).a.toNat)) := by
  induction n with
  | zero => simp [extDotByteSums]
  | succ n ih =>
      rw [extDotByteSums, ih]
      simp only [Finset.sum_range_succ]
      simp [pairAt, Nat.add_assoc]

private theorem certificatePair_finset_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (real imag : α → ZMod 101) :
    certificatePair (∑ i ∈ s, real i) (∑ i ∈ s, imag i) =
      ∑ i ∈ s, certificatePair (real i) (imag i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s i_not_mem ih =>
      simp only [Finset.sum_insert i_not_mem]
      rw [certificatePair_add, ih]

/-- The byte dot product used for every stored Krylov moment is the ordinary
dot product of the interpreted field vectors. -/
theorem extDotBytes_toCertificateField (u x : ByteArray) (n : ℕ) :
    (extDotBytes u x n).toCertificateField =
      ∑ i : Fin n, encodedVector u n i * encodedVector x n i := by
  rw [ExtElt.toCertificateField]
  simp only [extDotBytes]
  rw [extDotByteSums_eq]
  rw [zmod101_of_u8Mod101, zmod101_of_u8Mod101]
  push_cast
  rw [certificatePair_finset_sum, ← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro i
  rw [encodedVector, encodedVector,
    ExtElt.toCertificateField, ExtElt.toCertificateField,
    certificatePair_mul]

/-- One row of the parsed CSR matrix acting on a field vector.  Malformed
column indices contribute zero; the parser's CSR validation later rules them
out. -/
def csrApplyField (matrixBytes : ByteArray) (header : MatrixHeader)
    (x : Fin header.n → CertificateField) (row : Fin header.n) :
    CertificateField :=
  ∑ offset ∈ Finset.range
      (matrixRowStop matrixBytes header row -
        matrixRowStart matrixBytes header row),
    let entry := matrixRowEntry matrixBytes header row offset
    if h : matrixColumnAt matrixBytes header entry < header.n then
      algebraMap (ZMod 101) CertificateField
          (matrixValueAt matrixBytes header entry) *
        x ⟨matrixColumnAt matrixBytes header entry, h⟩
    else 0

/-- Mathematical linear operator represented by a parsed CSR matrix. -/
def csrLinearMap (matrixBytes : ByteArray) (header : MatrixHeader) :
    Module.End CertificateField (Fin header.n → CertificateField) where
  toFun x := csrApplyField matrixBytes header x
  map_add' x y := by
    funext row
    classical
    simp only [csrApplyField, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro entry entry_mem
    split_ifs <;> simp_all [mul_add]
  map_smul' c x := by
    funext row
    classical
    simp only [csrApplyField, Pi.smul_apply, RingHom.id_apply]
    change _ = c * _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro entry entry_mem
    split_ifs <;> simp_all
    ring

/-- The shifted operator `M - 50 I` used by every rank certificate. -/
def shiftedCSRLinearMap (matrixBytes : ByteArray) (header : MatrixHeader) :
    Module.End CertificateField (Fin header.n → CertificateField) :=
  csrLinearMap matrixBytes header -
    (50 : CertificateField) • LinearMap.id

/-- Pointwise diagonal multiplication by an encoded field vector. -/
def encodedDiagonalLinearMap (diagonal : ByteArray) (n : ℕ) :
    Module.End CertificateField (Fin n → CertificateField) where
  toFun x i := encodedVector diagonal n i * x i
  map_add' x y := by
    funext i
    simp [mul_add]
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

/-- Normal-certificate operator `D_L (M - 50 I) D_R`. -/
def preconditionedCSRLinearMap (matrixBytes : ByteArray) (header : MatrixHeader)
    (dR dL : ByteArray) :
    Module.End CertificateField (Fin header.n → CertificateField) :=
  (encodedDiagonalLinearMap dL header.n).comp
    ((shiftedCSRLinearMap matrixBytes header).comp
      (encodedDiagonalLinearMap dR header.n))

/-- Linear functional represented by the encoded Wiedemann probe vector. -/
def encodedProbeLinearMap (probe : ByteArray) (n : ℕ) :
    (Fin n → CertificateField) →ₗ[CertificateField] CertificateField where
  toFun x := ∑ i, encodedVector probe n i * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    change (∑ i, encodedVector probe n i * (c * x i)) =
      c * ∑ i, encodedVector probe n i * x i
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    ring

theorem extDotBytes_eq_encodedProbe
    (probe x : ByteArray) (n : ℕ) :
    (extDotBytes probe x n).toCertificateField =
      encodedProbeLinearMap probe n (encodedVector x n) := by
  exact extDotBytes_toCertificateField probe x n

private theorem matrixRowByteSums_eq
    (matrixBytes : ByteArray) (header : MatrixHeader) (x : ByteArray)
    (row count : ℕ) :
    matrixRowByteSums matrixBytes header x row count =
      (∑ offset ∈ Finset.range count, (
          matrixRowByteRealTerm matrixBytes header x row offset),
        ∑ offset ∈ Finset.range count, (
          matrixRowByteImagTerm matrixBytes header x row offset)) := by
  induction count with
  | zero => simp [matrixRowByteSums]
  | succ count ih =>
      rw [matrixRowByteSums, ih]
      simp only [Finset.sum_range_succ]

private theorem matrixRowBytes_toCertificateField_sum
    (matrixBytes : ByteArray) (header : MatrixHeader) (x : ByteArray)
    (row : ℕ) :
    (matrixRowBytes matrixBytes header x row).toCertificateField =
      ∑ offset ∈ Finset.range
        (matrixRowStop matrixBytes header row -
          matrixRowStart matrixBytes header row),
        let entry := matrixRowEntry matrixBytes header row offset
        algebraMap (ZMod 101) CertificateField
            (matrixValueAt matrixBytes header entry) *
          (pairAt x (matrixColumnAt matrixBytes header entry)).toCertificateField := by
  rw [ExtElt.toCertificateField]
  simp only [matrixRowBytes]
  rw [matrixRowByteSums_eq, zmod101_of_u8Mod101, zmod101_of_u8Mod101]
  simp only [Nat.cast_sum]
  rw [certificatePair_finset_sum]
  apply Finset.sum_congr rfl
  intro offset offset_mem
  simp only [matrixRowByteRealTerm, matrixRowByteImagTerm]
  change (matrixRowByteTerm matrixBytes header x row offset).toCertificateField = _
  rw [matrixRowByteTerm, ExtElt.toCertificateField_scale]

theorem matrixRowBytes_toCertificateField
    (matrixBytes : ByteArray) (header : MatrixHeader) (x : ByteArray)
    (row : Fin header.n)
    (columns_valid : ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    (matrixRowBytes matrixBytes header x row).toCertificateField =
      csrApplyField matrixBytes header (encodedVector x header.n) row := by
  rw [matrixRowBytes_toCertificateField_sum]
  simp only [csrApplyField]
  apply Finset.sum_congr rfl
  intro offset offset_mem
  have offset_lt : offset <
      matrixRowStop matrixBytes header row -
        matrixRowStart matrixBytes header row := Finset.mem_range.mp offset_mem
  have column_lt := columns_valid offset offset_lt
  have column_lt' : matrixColumnAt matrixBytes header
      (matrixRowEntry matrixBytes header row offset) < header.n := by
    simpa [matrixRowEntry] using column_lt
  rw [dif_pos column_lt', encodedVector]

theorem matrixApplyShiftedNormalRow_toCertificateField
    (matrixBytes : ByteArray) (header : MatrixHeader) (x : ByteArray)
    (row : Fin header.n)
    (columns_valid : ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    (matrixApplyShiftedNormalRow matrixBytes header x row).toCertificateField =
      shiftedCSRLinearMap matrixBytes header (encodedVector x header.n) row := by
  have row_canonical :
      (matrixRowBytes matrixBytes header x row).IsCanonical := by
    simp only [matrixRowBytes, ExtElt.IsCanonical]
    constructor
    · rw [toNat_u8Mod101]
      exact Nat.mod_lt _ (by omega)
    · rw [toNat_u8Mod101]
      exact Nat.mod_lt _ (by omega)
  have shift_canonical : ((pairAt x row).scale 50).IsCanonical :=
    ExtElt.isCanonical_scale 50 (pairAt x row)
  rw [matrixApplyShiftedNormalRow,
    ExtElt.toCertificateField_sub row_canonical shift_canonical,
    matrixRowBytes_toCertificateField matrixBytes header x row columns_valid,
    ExtElt.toCertificateField_scale]
  simp [shiftedCSRLinearMap, encodedVector]
  rfl

@[simp]
theorem pointwiseProductBytes_size (a b : ByteArray) (n : ℕ) :
    (pointwiseProductBytes a b n).size = 2 * n := by
  induction n with
  | zero => simp [pointwiseProductBytes]
  | succ n ih =>
      simp [pointwiseProductBytes, pushExtByteArray, ih]
      omega

private theorem pairAt_pushExtByteArray_lt (bytes : ByteArray) (p : ExtElt)
    {i : ℕ} (second_lt : 2 * i + 1 < bytes.size) :
    pairAt (pushExtByteArray bytes p) i = pairAt bytes i := by
  change ExtElt.mk _ _ = ExtElt.mk _ _
  rw [ExtElt.mk.injEq]
  constructor
  · change ((bytes.push p.a).push p.b)[2 * i]! = bytes[2 * i]!
    rw [ByteArray.getElem!_push_lt _ _ _ (by simp; omega),
      ByteArray.getElem!_push_lt _ _ _ (by omega)]
  · change ((bytes.push p.a).push p.b)[2 * i + 1]! = bytes[2 * i + 1]!
    rw [ByteArray.getElem!_push_lt _ _ _ (by simp; omega),
      ByteArray.getElem!_push_lt _ _ _ second_lt]

private theorem pairAt_pushExtByteArray_last (bytes : ByteArray) (p : ExtElt)
    (n : ℕ) (size_eq : bytes.size = 2 * n) :
    pairAt (pushExtByteArray bytes p) n = p := by
  change ExtElt.mk _ _ = ExtElt.mk _ _
  rw [ExtElt.mk.injEq]
  constructor
  · change ((bytes.push p.a).push p.b)[2 * n]! = p.a
    rw [ByteArray.getElem!_push_lt _ _ _ (by simp [size_eq]),
      show 2 * n = bytes.size from size_eq.symm,
      ByteArray.getElem!_push_eq]
  · change ((bytes.push p.a).push p.b)[2 * n + 1]! = p.b
    rw [show 2 * n + 1 = (bytes.push p.a).size by simp [size_eq],
      ByteArray.getElem!_push_eq]

theorem pairAt_pointwiseProductBytes (a b : ByteArray) {n i : ℕ}
    (i_lt : i < n) :
    pairAt (pointwiseProductBytes a b n) i =
      (pairAt a i).mul (pairAt b i) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [pointwiseProductBytes]
      by_cases i_lt_n : i < n
      · have second_lt : 2 * i + 1 < (pointwiseProductBytes a b n).size := by
          rw [pointwiseProductBytes_size]
          omega
        rw [pairAt_pushExtByteArray_lt _ _ second_lt]
        exact ih i_lt_n
      · have i_eq : i = n := by omega
        subst i
        exact pairAt_pushExtByteArray_last _ _ n
          (pointwiseProductBytes_size a b n)

theorem mulByteVectors_pairAt {a b out : ByteArray} {n i : ℕ}
    (result : mulByteVectors a b n = .ok out) (i_lt : i < n) :
    pairAt out i = (pairAt a i).mul (pairAt b i) := by
  simp only [mulByteVectors] at result
  split at result <;> try contradiction
  split at result <;> try contradiction
  have out_eq := Except.ok.inj result
  subst out
  exact pairAt_pointwiseProductBytes a b i_lt

theorem mulByteVectors_encodedVector {a b out : ByteArray} {n : ℕ}
    (result : mulByteVectors a b n = .ok out) :
    encodedVector out n =
      fun i => encodedVector a n i * encodedVector b n i := by
  funext i
  rw [encodedVector, encodedVector, encodedVector,
    mulByteVectors_pairAt result i.isLt,
    ExtElt.toCertificateField_mul]

@[simp]
theorem matrixApplyShiftedNormalBytesData_size
    (matrixBytes : ByteArray) (header : MatrixHeader) (x : ByteArray) (n : ℕ) :
    (matrixApplyShiftedNormalBytesData matrixBytes header x n).size = 2 * n := by
  induction n with
  | zero => simp [matrixApplyShiftedNormalBytesData]
  | succ n ih =>
      simp [matrixApplyShiftedNormalBytesData, pushExtByteArray, ih]
      omega

theorem pairAt_matrixApplyShiftedNormalBytesData
    (matrixBytes : ByteArray) (header : MatrixHeader) (x : ByteArray)
    {n row : ℕ} (row_lt : row < n) :
    pairAt (matrixApplyShiftedNormalBytesData matrixBytes header x n) row =
      matrixApplyShiftedNormalRow matrixBytes header x row := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [matrixApplyShiftedNormalBytesData]
      by_cases row_lt_n : row < n
      · have second_lt : 2 * row + 1 <
          (matrixApplyShiftedNormalBytesData matrixBytes header x n).size := by
          rw [matrixApplyShiftedNormalBytesData_size]
          omega
        rw [pairAt_pushExtByteArray_lt _ _ second_lt]
        exact ih row_lt_n
      · have row_eq : row = n := by omega
        subst row
        exact pairAt_pushExtByteArray_last _ _ n
          (matrixApplyShiftedNormalBytesData_size matrixBytes header x n)

theorem matrixApplyShiftedNormalBytes_pairAt
    {matrixBytes : ByteArray} {header : MatrixHeader} {x out : ByteArray}
    (result : matrixApplyShiftedNormalBytes matrixBytes header x = .ok out)
    (row : Fin header.n) :
    pairAt out row = matrixApplyShiftedNormalRow matrixBytes header x row := by
  simp only [matrixApplyShiftedNormalBytes] at result
  split at result <;> try contradiction
  have out_eq := Except.ok.inj result
  subst out
  exact pairAt_matrixApplyShiftedNormalBytesData matrixBytes header x row.isLt

theorem matrixApplyShiftedNormalBytes_encodedVector
    {matrixBytes : ByteArray} {header : MatrixHeader} {x out : ByteArray}
    (result : matrixApplyShiftedNormalBytes matrixBytes header x = .ok out)
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    encodedVector out header.n =
      shiftedCSRLinearMap matrixBytes header (encodedVector x header.n) := by
  funext row
  rw [encodedVector, matrixApplyShiftedNormalBytes_pairAt result row,
    matrixApplyShiftedNormalRow_toCertificateField matrixBytes header x row
      (columns_valid row)]

/-- One complete normal certificate step computes
`D_L (M - 50 I) D_R` on interpreted vectors. -/
theorem krylovStepBytes_normal_encodedVector
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {dR dL x out : ByteArray}
    (result : krylovStepBytes matrixBytes header none dR dL x header.n = .ok out)
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    encodedVector out header.n =
      preconditionedCSRLinearMap matrixBytes header dR dL
        (encodedVector x header.n) := by
  simp only [krylovStepBytes] at result
  generalize dx_result : mulByteVectors dR x header.n = dxResult at result
  cases dxResult with
  | error message => contradiction
  | ok dx =>
      change (matrixApplyShiftedNormalBytes matrixBytes header dx >>= fun y =>
        mulByteVectors dL y header.n) = .ok out at result
      generalize shifted_result :
        matrixApplyShiftedNormalBytes matrixBytes header dx = shiftedResult at result
      cases shiftedResult with
      | error message =>
          change (Except.error message : ParseM ByteArray) = .ok out at result
          contradiction
      | ok y =>
          change mulByteVectors dL y header.n = .ok out at result
          have dx_semantics := mulByteVectors_encodedVector dx_result
          have y_semantics := matrixApplyShiftedNormalBytes_encodedVector
            shifted_result columns_valid
          have out_semantics := mulByteVectors_encodedVector result
          rw [out_semantics]
          change encodedDiagonalLinearMap dL header.n (encodedVector y header.n) = _
          rw [y_semantics, dx_semantics]
          rfl

/-- Repeated successful byte steps represent powers of the normal
preconditioned operator. -/
theorem normalKrylovOrbit_encodedVector
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {dR dL initial : ByteArray} (orbit : ℕ → ByteArray)
    (orbit_zero : orbit 0 = initial)
    (step : ∀ k, krylovStepBytes matrixBytes header none dR dL (orbit k)
      header.n = .ok (orbit (k + 1)))
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    ∀ k, encodedVector (orbit k) header.n =
      (preconditionedCSRLinearMap matrixBytes header dR dL ^ k)
        (encodedVector initial header.n) := by
  intro k
  induction k with
  | zero => simp [orbit_zero]
  | succ k ih =>
      rw [krylovStepBytes_normal_encodedVector (step k) columns_valid, ih]
      simp [pow_succ', Module.End.mul_apply]

/-- A checked encoded dot product along such an orbit is the corresponding
scalar Krylov moment. -/
theorem normalKrylovMoment_of_orbit
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {dR dL probe initial : ByteArray} (orbit : ℕ → ByteArray)
    (orbit_zero : orbit 0 = initial)
    (step : ∀ k, krylovStepBytes matrixBytes header none dR dL (orbit k)
      header.n = .ok (orbit (k + 1)))
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n)
    (k : ℕ) :
    (extDotBytes probe (orbit k) header.n).toCertificateField =
      scalarKrylovMoment (encodedProbeLinearMap probe header.n)
        (preconditionedCSRLinearMap matrixBytes header dR dL)
        (encodedVector initial header.n) k := by
  rw [extDotBytes_eq_encodedProbe,
    normalKrylovOrbit_encodedVector orbit orbit_zero step columns_valid k]
  rfl

theorem RankCertificateFile.fieldMoment_eq_normalKrylovMoment_of_orbit
    (cert : RankCertificateFile)
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {dR dL probe initial : ByteArray} (orbit : ℕ → ByteArray)
    (orbit_zero : orbit 0 = initial)
    (step : ∀ k, krylovStepBytes matrixBytes header none dR dL (orbit k)
      header.n = .ok (orbit (k + 1)))
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n)
    {k : ℕ}
    (stored_match : pairAt cert.moments k =
      extDotBytes probe (orbit k) header.n) :
    cert.fieldMoment k =
      scalarKrylovMoment (encodedProbeLinearMap probe header.n)
        (preconditionedCSRLinearMap matrixBytes header dR dL)
        (encodedVector initial header.n) k := by
  rw [RankCertificateFile.fieldMoment, stored_match]
  exact normalKrylovMoment_of_orbit orbit orbit_zero step columns_valid k

/-- All mathematical pieces of a normal rank certificate, assembled.  The
remaining executable bridge is to obtain `orbit`, `stored_match`, and the full
stored recurrence from zero checker mismatch counts. -/
theorem PadeWitnessFile.injective_normal_of_checked_orbit
    (witness : PadeWitnessFile) (cert : RankCertificateFile)
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {dR dL probe initial : ByteArray} (orbit : ℕ → ByteArray)
    (degree_gt_one : 1 < cert.degree)
    (degree_eq : cert.degree = header.n)
    (bm_terms : cert.bmTerms = 2 * cert.degree)
    (u_length_le : witness.uLength ≤ cert.degree)
    (v_length_le : witness.vLength ≤ cert.degree)
    (no_bad : witness.bezoutBad cert = 0)
    (leading : cert.fieldCoefficient 0 = 1)
    (constant_ne_zero : cert.fieldCoefficient cert.degree ≠ 0)
    (orbit_zero : orbit 0 = initial)
    (step : ∀ k, krylovStepBytes matrixBytes header none dR dL (orbit k)
      header.n = .ok (orbit (k + 1)))
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n)
    (stored_match : ∀ k < 2 * cert.degree, pairAt cert.moments k =
      extDotBytes probe (orbit k) header.n)
    (stored_recurrence : ∀ k < cert.degree,
      ∑ i ∈ Finset.range (cert.degree + 1),
        cert.fieldCoefficient (cert.degree - i) * cert.fieldMoment (k + i) = 0) :
    Function.Injective
      (preconditionedCSRLinearMap matrixBytes header dR dL) := by
  let u := encodedProbeLinearMap probe header.n
  let A := preconditionedCSRLinearMap matrixBytes header dR dL
  let w := encodedVector initial header.n
  have moment_match : ∀ k < 2 * cert.degree,
      cert.fieldMoment k = scalarKrylovMoment u A w k := by
    intro k k_lt
    exact cert.fieldMoment_eq_normalKrylovMoment_of_orbit orbit orbit_zero step
      columns_valid (stored_match k k_lt)
  have recurrence : ∀ k < cert.degree,
      ∑ i ∈ Finset.range (cert.degree + 1),
        cert.fieldCoefficient (cert.degree - i) *
          scalarKrylovMoment u A w (k + i) = 0 := by
    intro k k_lt
    rw [← stored_recurrence k k_lt]
    apply Finset.sum_congr rfl
    intro i i_mem
    have i_lt : i < cert.degree + 1 := Finset.mem_range.mp i_mem
    rw [moment_match (k + i) (by omega)]
  have dimension : Module.finrank CertificateField
      (Fin header.n → CertificateField) = cert.degree := by
    simp [degree_eq]
  exact witness.injective_of_checked_pade cert u A w degree_gt_one dimension
    bm_terms u_length_le v_length_le no_bad moment_match leading recurrence
    constant_ne_zero

end

end KnuthFasc8aEx210
