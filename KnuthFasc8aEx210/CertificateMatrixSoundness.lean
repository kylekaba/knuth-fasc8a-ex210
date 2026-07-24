import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import KnuthFasc8aEx210.CertificateFieldEncoding
import KnuthFasc8aEx210.CertificatePadeSoundness
import KnuthFasc8aEx210.BorderLemma

/-!
# Soundness of encoded matrix-certificate operations

This file begins the bridge from executable Krylov replay to a mathematical
linear operator over `CertificateField`.
-/

namespace KnuthFasc8aEx210

noncomputable section

open Polynomial

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

theorem matrixColumnAt_lt_of_matrixCSRColumnBad_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (no_bad : matrixCSRColumnBad matrixBytes header = 0)
    {entry : ℕ} (entry_lt : entry < header.entries) :
    matrixColumnAt matrixBytes header entry < header.n := by
  by_contra column_bad
  have bad_mem : entry ∈ (List.range header.entries).filter (fun i =>
      decide (header.n ≤ matrixColumnAt matrixBytes header i)) := by
    simp [entry_lt, Nat.le_of_not_gt column_bad]
  have bad_pos : 0 < matrixCSRColumnBad matrixBytes header := by
    rw [matrixCSRColumnBad]
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem bad_mem)
  omega

theorem matrixRowBounds_of_matrixCSRRowPointerBad_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (no_bad : matrixCSRRowPointerBad matrixBytes header = 0)
    (row : Fin header.n) :
    matrixRowStart matrixBytes header row ≤ matrixRowStop matrixBytes header row ∧
      matrixRowStop matrixBytes header row ≤ header.entries := by
  by_contra bounds_bad
  have invalid :
      matrixRowStop matrixBytes header row < matrixRowStart matrixBytes header row ∨
        header.entries < matrixRowStop matrixBytes header row := by
    omega
  have bad_mem : row.val ∈ (List.range header.n).filter (fun i =>
      decide (matrixRowStop matrixBytes header i <
        matrixRowStart matrixBytes header i ∨
        header.entries < matrixRowStop matrixBytes header i)) := by
    simp [row.isLt, invalid]
  have bad_pos : 0 < matrixCSRRowPointerBad matrixBytes header := by
    rw [matrixCSRRowPointerBad]
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem bad_mem)
  omega

/-- Zero proof-shaped CSR counters imply the quantified column bound consumed
by every sparse-row semantics theorem. -/
theorem matrixColumnsValid_of_bad_counts_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (column_bad : matrixCSRColumnBad matrixBytes header = 0)
    (row_pointer_bad : matrixCSRRowPointerBad matrixBytes header = 0) :
    ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n := by
  intro row offset offset_lt
  have bounds := matrixRowBounds_of_matrixCSRRowPointerBad_eq_zero
    matrixBytes header row_pointer_bad row
  apply matrixColumnAt_lt_of_matrixCSRColumnBad_eq_zero matrixBytes header
    column_bad
  omega

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

theorem pairAt_isCanonical_of_encodedVectorCanonicalBad_eq_zero
    (bytes : ByteArray) (count : ℕ)
    (canonical_bad : encodedVectorCanonicalBad bytes count = 0)
    (i : Fin count) : (pairAt bytes i).IsCanonical := by
  by_contra not_canonical
  have invalid : 101 ≤ (pairAt bytes i).a.toNat ∨
      101 ≤ (pairAt bytes i).b.toNat := by
    simp only [ExtElt.IsCanonical, not_and_or, not_lt] at not_canonical
    exact not_canonical
  have bad_mem : i.val ∈ (List.range count).filter (fun j =>
      let x := pairAt bytes j
      decide (101 ≤ x.a.toNat ∨ 101 ≤ x.b.toNat)) := by
    simp [i.isLt, invalid]
  have bad_pos : 0 < encodedVectorCanonicalBad bytes count := by
    rw [encodedVectorCanonicalBad]
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem bad_mem)
  omega

theorem encodedVector_ne_zero_of_bad_counts_eq_zero
    (bytes : ByteArray) (count : ℕ)
    (canonical_bad : encodedVectorCanonicalBad bytes count = 0)
    (zero_bad : encodedVectorZeroBad bytes count = 0) :
    ∀ i : Fin count, encodedVector bytes count i ≠ 0 := by
  intro i field_zero
  have canonical := pairAt_isCanonical_of_encodedVectorCanonicalBad_eq_zero
    bytes count canonical_bad i
  have zero_test : (pairAt bytes i).isZero = true :=
    (ExtElt.toCertificateField_eq_zero_iff _ canonical).1 field_zero
  have bad_mem : i.val ∈ (List.range count).filter (fun j =>
      (pairAt bytes j).isZero) := by
    simp [i.isLt, zero_test]
  have bad_pos : 0 < encodedVectorZeroBad bytes count := by
    rw [encodedVectorZeroBad]
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem bad_mem)
  omega

theorem encodedDiagonalLinearMap_surjective
    (diagonal : ByteArray) (n : ℕ)
    (nonzero : ∀ i : Fin n, encodedVector diagonal n i ≠ 0) :
    Function.Surjective (encodedDiagonalLinearMap diagonal n) := by
  intro y
  refine ⟨fun i => (encodedVector diagonal n i)⁻¹ * y i, ?_⟩
  funext i
  simp [encodedDiagonalLinearMap, nonzero i]

/-- Normal-certificate operator `D_L (M - 50 I) D_R`. -/
def preconditionedCSRLinearMap (matrixBytes : ByteArray) (header : MatrixHeader)
    (dR dL : ByteArray) :
    Module.End CertificateField (Fin header.n → CertificateField) :=
  (encodedDiagonalLinearMap dL header.n).comp
    ((shiftedCSRLinearMap matrixBytes header).comp
      (encodedDiagonalLinearMap dR header.n))

theorem shiftedCSRLinearMap_injective_of_preconditioned_injective
    (matrixBytes : ByteArray) (header : MatrixHeader) (dR dL : ByteArray)
    (right_surjective : Function.Surjective
      (encodedDiagonalLinearMap dR header.n))
    (preconditioned_injective : Function.Injective
      (preconditionedCSRLinearMap matrixBytes header dR dL)) :
    Function.Injective (shiftedCSRLinearMap matrixBytes header) := by
  intro x y middle_equal
  obtain ⟨x', rfl⟩ := right_surjective x
  obtain ⟨y', rfl⟩ := right_surjective y
  apply congrArg (encodedDiagonalLinearMap dR header.n)
  apply preconditioned_injective
  change encodedDiagonalLinearMap dL header.n
      (shiftedCSRLinearMap matrixBytes header
        (encodedDiagonalLinearMap dR header.n x')) =
    encodedDiagonalLinearMap dL header.n
      (shiftedCSRLinearMap matrixBytes header
        (encodedDiagonalLinearMap dR header.n y'))
  rw [middle_equal]

theorem shiftedCSRLinearMap_injective_of_preconditioned_and_diagonal_counters
    (matrixBytes : ByteArray) (header : MatrixHeader) (dR dL : ByteArray)
    (dR_canonical_bad : encodedVectorCanonicalBad dR header.n = 0)
    (dR_zero_bad : encodedVectorZeroBad dR header.n = 0)
    (preconditioned_injective : Function.Injective
      (preconditionedCSRLinearMap matrixBytes header dR dL)) :
    Function.Injective (shiftedCSRLinearMap matrixBytes header) := by
  apply shiftedCSRLinearMap_injective_of_preconditioned_injective
    matrixBytes header dR dL
  · apply encodedDiagonalLinearMap_surjective
    exact encodedVector_ne_zero_of_bad_counts_eq_zero dR header.n
      dR_canonical_bad dR_zero_bad
  · exact preconditioned_injective

/-- An injective shifted operator has no corresponding characteristic root. -/
theorem charpoly_rootMultiplicity_eq_zero_of_shift_injective
    {n : ℕ} (f : Module.End CertificateField (Fin n → CertificateField))
    (mu : CertificateField)
    (shift_injective : Function.Injective
      (f - mu • (1 : Module.End CertificateField
        (Fin n → CertificateField)))) :
    f.charpoly.rootMultiplicity mu = 0 := by
  apply rootMultiplicity_eq_zero
  intro root
  have has_eigenvalue : f.HasEigenvalue mu :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f mu).2 root
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_def,
    LinearMap.ker_eq_bot.mpr shift_injective] at has_eigenvalue
  exact has_eigenvalue rfl

theorem csr_charpoly_rootMultiplicity_fifty_eq_zero_of_checked_counters
    (matrixBytes : ByteArray) (header : MatrixHeader) (dR dL : ByteArray)
    (preconditioned_injective : Function.Injective
      (preconditionedCSRLinearMap matrixBytes header dR dL))
    (dR_canonical_bad : encodedVectorCanonicalBad dR header.n = 0)
    (dR_zero_bad : encodedVectorZeroBad dR header.n = 0) :
    (csrLinearMap matrixBytes header).charpoly.rootMultiplicity
      (50 : CertificateField) = 0 := by
  apply charpoly_rootMultiplicity_eq_zero_of_shift_injective
  exact shiftedCSRLinearMap_injective_of_preconditioned_and_diagonal_counters
    matrixBytes header dR dL dR_canonical_bad dR_zero_bad
      preconditioned_injective

/-- Interpret the prime-field eigenvector bytes in the extension field. -/
def encodedEigenVector (eig : EigenvectorFile) (n : ℕ) :
    Fin n → CertificateField :=
  fun row => algebraMap (ZMod 101) CertificateField (eigenValueAt eig row)

/-- Coordinate functional used as the bottom row of the bordered matrix. -/
def coordinateLinearMap {n : ℕ} (pivot : Fin n) :
    (Fin n → CertificateField) →ₗ[CertificateField] CertificateField where
  toFun x := x pivot
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The parsed bordered operator on `n+1` encoded coordinates.  The first `n`
coordinates are `(M - 50I)x + c v`; the last is the pivot coordinate of `x`. -/
def borderedCSRLinearMap (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (pivot : Fin header.n) :
    Module.End CertificateField (Fin (header.n + 1) → CertificateField) where
  toFun x := Fin.lastCases (x pivot.castSucc) (fun row =>
    shiftedCSRLinearMap matrixBytes header (fun col => x col.castSucc) row +
      x (Fin.last header.n) * encodedEigenVector eig header.n row)
  map_add' x y := by
    funext i
    refine Fin.lastCases ?_ (fun row => ?_) i
    · simp
    · simp only [Fin.lastCases_castSucc, Pi.add_apply]
      have shifted_add :
          shiftedCSRLinearMap matrixBytes header
              (fun col => x col.castSucc + y col.castSucc) row =
            shiftedCSRLinearMap matrixBytes header
                (fun col => x col.castSucc) row +
              shiftedCSRLinearMap matrixBytes header
                (fun col => y col.castSucc) row := by
        rw [show (fun col : Fin header.n =>
            x col.castSucc + y col.castSucc) =
          (fun col => x col.castSucc) + (fun col => y col.castSucc) by rfl]
        exact congrFun
          ((shiftedCSRLinearMap matrixBytes header).map_add
            (fun col => x col.castSucc) (fun col => y col.castSucc)) row
      rw [shifted_add]
      ring
  map_smul' c x := by
    funext i
    refine Fin.lastCases ?_ (fun row => ?_) i
    · simp
    · simp only [Fin.lastCases_castSucc, Pi.smul_apply, RingHom.id_apply]
      have shifted_smul :
          shiftedCSRLinearMap matrixBytes header
              (fun col => c * x col.castSucc) row =
            c * shiftedCSRLinearMap matrixBytes header
              (fun col => x col.castSucc) row := by
        rw [show (fun col : Fin header.n => c * x col.castSucc) =
          c • (fun col => x col.castSucc) by rfl]
        exact congrFun
          ((shiftedCSRLinearMap matrixBytes header).map_smul c
            (fun col => x col.castSucc)) row
      change shiftedCSRLinearMap matrixBytes header
          (fun col => c * x col.castSucc) row +
        (c * x (Fin.last header.n)) * encodedEigenVector eig header.n row =
          c * (shiftedCSRLinearMap matrixBytes header
            (fun col => x col.castSucc) row +
              x (Fin.last header.n) * encodedEigenVector eig header.n row)
      rw [shifted_smul]
      ring

/-- Diagonally preconditioned bordered operator used by the bordered rank
certificate. -/
def preconditionedBorderedCSRLinearMap
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (pivot : Fin header.n) (dR dL : ByteArray) :
    Module.End CertificateField (Fin (header.n + 1) → CertificateField) :=
  (encodedDiagonalLinearMap dL (header.n + 1)).comp
    ((borderedCSRLinearMap matrixBytes header eig pivot).comp
      (encodedDiagonalLinearMap dR (header.n + 1)))

/-- Injectivity of `D_L B D_R` and surjectivity of `D_R` imply injectivity of
the unpreconditioned middle operator `B`. -/
theorem borderedCSRLinearMap_injective_of_preconditioned_injective
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (pivot : Fin header.n) (dR dL : ByteArray)
    (right_surjective : Function.Surjective
      (encodedDiagonalLinearMap dR (header.n + 1)))
    (preconditioned_injective : Function.Injective
      (preconditionedBorderedCSRLinearMap matrixBytes header eig pivot dR dL)) :
    Function.Injective (borderedCSRLinearMap matrixBytes header eig pivot) := by
  intro x y middle_equal
  obtain ⟨x', rfl⟩ := right_surjective x
  obtain ⟨y', rfl⟩ := right_surjective y
  apply congrArg (encodedDiagonalLinearMap dR (header.n + 1))
  apply preconditioned_injective
  change encodedDiagonalLinearMap dL (header.n + 1)
      (borderedCSRLinearMap matrixBytes header eig pivot
        (encodedDiagonalLinearMap dR (header.n + 1) x')) =
    encodedDiagonalLinearMap dL (header.n + 1)
      (borderedCSRLinearMap matrixBytes header eig pivot
        (encodedDiagonalLinearMap dR (header.n + 1) y'))
  rw [middle_equal]

theorem borderedCSRLinearMap_injective_of_preconditioned_and_diagonal_counters
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (pivot : Fin header.n) (dR dL : ByteArray)
    (dR_canonical_bad : encodedVectorCanonicalBad dR (header.n + 1) = 0)
    (dR_zero_bad : encodedVectorZeroBad dR (header.n + 1) = 0)
    (preconditioned_injective : Function.Injective
      (preconditionedBorderedCSRLinearMap matrixBytes header eig pivot dR dL)) :
    Function.Injective (borderedCSRLinearMap matrixBytes header eig pivot) := by
  apply borderedCSRLinearMap_injective_of_preconditioned_injective
    matrixBytes header eig pivot dR dL
  · apply encodedDiagonalLinearMap_surjective
    exact encodedVector_ne_zero_of_bad_counts_eq_zero dR (header.n + 1)
      dR_canonical_bad dR_zero_bad
  · exact preconditioned_injective

/-- Split an `(n+1)`-coordinate vector into its first `n` coordinates and its
last scalar coordinate. -/
def finSuccProdLinearEquiv (n : ℕ) :
    (Fin (n + 1) → CertificateField) ≃ₗ[CertificateField]
      (Fin n → CertificateField) × CertificateField where
  toFun x := (fun i => x i.castSucc, x (Fin.last n))
  invFun z := Fin.lastCases z.2 z.1
  left_inv x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv z := by
    apply Prod.ext
    · funext i
      simp
    · simp
  map_add' x y := by
    apply Prod.ext
    · funext i
      rfl
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · funext i
      rfl
    · rfl

/-- The coordinate-level bordered CSR map is exactly the abstract bordered
operator after splitting off the last coordinate. -/
theorem finSuccProdLinearEquiv_borderedCSRLinearMap
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (pivot : Fin header.n)
    (x : Fin (header.n + 1) → CertificateField) :
    finSuccProdLinearEquiv header.n
        (borderedCSRLinearMap matrixBytes header eig pivot x) =
      borderedOperator (shiftedCSRLinearMap matrixBytes header)
        (encodedEigenVector eig header.n) (coordinateLinearMap pivot)
        (finSuccProdLinearEquiv header.n x) := by
  apply Prod.ext
  · funext row
    simp [finSuccProdLinearEquiv, borderedCSRLinearMap, borderedOperator,
      coordinateLinearMap, Fin.lastCases_castSucc]
  · simp [finSuccProdLinearEquiv, borderedCSRLinearMap, borderedOperator,
      coordinateLinearMap, Fin.lastCases_last]

/-- Injectivity of the coordinate-level bordered CSR map transfers to the
abstract bordered operator used by `BorderLemma`. -/
theorem borderedOperator_injective_of_borderedCSRLinearMap_injective
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (pivot : Fin header.n)
    (injective : Function.Injective
      (borderedCSRLinearMap matrixBytes header eig pivot)) :
    Function.Injective
      (borderedOperator (shiftedCSRLinearMap matrixBytes header)
        (encodedEigenVector eig header.n) (coordinateLinearMap pivot)) := by
  intro x y equal
  let e := finSuccProdLinearEquiv header.n
  apply e.symm.injective
  apply injective
  apply e.injective
  rw [finSuccProdLinearEquiv_borderedCSRLinearMap,
    finSuccProdLinearEquiv_borderedCSRLinearMap]
  simpa [e] using equal

/-- The checked bordered CSR operator is already in the exact form required to
deduce that `50` has algebraic multiplicity one in the unbordered transfer
matrix. -/
theorem csr_charpoly_rootMultiplicity_fifty_eq_one_of_bordered_injective
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (pivot : Fin header.n)
    (eigen_residual : shiftedCSRLinearMap matrixBytes header
      (encodedEigenVector eig header.n) = 0)
    (pivot_ne_zero : encodedEigenVector eig header.n pivot ≠ 0)
    (border_injective : Function.Injective
      (borderedCSRLinearMap matrixBytes header eig pivot)) :
    (csrLinearMap matrixBytes header).charpoly.rootMultiplicity
      (50 : CertificateField) = 1 := by
  have eigenvector : csrLinearMap matrixBytes header
      (encodedEigenVector eig header.n) =
        (50 : CertificateField) • encodedEigenVector eig header.n := by
    have shifted_eq : csrLinearMap matrixBytes header
          (encodedEigenVector eig header.n) -
        (50 : CertificateField) • encodedEigenVector eig header.n = 0 := by
      simpa [shiftedCSRLinearMap] using eigen_residual
    exact sub_eq_zero.mp shifted_eq
  have abstract_injective :=
    borderedOperator_injective_of_borderedCSRLinearMap_injective
      matrixBytes header eig pivot border_injective
  exact charpoly_rootMultiplicity_eq_one_of_bordered_injective
    (csrLinearMap matrixBytes header) (50 : CertificateField)
    (encodedEigenVector eig header.n) (coordinateLinearMap pivot)
    eigenvector pivot_ne_zero abstract_injective

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

theorem matrixApplyShiftedNormalRow_isCanonical
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (x : ByteArray) (row : ℕ) :
    (matrixApplyShiftedNormalRow matrixBytes header x row).IsCanonical := by
  apply ExtElt.isCanonical_sub
  · simp only [matrixRowBytes, ExtElt.IsCanonical]
    constructor <;> rw [toNat_u8Mod101] <;> exact Nat.mod_lt _ (by omega)
  · exact ExtElt.isCanonical_scale 50 _

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

@[simp]
theorem eigenPairBytes_size (eig : EigenvectorFile) (n : ℕ) :
    (eigenPairBytes eig n).size = 2 * n := by
  induction n with
  | zero => simp [eigenPairBytes]
  | succ n ih => simp [eigenPairBytes, pushExtByteArray, ih]; omega

theorem pairAt_eigenPairBytes (eig : EigenvectorFile) {n i : ℕ}
    (i_lt : i < n) :
    pairAt (eigenPairBytes eig n) i = { a := eig.values[i]!, b := 0 } := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [eigenPairBytes]
      by_cases i_lt_n : i < n
      · have second_lt : 2 * i + 1 < (eigenPairBytes eig n).size := by
          rw [eigenPairBytes_size]
          omega
        rw [pairAt_pushExtByteArray_lt _ _ second_lt]
        exact ih i_lt_n
      · have i_eq : i = n := by omega
        subst i
        exact pairAt_pushExtByteArray_last _ _ n (eigenPairBytes_size eig n)

theorem encodedVector_eigenPairBytes
    (eig : EigenvectorFile) (n : ℕ) :
    encodedVector (eigenPairBytes eig n) n = encodedEigenVector eig n := by
  funext i
  rw [encodedVector, pairAt_eigenPairBytes eig i.isLt]
  simp [ExtElt.toCertificateField, encodedEigenVector, eigenValueAt,
    certificatePair]

theorem encodedEigenVector_ne_zero_of_canonical_count
    (eig : EigenvectorFile) (n : ℕ) (pivot : Fin n)
    (canonical_bad : encodedVectorCanonicalBad (eigenPairBytes eig n) n = 0)
    (value_ne_zero : eigenValueAt eig pivot ≠ 0) :
    encodedEigenVector eig n pivot ≠ 0 := by
  rw [← encodedVector_eigenPairBytes eig n]
  intro field_zero
  have canonical := pairAt_isCanonical_of_encodedVectorCanonicalBad_eq_zero
    (eigenPairBytes eig n) n canonical_bad pivot
  have zero_test := (ExtElt.toCertificateField_eq_zero_iff _ canonical).1 field_zero
  rw [pairAt_eigenPairBytes eig pivot.isLt] at zero_test
  simp only [ExtElt.isZero, Bool.and_eq_true, beq_iff_eq] at zero_test
  apply value_ne_zero
  simp [eigenValueAt, zero_test.1]

theorem eigenResidualRow_isZero_of_mismatchCount_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader) (eig : EigenvectorFile)
    (no_bad : eigenResidualMismatchCount matrixBytes header eig = 0)
    (row : Fin header.n) :
    (matrixApplyShiftedNormalRow matrixBytes header
      (eigenPairBytes eig header.n) row).isZero = true := by
  by_contra mismatch
  have zero_test_false :
      (matrixApplyShiftedNormalRow matrixBytes header
        (eigenPairBytes eig header.n) row).isZero = false :=
    Bool.eq_false_of_not_eq_true mismatch
  have bad_mem : row.val ∈ (List.range header.n).filter (fun i =>
      (matrixApplyShiftedNormalRow matrixBytes header
        (eigenPairBytes eig header.n) i).isZero != true) := by
    simp [row.isLt, zero_test_false]
  have bad_pos : 0 < eigenResidualMismatchCount matrixBytes header eig := by
    rw [eigenResidualMismatchCount]
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem bad_mem)
  omega

/-- A zero proof-shaped residual count proves that the parsed vector is a
genuine `50`-eigenvector of the CSR matrix. -/
theorem shiftedCSRLinearMap_encodedEigenVector_eq_zero_of_residualCount_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader) (eig : EigenvectorFile)
    (residual_bad : eigenResidualMismatchCount matrixBytes header eig = 0)
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    shiftedCSRLinearMap matrixBytes header (encodedEigenVector eig header.n) = 0 := by
  funext row
  rw [← encodedVector_eigenPairBytes eig header.n,
    ← matrixApplyShiftedNormalRow_toCertificateField matrixBytes header
      (eigenPairBytes eig header.n) row (columns_valid row)]
  apply (ExtElt.toCertificateField_eq_zero_iff _
    (matrixApplyShiftedNormalRow_isCanonical matrixBytes header
      (eigenPairBytes eig header.n) row)).2
  exact eigenResidualRow_isZero_of_mismatchCount_eq_zero
    matrixBytes header eig residual_bad row

theorem matrixApplyShiftedBorderRow_toCertificateField
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (x : ByteArray) (row : Fin header.n)
    (columns_valid : ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    (matrixApplyShiftedBorderRow matrixBytes header eig x row).toCertificateField =
      shiftedCSRLinearMap matrixBytes header
          (fun col => encodedVector x (header.n + 1) col.castSucc) row +
        encodedVector x (header.n + 1) (Fin.last header.n) *
          encodedEigenVector eig header.n row := by
  have row_canonical :
      (matrixRowBytes matrixBytes header x row).IsCanonical := by
    simp only [matrixRowBytes, ExtElt.IsCanonical]
    constructor <;> rw [toNat_u8Mod101] <;> exact Nat.mod_lt _ (by omega)
  have border_canonical :
      ((pairAt x header.n).scale (eigenValueAt eig row)).IsCanonical :=
    ExtElt.isCanonical_scale _ _
  have sum_canonical :
      ((matrixRowBytes matrixBytes header x row).add
        ((pairAt x header.n).scale (eigenValueAt eig row))).IsCanonical :=
    ExtElt.isCanonical_add _ _
  have shift_canonical : ((pairAt x row).scale 50).IsCanonical :=
    ExtElt.isCanonical_scale 50 _
  have restrict_eq : encodedVector x header.n =
      (fun col => encodedVector x (header.n + 1) col.castSucc) := by
    rfl
  calc
    (matrixApplyShiftedBorderRow matrixBytes header eig x row).toCertificateField =
        (matrixApplyShiftedNormalRow matrixBytes header x row).toCertificateField +
          ((pairAt x header.n).scale
            (eigenValueAt eig row)).toCertificateField := by
      rw [matrixApplyShiftedBorderRow, matrixApplyShiftedNormalRow,
        ExtElt.toCertificateField_sub sum_canonical shift_canonical,
        ExtElt.toCertificateField_add,
        ExtElt.toCertificateField_sub row_canonical shift_canonical]
      ring
    _ = shiftedCSRLinearMap matrixBytes header
          (encodedVector x header.n) row +
        algebraMap (ZMod 101) CertificateField (eigenValueAt eig row) *
          (pairAt x header.n).toCertificateField := by
      rw [matrixApplyShiftedNormalRow_toCertificateField matrixBytes header x row
        columns_valid, ExtElt.toCertificateField_scale]
    _ = _ := by
      rw [restrict_eq]
      simp [encodedVector, encodedEigenVector]
      ring

@[simp]
theorem pointwiseProductBytes_size (a b : ByteArray) (n : ℕ) :
    (pointwiseProductBytes a b n).size = 2 * n := by
  induction n with
  | zero => simp [pointwiseProductBytes]
  | succ n ih =>
      simp [pointwiseProductBytes, pushExtByteArray, ih]
      omega

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

@[simp]
theorem matrixApplyShiftedBorderBytesData_size
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (x : ByteArray) (n : ℕ) :
    (matrixApplyShiftedBorderBytesData matrixBytes header eig x n).size = 2 * n := by
  induction n with
  | zero => simp [matrixApplyShiftedBorderBytesData]
  | succ n ih =>
      simp [matrixApplyShiftedBorderBytesData, pushExtByteArray, ih]
      omega

theorem pairAt_matrixApplyShiftedBorderBytesData
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (x : ByteArray)
    {n row : ℕ} (row_lt : row < n) :
    pairAt (matrixApplyShiftedBorderBytesData matrixBytes header eig x n) row =
      matrixApplyShiftedBorderRow matrixBytes header eig x row := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [matrixApplyShiftedBorderBytesData]
      by_cases row_lt_n : row < n
      · have second_lt : 2 * row + 1 <
          (matrixApplyShiftedBorderBytesData matrixBytes header eig x n).size := by
          rw [matrixApplyShiftedBorderBytesData_size]
          omega
        rw [pairAt_pushExtByteArray_lt _ _ second_lt]
        exact ih row_lt_n
      · have row_eq : row = n := by omega
        subst row
        exact pairAt_pushExtByteArray_last _ _ n
          (matrixApplyShiftedBorderBytesData_size matrixBytes header eig x n)

theorem matrixApplyShiftedBorderBytes_pairAt_top
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {eig : EigenvectorFile} {x out : ByteArray}
    (result : matrixApplyShiftedBorderBytes matrixBytes header eig x = .ok out)
    (row : Fin header.n) :
    pairAt out row = matrixApplyShiftedBorderRow matrixBytes header eig x row := by
  simp only [matrixApplyShiftedBorderBytes] at result
  split at result <;> try contradiction
  split at result <;> try contradiction
  split at result <;> try contradiction
  have out_eq := Except.ok.inj result
  subst out
  have second_lt : 2 * row.val + 1 <
      (matrixApplyShiftedBorderBytesData matrixBytes header eig x header.n).size := by
    rw [matrixApplyShiftedBorderBytesData_size]
    omega
  rw [pairAt_pushExtByteArray_lt _ _ second_lt]
  exact pairAt_matrixApplyShiftedBorderBytesData matrixBytes header eig x row.isLt

theorem matrixApplyShiftedBorderBytes_pairAt_last
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {eig : EigenvectorFile} {x out : ByteArray}
    (result : matrixApplyShiftedBorderBytes matrixBytes header eig x = .ok out) :
    pairAt out header.n = pairAt x eig.pivot := by
  simp only [matrixApplyShiftedBorderBytes] at result
  split at result <;> try contradiction
  split at result <;> try contradiction
  split at result <;> try contradiction
  have out_eq := Except.ok.inj result
  subst out
  exact pairAt_pushExtByteArray_last _ _ header.n
    (matrixApplyShiftedBorderBytesData_size matrixBytes header eig x header.n)

theorem matrixApplyShiftedBorderBytes_encodedVector
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {eig : EigenvectorFile} {pivot : Fin header.n} {x out : ByteArray}
    (result : matrixApplyShiftedBorderBytes matrixBytes header eig x = .ok out)
    (pivot_eq : eig.pivot = pivot.val)
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    encodedVector out (header.n + 1) =
      borderedCSRLinearMap matrixBytes header eig pivot
        (encodedVector x (header.n + 1)) := by
  funext i
  refine Fin.lastCases ?_ (fun row => ?_) i
  · change (pairAt out header.n).toCertificateField = _
    rw [matrixApplyShiftedBorderBytes_pairAt_last result,
      pivot_eq]
    simp [borderedCSRLinearMap, encodedVector]
  · change (pairAt out row.val).toCertificateField = _
    rw [matrixApplyShiftedBorderBytes_pairAt_top result row,
      matrixApplyShiftedBorderRow_toCertificateField matrixBytes header eig x row
        (columns_valid row)]
    simp [borderedCSRLinearMap]

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

/-- One complete bordered certificate step computes the diagonally
preconditioned `[M - 50I, v; pivot, 0]` operator. -/
theorem krylovStepBytes_border_encodedVector
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {eig : EigenvectorFile} {pivot : Fin header.n}
    {dR dL x out : ByteArray}
    (result : krylovStepBytes matrixBytes header (some eig) dR dL x
      (header.n + 1) = .ok out)
    (pivot_eq : eig.pivot = pivot.val)
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    encodedVector out (header.n + 1) =
      preconditionedBorderedCSRLinearMap matrixBytes header eig pivot dR dL
        (encodedVector x (header.n + 1)) := by
  simp only [krylovStepBytes] at result
  generalize dx_result : mulByteVectors dR x (header.n + 1) = dxResult at result
  cases dxResult with
  | error message => contradiction
  | ok dx =>
      change (matrixApplyShiftedBorderBytes matrixBytes header eig dx >>= fun y =>
        mulByteVectors dL y (header.n + 1)) = .ok out at result
      generalize shifted_result :
        matrixApplyShiftedBorderBytes matrixBytes header eig dx = shiftedResult at result
      cases shiftedResult with
      | error message =>
          change (Except.error message : ParseM ByteArray) = .ok out at result
          contradiction
      | ok y =>
          change mulByteVectors dL y (header.n + 1) = .ok out at result
          have dx_semantics := mulByteVectors_encodedVector dx_result
          have y_semantics := matrixApplyShiftedBorderBytes_encodedVector
            shifted_result pivot_eq columns_valid
          have out_semantics := mulByteVectors_encodedVector result
          rw [out_semantics]
          change encodedDiagonalLinearMap dL (header.n + 1)
            (encodedVector y (header.n + 1)) = _
          rw [y_semantics, dx_semantics]
          rfl

@[simp]
theorem normalKrylovOrbitBytes_zero
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (dR dL initial : ByteArray) :
    normalKrylovOrbitBytes matrixBytes header dR dL initial 0 = initial := by
  rfl

theorem normalKrylovOrbitBytes_size
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (dR dL initial : ByteArray) (initial_size : initial.size = 2 * header.n) :
    ∀ k, (normalKrylovOrbitBytes matrixBytes header dR dL initial k).size =
      2 * header.n := by
  intro k
  cases k with
  | zero => exact initial_size
  | succ k => simp [normalKrylovOrbitBytes, pointwiseProductBytes_size]

theorem KrylovSeedByteData.sizes_of_sizeBad_eq_zero
    (data : KrylovSeedByteData) (order : ℕ)
    (no_bad : data.sizeBad order = 0) :
    data.dR.size = 2 * order ∧ data.dL.size = 2 * order ∧
      data.u.size = 2 * order ∧ data.x.size = 2 * order := by
  simp only [KrylovSeedByteData.sizeBad] at no_bad
  split at no_bad <;> split at no_bad <;> split at no_bad <;>
    split at no_bad <;> simp_all

/-- The canonical total normal orbit makes every partial byte step succeed
when the three input vectors have the expected encoded dimension. -/
theorem krylovStepBytes_normalKrylovOrbit
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (dR dL initial : ByteArray)
    (dR_size : dR.size = 2 * header.n)
    (dL_size : dL.size = 2 * header.n)
    (initial_size : initial.size = 2 * header.n) :
    ∀ k, krylovStepBytes matrixBytes header none dR dL
      (normalKrylovOrbitBytes matrixBytes header dR dL initial k) header.n =
        .ok (normalKrylovOrbitBytes matrixBytes header dR dL initial (k + 1)) := by
  intro k
  let orbit := normalKrylovOrbitBytes matrixBytes header dR dL initial k
  let dx := pointwiseProductBytes dR orbit header.n
  let y := matrixApplyShiftedNormalBytesData matrixBytes header dx header.n
  have orbit_size : orbit.size = 2 * header.n :=
    normalKrylovOrbitBytes_size matrixBytes header dR dL initial initial_size k
  have dx_result : mulByteVectors dR orbit header.n = .ok dx := by
    simp [mulByteVectors, dx, dR_size, orbit_size]
  have y_result : matrixApplyShiftedNormalBytes matrixBytes header dx = .ok y := by
    simp [matrixApplyShiftedNormalBytes, y, dx,
      pointwiseProductBytes_size]
  have out_result : mulByteVectors dL y header.n =
      .ok (pointwiseProductBytes dL y header.n) := by
    simp [mulByteVectors, dL_size, y, matrixApplyShiftedNormalBytesData_size]
  change (mulByteVectors dR orbit header.n >>= fun dx' =>
    matrixApplyShiftedNormalBytes matrixBytes header dx' >>= fun y' =>
      mulByteVectors dL y' header.n) = _
  rw [dx_result]
  change (matrixApplyShiftedNormalBytes matrixBytes header dx >>= fun y' =>
    mulByteVectors dL y' header.n) = _
  rw [y_result]
  change mulByteVectors dL y header.n =
    .ok (pointwiseProductBytes dL y header.n)
  exact out_result

/-- A zero mismatch count proves every stored moment in the requested prefix
equals the dot product along the canonical normal byte orbit. -/
theorem RankCertificateFile.storedMoment_eq_normalKrylovOrbit_of_mismatchCount_eq_zero
    (cert : RankCertificateFile) (matrixBytes : ByteArray)
    (header : MatrixHeader) (dR dL probe initial : ByteArray) (count : ℕ)
    (no_bad : cert.normalKrylovMismatchCount matrixBytes header dR dL probe
      initial count = 0) :
    ∀ k < count, pairAt cert.moments k =
      extDotBytes probe
        (normalKrylovOrbitBytes matrixBytes header dR dL initial k) header.n := by
  intro k k_lt
  by_contra mismatch
  have k_mem : k ∈ List.range count := by simpa using k_lt
  have bad_mem : k ∈ (List.range count).filter (fun i =>
      pairAt cert.moments i !=
        extDotBytes probe
          (normalKrylovOrbitBytes matrixBytes header dR dL initial i)
          header.n) := by
    simp [k_mem, mismatch]
  have bad_pos : 0 < cert.normalKrylovMismatchCount matrixBytes header dR dL
      probe initial count := by
    rw [RankCertificateFile.normalKrylovMismatchCount]
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem bad_mem)
  omega

@[simp]
theorem matrixApplyShiftedBorderBytesValue_size
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (x : ByteArray) :
    (matrixApplyShiftedBorderBytesValue matrixBytes header eig x).size =
      2 * (header.n + 1) := by
  simp [matrixApplyShiftedBorderBytesValue, pushExtByteArray,
    matrixApplyShiftedBorderBytesData_size]
  omega

theorem borderKrylovOrbitBytes_size
    (matrixBytes : ByteArray) (header : MatrixHeader) (eig : EigenvectorFile)
    (dR dL initial : ByteArray)
    (initial_size : initial.size = 2 * (header.n + 1)) :
    ∀ k, (borderKrylovOrbitBytes matrixBytes header eig dR dL initial k).size =
      2 * (header.n + 1) := by
  intro k
  cases k with
  | zero => exact initial_size
  | succ k => simp [borderKrylovOrbitBytes, pointwiseProductBytes_size]

/-- The canonical total bordered orbit makes every partial byte step succeed
under the checked dimension and pivot metadata. -/
theorem krylovStepBytes_borderKrylovOrbit
    (matrixBytes : ByteArray) (header : MatrixHeader) (eig : EigenvectorFile)
    (dR dL initial : ByteArray)
    (eig_n : eig.n = header.n) (pivot_lt : eig.pivot < header.n)
    (dR_size : dR.size = 2 * (header.n + 1))
    (dL_size : dL.size = 2 * (header.n + 1))
    (initial_size : initial.size = 2 * (header.n + 1)) :
    ∀ k, krylovStepBytes matrixBytes header (some eig) dR dL
      (borderKrylovOrbitBytes matrixBytes header eig dR dL initial k)
      (header.n + 1) =
        .ok (borderKrylovOrbitBytes matrixBytes header eig dR dL initial (k + 1)) := by
  intro k
  let orbit := borderKrylovOrbitBytes matrixBytes header eig dR dL initial k
  let dx := pointwiseProductBytes dR orbit (header.n + 1)
  let y := matrixApplyShiftedBorderBytesValue matrixBytes header eig dx
  have orbit_size : orbit.size = 2 * (header.n + 1) :=
    borderKrylovOrbitBytes_size matrixBytes header eig dR dL initial
      initial_size k
  have dx_result : mulByteVectors dR orbit (header.n + 1) = .ok dx := by
    simp [mulByteVectors, dx, dR_size, orbit_size]
  have y_result : matrixApplyShiftedBorderBytes matrixBytes header eig dx = .ok y := by
    simp [matrixApplyShiftedBorderBytes, matrixApplyShiftedBorderBytesValue,
      y, dx, pointwiseProductBytes_size, eig_n, pivot_lt]
  have out_result : mulByteVectors dL y (header.n + 1) =
      .ok (pointwiseProductBytes dL y (header.n + 1)) := by
    simp [mulByteVectors, dL_size, y, matrixApplyShiftedBorderBytesValue_size]
  change (mulByteVectors dR orbit (header.n + 1) >>= fun dx' =>
    matrixApplyShiftedBorderBytes matrixBytes header eig dx' >>= fun y' =>
      mulByteVectors dL y' (header.n + 1)) = _
  rw [dx_result]
  change (matrixApplyShiftedBorderBytes matrixBytes header eig dx >>= fun y' =>
    mulByteVectors dL y' (header.n + 1)) = _
  rw [y_result]
  change mulByteVectors dL y (header.n + 1) =
    .ok (pointwiseProductBytes dL y (header.n + 1))
  exact out_result

theorem RankCertificateFile.storedMoment_eq_borderKrylovOrbit_of_mismatchCount_eq_zero
    (cert : RankCertificateFile) (matrixBytes : ByteArray)
    (header : MatrixHeader) (eig : EigenvectorFile)
    (dR dL probe initial : ByteArray) (count : ℕ)
    (no_bad : cert.borderKrylovMismatchCount matrixBytes header eig dR dL probe
      initial count = 0) :
    ∀ k < count, pairAt cert.moments k =
      extDotBytes probe
        (borderKrylovOrbitBytes matrixBytes header eig dR dL initial k)
        (header.n + 1) := by
  intro k k_lt
  by_contra mismatch
  have k_mem : k ∈ List.range count := by simpa using k_lt
  have bad_mem : k ∈ (List.range count).filter (fun i =>
      pairAt cert.moments i !=
        extDotBytes probe
          (borderKrylovOrbitBytes matrixBytes header eig dR dL initial i)
          (header.n + 1)) := by
    simp [k_mem, mismatch]
  have bad_pos : 0 < cert.borderKrylovMismatchCount matrixBytes header eig dR dL
      probe initial count := by
    rw [RankCertificateFile.borderKrylovMismatchCount]
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem bad_mem)
  omega

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

/-- Repeated successful bordered byte steps represent powers of the
preconditioned bordered CSR operator. -/
theorem borderKrylovOrbit_encodedVector
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {eig : EigenvectorFile} {pivot : Fin header.n}
    {dR dL initial : ByteArray} (orbit : ℕ → ByteArray)
    (orbit_zero : orbit 0 = initial)
    (step : ∀ k, krylovStepBytes matrixBytes header (some eig) dR dL (orbit k)
      (header.n + 1) = .ok (orbit (k + 1)))
    (pivot_eq : eig.pivot = pivot.val)
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    ∀ k, encodedVector (orbit k) (header.n + 1) =
      (preconditionedBorderedCSRLinearMap matrixBytes header eig pivot dR dL ^ k)
        (encodedVector initial (header.n + 1)) := by
  intro k
  induction k with
  | zero => simp [orbit_zero]
  | succ k ih =>
      rw [krylovStepBytes_border_encodedVector (step k) pivot_eq columns_valid, ih]
      simp [pow_succ', Module.End.mul_apply]

theorem borderKrylovMoment_of_orbit
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {eig : EigenvectorFile} {pivot : Fin header.n}
    {dR dL probe initial : ByteArray} (orbit : ℕ → ByteArray)
    (orbit_zero : orbit 0 = initial)
    (step : ∀ k, krylovStepBytes matrixBytes header (some eig) dR dL (orbit k)
      (header.n + 1) = .ok (orbit (k + 1)))
    (pivot_eq : eig.pivot = pivot.val)
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n)
    (k : ℕ) :
    (extDotBytes probe (orbit k) (header.n + 1)).toCertificateField =
      scalarKrylovMoment (encodedProbeLinearMap probe (header.n + 1))
        (preconditionedBorderedCSRLinearMap matrixBytes header eig pivot dR dL)
        (encodedVector initial (header.n + 1)) k := by
  rw [extDotBytes_eq_encodedProbe,
    borderKrylovOrbit_encodedVector orbit orbit_zero step pivot_eq columns_valid k]
  rfl

/-- All mathematical pieces of a normal rank certificate, assembled from an
explicit replay orbit and stored recurrence. -/
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

/-- A normal certificate with no full-recurrence mismatches proves the
preconditioned shifted CSR operator injective.  Only the replay orbit and its
agreement with the stored moments remain as executable bridge premises. -/
theorem PadeWitnessFile.injective_normal_of_checked_full_recurrence
    (witness : PadeWitnessFile) (cert : RankCertificateFile)
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {dR dL probe initial : ByteArray} (orbit : ℕ → ByteArray)
    (degree_gt_one : 1 < cert.degree)
    (degree_eq : cert.degree = header.n)
    (bm_terms : cert.bmTerms = 2 * cert.degree)
    (bm_terms_le : cert.bmTerms ≤ cert.terms)
    (u_length_le : witness.uLength ≤ cert.degree)
    (v_length_le : witness.vLength ≤ cert.degree)
    (no_bad : witness.bezoutBad cert = 0)
    (full_recurrence_bad : cert.fullRecurrenceBad = 0)
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
      extDotBytes probe (orbit k) header.n) :
    Function.Injective
      (preconditionedCSRLinearMap matrixBytes header dR dL) := by
  apply witness.injective_normal_of_checked_orbit cert orbit degree_gt_one
    degree_eq bm_terms u_length_le v_length_le no_bad leading constant_ne_zero
    orbit_zero step columns_valid stored_match
  exact cert.stored_recurrence_of_fullRecurrenceBad_eq_zero bm_terms bm_terms_le
    full_recurrence_bad

/-- Zero recurrence and canonical-orbit mismatch counts are sufficient for
normal-certificate injectivity.  The replay orbit, successful step equations,
and individual stored-moment equalities are all derived internally. -/
theorem PadeWitnessFile.injective_normal_of_checked_mismatch_counts
    (witness : PadeWitnessFile) (cert : RankCertificateFile)
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {dR dL probe initial : ByteArray}
    (degree_gt_one : 1 < cert.degree)
    (degree_eq : cert.degree = header.n)
    (bm_terms : cert.bmTerms = 2 * cert.degree)
    (bm_terms_le : cert.bmTerms ≤ cert.terms)
    (u_length_le : witness.uLength ≤ cert.degree)
    (v_length_le : witness.vLength ≤ cert.degree)
    (no_bad : witness.bezoutBad cert = 0)
    (full_recurrence_bad : cert.fullRecurrenceBad = 0)
    (krylov_bad : cert.normalKrylovMismatchCount matrixBytes header dR dL
      probe initial (2 * cert.degree) = 0)
    (leading : cert.fieldCoefficient 0 = 1)
    (constant_ne_zero : cert.fieldCoefficient cert.degree ≠ 0)
    (dR_size : dR.size = 2 * header.n)
    (dL_size : dL.size = 2 * header.n)
    (initial_size : initial.size = 2 * header.n)
    (columns_valid : ∀ row : Fin header.n, ∀ offset <
      matrixRowStop matrixBytes header row - matrixRowStart matrixBytes header row,
      matrixColumnAt matrixBytes header
        (matrixRowStart matrixBytes header row + offset) < header.n) :
    Function.Injective
      (preconditionedCSRLinearMap matrixBytes header dR dL) := by
  let orbit := normalKrylovOrbitBytes matrixBytes header dR dL initial
  apply witness.injective_normal_of_checked_full_recurrence cert orbit
    degree_gt_one degree_eq bm_terms bm_terms_le u_length_le v_length_le no_bad
    full_recurrence_bad leading constant_ne_zero
  · rfl
  · exact krylovStepBytes_normalKrylovOrbit matrixBytes header dR dL initial
      dR_size dL_size initial_size
  · exact columns_valid
  · exact cert.storedMoment_eq_normalKrylovOrbit_of_mismatchCount_eq_zero
      matrixBytes header dR dL probe initial (2 * cert.degree) krylov_bad

/-- Fully counter-shaped normal-certificate bridge: recurrence, Krylov replay,
and CSR structure are all supplied by zero executable mismatch counts. -/
theorem PadeWitnessFile.injective_normal_of_checked_counters
    (witness : PadeWitnessFile) (cert : RankCertificateFile)
    {matrixBytes : ByteArray} {header : MatrixHeader}
    {dR dL probe initial : ByteArray}
    (degree_gt_one : 1 < cert.degree)
    (degree_eq : cert.degree = header.n)
    (bm_terms : cert.bmTerms = 2 * cert.degree)
    (bm_terms_le : cert.bmTerms ≤ cert.terms)
    (u_length_le : witness.uLength ≤ cert.degree)
    (v_length_le : witness.vLength ≤ cert.degree)
    (no_bad : witness.bezoutBad cert = 0)
    (full_recurrence_bad : cert.fullRecurrenceBad = 0)
    (krylov_bad : cert.normalKrylovMismatchCount matrixBytes header dR dL
      probe initial (2 * cert.degree) = 0)
    (csr_column_bad : matrixCSRColumnBad matrixBytes header = 0)
    (csr_row_pointer_bad : matrixCSRRowPointerBad matrixBytes header = 0)
    (leading : cert.fieldCoefficient 0 = 1)
    (constant_ne_zero : cert.fieldCoefficient cert.degree ≠ 0)
    (dR_size : dR.size = 2 * header.n)
    (dL_size : dL.size = 2 * header.n)
    (initial_size : initial.size = 2 * header.n) :
    Function.Injective
      (preconditionedCSRLinearMap matrixBytes header dR dL) := by
  apply witness.injective_normal_of_checked_mismatch_counts cert degree_gt_one
    degree_eq bm_terms bm_terms_le u_length_le v_length_le no_bad
    full_recurrence_bad krylov_bad leading constant_ne_zero dR_size dL_size
    initial_size
  exact matrixColumnsValid_of_bad_counts_eq_zero matrixBytes header
    csr_column_bad csr_row_pointer_bad

/-- Counter-shaped bridge specialized to a seed-expansion record. -/
theorem PadeWitnessFile.injective_normal_of_checked_seed_counters
    (witness : PadeWitnessFile) (cert : RankCertificateFile)
    {matrixBytes : ByteArray} {header : MatrixHeader}
    (seedData : KrylovSeedByteData)
    (degree_gt_one : 1 < cert.degree)
    (degree_eq : cert.degree = header.n)
    (bm_terms : cert.bmTerms = 2 * cert.degree)
    (bm_terms_le : cert.bmTerms ≤ cert.terms)
    (u_length_le : witness.uLength ≤ cert.degree)
    (v_length_le : witness.vLength ≤ cert.degree)
    (no_bad : witness.bezoutBad cert = 0)
    (full_recurrence_bad : cert.fullRecurrenceBad = 0)
    (krylov_bad : cert.normalKrylovMismatchCount matrixBytes header
      seedData.dR seedData.dL seedData.u seedData.x (2 * cert.degree) = 0)
    (csr_column_bad : matrixCSRColumnBad matrixBytes header = 0)
    (csr_row_pointer_bad : matrixCSRRowPointerBad matrixBytes header = 0)
    (seed_size_bad : seedData.sizeBad header.n = 0)
    (leading : cert.fieldCoefficient 0 = 1)
    (constant_ne_zero : cert.fieldCoefficient cert.degree ≠ 0) :
    Function.Injective
      (preconditionedCSRLinearMap matrixBytes header seedData.dR seedData.dL) := by
  have sizes := seedData.sizes_of_sizeBad_eq_zero header.n seed_size_bad
  exact witness.injective_normal_of_checked_counters cert degree_gt_one degree_eq
    bm_terms bm_terms_le u_length_le v_length_le no_bad full_recurrence_bad
    krylov_bad csr_column_bad csr_row_pointer_bad leading constant_ne_zero
    sizes.1 sizes.2.1 sizes.2.2.2

/-- Fully counter-shaped bordered-certificate bridge.  A successful checked
certificate proves injectivity of the diagonally preconditioned bordered CSR
operator without exposing replay-orbit or per-moment premises. -/
theorem PadeWitnessFile.injective_border_of_checked_seed_counters
    (witness : PadeWitnessFile) (cert : RankCertificateFile)
    {matrixBytes : ByteArray} {header : MatrixHeader}
    (eig : EigenvectorFile) (pivot : Fin header.n)
    (seedData : KrylovSeedByteData)
    (degree_gt_one : 1 < cert.degree)
    (degree_eq : cert.degree = header.n + 1)
    (bm_terms : cert.bmTerms = 2 * cert.degree)
    (bm_terms_le : cert.bmTerms ≤ cert.terms)
    (u_length_le : witness.uLength ≤ cert.degree)
    (v_length_le : witness.vLength ≤ cert.degree)
    (no_bad : witness.bezoutBad cert = 0)
    (full_recurrence_bad : cert.fullRecurrenceBad = 0)
    (krylov_bad : cert.borderKrylovMismatchCount matrixBytes header eig
      seedData.dR seedData.dL seedData.u seedData.x (2 * cert.degree) = 0)
    (csr_column_bad : matrixCSRColumnBad matrixBytes header = 0)
    (csr_row_pointer_bad : matrixCSRRowPointerBad matrixBytes header = 0)
    (seed_size_bad : seedData.sizeBad (header.n + 1) = 0)
    (eig_n : eig.n = header.n)
    (pivot_eq : eig.pivot = pivot.val)
    (leading : cert.fieldCoefficient 0 = 1)
    (constant_ne_zero : cert.fieldCoefficient cert.degree ≠ 0) :
    Function.Injective
      (preconditionedBorderedCSRLinearMap matrixBytes header eig pivot
        seedData.dR seedData.dL) := by
  let orbit := borderKrylovOrbitBytes matrixBytes header eig
    seedData.dR seedData.dL seedData.x
  let u := encodedProbeLinearMap seedData.u (header.n + 1)
  let A := preconditionedBorderedCSRLinearMap matrixBytes header eig pivot
    seedData.dR seedData.dL
  let w := encodedVector seedData.x (header.n + 1)
  have sizes := seedData.sizes_of_sizeBad_eq_zero (header.n + 1) seed_size_bad
  have pivot_lt : eig.pivot < header.n := by rw [pivot_eq]; exact pivot.isLt
  have columns_valid := matrixColumnsValid_of_bad_counts_eq_zero
    matrixBytes header csr_column_bad csr_row_pointer_bad
  have step : ∀ k, krylovStepBytes matrixBytes header (some eig)
      seedData.dR seedData.dL (orbit k) (header.n + 1) = .ok (orbit (k + 1)) :=
    krylovStepBytes_borderKrylovOrbit matrixBytes header eig seedData.dR
      seedData.dL seedData.x eig_n pivot_lt sizes.1 sizes.2.1 sizes.2.2.2
  have stored_match : ∀ k < 2 * cert.degree, pairAt cert.moments k =
      extDotBytes seedData.u (orbit k) (header.n + 1) :=
    cert.storedMoment_eq_borderKrylovOrbit_of_mismatchCount_eq_zero
      matrixBytes header eig seedData.dR seedData.dL seedData.u seedData.x
      (2 * cert.degree) krylov_bad
  have moment_match : ∀ k < 2 * cert.degree,
      cert.fieldMoment k = scalarKrylovMoment u A w k := by
    intro k k_lt
    rw [RankCertificateFile.fieldMoment, stored_match k k_lt]
    exact borderKrylovMoment_of_orbit orbit rfl step pivot_eq columns_valid k
  have stored_recurrence :=
    cert.stored_recurrence_of_fullRecurrenceBad_eq_zero bm_terms bm_terms_le
      full_recurrence_bad
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
      (Fin (header.n + 1) → CertificateField) = cert.degree := by
    simp [degree_eq]
  exact witness.injective_of_checked_pade cert u A w degree_gt_one dimension
    bm_terms u_length_le v_length_le no_bad moment_match leading recurrence
    constant_ne_zero

/-- The final bordered matrix bridge: checked preconditioned injectivity,
diagonal validity, CSR validity, and the eigenvector residual imply algebraic
multiplicity one for `50` in the unbordered CSR characteristic polynomial. -/
theorem csr_charpoly_rootMultiplicity_fifty_eq_one_of_checked_counters
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (eig : EigenvectorFile) (pivot : Fin header.n) (dR dL : ByteArray)
    (preconditioned_injective : Function.Injective
      (preconditionedBorderedCSRLinearMap matrixBytes header eig pivot dR dL))
    (dR_canonical_bad : encodedVectorCanonicalBad dR (header.n + 1) = 0)
    (dR_zero_bad : encodedVectorZeroBad dR (header.n + 1) = 0)
    (csr_column_bad : matrixCSRColumnBad matrixBytes header = 0)
    (csr_row_pointer_bad : matrixCSRRowPointerBad matrixBytes header = 0)
    (eigen_residual_bad : eigenResidualMismatchCount matrixBytes header eig = 0)
    (eigen_canonical_bad :
      encodedVectorCanonicalBad (eigenPairBytes eig header.n) header.n = 0)
    (pivot_value_ne_zero : eigenValueAt eig pivot ≠ 0) :
    (csrLinearMap matrixBytes header).charpoly.rootMultiplicity
      (50 : CertificateField) = 1 := by
  have columns_valid := matrixColumnsValid_of_bad_counts_eq_zero
    matrixBytes header csr_column_bad csr_row_pointer_bad
  have border_injective :=
    borderedCSRLinearMap_injective_of_preconditioned_and_diagonal_counters
      matrixBytes header eig pivot dR dL dR_canonical_bad dR_zero_bad
      preconditioned_injective
  have eigen_residual :=
    shiftedCSRLinearMap_encodedEigenVector_eq_zero_of_residualCount_eq_zero
      matrixBytes header eig eigen_residual_bad columns_valid
  have pivot_ne_zero := encodedEigenVector_ne_zero_of_canonical_count
    eig header.n pivot eigen_canonical_bad pivot_value_ne_zero
  exact csr_charpoly_rootMultiplicity_fifty_eq_one_of_bordered_injective
    matrixBytes header eig pivot eigen_residual pivot_ne_zero border_injective

end

end KnuthFasc8aEx210
