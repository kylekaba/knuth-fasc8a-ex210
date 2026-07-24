import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import KnuthFasc8aEx210.TransferMultiplicity

/-!
# Transfer matrices and reduced scalar denominators

This file formalizes the standard adjugate argument behind the denominator
statement used in the Knuth counterexample: every scalar matrix resolvent has
reduced denominator dividing `det (1 - X M)`.
-/

namespace KnuthFasc8aEx210

open Matrix Polynomial

noncomputable section

variable {K : Type*} [Field K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Polynomial matrix `1 - X M`. -/
def transferPolynomialMatrix (M : Matrix n n K) : Matrix n n K[X] :=
  1 - (X : K[X]) • M.map C

/-- Polynomial numerator obtained from the adjugate for a startup vector and
a terminal functional. -/
def transferNumerator (M : Matrix n n K) (start finish : n → K) : K[X] :=
  dotProduct (fun i => C (finish i))
    ((transferPolynomialMatrix M).adjugate *ᵥ (fun i => C (start i)))

/-- Scalar transfer rational function represented by the matrix resolvent. -/
def transferRatFunc (M : Matrix n n K) (start finish : n → K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (transferNumerator M start finish) /
    algebraMap K[X] (RatFunc K) M.charpolyRev

/-- Its canonical reduced denominator. -/
def transferDenominator (M : Matrix n n K) (start finish : n → K) : K[X] :=
  RatFunc.denom (transferRatFunc M start finish)

theorem transferPolynomialMatrix_det (M : Matrix n n K) :
    (transferPolynomialMatrix M).det = M.charpolyRev := by
  rfl

theorem charpolyRev_ne_zero (M : Matrix n n K) : M.charpolyRev ≠ 0 := by
  intro polynomial_zero
  have at_zero := congrArg (Polynomial.eval 0) polynomial_zero
  simp at at_zero

/-- Adjugate identity for the polynomial transfer matrix. -/
theorem transferPolynomialMatrix_mulVec_adjugate
    (M : Matrix n n K) (start : n → K) :
    transferPolynomialMatrix M *ᵥ
        ((transferPolynomialMatrix M).adjugate *ᵥ
          (fun i => C (start i))) =
      M.charpolyRev • (fun i => C (start i)) := by
  rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec,
    transferPolynomialMatrix_det]

/-- The reduced scalar denominator divides the characteristic power series
`det (1 - X M)`. -/
theorem transferDenominator_dvd_charpolyRev
    (M : Matrix n n K) (start finish : n → K) :
    transferDenominator M start finish ∣ M.charpolyRev := by
  unfold transferDenominator transferRatFunc
  exact RatFunc.denom_div_dvd _ _

theorem transferDenominator_monic
    (M : Matrix n n K) (start finish : n → K) :
    (transferDenominator M start finish).Monic := by
  unfold transferDenominator
  exact RatFunc.monic_denom _

theorem transferDenominator_coeff_zero_ne_zero
    (M : Matrix n n K) (start finish : n → K) :
    (transferDenominator M start finish).coeff 0 ≠ 0 := by
  intro constant_zero
  obtain ⟨q, factorization⟩ :=
    transferDenominator_dvd_charpolyRev M start finish
  have determinant_at_zero : Polynomial.eval 0 M.charpolyRev = 0 := by
    rw [factorization, eval_mul, ← coeff_zero_eq_eval_zero,
      constant_zero, zero_mul]
  simp at determinant_at_zero

/-- Constant-term-one normalization of the reduced transfer denominator. -/
def normalizedTransferDenominator
    (M : Matrix n n K) (start finish : n → K) : K[X] :=
  C ((transferDenominator M start finish).coeff 0)⁻¹ *
    transferDenominator M start finish

theorem normalizedTransferDenominator_coeff_zero
    (M : Matrix n n K) (start finish : n → K) :
    (normalizedTransferDenominator M start finish).coeff 0 = 1 := by
  simp [normalizedTransferDenominator,
    transferDenominator_coeff_zero_ne_zero]

theorem normalizedTransferDenominator_associated
    (M : Matrix n n K) (start finish : n → K) :
    Associated (normalizedTransferDenominator M start finish)
      (transferDenominator M start finish) := by
  apply associated_unit_mul_left
  rw [isUnit_C, isUnit_iff_ne_zero]
  exact inv_ne_zero
    (transferDenominator_coeff_zero_ne_zero M start finish)

theorem normalizedTransferDenominator_dvd_charpolyRev
    (M : Matrix n n K) (start finish : n → K) :
    normalizedTransferDenominator M start finish ∣ M.charpolyRev :=
  (normalizedTransferDenominator_associated M start finish).dvd.trans
    (transferDenominator_dvd_charpolyRev M start finish)

section Recurrences

/-- The scalar sequence observed from repeated application of a transfer
matrix. -/
def scalarKrylovSequence (M : Matrix n n K) (observe start : n → K)
    (k : ℕ) : K :=
  dotProduct observe (M ^ k *ᵥ start)

/-- A polynomial gives a forward recurrence for the observed Krylov
sequence when its coefficients annihilate every shifted window. -/
def IsForwardRecurrence (M : Matrix n n K) (observe start : n → K)
    (p : K[X]) : Prop :=
  ∀ k : ℕ, ∑ i ∈ Finset.range (p.natDegree + 1),
    p.coeff i * scalarKrylovSequence M observe start (k + i) = 0

theorem pow_mulVec_of_mulVec_eq_smul
    (M : Matrix n n K) (v : n → K) (a : K)
    (eigenvector : M *ᵥ v = a • v) :
    ∀ k : ℕ, M ^ k *ᵥ v = a ^ k • v := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec v M (M ^ k), ih, mulVec_smul,
        eigenvector]
      simp [pow_succ, smul_smul]

theorem scalarKrylovSequence_of_eigenvector
    (M : Matrix n n K) (observe v : n → K) (a : K)
    (eigenvector : M *ᵥ v = a • v) (k : ℕ) :
    scalarKrylovSequence M observe v k =
      a ^ k * dotProduct observe v := by
  rw [scalarKrylovSequence,
    pow_mulVec_of_mulVec_eq_smul M v a eigenvector k,
    dotProduct_smul]
  rfl

/-- An observable eigenvector forces every forward recurrence polynomial to
vanish at its eigenvalue. -/
theorem IsForwardRecurrence.isRoot_of_eigenvector
    (M : Matrix n n K) (observe v : n → K) (p : K[X]) (a : K)
    (recurrence : IsForwardRecurrence M observe v p)
    (eigenvector : M *ᵥ v = a • v)
    (visible : dotProduct observe v ≠ 0) :
    p.IsRoot a := by
  rw [Polynomial.IsRoot.def]
  have recurrence_zero := recurrence 0
  simp only [zero_add,
    scalarKrylovSequence_of_eigenvector M observe v a eigenvector] at recurrence_zero
  simp_rw [← mul_assoc] at recurrence_zero
  rw [← Finset.sum_mul, ← Polynomial.eval_eq_sum_range] at recurrence_zero
  exact (mul_eq_zero.mp recurrence_zero).resolve_right visible

/-- Over `F₁₀₁`, an observable eigenvector at eigenvalue `50` turns a
forward recurrence for the reversed denominator into the factor
`1 - 50X` of the denominator itself. -/
theorem visibleFactor_dvd_of_reverse_recurrence_eigenvector
    (M : Matrix n n F101) (observe v : n → F101) (q : ModPolynomial)
    (recurrence : IsForwardRecurrence M observe v q.reverse)
    (eigenvector : M *ᵥ v = (50 : F101) • v)
    (visible : dotProduct observe v ≠ 0) :
    visibleFactor ∣ q := by
  have reverse_root : q.reverse.IsRoot (50 : F101) :=
    recurrence.isRoot_of_eigenvector M observe v q.reverse 50
      eigenvector visible
  have ninetyNine_ne_zero : (99 : F101) ≠ 0 := by native_decide
  letI : Invertible (99 : F101) := invertibleOfNonzero ninetyNine_ne_zero
  have ninetyNine_inv : (99 : F101)⁻¹ = 50 := by native_decide
  have q_root : q.IsRoot (99 : F101) := by
    rw [Polynomial.IsRoot.def]
    apply (eval₂_reverse_eq_zero_iff (RingHom.id F101) (99 : F101) q).mp
    simpa [invOf_eq_inv, ninetyNine_inv] using reverse_root.eq_zero
  have linear_dvd : X - C (99 : F101) ∣ q := dvd_iff_isRoot.mpr q_root
  have scalar_unit : IsUnit (C (-50 : F101)) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    native_decide
  have factor_associated :
      Associated visibleFactor (X - C (99 : F101)) := by
    rw [visibleFactor_eq_unit_mul_X_sub_C]
    exact associated_unit_mul_left _ _ scalar_unit
  exact factor_associated.dvd_iff_dvd_left.mpr linear_dvd

end Recurrences

section Blocks

variable {m o : Type*} [Fintype m] [DecidableEq m]
  [Fintype o] [DecidableEq o]

/-- Characteristic power series multiply across an upper block-triangular
matrix. -/
theorem charpolyRev_fromBlocks_zero₂₁
    (A : Matrix m m K) (B : Matrix m o K) (D : Matrix o o K) :
    (Matrix.fromBlocks A B 0 D).charpolyRev = A.charpolyRev * D.charpolyRev := by
  rw [← Matrix.reverse_charpoly, Matrix.charpoly_fromBlocks_zero₂₁,
    reverse_mul_of_domain, Matrix.reverse_charpoly, Matrix.reverse_charpoly]

/-- The analogous lower block-triangular identity. -/
theorem charpolyRev_fromBlocks_zero₁₂
    (A : Matrix m m K) (C : Matrix o m K) (D : Matrix o o K) :
    (Matrix.fromBlocks A 0 C D).charpolyRev = A.charpolyRev * D.charpolyRev := by
  rw [← Matrix.reverse_charpoly, Matrix.charpoly_fromBlocks_zero₁₂,
    reverse_mul_of_domain, Matrix.reverse_charpoly, Matrix.reverse_charpoly]

/-- Simultaneous row/column permutation preserves the characteristic power
series. -/
theorem charpolyRev_reindex (e : m ≃ o) (M : Matrix m m K) :
    (Matrix.reindex e e M).charpolyRev = M.charpolyRev := by
  rw [← Matrix.reverse_charpoly, Matrix.charpoly_reindex,
    Matrix.reverse_charpoly]

end Blocks

section WidthFiveObstruction

variable {closedIndex openIndex : Type*}
  [Fintype closedIndex] [DecidableEq closedIndex]
  [Fintype openIndex] [DecidableEq openIndex]

/-- Matrix-level modular obstruction: a visible factor in the reduced closed
scalar denominator and multiplicity two in the open transfer determinant rule
out cubic divisibility of the normalized scalar denominators. -/
theorem normalizedTransferDenominator_cube_not_dvd
    (closedMatrix : Matrix closedIndex closedIndex F101)
    (closedStart closedFinish : closedIndex → F101)
    (openMatrix : Matrix openIndex openIndex F101)
    (openStart openFinish : openIndex → F101)
    (closed_visible : visibleFactor ∣
      normalizedTransferDenominator closedMatrix closedStart closedFinish)
    (open_multiplicity :
      emultiplicity visibleFactor openMatrix.charpolyRev = 2) :
    ¬(normalizedTransferDenominator closedMatrix closedStart closedFinish ^ 3 ∣
      normalizedTransferDenominator openMatrix openStart openFinish) := by
  intro denominator_cube_dvd
  have visible_cube_dvd_open_denominator : visibleFactor ^ 3 ∣
      normalizedTransferDenominator openMatrix openStart openFinish :=
    (pow_dvd_pow_of_dvd closed_visible 3).trans denominator_cube_dvd
  have visible_cube_dvd_open_transfer : visibleFactor ^ 3 ∣
      openMatrix.charpolyRev :=
    visible_cube_dvd_open_denominator.trans
      (normalizedTransferDenominator_dvd_charpolyRev
        openMatrix openStart openFinish)
  have visible_cube_not_dvd_open_transfer :
      ¬(visibleFactor ^ 3 ∣ openMatrix.charpolyRev) := by
    apply not_pow_dvd_of_emultiplicity_lt
    rw [open_multiplicity]
    norm_num
  exact visible_cube_not_dvd_open_transfer visible_cube_dvd_open_transfer

end WidthFiveObstruction

end

end KnuthFasc8aEx210
