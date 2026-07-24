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

end

end KnuthFasc8aEx210
