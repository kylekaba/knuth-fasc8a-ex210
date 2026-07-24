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

@[simp] theorem scalarKrylovSequence_zero
    (M : Matrix n n K) (observe : n → K) (k : ℕ) :
    scalarKrylovSequence M observe 0 k = 0 := by
  simp [scalarKrylovSequence]

@[simp] theorem scalarKrylovSequence_add
    (M : Matrix n n K) (observe u v : n → K) (k : ℕ) :
    scalarKrylovSequence M observe (u + v) k =
      scalarKrylovSequence M observe u k +
        scalarKrylovSequence M observe v k := by
  simp [scalarKrylovSequence, Matrix.mulVec_add, dotProduct_add]

@[simp] theorem scalarKrylovSequence_smul
    (M : Matrix n n K) (observe v : n → K) (a : K) (k : ℕ) :
    scalarKrylovSequence M observe (a • v) k =
      a * scalarKrylovSequence M observe v k := by
  simp [scalarKrylovSequence, Matrix.mulVec_smul, dotProduct_smul]

/-- For fixed matrix, observation, and polynomial, the startup vectors whose
scalar sequences satisfy the recurrence form a subspace. -/
def recurrenceStartSubmodule (M : Matrix n n K) (observe : n → K)
    (p : K[X]) : Submodule K (n → K) where
  carrier := {start | IsForwardRecurrence M observe start p}
  zero_mem' := by
    change IsForwardRecurrence M observe 0 p
    intro k
    simp
  add_mem' := by
    intro u v hu hv
    change IsForwardRecurrence M observe u p at hu
    change IsForwardRecurrence M observe v p at hv
    change IsForwardRecurrence M observe (u + v) p
    intro k
    simp only [scalarKrylovSequence_add, mul_add, Finset.sum_add_distrib,
      hu k, hv k, add_zero]
  smul_mem' := by
    intro a v hv
    change IsForwardRecurrence M observe v p at hv
    change IsForwardRecurrence M observe (a • v) p
    intro k
    simp only [scalarKrylovSequence_smul]
    simp_rw [← mul_assoc, mul_comm (p.coeff _) a, mul_assoc]
    rw [← Finset.mul_sum, hv k, mul_zero]

theorem scalarKrylovSequence_mulVec_pow
    (M : Matrix n n K) (observe start : n → K) (j k : ℕ) :
    scalarKrylovSequence M observe (M ^ j *ᵥ start) k =
      scalarKrylovSequence M observe start (k + j) := by
  unfold scalarKrylovSequence
  rw [mulVec_mulVec, ← pow_add]

/-- A recurrence remains valid after shifting the startup vector forward
along its matrix orbit. -/
theorem IsForwardRecurrence.mulVec_pow
    (M : Matrix n n K) (observe start : n → K) (p : K[X])
    (recurrence : IsForwardRecurrence M observe start p) (j : ℕ) :
    IsForwardRecurrence M observe (M ^ j *ᵥ start) p := by
  intro k
  simpa [scalarKrylovSequence_mulVec_pow, add_assoc, add_comm, add_left_comm]
    using recurrence (k + j)

/-- Every vector in the Krylov span of a startup vector inherits all forward
recurrences of its observed scalar sequence. -/
theorem IsForwardRecurrence.of_mem_krylovSpan
    (M : Matrix n n K) (observe start v : n → K) (p : K[X])
    (recurrence : IsForwardRecurrence M observe start p)
    (v_mem : v ∈ Submodule.span K
      (Set.range fun j : ℕ ↦ M ^ j *ᵥ start)) :
    IsForwardRecurrence M observe v p := by
  apply (show v ∈ recurrenceStartSubmodule M observe p from ?_)
  apply (Submodule.span_le.mpr ?_) v_mem
  rintro _ ⟨j, rfl⟩
  exact recurrence.mulVec_pow M observe start p j

/-- The Krylov span is invariant under one further application of its
matrix. -/
theorem mulVec_mem_krylovSpan
    (M : Matrix n n K) (start v : n → K)
    (v_mem : v ∈ Submodule.span K
      (Set.range fun j : ℕ ↦ M ^ j *ᵥ start)) :
    M *ᵥ v ∈ Submodule.span K
      (Set.range fun j : ℕ ↦ M ^ j *ᵥ start) := by
  induction v_mem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      simpa [pow_succ', mulVec_mulVec] using
        (Submodule.subset_span
          (s := Set.range fun j : ℕ ↦ M ^ j *ᵥ start)
          (Set.mem_range_self (j + 1)))
  | zero => simp
  | add x y _ _ hx hy =>
      simpa [Matrix.mulVec_add] using
        (Submodule.add_mem _ hx hy)
  | smul a x _ hx =>
      simpa [Matrix.mulVec_smul] using
        (Submodule.smul_mem _ a hx)

/-- The concrete polynomial-in-`M²` vector used by the visible-factor
certificate, written independently of the executable Horner evaluator. -/
def evenPolynomialKrylovVector
    (M : Matrix n n K) (start : n → K) (g : K[X]) : n → K :=
  ∑ i ∈ Finset.range (g.natDegree + 1),
    g.coeff i • (M ^ (2 * i) *ᵥ start)

theorem evenPolynomialKrylovVector_mem_krylovSpan
    (M : Matrix n n K) (start : n → K) (g : K[X]) :
    evenPolynomialKrylovVector M start g ∈ Submodule.span K
      (Set.range fun j : ℕ ↦ M ^ j *ᵥ start) := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self (2 * i))

/-- The vector `r + 99 M r` constructed by the width-five visible-factor
certificate lies in the startup Krylov span. -/
theorem visibleEigenvectorCandidate_mem_krylovSpan
    (M : Matrix n n F101) (start : n → F101) (g : ModPolynomial) :
    let r := evenPolynomialKrylovVector M start g
    r + (99 : F101) • (M *ᵥ r) ∈ Submodule.span F101
      (Set.range fun j : ℕ ↦ M ^ j *ᵥ start) := by
  dsimp
  apply Submodule.add_mem
  · exact evenPolynomialKrylovVector_mem_krylovSpan M start g
  · apply Submodule.smul_mem
    exact mulVec_mem_krylovSpan M start _
      (evenPolynomialKrylovVector_mem_krylovSpan M start g)

/-- The `76 = 50²` square-eigenvector check implies the derived vector is
a `50`-eigenvector; this makes the second executable residual check
mathematically redundant. -/
theorem derived_fifty_eigenvector_of_square_seventySix
    (M : Matrix n n F101) (r : n → F101)
    (square_eigenvector : M ^ 2 *ᵥ r = (76 : F101) • r) :
    M *ᵥ (r + (99 : F101) • (M *ᵥ r)) =
      (50 : F101) • (r + (99 : F101) • (M *ᵥ r)) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, mulVec_mulVec]
  rw [← pow_two]
  rw [square_eigenvector]
  ext i
  change (M *ᵥ r) i + 99 * (76 * r i) =
    50 * (r i + 99 * (M *ᵥ r) i)
  have h₁ : (99 : F101) * 76 = 50 := by native_decide
  have h₂ : (50 : F101) * 99 = 1 := by native_decide
  rw [← mul_assoc, h₁, mul_add, ← mul_assoc, h₂, one_mul]
  ring

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

/-- Closed-side visibility in the form used by the certificate: it is enough
for the visible eigenvector to lie in the startup vector's Krylov span. -/
theorem visibleFactor_dvd_of_reverse_recurrence_of_mem_krylovSpan
    (M : Matrix n n F101) (observe start v : n → F101)
    (q : ModPolynomial)
    (recurrence : IsForwardRecurrence M observe start q.reverse)
    (v_mem : v ∈ Submodule.span F101
      (Set.range fun j : ℕ ↦ M ^ j *ᵥ start))
    (eigenvector : M *ᵥ v = (50 : F101) • v)
    (visible : dotProduct observe v ≠ 0) :
    visibleFactor ∣ q := by
  apply visibleFactor_dvd_of_reverse_recurrence_eigenvector
    M observe v q
  · exact recurrence.of_mem_krylovSpan M observe start v q.reverse v_mem
  · exact eigenvector
  · exact visible

/-- The closed visibility theorem specialized to the exact vector formula
replayed by `visibleFactorFullCheck`. -/
theorem visibleFactor_dvd_of_visibleEigenvectorCandidate
    (M : Matrix n n F101) (observe start : n → F101)
    (g q : ModPolynomial)
    (recurrence : IsForwardRecurrence M observe start q.reverse)
    (eigenvector :
      let r := evenPolynomialKrylovVector M start g
      M *ᵥ (r + (99 : F101) • (M *ᵥ r)) =
        (50 : F101) • (r + (99 : F101) • (M *ᵥ r)))
    (visible :
      let r := evenPolynomialKrylovVector M start g
      dotProduct observe (r + (99 : F101) • (M *ᵥ r)) ≠ 0) :
    visibleFactor ∣ q := by
  let r := evenPolynomialKrylovVector M start g
  apply visibleFactor_dvd_of_reverse_recurrence_of_mem_krylovSpan
    M observe start (r + (99 : F101) • (M *ᵥ r)) q recurrence
  · exact visibleEigenvectorCandidate_mem_krylovSpan M start g
  · exact eigenvector
  · exact visible

/-- Strongest closed visibility interface: the certificate need only expose
its polynomial-in-`M²` vector, the checked `76` residual, and a nonzero
observable coordinate. -/
theorem visibleFactor_dvd_of_visibleCandidate_square_eigenvector
    (M : Matrix n n F101) (observe start : n → F101)
    (g q : ModPolynomial)
    (recurrence : IsForwardRecurrence M observe start q.reverse)
    (square_eigenvector :
      let r := evenPolynomialKrylovVector M start g
      M ^ 2 *ᵥ r = (76 : F101) • r)
    (visible :
      let r := evenPolynomialKrylovVector M start g
      dotProduct observe (r + (99 : F101) • (M *ᵥ r)) ≠ 0) :
    visibleFactor ∣ q := by
  apply visibleFactor_dvd_of_visibleEigenvectorCandidate
    M observe start g q recurrence
  · exact derived_fifty_eigenvector_of_square_seventySix M _ square_eigenvector
  · exact visible

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
