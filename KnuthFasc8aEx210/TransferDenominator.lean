import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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

/-- A recurrence that is required only after a fixed prefix.  Reduced rational
functions may have a polynomial part, so this is the natural interface for a
canonical denominator. -/
def IsTailForwardRecurrence (M : Matrix n n K) (observe start : n → K)
    (p : K[X]) (threshold : ℕ) : Prop :=
  ∀ k ≥ threshold, ∑ i ∈ Finset.range (p.natDegree + 1),
    p.coeff i * scalarKrylovSequence M observe start (k + i) = 0

/-- A polynomial is an eventual recurrence when some finite prefix may be
discarded. -/
def IsEventuallyForwardRecurrence (M : Matrix n n K)
    (observe start : n → K) (p : K[X]) : Prop :=
  ∃ threshold, IsTailForwardRecurrence M observe start p threshold

/-- Reversal converts the usual denominator convolution into the forward
recurrence convention used for Krylov sequences. -/
theorem reverseRecurrenceSum_eq_denominatorConvolution
    (q : K[X]) (sequence : ℕ → K) (k : ℕ)
    (constant_ne_zero : q.coeff 0 ≠ 0) :
    (∑ i ∈ Finset.range (q.reverse.natDegree + 1),
      q.reverse.coeff i * sequence (k + i)) =
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * sequence (k + q.natDegree - i) := by
  have trailing_zero : q.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero.mpr (Or.inr constant_ne_zero)
  have reverse_degree : q.reverse.natDegree = q.natDegree := by
    rw [reverse_natDegree, trailing_zero, Nat.sub_zero]
  rw [reverse_degree]
  conv_rhs =>
    rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have i_le : i ≤ q.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [coeff_reverse, revAt_le i_le]
  congr 2
  omega

/-- Formal power series of an arbitrary scalar sequence. -/
def sequencePowerSeries (sequence : ℕ → K) : PowerSeries K :=
  PowerSeries.mk sequence

@[simp] theorem sequencePowerSeries_coeff (sequence : ℕ → K) (k : ℕ) :
    PowerSeries.coeff k (sequencePowerSeries sequence) = sequence k := by
  simp [sequencePowerSeries]

/-- A polynomial denominator times the sequence series equals a polynomial
numerator.  This formulation also permits a finite polynomial prefix. -/
def IsRationalSequenceRepresentation (sequence : ℕ → K)
    (numerator denominator : K[X]) : Prop :=
  (denominator : PowerSeries K) * sequencePowerSeries sequence =
    (numerator : PowerSeries K)

/-- Vector of formal Krylov generating series. -/
def krylovVectorPowerSeries (M : Matrix n n K) (start : n → K) :
    n → PowerSeries K :=
  fun i ↦ PowerSeries.mk fun k ↦ (M ^ k *ᵥ start) i

/-- Formal-power-series version of `1-XM`. -/
def transferPowerSeriesMatrix (M : Matrix n n K) :
    Matrix n n (PowerSeries K) :=
  (1 : Matrix n n (PowerSeries K)) -
    (PowerSeries.X : PowerSeries K) • M.map PowerSeries.C

omit [DecidableEq n] in
theorem coeff_map_C_mulVec (M : Matrix n n K)
    (v : n → PowerSeries K) (k : ℕ) (row : n) :
    PowerSeries.coeff k ((M.map PowerSeries.C *ᵥ v) row) =
      (M *ᵥ fun i ↦ PowerSeries.coeff k (v i)) row := by
  simp [Matrix.mulVec, dotProduct, map_sum, PowerSeries.coeff_C_mul]

/-- The Krylov series vector is the formal inverse action of `1-XM` on the
constant startup vector. -/
theorem transferPowerSeriesMatrix_mulVec_krylov
    (M : Matrix n n K) (start : n → K) :
    transferPowerSeriesMatrix M *ᵥ krylovVectorPowerSeries M start =
      fun i ↦ PowerSeries.C (start i) := by
  rw [transferPowerSeriesMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  funext row
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
      simp [krylovVectorPowerSeries, smul_eq_mul]
  | succ k =>
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
        PowerSeries.coeff_succ_C, sub_eq_zero]
      rw [PowerSeries.coeff_succ_X_mul]
      rw [coeff_map_C_mulVec]
      simp only [krylovVectorPowerSeries, PowerSeries.coeff_mk]
      rw [Matrix.mulVec_mulVec, ← pow_succ']

/-- Formal generating series of the observed scalar Krylov sequence. -/
def scalarKrylovPowerSeries (M : Matrix n n K) (observe start : n → K) :
    PowerSeries K :=
  sequencePowerSeries (scalarKrylovSequence M observe start)

theorem scalarKrylovPowerSeries_eq_dotProduct
    (M : Matrix n n K) (observe start : n → K) :
    scalarKrylovPowerSeries M observe start =
      dotProduct (fun i ↦ PowerSeries.C (observe i))
        (krylovVectorPowerSeries M start) := by
  apply PowerSeries.ext
  intro k
  simp [scalarKrylovPowerSeries, scalarKrylovSequence,
    sequencePowerSeries, krylovVectorPowerSeries, dotProduct,
    map_sum, PowerSeries.coeff_C_mul]

omit [Fintype n] in
theorem transferPolynomialMatrix_map_toPowerSeries (M : Matrix n n K) :
    (transferPolynomialMatrix M).map
        Polynomial.coeToPowerSeries.ringHom =
      transferPowerSeriesMatrix M := by
  funext i j
  simp [transferPolynomialMatrix, transferPowerSeriesMatrix,
    Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, Polynomial.coe_C]
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

theorem transferNumerator_toPowerSeries
    (M : Matrix n n K) (start finish : n → K) :
    (transferNumerator M start finish : PowerSeries K) =
      dotProduct (fun i ↦ PowerSeries.C (finish i))
        (((transferPolynomialMatrix M).adjugate.map
          Polynomial.coeToPowerSeries.ringHom) *ᵥ
            (fun i ↦ PowerSeries.C (start i))) := by
  change Polynomial.coeToPowerSeries.ringHom
      (transferNumerator M start finish) = _
  simp [transferNumerator, dotProduct, Matrix.mulVec, map_sum,
    Polynomial.coe_C]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change Polynomial.coeToPowerSeries.ringHom
      (∑ j, (transferPolynomialMatrix M).adjugate i j * C (start j)) = _
  rw [map_sum]
  simp [Polynomial.coe_C]

/-- The adjugate numerator and characteristic power series represent the
observed Krylov generating series. -/
theorem transferNumerator_charpolyRev_representation
    (M : Matrix n n K) (start finish : n → K) :
    IsRationalSequenceRepresentation
      (scalarKrylovSequence M finish start)
      (transferNumerator M start finish) M.charpolyRev := by
  let P := transferPolynomialMatrix M
  let A : Matrix n n (PowerSeries K) :=
    P.adjugate.map Polynomial.coeToPowerSeries.ringHom
  have inverse_equation :
      (P.map Polynomial.coeToPowerSeries.ringHom) *ᵥ
          krylovVectorPowerSeries M start =
        fun i ↦ PowerSeries.C (start i) := by
    rw [transferPolynomialMatrix_map_toPowerSeries]
    exact transferPowerSeriesMatrix_mulVec_krylov M start
  have adjugate_equation := congrArg (fun v ↦ A *ᵥ v) inverse_equation
  rw [Matrix.mulVec_mulVec] at adjugate_equation
  have matrix_product :
      A * P.map Polynomial.coeToPowerSeries.ringHom =
        (M.charpolyRev : PowerSeries K) • 1 := by
    dsimp [A]
    rw [← Matrix.map_mul, Matrix.adjugate_mul,
      transferPolynomialMatrix_det]
    funext i j
    by_cases h : i = j <;>
      simp [h, Polynomial.coeToPowerSeries.ringHom_apply]
  rw [matrix_product, Matrix.smul_mulVec, Matrix.one_mulVec] at adjugate_equation
  have observed_equation := congrArg
    (dotProduct (fun i ↦ PowerSeries.C (finish i))) adjugate_equation
  rw [dotProduct_smul] at observed_equation
  rw [← scalarKrylovPowerSeries_eq_dotProduct] at observed_equation
  rw [← transferNumerator_toPowerSeries] at observed_equation
  exact observed_equation

/-- Cancellation in the rational function descends to formal power series:
the canonical reduced denominator and numerator still represent the Krylov
generating series. -/
theorem transferDenominator_representation
    (M : Matrix n n K) (start finish : n → K) :
    IsRationalSequenceRepresentation
      (scalarKrylovSequence M finish start)
      (RatFunc.num (transferRatFunc M start finish))
      (transferDenominator M start finish) := by
  let x := transferRatFunc M start finish
  let q := transferDenominator M start finish
  let r := RatFunc.num x
  obtain ⟨h, charpoly_factorization⟩ :=
    transferDenominator_dvd_charpolyRev M start finish
  have q_ne : q ≠ 0 := by
    dsimp [q, transferDenominator]
    exact RatFunc.denom_ne_zero _
  have h_ne : h ≠ 0 := by
    intro h_zero
    apply charpolyRev_ne_zero M
    rw [charpoly_factorization, h_zero, mul_zero]
  have rational_equality :
      algebraMap K[X] (RatFunc K) (transferNumerator M start finish) /
          algebraMap K[X] (RatFunc K) M.charpolyRev =
        algebraMap K[X] (RatFunc K) r /
          algebraMap K[X] (RatFunc K) q := by
    calc
      _ = x := by rfl
      _ = _ := (RatFunc.num_div_denom x).symm
  have polynomial_cross_product :
      transferNumerator M start finish * q = r * M.charpolyRev := by
    have mapped_charpoly_ne :
        algebraMap K[X] (RatFunc K) M.charpolyRev ≠ 0 := by
      rw [← map_zero (algebraMap K[X] (RatFunc K))]
      exact (RatFunc.algebraMap_injective K).ne (charpolyRev_ne_zero M)
    have mapped_q_ne : algebraMap K[X] (RatFunc K) q ≠ 0 := by
      rw [← map_zero (algebraMap K[X] (RatFunc K))]
      exact (RatFunc.algebraMap_injective K).ne q_ne
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul] using
      (div_eq_div_iff mapped_charpoly_ne mapped_q_ne).mp
          rational_equality
  have numerator_factorization :
      transferNumerator M start finish = r * h := by
    apply mul_right_cancel₀ q_ne
    calc
      transferNumerator M start finish * q = r * M.charpolyRev :=
        polynomial_cross_product
      _ = (r * h) * q := by rw [charpoly_factorization]; ring
  have full_representation :=
    transferNumerator_charpolyRev_representation M start finish
  rw [charpoly_factorization, numerator_factorization] at full_representation
  change ((q * h : K[X]) : PowerSeries K) *
      scalarKrylovPowerSeries M finish start =
    ((r * h : K[X]) : PowerSeries K) at full_representation
  rw [Polynomial.coe_mul, Polynomial.coe_mul] at full_representation
  have coe_h_ne : (h : PowerSeries K) ≠ 0 := by
    intro coe_zero
    apply h_ne
    apply Polynomial.coe_injective K
    simpa using coe_zero
  have cancellable :
      ((q : PowerSeries K) * scalarKrylovPowerSeries M finish start) *
          (h : PowerSeries K) =
        (r : PowerSeries K) * (h : PowerSeries K) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using full_representation
  have reduced_representation := mul_right_cancel₀ coe_h_ne cancellable
  simpa [IsRationalSequenceRepresentation, scalarKrylovPowerSeries,
    x, q, r] using reduced_representation

/-- Every power-series rational representation supplies an eventual forward
recurrence for the reversed denominator. -/
theorem IsRationalSequenceRepresentation.eventualRecurrence
    (sequence : ℕ → K) (numerator denominator : K[X])
    (representation :
      IsRationalSequenceRepresentation sequence numerator denominator)
    (constant_ne_zero : denominator.coeff 0 ≠ 0) :
    ∃ threshold, ∀ k ≥ threshold,
      ∑ i ∈ Finset.range (denominator.reverse.natDegree + 1),
        denominator.reverse.coeff i * sequence (k + i) = 0 := by
  refine ⟨numerator.natDegree + 1, ?_⟩
  intro k hk
  rw [reverseRecurrenceSum_eq_denominatorConvolution
    denominator sequence k constant_ne_zero]
  let total := k + denominator.natDegree
  have coefficient_identity := congrArg (PowerSeries.coeff total) representation
  have numerator_coefficient_zero : numerator.coeff total = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    dsimp [total]
    omega
  simp only [PowerSeries.coeff_mul, Polynomial.coeff_coe,
    sequencePowerSeries_coeff, numerator_coefficient_zero] at coefficient_identity
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at coefficient_identity
  have range_subset : Finset.range (denominator.natDegree + 1) ⊆
      Finset.range (total + 1) := by
    apply Finset.range_mono
    dsimp [total]
    omega
  have truncate :
      (∑ i ∈ Finset.range (denominator.natDegree + 1),
        denominator.coeff i * sequence (total - i)) =
      ∑ i ∈ Finset.range (total + 1),
        denominator.coeff i * sequence (total - i) := by
    apply Finset.sum_subset range_subset
    intro i i_mem i_not_mem
    have degree_lt_i : denominator.natDegree < i := by
      simp only [Finset.mem_range, Nat.not_lt] at i_not_mem
      omega
    rw [coeff_eq_zero_of_natDegree_lt degree_lt_i, zero_mul]
  rw [truncate, coefficient_identity]

/-- The canonical reduced transfer denominator itself supplies the eventual
recurrence needed by the closed visibility proof. -/
theorem transferDenominator_reverse_isEventuallyForwardRecurrence
    (M : Matrix n n K) (start finish : n → K) :
    IsEventuallyForwardRecurrence M finish start
      (transferDenominator M start finish).reverse := by
  have representation := transferDenominator_representation M start finish
  obtain ⟨threshold, recurrence⟩ :=
    representation.eventualRecurrence
      (scalarKrylovSequence M finish start)
      (RatFunc.num (transferRatFunc M start finish))
      (transferDenominator M start finish)
      (transferDenominator_coeff_zero_ne_zero M start finish)
  exact ⟨threshold, recurrence⟩

theorem IsForwardRecurrence.isEventually
    (M : Matrix n n K) (observe start : n → K) (p : K[X])
    (recurrence : IsForwardRecurrence M observe start p) :
    IsEventuallyForwardRecurrence M observe start p := by
  exact ⟨0, fun k _ ↦ recurrence k⟩

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

/-- Startup vectors satisfying a recurrence after one fixed threshold form a
subspace. -/
def tailRecurrenceStartSubmodule (M : Matrix n n K) (observe : n → K)
    (p : K[X]) (threshold : ℕ) : Submodule K (n → K) where
  carrier := {start | IsTailForwardRecurrence M observe start p threshold}
  zero_mem' := by
    intro k _
    simp
  add_mem' := by
    intro u v hu hv
    change IsTailForwardRecurrence M observe u p threshold at hu
    change IsTailForwardRecurrence M observe v p threshold at hv
    change IsTailForwardRecurrence M observe (u + v) p threshold
    intro k hk
    simp only [scalarKrylovSequence_add, mul_add, Finset.sum_add_distrib,
      hu k hk, hv k hk, add_zero]
  smul_mem' := by
    intro a v hv
    change IsTailForwardRecurrence M observe v p threshold at hv
    change IsTailForwardRecurrence M observe (a • v) p threshold
    intro k hk
    simp only [scalarKrylovSequence_smul]
    simp_rw [← mul_assoc, mul_comm (p.coeff _) a, mul_assoc]
    rw [← Finset.mul_sum, hv k hk, mul_zero]

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

theorem IsTailForwardRecurrence.mulVec_pow
    (M : Matrix n n K) (observe start : n → K) (p : K[X])
    (threshold : ℕ)
    (recurrence : IsTailForwardRecurrence M observe start p threshold)
    (j : ℕ) :
    IsTailForwardRecurrence M observe (M ^ j *ᵥ start) p threshold := by
  intro k hk
  simpa [scalarKrylovSequence_mulVec_pow, add_assoc, add_comm, add_left_comm]
    using recurrence (k + j) (hk.trans (Nat.le_add_right k j))

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

theorem IsTailForwardRecurrence.of_mem_krylovSpan
    (M : Matrix n n K) (observe start v : n → K) (p : K[X])
    (threshold : ℕ)
    (recurrence : IsTailForwardRecurrence M observe start p threshold)
    (v_mem : v ∈ Submodule.span K
      (Set.range fun j : ℕ ↦ M ^ j *ᵥ start)) :
    IsTailForwardRecurrence M observe v p threshold := by
  apply (show v ∈ tailRecurrenceStartSubmodule M observe p threshold from ?_)
  apply (Submodule.span_le.mpr ?_) v_mem
  rintro _ ⟨j, rfl⟩
  exact recurrence.mulVec_pow M observe start p threshold j

theorem IsEventuallyForwardRecurrence.of_mem_krylovSpan
    (M : Matrix n n K) (observe start v : n → K) (p : K[X])
    (recurrence : IsEventuallyForwardRecurrence M observe start p)
    (v_mem : v ∈ Submodule.span K
      (Set.range fun j : ℕ ↦ M ^ j *ᵥ start)) :
    IsEventuallyForwardRecurrence M observe v p := by
  obtain ⟨threshold, recurrence⟩ := recurrence
  exact ⟨threshold, recurrence.of_mem_krylovSpan
    M observe start v p threshold v_mem⟩

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

/-- An observable nonzero eigenvalue is a root even when the recurrence starts
only after a finite prefix. -/
theorem IsEventuallyForwardRecurrence.isRoot_of_eigenvector
    (M : Matrix n n K) (observe v : n → K) (p : K[X]) (a : K)
    (recurrence : IsEventuallyForwardRecurrence M observe v p)
    (eigenvector : M *ᵥ v = a • v)
    (eigenvalue_ne_zero : a ≠ 0)
    (visible : dotProduct observe v ≠ 0) :
    p.IsRoot a := by
  obtain ⟨threshold, recurrence⟩ := recurrence
  have recurrence_at_threshold := recurrence threshold le_rfl
  simp only [scalarKrylovSequence_of_eigenvector M observe v a eigenvector]
    at recurrence_at_threshold
  have product_zero : a ^ threshold *
      (p.eval a * dotProduct observe v) = 0 := by
    rw [Polynomial.eval_eq_sum_range, ← mul_assoc, Finset.mul_sum,
      Finset.sum_mul]
    calc
      ∑ i ∈ Finset.range (p.natDegree + 1),
          a ^ threshold * (p.coeff i * a ^ i) * dotProduct observe v =
          ∑ i ∈ Finset.range (p.natDegree + 1),
            p.coeff i * (a ^ (threshold + i) *
              dotProduct observe v) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [pow_add]
                ring
      _ = 0 := recurrence_at_threshold
  have evaluation_times_visible : p.eval a * dotProduct observe v = 0 :=
    (mul_eq_zero.mp product_zero).resolve_left
      (pow_ne_zero threshold eigenvalue_ne_zero)
  rw [Polynomial.IsRoot.def]
  exact (mul_eq_zero.mp evaluation_times_visible).resolve_right visible

theorem IsTailForwardRecurrence.isRoot_of_eigenvector
    (M : Matrix n n K) (observe v : n → K) (p : K[X]) (a : K)
    (threshold : ℕ)
    (recurrence : IsTailForwardRecurrence M observe v p threshold)
    (eigenvector : M *ᵥ v = a • v)
    (eigenvalue_ne_zero : a ≠ 0)
    (visible : dotProduct observe v ≠ 0) :
    p.IsRoot a := by
  have eventual : IsEventuallyForwardRecurrence M observe v p :=
    ⟨threshold, recurrence⟩
  exact IsEventuallyForwardRecurrence.isRoot_of_eigenvector
    M observe v p a eventual eigenvector eigenvalue_ne_zero visible

/-- A root `50` of the reversed polynomial is precisely the width-five
visible factor of the original polynomial. -/
theorem visibleFactor_dvd_of_reverse_root (q : ModPolynomial)
    (reverse_root : q.reverse.IsRoot (50 : F101)) :
    visibleFactor ∣ q := by
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
  exact visibleFactor_dvd_of_reverse_root q reverse_root

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

/-- Eventual-recurrence version used by a canonical reduced rational-function
denominator; a finite numerator prefix has no effect on visibility. -/
theorem visibleFactor_dvd_of_visibleCandidate_eventual_recurrence
    (M : Matrix n n F101) (observe start : n → F101)
    (g q : ModPolynomial)
    (recurrence : IsEventuallyForwardRecurrence M observe start q.reverse)
    (square_eigenvector :
      let r := evenPolynomialKrylovVector M start g
      M ^ 2 *ᵥ r = (76 : F101) • r)
    (visible :
      let r := evenPolynomialKrylovVector M start g
      dotProduct observe (r + (99 : F101) • (M *ᵥ r)) ≠ 0) :
    visibleFactor ∣ q := by
  let r := evenPolynomialKrylovVector M start g
  let v := r + (99 : F101) • (M *ᵥ r)
  have v_mem : v ∈ Submodule.span F101
      (Set.range fun j : ℕ ↦ M ^ j *ᵥ start) :=
    visibleEigenvectorCandidate_mem_krylovSpan M start g
  have v_recurrence :
      IsEventuallyForwardRecurrence M observe v q.reverse :=
    recurrence.of_mem_krylovSpan M observe start v q.reverse v_mem
  have v_eigenvector : M *ᵥ v = (50 : F101) • v :=
    derived_fifty_eigenvector_of_square_seventySix M r square_eigenvector
  have reverse_root : q.reverse.IsRoot (50 : F101) :=
    v_recurrence.isRoot_of_eigenvector M observe v q.reverse 50
      v_eigenvector (by native_decide) visible
  exact visibleFactor_dvd_of_reverse_root q reverse_root

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
