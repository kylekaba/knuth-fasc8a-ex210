import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# From a scalar Krylov recurrence to nonsingularity

The rank certificates use scalar moments `u (A^k w)`.  Berlekamp--Massey
returns a monic recurrence polynomial of degree equal to the dimension.  This
file isolates the algebraic fact needed by the certificate proof: if the
finite moment prefix admits no nonzero recurrence of smaller degree, then the
full-degree recurrence polynomial is the minimal polynomial of `A`.  A
nonzero constant coefficient therefore makes `A` injective.

The executable verifier still has to prove that its concrete BM replay has
the stated minimality property; that computational-correctness layer is kept
separate from this theorem.
-/

namespace KnuthFasc8aEx210

open Module Polynomial

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

local instance : DecidableEq K := Classical.decEq K

/-- The scalar moment sequence used by a Wiedemann certificate. -/
def scalarKrylovMoment (u : V →ₗ[K] K) (A : Module.End K V) (w : V)
    (k : ℕ) : K :=
  u ((A ^ k) w)

/-- `p` annihilates the first `shifts` scalar Krylov tests. -/
def AnnihilatesMomentPrefix (u : V →ₗ[K] K) (A : Module.End K V) (w : V)
    (shifts : ℕ) (p : K[X]) : Prop :=
  ∀ k < shifts, u ((A ^ k) ((aeval A p) w)) = 0

/-- No nonzero polynomial of degree below `degree` annihilates the tested
moment prefix.  This is the mathematical postcondition required from the
Berlekamp--Massey replay. -/
def HasScalarKrylovDegree (u : V →ₗ[K] K) (A : Module.End K V) (w : V)
    (shifts degree : ℕ) : Prop :=
  ∀ p : K[X], AnnihilatesMomentPrefix u A w shifts p → p ≠ 0 →
    degree ≤ p.natDegree

/-- Pure sequence form of the lower-bound postcondition expected from
Berlekamp--Massey: no nonzero polynomial of degree below `degree` satisfies
all `shifts` tested recurrence positions. -/
def HasMomentLinearComplexity (moment : ℕ → K) (shifts degree : ℕ) : Prop :=
  ∀ p : K[X],
    (∀ k < shifts,
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * moment (k + i) = 0) →
    p ≠ 0 → degree ≤ p.natDegree

/-- Evaluating a polynomial at the Krylov operator is exactly the usual
linear recurrence on the scalar moments.  In particular, polynomial
coefficient `i` multiplies moment `k + i`; certificate formats that store
coefficients in descending order must reverse their array when constructing
the polynomial. -/
theorem scalarKrylovMoment_aeval_eq_sum
    (u : V →ₗ[K] K) (A : Module.End K V) (w : V) (k : ℕ) (p : K[X]) :
    u ((A ^ k) ((aeval A p) w)) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        p.coeff i * scalarKrylovMoment u A w (k + i) := by
  rw [aeval_eq_sum_range]
  simp [scalarKrylovMoment, pow_add, Module.End.mul_apply]

theorem annihilatesMomentPrefix_iff_moment_recurrence
    (u : V →ₗ[K] K) (A : Module.End K V) (w : V) (shifts : ℕ) (p : K[X]) :
    AnnihilatesMomentPrefix u A w shifts p ↔
      ∀ k < shifts,
        ∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * scalarKrylovMoment u A w (k + i) = 0 := by
  constructor <;> intro h k hk
  · rw [← scalarKrylovMoment_aeval_eq_sum]
    exact h k hk
  · rw [scalarKrylovMoment_aeval_eq_sum]
    exact h k hk

/-- Once certificate moments have been identified with actual Krylov moments,
the sequence-only BM postcondition is exactly `HasScalarKrylovDegree`. -/
theorem hasMomentLinearComplexity_krylov_iff
    (u : V →ₗ[K] K) (A : Module.End K V) (w : V) (shifts degree : ℕ) :
    HasMomentLinearComplexity (scalarKrylovMoment u A w) shifts degree ↔
      HasScalarKrylovDegree u A w shifts degree := by
  constructor
  · intro complexity p recurrence p_ne_zero
    apply complexity p _ p_ne_zero
    exact (annihilatesMomentPrefix_iff_moment_recurrence
      u A w shifts p).mp recurrence
  · intro krylovDegree p recurrence p_ne_zero
    apply krylovDegree p _ p_ne_zero
    exact (annihilatesMomentPrefix_iff_moment_recurrence
      u A w shifts p).mpr recurrence

/-- Convert the certificate's descending coefficient array
`[1, c₁, ..., c_degree]` into the polynomial
`X^degree + c₁ X^(degree-1) + ... + c_degree`.

The function is deliberately defined using ascending polynomial powers: array
entry `j` becomes polynomial coefficient `degree - j`. -/
def descendingConnectionPolynomial (degree : ℕ) (coefficient : ℕ → K) : K[X] :=
  ofFn (degree + 1) fun i => coefficient (degree - i)

theorem descendingConnectionPolynomial_coeff
    (degree : ℕ) (coefficient : ℕ → K) {i : ℕ} (i_le : i ≤ degree) :
    (descendingConnectionPolynomial degree coefficient).coeff i =
      coefficient (degree - i) := by
  simp [descendingConnectionPolynomial, Nat.lt_succ_of_le i_le]

theorem descendingConnectionPolynomial_isMonicOfDegree
    (degree : ℕ) (coefficient : ℕ → K) (leading : coefficient 0 = 1) :
    IsMonicOfDegree (descendingConnectionPolynomial degree coefficient) degree := by
  rw [isMonicOfDegree_iff]
  constructor
  · exact Nat.lt_succ_iff.mp
      (ofFn_natDegree_lt (Nat.succ_le_succ (Nat.zero_le degree)) _)
  · rw [descendingConnectionPolynomial_coeff degree coefficient (le_refl degree)]
    simpa using leading

theorem descendingConnectionPolynomial_constantCoeff
    (degree : ℕ) (coefficient : ℕ → K) :
    (descendingConnectionPolynomial degree coefficient).coeff 0 = coefficient degree := by
  simpa using descendingConnectionPolynomial_coeff degree coefficient (Nat.zero_le degree)

/-- The exact finite recurrence represented by the descending coefficient
array.  The index `i` on the right is the polynomial power, so it reads the
certificate array at `degree - i`. -/
theorem descendingConnectionPolynomial_annihilates_iff
    (u : V →ₗ[K] K) (A : Module.End K V) (w : V) (shifts degree : ℕ)
    (coefficient : ℕ → K) (leading : coefficient 0 = 1) :
    AnnihilatesMomentPrefix u A w shifts
        (descendingConnectionPolynomial degree coefficient) ↔
      ∀ k < shifts,
        ∑ i ∈ Finset.range (degree + 1),
          coefficient (degree - i) * scalarKrylovMoment u A w (k + i) = 0 := by
  rw [annihilatesMomentPrefix_iff_moment_recurrence]
  have monic := descendingConnectionPolynomial_isMonicOfDegree
    degree coefficient leading
  simp_rw [monic.natDegree_eq]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro _
  have sums_equal :
      (∑ i ∈ Finset.range (degree + 1),
          (descendingConnectionPolynomial degree coefficient).coeff i *
            scalarKrylovMoment u A w (k + i)) =
        ∑ i ∈ Finset.range (degree + 1),
          coefficient (degree - i) * scalarKrylovMoment u A w (k + i) := by
    apply Finset.sum_congr rfl
    intro i i_mem
    rw [descendingConnectionPolynomial_coeff degree coefficient]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp i_mem)
  rw [sums_equal]

theorem annihilatesMomentPrefix_sub
    {u : V →ₗ[K] K} {A : Module.End K V} {w : V} {shifts : ℕ} {p q : K[X]}
    (hp : AnnihilatesMomentPrefix u A w shifts p)
    (hq : AnnihilatesMomentPrefix u A w shifts q) :
    AnnihilatesMomentPrefix u A w shifts (p - q) := by
  intro k hk
  rw [map_sub]
  change u ((A ^ k) ((aeval A p) w - (aeval A q) w)) = 0
  rw [map_sub, map_sub, hp k hk, hq k hk, sub_zero]

theorem minpoly_annihilatesMomentPrefix
    (u : V →ₗ[K] K) (A : Module.End K V) (w : V) (shifts : ℕ) :
    AnnihilatesMomentPrefix u A w shifts (minpoly K A) := by
  intro k _
  rw [minpoly.aeval K A]
  simp

/-- Scalar Krylov degree equal to the vector-space dimension forces the
minimal polynomial to have that full degree. -/
theorem minpoly_natDegree_eq_of_scalarKrylovDegree
    [FiniteDimensional K V]
    (u : V →ₗ[K] K) (A : Module.End K V) (w : V) (shifts degree : ℕ)
    (dimension : finrank K V = degree)
    (fullDegree : HasScalarKrylovDegree u A w shifts degree) :
    (minpoly K A).natDegree = degree := by
  apply Nat.le_antisymm
  · rw [← dimension, ← A.charpoly_natDegree]
    exact natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly A)
      A.charpoly_monic.ne_zero
  · exact fullDegree (minpoly K A)
      (minpoly_annihilatesMomentPrefix u A w shifts)
      (minpoly.ne_zero (LinearMap.isIntegral A))

/-- Under the full-degree scalar Krylov condition, any monic recurrence of
that degree is the minimal polynomial. -/
theorem recurrence_eq_minpoly_of_scalarKrylovDegree
    [FiniteDimensional K V]
    (u : V →ₗ[K] K) (A : Module.End K V) (w : V) (shifts degree : ℕ)
    (degree_ne_zero : degree ≠ 0)
    (dimension : finrank K V = degree)
    (fullDegree : HasScalarKrylovDegree u A w shifts degree)
    (p : K[X]) (p_monic : IsMonicOfDegree p degree)
    (p_recurrence : AnnihilatesMomentPrefix u A w shifts p) :
    p = minpoly K A := by
  have minpoly_degree : (minpoly K A).natDegree = degree :=
    minpoly_natDegree_eq_of_scalarKrylovDegree u A w shifts degree
      dimension fullDegree
  have minpoly_monic : IsMonicOfDegree (minpoly K A) degree :=
    ⟨minpoly_degree, minpoly.monic (LinearMap.isIntegral A)⟩
  have difference_recurrence :
      AnnihilatesMomentPrefix u A w shifts (p - minpoly K A) :=
    annihilatesMomentPrefix_sub p_recurrence
      (minpoly_annihilatesMomentPrefix u A w shifts)
  have difference_zero : p - minpoly K A = 0 := by
    by_contra difference_ne_zero
    have degree_lower := fullDegree (p - minpoly K A)
      difference_recurrence difference_ne_zero
    have degree_upper := p_monic.natDegree_sub_lt degree_ne_zero minpoly_monic
    exact (Nat.not_le_of_lt degree_upper) degree_lower
  exact sub_eq_zero.mp difference_zero

/-- A nonzero constant coefficient of the minimal polynomial rules out a
kernel vector. -/
theorem injective_of_minpoly_coeff_zero_ne_zero
    (A : Module.End K V) (constant_ne_zero : (minpoly K A).coeff 0 ≠ 0) :
    Function.Injective A := by
  have kernel_zero : ∀ x : V, A x = 0 → x = 0 := by
    intro x Ax
    have annihilated : (aeval A (minpoly K A)) x = 0 := by
      rw [minpoly.aeval K A]
      rfl
    have eigen_at_zero : A x = (0 : K) • x := by simpa using Ax
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul eigen_at_zero,
      ← coeff_zero_eq_eval_zero] at annihilated
    exact (smul_eq_zero.mp annihilated).resolve_left constant_ne_zero
  intro x y same_image
  apply sub_eq_zero.mp
  apply kernel_zero (x - y)
  rw [map_sub, same_image, sub_self]

/-- The certificate-facing bridge: a monic full-dimensional scalar recurrence
with nonzero constant coefficient certifies that the endomorphism is
injective (and hence nonsingular in finite dimension). -/
theorem injective_of_fullDegree_scalarKrylov_recurrence
    [FiniteDimensional K V]
    (u : V →ₗ[K] K) (A : Module.End K V) (w : V) (shifts degree : ℕ)
    (degree_ne_zero : degree ≠ 0)
    (dimension : finrank K V = degree)
    (fullDegree : HasScalarKrylovDegree u A w shifts degree)
    (p : K[X]) (p_monic : IsMonicOfDegree p degree)
    (p_recurrence : AnnihilatesMomentPrefix u A w shifts p)
    (constant_ne_zero : p.coeff 0 ≠ 0) :
    Function.Injective A := by
  have p_eq : p = minpoly K A :=
    recurrence_eq_minpoly_of_scalarKrylovDegree u A w shifts degree
      degree_ne_zero dimension fullDegree p p_monic p_recurrence
  apply injective_of_minpoly_coeff_zero_ne_zero A
  rwa [← p_eq]

/-- Array-oriented form of the certificate bridge.  It consumes the same
descending coefficient convention as `KMW2CERT`: entry zero is the monic
leading coefficient and entry `degree` is the nonzero constant coefficient. -/
theorem injective_of_fullDegree_descendingConnection
    [FiniteDimensional K V]
    (u : V →ₗ[K] K) (A : Module.End K V) (w : V) (shifts degree : ℕ)
    (degree_ne_zero : degree ≠ 0)
    (dimension : finrank K V = degree)
    (fullDegree : HasScalarKrylovDegree u A w shifts degree)
    (coefficient : ℕ → K) (leading : coefficient 0 = 1)
    (recurrence : ∀ k < shifts,
      ∑ i ∈ Finset.range (degree + 1),
        coefficient (degree - i) * scalarKrylovMoment u A w (k + i) = 0)
    (constant_ne_zero : coefficient degree ≠ 0) :
    Function.Injective A := by
  let p := descendingConnectionPolynomial degree coefficient
  apply injective_of_fullDegree_scalarKrylov_recurrence
    u A w shifts degree degree_ne_zero dimension fullDegree p
  · exact descendingConnectionPolynomial_isMonicOfDegree degree coefficient leading
  · exact (descendingConnectionPolynomial_annihilates_iff
      u A w shifts degree coefficient leading).mpr recurrence
  · simpa [p, descendingConnectionPolynomial_constantCoeff]

end

end KnuthFasc8aEx210
