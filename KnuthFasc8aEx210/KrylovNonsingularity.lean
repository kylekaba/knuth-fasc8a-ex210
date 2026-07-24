import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
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

end

end KnuthFasc8aEx210
