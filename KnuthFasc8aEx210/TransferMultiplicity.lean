import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import KnuthFasc8aEx210.CertificateMatrixSoundness

/-!
# Transfer-block multiplicity assembly

This file assembles the six reflection-block characteristic-polynomial facts
certified by the rank certificates.  The two copies of `Trel` account for the
closed and terminal-coreachable sectors of the open transfer.
-/

namespace KnuthFasc8aEx210

open Polynomial

noncomputable section

/-- Reversing a nonzero polynomial sends a nonzero root to its reciprocal,
without changing its multiplicity.  This is the algebraic bridge from a
transfer-matrix eigenvalue to the corresponding characteristic-power-series
factor. -/
theorem rootMultiplicity_reverse_inv
    {K : Type*} [Field K] (p : K[X]) (a : K) (p_ne : p ≠ 0) (a_ne : a ≠ 0) :
    p.reverse.rootMultiplicity a⁻¹ = p.rootMultiplicity a := by
  letI : Invertible a := invertibleOfNonzero a_ne
  obtain ⟨q, p_eq, factor_not_dvd⟩ :=
    p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p_ne a
  have q_ne : q ≠ 0 := by
    intro q_eq
    apply p_ne
    rw [p_eq, q_eq, mul_zero]
  have reverse_q_ne : q.reverse ≠ 0 := by
    simpa using q_ne
  have q_not_root : ¬q.IsRoot a := by
    intro q_root
    exact factor_not_dvd (dvd_iff_isRoot.mpr q_root)
  have reverse_q_not_root : ¬q.reverse.IsRoot a⁻¹ := by
    intro reverse_q_root
    apply q_not_root
    change eval₂ (RingHom.id K) a⁻¹ q.reverse = 0 at reverse_q_root
    change eval₂ (RingHom.id K) a q = 0
    exact (eval₂_reverse_eq_zero_iff (RingHom.id K) a q).mp (by
      simpa [invOf_eq_inv] using reverse_q_root)
  have reverse_factor :
      (X - C a).reverse = C (-a) * (X - C a⁻¹) := by
    rw [reverse, natDegree_X_sub_C]
    simp [reflect_sub]
    simp only [mul_sub, ← C_mul, mul_inv_cancel₀ a_ne, C_1]
    ring
  have reverse_power : ∀ n : ℕ,
      ((X - C a) ^ n).reverse = ((X - C a).reverse) ^ n := by
    intro n
    induction n with
    | zero => simpa using reverse_C (1 : K)
    | succ n ih => rw [pow_succ, reverse_mul_of_domain, ih, pow_succ]
  rw [p_eq, reverse_mul_of_domain, reverse_power, reverse_factor, mul_pow,
    rootMultiplicity_mul]
  · rw [rootMultiplicity_mul]
    · rw [rootMultiplicity_mul]
      · simp [rootMultiplicity_X_sub_C_pow,
          rootMultiplicity_eq_zero reverse_q_not_root,
          rootMultiplicity_eq_zero q_not_root]
      · exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero a)) q_ne
    · exact mul_ne_zero (pow_ne_zero _ (C_ne_zero.mpr (neg_ne_zero.mpr a_ne)))
        (pow_ne_zero _ (X_sub_C_ne_zero a⁻¹))
  · exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (C_ne_zero.mpr (neg_ne_zero.mpr a_ne)))
        (pow_ne_zero _ (X_sub_C_ne_zero a⁻¹))) reverse_q_ne

private theorem rootMultiplicity_list_prod
    (mu : CertificateField) : ∀ polynomials : List CertificateField[X],
    (∀ p ∈ polynomials, p ≠ 0) →
      rootMultiplicity mu polynomials.prod =
        (polynomials.map (rootMultiplicity mu)).sum
  | [], _ => by simp
  | p :: ps, nonzero => by
      have p_ne : p ≠ 0 := nonzero p (by simp)
      have ps_nonzero : ∀ q ∈ ps, q ≠ 0 := by
        intro q q_mem
        exact nonzero q (by simp [q_mem])
      have prod_ne : ps.prod ≠ 0 := List.prod_ne_zero (by
        intro zero_mem
        exact ps_nonzero 0 zero_mem rfl)
      rw [List.prod_cons, rootMultiplicity_mul (mul_ne_zero p_ne prod_ne),
        rootMultiplicity_list_prod mu ps ps_nonzero]
      simp

/-- Product of the six nontrivial reflection blocks, with `Trel` repeated for
the permutation-similar `Wrel` sector. -/
def certifiedOpenBlockCharpolyProduct
    {nTp nTm nU1p nU1m nU2p nU2m : ℕ}
    (tPlus : Module.End CertificateField (Fin nTp → CertificateField))
    (tMinus : Module.End CertificateField (Fin nTm → CertificateField))
    (u1Plus : Module.End CertificateField (Fin nU1p → CertificateField))
    (u1Minus : Module.End CertificateField (Fin nU1m → CertificateField))
    (u2Plus : Module.End CertificateField (Fin nU2p → CertificateField))
    (u2Minus : Module.End CertificateField (Fin nU2m → CertificateField)) :
    CertificateField[X] :=
  [tPlus.charpoly, tMinus.charpoly, u1Plus.charpoly, u1Minus.charpoly,
    u2Plus.charpoly, u2Minus.charpoly, tPlus.charpoly].prod

/-- The characteristic power-series polynomial corresponding to the
certified block product.  For a matrix this reversal is `det (1 - X M)`. -/
def certifiedOpenBlockPowerSeriesProduct
    {nTp nTm nU1p nU1m nU2p nU2m : ℕ}
    (tPlus : Module.End CertificateField (Fin nTp → CertificateField))
    (tMinus : Module.End CertificateField (Fin nTm → CertificateField))
    (u1Plus : Module.End CertificateField (Fin nU1p → CertificateField))
    (u1Minus : Module.End CertificateField (Fin nU1m → CertificateField))
    (u2Plus : Module.End CertificateField (Fin nU2p → CertificateField))
    (u2Minus : Module.End CertificateField (Fin nU2m → CertificateField)) :
    CertificateField[X] :=
  (certifiedOpenBlockCharpolyProduct tPlus tMinus u1Plus u1Minus u2Plus
    u2Minus).reverse

/-- The six certificate conclusions assemble to total characteristic-root
multiplicity `1 + 0 + 0 + 0 + 0 + 0 + 1 = 2`. -/
theorem certifiedOpenBlockCharpolyProduct_rootMultiplicity_fifty_eq_two
    {nTp nTm nU1p nU1m nU2p nU2m : ℕ}
    (tPlus : Module.End CertificateField (Fin nTp → CertificateField))
    (tMinus : Module.End CertificateField (Fin nTm → CertificateField))
    (u1Plus : Module.End CertificateField (Fin nU1p → CertificateField))
    (u1Minus : Module.End CertificateField (Fin nU1m → CertificateField))
    (u2Plus : Module.End CertificateField (Fin nU2p → CertificateField))
    (u2Minus : Module.End CertificateField (Fin nU2m → CertificateField))
    (tPlus_one : tPlus.charpoly.rootMultiplicity (50 : CertificateField) = 1)
    (tMinus_zero : tMinus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u1Plus_zero : u1Plus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u1Minus_zero : u1Minus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u2Plus_zero : u2Plus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u2Minus_zero : u2Minus.charpoly.rootMultiplicity (50 : CertificateField) = 0) :
    (certifiedOpenBlockCharpolyProduct tPlus tMinus u1Plus u1Minus u2Plus
      u2Minus).rootMultiplicity (50 : CertificateField) = 2 := by
  rw [certifiedOpenBlockCharpolyProduct,
    rootMultiplicity_list_prod (50 : CertificateField)]
  · simp [tPlus_one, tMinus_zero, u1Plus_zero, u1Minus_zero, u2Plus_zero,
      u2Minus_zero]
  · intro p p_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at p_mem
    rcases p_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (LinearMap.charpoly_monic _).ne_zero

/-- On the characteristic-power-series side, the reciprocal of `50` has
exactly the same multiplicity two certified by the six block checks. -/
theorem certifiedOpenBlockPowerSeriesProduct_rootMultiplicity_inv_fifty_eq_two
    {nTp nTm nU1p nU1m nU2p nU2m : ℕ}
    (tPlus : Module.End CertificateField (Fin nTp → CertificateField))
    (tMinus : Module.End CertificateField (Fin nTm → CertificateField))
    (u1Plus : Module.End CertificateField (Fin nU1p → CertificateField))
    (u1Minus : Module.End CertificateField (Fin nU1m → CertificateField))
    (u2Plus : Module.End CertificateField (Fin nU2p → CertificateField))
    (u2Minus : Module.End CertificateField (Fin nU2m → CertificateField))
    (tPlus_one : tPlus.charpoly.rootMultiplicity (50 : CertificateField) = 1)
    (tMinus_zero : tMinus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u1Plus_zero : u1Plus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u1Minus_zero : u1Minus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u2Plus_zero : u2Plus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u2Minus_zero : u2Minus.charpoly.rootMultiplicity (50 : CertificateField) = 0) :
    (certifiedOpenBlockPowerSeriesProduct tPlus tMinus u1Plus u1Minus u2Plus
      u2Minus).rootMultiplicity (50 : CertificateField)⁻¹ = 2 := by
  rw [certifiedOpenBlockPowerSeriesProduct,
    rootMultiplicity_reverse_inv _ (50 : CertificateField)]
  · exact certifiedOpenBlockCharpolyProduct_rootMultiplicity_fifty_eq_two
      tPlus tMinus u1Plus u1Minus u2Plus u2Minus tPlus_one tMinus_zero
      u1Plus_zero u1Minus_zero u2Plus_zero u2Minus_zero
  · exact List.prod_ne_zero (by
      intro zero_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at zero_mem
      rcases zero_mem with h | h | h | h | h | h | h <;>
        exact (LinearMap.charpoly_monic _).ne_zero h.symm)
  · change algebraMap (ZMod 101) CertificateField (50 : ZMod 101) ≠ 0
    intro h
    have h_base : (50 : ZMod 101) = 0 :=
      (algebraMap (ZMod 101) CertificateField).injective (by simpa using h)
    have h_base_ne : (50 : ZMod 101) ≠ 0 := by native_decide
    exact h_base_ne h_base

end

end KnuthFasc8aEx210
