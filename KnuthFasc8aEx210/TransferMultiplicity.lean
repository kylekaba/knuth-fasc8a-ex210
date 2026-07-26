import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import KnuthFasc8aEx210.CertificateMatrixSoundness
import KnuthFasc8aEx210.Counterexample

/-!
# Transfer-block multiplicity assembly

This file assembles the six reflection-block characteristic-polynomial facts
certified by the rank certificates.  The two copies of `Trel` account for the
closed and terminal-coreachable sectors of the open transfer.
-/

namespace KnuthFasc8aEx210

open Polynomial

noncomputable section

private theorem certificateField_fifty_ne_zero :
    (50 : CertificateField) ≠ 0 := by
  change algebraMap (ZMod 101) CertificateField (50 : ZMod 101) ≠ 0
  intro h
  have h_base : (50 : ZMod 101) = 0 :=
    (algebraMap (ZMod 101) CertificateField).injective (by simpa using h)
  have h_base_ne : (50 : ZMod 101) ≠ 0 := by native_decide
  exact h_base_ne h_base

private theorem certificateField_ninetyNine_eq_inv_fifty :
    algebraMap (ZMod 101) CertificateField (99 : ZMod 101) =
      (50 : CertificateField)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change algebraMap (ZMod 101) CertificateField (99 : ZMod 101) *
      algebraMap (ZMod 101) CertificateField (50 : ZMod 101) = 1
  rw [← map_mul]
  have h : (99 : ZMod 101) * 50 = 1 := by native_decide
  rw [h, map_one]

/-- The concrete factor `1 - 50X` measures root multiplicity at `99` over
`F₁₀₁`. -/
theorem visibleFactor_emultiplicity_eq_rootMultiplicity
    (p : ModPolynomial) (p_ne : p ≠ 0) :
    emultiplicity visibleFactor p = p.rootMultiplicity (99 : F101) := by
  have scalar_unit : IsUnit (C (-50 : F101)) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    native_decide
  have factor_associated : Associated visibleFactor (X - C (99 : F101)) := by
    rw [visibleFactor_eq_unit_mul_X_sub_C]
    exact associated_unit_mul_left _ _ scalar_unit
  rw [← emultiplicity_eq_of_associated_left factor_associated]
  rw [(finiteMultiplicity_X_sub_C (99 : F101) p_ne).emultiplicity_eq_multiplicity]
  rw [rootMultiplicity_eq_multiplicity, if_neg p_ne]

theorem visibleFactor_prime : Prime visibleFactor := by
  have scalar_unit : IsUnit (C (-50 : F101)) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    native_decide
  have factor_associated : Associated visibleFactor (X - C (99 : F101)) := by
    rw [visibleFactor_eq_unit_mul_X_sub_C]
    exact associated_unit_mul_left _ _ scalar_unit
  exact factor_associated.symm.prime (prime_X_sub_C (99 : F101))

/-- Root multiplicity of a base-field polynomial is unchanged by the
injective coefficient embedding into the certificate field. -/
theorem rootMultiplicity_map_certificateField (p : ModPolynomial) (a : F101) :
    (p.map (algebraMap F101 CertificateField)).rootMultiplicity
        (algebraMap F101 CertificateField a) =
      p.rootMultiplicity a := by
  exact (eq_rootMultiplicity_map
    (algebraMap F101 CertificateField).injective a).symm

/-- Polynomial reversal commutes with an injective coefficient map. -/
theorem map_reverse_of_injective
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f) (p : R[X]) :
    p.reverse.map f = (p.map f).reverse := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

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
    {K : Type*} [Field K] (mu : K) : ∀ polynomials : List K[X],
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

/-- Characteristic-power-series contribution of one singleton SCC with
diagonal entry `d`. -/
def singletonPowerSeriesFactor (d : F101) : ModPolynomial :=
  1 - C d * X

/-- Product of all singleton-SCC factors. -/
def singletonPowerSeriesProduct (diagonal : List F101) : ModPolynomial :=
  (diagonal.map singletonPowerSeriesFactor).prod

private theorem singletonPowerSeriesFactor_ne_zero (d : F101) :
    singletonPowerSeriesFactor d ≠ 0 := by
  intro factor_zero
  have coeff_zero := congrArg (fun p : ModPolynomial => p.coeff 0) factor_zero
  simp [singletonPowerSeriesFactor] at coeff_zero

private theorem singletonPowerSeriesFactor_not_root_ninetyNine
    (d : F101) (d_ne : d ≠ 50) :
    ¬(singletonPowerSeriesFactor d).IsRoot (99 : F101) := by
  intro factor_root
  have product_one : d * (99 : F101) = 1 := by
    change eval (99 : F101) (singletonPowerSeriesFactor d) = 0 at factor_root
    have one_product : (1 : F101) = d * 99 := by
      simpa [singletonPowerSeriesFactor, sub_eq_zero] using factor_root
    exact one_product.symm
  apply d_ne
  calc
    d = (99 : F101)⁻¹ := eq_inv_of_mul_eq_one_left product_one
    _ = 50 := by native_decide

/-- Singleton SCCs whose loop weights are not `50` contribute no copy of
Knuth's visible factor. -/
theorem singletonPowerSeriesProduct_visibleFactor_emultiplicity_eq_zero
    (diagonal : List F101) (none_fifty : ∀ d ∈ diagonal, d ≠ 50) :
    emultiplicity visibleFactor (singletonPowerSeriesProduct diagonal) = 0 := by
  have product_ne : singletonPowerSeriesProduct diagonal ≠ 0 := by
    apply List.prod_ne_zero
    intro zero_mem
    simp only [List.mem_map] at zero_mem
    obtain ⟨d, _, factor_eq_zero⟩ := zero_mem
    exact singletonPowerSeriesFactor_ne_zero d factor_eq_zero
  rw [visibleFactor_emultiplicity_eq_rootMultiplicity _ product_ne]
  rw [singletonPowerSeriesProduct,
    rootMultiplicity_list_prod (99 : F101)]
  · norm_cast
    simp only [List.map_map]
    apply List.sum_eq_zero
    intro multiplicity multiplicity_mem
    simp only [List.mem_map] at multiplicity_mem
    obtain ⟨d, d_mem, multiplicity_eq⟩ := multiplicity_mem
    rw [← multiplicity_eq]
    exact rootMultiplicity_eq_zero
      (singletonPowerSeriesFactor_not_root_ninetyNine d (none_fifty d d_mem))
  · intro p p_mem
    simp only [List.mem_map] at p_mem
    obtain ⟨d, _, polynomial_eq⟩ := p_mem
    rw [← polynomial_eq]
    exact singletonPowerSeriesFactor_ne_zero d

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
    u2Plus.charpoly, u2Minus.charpoly, tPlus.charpoly,
    tMinus.charpoly].prod

/-- Base-field counterpart of the certified nontrivial block product. -/
def baseOpenBlockPowerSeriesProduct
    (tPlus tMinus u1Plus u1Minus u2Plus u2Minus : ModPolynomial) :
    ModPolynomial :=
  [tPlus, tMinus, u1Plus, u1Minus, u2Plus, u2Minus, tPlus,
    tMinus].prod.reverse

/-- Native `F₁₀₁` block multiplicities assemble directly to visible-factor
multiplicity two; no scalar-extension comparison remains in this theorem. -/
theorem baseOpenBlockPowerSeriesProduct_visibleFactor_emultiplicity_eq_two_of_roots
    (tPlus tMinus u1Plus u1Minus u2Plus u2Minus : ModPolynomial)
    (tPlus_ne : tPlus ≠ 0) (tMinus_ne : tMinus ≠ 0)
    (u1Plus_ne : u1Plus ≠ 0) (u1Minus_ne : u1Minus ≠ 0)
    (u2Plus_ne : u2Plus ≠ 0) (u2Minus_ne : u2Minus ≠ 0)
    (tPlus_one : tPlus.rootMultiplicity (50 : F101) = 1)
    (tMinus_zero : tMinus.rootMultiplicity (50 : F101) = 0)
    (u1Plus_zero : u1Plus.rootMultiplicity (50 : F101) = 0)
    (u1Minus_zero : u1Minus.rootMultiplicity (50 : F101) = 0)
    (u2Plus_zero : u2Plus.rootMultiplicity (50 : F101) = 0)
    (u2Minus_zero : u2Minus.rootMultiplicity (50 : F101) = 0) :
    emultiplicity visibleFactor
      (baseOpenBlockPowerSeriesProduct tPlus tMinus u1Plus u1Minus
        u2Plus u2Minus) = 2 := by
  let product := [tPlus, tMinus, u1Plus, u1Minus, u2Plus, u2Minus,
    tPlus, tMinus].prod
  have product_ne : product ≠ 0 := by
    apply List.prod_ne_zero
    intro zero_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at zero_mem
    rcases zero_mem with h | h | h | h | h | h | h | h
    · exact tPlus_ne h.symm
    · exact tMinus_ne h.symm
    · exact u1Plus_ne h.symm
    · exact u1Minus_ne h.symm
    · exact u2Plus_ne h.symm
    · exact u2Minus_ne h.symm
    · exact tPlus_ne h.symm
    · exact tMinus_ne h.symm
  have reverse_ne : product.reverse ≠ 0 := by
    simpa only [Ne, reverse_eq_zero] using product_ne
  rw [baseOpenBlockPowerSeriesProduct,
    visibleFactor_emultiplicity_eq_rootMultiplicity _ reverse_ne]
  have inverse_fifty : (50 : F101)⁻¹ = 99 := by native_decide
  rw [← inverse_fifty, rootMultiplicity_reverse_inv product (50 : F101)
    product_ne (by native_decide)]
  rw [rootMultiplicity_list_prod (50 : F101)]
  · simp [tPlus_one, tMinus_zero, u1Plus_zero, u1Minus_zero,
      u2Plus_zero, u2Minus_zero]
  · intro p p_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at p_mem
    rcases p_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      assumption

/-- Operator-level native-field assembly theorem consumed by the six concrete
CSR certificate conclusions. -/
theorem baseOpenBlockOperators_visibleFactor_emultiplicity_eq_two
    {nTp nTm nU1p nU1m nU2p nU2m : ℕ}
    (tPlus : Module.End F101 (Fin nTp → F101))
    (tMinus : Module.End F101 (Fin nTm → F101))
    (u1Plus : Module.End F101 (Fin nU1p → F101))
    (u1Minus : Module.End F101 (Fin nU1m → F101))
    (u2Plus : Module.End F101 (Fin nU2p → F101))
    (u2Minus : Module.End F101 (Fin nU2m → F101))
    (tPlus_one : tPlus.charpoly.rootMultiplicity (50 : F101) = 1)
    (tMinus_zero : tMinus.charpoly.rootMultiplicity (50 : F101) = 0)
    (u1Plus_zero : u1Plus.charpoly.rootMultiplicity (50 : F101) = 0)
    (u1Minus_zero : u1Minus.charpoly.rootMultiplicity (50 : F101) = 0)
    (u2Plus_zero : u2Plus.charpoly.rootMultiplicity (50 : F101) = 0)
    (u2Minus_zero : u2Minus.charpoly.rootMultiplicity (50 : F101) = 0) :
    emultiplicity visibleFactor
      (baseOpenBlockPowerSeriesProduct tPlus.charpoly tMinus.charpoly
        u1Plus.charpoly u1Minus.charpoly u2Plus.charpoly u2Minus.charpoly) = 2 := by
  apply baseOpenBlockPowerSeriesProduct_visibleFactor_emultiplicity_eq_two_of_roots
  · exact (LinearMap.charpoly_monic _).ne_zero
  · exact (LinearMap.charpoly_monic _).ne_zero
  · exact (LinearMap.charpoly_monic _).ne_zero
  · exact (LinearMap.charpoly_monic _).ne_zero
  · exact (LinearMap.charpoly_monic _).ne_zero
  · exact (LinearMap.charpoly_monic _).ne_zero
  · exact tPlus_one
  · exact tMinus_zero
  · exact u1Plus_zero
  · exact u1Minus_zero
  · exact u2Plus_zero
  · exact u2Minus_zero

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

/-- Six scalar-extension equalities for the raw reflection blocks assemble to
the mapped certified power-series product, including the second `Trel` copy
used for the permutation-similar `Wrel` sector. -/
theorem baseOpenBlockPowerSeriesProduct_map_eq_certified
    {nTp nTm nU1p nU1m nU2p nU2m : ℕ}
    (tPlusBase tMinusBase u1PlusBase u1MinusBase u2PlusBase u2MinusBase :
      ModPolynomial)
    (tPlus : Module.End CertificateField (Fin nTp → CertificateField))
    (tMinus : Module.End CertificateField (Fin nTm → CertificateField))
    (u1Plus : Module.End CertificateField (Fin nU1p → CertificateField))
    (u1Minus : Module.End CertificateField (Fin nU1m → CertificateField))
    (u2Plus : Module.End CertificateField (Fin nU2p → CertificateField))
    (u2Minus : Module.End CertificateField (Fin nU2m → CertificateField))
    (tPlus_map : tPlusBase.map (algebraMap F101 CertificateField) =
      tPlus.charpoly)
    (tMinus_map : tMinusBase.map (algebraMap F101 CertificateField) =
      tMinus.charpoly)
    (u1Plus_map : u1PlusBase.map (algebraMap F101 CertificateField) =
      u1Plus.charpoly)
    (u1Minus_map : u1MinusBase.map (algebraMap F101 CertificateField) =
      u1Minus.charpoly)
    (u2Plus_map : u2PlusBase.map (algebraMap F101 CertificateField) =
      u2Plus.charpoly)
    (u2Minus_map : u2MinusBase.map (algebraMap F101 CertificateField) =
      u2Minus.charpoly) :
    (baseOpenBlockPowerSeriesProduct tPlusBase tMinusBase u1PlusBase
      u1MinusBase u2PlusBase u2MinusBase).map
        (algebraMap F101 CertificateField) =
      certifiedOpenBlockPowerSeriesProduct tPlus tMinus u1Plus u1Minus
        u2Plus u2Minus := by
  rw [baseOpenBlockPowerSeriesProduct, certifiedOpenBlockPowerSeriesProduct,
    map_reverse_of_injective _
      (algebraMap F101 CertificateField).injective]
  simp only [certifiedOpenBlockCharpolyProduct, List.prod_cons, List.prod_nil,
    mul_one, Polynomial.map_mul, reverse_mul_of_domain]
  rw [tPlus_map, tMinus_map, u1Plus_map, u1Minus_map, u2Plus_map,
    u2Minus_map]

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
    rcases p_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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
      rcases zero_mem with h | h | h | h | h | h | h | h <;>
        exact (LinearMap.charpoly_monic _).ne_zero h.symm)
  · exact certificateField_fifty_ne_zero

/-- If an `F₁₀₁` transfer polynomial becomes the certified block power
series after scalar extension, then Knuth's visible factor has multiplicity
exactly two in the original polynomial.  The remaining decomposition proof
only has to supply the displayed map equality. -/
theorem visibleFactor_emultiplicity_two_of_map_eq_certifiedBlockProduct
    {nTp nTm nU1p nU1m nU2p nU2m : ℕ}
    (baseProduct : ModPolynomial) (baseProduct_ne : baseProduct ≠ 0)
    (tPlus : Module.End CertificateField (Fin nTp → CertificateField))
    (tMinus : Module.End CertificateField (Fin nTm → CertificateField))
    (u1Plus : Module.End CertificateField (Fin nU1p → CertificateField))
    (u1Minus : Module.End CertificateField (Fin nU1m → CertificateField))
    (u2Plus : Module.End CertificateField (Fin nU2p → CertificateField))
    (u2Minus : Module.End CertificateField (Fin nU2m → CertificateField))
    (map_eq : baseProduct.map (algebraMap F101 CertificateField) =
      certifiedOpenBlockPowerSeriesProduct tPlus tMinus u1Plus u1Minus
        u2Plus u2Minus)
    (tPlus_one : tPlus.charpoly.rootMultiplicity (50 : CertificateField) = 1)
    (tMinus_zero : tMinus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u1Plus_zero : u1Plus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u1Minus_zero : u1Minus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u2Plus_zero : u2Plus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u2Minus_zero : u2Minus.charpoly.rootMultiplicity (50 : CertificateField) = 0) :
    emultiplicity visibleFactor baseProduct = 2 := by
  rw [visibleFactor_emultiplicity_eq_rootMultiplicity baseProduct baseProduct_ne]
  rw [← rootMultiplicity_map_certificateField baseProduct (99 : F101), map_eq,
    certificateField_ninetyNine_eq_inv_fifty]
  exact_mod_cast
    certifiedOpenBlockPowerSeriesProduct_rootMultiplicity_inv_fifty_eq_two
      tPlus tMinus u1Plus u1Minus u2Plus u2Minus tPlus_one tMinus_zero
      u1Plus_zero u1Minus_zero u2Plus_zero u2Minus_zero

/-- Per-block scalar-extension equalities plus the six certificate conclusions
imply visible-factor multiplicity two for the raw `F₁₀₁` nontrivial block
product. -/
theorem baseOpenBlockPowerSeriesProduct_visibleFactor_emultiplicity_eq_two
    {nTp nTm nU1p nU1m nU2p nU2m : ℕ}
    (tPlusBase tMinusBase u1PlusBase u1MinusBase u2PlusBase u2MinusBase :
      ModPolynomial)
    (tPlus : Module.End CertificateField (Fin nTp → CertificateField))
    (tMinus : Module.End CertificateField (Fin nTm → CertificateField))
    (u1Plus : Module.End CertificateField (Fin nU1p → CertificateField))
    (u1Minus : Module.End CertificateField (Fin nU1m → CertificateField))
    (u2Plus : Module.End CertificateField (Fin nU2p → CertificateField))
    (u2Minus : Module.End CertificateField (Fin nU2m → CertificateField))
    (tPlus_map : tPlusBase.map (algebraMap F101 CertificateField) =
      tPlus.charpoly)
    (tMinus_map : tMinusBase.map (algebraMap F101 CertificateField) =
      tMinus.charpoly)
    (u1Plus_map : u1PlusBase.map (algebraMap F101 CertificateField) =
      u1Plus.charpoly)
    (u1Minus_map : u1MinusBase.map (algebraMap F101 CertificateField) =
      u1Minus.charpoly)
    (u2Plus_map : u2PlusBase.map (algebraMap F101 CertificateField) =
      u2Plus.charpoly)
    (u2Minus_map : u2MinusBase.map (algebraMap F101 CertificateField) =
      u2Minus.charpoly)
    (tPlus_one : tPlus.charpoly.rootMultiplicity (50 : CertificateField) = 1)
    (tMinus_zero : tMinus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u1Plus_zero : u1Plus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u1Minus_zero : u1Minus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u2Plus_zero : u2Plus.charpoly.rootMultiplicity (50 : CertificateField) = 0)
    (u2Minus_zero : u2Minus.charpoly.rootMultiplicity (50 : CertificateField) = 0) :
    emultiplicity visibleFactor
      (baseOpenBlockPowerSeriesProduct tPlusBase tMinusBase u1PlusBase
        u1MinusBase u2PlusBase u2MinusBase) = 2 := by
  have base_ne : baseOpenBlockPowerSeriesProduct tPlusBase tMinusBase
      u1PlusBase u1MinusBase u2PlusBase u2MinusBase ≠ 0 := by
    intro base_zero
    have mapped_zero := congrArg
      (Polynomial.map (algebraMap F101 CertificateField)) base_zero
    rw [baseOpenBlockPowerSeriesProduct_map_eq_certified tPlusBase tMinusBase
      u1PlusBase u1MinusBase u2PlusBase u2MinusBase tPlus tMinus u1Plus
      u1Minus u2Plus u2Minus tPlus_map tMinus_map u1Plus_map u1Minus_map
      u2Plus_map u2Minus_map] at mapped_zero
    have certified_ne : certifiedOpenBlockPowerSeriesProduct tPlus tMinus
        u1Plus u1Minus u2Plus u2Minus ≠ 0 := by
      have product_ne : certifiedOpenBlockCharpolyProduct tPlus tMinus
          u1Plus u1Minus u2Plus u2Minus ≠ 0 := by
        apply List.prod_ne_zero
        intro zero_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at zero_mem
        rcases zero_mem with h | h | h | h | h | h | h | h <;>
          exact (LinearMap.charpoly_monic _).ne_zero h.symm
      rw [certifiedOpenBlockPowerSeriesProduct]
      simpa only [Ne, reverse_eq_zero] using product_ne
    exact certified_ne (by simpa using mapped_zero)
  apply visibleFactor_emultiplicity_two_of_map_eq_certifiedBlockProduct
    (baseOpenBlockPowerSeriesProduct tPlusBase tMinusBase u1PlusBase
      u1MinusBase u2PlusBase u2MinusBase) base_ne tPlus tMinus u1Plus
      u1Minus u2Plus u2Minus
  · exact baseOpenBlockPowerSeriesProduct_map_eq_certified
      tPlusBase tMinusBase u1PlusBase u1MinusBase u2PlusBase u2MinusBase
      tPlus tMinus u1Plus u1Minus u2Plus u2Minus tPlus_map tMinus_map
      u1Plus_map u1Minus_map u2Plus_map u2Minus_map
  · exact tPlus_one
  · exact tMinus_zero
  · exact u1Plus_zero
  · exact u1Minus_zero
  · exact u2Plus_zero
  · exact u2Minus_zero

/-- Adding all singleton SCC factors to the certified nontrivial blocks leaves
the visible-factor multiplicity equal to two when no singleton loop has weight
`50`. -/
theorem visibleFactor_emultiplicity_two_with_singletons
    (baseBlockProduct : ModPolynomial)
    (block_multiplicity : emultiplicity visibleFactor baseBlockProduct = 2)
    (singletonDiagonal : List F101)
    (none_fifty : ∀ d ∈ singletonDiagonal, d ≠ 50) :
    emultiplicity visibleFactor
        (baseBlockProduct * singletonPowerSeriesProduct singletonDiagonal) = 2 := by
  rw [emultiplicity_mul visibleFactor_prime, block_multiplicity,
    singletonPowerSeriesProduct_visibleFactor_emultiplicity_eq_zero
      singletonDiagonal none_fifty]
  norm_num

end

end KnuthFasc8aEx210
