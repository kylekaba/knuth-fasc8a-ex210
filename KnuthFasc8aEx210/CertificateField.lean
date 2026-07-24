import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.AdjoinRoot

/-!
# The extension field used by the rank certificates

The `KMW2CERT` files encode elements as byte pairs `a + b*t`, with arithmetic
modulo 101 and `t^2 = 2`.  This file gives that representation an actual field
semantics.  Subsequent certificate-soundness proofs can map the executable
byte operations into this field.
-/

namespace KnuthFasc8aEx210

open Polynomial

instance certificatePrimeFact : Fact (Nat.Prime 101) := ⟨by native_decide⟩

/-- The defining polynomial for the certificate extension field. -/
noncomputable abbrev certificateExtensionPolynomial : (ZMod 101)[X] := X ^ 2 - C 2

private theorem certificateExtensionPolynomial_monic :
    certificateExtensionPolynomial.Monic := by
  exact monic_X_pow_sub_C 2 (by omega)

private theorem certificateExtensionPolynomial_natDegree :
    certificateExtensionPolynomial.natDegree = 2 := by
  exact natDegree_X_pow_sub_C

private theorem two_is_not_square_mod_101 :
    ∀ x : ZMod 101, x ^ 2 ≠ 2 := by
  native_decide

theorem certificateExtensionPolynomial_irreducible :
    Irreducible certificateExtensionPolynomial := by
  rw [certificateExtensionPolynomial_monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro x x_mem
    have is_root := (mem_roots certificateExtensionPolynomial_monic.ne_zero).mp x_mem
    apply two_is_not_square_mod_101 x
    apply sub_eq_zero.mp
    simpa [certificateExtensionPolynomial, IsRoot, eval_sub, eval_pow] using is_root
  · simp
  · simp

instance certificateExtensionPolynomial.factIrreducible :
    Fact (Irreducible certificateExtensionPolynomial) :=
  ⟨certificateExtensionPolynomial_irreducible⟩

/-- The genuine field represented by the rank-certificate byte pairs. -/
abbrev CertificateField := AdjoinRoot certificateExtensionPolynomial

/-- The distinguished element `t` represented by the second byte. -/
noncomputable def certificateRoot : CertificateField :=
  AdjoinRoot.root certificateExtensionPolynomial

theorem certificateRoot_sq : certificateRoot ^ 2 = 2 := by
  have root_zero : AdjoinRoot.mk certificateExtensionPolynomial
      certificateExtensionPolynomial = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C] at root_zero
  change certificateRoot ^ 2 - (2 : CertificateField) = 0 at root_zero
  exact sub_eq_zero.mp root_zero

/-- Mathematical interpretation of a coefficient pair `a + b*t`. -/
noncomputable def certificatePair (a b : ZMod 101) : CertificateField :=
  algebraMap (ZMod 101) CertificateField a +
    algebraMap (ZMod 101) CertificateField b * certificateRoot

@[simp]
theorem certificatePair_zero : certificatePair 0 0 = 0 := by
  simp [certificatePair]

@[simp]
theorem certificatePair_one : certificatePair 1 0 = 1 := by
  simp [certificatePair]

theorem certificatePair_add (a b c d : ZMod 101) :
    certificatePair (a + c) (b + d) =
      certificatePair a b + certificatePair c d := by
  simp only [certificatePair, map_add]
  ring

theorem certificatePair_neg (a b : ZMod 101) :
    certificatePair (-a) (-b) = -certificatePair a b := by
  simp only [certificatePair, map_neg]
  ring

theorem certificatePair_mul (a b c d : ZMod 101) :
    certificatePair (a * c + 2 * b * d) (a * d + b * c) =
      certificatePair a b * certificatePair c d := by
  simp only [certificatePair, map_add, map_mul, map_ofNat]
  ring_nf
  rw [certificateRoot_sq]

/-- Multiplication by the conjugate lands in the base field with norm
`a² - 2b²`, exactly the denominator used by `ExtElt.inv`. -/
theorem certificatePair_mul_conjugate (a b : ZMod 101) :
    certificatePair a b * certificatePair a (-b) =
      algebraMap (ZMod 101) CertificateField (a ^ 2 - 2 * b ^ 2) := by
  rw [← certificatePair_mul]
  simp [pow_two, certificatePair]
  ring

theorem certificatePair_eq_mk (a b : ZMod 101) :
    certificatePair a b = AdjoinRoot.mk certificateExtensionPolynomial
      (C a + C b * X) := by
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rfl

/-- Uniqueness of the two-coordinate representation. -/
@[simp]
theorem certificatePair_eq_zero_iff (a b : ZMod 101) :
    certificatePair a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro pair_zero
    let g : (ZMod 101)[X] := C a + C b * X
    have g_degree_lt : g.natDegree < 2 := by
      have constant_degree : (C a).natDegree ≤ 0 := by
        simpa only [pow_zero, mul_one] using natDegree_C_mul_X_pow_le a 0
      calc
        g.natDegree ≤ max (C a).natDegree (C b * X).natDegree :=
          by simp [g]
        _ ≤ 1 := max_le (constant_degree.trans (by omega)) (by
          simpa only [pow_one] using natDegree_C_mul_X_pow_le b 1)
        _ < 2 := by omega
    have g_zero : g = 0 := by
      by_contra g_ne_zero
      have mk_ne_zero := AdjoinRoot.mk_ne_zero_of_natDegree_lt
        certificateExtensionPolynomial_monic g_ne_zero (by
          simpa [certificateExtensionPolynomial_natDegree] using g_degree_lt)
      apply mk_ne_zero
      simpa [g, ← certificatePair_eq_mk] using pair_zero
    constructor
    · have coefficient_zero := congrArg (fun p : (ZMod 101)[X] => p.coeff 0) g_zero
      simpa [g] using coefficient_zero
    · have coefficient_one := congrArg (fun p : (ZMod 101)[X] => p.coeff 1) g_zero
      simpa [g] using coefficient_one
  · rintro ⟨rfl, rfl⟩
    exact certificatePair_zero

end KnuthFasc8aEx210
