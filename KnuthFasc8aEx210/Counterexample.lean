/-!
# Knuth Fascicle 8A, Exercise 210: width-5 certificate core

This file formalizes the small logical core of the counterexample described in
the repository `kylekaba/knuth-fasc8a-ex210`.

The large external checkers establish the following facts modulo 101 for the
linear factor `1 - 50 z`:

* the closed denominator has at least one visible copy of the factor;
* the open-side transfer determinant has exactly two copies of the factor;
* the open denominator divides that transfer determinant.

Lean checks here that these facts are incompatible with the proposed cubic
divisibility `Q_5(z)^3 | Q_5^+(z)`, and therefore with the universal claim.
-/

namespace KnuthFasc8aEx210

universe u

/-- The modular linear factor `1 - eigenvalue * z` over `Z/modulus Z`. -/
structure ModularLinearFactor where
  modulus : Nat
  eigenvalue : Nat
deriving DecidableEq, Repr

/-- The factor singled out by the repository certificate: `1 - 50 z` modulo 101. -/
def visibleFactor : ModularLinearFactor where
  modulus := 101
  eigenvalue := 50

/--
The concrete multiplicity summary produced by the external certificate.

`closedDenominatorCopies = 1` records the visible copy in the closed
denominator. `openTransferCopies = 2` records the exact multiplicity in the
open-side transfer determinant `det(I - zT) det(I - zU) det(I - zW_rel)`.
-/
structure MultiplicitySummary where
  width : Nat
  factor : ModularLinearFactor
  closedDenominatorCopies : Nat
  openTransferCopies : Nat
deriving Repr

/-- The width-5 numerical summary from the repository proof. -/
def repositorySummary : MultiplicitySummary where
  width := 5
  factor := visibleFactor
  closedDenominatorCopies := 1
  openTransferCopies := 2

/--
Necessary multiplicity test for cubic divisibility at a chosen factor.

If `Q_m(z)^3` divides `Q_m^+(z)`, and the open denominator divides an open-side
transfer determinant, then the determinant must contain at least three times as
many copies of every factor visible in `Q_m(z)`.
-/
def CubicMultiplicityTest (summary : MultiplicitySummary) : Prop :=
  3 * summary.closedDenominatorCopies <= summary.openTransferCopies

/-- The repository witness has width at least five. -/
theorem repository_width_ge_five : 5 <= repositorySummary.width := by
  decide

/-- The concrete arithmetic obstruction: three visible copies cannot fit into two. -/
theorem repository_cubic_multiplicity_test_fails :
    Not (CubicMultiplicityTest repositorySummary) := by
  unfold CubicMultiplicityTest repositorySummary
  decide

/--
An abstract interface for a single-factor multiplicity valuation.

This avoids trusting any polynomial implementation here. The theorem below only
needs two standard properties of such a valuation:

* divisibility cannot decrease multiplicity;
* the multiplicity of `a^n` is `n` times the multiplicity of `a`.
-/
structure FactorArithmetic (alpha : Type u) where
  divides : alpha -> alpha -> Prop
  pow : alpha -> Nat -> alpha
  multiplicity : alpha -> Nat
  divides_trans :
    forall {a b c : alpha}, divides a b -> divides b c -> divides a c
  multiplicity_mono :
    forall {a b : alpha}, divides a b -> multiplicity a <= multiplicity b
  multiplicity_pow :
    forall (a : alpha) (n : Nat), multiplicity (pow a n) = n * multiplicity a

/--
The certificate facts needed at width 5, stated for arbitrary polynomial-like
objects equipped with a single-factor multiplicity valuation.
-/
structure WidthFiveCertificate (alpha : Type u) where
  arithmetic : FactorArithmetic alpha
  closedDenominator : alpha
  openDenominator : alpha
  openTransferDeterminant : alpha
  closed_factor_visible :
    1 <= arithmetic.multiplicity closedDenominator
  open_transfer_multiplicity_two :
    arithmetic.multiplicity openTransferDeterminant = 2
  open_denominator_divides_transfer :
    arithmetic.divides openDenominator openTransferDeterminant

/-- The proposed width-5 divisibility `Q_5(z)^3 | Q_5^+(z)`. -/
def CubicDivisibilityAtWidthFive {alpha : Type u}
    (cert : WidthFiveCertificate alpha) : Prop :=
  cert.arithmetic.divides
    (cert.arithmetic.pow cert.closedDenominator 3)
    cert.openDenominator

/--
The certified contradiction.

The visible closed factor supplies at least one copy. Cubing would require at
least three copies in the open determinant, but the certificate says the open
determinant has exactly two.
-/
theorem WidthFiveCertificate.not_cubic_divisibility {alpha : Type u}
    (cert : WidthFiveCertificate alpha) :
    Not (CubicDivisibilityAtWidthFive cert) := by
  intro h_cubic
  have h_pow_divides_det :
      cert.arithmetic.divides
        (cert.arithmetic.pow cert.closedDenominator 3)
        cert.openTransferDeterminant :=
    cert.arithmetic.divides_trans
      h_cubic
      cert.open_denominator_divides_transfer
  have h_pow_le_det :
      cert.arithmetic.multiplicity
          (cert.arithmetic.pow cert.closedDenominator 3)
        <= cert.arithmetic.multiplicity cert.openTransferDeterminant :=
    cert.arithmetic.multiplicity_mono h_pow_divides_det
  have h_three_le_det :
      3 <= cert.arithmetic.multiplicity cert.openTransferDeterminant := by
    calc
      3 = 3 * 1 := by
        decide
      _ <= 3 * cert.arithmetic.multiplicity cert.closedDenominator :=
        Nat.mul_le_mul_left 3 cert.closed_factor_visible
      _ = cert.arithmetic.multiplicity
          (cert.arithmetic.pow cert.closedDenominator 3) := by
        exact (cert.arithmetic.multiplicity_pow cert.closedDenominator 3).symm
      _ <= cert.arithmetic.multiplicity cert.openTransferDeterminant :=
        h_pow_le_det
  rw [cert.open_transfer_multiplicity_two] at h_three_le_det
  exact repository_cubic_multiplicity_test_fails h_three_le_det

/--
Any universal statement implying the width-5 divisibility is false.

The bridge hypothesis lets callers connect their own formalization of
"`Q_m(z)^3` divides `Q_m^+(z)`" to the certificate interface above.
-/
theorem not_universal_claim_from_width_five {alpha : Type u}
    (cert : WidthFiveCertificate alpha)
    (ClaimAtWidth : Nat -> Prop)
    (bridge :
      ClaimAtWidth 5 -> CubicDivisibilityAtWidthFive cert) :
    Not (forall m, 5 <= m -> ClaimAtWidth m) := by
  intro h_universal
  exact cert.not_cubic_divisibility (bridge (h_universal 5 (by decide)))

end KnuthFasc8aEx210
