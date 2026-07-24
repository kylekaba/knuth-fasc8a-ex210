/-!
# Knuth Fascicle 8A, Exercise 210: width-5 contradiction

The mathematical argument uses three facts modulo 101 about the factor
`1 - 50z`, whose computational evidence is replayed by the certificate checker:

* it occurs at least once in the closed denominator;
* it occurs exactly twice in the open transfer determinant;
* the open denominator divides that determinant.

This file isolates the short argument showing that those facts rule out
`Q₅(z)³ ∣ Q₅⁺(z)`. The expensive matrix and certificate checks live in
`CertificateFiles.lean` and `CertCheck.lean`; they do not construct a proof term
of `WidthFiveCertificate`.
-/

namespace KnuthFasc8aEx210

universe u

/--
The properties of a chosen irreducible-factor multiplicity used by the proof.

For polynomials, `divides` is polynomial divisibility, `pow` is polynomial
power, and `multiplicity p` counts copies of the fixed factor in `p`.
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
If `a` contains at least `lower` copies of the chosen factor, then `a^n`
cannot divide `b` when `b` divides an object containing fewer than
`n * lower` copies.
-/
theorem not_pow_divides_of_multiplicity {alpha : Type u}
    (arithmetic : FactorArithmetic alpha)
    (a b bound : alpha) (n lower upper : Nat)
    (b_divides_bound : arithmetic.divides b bound)
    (lower_le_a : lower <= arithmetic.multiplicity a)
    (bound_multiplicity : arithmetic.multiplicity bound = upper)
    (insufficient : Not (n * lower <= upper)) :
    Not (arithmetic.divides (arithmetic.pow a n) b) := by
  intro power_divides_b
  apply insufficient
  calc
    n * lower <= n * arithmetic.multiplicity a :=
      Nat.mul_le_mul_left n lower_le_a
    _ = arithmetic.multiplicity (arithmetic.pow a n) :=
      (arithmetic.multiplicity_pow a n).symm
    _ <= arithmetic.multiplicity bound :=
      arithmetic.multiplicity_mono
        (arithmetic.divides_trans power_divides_b b_divides_bound)
    _ = upper := bound_multiplicity

/-- The three externally certified multiplicity facts needed at width 5. -/
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

/-- The proposed width-5 divisibility `Q₅(z)³ ∣ Q₅⁺(z)`. -/
def CubicDivisibilityAtWidthFive {alpha : Type u}
    (cert : WidthFiveCertificate alpha) : Prop :=
  cert.arithmetic.divides
    (cert.arithmetic.pow cert.closedDenominator 3)
    cert.openDenominator

/--
The certified contradiction: cubing one visible copy would require three
copies in a transfer determinant that has exactly two.
-/
theorem WidthFiveCertificate.not_cubic_divisibility {alpha : Type u}
    (cert : WidthFiveCertificate alpha) :
    Not (CubicDivisibilityAtWidthFive cert) :=
  not_pow_divides_of_multiplicity
    cert.arithmetic
    cert.closedDenominator
    cert.openDenominator
    cert.openTransferDeterminant
    3 1 2
    cert.open_denominator_divides_transfer
    cert.closed_factor_visible
    cert.open_transfer_multiplicity_two
    (by decide)

/-- Any universal claim that implies the width-5 divisibility is false. -/
theorem not_universal_claim_from_width_five {alpha : Type u}
    (cert : WidthFiveCertificate alpha)
    (ClaimAtWidth : Nat -> Prop)
    (bridge : ClaimAtWidth 5 -> CubicDivisibilityAtWidthFive cert) :
    Not (forall m, 5 <= m -> ClaimAtWidth m) := by
  intro universal
  exact cert.not_cubic_divisibility (bridge (universal 5 (by decide)))

end KnuthFasc8aEx210
