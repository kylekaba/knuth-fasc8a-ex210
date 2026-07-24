import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Knuth Fascicle 8A, Exercise 210: width-5 contradiction

This file formalizes the algebraic bridge from the width-5 certificate facts
to the failure of cubic divisibility. Unlike the certificate-file executable,
the objects here are actual polynomials:

* the normalized denominators and transfer determinant lie in `ℤ[X]`;
* the conjectured divisibility is stated in `ℚ[X]`;
* the decisive factor is `1 - 50X` in `(ZMod 101)[X]`.

Mathlib's Gauss lemma moves a hypothetical rational divisibility back to
`ℤ[X]`. Mapping coefficients modulo 101 then contradicts the certified fact
that the open transfer determinant contains exactly two copies of `1 - 50X`.

The expensive matrix and certificate checks live in `CertificateFiles.lean`
and `CertCheck.lean`; as an `IO` program, that checker does not construct a
proof term of `WidthFiveCertificate`.
-/

namespace KnuthFasc8aEx210

open Polynomial

noncomputable section

/-- The field used by the width-5 certificate. -/
abbrev F101 := ZMod 101

/-- Integer, rational, and mod-101 polynomial types used in the bridge. -/
abbrev IntegerPolynomial := Polynomial ℤ
abbrev RationalPolynomial := Polynomial ℚ
abbrev ModPolynomial := Polynomial F101

/-- Coefficientwise reduction of an integer polynomial modulo 101. -/
def reduce101 (p : IntegerPolynomial) : ModPolynomial :=
  p.map (Int.castRingHom F101)

/-- Coefficientwise inclusion of an integer polynomial into `ℚ[X]`. -/
def toRational (p : IntegerPolynomial) : RationalPolynomial :=
  p.map (Int.castRingHom ℚ)

/-- The concrete linear factor detected by the certificate: `1 - 50X`. -/
def visibleFactor : ModPolynomial :=
  1 - C 50 * X

/-- In `F_101`, `1 - 50X` is a unit multiple of `X - 99`. -/
theorem visibleFactor_eq_unit_mul_X_sub_C :
    visibleFactor = C (-50 : F101) * (X - C 99) := by
  rw [visibleFactor, mul_sub, ← C_mul]
  have h : (-50 : F101) * 99 = -1 := by native_decide
  rw [h]
  simp
  ring

/-- Powers of a primitive integer polynomial remain primitive. -/
theorem isPrimitive_pow {p : IntegerPolynomial} (hp : p.IsPrimitive) :
    ∀ n : Nat, (p ^ n).IsPrimitive
  | 0 => by simp [Polynomial.isPrimitive_one]
  | n + 1 => by
      rw [pow_succ]
      exact (isPrimitive_pow hp n).mul hp

/-- An integer polynomial with constant coefficient one is primitive. -/
theorem isPrimitive_of_coeff_zero_eq_one {p : IntegerPolynomial}
    (constant_one : p.coeff 0 = 1) : p.IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r constant_dvd
  apply isUnit_iff_dvd_one.mpr
  rw [← constant_one]
  exact (Polynomial.C_dvd_iff_dvd_coeff r p).mp constant_dvd 0

/--
The algebraic facts supplied by the mathematical width-5 certificate.

The first two fields record the constant-term-one normalization used in
`PROOF.md`; Lean derives primitiveness from that normalization.
The remaining fields are the three facts used in the contradiction:

* `1 - 50X` divides the reduced closed denominator;
* the integer open denominator divides the integer transfer determinant;
* `1 - 50X` has multiplicity exactly two in the reduced determinant.
-/
structure WidthFiveCertificate where
  closedDenominator : IntegerPolynomial
  openDenominator : IntegerPolynomial
  openTransferDeterminant : IntegerPolynomial
  closed_constant_one : closedDenominator.coeff 0 = 1
  open_constant_one : openDenominator.coeff 0 = 1
  closed_factor_visible :
    visibleFactor ∣ reduce101 closedDenominator
  open_denominator_divides_transfer :
    openDenominator ∣ openTransferDeterminant
  open_transfer_multiplicity_two :
    emultiplicity visibleFactor (reduce101 openTransferDeterminant) = 2

/-- The conjectured width-5 divisibility, stated in the intended ring `ℚ[X]`. -/
def CubicDivisibilityAtWidthFive (cert : WidthFiveCertificate) : Prop :=
  toRational cert.closedDenominator ^ 3 ∣ toRational cert.openDenominator

/-- Multiplicity two rules out a third copy of the visible factor. -/
theorem WidthFiveCertificate.visible_factor_cube_not_dvd_transfer
    (cert : WidthFiveCertificate) :
    Not (visibleFactor ^ 3 ∣ reduce101 cert.openTransferDeterminant) := by
  apply not_pow_dvd_of_emultiplicity_lt
  rw [cert.open_transfer_multiplicity_two]
  norm_num

/--
The certified width-5 contradiction over actual polynomial rings.

A hypothetical divisibility in `ℚ[X]` descends to `ℤ[X]` by Gauss's lemma
because both normalized denominators are primitive. It then survives reduction
modulo 101. The visible factor in the closed denominator would therefore occur
at least three times in the transfer determinant, contradicting its certified
multiplicity two.
-/
theorem WidthFiveCertificate.not_cubic_divisibility
    (cert : WidthFiveCertificate) :
    Not (CubicDivisibilityAtWidthFive cert) := by
  intro rational_dvd
  have integer_dvd :
      cert.closedDenominator ^ 3 ∣ cert.openDenominator := by
    apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
      (cert.closedDenominator ^ 3) cert.openDenominator
      (isPrimitive_pow
        (isPrimitive_of_coeff_zero_eq_one cert.closed_constant_one) 3)
      (isPrimitive_of_coeff_zero_eq_one cert.open_constant_one)).mpr
    rw [Polynomial.map_pow]
    exact rational_dvd
  have integer_dvd_transfer :
      cert.closedDenominator ^ 3 ∣ cert.openTransferDeterminant :=
    integer_dvd.trans cert.open_denominator_divides_transfer
  have reduced_dvd_transfer :
      reduce101 cert.closedDenominator ^ 3 ∣
        reduce101 cert.openTransferDeterminant := by
    simpa [reduce101, Polynomial.map_pow] using
      Polynomial.map_dvd (Int.castRingHom F101) integer_dvd_transfer
  exact cert.visible_factor_cube_not_dvd_transfer
    ((pow_dvd_pow_of_dvd cert.closed_factor_visible 3).trans
      reduced_dvd_transfer)

/-- Any universal claim that implies the concrete width-5 divisibility is false. -/
theorem not_universal_claim_from_width_five
    (cert : WidthFiveCertificate)
    (ClaimAtWidth : Nat -> Prop)
    (bridge : ClaimAtWidth 5 -> CubicDivisibilityAtWidthFive cert) :
    Not (forall m, 5 <= m -> ClaimAtWidth m) := by
  intro universal
  exact cert.not_cubic_divisibility (bridge (universal 5 (by decide)))

end

end KnuthFasc8aEx210
