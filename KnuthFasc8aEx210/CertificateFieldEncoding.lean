import KnuthFasc8aEx210.CertificateField
import KnuthFasc8aEx210.CertificateFiles

/-!
# Sound interpretation of encoded extension-field elements

This file connects the executable `UInt8 × UInt8` arithmetic used while
replaying rank certificates to the genuine field in `CertificateField.lean`.
-/

namespace KnuthFasc8aEx210

/-- Exact natural-number value of the verifier's reduction helper. -/
theorem toNat_u8Mod101 (n : ℕ) : (u8Mod101 n).toNat = n % 101 := by
  simp only [u8Mod101, p101]
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt n (by omega)) (by omega))

/-- Reduction through the verifier's byte helper has the expected value in
the base field. -/
theorem zmod101_of_u8Mod101 (n : ℕ) :
    ((u8Mod101 n).toNat : ZMod 101) = n := by
  rw [toNat_u8Mod101]
  exact ZMod.natCast_mod n 101

/-- Mathematical value of an encoded pair. -/
noncomputable def ExtElt.toCertificateField (x : ExtElt) : CertificateField :=
  certificatePair x.a.toNat x.b.toNat

/-- Encoded field elements are canonical when both bytes are reduced modulo
101.  All values produced by `u8Mod101` satisfy this invariant. -/
def ExtElt.IsCanonical (x : ExtElt) : Prop :=
  x.a.toNat < 101 ∧ x.b.toNat < 101

theorem ExtElt.isCanonical_add (x y : ExtElt) : (x.add y).IsCanonical := by
  constructor <;> simp [ExtElt.add, toNat_u8Mod101,
    Nat.mod_lt]

theorem ExtElt.isCanonical_mul (x y : ExtElt) : (x.mul y).IsCanonical := by
  constructor <;> simp [ExtElt.mul, toNat_u8Mod101,
    Nat.mod_lt]

private theorem zmod101_natCast_eq_zero_iff_of_lt {n : ℕ} (n_lt : n < 101) :
    (n : ZMod 101) = 0 ↔ n = 0 := by
  constructor
  · intro cast_zero
    have values_equal := congrArg ZMod.val cast_zero
    simpa [ZMod.val_natCast_of_lt n_lt] using values_equal
  · rintro rfl
    simp

/-- On canonical encodings, the executable zero test agrees with equality in
the mathematical extension field. -/
theorem ExtElt.toCertificateField_eq_zero_iff
    (x : ExtElt) (canonical : x.IsCanonical) :
    x.toCertificateField = 0 ↔ x.isZero = true := by
  rw [ExtElt.toCertificateField, certificatePair_eq_zero_iff,
    zmod101_natCast_eq_zero_iff_of_lt canonical.1,
    zmod101_natCast_eq_zero_iff_of_lt canonical.2]
  simp only [ExtElt.isZero, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · exact UInt8.toNat_inj.mp (by simpa using ha)
    · exact UInt8.toNat_inj.mp (by simpa using hb)
  · rintro ⟨ha, hb⟩
    constructor <;> simp [ha, hb]

@[simp]
theorem ExtElt.toCertificateField_add (x y : ExtElt) :
    (x.add y).toCertificateField =
      x.toCertificateField + y.toCertificateField := by
  rw [ExtElt.toCertificateField, ExtElt.add, ExtElt.toCertificateField,
    ExtElt.toCertificateField, ← certificatePair_add]
  congr 1
  · simpa only [Nat.cast_add] using
      zmod101_of_u8Mod101 (x.a.toNat + y.a.toNat)
  · simpa only [Nat.cast_add] using
      zmod101_of_u8Mod101 (x.b.toNat + y.b.toNat)

@[simp]
theorem ExtElt.toCertificateField_mul (x y : ExtElt) :
    (x.mul y).toCertificateField =
      x.toCertificateField * y.toCertificateField := by
  rw [ExtElt.toCertificateField, ExtElt.mul, ExtElt.toCertificateField,
    ExtElt.toCertificateField, ← certificatePair_mul]
  congr 1
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      zmod101_of_u8Mod101
        (x.a.toNat * y.a.toNat + 2 * x.b.toNat * y.b.toNat)
  · simpa only [Nat.cast_add, Nat.cast_mul] using
      zmod101_of_u8Mod101
        (x.a.toNat * y.b.toNat + x.b.toNat * y.a.toNat)

end KnuthFasc8aEx210
