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

theorem ExtElt.isCanonical_scale (c : ℕ) (x : ExtElt) : (x.scale c).IsCanonical := by
  constructor <;> simp [ExtElt.scale, toNat_u8Mod101, Nat.mod_lt]

theorem isCanonical_u8SubMod101 {x y : UInt8}
    (x_lt : x.toNat < 101) (y_lt : y.toNat < 101) :
    (u8SubMod101 x y).toNat < 101 := by
  unfold u8SubMod101
  split <;> rw [UInt8.toNat_ofNat']
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem zmod101_of_u8SubMod101 {x y : UInt8}
    (x_lt : x.toNat < 101) (y_lt : y.toNat < 101) :
    ((u8SubMod101 x y).toNat : ZMod 101) = x.toNat - y.toNat := by
  unfold u8SubMod101
  split <;> rw [UInt8.toNat_ofNat']
  · rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.cast_sub (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.cast_sub (by omega), Nat.cast_add]
    rw [ZMod.natCast_self]
    simp

theorem ExtElt.isCanonical_sub {x y : ExtElt}
    (x_canonical : x.IsCanonical) (y_canonical : y.IsCanonical) :
    (x.sub y).IsCanonical := by
  exact ⟨isCanonical_u8SubMod101 x_canonical.1 y_canonical.1,
    isCanonical_u8SubMod101 x_canonical.2 y_canonical.2⟩

/-- Exhaustive soundness check for the actual 101-input inverse-search loop.
The quantified proposition is closed and decidable, so `native_decide`
checks every base-field input and every possible returned byte. -/
private theorem inverseMod101?_sound_finite :
    ∀ a : Fin 101, ∀ q : UInt8,
      inverseMod101? a = some q →
        (a * q.toNat) % 101 = 1 ∧ q.toNat < 101 := by
  native_decide

theorem inverseMod101?_sound {a : ℕ} (a_lt : a < 101) {q : UInt8}
    (result : inverseMod101? a = some q) :
    (a : ZMod 101) * q.toNat = 1 ∧ q.toNat < 101 := by
  have checked := inverseMod101?_sound_finite ⟨a, a_lt⟩ q result
  constructor
  · rw [← Nat.cast_mul, ← ZMod.natCast_mod (a * q.toNat) 101, checked.1]
    norm_num
  · exact checked.2

private theorem zmod101_if_negByte (b : UInt8) (b_lt : b.toNat < 101) :
    ((if b == 0 then 0 else 101 - b.toNat : ℕ) : ZMod 101) = -b.toNat := by
  split
  · rename_i b_zero
    have : b = 0 := beq_iff_eq.mp b_zero
    simp [this]
  · rename_i b_ne_zero
    have b_pos : 0 < b.toNat := by
      have : b ≠ 0 := by simpa only [beq_iff_eq] using b_ne_zero
      have b_toNat_ne : b.toNat ≠ 0 := by
        intro b_toNat_zero
        apply this
        exact UInt8.toNat_inj.mp (by simpa using b_toNat_zero)
      omega
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp

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
theorem ExtElt.toCertificateField_sub {x y : ExtElt}
    (x_canonical : x.IsCanonical) (y_canonical : y.IsCanonical) :
    (x.sub y).toCertificateField =
      x.toCertificateField - y.toCertificateField := by
  rw [ExtElt.toCertificateField, ExtElt.sub, ExtElt.toCertificateField,
    ExtElt.toCertificateField, ← certificatePair_sub]
  congr 1
  · exact zmod101_of_u8SubMod101 x_canonical.1 y_canonical.1
  · exact zmod101_of_u8SubMod101 x_canonical.2 y_canonical.2

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

/-- The executable convolution coefficient has the usual field-valued
coefficient semantics. -/
private theorem extConvolutionSums_eq
    (left right : ℕ → ExtElt) (rightLength k n : ℕ) :
    extConvolutionSums left right rightLength k n =
      (∑ i ∈ Finset.range n,
          if i ≤ k ∧ k - i < rightLength then
            (left i).a.toNat * (right (k - i)).a.toNat +
              2 * (left i).b.toNat * (right (k - i)).b.toNat
          else 0,
        ∑ i ∈ Finset.range n,
          if i ≤ k ∧ k - i < rightLength then
            (left i).a.toNat * (right (k - i)).b.toNat +
              (left i).b.toNat * (right (k - i)).a.toNat
          else 0) := by
  induction n with
  | zero => simp [extConvolutionSums]
  | succ n ih =>
      rw [extConvolutionSums, ih]
      simp only [Finset.sum_range_succ]
      split_ifs <;> simp_all [Nat.add_assoc]

private theorem certificatePair_finset_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (real imag : α → ZMod 101) :
    certificatePair (∑ i ∈ s, real i) (∑ i ∈ s, imag i) =
      ∑ i ∈ s, certificatePair (real i) (imag i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s i_not_mem ih =>
      simp only [Finset.sum_insert i_not_mem]
      rw [certificatePair_add, ih]

theorem extConvolutionCoefficient_toCertificateField
    (left : ℕ → ExtElt) (leftLength : ℕ)
    (right : ℕ → ExtElt) (rightLength k : ℕ) :
    (extConvolutionCoefficient left leftLength right rightLength k).toCertificateField =
      ∑ i ∈ Finset.range leftLength,
        if i ≤ k ∧ k - i < rightLength then
          (left i).toCertificateField * (right (k - i)).toCertificateField
        else 0 := by
  rw [ExtElt.toCertificateField]
  simp only [extConvolutionCoefficient, extConvolutionSums_eq]
  rw [zmod101_of_u8Mod101, zmod101_of_u8Mod101]
  push_cast
  rw [certificatePair_finset_sum]
  apply Finset.sum_congr rfl
  intro i i_mem
  split_ifs with valid
  · rw [ExtElt.toCertificateField, ExtElt.toCertificateField,
      certificatePair_mul]
  · simp

@[simp]
theorem ExtElt.toCertificateField_scale (c : ℕ) (x : ExtElt) :
    (x.scale c).toCertificateField =
      algebraMap (ZMod 101) CertificateField c * x.toCertificateField := by
  rw [ExtElt.toCertificateField, ExtElt.scale, ExtElt.toCertificateField,
    ← certificatePair_scale]
  congr 1
  · simpa only [Nat.cast_mul] using
      zmod101_of_u8Mod101 (c * x.a.toNat)
  · simpa only [Nat.cast_mul] using
      zmod101_of_u8Mod101 (c * x.b.toNat)

/-- Soundness of the executable quadratic-field inverse.  A successful
return is canonical and multiplies the input to one in `CertificateField`. -/
theorem ExtElt.inv_sound {x y : ExtElt} (x_canonical : x.IsCanonical)
    (result : x.inv = .ok y) :
    y.IsCanonical ∧ y.toCertificateField * x.toCertificateField = 1 := by
  let denom : ℕ :=
    (x.a.toNat * x.a.toNat + 101 -
      (2 * x.b.toNat * x.b.toNat) % 101) % 101
  have denom_lt : denom < 101 := Nat.mod_lt _ (by omega)
  change (match inverseMod101? denom with
    | none => (Except.error "attempted to invert zero extension-field element" : ParseM ExtElt)
    | some q => (Except.ok {
        a := u8Mod101 (x.a.toNat * q.toNat)
        b := u8Mod101
          ((if x.b == 0 then 0 else 101 - x.b.toNat) * q.toNat) } : ParseM ExtElt)) =
      Except.ok y at result
  generalize inverse_result : inverseMod101? denom = inverse at result
  cases inverse with
  | none => simp at result
  | some q =>
      have y_eq : y = {
          a := u8Mod101 (x.a.toNat * q.toNat)
          b := u8Mod101
            ((if x.b == 0 then 0 else 101 - x.b.toNat) * q.toNat) } := by
        simpa [inverse_result] using result.symm
      subst y
      constructor
      · constructor <;> simp [toNat_u8Mod101, Nat.mod_lt]
      · have q_inverse := inverseMod101?_sound denom_lt inverse_result
        have denom_cast : (denom : ZMod 101) =
            (x.a.toNat : ZMod 101) ^ 2 -
              2 * (x.b.toNat : ZMod 101) ^ 2 := by
          dsimp [denom]
          rw [ZMod.natCast_mod]
          rw [Nat.cast_sub (by
            have := Nat.mod_lt (2 * x.b.toNat * x.b.toNat) (by omega : 0 < 101)
            omega)]
          rw [Nat.cast_add, ZMod.natCast_self, add_zero]
          rw [ZMod.natCast_mod]
          push_cast
          ring
        have encoded_inverse :
            ({
              a := u8Mod101 (x.a.toNat * q.toNat)
              b := u8Mod101
                ((if x.b == 0 then 0 else 101 - x.b.toNat) * q.toNat)
            } : ExtElt).toCertificateField =
              algebraMap (ZMod 101) CertificateField q.toNat *
                certificatePair x.a.toNat (-(x.b.toNat : ZMod 101)) := by
          rw [ExtElt.toCertificateField, ← certificatePair_scale]
          congr 1
          · simpa only [Nat.cast_mul, mul_comm] using
              zmod101_of_u8Mod101 (x.a.toNat * q.toNat)
          · rw [zmod101_of_u8Mod101, Nat.cast_mul,
              zmod101_if_negByte x.b x_canonical.2]
            ring
        rw [encoded_inverse, ExtElt.toCertificateField]
        calc
          _ = algebraMap (ZMod 101) CertificateField q.toNat *
              (certificatePair x.a.toNat x.b.toNat *
                certificatePair x.a.toNat (-(x.b.toNat : ZMod 101))) := by ring
          _ = algebraMap (ZMod 101) CertificateField q.toNat *
              algebraMap (ZMod 101) CertificateField
                ((x.a.toNat : ZMod 101) ^ 2 -
                  2 * (x.b.toNat : ZMod 101) ^ 2) := by
            rw [certificatePair_mul_conjugate]
          _ = algebraMap (ZMod 101) CertificateField
              ((q.toNat : ZMod 101) *
                ((x.a.toNat : ZMod 101) ^ 2 -
                  2 * (x.b.toNat : ZMod 101) ^ 2)) := by rw [map_mul]
          _ = 1 := by
            rw [← denom_cast, mul_comm, q_inverse.1, map_one]

theorem ExtElt.inv_toCertificateField {x y : ExtElt}
    (x_canonical : x.IsCanonical) (result : x.inv = .ok y) :
    y.toCertificateField = x.toCertificateField⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (x.inv_sound x_canonical result).2

/-- Soundness of the `Except`-valued division operation used at every
nonzero BM discrepancy. -/
theorem ExtElt.div_sound {x y z : ExtElt} (y_canonical : y.IsCanonical)
    (result : x.div y = .ok z) :
    z.IsCanonical ∧
      z.toCertificateField = x.toCertificateField / y.toCertificateField := by
  change (y.inv >>= fun yInv => Except.ok (x.mul yInv)) = Except.ok z at result
  generalize inverse_result : y.inv = inverse at result
  cases inverse with
  | error message =>
      change Except.error message = Except.ok z at result
      contradiction
  | ok yInv =>
      change Except.ok (x.mul yInv) = Except.ok z at result
      have z_eq : z = x.mul yInv := (Except.ok.inj result).symm
      subst z
      constructor
      · exact ExtElt.isCanonical_mul x yInv
      · rw [ExtElt.toCertificateField_mul,
          y.inv_toCertificateField y_canonical inverse_result]
        rfl

end KnuthFasc8aEx210
