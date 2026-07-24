import KnuthFasc8aEx210.CertificateFieldEncoding

/-!
# Soundness of encoded matrix-certificate operations

This file begins the bridge from executable Krylov replay to a mathematical
linear operator over `CertificateField`.
-/

namespace KnuthFasc8aEx210

noncomputable section

/-- Interpret `n` consecutive byte pairs as a vector over the certificate
field. -/
def encodedVector (bytes : ByteArray) (n : ℕ) : Fin n → CertificateField :=
  fun i => (pairAt bytes i).toCertificateField

private theorem extDotByteSums_eq (u x : ByteArray) (n : ℕ) :
    extDotByteSums u x n =
      (∑ i ∈ Finset.range n, (
          (pairAt u i).a.toNat * (pairAt x i).a.toNat +
            2 * (pairAt u i).b.toNat * (pairAt x i).b.toNat),
        ∑ i ∈ Finset.range n, (
          (pairAt u i).a.toNat * (pairAt x i).b.toNat +
            (pairAt u i).b.toNat * (pairAt x i).a.toNat)) := by
  induction n with
  | zero => simp [extDotByteSums]
  | succ n ih =>
      rw [extDotByteSums, ih]
      simp only [Finset.sum_range_succ]
      simp [pairAt, Nat.add_assoc]

private theorem certificatePair_finset_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (real imag : α → ZMod 101) :
    certificatePair (∑ i ∈ s, real i) (∑ i ∈ s, imag i) =
      ∑ i ∈ s, certificatePair (real i) (imag i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s i_not_mem ih =>
      simp only [Finset.sum_insert i_not_mem]
      rw [certificatePair_add, ih]

/-- The byte dot product used for every stored Krylov moment is the ordinary
dot product of the interpreted field vectors. -/
theorem extDotBytes_toCertificateField (u x : ByteArray) (n : ℕ) :
    (extDotBytes u x n).toCertificateField =
      ∑ i : Fin n, encodedVector u n i * encodedVector x n i := by
  rw [ExtElt.toCertificateField]
  simp only [extDotBytes]
  rw [extDotByteSums_eq]
  rw [zmod101_of_u8Mod101, zmod101_of_u8Mod101]
  push_cast
  rw [certificatePair_finset_sum, ← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro i
  rw [encodedVector, encodedVector,
    ExtElt.toCertificateField, ExtElt.toCertificateField,
    certificatePair_mul]

end

end KnuthFasc8aEx210
