import Mathlib.LinearAlgebra.FiniteDimensional.Basic
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

/-- One row of the parsed CSR matrix acting on a field vector.  Malformed
column indices contribute zero; the parser's CSR validation later rules them
out. -/
def csrApplyField (matrixBytes : ByteArray) (header : MatrixHeader)
    (x : Fin header.n → CertificateField) (row : Fin header.n) :
    CertificateField :=
  ∑ entry ∈ Finset.range header.entries,
    if matrixRowStart matrixBytes header row ≤ entry ∧
        entry < matrixRowStop matrixBytes header row then
      if h : matrixColumnAt matrixBytes header entry < header.n then
        algebraMap (ZMod 101) CertificateField
            (matrixValueAt matrixBytes header entry) *
          x ⟨matrixColumnAt matrixBytes header entry, h⟩
      else 0
    else 0

/-- Mathematical linear operator represented by a parsed CSR matrix. -/
def csrLinearMap (matrixBytes : ByteArray) (header : MatrixHeader) :
    Module.End CertificateField (Fin header.n → CertificateField) where
  toFun x := csrApplyField matrixBytes header x
  map_add' x y := by
    funext row
    classical
    simp only [csrApplyField, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro entry entry_mem
    split_ifs <;> simp_all [mul_add]
  map_smul' c x := by
    funext row
    classical
    simp only [csrApplyField, Pi.smul_apply, RingHom.id_apply]
    change _ = c * _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro entry entry_mem
    split_ifs <;> simp_all
    ring

/-- The shifted operator `M - 50 I` used by every rank certificate. -/
def shiftedCSRLinearMap (matrixBytes : ByteArray) (header : MatrixHeader) :
    Module.End CertificateField (Fin header.n → CertificateField) :=
  csrLinearMap matrixBytes header -
    (50 : CertificateField) • LinearMap.id

/-- Pointwise diagonal multiplication by an encoded field vector. -/
def encodedDiagonalLinearMap (diagonal : ByteArray) (n : ℕ) :
    Module.End CertificateField (Fin n → CertificateField) where
  toFun x i := encodedVector diagonal n i * x i
  map_add' x y := by
    funext i
    simp [mul_add]
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

/-- Normal-certificate operator `D_L (M - 50 I) D_R`. -/
def preconditionedCSRLinearMap (matrixBytes : ByteArray) (header : MatrixHeader)
    (dR dL : ByteArray) :
    Module.End CertificateField (Fin header.n → CertificateField) :=
  (encodedDiagonalLinearMap dL header.n).comp
    ((shiftedCSRLinearMap matrixBytes header).comp
      (encodedDiagonalLinearMap dR header.n))

/-- Linear functional represented by the encoded Wiedemann probe vector. -/
def encodedProbeLinearMap (probe : ByteArray) (n : ℕ) :
    (Fin n → CertificateField) →ₗ[CertificateField] CertificateField where
  toFun x := ∑ i, encodedVector probe n i * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    change (∑ i, encodedVector probe n i * (c * x i)) =
      c * ∑ i, encodedVector probe n i * x i
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    ring

theorem extDotBytes_eq_encodedProbe
    (probe x : ByteArray) (n : ℕ) :
    (extDotBytes probe x n).toCertificateField =
      encodedProbeLinearMap probe n (encodedVector x n) := by
  exact extDotBytes_toCertificateField probe x n

end

end KnuthFasc8aEx210
