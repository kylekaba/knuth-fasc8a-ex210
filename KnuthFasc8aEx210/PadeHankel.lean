import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Coprime.Basic
import KnuthFasc8aEx210.KrylovNonsingularity

/-!
# Padé/Bézout certificates for Hankel nonsingularity

A scalar Wiedemann sequence can certify full linear complexity without
trusting a Berlekamp--Massey implementation.  Its connection denominator `D`
and truncated numerator `R` determine a Padé approximation.  If a compact
Bézout witness proves `D` and `R` coprime, then any shorter recurrence would
force a polynomial of degree below `D` to be divisible by `D`, hence to vanish.

This file develops the polynomial core of that argument.  The later
certificate layer will construct `D`, `R`, and the Bézout witness from the
checked bytes.
-/

namespace KnuthFasc8aEx210

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

local instance : DecidableEq K := Classical.decEq K

/-- Two polynomials have identical coefficients below the exclusive bound
`n`; equivalently, they agree modulo `X^n`. -/
def CoeffEqBelow (p q : K[X]) (n : ℕ) : Prop :=
  ∀ k < n, p.coeff k = q.coeff k

namespace CoeffEqBelow

theorem refl (p : K[X]) (n : ℕ) : CoeffEqBelow p p n := by
  intro _ _
  rfl

theorem symm {p q : K[X]} {n : ℕ} (h : CoeffEqBelow p q n) :
    CoeffEqBelow q p n := by
  intro k hk
  exact (h k hk).symm

theorem trans {p q r : K[X]} {n : ℕ}
    (hpq : CoeffEqBelow p q n) (hqr : CoeffEqBelow q r n) :
    CoeffEqBelow p r n := by
  intro k hk
  exact (hpq k hk).trans (hqr k hk)

theorem mono {p q : K[X]} {m n : ℕ} (h : CoeffEqBelow p q n) (hmn : m ≤ n) :
    CoeffEqBelow p q m := by
  intro k hk
  exact h k (hk.trans_le hmn)

theorem mul_right {p q : K[X]} {n : ℕ} (h : CoeffEqBelow p q n)
    (r : K[X]) : CoeffEqBelow (p * r) (q * r) n := by
  intro k hk
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ij ij_mem
  have indices := Finset.mem_antidiagonal.mp ij_mem
  rw [h ij.1 (by omega)]

theorem mul_left {p q : K[X]} {n : ℕ} (h : CoeffEqBelow p q n)
    (r : K[X]) : CoeffEqBelow (r * p) (r * q) n := by
  simpa [mul_comm] using h.mul_right r

theorem eq_of_natDegree_lt {p q : K[X]} {n : ℕ}
    (h : CoeffEqBelow p q n) (p_degree : p.natDegree < n)
    (q_degree : q.natDegree < n) : p = q := by
  ext k
  by_cases k_lt : k < n
  · exact h k k_lt
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end CoeffEqBelow

/-- Keep exactly the coefficients below `n`. -/
def truncatePolynomial (n : ℕ) (p : K[X]) : K[X] :=
  ofFn n fun i => p.coeff i

@[simp]
theorem truncatePolynomial_coeff_of_lt (p : K[X]) {n k : ℕ} (k_lt : k < n) :
    (truncatePolynomial n p).coeff k = p.coeff k := by
  simp [truncatePolynomial, k_lt]

@[simp]
theorem truncatePolynomial_coeff_of_le (p : K[X]) {n k : ℕ} (n_le : n ≤ k) :
    (truncatePolynomial n p).coeff k = 0 := by
  exact ofFn_coeff_eq_zero_of_ge _ n_le

theorem truncatePolynomial_natDegree_lt (p : K[X]) {n : ℕ} (n_pos : 0 < n) :
    (truncatePolynomial n p).natDegree < n := by
  exact ofFn_natDegree_lt n_pos _

theorem coeffEqBelow_truncate (p : K[X]) (n : ℕ) :
    CoeffEqBelow p (truncatePolynomial n p) n := by
  intro k k_lt
  exact (truncatePolynomial_coeff_of_lt p k_lt).symm

/-- If all coefficients in `[base, precision)` vanish, truncation below
`base` agrees with the original polynomial throughout `precision`. -/
theorem coeffEqBelow_truncate_of_middle_zero (p : K[X]) (base precision : ℕ)
    (middle_zero : ∀ k, base ≤ k → k < precision → p.coeff k = 0) :
    CoeffEqBelow p (truncatePolynomial base p) precision := by
  intro k k_lt
  by_cases below : k < base
  · exact (truncatePolynomial_coeff_of_lt p below).symm
  · rw [middle_zero k (Nat.le_of_not_gt below) k_lt,
      truncatePolynomial_coeff_of_le p (Nat.le_of_not_gt below)]

/-- Polynomial containing the first `terms` scalar moments. -/
def momentPolynomial (moment : ℕ → K) (terms : ℕ) : K[X] :=
  ofFn terms fun i => moment i

@[simp]
theorem momentPolynomial_coeff_of_lt (moment : ℕ → K) {terms k : ℕ}
    (k_lt : k < terms) :
    (momentPolynomial moment terms).coeff k = moment k := by
  simp [momentPolynomial, k_lt]

@[simp]
theorem momentPolynomial_coeff_of_le (moment : ℕ → K) {terms k : ℕ}
    (terms_le : terms ≤ k) :
    (momentPolynomial moment terms).coeff k = 0 := by
  exact ofFn_coeff_eq_zero_of_ge _ terms_le

/-- The Padé denominator uses the certificate's stored order directly:
`[1,c₁,...,c_N]` is the ascending coefficient vector of `D`. -/
def certificateDenominator (degree : ℕ) (coefficient : ℕ → K) : K[X] :=
  ofFn (degree + 1) fun i => coefficient i

@[simp]
theorem certificateDenominator_coeff_of_le (degree : ℕ) (coefficient : ℕ → K)
    {i : ℕ} (i_le : i ≤ degree) :
    (certificateDenominator degree coefficient).coeff i = coefficient i := by
  simp [certificateDenominator, Nat.lt_succ_of_le i_le]

theorem certificateDenominator_natDegree_eq (degree : ℕ) (coefficient : ℕ → K)
    (last_ne_zero : coefficient degree ≠ 0) :
    (certificateDenominator degree coefficient).natDegree = degree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact Nat.lt_succ_iff.mp (ofFn_natDegree_lt (by omega) _)
  · simpa using last_ne_zero

/-- Coefficients in the recurrence window of `S*D` are exactly the stored
descending recurrence sums. -/
theorem coeff_momentPolynomial_mul_certificateDenominator
    (moment : ℕ → K) (degree : ℕ) (coefficient : ℕ → K) (row : Fin degree) :
    (momentPolynomial moment (2 * degree) *
        certificateDenominator degree coefficient).coeff (degree + row) =
      ∑ i ∈ Finset.range (degree + 1),
        coefficient (degree - i) * moment (row + i) := by
  let total := degree + row.val
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ i ∈ Finset.range (total + 1),
      (certificateDenominator degree coefficient).coeff i *
        (momentPolynomial moment (2 * degree)).coeff (total - i)) = _
  have range_subset : Finset.range (degree + 1) ⊆ Finset.range (total + 1) :=
    Finset.range_mono (by dsimp [total]; omega)
  rw [← Finset.sum_subset range_subset]
  · rw [← Fin.sum_univ_eq_sum_range]
    rw [← Equiv.sum_comp Fin.revPerm]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Fintype.sum_congr
    intro i
    have reverse_value : (Fin.revPerm i).val = degree - i.val := by
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    have moment_index : total - (Fin.revPerm i).val = row.val + i.val := by
      dsimp [total]
      rw [reverse_value]
      omega
    have moment_index' : total - (degree - i.val) = row.val + i.val := by
      rw [← reverse_value]
      exact moment_index
    rw [certificateDenominator_coeff_of_le]
    · rw [momentPolynomial_coeff_of_lt]
      · rw [reverse_value, moment_index']
      · rw [moment_index]
        omega
    · omega
  · intro i i_mem i_not_mem
    have degree_lt : degree < i := by
      simpa [Finset.mem_range, not_lt] using i_not_mem
    rw [certificateDenominator,
      ofFn_coeff_eq_zero_of_ge (fun j : Fin (degree + 1) => coefficient j)
        (by omega), zero_mul]

/-- Encode a vector as a polynomial in ascending coordinate order. -/
def vectorPolynomial (degree : ℕ) (v : Fin degree → K) : K[X] :=
  ofFn degree v

/-- Reverse a vector polynomial around the fixed index `degree - 1`. -/
def reversedVectorPolynomial (degree : ℕ) (v : Fin degree → K) : K[X] :=
  (vectorPolynomial degree v).reflect (degree - 1)

theorem reversedVectorPolynomial_natDegree_lt {degree : ℕ} (degree_pos : 0 < degree)
    (v : Fin degree → K) :
    (reversedVectorPolynomial degree v).natDegree < degree := by
  have vector_degree : (vectorPolynomial degree v).natDegree < degree := by
    exact ofFn_natDegree_lt degree_pos _
  calc
    (reversedVectorPolynomial degree v).natDegree ≤
        max (degree - 1) (vectorPolynomial degree v).natDegree :=
      natDegree_reflect_le
    _ < degree := by omega

theorem reversedVectorPolynomial_eq_zero_iff {degree : ℕ} (v : Fin degree → K) :
    reversedVectorPolynomial degree v = 0 ↔ v = 0 := by
  rw [reversedVectorPolynomial, reflect_eq_zero_iff]
  constructor
  · intro vector_zero
    apply Polynomial.injective_ofFn degree
    simpa [vectorPolynomial] using vector_zero
  · rintro rfl
    simp [vectorPolynomial]

theorem reversedVectorPolynomial_coeff_of_le {degree i : ℕ}
    (degree_pos : 0 < degree) (v : Fin degree → K) (degree_le : degree ≤ i) :
    (reversedVectorPolynomial degree v).coeff i = 0 := by
  rw [reversedVectorPolynomial, coeff_reflect]
  rw [revAt_eq_self_of_lt (by omega)]
  exact ofFn_coeff_eq_zero_of_ge _ degree_le

/-- The middle coefficient of the moment polynomial times a reversed vector
is exactly the corresponding Hankel matrix row. -/
theorem coeff_momentPolynomial_mul_reversedVectorPolynomial
    (moment : ℕ → K) {degree : ℕ} (degree_pos : 0 < degree)
    (v : Fin degree → K) (row : Fin degree) :
    (momentPolynomial moment (2 * degree) *
        reversedVectorPolynomial degree v).coeff (degree - 1 + row) =
      ∑ j : Fin degree, moment (row + j) * v j := by
  let total := degree - 1 + row.val
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ i ∈ Finset.range (total + 1),
      (reversedVectorPolynomial degree v).coeff i *
        (momentPolynomial moment (2 * degree)).coeff (total - i)) = _
  have range_subset : Finset.range degree ⊆ Finset.range (total + 1) :=
    Finset.range_mono (by dsimp [total]; omega)
  rw [← Finset.sum_subset range_subset]
  · rw [← Fin.sum_univ_eq_sum_range]
    rw [← Equiv.sum_comp Fin.revPerm]
    apply Fintype.sum_congr
    intro i
    have reverse_index : degree - 1 - (Fin.revPerm i).val = i.val := by
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    have moment_index : total - (Fin.revPerm i).val = row.val + i.val := by
      dsimp [total]
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    rw [reversedVectorPolynomial, coeff_reflect]
    rw [revAt_le (by omega)]
    rw [vectorPolynomial,
      Polynomial.ofFn_coeff_eq_val_of_lt v (by omega)]
    have fin_index :
        (⟨degree - 1 - (Fin.revPerm i).val, by omega⟩ : Fin degree) = i := by
      exact Fin.ext reverse_index
    rw [fin_index]
    rw [momentPolynomial_coeff_of_lt]
    · rw [mul_comm]
      rw [moment_index]
    · dsimp [total]
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
  · intro i i_mem i_not_mem
    have degree_le : degree ≤ i := by
      simpa [Finset.mem_range, not_lt] using i_not_mem
    rw [reversedVectorPolynomial_coeff_of_le degree_pos v degree_le, zero_mul]

theorem middle_coeff_zero_of_hankel_kernel
    (moment : ℕ → K) {degree : ℕ} (degree_pos : 0 < degree)
    (v : Fin degree → K)
    (kernel : Matrix.toLin' (momentHankelMatrix moment degree) v = 0) :
    ∀ k, degree - 1 ≤ k → k < 2 * degree - 1 →
      (momentPolynomial moment (2 * degree) *
        reversedVectorPolynomial degree v).coeff k = 0 := by
  intro k lower upper
  let row : Fin degree := ⟨k - (degree - 1), by omega⟩
  have row_zero := congrFun kernel row
  rw [Matrix.toLin'_apply] at row_zero
  have row_sum_zero : (∑ j : Fin degree, moment (row + j) * v j) = 0 := by
    simpa [momentHankelMatrix, Matrix.mulVec, dotProduct] using row_zero
  rw [show k = degree - 1 + row.val by dsimp [row]; omega]
  rw [coeff_momentPolynomial_mul_reversedVectorPolynomial
    moment degree_pos v row]
  exact row_sum_zero

/-- Polynomial heart of the Padé argument.  The two congruences say that the
same truncated series has denominator/numerator pair `(D,R)` and a putative
shorter pair `(E,Q)`.  Coprimality of `D,R` forces `D ∣ E`; if `E` has lower
degree than monic `D`, it must be zero. -/
theorem shorter_pade_denominator_eq_zero
    {S D R E Q : K[X]} {precision fullPrecision degree : ℕ}
    (precision_le : precision ≤ fullPrecision)
    (SD_R : CoeffEqBelow (S * D) R fullPrecision)
    (SE_Q : CoeffEqBelow (S * E) Q precision)
    (RE_degree : (R * E).natDegree < precision)
    (QD_degree : (Q * D).natDegree < precision)
    (D_degree : D.natDegree = degree)
    (E_degree : E.natDegree < degree)
    (coprime : IsCoprime D R) :
    E = 0 := by
  have SDE_RE : CoeffEqBelow ((S * D) * E) (R * E) precision :=
    (SD_R.mul_right E).mono precision_le
  have SED_QD : CoeffEqBelow ((S * E) * D) (Q * D) precision :=
    SE_Q.mul_right D
  have RE_QD : CoeffEqBelow (R * E) (Q * D) precision := by
    apply SDE_RE.symm.trans
    · simpa [mul_assoc, mul_left_comm, mul_comm] using SED_QD
  have products_equal : R * E = Q * D :=
    RE_QD.eq_of_natDegree_lt RE_degree QD_degree
  have D_dvd_RE : D ∣ R * E := by
    use Q
    simpa [mul_comm] using products_equal
  have D_dvd_E : D ∣ E := coprime.dvd_of_dvd_mul_left D_dvd_RE
  by_contra E_ne_zero
  exact (Polynomial.not_dvd_of_natDegree_lt E_ne_zero
    (by simpa [D_degree] using E_degree)) D_dvd_E

/-- Certificate-oriented Padé theorem.  `R` and `Q` are not trusted inputs:
they are defined as low truncations of `S*D` and `S*E`.  Vanishing of the
middle coefficients gives the two Padé congruences, while the displayed
Bézout identity certifies coprimality. -/
theorem shorter_denominator_eq_zero_of_bezout
    {S D E U V : K[X]} {degree : ℕ}
    (degree_gt_one : 1 < degree)
    (D_degree : D.natDegree = degree)
    (E_degree : E.natDegree < degree)
    (SD_middle_zero : ∀ k, degree ≤ k → k < 2 * degree →
      (S * D).coeff k = 0)
    (SE_middle_zero : ∀ k, degree - 1 ≤ k → k < 2 * degree - 1 →
      (S * E).coeff k = 0)
    (bezout : U * D + V * truncatePolynomial degree (S * D) = 1) :
    E = 0 := by
  let R := truncatePolynomial degree (S * D)
  let Q := truncatePolynomial (degree - 1) (S * E)
  have R_degree : R.natDegree < degree := by
    exact truncatePolynomial_natDegree_lt _ (by omega)
  have Q_degree : Q.natDegree < degree - 1 := by
    exact truncatePolynomial_natDegree_lt _ (by omega)
  have RE_degree : (R * E).natDegree < 2 * degree - 1 := by
    calc
      (R * E).natDegree ≤ R.natDegree + E.natDegree := natDegree_mul_le
      _ < 2 * degree - 1 := by omega
  have QD_degree : (Q * D).natDegree < 2 * degree - 1 := by
    calc
      (Q * D).natDegree ≤ Q.natDegree + D.natDegree := natDegree_mul_le
      _ < 2 * degree - 1 := by omega
  apply shorter_pade_denominator_eq_zero
    (precision := 2 * degree - 1) (fullPrecision := 2 * degree)
    (degree := degree) (S := S) (D := D) (R := R) (E := E) (Q := Q)
  · omega
  · exact coeffEqBelow_truncate_of_middle_zero _ degree (2 * degree)
      SD_middle_zero
  · exact coeffEqBelow_truncate_of_middle_zero _ (degree - 1)
      (2 * degree - 1) SE_middle_zero
  · exact RE_degree
  · exact QD_degree
  · exact D_degree
  · exact E_degree
  · exact ⟨U, V, by simpa [R] using bezout⟩

/-- A checked Padé/Bézout identity plus the stored full recurrence proves the
moment Hankel matrix injective. -/
theorem hankel_injective_of_bezout
    (moment : ℕ → K) {degree : ℕ} (degree_gt_one : 1 < degree)
    {D U V : K[X]}
    (D_degree : D.natDegree = degree)
    (recurrence_middle_zero : ∀ k, degree ≤ k → k < 2 * degree →
      (momentPolynomial moment (2 * degree) * D).coeff k = 0)
    (bezout : U * D +
      V * truncatePolynomial degree
        (momentPolynomial moment (2 * degree) * D) = 1) :
    Function.Injective (Matrix.toLin' (momentHankelMatrix moment degree)) := by
  have kernel_vector_zero : ∀ v : Fin degree → K,
      Matrix.toLin' (momentHankelMatrix moment degree) v = 0 → v = 0 := by
    intro v kernel
    let E := reversedVectorPolynomial degree v
    have E_degree : E.natDegree < degree :=
      reversedVectorPolynomial_natDegree_lt (by omega) v
    have E_zero : E = 0 := by
      apply shorter_denominator_eq_zero_of_bezout
        (S := momentPolynomial moment (2 * degree)) (D := D)
        (E := E) (U := U) (V := V) degree_gt_one D_degree E_degree
      · exact recurrence_middle_zero
      · exact middle_coeff_zero_of_hankel_kernel moment (by omega) v kernel
      · exact bezout
    exact (reversedVectorPolynomial_eq_zero_iff v).mp E_zero
  intro x y same_image
  apply sub_eq_zero.mp
  apply kernel_vector_zero (x - y)
  rw [map_sub, same_image, sub_self]

/-- End-to-end algebraic rank-certificate interface.  It consumes the stored
moment recurrence, its nonzero constant coefficient, and a checked Bézout
identity, then proves the represented endomorphism nonsingular. -/
theorem injective_of_padeBezout_descendingConnection
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (u : W →ₗ[K] K) (A : Module.End K W) (w : W) (degree : ℕ)
    (degree_gt_one : 1 < degree)
    (dimension : Module.finrank K W = degree)
    (coefficient : ℕ → K) (leading : coefficient 0 = 1)
    (recurrence : ∀ k < degree,
      ∑ i ∈ Finset.range (degree + 1),
        coefficient (degree - i) * scalarKrylovMoment u A w (k + i) = 0)
    (constant_ne_zero : coefficient degree ≠ 0)
    (U V : K[X])
    (bezout : U * certificateDenominator degree coefficient +
      V * truncatePolynomial degree
        (momentPolynomial (scalarKrylovMoment u A w) (2 * degree) *
          certificateDenominator degree coefficient) = 1) :
    Function.Injective A := by
  have denominator_degree :
      (certificateDenominator degree coefficient).natDegree = degree :=
    certificateDenominator_natDegree_eq degree coefficient constant_ne_zero
  have recurrence_middle_zero : ∀ k, degree ≤ k → k < 2 * degree →
      (momentPolynomial (scalarKrylovMoment u A w) (2 * degree) *
        certificateDenominator degree coefficient).coeff k = 0 := by
    intro k lower upper
    let row : Fin degree := ⟨k - degree, by omega⟩
    rw [show k = degree + row.val by dsimp [row]; omega]
    rw [coeff_momentPolynomial_mul_certificateDenominator]
    exact recurrence row row.isLt
  have hankel_injective : Function.Injective
      (Matrix.toLin'
        (momentHankelMatrix (scalarKrylovMoment u A w) degree)) :=
    hankel_injective_of_bezout (scalarKrylovMoment u A w) degree_gt_one
      denominator_degree recurrence_middle_zero bezout
  exact injective_of_hankel_and_descendingConnection
    u A w degree (by omega) dimension hankel_injective coefficient leading
    recurrence constant_ne_zero

end

end KnuthFasc8aEx210
