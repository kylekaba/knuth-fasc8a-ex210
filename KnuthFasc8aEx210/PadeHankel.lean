import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Coprime.Basic

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
    (D_monic : D.Monic) (D_degree : D.natDegree = degree)
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
  exact (Polynomial.Monic.not_dvd_of_natDegree_lt D_monic E_ne_zero
    (by simpa [D_degree] using E_degree)) D_dvd_E

/-- Certificate-oriented Padé theorem.  `R` and `Q` are not trusted inputs:
they are defined as low truncations of `S*D` and `S*E`.  Vanishing of the
middle coefficients gives the two Padé congruences, while the displayed
Bézout identity certifies coprimality. -/
theorem shorter_denominator_eq_zero_of_bezout
    {S D E U V : K[X]} {degree : ℕ}
    (degree_gt_one : 1 < degree)
    (D_monic : D.Monic) (D_degree : D.natDegree = degree)
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
  · exact D_monic
  · exact D_degree
  · exact E_degree
  · exact ⟨U, V, by simpa [R] using bezout⟩

end

end KnuthFasc8aEx210
