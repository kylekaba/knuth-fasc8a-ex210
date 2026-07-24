import KnuthFasc8aEx210.CertificateFieldEncoding
import KnuthFasc8aEx210.PadeHankel

/-!
# Soundness of the concrete Padé certificate representation

This file connects byte-pair coefficient arrays and the executable
convolution checker to ordinary polynomials over `CertificateField`.
-/

namespace KnuthFasc8aEx210

open Polynomial

noncomputable section

local instance : DecidableEq CertificateField := Classical.decEq _

/-- Interpret the first `length` encoded pairs as an ascending polynomial. -/
def encodedPolynomial (coefficient : ℕ → ExtElt) (length : ℕ) :
    CertificateField[X] :=
  ofFn length fun i => (coefficient i).toCertificateField

@[simp]
theorem encodedPolynomial_coeff_of_lt
    (coefficient : ℕ → ExtElt) {length k : ℕ} (k_lt : k < length) :
    (encodedPolynomial coefficient length).coeff k =
      (coefficient k).toCertificateField := by
  simp [encodedPolynomial, k_lt]

@[simp]
theorem encodedPolynomial_coeff_of_le
    (coefficient : ℕ → ExtElt) {length k : ℕ} (length_le : length ≤ k) :
    (encodedPolynomial coefficient length).coeff k = 0 := by
  exact ofFn_coeff_eq_zero_of_ge _ length_le

theorem encodedPolynomial_coeff
    (coefficient : ℕ → ExtElt) (length k : ℕ) :
    (encodedPolynomial coefficient length).coeff k =
      if k < length then (coefficient k).toCertificateField else 0 := by
  split_ifs with k_lt
  · exact encodedPolynomial_coeff_of_lt coefficient k_lt
  · exact encodedPolynomial_coeff_of_le coefficient (Nat.le_of_not_gt k_lt)

/-- The executable convolution is exactly polynomial coefficient extraction. -/
theorem extConvolutionCoefficient_eq_coeff_mul
    (left right : ℕ → ExtElt) (leftLength rightLength k : ℕ) :
    (extConvolutionCoefficient left leftLength right rightLength k).toCertificateField =
      (encodedPolynomial left leftLength *
        encodedPolynomial right rightLength).coeff k := by
  classical
  rw [extConvolutionCoefficient_toCertificateField, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Finset.sum_filter]
  simp_rw [encodedPolynomial_coeff]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro i i_mem
    rfl

def RankCertificateFile.denominatorPolynomial
    (cert : RankCertificateFile) : CertificateField[X] :=
  encodedPolynomial (pairAt cert.coefficients) (cert.degree + 1)

def RankCertificateFile.fieldCoefficient
    (cert : RankCertificateFile) (i : ℕ) : CertificateField :=
  (pairAt cert.coefficients i).toCertificateField

def RankCertificateFile.fieldMoment
    (cert : RankCertificateFile) (i : ℕ) : CertificateField :=
  (pairAt cert.moments i).toCertificateField

def RankCertificateFile.storedMomentPolynomial
    (cert : RankCertificateFile) : CertificateField[X] :=
  encodedPolynomial (pairAt cert.moments) cert.bmTerms

def RankCertificateFile.padeNumeratorPolynomial
    (cert : RankCertificateFile) : CertificateField[X] :=
  encodedPolynomial cert.padeNumeratorCoefficient cert.degree

def PadeWitnessFile.uPolynomial
    (witness : PadeWitnessFile) : CertificateField[X] :=
  encodedPolynomial (pairAt witness.uCoefficients) witness.uLength

def PadeWitnessFile.vPolynomial
    (witness : PadeWitnessFile) : CertificateField[X] :=
  encodedPolynomial (pairAt witness.vCoefficients) witness.vLength

/-- Recomputing each low numerator coefficient is the same as truncating the
product of the stored denominator and moment polynomials. -/
theorem RankCertificateFile.padeNumeratorPolynomial_eq
    (cert : RankCertificateFile) :
    cert.padeNumeratorPolynomial =
      truncatePolynomial cert.degree
        (cert.denominatorPolynomial * cert.storedMomentPolynomial) := by
  ext k
  by_cases k_lt : k < cert.degree
  · rw [RankCertificateFile.padeNumeratorPolynomial,
      encodedPolynomial_coeff_of_lt _ k_lt,
      RankCertificateFile.padeNumeratorCoefficient,
      extConvolutionCoefficient_eq_coeff_mul,
      truncatePolynomial_coeff_of_lt _ k_lt]
    rfl
  · rw [RankCertificateFile.padeNumeratorPolynomial,
      encodedPolynomial_coeff_of_le _ (Nat.le_of_not_gt k_lt),
      truncatePolynomial_coeff_of_le _ (Nat.le_of_not_gt k_lt)]

theorem RankCertificateFile.denominatorPolynomial_eq
    (cert : RankCertificateFile) :
    cert.denominatorPolynomial =
      certificateDenominator cert.degree cert.fieldCoefficient := by
  rfl

theorem RankCertificateFile.storedMomentPolynomial_eq
    (cert : RankCertificateFile) (bm_terms : cert.bmTerms = 2 * cert.degree) :
    cert.storedMomentPolynomial =
      momentPolynomial cert.fieldMoment (2 * cert.degree) := by
  simp only [RankCertificateFile.storedMomentPolynomial, encodedPolynomial,
    momentPolynomial, RankCertificateFile.fieldMoment]
  rw [bm_terms]

/-- The checked recurrence coefficient is the corresponding coefficient of
the interpreted denominator/moment product. -/
theorem RankCertificateFile.recurrenceCoefficient_toCertificateField
    (cert : RankCertificateFile) (n : ℕ) :
    (cert.recurrenceCoefficient n).toCertificateField =
      (cert.denominatorPolynomial *
        encodedPolynomial (pairAt cert.moments) cert.terms).coeff n := by
  exact extConvolutionCoefficient_eq_coeff_mul _ _ _ _ _

/-- A zero full-recurrence mismatch count forces every tested encoded
coefficient to pass the executable zero test. -/
theorem RankCertificateFile.recurrenceCoefficient_isZero_of_fullRecurrenceBad_eq_zero
    (cert : RankCertificateFile) (no_bad : cert.fullRecurrenceBad = 0)
    {offset : ℕ} (offset_lt : offset < cert.bmTerms - cert.degree) :
    (cert.recurrenceCoefficient (cert.degree + offset)).isZero = true := by
  rw [RankCertificateFile.fullRecurrenceBad] at no_bad
  have filtered_nil := List.length_eq_zero_iff.mp no_bad
  by_contra mismatch
  have zero_test_false :
      (cert.recurrenceCoefficient (cert.degree + offset)).isZero = false :=
    Bool.eq_false_of_not_eq_true mismatch
  have bad_mem : offset ∈
      (List.range (cert.bmTerms - cert.degree)).filter (fun i =>
        (cert.recurrenceCoefficient (cert.degree + i)).isZero != true) := by
    simp [offset_lt, zero_test_false]
  rw [filtered_nil] at bad_mem
  simp at bad_mem

/-- A checked recurrence coefficient is zero in the mathematical extension
field.  Canonicality is supplied by the modular convolution implementation. -/
theorem RankCertificateFile.recurrenceCoefficient_toCertificateField_eq_zero
    (cert : RankCertificateFile) (no_bad : cert.fullRecurrenceBad = 0)
    {offset : ℕ} (offset_lt : offset < cert.bmTerms - cert.degree) :
    (cert.recurrenceCoefficient (cert.degree + offset)).toCertificateField = 0 := by
  apply (ExtElt.toCertificateField_eq_zero_iff _
    (ExtElt.isCanonical_extConvolutionCoefficient _ _ _ _ _)).2
  exact cert.recurrenceCoefficient_isZero_of_fullRecurrenceBad_eq_zero
    no_bad offset_lt

/-- The exact all-rows executable check supplies the stored descending
recurrence premise expected by the Padé/Krylov injectivity proof. -/
theorem RankCertificateFile.stored_recurrence_of_fullRecurrenceBad_eq_zero
    (cert : RankCertificateFile)
    (bm_terms : cert.bmTerms = 2 * cert.degree)
    (bm_terms_le : cert.bmTerms ≤ cert.terms)
    (no_bad : cert.fullRecurrenceBad = 0) :
    ∀ k < cert.degree,
      ∑ i ∈ Finset.range (cert.degree + 1),
        cert.fieldCoefficient (cert.degree - i) * cert.fieldMoment (k + i) = 0 := by
  intro k k_lt
  have encoded_below :
      CoeffEqBelow (encodedPolynomial (pairAt cert.moments) cert.terms)
        (momentPolynomial cert.fieldMoment (2 * cert.degree))
        (2 * cert.degree) := by
    intro j j_lt
    rw [encodedPolynomial_coeff_of_lt _
      (j_lt.trans_le (bm_terms ▸ bm_terms_le)),
      momentPolynomial_coeff_of_lt _ j_lt]
    rfl
  have products_below := encoded_below.mul_left cert.denominatorPolynomial
  have offset_lt : k < cert.bmTerms - cert.degree := by
    omega
  have checked_zero :
      (cert.denominatorPolynomial *
        encodedPolynomial (pairAt cert.moments) cert.terms).coeff
          (cert.degree + k) = 0 := by
    rw [← cert.recurrenceCoefficient_toCertificateField]
    exact cert.recurrenceCoefficient_toCertificateField_eq_zero no_bad offset_lt
  let row : Fin cert.degree := ⟨k, k_lt⟩
  calc
    (∑ i ∈ Finset.range (cert.degree + 1),
        cert.fieldCoefficient (cert.degree - i) * cert.fieldMoment (k + i)) =
        (momentPolynomial cert.fieldMoment (2 * cert.degree) *
          certificateDenominator cert.degree cert.fieldCoefficient).coeff
            (cert.degree + row) := by
              symm
              exact coeff_momentPolynomial_mul_certificateDenominator
                cert.fieldMoment cert.degree cert.fieldCoefficient row
    _ = (cert.denominatorPolynomial *
          momentPolynomial cert.fieldMoment (2 * cert.degree)).coeff
            (cert.degree + k) := by
              simp [row, cert.denominatorPolynomial_eq, mul_comm]
    _ = (cert.denominatorPolynomial *
          encodedPolynomial (pairAt cert.moments) cert.terms).coeff
            (cert.degree + k) := by
              exact (products_below (cert.degree + k) (by omega)).symm
    _ = 0 := checked_zero

/-- One executable Bézout coefficient is the matching coefficient of the
interpreted polynomial expression. -/
theorem PadeWitnessFile.bezoutCoefficient_toCertificateField
    (witness : PadeWitnessFile) (cert : RankCertificateFile) (k : ℕ) :
    (witness.bezoutCoefficient cert k).toCertificateField =
      (witness.uPolynomial * cert.denominatorPolynomial +
        witness.vPolynomial * cert.padeNumeratorPolynomial).coeff k := by
  rw [PadeWitnessFile.bezoutCoefficient, ExtElt.toCertificateField_add,
    extConvolutionCoefficient_eq_coeff_mul,
    extConvolutionCoefficient_eq_coeff_mul, coeff_add]
  rfl

@[simp]
theorem padeBezoutExpected_toCertificateField (k : ℕ) :
    (padeBezoutExpected k).toCertificateField =
      (1 : CertificateField[X]).coeff k := by
  by_cases k_zero : k = 0
  · subst k
    simp [padeBezoutExpected, ExtElt.toCertificateField, certificatePair]
  · rw [coeff_one]
    simp [padeBezoutExpected, k_zero, ExtElt.toCertificateField,
      certificatePair]

theorem PadeWitnessFile.bezoutCoefficient_eq_expected_of_bad_eq_zero
    (witness : PadeWitnessFile) (cert : RankCertificateFile)
    (no_bad : witness.bezoutBad cert = 0) {k : ℕ}
    (k_lt : k < 2 * cert.degree) :
    witness.bezoutCoefficient cert k = padeBezoutExpected k := by
  by_contra mismatch
  have k_mem : k ∈ List.range (2 * cert.degree) := by
    simpa using k_lt
  have bad_mem : k ∈ (List.range (2 * cert.degree)).filter (fun i =>
      witness.bezoutCoefficient cert i != padeBezoutExpected i) := by
    simp [k_mem, mismatch]
  have bad_pos : 0 < witness.bezoutBad cert := by
    rw [PadeWitnessFile.bezoutBad]
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem bad_mem)
  omega

theorem encodedPolynomial_natDegree_lt_of_length_le
    (coefficient : ℕ → ExtElt) {length bound : ℕ}
    (bound_pos : 0 < bound) (length_le : length ≤ bound) :
    (encodedPolynomial coefficient length).natDegree < bound := by
  by_cases length_zero : length = 0
  · subst length
    simp [encodedPolynomial, bound_pos]
  · exact (ofFn_natDegree_lt (Nat.pos_of_ne_zero length_zero) _).trans_le length_le

/-- A zero mismatch count proves the complete polynomial Bézout identity,
not merely the checked coefficient prefix.  The length bounds show that the
entire left side has degree below the checked `2 * degree` range. -/
theorem PadeWitnessFile.bezoutIdentity_of_bad_eq_zero
    (witness : PadeWitnessFile) (cert : RankCertificateFile)
    (degree_pos : 0 < cert.degree)
    (u_length_le : witness.uLength ≤ cert.degree)
    (v_length_le : witness.vLength ≤ cert.degree)
    (no_bad : witness.bezoutBad cert = 0) :
    witness.uPolynomial * cert.denominatorPolynomial +
      witness.vPolynomial *
        truncatePolynomial cert.degree
          (cert.storedMomentPolynomial * cert.denominatorPolynomial) = 1 := by
  let U := witness.uPolynomial
  let V := witness.vPolynomial
  let D := cert.denominatorPolynomial
  let R := cert.padeNumeratorPolynomial
  have U_degree : U.natDegree < cert.degree := by
    exact encodedPolynomial_natDegree_lt_of_length_le _ degree_pos u_length_le
  have V_degree : V.natDegree < cert.degree := by
    exact encodedPolynomial_natDegree_lt_of_length_le _ degree_pos v_length_le
  have D_degree : D.natDegree < cert.degree + 1 := by
    exact encodedPolynomial_natDegree_lt_of_length_le _ (by omega) le_rfl
  have R_degree : R.natDegree < cert.degree := by
    dsimp only [R]
    rw [RankCertificateFile.padeNumeratorPolynomial_eq]
    exact truncatePolynomial_natDegree_lt _ degree_pos
  have UD_degree : (U * D).natDegree < 2 * cert.degree := by
    calc
      (U * D).natDegree ≤ U.natDegree + D.natDegree := natDegree_mul_le
      _ < 2 * cert.degree := by omega
  have VR_degree : (V * R).natDegree < 2 * cert.degree := by
    calc
      (V * R).natDegree ≤ V.natDegree + R.natDegree := natDegree_mul_le
      _ < 2 * cert.degree := by omega
  have lhs_degree : (U * D + V * R).natDegree < 2 * cert.degree :=
    (natDegree_add_le _ _).trans_lt (max_lt UD_degree VR_degree)
  have rhs_degree : (1 : CertificateField[X]).natDegree < 2 * cert.degree := by
    simp
    omega
  have below : CoeffEqBelow (U * D + V * R) 1 (2 * cert.degree) := by
    intro k k_lt
    rw [← PadeWitnessFile.bezoutCoefficient_toCertificateField]
    rw [witness.bezoutCoefficient_eq_expected_of_bad_eq_zero cert no_bad k_lt]
    exact padeBezoutExpected_toCertificateField k
  have identity : U * D + V * R = 1 :=
    below.eq_of_natDegree_lt lhs_degree rhs_degree
  simpa [U, V, D, R, RankCertificateFile.padeNumeratorPolynomial_eq,
    mul_comm] using identity

/-- The concrete checked Padé witness supplies the Bézout premise of the
abstract Krylov nonsingularity theorem.  The only remaining data premise is
that the stored moments are the actual scalar Krylov moments. -/
theorem PadeWitnessFile.injective_of_checked_pade
    {W : Type*} [AddCommGroup W] [Module CertificateField W]
    [FiniteDimensional CertificateField W]
    (witness : PadeWitnessFile) (cert : RankCertificateFile)
    (u : W →ₗ[CertificateField] CertificateField)
    (A : Module.End CertificateField W) (w : W)
    (degree_gt_one : 1 < cert.degree)
    (dimension : Module.finrank CertificateField W = cert.degree)
    (bm_terms : cert.bmTerms = 2 * cert.degree)
    (u_length_le : witness.uLength ≤ cert.degree)
    (v_length_le : witness.vLength ≤ cert.degree)
    (no_bad : witness.bezoutBad cert = 0)
    (moment_match : ∀ k < 2 * cert.degree,
      cert.fieldMoment k = scalarKrylovMoment u A w k)
    (leading : cert.fieldCoefficient 0 = 1)
    (recurrence : ∀ k < cert.degree,
      ∑ i ∈ Finset.range (cert.degree + 1),
        cert.fieldCoefficient (cert.degree - i) *
          scalarKrylovMoment u A w (k + i) = 0)
    (constant_ne_zero : cert.fieldCoefficient cert.degree ≠ 0) :
    Function.Injective A := by
  have stored_moments : cert.storedMomentPolynomial =
      momentPolynomial (scalarKrylovMoment u A w) (2 * cert.degree) := by
    rw [cert.storedMomentPolynomial_eq bm_terms]
    ext k
    by_cases k_lt : k < 2 * cert.degree
    · rw [momentPolynomial_coeff_of_lt _ k_lt,
        momentPolynomial_coeff_of_lt _ k_lt]
      exact moment_match k k_lt
    · rw [momentPolynomial_coeff_of_le _ (Nat.le_of_not_gt k_lt),
        momentPolynomial_coeff_of_le _ (Nat.le_of_not_gt k_lt)]
  have bezout := witness.bezoutIdentity_of_bad_eq_zero cert
    (by omega) u_length_le v_length_le no_bad
  rw [stored_moments, cert.denominatorPolynomial_eq] at bezout
  exact injective_of_padeBezout_descendingConnection
    u A w cert.degree degree_gt_one dimension cert.fieldCoefficient leading
    recurrence constant_ne_zero witness.uPolynomial witness.vPolynomial bezout

end

end KnuthFasc8aEx210
