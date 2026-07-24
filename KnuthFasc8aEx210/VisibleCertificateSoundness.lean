import KnuthFasc8aEx210.TransferDenominator

/-!
# Soundness interface for the closed visible-factor certificate

This file gives mathematical meanings to the parsed closed CSR matrix,
terminal vector, and polynomial certificate.  Its single bad-count predicate
is deliberately proof-shaped: zero residuals and a nonzero observed
coordinate feed the generic recurrence/Krylov-span theorem directly.
-/

namespace KnuthFasc8aEx210

open Matrix Polynomial

noncomputable section

/-- Matrix over `F₁₀₁` denoted by the parsed CSR operator. -/
def csrMatrixBase (matrixBytes : ByteArray) (header : MatrixHeader) :
    Matrix (Fin header.n) (Fin header.n) F101 :=
  LinearMap.toMatrix' (csrLinearMapBase matrixBytes header)

@[simp] theorem csrMatrixBase_mulVec
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (v : Fin header.n → F101) :
    csrMatrixBase matrixBytes header *ᵥ v =
      csrLinearMapBase matrixBytes header v := by
  rw [← Matrix.toLin'_apply, csrMatrixBase, Matrix.toLin'_toMatrix']

/-- Native-field interpretation of the terminal/startup vector file. -/
def finishVectorBase (finish : FinishVectorFile) (n : ℕ) : Fin n → F101 :=
  fun i ↦ finish.values[i]!.toNat

/-- Native-field polynomial represented by the visible polynomial file. -/
def polynomialFileBase (poly : PolynomialFile) : ModPolynomial :=
  ∑ i ∈ Finset.range poly.length,
    monomial i (poly.coefficients[i]!.toNat : F101)

/-- Coordinate observation vector; dotting with it selects `bare`. -/
def coordinateObservation {n : ℕ} (bare : Fin n) : Fin n → F101 :=
  Pi.single bare 1

@[simp] theorem dotProduct_coordinateObservation
    {n : ℕ} (bare : Fin n) (v : Fin n → F101) :
    dotProduct (coordinateObservation bare) v = v bare := by
  classical
  simp [coordinateObservation, dotProduct, Pi.single_apply]

/-- The exact `r = g(M²) beta` vector denoted by the visible certificate. -/
def visibleCertificateR (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile) :
    Fin header.n → F101 :=
  evenPolynomialKrylovVector (csrMatrixBase matrixBytes header)
    (finishVectorBase finish header.n) (polynomialFileBase poly)

/-- The derived `50`-eigenvector candidate `r + 99 M r`. -/
def visibleCertificateV (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile) :
    Fin header.n → F101 :=
  let M := csrMatrixBase matrixBytes header
  let r := visibleCertificateR matrixBytes header poly finish
  r + (99 : F101) • (M *ᵥ r)

/-- Number of mathematically nonzero rows in the checked `M²r-76r`
residual. -/
def visibleSquareResidualBad (matrixBytes : ByteArray)
    (header : MatrixHeader) (poly : PolynomialFile)
    (finish : FinishVectorFile) : ℕ :=
  let M := csrMatrixBase matrixBytes header
  let r := visibleCertificateR matrixBytes header poly finish
  (Finset.univ.filter fun i ↦ (M ^ 2 *ᵥ r) i ≠ (76 : F101) * r i).card

/-- One precisely when the certificate's observed coordinate is zero. -/
def visibleCoordinateZeroBad (matrixBytes : ByteArray)
    (header : MatrixHeader) (poly : PolynomialFile)
    (finish : FinishVectorFile) (bare : Fin header.n) : ℕ :=
  if visibleCertificateV matrixBytes header poly finish bare = 0 then 1 else 0

/-- Proof-shaped aggregate for the closed visibility certificate. -/
private unsafe def visibleCertificateBadFast (matrixBytes : ByteArray)
    (header : MatrixHeader) (poly : PolynomialFile)
    (finish : FinishVectorFile) (bare : Fin header.n) : ℕ :=
  let result : ParseM ℕ := do
    let r ← visiblePolynomialHornerPrefix matrixBytes header poly finish poly.length
    let square ← matrixApplyByteVectorTwice matrixBytes header r
    let squareBad ← scaledVectorMismatchCount square 76 r
    let mr ← matrixApplyByteVector matrixBytes header r
    let v := addScaledByteVector r 99 mr
    let coordinateBad := if byteVectorAt v bare = 0 then 1 else 0
    pure (squareBad + coordinateBad)
  match result with
  | .ok bad => bad
  | .error _ => 1

@[implemented_by visibleCertificateBadFast]
def visibleCertificateBad (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n) : ℕ :=
  visibleSquareResidualBad matrixBytes header poly finish +
    visibleCoordinateZeroBad matrixBytes header poly finish bare

theorem visibleSquareResidualBad_eq_zero_iff
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile) :
    visibleSquareResidualBad matrixBytes header poly finish = 0 ↔
      let M := csrMatrixBase matrixBytes header
      let r := visibleCertificateR matrixBytes header poly finish
      M ^ 2 *ᵥ r = (76 : F101) • r := by
  unfold visibleSquareResidualBad
  rw [Finset.card_eq_zero]
  constructor
  · intro empty
    funext i
    have coordinate : (csrMatrixBase matrixBytes header ^ 2 *ᵥ
        visibleCertificateR matrixBytes header poly finish) i =
        (76 : F101) *
          visibleCertificateR matrixBytes header poly finish i := by
      by_contra unequal
      have mem : i ∈ Finset.univ.filter fun j ↦
          (csrMatrixBase matrixBytes header ^ 2 *ᵥ
            visibleCertificateR matrixBytes header poly finish) j ≠
              (76 : F101) *
                visibleCertificateR matrixBytes header poly finish j := by
        simp [unequal]
      rw [empty] at mem
      simp at mem
    simpa using coordinate
  · intro vector_eq
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ unequal
    apply unequal
    have coordinate := congrFun vector_eq i
    simpa using coordinate

theorem visibleCoordinateZeroBad_eq_zero_iff
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n) :
    visibleCoordinateZeroBad matrixBytes header poly finish bare = 0 ↔
      visibleCertificateV matrixBytes header poly finish bare ≠ 0 := by
  simp [visibleCoordinateZeroBad]

/-- Zero mathematical bad count gives exactly the square-eigenvector and
visibility facts consumed by the closed denominator theorem. -/
theorem visibleCertificateBad_eq_zero_iff
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n) :
    visibleCertificateBad matrixBytes header poly finish bare = 0 ↔
      (let M := csrMatrixBase matrixBytes header
       let r := visibleCertificateR matrixBytes header poly finish
       M ^ 2 *ᵥ r = (76 : F101) • r) ∧
      visibleCertificateV matrixBytes header poly finish bare ≠ 0 := by
  rw [visibleCertificateBad, Nat.add_eq_zero_iff,
    visibleSquareResidualBad_eq_zero_iff,
    visibleCoordinateZeroBad_eq_zero_iff]

/-- End-to-end mathematical consequence of a zero closed visible-certificate
counter, leaving only the denominator-recurrence premise to its rational
generating-function bridge. -/
theorem visibleFactor_dvd_of_visibleCertificateBad_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n) (q : ModPolynomial)
    (recurrence : IsEventuallyForwardRecurrence (csrMatrixBase matrixBytes header)
      (coordinateObservation bare) (finishVectorBase finish header.n)
      q.reverse)
    (no_bad : visibleCertificateBad matrixBytes header poly finish bare = 0) :
    visibleFactor ∣ q := by
  have facts := (visibleCertificateBad_eq_zero_iff
    matrixBytes header poly finish bare).mp no_bad
  apply visibleFactor_dvd_of_visibleCandidate_eventual_recurrence
    (csrMatrixBase matrixBytes header) (coordinateObservation bare)
    (finishVectorBase finish header.n) (polynomialFileBase poly) q recurrence
  · exact facts.1
  · simpa [visibleCertificateV, visibleCertificateR] using facts.2

/-- A passing closed certificate proves visibility in the actual canonical
reduced scalar transfer denominator; no recurrence premise remains. -/
theorem visibleFactor_dvd_transferDenominator_of_visibleCertificateBad_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n)
    (no_bad : visibleCertificateBad matrixBytes header poly finish bare = 0) :
    visibleFactor ∣ transferDenominator (csrMatrixBase matrixBytes header)
      (finishVectorBase finish header.n) (coordinateObservation bare) := by
  apply visibleFactor_dvd_of_visibleCertificateBad_eq_zero
    matrixBytes header poly finish bare _
  · exact transferDenominator_reverse_isEventuallyForwardRecurrence
      (csrMatrixBase matrixBytes header)
      (finishVectorBase finish header.n) (coordinateObservation bare)
  · exact no_bad

/-- Constant-term-one normalization preserves the certificate's visible
factor. -/
theorem visibleFactor_dvd_normalizedTransferDenominator_of_visibleCertificateBad_eq_zero
    (matrixBytes : ByteArray) (header : MatrixHeader)
    (poly : PolynomialFile) (finish : FinishVectorFile)
    (bare : Fin header.n)
    (no_bad : visibleCertificateBad matrixBytes header poly finish bare = 0) :
    visibleFactor ∣
      normalizedTransferDenominator (csrMatrixBase matrixBytes header)
        (finishVectorBase finish header.n) (coordinateObservation bare) := by
  apply (normalizedTransferDenominator_associated
    (csrMatrixBase matrixBytes header)
    (finishVectorBase finish header.n)
    (coordinateObservation bare)).dvd_iff_dvd_right.mpr
  exact visibleFactor_dvd_transferDenominator_of_visibleCertificateBad_eq_zero
    matrixBytes header poly finish bare no_bad

end

end KnuthFasc8aEx210
