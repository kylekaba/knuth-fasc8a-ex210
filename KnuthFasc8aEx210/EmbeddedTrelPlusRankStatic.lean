import KnuthFasc8aEx210.EmbeddedTrelPlusRankData

namespace KnuthFasc8aEx210

/-! All non-Krylov counters and binding metadata for the bordered `Trel+`
rank certificate.  The long orbit replay is compiled in separate modules. -/

theorem embeddedTrelPlusRankStaticChecks :
    1 < embeddedTrelPlusCertificate.degree ∧
    embeddedTrelPlusCertificate.degree = embeddedTrelPlusHeader.n + 1 ∧
    embeddedTrelPlusCertificate.bmTerms = 2 * embeddedTrelPlusCertificate.degree ∧
    embeddedTrelPlusCertificate.bmTerms ≤ embeddedTrelPlusCertificate.terms ∧
    embeddedTrelPlusPade.uLength ≤ embeddedTrelPlusCertificate.degree ∧
    embeddedTrelPlusPade.vLength ≤ embeddedTrelPlusCertificate.degree ∧
    embeddedTrelPlusPade.bezoutBad embeddedTrelPlusCertificate = 0 ∧
    embeddedTrelPlusCertificate.fullRecurrenceBad = 0 ∧
    matrixCSRColumnBad embeddedTrelPlusMatrixBytes embeddedTrelPlusHeader = 0 ∧
    matrixCSRRowPointerBad embeddedTrelPlusMatrixBytes embeddedTrelPlusHeader = 0 ∧
    embeddedTrelPlusSeed.sizeBad (embeddedTrelPlusHeader.n + 1) = 0 ∧
    encodedVectorCanonicalBad embeddedTrelPlusSeed.dR
      (embeddedTrelPlusHeader.n + 1) = 0 ∧
    encodedVectorZeroBad embeddedTrelPlusSeed.dR
      (embeddedTrelPlusHeader.n + 1) = 0 ∧
    rankCheckpointVector embeddedTrelPlusCheckpoints 0 = embeddedTrelPlusSeed.x ∧
    embeddedTrelPlusCertificate.matrixHash =
      fnv64Bytes embeddedTrelPlusMatrixBytes ∧
    embeddedTrelPlusCertificate.eigenHash =
      fnv64Bytes embeddedTrelPlusEigenBytes ∧
    embeddedTrelPlusPade.certificateHash =
      fnv64Bytes embeddedTrelPlusCertificateBytes ∧
    embeddedTrelPlusCheckpoints.seed = embeddedTrelPlusCertificate.seed ∧
    embeddedTrelPlusCheckpoints.matrixHash =
      embeddedTrelPlusCertificate.matrixHash ∧
    embeddedTrelPlusCheckpoints.eigenHash =
      embeddedTrelPlusCertificate.eigenHash ∧
    embeddedTrelPlusEigen.n = embeddedTrelPlusHeader.n ∧
    embeddedTrelPlusEigen.pivot = 0 ∧
    embeddedTrelPlusCertificate.pivot = 0 ∧
    embeddedTrelPlusCertificate.connectionLeadingCoefficient =
      { a := 1, b := 0 } ∧
    embeddedTrelPlusCertificate.connectionConstantCoefficient ≠
      { a := 0, b := 0 } ∧
    eigenResidualMismatchCount embeddedTrelPlusMatrixBytes embeddedTrelPlusHeader
      embeddedTrelPlusEigen = 0 ∧
    encodedVectorCanonicalBad
      (eigenPairBytes embeddedTrelPlusEigen embeddedTrelPlusHeader.n)
      embeddedTrelPlusHeader.n = 0 ∧
    embeddedTrelPlusEigen.pivotValue ≠ 0 := by
  native_decide

end KnuthFasc8aEx210
