import KnuthFasc8aEx210.EmbeddedTrelMinusRankData

namespace KnuthFasc8aEx210

theorem embeddedTrelMinusRankStaticChecks :
    1 < embeddedTrelMinusCertificate.degree ∧
    embeddedTrelMinusCertificate.degree = embeddedTrelMinusHeader.n ∧
    embeddedTrelMinusCertificate.bmTerms = 2 * embeddedTrelMinusCertificate.degree ∧
    embeddedTrelMinusCertificate.bmTerms ≤ embeddedTrelMinusCertificate.terms ∧
    embeddedTrelMinusPade.uLength ≤ embeddedTrelMinusCertificate.degree ∧
    embeddedTrelMinusPade.vLength ≤ embeddedTrelMinusCertificate.degree ∧
    embeddedTrelMinusPade.bezoutBad embeddedTrelMinusCertificate = 0 ∧
    embeddedTrelMinusCertificate.fullRecurrenceBad = 0 ∧
    matrixCSRColumnBad embeddedTrelMinusMatrixBytes embeddedTrelMinusHeader = 0 ∧
    matrixCSRRowPointerBad embeddedTrelMinusMatrixBytes embeddedTrelMinusHeader = 0 ∧
    embeddedTrelMinusSeed.sizeBad embeddedTrelMinusHeader.n = 0 ∧
    encodedVectorCanonicalBad embeddedTrelMinusSeed.dR embeddedTrelMinusHeader.n = 0 ∧
    encodedVectorZeroBad embeddedTrelMinusSeed.dR embeddedTrelMinusHeader.n = 0 ∧
    rankCheckpointVector embeddedTrelMinusCheckpoints 0 = embeddedTrelMinusSeed.x ∧
    embeddedTrelMinusCertificate.matrixHash = fnv64Bytes embeddedTrelMinusMatrixBytes ∧
    embeddedTrelMinusPade.certificateHash = fnv64Bytes embeddedTrelMinusCertificateBytes ∧
    embeddedTrelMinusCheckpoints.seed = embeddedTrelMinusCertificate.seed ∧
    embeddedTrelMinusCheckpoints.matrixHash = embeddedTrelMinusCertificate.matrixHash ∧
    embeddedTrelMinusCheckpoints.eigenHash = embeddedTrelMinusCertificate.eigenHash ∧
    embeddedTrelMinusCertificate.connectionLeadingCoefficient = { a := 1, b := 0 } ∧
    embeddedTrelMinusCertificate.connectionConstantCoefficient ≠ { a := 0, b := 0 } := by
  native_decide

end KnuthFasc8aEx210
