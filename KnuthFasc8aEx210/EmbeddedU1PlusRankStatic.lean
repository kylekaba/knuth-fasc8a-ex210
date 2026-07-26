import KnuthFasc8aEx210.EmbeddedU1PlusRankData

namespace KnuthFasc8aEx210

theorem embeddedU1PlusRankStaticChecks :
    1 < embeddedU1PlusCertificate.degree ∧
    embeddedU1PlusCertificate.degree = embeddedU1PlusHeader.n ∧
    embeddedU1PlusCertificate.bmTerms = 2 * embeddedU1PlusCertificate.degree ∧
    embeddedU1PlusCertificate.bmTerms ≤ embeddedU1PlusCertificate.terms ∧
    embeddedU1PlusPade.uLength ≤ embeddedU1PlusCertificate.degree ∧
    embeddedU1PlusPade.vLength ≤ embeddedU1PlusCertificate.degree ∧
    embeddedU1PlusPade.bezoutBad embeddedU1PlusCertificate = 0 ∧
    embeddedU1PlusCertificate.fullRecurrenceBad = 0 ∧
    matrixCSRColumnBad embeddedU1PlusMatrixBytes embeddedU1PlusHeader = 0 ∧
    matrixCSRRowPointerBad embeddedU1PlusMatrixBytes embeddedU1PlusHeader = 0 ∧
    embeddedU1PlusSeed.sizeBad embeddedU1PlusHeader.n = 0 ∧
    encodedVectorCanonicalBad embeddedU1PlusSeed.dR embeddedU1PlusHeader.n = 0 ∧
    encodedVectorZeroBad embeddedU1PlusSeed.dR embeddedU1PlusHeader.n = 0 ∧
    rankCheckpointVector embeddedU1PlusCheckpoints 0 = embeddedU1PlusSeed.x ∧
    embeddedU1PlusCertificate.matrixHash = fnv64Bytes embeddedU1PlusMatrixBytes ∧
    embeddedU1PlusPade.certificateHash = fnv64Bytes embeddedU1PlusCertificateBytes ∧
    embeddedU1PlusCheckpoints.seed = embeddedU1PlusCertificate.seed ∧
    embeddedU1PlusCheckpoints.matrixHash = embeddedU1PlusCertificate.matrixHash ∧
    embeddedU1PlusCheckpoints.eigenHash = embeddedU1PlusCertificate.eigenHash ∧
    embeddedU1PlusCertificate.connectionLeadingCoefficient = { a := 1, b := 0 } ∧
    embeddedU1PlusCertificate.connectionConstantCoefficient ≠ { a := 0, b := 0 } := by
  native_decide

end KnuthFasc8aEx210
