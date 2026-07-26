import KnuthFasc8aEx210.EmbeddedTrelMinusRankStoredMoment

namespace KnuthFasc8aEx210

noncomputable section

theorem embeddedTrelMinusKrylovBad_eq_zero :
    embeddedTrelMinusCertificate.normalKrylovMismatchCount
      embeddedTrelMinusMatrixBytes embeddedTrelMinusHeader
      embeddedTrelMinusSeed.dR embeddedTrelMinusSeed.dL embeddedTrelMinusSeed.u
      embeddedTrelMinusSeed.x (2 * embeddedTrelMinusCertificate.degree) = 0 := by
  rw [RankCertificateFile.normalKrylovMismatchCount]
  have degree : embeddedTrelMinusCertificate.degree = 16578 :=
    embeddedTrelMinus_metadata.2.2.1
  rw [degree]
  simp only [Nat.reduceMul, List.length_eq_zero_iff]
  apply List.filter_eq_nil_iff.mpr
  intro k k_mem
  simp only [List.mem_range] at k_mem
  have stored := embeddedTrelMinusStoredMoment_eq_orbit k k_mem
  simpa [embeddedTrelMinusOrbit] using stored

end

end KnuthFasc8aEx210
