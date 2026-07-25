import KnuthFasc8aEx210.EmbeddedTrelPlusRankStoredMoment

namespace KnuthFasc8aEx210

noncomputable section

theorem embeddedTrelPlusKrylovBad_eq_zero :
    embeddedTrelPlusCertificate.borderKrylovMismatchCount
      embeddedTrelPlusMatrixBytes embeddedTrelPlusHeader embeddedTrelPlusEigen
      embeddedTrelPlusSeed.dR embeddedTrelPlusSeed.dL embeddedTrelPlusSeed.u
      embeddedTrelPlusSeed.x (2 * embeddedTrelPlusCertificate.degree) = 0 := by
  rw [RankCertificateFile.borderKrylovMismatchCount]
  have degree : embeddedTrelPlusCertificate.degree = 16832 :=
    embeddedTrelPlus_metadata.2.2.1
  rw [degree]
  simp only [Nat.reduceMul, List.length_eq_zero_iff]
  apply List.filter_eq_nil_iff.mpr
  intro k k_mem
  simp only [List.mem_range] at k_mem
  have stored := embeddedTrelPlusStoredMoment_eq_orbit k k_mem
  simpa [embeddedTrelPlusOrbit] using stored

end

end KnuthFasc8aEx210
