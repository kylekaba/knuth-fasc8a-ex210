import KnuthFasc8aEx210.EmbeddedU1PlusRankStoredMoment

namespace KnuthFasc8aEx210

noncomputable section

theorem embeddedU1PlusKrylovBad_eq_zero :
    embeddedU1PlusCertificate.normalKrylovMismatchCount
      embeddedU1PlusMatrixBytes embeddedU1PlusHeader
      embeddedU1PlusSeed.dR embeddedU1PlusSeed.dL embeddedU1PlusSeed.u
      embeddedU1PlusSeed.x (2 * embeddedU1PlusCertificate.degree) = 0 := by
  rw [RankCertificateFile.normalKrylovMismatchCount]
  have degree : embeddedU1PlusCertificate.degree = 25617 :=
    embeddedU1Plus_metadata.2.2.1
  rw [degree]
  simp only [Nat.reduceMul, List.length_eq_zero_iff]
  apply List.filter_eq_nil_iff.mpr
  intro k k_mem
  simp only [List.mem_range] at k_mem
  have stored := embeddedU1PlusStoredMoment_eq_orbit k k_mem
  simpa [embeddedU1PlusOrbit] using stored

end

end KnuthFasc8aEx210
