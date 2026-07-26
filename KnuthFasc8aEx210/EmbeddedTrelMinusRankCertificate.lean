import KnuthFasc8aEx210.EmbeddedTrelMinusRankKrylov
import KnuthFasc8aEx210.EmbeddedTrelMinusRankStatic
import KnuthFasc8aEx210.EmbeddedTrelMinusRankFacts

namespace KnuthFasc8aEx210

noncomputable section

/-- The checked-in normal Trel- rank certificate proves that 50 is absent from
its native characteristic polynomial. -/
theorem embeddedTrelMinus_rootMultiplicity_fifty_eq_zero :
    ((csrLinearMapBase embeddedTrelMinusMatrixBytes
      embeddedTrelMinusHeader).charpoly).rootMultiplicity (50 : ZMod 101) = 0 := by
  obtain ⟨degree_gt, degree_eq, bm_terms, bm_terms_le, u_length, v_length,
    bezout, full_recurrence, csr_columns, csr_rows, seed_size, dR_canonical,
    dR_nonzero, initial, matrix_hash, pade_hash, checkpoint_seed,
    checkpoint_matrix, checkpoint_eigen, leading_encoded, constant_encoded⟩ :=
      embeddedTrelMinusRankStaticChecks
  have leading : embeddedTrelMinusCertificate.fieldCoefficient 0 = 1 := by
    change embeddedTrelMinusCertificate.connectionLeadingCoefficient.toCertificateField = 1
    rw [leading_encoded]
    exact certificatePair_one
  have constant_ne : embeddedTrelMinusCertificate.fieldCoefficient
      embeddedTrelMinusCertificate.degree ≠ 0 := by
    change embeddedTrelMinusCertificate.connectionConstantCoefficient.toCertificateField ≠ 0
    have canonical := embeddedTrelMinusConstantCoefficientCanonical
    intro field_zero
    have is_zero :=
      (ExtElt.toCertificateField_eq_zero_iff _ canonical).mp field_zero
    apply constant_encoded
    generalize embeddedTrelMinusCertificate.connectionConstantCoefficient = x at is_zero ⊢
    rcases x with ⟨a, b⟩
    simp [ExtElt.isZero] at is_zero ⊢
    exact is_zero
  have preconditioned :=
    embeddedTrelMinusPade.injective_normal_of_checked_seed_counters
      embeddedTrelMinusCertificate embeddedTrelMinusSeed degree_gt degree_eq
      bm_terms bm_terms_le u_length v_length bezout full_recurrence
      embeddedTrelMinusKrylovBad_eq_zero csr_columns csr_rows seed_size leading
      constant_ne
  exact csrLinearMapBase_charpoly_rootMultiplicity_fifty_eq_zero_of_checked_counters
    embeddedTrelMinusMatrixBytes embeddedTrelMinusHeader embeddedTrelMinusSeed.dR
    embeddedTrelMinusSeed.dL preconditioned dR_canonical dR_nonzero

end

end KnuthFasc8aEx210
