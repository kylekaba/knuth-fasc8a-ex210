import KnuthFasc8aEx210.EmbeddedU1PlusRankKrylov
import KnuthFasc8aEx210.EmbeddedU1PlusRankStatic
import KnuthFasc8aEx210.EmbeddedU1PlusRankFacts

namespace KnuthFasc8aEx210

noncomputable section

/-- The checked-in normal U1+ rank certificate proves that 50 is absent from
its native characteristic polynomial. -/
theorem embeddedU1Plus_rootMultiplicity_fifty_eq_zero :
    ((csrLinearMapBase embeddedU1PlusMatrixBytes
      embeddedU1PlusHeader).charpoly).rootMultiplicity (50 : ZMod 101) = 0 := by
  obtain ⟨degree_gt, degree_eq, bm_terms, bm_terms_le, u_length, v_length,
    bezout, full_recurrence, csr_columns, csr_rows, seed_size, dR_canonical,
    dR_nonzero, initial, matrix_hash, pade_hash, checkpoint_seed,
    checkpoint_matrix, checkpoint_eigen, leading_encoded, constant_encoded⟩ :=
      embeddedU1PlusRankStaticChecks
  have leading : embeddedU1PlusCertificate.fieldCoefficient 0 = 1 := by
    change embeddedU1PlusCertificate.connectionLeadingCoefficient.toCertificateField = 1
    rw [leading_encoded]
    exact certificatePair_one
  have constant_ne : embeddedU1PlusCertificate.fieldCoefficient
      embeddedU1PlusCertificate.degree ≠ 0 := by
    change embeddedU1PlusCertificate.connectionConstantCoefficient.toCertificateField ≠ 0
    have canonical := embeddedU1PlusConstantCoefficientCanonical
    intro field_zero
    have is_zero :=
      (ExtElt.toCertificateField_eq_zero_iff _ canonical).mp field_zero
    apply constant_encoded
    generalize embeddedU1PlusCertificate.connectionConstantCoefficient = x at is_zero ⊢
    rcases x with ⟨a, b⟩
    simp [ExtElt.isZero] at is_zero ⊢
    exact is_zero
  have preconditioned :=
    embeddedU1PlusPade.injective_normal_of_checked_seed_counters
      embeddedU1PlusCertificate embeddedU1PlusSeed degree_gt degree_eq
      bm_terms bm_terms_le u_length v_length bezout full_recurrence
      embeddedU1PlusKrylovBad_eq_zero csr_columns csr_rows seed_size leading
      constant_ne
  exact csrLinearMapBase_charpoly_rootMultiplicity_fifty_eq_zero_of_checked_counters
    embeddedU1PlusMatrixBytes embeddedU1PlusHeader embeddedU1PlusSeed.dR
    embeddedU1PlusSeed.dL preconditioned dR_canonical dR_nonzero

end

end KnuthFasc8aEx210
