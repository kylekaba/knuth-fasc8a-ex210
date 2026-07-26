import KnuthFasc8aEx210.EmbeddedTrelPlusRankKrylov
import KnuthFasc8aEx210.EmbeddedTrelPlusRankStatic
import KnuthFasc8aEx210.EmbeddedTrelPlusRankPivot

/-!
# The embedded bordered Trel+ rank certificate

The imported modules replay all 33 bounded Krylov segments. This module
stitches their exact endpoint equalities into one orbit and derives simple
root multiplicity at 50 for the checked-in Trel+ CSR operator.
-/

namespace KnuthFasc8aEx210

noncomputable section


def embeddedTrelPlusPivot : Fin embeddedTrelPlusHeader.n :=
  ⟨0, by rw [embeddedTrelPlus_metadata.1]; omega⟩

/-- The checked-in bordered rank certificate proves that 50 has algebraic
multiplicity exactly one in the native Trel+ characteristic polynomial. -/
theorem embeddedTrelPlus_rootMultiplicity_fifty_eq_one :
    ((csrLinearMapBase embeddedTrelPlusMatrixBytes
      embeddedTrelPlusHeader).charpoly).rootMultiplicity (50 : ZMod 101) = 1 := by
  obtain ⟨degree_gt, degree_eq, bm_terms, bm_terms_le, u_length, v_length,
    bezout, full_recurrence, csr_columns, csr_rows, seed_size, dR_canonical,
    dR_nonzero, initial, matrix_hash, eigen_hash, pade_hash, checkpoint_seed,
    checkpoint_matrix, checkpoint_eigen, eig_n, eig_pivot, cert_pivot,
    leading_encoded, constant_encoded, eigen_residual, eigen_canonical,
    pivot_nonzero⟩ := embeddedTrelPlusRankStaticChecks
  have pivot_eq : embeddedTrelPlusEigen.pivot = embeddedTrelPlusPivot.val := by
    simpa [embeddedTrelPlusPivot] using eig_pivot
  have leading : embeddedTrelPlusCertificate.fieldCoefficient 0 = 1 := by
    change embeddedTrelPlusCertificate.connectionLeadingCoefficient.toCertificateField = 1
    rw [leading_encoded]
    exact certificatePair_one
  have constant_ne : embeddedTrelPlusCertificate.fieldCoefficient
      embeddedTrelPlusCertificate.degree ≠ 0 := by
    change embeddedTrelPlusCertificate.connectionConstantCoefficient.toCertificateField ≠ 0
    have canonical := embeddedTrelPlusConstantCoefficientCanonical
    intro field_zero
    have is_zero :=
      (ExtElt.toCertificateField_eq_zero_iff _ canonical).mp field_zero
    apply constant_encoded
    generalize embeddedTrelPlusCertificate.connectionConstantCoefficient = x at is_zero ⊢
    rcases x with ⟨a, b⟩
    simp [ExtElt.isZero] at is_zero ⊢
    exact is_zero
  have preconditioned :=
    embeddedTrelPlusPade.injective_border_of_checked_seed_counters
      embeddedTrelPlusCertificate embeddedTrelPlusEigen embeddedTrelPlusPivot
      embeddedTrelPlusSeed degree_gt degree_eq bm_terms bm_terms_le u_length
      v_length bezout full_recurrence embeddedTrelPlusKrylovBad_eq_zero
      csr_columns csr_rows seed_size eig_n pivot_eq leading constant_ne
  exact csrLinearMapBase_charpoly_rootMultiplicity_fifty_eq_one_of_checked_counters
    embeddedTrelPlusMatrixBytes embeddedTrelPlusHeader embeddedTrelPlusEigen
    embeddedTrelPlusPivot embeddedTrelPlusSeed.dR embeddedTrelPlusSeed.dL
    preconditioned dR_canonical dR_nonzero csr_columns csr_rows eigen_residual
    eigen_canonical (by
      simpa [embeddedTrelPlusPivot] using
        embeddedTrelPlusEigenValueAtZero_ne_zero)

end

end KnuthFasc8aEx210
