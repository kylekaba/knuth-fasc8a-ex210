import KnuthFasc8aEx210.EmbeddedVisibleSegment00
import KnuthFasc8aEx210.EmbeddedVisibleSegment01
import KnuthFasc8aEx210.EmbeddedVisibleSegment02
import KnuthFasc8aEx210.EmbeddedVisibleSegment03

/-!
# Closed visible factor from embedded checked-in bytes

The four imported modules replay disjoint bounded segments of the full Horner
certificate.  This module composes their mathematical equalities, proves the
final checkpoint remains in the startup Krylov span, and derives the factor in
the actual normalized reduced scalar transfer denominator.
-/

namespace KnuthFasc8aEx210

open Matrix Polynomial

noncomputable section

theorem embeddedVisibleHornerInitial_eq_zero :
    hornerCheckpointBase embeddedVisibleHorner 0 embeddedTallHeader.n = 0 := by
  native_decide

theorem embeddedVisibleCheckpointFinalBad_eq_zero :
    checkedVisibleCheckpointFinalBad embeddedTallBytes embeddedTallHeader
      embeddedVisibleHorner 4 embeddedBare = 0 := by
  native_decide

private theorem embeddedVisibleCheckpointFinal_mem_krylovSpan :
    hornerCheckpointBase embeddedVisibleHorner 4 embeddedTallHeader.n ∈
      Submodule.span F101 (Set.range fun j : Nat ↦
        csrMatrixBase embeddedTallBytes embeddedTallHeader ^ j *ᵥ
          finishVectorBase embeddedTallFinish embeddedTallHeader.n) := by
  let M := csrMatrixBase embeddedTallBytes embeddedTallHeader
  let beta := finishVectorBase embeddedTallFinish embeddedTallHeader.n
  let K := Submodule.span F101 (Set.range fun j : Nat ↦ M ^ j *ᵥ beta)
  have segment0 := (checkedVisibleHornerSegmentBad_eq_zero_iff
    embeddedTallBytes embeddedTallHeader embeddedVisiblePolynomial
    embeddedTallFinish embeddedVisibleHorner 0).mp
      embeddedVisibleSegment00_eq_zero
  have segment1 := (checkedVisibleHornerSegmentBad_eq_zero_iff
    embeddedTallBytes embeddedTallHeader embeddedVisiblePolynomial
    embeddedTallFinish embeddedVisibleHorner 1).mp
      embeddedVisibleSegment01_eq_zero
  have segment2 := (checkedVisibleHornerSegmentBad_eq_zero_iff
    embeddedTallBytes embeddedTallHeader embeddedVisiblePolynomial
    embeddedTallFinish embeddedVisibleHorner 2).mp
      embeddedVisibleSegment02_eq_zero
  have segment3 := (checkedVisibleHornerSegmentBad_eq_zero_iff
    embeddedTallBytes embeddedTallHeader embeddedVisiblePolynomial
    embeddedTallFinish embeddedVisibleHorner 3).mp
      embeddedVisibleSegment03_eq_zero
  have checkpoint0 :
      hornerCheckpointBase embeddedVisibleHorner 0 embeddedTallHeader.n ∈ K := by
    rw [embeddedVisibleHornerInitial_eq_zero]
    exact Submodule.zero_mem K
  have checkpoint1 :
      hornerCheckpointBase embeddedVisibleHorner 1 embeddedTallHeader.n ∈ K := by
    rw [← segment0]
    exact visibleHornerSegment_mem_krylovSpan M beta _
      embeddedVisiblePolynomial _ _ checkpoint0
  have checkpoint2 :
      hornerCheckpointBase embeddedVisibleHorner 2 embeddedTallHeader.n ∈ K := by
    rw [← segment1]
    exact visibleHornerSegment_mem_krylovSpan M beta _
      embeddedVisiblePolynomial _ _ checkpoint1
  have checkpoint3 :
      hornerCheckpointBase embeddedVisibleHorner 3 embeddedTallHeader.n ∈ K := by
    rw [← segment2]
    exact visibleHornerSegment_mem_krylovSpan M beta _
      embeddedVisiblePolynomial _ _ checkpoint2
  have checkpoint4 :
      hornerCheckpointBase embeddedVisibleHorner 4 embeddedTallHeader.n ∈ K := by
    rw [← segment3]
    exact visibleHornerSegment_mem_krylovSpan M beta _
      embeddedVisiblePolynomial _ _ checkpoint3
  exact checkpoint4

/-- The checked-in closed matrix, finish vector, visible polynomial, and
bounded Horner checkpoints prove `1 - 50X` divides the canonical normalized
reduced closed transfer denominator. -/
theorem embedded_visibleFactor_dvd_normalizedTransferDenominator :
    visibleFactor ∣
      normalizedTransferDenominator
        (csrMatrixBase embeddedTallBytes embeddedTallHeader)
        (finishVectorBase embeddedTallFinish embeddedTallHeader.n)
        (coordinateObservation embeddedBare) := by
  apply visibleFactor_dvd_normalizedTransferDenominator_of_checkpoint
    embeddedTallBytes embeddedTallHeader embeddedTallFinish
    embeddedVisibleHorner 4 embeddedBare
  · change hornerCheckpointBase embeddedVisibleHorner 4 embeddedTallHeader.n ∈ _
    exact embeddedVisibleCheckpointFinal_mem_krylovSpan
  · exact embeddedVisibleCheckpointFinalBad_eq_zero

end

end KnuthFasc8aEx210
