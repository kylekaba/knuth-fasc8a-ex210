import KnuthFasc8aEx210.EmbeddedTrelPlusRankOrbitBasics
import KnuthFasc8aEx210.EmbeddedTrelPlusRankSegmentSoundness
import KnuthFasc8aEx210.EmbeddedTrelPlusRankPivot

namespace KnuthFasc8aEx210

noncomputable section

theorem embeddedTrelPlusCheckpoint_eq_orbit :
    ∀ segment ≤ 33,
      rankCheckpointVector embeddedTrelPlusCheckpoints segment =
        embeddedTrelPlusOrbit (Nat.min (segment * 1024) 33664) := by
  intro segment segment_le
  induction segment with
  | zero =>
      simpa [embeddedTrelPlusOrbit, borderKrylovOrbitBytes] using
        embeddedTrelPlusInitialCheckpoint
  | succ segment ih =>
      have segment_lt : segment < 33 := by omega
      have endpoint := (embeddedTrelPlusRankSegmentSound segment segment_lt).2
      have chunk_eq := embeddedTrelPlusCheckpointChunk
      have steps_eq := embeddedTrelPlusCheckpointSteps
      rw [chunk_eq, steps_eq] at endpoint
      have position_lt : segment * 1024 < 33664 := by omega
      have ih' : rankCheckpointVector embeddedTrelPlusCheckpoints segment =
          embeddedTrelPlusOrbit (segment * 1024) := by
        simpa [Nat.min_eq_left (Nat.le_of_lt position_lt)] using ih (by omega)
      calc
        rankCheckpointVector embeddedTrelPlusCheckpoints (segment + 1) =
            borderKrylovOrbitBytes embeddedTrelPlusMatrixBytes
              embeddedTrelPlusHeader embeddedTrelPlusEigen
              embeddedTrelPlusSeed.dR embeddedTrelPlusSeed.dL
              (rankCheckpointVector embeddedTrelPlusCheckpoints segment)
              (Nat.min 1024 (33664 - segment * 1024)) := endpoint.symm
        _ = borderKrylovOrbitBytes embeddedTrelPlusMatrixBytes
              embeddedTrelPlusHeader embeddedTrelPlusEigen
              embeddedTrelPlusSeed.dR embeddedTrelPlusSeed.dL
              (embeddedTrelPlusOrbit (segment * 1024))
              (Nat.min 1024 (33664 - segment * 1024)) := by rw [ih']
        _ = embeddedTrelPlusOrbit
              (segment * 1024 + Nat.min 1024
                (33664 - segment * 1024)) := by
              rw [embeddedTrelPlusOrbit_add]
        _ = embeddedTrelPlusOrbit
              (Nat.min ((segment + 1) * 1024) 33664) := by
              congr 1
              by_cases h : segment < 32
              · have h₁ : Nat.min 1024 (33664 - segment * 1024) = 1024 :=
                  Nat.min_eq_left (by omega)
                have h₂ : Nat.min ((segment + 1) * 1024) 33664 =
                    (segment + 1) * 1024 := Nat.min_eq_left (by omega)
                rw [h₁, h₂]
                omega
              · have : segment = 32 := by omega
                subst segment
                decide

end

end KnuthFasc8aEx210
