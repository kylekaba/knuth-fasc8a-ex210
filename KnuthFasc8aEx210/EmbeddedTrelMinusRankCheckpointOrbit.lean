import KnuthFasc8aEx210.EmbeddedTrelMinusRankOrbitBasics
import KnuthFasc8aEx210.EmbeddedTrelMinusRankSegmentSoundness
import KnuthFasc8aEx210.EmbeddedTrelMinusRankFacts

namespace KnuthFasc8aEx210

noncomputable section

theorem embeddedTrelMinusCheckpoint_eq_orbit :
    ∀ segment ≤ 33,
      rankCheckpointVector embeddedTrelMinusCheckpoints segment =
        embeddedTrelMinusOrbit (Nat.min (segment * 1024) 33156) := by
  intro segment segment_le
  induction segment with
  | zero =>
      simpa [embeddedTrelMinusOrbit, normalKrylovOrbitBytes] using
        embeddedTrelMinusInitialCheckpoint
  | succ segment ih =>
      have segment_lt : segment < 33 := by omega
      have endpoint := (embeddedTrelMinusRankSegmentSound segment segment_lt).2
      have chunk_eq := embeddedTrelMinusCheckpointChunk
      have steps_eq := embeddedTrelMinusCheckpointSteps
      rw [chunk_eq, steps_eq] at endpoint
      have position_lt : segment * 1024 < 33156 := by omega
      have ih' : rankCheckpointVector embeddedTrelMinusCheckpoints segment =
          embeddedTrelMinusOrbit (segment * 1024) := by
        simpa [Nat.min_eq_left (Nat.le_of_lt position_lt)] using ih (by omega)
      calc
        rankCheckpointVector embeddedTrelMinusCheckpoints (segment + 1) =
            normalKrylovOrbitBytes embeddedTrelMinusMatrixBytes
              embeddedTrelMinusHeader embeddedTrelMinusSeed.dR
              embeddedTrelMinusSeed.dL
              (rankCheckpointVector embeddedTrelMinusCheckpoints segment)
              (Nat.min 1024 (33156 - segment * 1024)) := endpoint.symm
        _ = normalKrylovOrbitBytes embeddedTrelMinusMatrixBytes
              embeddedTrelMinusHeader embeddedTrelMinusSeed.dR
              embeddedTrelMinusSeed.dL (embeddedTrelMinusOrbit (segment * 1024))
              (Nat.min 1024 (33156 - segment * 1024)) := by rw [ih']
        _ = embeddedTrelMinusOrbit
              (segment * 1024 + Nat.min 1024 (33156 - segment * 1024)) := by
              rw [embeddedTrelMinusOrbit_add]
        _ = embeddedTrelMinusOrbit
              (Nat.min ((segment + 1) * 1024) 33156) := by
              congr 1
              by_cases h : segment < 32
              · have h₁ : Nat.min 1024 (33156 - segment * 1024) = 1024 :=
                  Nat.min_eq_left (by omega)
                have h₂ : Nat.min ((segment + 1) * 1024) 33156 =
                    (segment + 1) * 1024 := Nat.min_eq_left (by omega)
                rw [h₁, h₂]
                omega
              · have : segment = 32 := by omega
                subst segment
                decide

end

end KnuthFasc8aEx210
