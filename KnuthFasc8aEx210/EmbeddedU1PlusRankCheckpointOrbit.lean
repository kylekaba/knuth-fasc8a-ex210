import KnuthFasc8aEx210.EmbeddedU1PlusRankOrbitBasics
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegmentSoundness
import KnuthFasc8aEx210.EmbeddedU1PlusRankFacts

namespace KnuthFasc8aEx210

noncomputable section

theorem embeddedU1PlusCheckpoint_eq_orbit :
    ∀ segment ≤ 51,
      rankCheckpointVector embeddedU1PlusCheckpoints segment =
        embeddedU1PlusOrbit (Nat.min (segment * 1024) 51234) := by
  intro segment segment_le
  induction segment with
  | zero =>
      simpa [embeddedU1PlusOrbit, normalKrylovOrbitBytes] using
        embeddedU1PlusInitialCheckpoint
  | succ segment ih =>
      have segment_lt : segment < 51 := by omega
      have endpoint := (embeddedU1PlusRankSegmentSound segment segment_lt).2
      have chunk_eq := embeddedU1PlusCheckpointChunk
      have steps_eq := embeddedU1PlusCheckpointSteps
      rw [chunk_eq, steps_eq] at endpoint
      have position_lt : segment * 1024 < 51234 := by omega
      have ih' : rankCheckpointVector embeddedU1PlusCheckpoints segment =
          embeddedU1PlusOrbit (segment * 1024) := by
        simpa [Nat.min_eq_left (Nat.le_of_lt position_lt)] using ih (by omega)
      calc
        rankCheckpointVector embeddedU1PlusCheckpoints (segment + 1) =
            normalKrylovOrbitBytes embeddedU1PlusMatrixBytes
              embeddedU1PlusHeader embeddedU1PlusSeed.dR
              embeddedU1PlusSeed.dL
              (rankCheckpointVector embeddedU1PlusCheckpoints segment)
              (Nat.min 1024 (51234 - segment * 1024)) := endpoint.symm
        _ = normalKrylovOrbitBytes embeddedU1PlusMatrixBytes
              embeddedU1PlusHeader embeddedU1PlusSeed.dR
              embeddedU1PlusSeed.dL (embeddedU1PlusOrbit (segment * 1024))
              (Nat.min 1024 (51234 - segment * 1024)) := by rw [ih']
        _ = embeddedU1PlusOrbit
              (segment * 1024 + Nat.min 1024 (51234 - segment * 1024)) := by
              rw [embeddedU1PlusOrbit_add]
        _ = embeddedU1PlusOrbit
              (Nat.min ((segment + 1) * 1024) 51234) := by
              congr 1
              by_cases h : segment < 50
              · have h₁ : Nat.min 1024 (51234 - segment * 1024) = 1024 :=
                  Nat.min_eq_left (by omega)
                have h₂ : Nat.min ((segment + 1) * 1024) 51234 =
                    (segment + 1) * 1024 := Nat.min_eq_left (by omega)
                rw [h₁, h₂]
                omega
              · have : segment = 50 := by omega
                subst segment
                decide

end

end KnuthFasc8aEx210
