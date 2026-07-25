import KnuthFasc8aEx210.EmbeddedTrelPlusRankCheckpointOrbit

namespace KnuthFasc8aEx210

noncomputable section

theorem embeddedTrelPlusStoredMoment_eq_orbit :
    ∀ k < 33664,
      pairAt embeddedTrelPlusCertificate.moments k =
        extDotBytes embeddedTrelPlusSeed.u (embeddedTrelPlusOrbit k)
          (embeddedTrelPlusHeader.n + 1) := by
  intro k k_lt
  let segment := k / 1024
  let offset := k % 1024
  have segment_lt : segment < 33 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    omega
  have offset_lt : offset < 1024 := Nat.mod_lt k (by omega)
  have decompose : segment * 1024 + offset = k := by
    simpa [segment, offset, Nat.mul_comm] using Nat.div_add_mod k 1024
  have offset_steps : offset < Nat.min 1024 (33664 - segment * 1024) := by
    by_cases h : 1024 ≤ 33664 - segment * 1024
    · have min_eq : Nat.min 1024 (33664 - segment * 1024) = 1024 :=
        Nat.min_eq_left h
      rw [min_eq]
      exact offset_lt
    · have min_eq : Nat.min 1024 (33664 - segment * 1024) =
          33664 - segment * 1024 := Nat.min_eq_right (by omega)
      rw [min_eq]
      omega
  have chunk_eq := embeddedTrelPlusCheckpointChunk
  have steps_eq := embeddedTrelPlusCheckpointSteps
  have segment_sound := embeddedTrelPlusRankSegmentSound segment segment_lt
  simp only [EmbeddedTrelPlusSegmentSound] at segment_sound
  rw [chunk_eq, steps_eq] at segment_sound
  have stored := segment_sound.1 offset offset_steps
  have checkpoint := embeddedTrelPlusCheckpoint_eq_orbit segment (by omega)
  have position_lt : segment * 1024 < 33664 := by omega
  have checkpoint' : rankCheckpointVector embeddedTrelPlusCheckpoints segment =
      embeddedTrelPlusOrbit (segment * 1024) := by
    simpa [Nat.min_eq_left (Nat.le_of_lt position_lt)] using checkpoint
  calc
    pairAt embeddedTrelPlusCertificate.moments k =
        pairAt embeddedTrelPlusCertificate.moments
          (segment * 1024 + offset) := by rw [decompose]
    _ = extDotBytes embeddedTrelPlusSeed.u
          (borderKrylovOrbitBytes embeddedTrelPlusMatrixBytes
            embeddedTrelPlusHeader embeddedTrelPlusEigen
            embeddedTrelPlusSeed.dR embeddedTrelPlusSeed.dL
            (rankCheckpointVector embeddedTrelPlusCheckpoints segment) offset)
          (embeddedTrelPlusHeader.n + 1) := stored
    _ = extDotBytes embeddedTrelPlusSeed.u (embeddedTrelPlusOrbit k)
          (embeddedTrelPlusHeader.n + 1) := by
      rw [checkpoint', ← embeddedTrelPlusOrbit_add, decompose]

end

end KnuthFasc8aEx210
