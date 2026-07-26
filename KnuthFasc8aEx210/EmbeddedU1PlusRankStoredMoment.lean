import KnuthFasc8aEx210.EmbeddedU1PlusRankCheckpointOrbit

namespace KnuthFasc8aEx210

noncomputable section

theorem embeddedU1PlusStoredMoment_eq_orbit :
    ∀ k < 51234,
      pairAt embeddedU1PlusCertificate.moments k =
        extDotBytes embeddedU1PlusSeed.u (embeddedU1PlusOrbit k)
          embeddedU1PlusHeader.n := by
  intro k k_lt
  let segment := k / 1024
  let offset := k % 1024
  have segment_lt : segment < 51 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    omega
  have offset_lt : offset < 1024 := Nat.mod_lt k (by omega)
  have decompose : segment * 1024 + offset = k := by
    simpa [segment, offset, Nat.mul_comm] using Nat.div_add_mod k 1024
  have offset_steps : offset < Nat.min 1024 (51234 - segment * 1024) := by
    by_cases h : 1024 ≤ 51234 - segment * 1024
    · have min_eq : Nat.min 1024 (51234 - segment * 1024) = 1024 :=
        Nat.min_eq_left h
      rw [min_eq]
      exact offset_lt
    · have min_eq : Nat.min 1024 (51234 - segment * 1024) =
          51234 - segment * 1024 := Nat.min_eq_right (by omega)
      rw [min_eq]
      omega
  have chunk_eq := embeddedU1PlusCheckpointChunk
  have steps_eq := embeddedU1PlusCheckpointSteps
  have segment_sound := embeddedU1PlusRankSegmentSound segment segment_lt
  simp only [EmbeddedU1PlusSegmentSound] at segment_sound
  rw [chunk_eq, steps_eq] at segment_sound
  have stored := segment_sound.1 offset offset_steps
  have checkpoint := embeddedU1PlusCheckpoint_eq_orbit segment (by omega)
  have position_lt : segment * 1024 < 51234 := by omega
  have checkpoint' : rankCheckpointVector embeddedU1PlusCheckpoints segment =
      embeddedU1PlusOrbit (segment * 1024) := by
    simpa [Nat.min_eq_left (Nat.le_of_lt position_lt)] using checkpoint
  calc
    pairAt embeddedU1PlusCertificate.moments k =
        pairAt embeddedU1PlusCertificate.moments
          (segment * 1024 + offset) := by rw [decompose]
    _ = extDotBytes embeddedU1PlusSeed.u
          (normalKrylovOrbitBytes embeddedU1PlusMatrixBytes
            embeddedU1PlusHeader embeddedU1PlusSeed.dR
            embeddedU1PlusSeed.dL
            (rankCheckpointVector embeddedU1PlusCheckpoints segment) offset)
          embeddedU1PlusHeader.n := stored
    _ = extDotBytes embeddedU1PlusSeed.u (embeddedU1PlusOrbit k)
          embeddedU1PlusHeader.n := by
      rw [checkpoint', ← embeddedU1PlusOrbit_add, decompose]

end

end KnuthFasc8aEx210
