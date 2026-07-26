import KnuthFasc8aEx210.EmbeddedTrelMinusRankSegment00
import KnuthFasc8aEx210.EmbeddedTrelMinusRankSegments01_04
import KnuthFasc8aEx210.EmbeddedTrelMinusRankSegments05_08
import KnuthFasc8aEx210.EmbeddedTrelMinusRankSegments09_12
import KnuthFasc8aEx210.EmbeddedTrelMinusRankSegments13_16
import KnuthFasc8aEx210.EmbeddedTrelMinusRankSegments17_20
import KnuthFasc8aEx210.EmbeddedTrelMinusRankSegments21_24
import KnuthFasc8aEx210.EmbeddedTrelMinusRankSegments25_28
import KnuthFasc8aEx210.EmbeddedTrelMinusRankSegments29_32

namespace KnuthFasc8aEx210

def EmbeddedTrelMinusSegmentSound (segment : Nat) : Prop :=
  let first := segment * embeddedTrelMinusCheckpoints.chunk
  let steps := Nat.min embeddedTrelMinusCheckpoints.chunk
    (embeddedTrelMinusCheckpoints.steps - first)
  let initial := rankCheckpointVector embeddedTrelMinusCheckpoints segment
  let orbit := normalKrylovOrbitBytes embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed.dR embeddedTrelMinusSeed.dL initial
  (∀ offset < steps,
    pairAt embeddedTrelMinusCertificate.moments (first + offset) =
      extDotBytes embeddedTrelMinusSeed.u (orbit offset)
        embeddedTrelMinusHeader.n) ∧
    orbit steps = rankCheckpointVector embeddedTrelMinusCheckpoints (segment + 1)

theorem embeddedTrelMinusRankSegmentSound00 :
    EmbeddedTrelMinusSegmentSound 0 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 0).mp embeddedTrelMinusRankSegment00_eq_zero

theorem embeddedTrelMinusRankSegmentSound01 :
    EmbeddedTrelMinusSegmentSound 1 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 1).mp embeddedTrelMinusRankSegment01_eq_zero

theorem embeddedTrelMinusRankSegmentSound02 :
    EmbeddedTrelMinusSegmentSound 2 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 2).mp embeddedTrelMinusRankSegment02_eq_zero

theorem embeddedTrelMinusRankSegmentSound03 :
    EmbeddedTrelMinusSegmentSound 3 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 3).mp embeddedTrelMinusRankSegment03_eq_zero

theorem embeddedTrelMinusRankSegmentSound04 :
    EmbeddedTrelMinusSegmentSound 4 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 4).mp embeddedTrelMinusRankSegment04_eq_zero

theorem embeddedTrelMinusRankSegmentSound05 :
    EmbeddedTrelMinusSegmentSound 5 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 5).mp embeddedTrelMinusRankSegment05_eq_zero

theorem embeddedTrelMinusRankSegmentSound06 :
    EmbeddedTrelMinusSegmentSound 6 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 6).mp embeddedTrelMinusRankSegment06_eq_zero

theorem embeddedTrelMinusRankSegmentSound07 :
    EmbeddedTrelMinusSegmentSound 7 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 7).mp embeddedTrelMinusRankSegment07_eq_zero

theorem embeddedTrelMinusRankSegmentSound08 :
    EmbeddedTrelMinusSegmentSound 8 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 8).mp embeddedTrelMinusRankSegment08_eq_zero

theorem embeddedTrelMinusRankSegmentSound09 :
    EmbeddedTrelMinusSegmentSound 9 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 9).mp embeddedTrelMinusRankSegment09_eq_zero

theorem embeddedTrelMinusRankSegmentSound10 :
    EmbeddedTrelMinusSegmentSound 10 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 10).mp embeddedTrelMinusRankSegment10_eq_zero

theorem embeddedTrelMinusRankSegmentSound11 :
    EmbeddedTrelMinusSegmentSound 11 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 11).mp embeddedTrelMinusRankSegment11_eq_zero

theorem embeddedTrelMinusRankSegmentSound12 :
    EmbeddedTrelMinusSegmentSound 12 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 12).mp embeddedTrelMinusRankSegment12_eq_zero

theorem embeddedTrelMinusRankSegmentSound13 :
    EmbeddedTrelMinusSegmentSound 13 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 13).mp embeddedTrelMinusRankSegment13_eq_zero

theorem embeddedTrelMinusRankSegmentSound14 :
    EmbeddedTrelMinusSegmentSound 14 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 14).mp embeddedTrelMinusRankSegment14_eq_zero

theorem embeddedTrelMinusRankSegmentSound15 :
    EmbeddedTrelMinusSegmentSound 15 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 15).mp embeddedTrelMinusRankSegment15_eq_zero

theorem embeddedTrelMinusRankSegmentSound16 :
    EmbeddedTrelMinusSegmentSound 16 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 16).mp embeddedTrelMinusRankSegment16_eq_zero

theorem embeddedTrelMinusRankSegmentSound17 :
    EmbeddedTrelMinusSegmentSound 17 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 17).mp embeddedTrelMinusRankSegment17_eq_zero

theorem embeddedTrelMinusRankSegmentSound18 :
    EmbeddedTrelMinusSegmentSound 18 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 18).mp embeddedTrelMinusRankSegment18_eq_zero

theorem embeddedTrelMinusRankSegmentSound19 :
    EmbeddedTrelMinusSegmentSound 19 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 19).mp embeddedTrelMinusRankSegment19_eq_zero

theorem embeddedTrelMinusRankSegmentSound20 :
    EmbeddedTrelMinusSegmentSound 20 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 20).mp embeddedTrelMinusRankSegment20_eq_zero

theorem embeddedTrelMinusRankSegmentSound21 :
    EmbeddedTrelMinusSegmentSound 21 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 21).mp embeddedTrelMinusRankSegment21_eq_zero

theorem embeddedTrelMinusRankSegmentSound22 :
    EmbeddedTrelMinusSegmentSound 22 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 22).mp embeddedTrelMinusRankSegment22_eq_zero

theorem embeddedTrelMinusRankSegmentSound23 :
    EmbeddedTrelMinusSegmentSound 23 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 23).mp embeddedTrelMinusRankSegment23_eq_zero

theorem embeddedTrelMinusRankSegmentSound24 :
    EmbeddedTrelMinusSegmentSound 24 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 24).mp embeddedTrelMinusRankSegment24_eq_zero

theorem embeddedTrelMinusRankSegmentSound25 :
    EmbeddedTrelMinusSegmentSound 25 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 25).mp embeddedTrelMinusRankSegment25_eq_zero

theorem embeddedTrelMinusRankSegmentSound26 :
    EmbeddedTrelMinusSegmentSound 26 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 26).mp embeddedTrelMinusRankSegment26_eq_zero

theorem embeddedTrelMinusRankSegmentSound27 :
    EmbeddedTrelMinusSegmentSound 27 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 27).mp embeddedTrelMinusRankSegment27_eq_zero

theorem embeddedTrelMinusRankSegmentSound28 :
    EmbeddedTrelMinusSegmentSound 28 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 28).mp embeddedTrelMinusRankSegment28_eq_zero

theorem embeddedTrelMinusRankSegmentSound29 :
    EmbeddedTrelMinusSegmentSound 29 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 29).mp embeddedTrelMinusRankSegment29_eq_zero

theorem embeddedTrelMinusRankSegmentSound30 :
    EmbeddedTrelMinusSegmentSound 30 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 30).mp embeddedTrelMinusRankSegment30_eq_zero

theorem embeddedTrelMinusRankSegmentSound31 :
    EmbeddedTrelMinusSegmentSound 31 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 31).mp embeddedTrelMinusRankSegment31_eq_zero

theorem embeddedTrelMinusRankSegmentSound32 :
    EmbeddedTrelMinusSegmentSound 32 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelMinusCertificate embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed
    embeddedTrelMinusCheckpoints 32).mp embeddedTrelMinusRankSegment32_eq_zero

theorem embeddedTrelMinusRankSegmentSound (segment : Nat)
    (segment_lt : segment < 33) : EmbeddedTrelMinusSegmentSound segment := by
  interval_cases segment <;>
  first
  | exact embeddedTrelMinusRankSegmentSound00
  | exact embeddedTrelMinusRankSegmentSound01
  | exact embeddedTrelMinusRankSegmentSound02
  | exact embeddedTrelMinusRankSegmentSound03
  | exact embeddedTrelMinusRankSegmentSound04
  | exact embeddedTrelMinusRankSegmentSound05
  | exact embeddedTrelMinusRankSegmentSound06
  | exact embeddedTrelMinusRankSegmentSound07
  | exact embeddedTrelMinusRankSegmentSound08
  | exact embeddedTrelMinusRankSegmentSound09
  | exact embeddedTrelMinusRankSegmentSound10
  | exact embeddedTrelMinusRankSegmentSound11
  | exact embeddedTrelMinusRankSegmentSound12
  | exact embeddedTrelMinusRankSegmentSound13
  | exact embeddedTrelMinusRankSegmentSound14
  | exact embeddedTrelMinusRankSegmentSound15
  | exact embeddedTrelMinusRankSegmentSound16
  | exact embeddedTrelMinusRankSegmentSound17
  | exact embeddedTrelMinusRankSegmentSound18
  | exact embeddedTrelMinusRankSegmentSound19
  | exact embeddedTrelMinusRankSegmentSound20
  | exact embeddedTrelMinusRankSegmentSound21
  | exact embeddedTrelMinusRankSegmentSound22
  | exact embeddedTrelMinusRankSegmentSound23
  | exact embeddedTrelMinusRankSegmentSound24
  | exact embeddedTrelMinusRankSegmentSound25
  | exact embeddedTrelMinusRankSegmentSound26
  | exact embeddedTrelMinusRankSegmentSound27
  | exact embeddedTrelMinusRankSegmentSound28
  | exact embeddedTrelMinusRankSegmentSound29
  | exact embeddedTrelMinusRankSegmentSound30
  | exact embeddedTrelMinusRankSegmentSound31
  | exact embeddedTrelMinusRankSegmentSound32

end KnuthFasc8aEx210
