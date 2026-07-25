import KnuthFasc8aEx210.EmbeddedTrelPlusRankSegment00
import KnuthFasc8aEx210.EmbeddedTrelPlusRankSegments01_04
import KnuthFasc8aEx210.EmbeddedTrelPlusRankSegments05_08
import KnuthFasc8aEx210.EmbeddedTrelPlusRankSegments09_12
import KnuthFasc8aEx210.EmbeddedTrelPlusRankSegments13_16
import KnuthFasc8aEx210.EmbeddedTrelPlusRankSegments17_20
import KnuthFasc8aEx210.EmbeddedTrelPlusRankSegments21_24
import KnuthFasc8aEx210.EmbeddedTrelPlusRankSegments25_28
import KnuthFasc8aEx210.EmbeddedTrelPlusRankSegments29_32

namespace KnuthFasc8aEx210

def EmbeddedTrelPlusSegmentSound (segment : Nat) : Prop :=
  let first := segment * embeddedTrelPlusCheckpoints.chunk
  let steps := Nat.min embeddedTrelPlusCheckpoints.chunk
    (embeddedTrelPlusCheckpoints.steps - first)
  let initial := rankCheckpointVector embeddedTrelPlusCheckpoints segment
  let orbit := borderKrylovOrbitBytes embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed.dR
    embeddedTrelPlusSeed.dL initial
  (∀ offset < steps,
    pairAt embeddedTrelPlusCertificate.moments (first + offset) =
      extDotBytes embeddedTrelPlusSeed.u (orbit offset)
        (embeddedTrelPlusHeader.n + 1)) ∧
    orbit steps = rankCheckpointVector embeddedTrelPlusCheckpoints
      (segment + 1)

theorem embeddedTrelPlusRankSegmentSound00 :
    EmbeddedTrelPlusSegmentSound 0 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 0).mp embeddedTrelPlusRankSegment00_eq_zero

theorem embeddedTrelPlusRankSegmentSound01 :
    EmbeddedTrelPlusSegmentSound 1 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 1).mp embeddedTrelPlusRankSegment01_eq_zero

theorem embeddedTrelPlusRankSegmentSound02 :
    EmbeddedTrelPlusSegmentSound 2 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 2).mp embeddedTrelPlusRankSegment02_eq_zero

theorem embeddedTrelPlusRankSegmentSound03 :
    EmbeddedTrelPlusSegmentSound 3 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 3).mp embeddedTrelPlusRankSegment03_eq_zero

theorem embeddedTrelPlusRankSegmentSound04 :
    EmbeddedTrelPlusSegmentSound 4 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 4).mp embeddedTrelPlusRankSegment04_eq_zero

theorem embeddedTrelPlusRankSegmentSound05 :
    EmbeddedTrelPlusSegmentSound 5 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 5).mp embeddedTrelPlusRankSegment05_eq_zero

theorem embeddedTrelPlusRankSegmentSound06 :
    EmbeddedTrelPlusSegmentSound 6 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 6).mp embeddedTrelPlusRankSegment06_eq_zero

theorem embeddedTrelPlusRankSegmentSound07 :
    EmbeddedTrelPlusSegmentSound 7 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 7).mp embeddedTrelPlusRankSegment07_eq_zero

theorem embeddedTrelPlusRankSegmentSound08 :
    EmbeddedTrelPlusSegmentSound 8 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 8).mp embeddedTrelPlusRankSegment08_eq_zero

theorem embeddedTrelPlusRankSegmentSound09 :
    EmbeddedTrelPlusSegmentSound 9 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 9).mp embeddedTrelPlusRankSegment09_eq_zero

theorem embeddedTrelPlusRankSegmentSound10 :
    EmbeddedTrelPlusSegmentSound 10 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 10).mp embeddedTrelPlusRankSegment10_eq_zero

theorem embeddedTrelPlusRankSegmentSound11 :
    EmbeddedTrelPlusSegmentSound 11 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 11).mp embeddedTrelPlusRankSegment11_eq_zero

theorem embeddedTrelPlusRankSegmentSound12 :
    EmbeddedTrelPlusSegmentSound 12 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 12).mp embeddedTrelPlusRankSegment12_eq_zero

theorem embeddedTrelPlusRankSegmentSound13 :
    EmbeddedTrelPlusSegmentSound 13 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 13).mp embeddedTrelPlusRankSegment13_eq_zero

theorem embeddedTrelPlusRankSegmentSound14 :
    EmbeddedTrelPlusSegmentSound 14 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 14).mp embeddedTrelPlusRankSegment14_eq_zero

theorem embeddedTrelPlusRankSegmentSound15 :
    EmbeddedTrelPlusSegmentSound 15 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 15).mp embeddedTrelPlusRankSegment15_eq_zero

theorem embeddedTrelPlusRankSegmentSound16 :
    EmbeddedTrelPlusSegmentSound 16 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 16).mp embeddedTrelPlusRankSegment16_eq_zero

theorem embeddedTrelPlusRankSegmentSound17 :
    EmbeddedTrelPlusSegmentSound 17 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 17).mp embeddedTrelPlusRankSegment17_eq_zero

theorem embeddedTrelPlusRankSegmentSound18 :
    EmbeddedTrelPlusSegmentSound 18 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 18).mp embeddedTrelPlusRankSegment18_eq_zero

theorem embeddedTrelPlusRankSegmentSound19 :
    EmbeddedTrelPlusSegmentSound 19 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 19).mp embeddedTrelPlusRankSegment19_eq_zero

theorem embeddedTrelPlusRankSegmentSound20 :
    EmbeddedTrelPlusSegmentSound 20 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 20).mp embeddedTrelPlusRankSegment20_eq_zero

theorem embeddedTrelPlusRankSegmentSound21 :
    EmbeddedTrelPlusSegmentSound 21 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 21).mp embeddedTrelPlusRankSegment21_eq_zero

theorem embeddedTrelPlusRankSegmentSound22 :
    EmbeddedTrelPlusSegmentSound 22 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 22).mp embeddedTrelPlusRankSegment22_eq_zero

theorem embeddedTrelPlusRankSegmentSound23 :
    EmbeddedTrelPlusSegmentSound 23 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 23).mp embeddedTrelPlusRankSegment23_eq_zero

theorem embeddedTrelPlusRankSegmentSound24 :
    EmbeddedTrelPlusSegmentSound 24 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 24).mp embeddedTrelPlusRankSegment24_eq_zero

theorem embeddedTrelPlusRankSegmentSound25 :
    EmbeddedTrelPlusSegmentSound 25 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 25).mp embeddedTrelPlusRankSegment25_eq_zero

theorem embeddedTrelPlusRankSegmentSound26 :
    EmbeddedTrelPlusSegmentSound 26 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 26).mp embeddedTrelPlusRankSegment26_eq_zero

theorem embeddedTrelPlusRankSegmentSound27 :
    EmbeddedTrelPlusSegmentSound 27 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 27).mp embeddedTrelPlusRankSegment27_eq_zero

theorem embeddedTrelPlusRankSegmentSound28 :
    EmbeddedTrelPlusSegmentSound 28 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 28).mp embeddedTrelPlusRankSegment28_eq_zero

theorem embeddedTrelPlusRankSegmentSound29 :
    EmbeddedTrelPlusSegmentSound 29 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 29).mp embeddedTrelPlusRankSegment29_eq_zero

theorem embeddedTrelPlusRankSegmentSound30 :
    EmbeddedTrelPlusSegmentSound 30 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 30).mp embeddedTrelPlusRankSegment30_eq_zero

theorem embeddedTrelPlusRankSegmentSound31 :
    EmbeddedTrelPlusSegmentSound 31 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 31).mp embeddedTrelPlusRankSegment31_eq_zero

theorem embeddedTrelPlusRankSegmentSound32 :
    EmbeddedTrelPlusSegmentSound 32 :=
  (checkedBorderRankCheckpointSegmentBad_eq_zero_iff
    embeddedTrelPlusCertificate embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed
    embeddedTrelPlusCheckpoints 32).mp embeddedTrelPlusRankSegment32_eq_zero

theorem embeddedTrelPlusRankSegmentSound (segment : Nat)
    (segment_lt : segment < 33) : EmbeddedTrelPlusSegmentSound segment := by
  interval_cases segment <;>
  first
  | exact embeddedTrelPlusRankSegmentSound00
  | exact embeddedTrelPlusRankSegmentSound01
  | exact embeddedTrelPlusRankSegmentSound02
  | exact embeddedTrelPlusRankSegmentSound03
  | exact embeddedTrelPlusRankSegmentSound04
  | exact embeddedTrelPlusRankSegmentSound05
  | exact embeddedTrelPlusRankSegmentSound06
  | exact embeddedTrelPlusRankSegmentSound07
  | exact embeddedTrelPlusRankSegmentSound08
  | exact embeddedTrelPlusRankSegmentSound09
  | exact embeddedTrelPlusRankSegmentSound10
  | exact embeddedTrelPlusRankSegmentSound11
  | exact embeddedTrelPlusRankSegmentSound12
  | exact embeddedTrelPlusRankSegmentSound13
  | exact embeddedTrelPlusRankSegmentSound14
  | exact embeddedTrelPlusRankSegmentSound15
  | exact embeddedTrelPlusRankSegmentSound16
  | exact embeddedTrelPlusRankSegmentSound17
  | exact embeddedTrelPlusRankSegmentSound18
  | exact embeddedTrelPlusRankSegmentSound19
  | exact embeddedTrelPlusRankSegmentSound20
  | exact embeddedTrelPlusRankSegmentSound21
  | exact embeddedTrelPlusRankSegmentSound22
  | exact embeddedTrelPlusRankSegmentSound23
  | exact embeddedTrelPlusRankSegmentSound24
  | exact embeddedTrelPlusRankSegmentSound25
  | exact embeddedTrelPlusRankSegmentSound26
  | exact embeddedTrelPlusRankSegmentSound27
  | exact embeddedTrelPlusRankSegmentSound28
  | exact embeddedTrelPlusRankSegmentSound29
  | exact embeddedTrelPlusRankSegmentSound30
  | exact embeddedTrelPlusRankSegmentSound31
  | exact embeddedTrelPlusRankSegmentSound32

end KnuthFasc8aEx210
