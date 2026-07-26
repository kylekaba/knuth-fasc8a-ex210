import KnuthFasc8aEx210.EmbeddedU1PlusRankSegment00
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments01_04
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments05_08
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments09_12
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments13_16
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments17_20
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments21_24
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments25_28
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments29_32
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments33_36
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments37_40
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments41_44
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments45_48
import KnuthFasc8aEx210.EmbeddedU1PlusRankSegments49_50

namespace KnuthFasc8aEx210

def EmbeddedU1PlusSegmentSound (segment : Nat) : Prop :=
  let first := segment * embeddedU1PlusCheckpoints.chunk
  let steps := Nat.min embeddedU1PlusCheckpoints.chunk
    (embeddedU1PlusCheckpoints.steps - first)
  let initial := rankCheckpointVector embeddedU1PlusCheckpoints segment
  let orbit := normalKrylovOrbitBytes embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed.dR embeddedU1PlusSeed.dL initial
  (∀ offset < steps,
    pairAt embeddedU1PlusCertificate.moments (first + offset) =
      extDotBytes embeddedU1PlusSeed.u (orbit offset)
        embeddedU1PlusHeader.n) ∧
    orbit steps = rankCheckpointVector embeddedU1PlusCheckpoints (segment + 1)

theorem embeddedU1PlusRankSegmentSound00 :
    EmbeddedU1PlusSegmentSound 0 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 0).mp embeddedU1PlusRankSegment00_eq_zero

theorem embeddedU1PlusRankSegmentSound01 :
    EmbeddedU1PlusSegmentSound 1 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 1).mp embeddedU1PlusRankSegment01_eq_zero

theorem embeddedU1PlusRankSegmentSound02 :
    EmbeddedU1PlusSegmentSound 2 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 2).mp embeddedU1PlusRankSegment02_eq_zero

theorem embeddedU1PlusRankSegmentSound03 :
    EmbeddedU1PlusSegmentSound 3 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 3).mp embeddedU1PlusRankSegment03_eq_zero

theorem embeddedU1PlusRankSegmentSound04 :
    EmbeddedU1PlusSegmentSound 4 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 4).mp embeddedU1PlusRankSegment04_eq_zero

theorem embeddedU1PlusRankSegmentSound05 :
    EmbeddedU1PlusSegmentSound 5 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 5).mp embeddedU1PlusRankSegment05_eq_zero

theorem embeddedU1PlusRankSegmentSound06 :
    EmbeddedU1PlusSegmentSound 6 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 6).mp embeddedU1PlusRankSegment06_eq_zero

theorem embeddedU1PlusRankSegmentSound07 :
    EmbeddedU1PlusSegmentSound 7 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 7).mp embeddedU1PlusRankSegment07_eq_zero

theorem embeddedU1PlusRankSegmentSound08 :
    EmbeddedU1PlusSegmentSound 8 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 8).mp embeddedU1PlusRankSegment08_eq_zero

theorem embeddedU1PlusRankSegmentSound09 :
    EmbeddedU1PlusSegmentSound 9 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 9).mp embeddedU1PlusRankSegment09_eq_zero

theorem embeddedU1PlusRankSegmentSound10 :
    EmbeddedU1PlusSegmentSound 10 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 10).mp embeddedU1PlusRankSegment10_eq_zero

theorem embeddedU1PlusRankSegmentSound11 :
    EmbeddedU1PlusSegmentSound 11 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 11).mp embeddedU1PlusRankSegment11_eq_zero

theorem embeddedU1PlusRankSegmentSound12 :
    EmbeddedU1PlusSegmentSound 12 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 12).mp embeddedU1PlusRankSegment12_eq_zero

theorem embeddedU1PlusRankSegmentSound13 :
    EmbeddedU1PlusSegmentSound 13 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 13).mp embeddedU1PlusRankSegment13_eq_zero

theorem embeddedU1PlusRankSegmentSound14 :
    EmbeddedU1PlusSegmentSound 14 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 14).mp embeddedU1PlusRankSegment14_eq_zero

theorem embeddedU1PlusRankSegmentSound15 :
    EmbeddedU1PlusSegmentSound 15 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 15).mp embeddedU1PlusRankSegment15_eq_zero

theorem embeddedU1PlusRankSegmentSound16 :
    EmbeddedU1PlusSegmentSound 16 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 16).mp embeddedU1PlusRankSegment16_eq_zero

theorem embeddedU1PlusRankSegmentSound17 :
    EmbeddedU1PlusSegmentSound 17 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 17).mp embeddedU1PlusRankSegment17_eq_zero

theorem embeddedU1PlusRankSegmentSound18 :
    EmbeddedU1PlusSegmentSound 18 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 18).mp embeddedU1PlusRankSegment18_eq_zero

theorem embeddedU1PlusRankSegmentSound19 :
    EmbeddedU1PlusSegmentSound 19 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 19).mp embeddedU1PlusRankSegment19_eq_zero

theorem embeddedU1PlusRankSegmentSound20 :
    EmbeddedU1PlusSegmentSound 20 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 20).mp embeddedU1PlusRankSegment20_eq_zero

theorem embeddedU1PlusRankSegmentSound21 :
    EmbeddedU1PlusSegmentSound 21 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 21).mp embeddedU1PlusRankSegment21_eq_zero

theorem embeddedU1PlusRankSegmentSound22 :
    EmbeddedU1PlusSegmentSound 22 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 22).mp embeddedU1PlusRankSegment22_eq_zero

theorem embeddedU1PlusRankSegmentSound23 :
    EmbeddedU1PlusSegmentSound 23 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 23).mp embeddedU1PlusRankSegment23_eq_zero

theorem embeddedU1PlusRankSegmentSound24 :
    EmbeddedU1PlusSegmentSound 24 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 24).mp embeddedU1PlusRankSegment24_eq_zero

theorem embeddedU1PlusRankSegmentSound25 :
    EmbeddedU1PlusSegmentSound 25 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 25).mp embeddedU1PlusRankSegment25_eq_zero

theorem embeddedU1PlusRankSegmentSound26 :
    EmbeddedU1PlusSegmentSound 26 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 26).mp embeddedU1PlusRankSegment26_eq_zero

theorem embeddedU1PlusRankSegmentSound27 :
    EmbeddedU1PlusSegmentSound 27 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 27).mp embeddedU1PlusRankSegment27_eq_zero

theorem embeddedU1PlusRankSegmentSound28 :
    EmbeddedU1PlusSegmentSound 28 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 28).mp embeddedU1PlusRankSegment28_eq_zero

theorem embeddedU1PlusRankSegmentSound29 :
    EmbeddedU1PlusSegmentSound 29 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 29).mp embeddedU1PlusRankSegment29_eq_zero

theorem embeddedU1PlusRankSegmentSound30 :
    EmbeddedU1PlusSegmentSound 30 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 30).mp embeddedU1PlusRankSegment30_eq_zero

theorem embeddedU1PlusRankSegmentSound31 :
    EmbeddedU1PlusSegmentSound 31 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 31).mp embeddedU1PlusRankSegment31_eq_zero

theorem embeddedU1PlusRankSegmentSound32 :
    EmbeddedU1PlusSegmentSound 32 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 32).mp embeddedU1PlusRankSegment32_eq_zero

theorem embeddedU1PlusRankSegmentSound33 :
    EmbeddedU1PlusSegmentSound 33 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 33).mp embeddedU1PlusRankSegment33_eq_zero

theorem embeddedU1PlusRankSegmentSound34 :
    EmbeddedU1PlusSegmentSound 34 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 34).mp embeddedU1PlusRankSegment34_eq_zero

theorem embeddedU1PlusRankSegmentSound35 :
    EmbeddedU1PlusSegmentSound 35 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 35).mp embeddedU1PlusRankSegment35_eq_zero

theorem embeddedU1PlusRankSegmentSound36 :
    EmbeddedU1PlusSegmentSound 36 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 36).mp embeddedU1PlusRankSegment36_eq_zero

theorem embeddedU1PlusRankSegmentSound37 :
    EmbeddedU1PlusSegmentSound 37 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 37).mp embeddedU1PlusRankSegment37_eq_zero

theorem embeddedU1PlusRankSegmentSound38 :
    EmbeddedU1PlusSegmentSound 38 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 38).mp embeddedU1PlusRankSegment38_eq_zero

theorem embeddedU1PlusRankSegmentSound39 :
    EmbeddedU1PlusSegmentSound 39 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 39).mp embeddedU1PlusRankSegment39_eq_zero

theorem embeddedU1PlusRankSegmentSound40 :
    EmbeddedU1PlusSegmentSound 40 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 40).mp embeddedU1PlusRankSegment40_eq_zero

theorem embeddedU1PlusRankSegmentSound41 :
    EmbeddedU1PlusSegmentSound 41 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 41).mp embeddedU1PlusRankSegment41_eq_zero

theorem embeddedU1PlusRankSegmentSound42 :
    EmbeddedU1PlusSegmentSound 42 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 42).mp embeddedU1PlusRankSegment42_eq_zero

theorem embeddedU1PlusRankSegmentSound43 :
    EmbeddedU1PlusSegmentSound 43 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 43).mp embeddedU1PlusRankSegment43_eq_zero

theorem embeddedU1PlusRankSegmentSound44 :
    EmbeddedU1PlusSegmentSound 44 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 44).mp embeddedU1PlusRankSegment44_eq_zero

theorem embeddedU1PlusRankSegmentSound45 :
    EmbeddedU1PlusSegmentSound 45 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 45).mp embeddedU1PlusRankSegment45_eq_zero

theorem embeddedU1PlusRankSegmentSound46 :
    EmbeddedU1PlusSegmentSound 46 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 46).mp embeddedU1PlusRankSegment46_eq_zero

theorem embeddedU1PlusRankSegmentSound47 :
    EmbeddedU1PlusSegmentSound 47 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 47).mp embeddedU1PlusRankSegment47_eq_zero

theorem embeddedU1PlusRankSegmentSound48 :
    EmbeddedU1PlusSegmentSound 48 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 48).mp embeddedU1PlusRankSegment48_eq_zero

theorem embeddedU1PlusRankSegmentSound49 :
    EmbeddedU1PlusSegmentSound 49 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 49).mp embeddedU1PlusRankSegment49_eq_zero

theorem embeddedU1PlusRankSegmentSound50 :
    EmbeddedU1PlusSegmentSound 50 :=
  (checkedNormalRankCheckpointSegmentBad_eq_zero_iff
    embeddedU1PlusCertificate embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed
    embeddedU1PlusCheckpoints 50).mp embeddedU1PlusRankSegment50_eq_zero

theorem embeddedU1PlusRankSegmentSound (segment : Nat)
    (segment_lt : segment < 51) : EmbeddedU1PlusSegmentSound segment := by
  interval_cases segment <;>
  first
  | exact embeddedU1PlusRankSegmentSound00
  | exact embeddedU1PlusRankSegmentSound01
  | exact embeddedU1PlusRankSegmentSound02
  | exact embeddedU1PlusRankSegmentSound03
  | exact embeddedU1PlusRankSegmentSound04
  | exact embeddedU1PlusRankSegmentSound05
  | exact embeddedU1PlusRankSegmentSound06
  | exact embeddedU1PlusRankSegmentSound07
  | exact embeddedU1PlusRankSegmentSound08
  | exact embeddedU1PlusRankSegmentSound09
  | exact embeddedU1PlusRankSegmentSound10
  | exact embeddedU1PlusRankSegmentSound11
  | exact embeddedU1PlusRankSegmentSound12
  | exact embeddedU1PlusRankSegmentSound13
  | exact embeddedU1PlusRankSegmentSound14
  | exact embeddedU1PlusRankSegmentSound15
  | exact embeddedU1PlusRankSegmentSound16
  | exact embeddedU1PlusRankSegmentSound17
  | exact embeddedU1PlusRankSegmentSound18
  | exact embeddedU1PlusRankSegmentSound19
  | exact embeddedU1PlusRankSegmentSound20
  | exact embeddedU1PlusRankSegmentSound21
  | exact embeddedU1PlusRankSegmentSound22
  | exact embeddedU1PlusRankSegmentSound23
  | exact embeddedU1PlusRankSegmentSound24
  | exact embeddedU1PlusRankSegmentSound25
  | exact embeddedU1PlusRankSegmentSound26
  | exact embeddedU1PlusRankSegmentSound27
  | exact embeddedU1PlusRankSegmentSound28
  | exact embeddedU1PlusRankSegmentSound29
  | exact embeddedU1PlusRankSegmentSound30
  | exact embeddedU1PlusRankSegmentSound31
  | exact embeddedU1PlusRankSegmentSound32
  | exact embeddedU1PlusRankSegmentSound33
  | exact embeddedU1PlusRankSegmentSound34
  | exact embeddedU1PlusRankSegmentSound35
  | exact embeddedU1PlusRankSegmentSound36
  | exact embeddedU1PlusRankSegmentSound37
  | exact embeddedU1PlusRankSegmentSound38
  | exact embeddedU1PlusRankSegmentSound39
  | exact embeddedU1PlusRankSegmentSound40
  | exact embeddedU1PlusRankSegmentSound41
  | exact embeddedU1PlusRankSegmentSound42
  | exact embeddedU1PlusRankSegmentSound43
  | exact embeddedU1PlusRankSegmentSound44
  | exact embeddedU1PlusRankSegmentSound45
  | exact embeddedU1PlusRankSegmentSound46
  | exact embeddedU1PlusRankSegmentSound47
  | exact embeddedU1PlusRankSegmentSound48
  | exact embeddedU1PlusRankSegmentSound49
  | exact embeddedU1PlusRankSegmentSound50

end KnuthFasc8aEx210
