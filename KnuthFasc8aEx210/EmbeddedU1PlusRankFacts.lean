import KnuthFasc8aEx210.EmbeddedU1PlusRankData

namespace KnuthFasc8aEx210

theorem embeddedU1PlusInitialCheckpoint :
    rankCheckpointVector embeddedU1PlusCheckpoints 0 = embeddedU1PlusSeed.x := by
  native_decide

theorem embeddedU1PlusCheckpointChunk : embeddedU1PlusCheckpoints.chunk = 1024 := by
  native_decide

theorem embeddedU1PlusCheckpointSteps : embeddedU1PlusCheckpoints.steps = 51234 := by
  native_decide

theorem embeddedU1PlusConstantCoefficientCanonical :
    embeddedU1PlusCertificate.connectionConstantCoefficient.IsCanonical := by
  constructor <;> native_decide

end KnuthFasc8aEx210
