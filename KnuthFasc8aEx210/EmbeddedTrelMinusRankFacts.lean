import KnuthFasc8aEx210.EmbeddedTrelMinusRankData

namespace KnuthFasc8aEx210

theorem embeddedTrelMinusInitialCheckpoint :
    rankCheckpointVector embeddedTrelMinusCheckpoints 0 =
      embeddedTrelMinusSeed.x := by
  native_decide

theorem embeddedTrelMinusCheckpointChunk :
    embeddedTrelMinusCheckpoints.chunk = 1024 := by
  native_decide

theorem embeddedTrelMinusCheckpointSteps :
    embeddedTrelMinusCheckpoints.steps = 33156 := by
  native_decide

theorem embeddedTrelMinusConstantCoefficientCanonical :
    embeddedTrelMinusCertificate.connectionConstantCoefficient.IsCanonical := by
  constructor <;> native_decide

end KnuthFasc8aEx210
