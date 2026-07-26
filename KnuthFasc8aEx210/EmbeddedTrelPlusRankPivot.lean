import KnuthFasc8aEx210.EmbeddedTrelPlusRankData

namespace KnuthFasc8aEx210

/-! Keep this direct parsed-data check outside the large aggregate proof.  Native
code generation then sees only the embedded inputs, rather than the 33 stitched
checkpoint theorems. -/

theorem embeddedTrelPlusEigenValueAtZero_ne_zero :
    eigenValueAt embeddedTrelPlusEigen 0 ≠ 0 := by
  native_decide

theorem embeddedTrelPlusInitialCheckpoint :
    rankCheckpointVector embeddedTrelPlusCheckpoints 0 =
      embeddedTrelPlusSeed.x := by
  native_decide

theorem embeddedTrelPlusCheckpointChunk :
    embeddedTrelPlusCheckpoints.chunk = 1024 := by
  native_decide

theorem embeddedTrelPlusCheckpointSteps :
    embeddedTrelPlusCheckpoints.steps = 33664 := by
  native_decide

theorem embeddedTrelPlusConstantCoefficientCanonical :
    embeddedTrelPlusCertificate.connectionConstantCoefficient.IsCanonical := by
  constructor <;> native_decide

end KnuthFasc8aEx210
