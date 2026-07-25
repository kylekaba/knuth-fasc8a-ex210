import KnuthFasc8aEx210.EmbeddedCertificateData
import KnuthFasc8aEx210.RankCheckpointSoundness

/-!
# Shared parsing defaults for embedded rank certificates

Concrete per-block modules embed their files independently so Lake can compile
long rank replays in parallel without making every segment initialize all six
matrices.
-/

namespace KnuthFasc8aEx210

def emptyEmbeddedMatrixHeader : MatrixHeader where
  n := 0
  prime := 0
  entries := 0
  rowPtrOffset := 0
  colIndexOffset := 0
  valueOffset := 0
  rowPtrBytes := 0
  colIndexBytes := 0
  valueBytes := 0
  trailingBytes := 0

def emptyEmbeddedRankCertificate : RankCertificateFile where
  version := 0
  prime := 0
  nonresidue := 0
  n := 0
  lambda := 0
  border := false
  pivot := 0
  terms := 0
  bmTerms := 0
  degree := 0
  seed := 0
  matrixHash := 0
  eigenHash := 0
  constantA := 0
  constantB := 0
  moments := ByteArray.empty
  coefficients := ByteArray.empty

def emptyEmbeddedPadeWitness : PadeWitnessFile where
  version := 0
  prime := 0
  nonresidue := 0
  degree := 0
  uLength := 0
  vLength := 0
  certificateHash := 0
  uCoefficients := ByteArray.empty
  vCoefficients := ByteArray.empty

def emptyEmbeddedEigenvector : EigenvectorFile where
  n := 0
  pivot := 0
  values := ByteArray.empty
  pivotValue := 0
  length := 0

def emptyEmbeddedRankCheckpoints : RankCheckpointFile where
  version := 0
  order := 0
  steps := 0
  chunk := 1
  count := 1
  seed := 0
  matrixHash := 0
  eigenHash := 0
  values := ByteArray.empty

def embeddedMatrixHeader (bytes : ByteArray) : MatrixHeader :=
  (parseMatrixHeader bytes).toOption.getD emptyEmbeddedMatrixHeader

def embeddedRankCertificate (bytes : ByteArray) : RankCertificateFile :=
  (parseRankCertificate bytes).toOption.getD emptyEmbeddedRankCertificate

def embeddedPadeWitness (bytes : ByteArray) : PadeWitnessFile :=
  (parsePadeWitness bytes).toOption.getD emptyEmbeddedPadeWitness

def embeddedEigenvector (bytes : ByteArray) : EigenvectorFile :=
  (parseEigenvector bytes).toOption.getD emptyEmbeddedEigenvector

def embeddedRankCheckpoints (bytes : ByteArray) : RankCheckpointFile :=
  (parseRankCheckpoints bytes).toOption.getD emptyEmbeddedRankCheckpoints

end KnuthFasc8aEx210
