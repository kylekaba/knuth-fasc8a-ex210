import KnuthFasc8aEx210.EmbeddedRankData

namespace KnuthFasc8aEx210

def embeddedTrelMinusMatrixBytes : ByteArray :=
  include_hex_bytes% "data/blocks/Trel_minus.kmc"

def embeddedTrelMinusCertificateBytes : ByteArray :=
  include_hex_bytes% "data/certs/Trel_minus_shift50.kwc2"

def embeddedTrelMinusPadeBytes : ByteArray :=
  include_hex_bytes% "data/certs/Trel_minus_shift50.kpw1"

def embeddedTrelMinusCheckpointBytes : ByteArray :=
  include_hex_bytes% "data/certs/Trel_minus_shift50.krc1"

def embeddedTrelMinusHeader : MatrixHeader :=
  embeddedMatrixHeader embeddedTrelMinusMatrixBytes

def embeddedTrelMinusCertificate : RankCertificateFile :=
  embeddedRankCertificate embeddedTrelMinusCertificateBytes

def embeddedTrelMinusPade : PadeWitnessFile :=
  embeddedPadeWitness embeddedTrelMinusPadeBytes

def embeddedTrelMinusCheckpoints : RankCheckpointFile :=
  embeddedRankCheckpoints embeddedTrelMinusCheckpointBytes

def embeddedTrelMinusSeed : KrylovSeedByteData :=
  rankSeedByteData embeddedTrelMinusCertificate.n embeddedTrelMinusCertificate.seed

theorem embeddedTrelMinus_metadata :
    embeddedTrelMinusHeader.n = 16578 ∧
    embeddedTrelMinusCertificate.n = 16578 ∧
    embeddedTrelMinusCertificate.degree = 16578 ∧
    embeddedTrelMinusCertificate.bmTerms = 33156 ∧
    embeddedTrelMinusCertificate.border = false ∧
    embeddedTrelMinusCheckpoints.order = embeddedTrelMinusCertificate.n ∧
    embeddedTrelMinusCheckpoints.steps = 2 * embeddedTrelMinusCertificate.degree ∧
    embeddedTrelMinusCheckpoints.chunk = 1024 ∧
    embeddedTrelMinusCheckpoints.count = 34 := by
  native_decide

end KnuthFasc8aEx210
