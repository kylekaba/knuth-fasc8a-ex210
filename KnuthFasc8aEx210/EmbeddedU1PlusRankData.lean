import KnuthFasc8aEx210.EmbeddedRankData

namespace KnuthFasc8aEx210

def embeddedU1PlusMatrixBytes : ByteArray :=
  include_hex_bytes% "data/blocks/U1_plus.kmc"

def embeddedU1PlusCertificateBytes : ByteArray :=
  include_hex_bytes% "data/certs/U1_plus_shift50.kwc2"

def embeddedU1PlusPadeBytes : ByteArray :=
  include_hex_bytes% "data/certs/U1_plus_shift50.kpw1"

def embeddedU1PlusCheckpointBytes : ByteArray :=
  include_hex_bytes% "data/certs/U1_plus_shift50.krc1"

def embeddedU1PlusHeader : MatrixHeader :=
  embeddedMatrixHeader embeddedU1PlusMatrixBytes

def embeddedU1PlusCertificate : RankCertificateFile :=
  embeddedRankCertificate embeddedU1PlusCertificateBytes

def embeddedU1PlusPade : PadeWitnessFile :=
  embeddedPadeWitness embeddedU1PlusPadeBytes

def embeddedU1PlusCheckpoints : RankCheckpointFile :=
  embeddedRankCheckpoints embeddedU1PlusCheckpointBytes

def embeddedU1PlusSeed : KrylovSeedByteData :=
  rankSeedByteData embeddedU1PlusCertificate.n embeddedU1PlusCertificate.seed

theorem embeddedU1Plus_metadata :
    embeddedU1PlusHeader.n = 25617 ∧
    embeddedU1PlusCertificate.n = 25617 ∧
    embeddedU1PlusCertificate.degree = 25617 ∧
    embeddedU1PlusCertificate.bmTerms = 51234 ∧
    embeddedU1PlusCertificate.border = false ∧
    embeddedU1PlusCheckpoints.order = embeddedU1PlusCertificate.n ∧
    embeddedU1PlusCheckpoints.steps = 2 * embeddedU1PlusCertificate.degree ∧
    embeddedU1PlusCheckpoints.chunk = 1024 ∧
    embeddedU1PlusCheckpoints.count = 52 := by
  native_decide

end KnuthFasc8aEx210
