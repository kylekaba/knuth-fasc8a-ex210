import KnuthFasc8aEx210.EmbeddedRankData

namespace KnuthFasc8aEx210

def embeddedTrelPlusMatrixBytes : ByteArray :=
  include_hex_bytes% "data/blocks/Trel_plus.kmc"

def embeddedTrelPlusCertificateBytes : ByteArray :=
  include_hex_bytes% "data/certs/Trel_plus_border.kwc2"

def embeddedTrelPlusPadeBytes : ByteArray :=
  include_hex_bytes% "data/certs/Trel_plus_border.kpw1"

def embeddedTrelPlusEigenBytes : ByteArray :=
  include_hex_bytes% "data/certs/Trel_plus_eigen50.vec"

def embeddedTrelPlusCheckpointBytes : ByteArray :=
  include_hex_bytes% "data/certs/Trel_plus_border.krc1"

def embeddedTrelPlusHeader : MatrixHeader :=
  embeddedMatrixHeader embeddedTrelPlusMatrixBytes

def embeddedTrelPlusCertificate : RankCertificateFile :=
  embeddedRankCertificate embeddedTrelPlusCertificateBytes

def embeddedTrelPlusPade : PadeWitnessFile :=
  embeddedPadeWitness embeddedTrelPlusPadeBytes

def embeddedTrelPlusEigen : EigenvectorFile :=
  embeddedEigenvector embeddedTrelPlusEigenBytes

def embeddedTrelPlusCheckpoints : RankCheckpointFile :=
  embeddedRankCheckpoints embeddedTrelPlusCheckpointBytes

def embeddedTrelPlusSeed : KrylovSeedByteData :=
  rankSeedByteData embeddedTrelPlusCertificate.n embeddedTrelPlusCertificate.seed

theorem embeddedTrelPlus_metadata :
    embeddedTrelPlusHeader.n = 16831 ∧
    embeddedTrelPlusCertificate.n = 16832 ∧
    embeddedTrelPlusCertificate.degree = 16832 ∧
    embeddedTrelPlusCertificate.bmTerms = 33664 ∧
    embeddedTrelPlusCertificate.border = true ∧
    embeddedTrelPlusEigen.n = embeddedTrelPlusHeader.n ∧
    embeddedTrelPlusEigen.pivot = 0 ∧
    embeddedTrelPlusCheckpoints.order = embeddedTrelPlusCertificate.n ∧
    embeddedTrelPlusCheckpoints.steps = 2 * embeddedTrelPlusCertificate.degree ∧
    embeddedTrelPlusCheckpoints.chunk = 1024 ∧
    embeddedTrelPlusCheckpoints.count = 34 := by
  native_decide

end KnuthFasc8aEx210
