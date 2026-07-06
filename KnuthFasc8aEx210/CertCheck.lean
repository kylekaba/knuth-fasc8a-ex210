import KnuthFasc8aEx210.CertificateFiles
import KnuthFasc8aEx210.SHA256

open System

namespace KnuthFasc8aEx210

structure RankExpectation where
  matrix : FilePath
  matrixSha256 : String
  cert : FilePath
  certSha256 : String
  eig : Option FilePath
  eigSha256 : Option String
  order : Nat
  degree : Nat
  constantA : UInt8
  constantB : UInt8
  border : Bool

def rankExpectations (root : FilePath) : List RankExpectation := [
  {
    matrix := root / "data/blocks/Trel_plus.kmc",
    matrixSha256 := "55c89f1883f95c0a9cce964bd2193dbc1220badf216a75e198f50b24da9844cb",
    cert := root / "data/certs/Trel_plus_border.kwc2",
    certSha256 := "f9f7c2a40d13b3dff6c0a35ae5c0a3123b30b7d7e89ccedc52e73461920dd97a",
    eig := some (root / "data/certs/Trel_plus_eigen50.vec"),
    eigSha256 := some "d38a64b7ef34ccfd4c714ac10970f996bc0ee7d5a76a6ef48f56da6920bb9ce9",
    order := 16832, degree := 16832,
    constantA := 23, constantB := 34, border := true
  },
  {
    matrix := root / "data/blocks/Trel_minus.kmc",
    matrixSha256 := "9a4b56c30ba48b25ba64034889d6ce10b2581ac18523870d7fa850fb294c107f",
    cert := root / "data/certs/Trel_minus_shift50.kwc2",
    certSha256 := "eec4d64aedb6aa679d0ff53fd64a02fce3e6764126cdcaecb2d34d771c697f38",
    eig := none,
    eigSha256 := none,
    order := 16578, degree := 16578,
    constantA := 56, constantB := 31, border := false
  },
  {
    matrix := root / "data/blocks/U1_plus.kmc",
    matrixSha256 := "5c21c664c261519e967635a02f10cb79cf945790f3b6828a20d346e55d6e3ce3",
    cert := root / "data/certs/U1_plus_shift50.kwc2",
    certSha256 := "eed6892a2fce9d5c3b229b5d3c6a418fa32a72125a7fbd7d6f6813d88bd6b992",
    eig := none,
    eigSha256 := none,
    order := 25617, degree := 25617,
    constantA := 80, constantB := 91, border := false
  },
  {
    matrix := root / "data/blocks/U1_minus.kmc",
    matrixSha256 := "8412832c21ec5be2b242882b3ef2d8d688c503d42a345efdf88c5d02de7dde53",
    cert := root / "data/certs/U1_minus_shift50.kwc2",
    certSha256 := "c05347fe795621b5b17b92bb44f29828747dfcec9e620ccabcb45d7c64b65ed6",
    eig := none,
    eigSha256 := none,
    order := 25495, degree := 25495,
    constantA := 89, constantB := 57, border := false
  },
  {
    matrix := root / "data/blocks/U2_plus.kmc",
    matrixSha256 := "0cf983f4721d5704fcfbde68571d600272fa03ff283355858d5735ea04b9ef88",
    cert := root / "data/certs/U2_plus_shift50.kwc2",
    certSha256 := "fed9c7c7ab70e7593d49a69ade95739d334bb23610c050e22e66751083053100",
    eig := none,
    eigSha256 := none,
    order := 23646, degree := 23646,
    constantA := 87, constantB := 46, border := false
  },
  {
    matrix := root / "data/blocks/U2_minus.kmc",
    matrixSha256 := "a2258bc6ad37442592c1d8a037aa4ba807b38d7c5dbde64a2307d86b2ff98faa",
    cert := root / "data/certs/U2_minus_shift50.kwc2",
    certSha256 := "0a9ecde164fd7a9fdc99e48576696d752bec017282e5a2ec7c29cd75ac917d7f",
    eig := none,
    eigSha256 := none,
    order := 23552, degree := 23552,
    constantA := 16, constantB := 38, border := false
  }
]

def readBin (path : FilePath) : IO ByteArray :=
  IO.FS.readBinFile path

def exceptToIO {α : Type} (context : String) : Except String α -> IO α
  | .ok x => pure x
  | .error e => throw <| IO.userError s!"{context}: {e}"

def verifySha256 (path : FilePath) (expected : String) (bytes : ByteArray) :
    IO Unit := do
  let actual := sha256Hex bytes
  if actual != expected then
    throw <| IO.userError
      s!"SHA-256 mismatch for {path}: expected {expected}, got {actual}"

def parseStepArg (default : Nat) (s : String) : Nat :=
  if s == "all" || s == "full" then
    1000000000
  else
    s.toNat?.getD default

def parseBMReplayFlag (s : String) : Bool :=
  s == "bm" || s == "stored-bm" || s == "all"

def checkKrylovMomentsWithProgress (label : String)
    (cert : RankCertificateFile) (matrixBytes : ByteArray)
    (header : MatrixHeader) (eig? : Option EigenvectorFile)
    (count : Nat) : IO Nat := do
  let expectedOrder := header.n + if eig?.isSome then 1 else 0
  if cert.n != expectedOrder then
    throw <| IO.userError "certificate order does not match operator dimension"
  let seedData := rankSeedByteData cert.n cert.seed
  let mut x := seedData.x
  let mut bad := 0
  let limit := Nat.min count cert.terms
  let progressStride := 5000
  let showProgress := progressStride <= limit
  for k in [0:limit] do
    let actual := extDotBytes seedData.u x cert.n
    let expected := pairAt cert.moments k
    if actual != expected then
      bad := bad + 1
    if k + 1 < limit then
      x ← exceptToIO s!"Krylov step {label}"
        (krylovStepBytes matrixBytes header eig? seedData.dR seedData.dL x cert.n)
    let done := k + 1
    if showProgress && (done % progressStride == 0 || done == limit) then
      IO.eprintln s!"krylov {label}: checked {done}/{limit} moments, bad={bad}"
  pure bad

def checkVisibleFiles (root : FilePath) (visiblePrefixSteps : Nat) : IO Unit := do
  let tallBytes ← readBin (root / "data/blocks/Tall_plus.kmc")
  verifySha256 (root / "data/blocks/Tall_plus.kmc")
    "c04a0b08245462f519736bac506411b5f1936a386e83c03934223d2184bd00ed"
    tallBytes
  let tall ← exceptToIO "Tall_plus.kmc" (parseMatrixHeader tallBytes)
  let tallValidation ← exceptToIO "Tall_plus.kmc CSR" (validateMatrixCSR tallBytes tall)
  let finishBytes ← readBin (root / "data/blocks/Tall_finish.vec")
  verifySha256 (root / "data/blocks/Tall_finish.vec")
    "b1e5eb2e9f27b164a28716b02879e130e5a8057c9b26f341eb013241420bcb85"
    finishBytes
  let finish ← exceptToIO "Tall_finish.vec" (parseFinishVector finishBytes)
  if finish.n != tall.n then
    throw <| IO.userError
      s!"finish vector dimension {finish.n} does not match Tall_plus dimension {tall.n}"
  let polyBytes ← readBin (root / "data/certs/visible76.poly")
  verifySha256 (root / "data/certs/visible76.poly")
    "4add074b2bfbfe3f51d9449e7291ef008c3ab4963d772fd8a51283bbcf004dc6"
    polyBytes
  let poly ← exceptToIO "visible76.poly" (parsePolynomial polyBytes)
  if poly.degree != 4106 then
    throw <| IO.userError s!"visible polynomial degree {poly.degree}, expected 4106"
  let relBytes ← readBin (root / "data/blocks/Trel_plus.kmc")
  verifySha256 (root / "data/blocks/Trel_plus.kmc")
    "55c89f1883f95c0a9cce964bd2193dbc1220badf216a75e198f50b24da9844cb"
    relBytes
  let rel ← exceptToIO "Trel_plus.kmc" (parseMatrixHeader relBytes)
  let relValidation ← exceptToIO "Trel_plus.kmc CSR" (validateMatrixCSR relBytes rel)
  let eigBytes ← readBin (root / "data/certs/Trel_plus_eigen50.vec")
  verifySha256 (root / "data/certs/Trel_plus_eigen50.vec")
    "d38a64b7ef34ccfd4c714ac10970f996bc0ee7d5a76a6ef48f56da6920bb9ce9"
    eigBytes
  let eig ← exceptToIO "Trel_plus_eigen50.vec" (parseEigenvector eigBytes)
  if eig.n != 16831 || eig.pivot != 0 || eig.pivotValue != 37 then
    throw <| IO.userError s!"unexpected Trel_plus_eigen50.vec metadata: {eig.summary}"
  if rel.n != eig.n then
    throw <| IO.userError
      s!"Trel_plus dimension {rel.n} does not match eigenvector dimension {eig.n}"
  if visiblePrefixSteps < poly.length then
    let visiblePrefix ← exceptToIO "visible polynomial prefix"
      (visiblePolynomialHornerPrefix tallBytes tall poly finish visiblePrefixSteps)
    if visiblePrefix.size != tall.n then
      throw <| IO.userError
        s!"visible prefix vector size {visiblePrefix.size} does not match Tall_plus dimension {tall.n}"
    IO.println s!"PASS Lean parse visible files: Tall_plus_n={tallValidation.rows}, Tall_plus_entries={tallValidation.entries}, Trel_plus_n={relValidation.rows}, Trel_plus_entries={relValidation.entries}, finish_n={finish.n}, degree(g)={poly.degree}, visible_prefix_steps={Nat.min visiblePrefixSteps poly.length}, visible_prefix_bare={visiblePrefix[0]!.toNat}, eig_n={eig.n}, pivot={eig.pivot}, pivot_value={eig.pivotValue.toNat}, sha256=ok"
  else
    let visible ← exceptToIO "full visible-factor check"
      (visibleFactorFullCheck tallBytes tall relBytes rel poly finish eig)
    if visible.eigen76Bad != 0 then
      throw <| IO.userError
        s!"visible 76-eigenvector check failed: {visible.eigen76Bad} bad rows"
    if visible.rBare == 0 then
      throw <| IO.userError "visible 76-eigenvector has zero bare coordinate"
    if visible.eigen50Bad != 0 then
      throw <| IO.userError
        s!"visible 50-eigenvector check failed: {visible.eigen50Bad} bad rows"
    if visible.vBare == 0 then
      throw <| IO.userError "visible 50-eigenvector has zero bare coordinate"
    if visible.restrictedMismatch != 0 then
      throw <| IO.userError
        s!"restricted Trel_plus eigenvector comparison failed: {visible.restrictedMismatch} mismatches"
    IO.println s!"PASS Lean full visible factor: Tall_plus_n={tallValidation.rows}, Tall_plus_entries={tallValidation.entries}, Trel_plus_n={relValidation.rows}, Trel_plus_entries={relValidation.entries}, finish_n={finish.n}, degree(g)={poly.degree}, r_bare={visible.rBare.toNat}, v_bare={visible.vBare.toNat}, eigen76_bad={visible.eigen76Bad}, eigen50_bad={visible.eigen50Bad}, restricted_mismatch={visible.restrictedMismatch}, pivot={eig.pivot}, pivot_value={eig.pivotValue.toNat}, sha256=ok"

def checkRankFile (e : RankExpectation) (krylovPrefixMoments : Nat)
    (replayBM : Bool) : IO Unit := do
  let matrixBytes ← readBin e.matrix
  verifySha256 e.matrix e.matrixSha256 matrixBytes
  let matrix ← exceptToIO s!"matrix {e.matrix}" (parseMatrixHeader matrixBytes)
  let matrixValidation ← exceptToIO s!"matrix CSR {e.matrix}" (validateMatrixCSR matrixBytes matrix)
  if matrix.prime != 101 then
    throw <| IO.userError s!"matrix {e.matrix} has prime {matrix.prime}, expected 101"
  let certBytes ← readBin e.cert
  verifySha256 e.cert e.certSha256 certBytes
  let cert ← exceptToIO s!"certificate {e.cert}" (parseRankCertificate certBytes)
  let c0 := cert.connectionLeadingCoefficient
  if c0.a != 1 || c0.b != 0 then
    throw <| IO.userError
      s!"connection polynomial for {e.cert} does not start with 1: {c0.a.toNat}+{c0.b.toNat}t"
  let initialRecurrenceBad := cert.initialRecurrenceBad
  if initialRecurrenceBad != 0 then
    throw <| IO.userError
      s!"initial stored recurrence check failed for {e.cert}: {initialRecurrenceBad} bad moments"
  let recurrenceBad := cert.extraRecurrenceBad
  if recurrenceBad != 0 then
    throw <| IO.userError
      s!"extra recurrence check failed for {e.cert}: {recurrenceBad} bad moments"
  if cert.n != e.order || cert.degree != e.degree ||
      cert.constantA != e.constantA || cert.constantB != e.constantB ||
      cert.border != e.border then
    throw <| IO.userError
      s!"unexpected certificate metadata for {e.cert}: n={cert.n}, degree={cert.degree}, constant={cert.constantA.toNat}+{cert.constantB.toNat}t, border={cert.border}"
  if cert.matrixHash != fnv64Bytes matrixBytes then
    throw <| IO.userError s!"matrix hash mismatch for {e.cert}"
  let (eigForKrylov?, eigenResidualBad?) ←
    match e.eig with
    | none =>
        if cert.eigenHash != 0 then
          throw <| IO.userError s!"non-border certificate {e.cert} has nonzero eigen hash"
        pure (none, none)
    | some eigPath =>
      let eigBytes ← readBin eigPath
      match e.eigSha256 with
      | none =>
          throw <| IO.userError s!"missing expected SHA-256 for eigenvector {eigPath}"
      | some expected =>
          verifySha256 eigPath expected eigBytes
      let eig ← exceptToIO s!"eigenvector {eigPath}" (parseEigenvector eigBytes)
      if eig.n + 1 != cert.n || eig.pivot != cert.pivot || eig.pivotValue == 0 then
        throw <| IO.userError s!"eigenvector metadata mismatch for {e.cert}: {eig.summary}"
      if cert.eigenHash != fnv64Bytes eigBytes then
        throw <| IO.userError s!"eigenvector hash mismatch for {e.cert}"
      let residualBad ← exceptToIO s!"eigenvector residual {eigPath}"
        (eigenResidualBadRows matrixBytes matrix eig)
      if residualBad != 0 then
        throw <| IO.userError
          s!"eigenvector residual check failed for {e.cert}: {residualBad} bad rows"
      pure (some eig, some residualBad)
  let krylovRequested := Nat.min krylovPrefixMoments cert.terms
  let krylovPrefixBad ←
    checkKrylovMomentsWithProgress (toString e.cert) cert matrixBytes matrix
      eigForKrylov? krylovPrefixMoments
  if krylovPrefixBad != 0 then
    throw <| IO.userError
      s!"Krylov moment check failed for {e.cert}: {krylovPrefixBad} bad moments"
  let krylovText :=
    if krylovRequested == cert.terms then
      s!"krylov_bad={krylovPrefixBad}/{krylovRequested} (full)"
    else
      s!"krylov_prefix_bad={krylovPrefixBad}/{krylovRequested}"
  let bmText ←
    if replayBM then
      let bm ← exceptToIO s!"BM replay {e.cert}" cert.bmReplayCheck
      if bm.degree != cert.degree then
        throw <| IO.userError
          s!"BM replay degree mismatch for {e.cert}: got {bm.degree}, expected {cert.degree}"
      if bm.coefficientBad != 0 then
        throw <| IO.userError
          s!"BM replay coefficient mismatch for {e.cert}: {bm.coefficientBad} bad coefficients"
      pure s!", bm_replay_degree={bm.degree}, bm_coefficient_bad={bm.coefficientBad}"
    else
      pure ", bm_replay=skipped"
  let seedSummary := rankSeedExpansionSummary cert.n cert.seed
  let residualText :=
    match eigenResidualBad? with
    | none => "n/a"
    | some n => toString n
  IO.println s!"PASS Lean rank cert content: {e.cert}, n={cert.n}, constant={cert.constantA.toNat}+{cert.constantB.toNat}t, {krylovText}{bmText}, initial_recurrence_bad={initialRecurrenceBad}, extra_recurrence_bad={recurrenceBad}, eigen_residual_bad={residualText}, seed_diag_rejections={seedSummary.diagonalRejections}, matrix_n={matrixValidation.rows}, entries={matrixValidation.entries}, sha256=ok"

def run (args : List String) : IO UInt32 := do
  let root : FilePath :=
    match args with
    | [] => "."
    | x :: _ => x
  let krylovPrefixMoments : Nat :=
    match args with
    | _ :: k :: _ => parseStepArg 2 k
    | _ => 2
  let visiblePrefixSteps : Nat :=
    match args with
    | _ :: _ :: k :: _ => parseStepArg 2 k
    | _ => 2
  let replayBM : Bool :=
    match args with
    | _ :: _ :: _ :: mode :: _ => parseBMReplayFlag mode
    | _ => false
  let rankLimit : Nat :=
    match args with
    | _ :: _ :: _ :: _ :: limit :: _ => limit.toNat?.getD (rankExpectations root).length
    | _ => (rankExpectations root).length
  try
    checkVisibleFiles root visiblePrefixSteps
    for e in (rankExpectations root).take rankLimit do
      checkRankFile e krylovPrefixMoments replayBM
    IO.println "Lean certificate-file checks completed."
    pure 0
  catch err =>
    IO.eprintln s!"FAIL: {err}"
    pure 1

end KnuthFasc8aEx210

def main (args : List String) : IO UInt32 :=
  KnuthFasc8aEx210.run args
