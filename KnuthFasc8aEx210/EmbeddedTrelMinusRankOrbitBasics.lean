import KnuthFasc8aEx210.EmbeddedTrelMinusRankData

namespace KnuthFasc8aEx210

noncomputable section

theorem normalKrylovOrbitBytes_add (matrixBytes : ByteArray)
    (header : MatrixHeader) (dR dL x : ByteArray) (a b : Nat) :
    normalKrylovOrbitBytes matrixBytes header dR dL x (a + b) =
      normalKrylovOrbitBytes matrixBytes header dR dL
        (normalKrylovOrbitBytes matrixBytes header dR dL x a) b := by
  induction b with
  | zero => simp [normalKrylovOrbitBytes]
  | succ b ih =>
      simp only [normalKrylovOrbitBytes]
      congr 3

def embeddedTrelMinusOrbit (k : Nat) : ByteArray :=
  normalKrylovOrbitBytes embeddedTrelMinusMatrixBytes embeddedTrelMinusHeader
    embeddedTrelMinusSeed.dR embeddedTrelMinusSeed.dL embeddedTrelMinusSeed.x k

theorem embeddedTrelMinusOrbit_add (a b : Nat) :
    embeddedTrelMinusOrbit (a + b) =
      normalKrylovOrbitBytes embeddedTrelMinusMatrixBytes embeddedTrelMinusHeader
        embeddedTrelMinusSeed.dR embeddedTrelMinusSeed.dL
        (embeddedTrelMinusOrbit a) b := by
  exact normalKrylovOrbitBytes_add embeddedTrelMinusMatrixBytes
    embeddedTrelMinusHeader embeddedTrelMinusSeed.dR embeddedTrelMinusSeed.dL
    embeddedTrelMinusSeed.x a b

end

end KnuthFasc8aEx210
