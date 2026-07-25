import KnuthFasc8aEx210.EmbeddedTrelPlusRankData

namespace KnuthFasc8aEx210

noncomputable section

theorem borderKrylovOrbitBytes_add (matrixBytes : ByteArray)
    (header : MatrixHeader) (eig : EigenvectorFile) (dR dL x : ByteArray)
    (a b : Nat) :
    borderKrylovOrbitBytes matrixBytes header eig dR dL x (a + b) =
      borderKrylovOrbitBytes matrixBytes header eig dR dL
        (borderKrylovOrbitBytes matrixBytes header eig dR dL x a) b := by
  induction b with
  | zero => simp [borderKrylovOrbitBytes]
  | succ b ih =>
      simp only [Nat.add_succ, borderKrylovOrbitBytes]
      congr 3

def embeddedTrelPlusOrbit (k : Nat) : ByteArray :=
  borderKrylovOrbitBytes embeddedTrelPlusMatrixBytes embeddedTrelPlusHeader
    embeddedTrelPlusEigen embeddedTrelPlusSeed.dR embeddedTrelPlusSeed.dL
    embeddedTrelPlusSeed.x k

theorem embeddedTrelPlusOrbit_add (a b : Nat) :
    embeddedTrelPlusOrbit (a + b) =
      borderKrylovOrbitBytes embeddedTrelPlusMatrixBytes embeddedTrelPlusHeader
        embeddedTrelPlusEigen embeddedTrelPlusSeed.dR embeddedTrelPlusSeed.dL
        (embeddedTrelPlusOrbit a) b := by
  exact borderKrylovOrbitBytes_add embeddedTrelPlusMatrixBytes
    embeddedTrelPlusHeader embeddedTrelPlusEigen embeddedTrelPlusSeed.dR
    embeddedTrelPlusSeed.dL embeddedTrelPlusSeed.x a b


end

end KnuthFasc8aEx210
