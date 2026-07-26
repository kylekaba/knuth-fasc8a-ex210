import KnuthFasc8aEx210.EmbeddedTrelMinusRankOrbitBasics
import KnuthFasc8aEx210.EmbeddedU1PlusRankData

namespace KnuthFasc8aEx210

noncomputable section

def embeddedU1PlusOrbit (k : Nat) : ByteArray :=
  normalKrylovOrbitBytes embeddedU1PlusMatrixBytes embeddedU1PlusHeader
    embeddedU1PlusSeed.dR embeddedU1PlusSeed.dL embeddedU1PlusSeed.x k

theorem embeddedU1PlusOrbit_add (a b : Nat) :
    embeddedU1PlusOrbit (a + b) =
      normalKrylovOrbitBytes embeddedU1PlusMatrixBytes embeddedU1PlusHeader
        embeddedU1PlusSeed.dR embeddedU1PlusSeed.dL
        (embeddedU1PlusOrbit a) b := by
  exact normalKrylovOrbitBytes_add embeddedU1PlusMatrixBytes
    embeddedU1PlusHeader embeddedU1PlusSeed.dR embeddedU1PlusSeed.dL
    embeddedU1PlusSeed.x a b

end

end KnuthFasc8aEx210
