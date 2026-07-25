import Lean
import KnuthFasc8aEx210.VisibleCertificateSoundness

/-!
# Checked-in certificate bytes as closed Lean data

`include_hex_bytes%` reads a repository file while elaborating this module and
places a hexadecimal string literal in the resulting declaration.  Thus the
compiled proof term contains the bytes; theorem checking does not perform
runtime file I/O.  Hex encoding keeps the generated syntax and `.olean`
substantially smaller than a three-million-element `UInt8` array literal.
-/

namespace KnuthFasc8aEx210

open Lean Elab Term

def hexNibble (b : UInt8) : UInt8 :=
  if b.toNat < 58 then b - 48 else b - 87

def decodeHexBytes (hex : String) : ByteArray :=
  Id.run do
    let input := hex.toUTF8
    let mut output := ByteArray.emptyWithCapacity (input.size / 2)
    for i in [0 : input.size / 2] do
      output := output.push (16 * hexNibble input[2 * i]! +
        hexNibble input[2 * i + 1]!)
    pure output

syntax "include_hex_bytes% " str : term

elab_rules : term
  | `(include_hex_bytes% $path:str) => do
      let some fileName := path.raw.isStrLit?
        | throwErrorAt path "expected a file path"
      let bytes ← IO.FS.readBinFile fileName
      let digits := "0123456789abcdef".toUTF8
      let mut encoded := ByteArray.emptyWithCapacity (2 * bytes.size)
      for b in bytes do
        encoded := encoded.push digits[b.toNat / 16]!
        encoded := encoded.push digits[b.toNat % 16]!
      let some hex := String.fromUTF8? encoded
        | throwErrorAt path "internal hex encoding failure"
      elabTerm (← `(decodeHexBytes $(Syntax.mkStrLit hex))) none

/-- The checked-in symmetric closed transfer block. -/
def embeddedTallBytes : ByteArray :=
  include_hex_bytes% "data/blocks/Tall_plus.kmc"

/-- The checked-in closed terminal vector. -/
def embeddedTallFinishBytes : ByteArray :=
  include_hex_bytes% "data/blocks/Tall_finish.vec"

/-- The checked-in `76`-eigenvector polynomial. -/
def embeddedVisiblePolynomialBytes : ByteArray :=
  include_hex_bytes% "data/certs/visible76.poly"

/-- Bounded checkpoints for the checked-in visible Horner replay. -/
def embeddedVisibleHornerBytes : ByteArray :=
  include_hex_bytes% "data/certs/visible76.khc1"

private def emptyMatrixHeader : MatrixHeader where
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

private def emptyFinishVector : FinishVectorFile where
  n := 0
  values := ByteArray.empty

private def emptyPolynomial : PolynomialFile where
  length := 0
  degree := 0
  coefficients := ByteArray.empty

private def emptyHornerCheckpoints : HornerCheckpointFile where
  n := 0
  steps := 0
  chunk := 1
  count := 1
  values := ByteArray.empty

def embeddedTallHeader : MatrixHeader :=
  (parseMatrixHeader embeddedTallBytes).toOption.getD emptyMatrixHeader

def embeddedTallFinish : FinishVectorFile :=
  (parseFinishVector embeddedTallFinishBytes).toOption.getD emptyFinishVector

def embeddedVisiblePolynomial : PolynomialFile :=
  (parsePolynomial embeddedVisiblePolynomialBytes).toOption.getD emptyPolynomial

def embeddedVisibleHorner : HornerCheckpointFile :=
  (parseHornerCheckpoints embeddedVisibleHornerBytes).toOption.getD
    emptyHornerCheckpoints

theorem embeddedTallHeader_n : embeddedTallHeader.n = 18325 := by
  native_decide

def embeddedBare : Fin embeddedTallHeader.n :=
  ⟨0, by rw [embeddedTallHeader_n]; omega⟩

theorem embeddedVisibleHorner_metadata :
    embeddedVisibleHorner.n = embeddedTallHeader.n ∧
    embeddedVisibleHorner.steps = embeddedVisiblePolynomial.length ∧
    embeddedVisibleHorner.chunk = 1027 ∧
    embeddedVisibleHorner.count = 5 := by
  native_decide

end KnuthFasc8aEx210
