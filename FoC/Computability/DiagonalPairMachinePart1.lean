import FoC.Computability.Coding
import FoC.Computability.Encoding

set_option doc.verso true

/-!
# Concrete diagonal pair machine

This module contains the explicit finite-machine witness for the concrete
diagonal pair map used in Chapter 5, Section 5.3.

The file defines the shared concrete pair-code vocabulary and the faithful
copy machine's alphabet and layout. The machine proves
{name}`FoC.Computability.FaithfulTuringComputable` by preserving the concrete
pair-code alphabet through injective encodings; the compatibility-level
{name}`FoC.Computability.TuringComputable` statement follows as a corollary in
Part 2. The legacy non-faithful marker machine that previously lived here was
deleted after a zero-consumer audit; see {lit}`docs/COMPILER_DELETION_LEDGER.md`.
-/

namespace FoC
namespace Computability

open Foundation
open Languages

def ConcretePairCodeSymbol (code : Type u) : Type u :=
  PairCodeSymbol code

def ConcreteDiagonalPairMap (w : Word code) :
    Word (ConcretePairCodeSymbol code) :=
  PairCodeSymbol.diagonalMap w

def ConcreteMachineCodeSymbol : Type :=
  MachineCodeSymbol

def ConcreteDiagonalPairMapComputable : Prop :=
  TuringComputable
    (ConcreteDiagonalPairMap :
      Word ConcreteMachineCodeSymbol ->
        Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))

def FaithfulConcreteDiagonalPairMapComputable : Prop :=
  FaithfulTuringComputable
    (ConcreteDiagonalPairMap :
      Word ConcreteMachineCodeSymbol ->
        Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))

def ConcreteMachineCodeSymbolFinite :
    Foundation.FiniteType ConcreteMachineCodeSymbol :=
  MachineCodeSymbol.finite

/-!
## Faithful copy machine

The faithful machine below preserves the concrete pair-code alphabet through an
injective output encoding. It scans the input once to append the separator,
rewinds to the left edge, and then processes input symbols from left to right.
For each raw code symbol it temporarily marks the left-copy cell, appends the
matching right-copy tag at the far right, returns to the temporary mark, turns
it into the final left tag, and advances to the next unprocessed raw cell.
-/

inductive FaithfulDiagonalPairMapMachineSymbol where
  | raw : ConcreteMachineCodeSymbol -> FaithfulDiagonalPairMapMachineSymbol
  | markLeft : ConcreteMachineCodeSymbol -> FaithfulDiagonalPairMapMachineSymbol
  | out : ConcretePairCodeSymbol ConcreteMachineCodeSymbol ->
      FaithfulDiagonalPairMapMachineSymbol

namespace FaithfulDiagonalPairMapMachineSymbol

def finite : Foundation.FiniteType FaithfulDiagonalPairMapMachineSymbol where
  elems :=
    ConcreteMachineCodeSymbolFinite.elems.map
      FaithfulDiagonalPairMapMachineSymbol.raw ++
    ConcreteMachineCodeSymbolFinite.elems.map
      FaithfulDiagonalPairMapMachineSymbol.markLeft ++
    (PairCodeSymbol.finite ConcreteMachineCodeSymbolFinite).elems.map
      FaithfulDiagonalPairMapMachineSymbol.out
  complete := by
    intro symbol
    cases symbol with
    | raw code =>
        simp [ConcreteMachineCodeSymbolFinite.complete code]
    | markLeft code =>
        simp [ConcreteMachineCodeSymbolFinite.complete code]
    | out pair =>
        simp
        exact (PairCodeSymbol.finite ConcreteMachineCodeSymbolFinite).complete
          pair

end FaithfulDiagonalPairMapMachineSymbol

inductive FaithfulDiagonalPairMapMachineState where
  | initStart
  | initScan
  | rewind
  | process
  | append : ConcreteMachineCodeSymbol -> FaithfulDiagonalPairMapMachineState
  | seekMark
  | halt

namespace FaithfulDiagonalPairMapMachineState

def finite : Foundation.FiniteType FaithfulDiagonalPairMapMachineState where
  elems :=
    [ FaithfulDiagonalPairMapMachineState.initStart
    , FaithfulDiagonalPairMapMachineState.initScan
    , FaithfulDiagonalPairMapMachineState.rewind
    , FaithfulDiagonalPairMapMachineState.process
    , FaithfulDiagonalPairMapMachineState.seekMark
    , FaithfulDiagonalPairMapMachineState.halt
    ] ++ ConcreteMachineCodeSymbolFinite.elems.map
      FaithfulDiagonalPairMapMachineState.append
  complete := by
    intro state
    cases state with
    | initStart => simp
    | initScan => simp
    | rewind => simp
    | process => simp
    | append code =>
        simp [ConcreteMachineCodeSymbolFinite.complete code]
    | seekMark => simp
    | halt => simp

end FaithfulDiagonalPairMapMachineState

inductive FaithfulDiagonalPairMapScanCell where
  | raw : ConcreteMachineCodeSymbol -> FaithfulDiagonalPairMapScanCell
  | separator : FaithfulDiagonalPairMapScanCell
  | right : ConcreteMachineCodeSymbol -> FaithfulDiagonalPairMapScanCell

def faithfulDiagonalPairMapInputEncode
    (code : ConcreteMachineCodeSymbol) :
    FaithfulDiagonalPairMapMachineSymbol :=
  FaithfulDiagonalPairMapMachineSymbol.raw code

def faithfulDiagonalPairMapOutputEncode
    (pair : ConcretePairCodeSymbol ConcreteMachineCodeSymbol) :
    FaithfulDiagonalPairMapMachineSymbol :=
  FaithfulDiagonalPairMapMachineSymbol.out pair

theorem faithfulDiagonalPairMapInputEncode_injective :
    Function.Injective faithfulDiagonalPairMapInputEncode := by
  intro a b h
  cases h
  rfl

theorem faithfulDiagonalPairMapOutputEncode_injective :
    Function.Injective faithfulDiagonalPairMapOutputEncode := by
  intro a b h
  cases h
  rfl

def faithfulDiagonalPairMapScanCellEncode :
    FaithfulDiagonalPairMapScanCell ->
      Option FaithfulDiagonalPairMapMachineSymbol
  | FaithfulDiagonalPairMapScanCell.raw code =>
      some (FaithfulDiagonalPairMapMachineSymbol.raw code)
  | FaithfulDiagonalPairMapScanCell.separator =>
      some (FaithfulDiagonalPairMapMachineSymbol.out
        PairCodeSymbol.separator)
  | FaithfulDiagonalPairMapScanCell.right code =>
      some (FaithfulDiagonalPairMapMachineSymbol.out
        (PairCodeSymbol.right code))

def faithfulDiagonalPairMapScanCells
    (remaining processed : Word ConcreteMachineCodeSymbol) :
    List FaithfulDiagonalPairMapScanCell :=
  remaining.map FaithfulDiagonalPairMapScanCell.raw ++
    [FaithfulDiagonalPairMapScanCell.separator] ++
      processed.map FaithfulDiagonalPairMapScanCell.right

def faithfulDiagonalPairMapScanTapeCells
    (cells : List FaithfulDiagonalPairMapScanCell) :
    List (Option FaithfulDiagonalPairMapMachineSymbol) :=
  cells.map faithfulDiagonalPairMapScanCellEncode

def faithfulDiagonalPairMapLeftCells
    (processed : Word ConcreteMachineCodeSymbol) :
    List (Option FaithfulDiagonalPairMapMachineSymbol) :=
  processed.map (fun code =>
    some (FaithfulDiagonalPairMapMachineSymbol.out
      (PairCodeSymbol.left code)))

def faithfulDiagonalPairMapRightCells
    (processed : Word ConcreteMachineCodeSymbol) :
    List (Option FaithfulDiagonalPairMapMachineSymbol) :=
  processed.map (fun code =>
    some (FaithfulDiagonalPairMapMachineSymbol.out
      (PairCodeSymbol.right code)))

def faithfulDiagonalPairMapLeftContext
    (processed : Word ConcreteMachineCodeSymbol) :
    List (Option FaithfulDiagonalPairMapMachineSymbol) :=
  (faithfulDiagonalPairMapLeftCells processed).reverse ++ [none]

def faithfulDiagonalPairMapMarkedLeftContext
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol) :
    List (Option FaithfulDiagonalPairMapMachineSymbol) :=
  some (FaithfulDiagonalPairMapMachineSymbol.markLeft code) ::
    faithfulDiagonalPairMapLeftContext processed

def faithfulDiagonalPairMapProcessScanTape
    (processed : Word ConcreteMachineCodeSymbol)
    (cells : List FaithfulDiagonalPairMapScanCell) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  match faithfulDiagonalPairMapScanTapeCells cells with
  | [] =>
      { left := faithfulDiagonalPairMapLeftContext processed
        head := none
        right := [] }
  | cell :: rest =>
      { left := faithfulDiagonalPairMapLeftContext processed
        head := cell
        right := rest }

def faithfulDiagonalPairMapProcessTape
    (processed remaining : Word ConcreteMachineCodeSymbol) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  faithfulDiagonalPairMapProcessScanTape processed
    (faithfulDiagonalPairMapScanCells remaining processed)

def faithfulDiagonalPairMapInitScanTape
    (seenRev rest : Word ConcreteMachineCodeSymbol) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  match rest with
  | [] =>
      { left :=
          seenRev.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code))
        head := none
        right := [] }
  | code :: suffix =>
      { left :=
          seenRev.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code))
        head := some (FaithfulDiagonalPairMapMachineSymbol.raw code)
        right :=
          suffix.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code)) }

end Computability
end FoC
