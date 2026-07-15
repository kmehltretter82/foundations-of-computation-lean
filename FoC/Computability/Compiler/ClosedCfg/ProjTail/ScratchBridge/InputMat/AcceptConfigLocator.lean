import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.InPlaceDecoderCopier
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape
namespace CountWindowInputMat
namespace AcceptConfigCopy

open EncRewriters.CanonicalLayouts.DovetailLayoutScanner

inductive Kind where
  | transition
  | tick
  | done
  | blank
  | zero
  | one
deriving DecidableEq, Repr

def Kind.bits : Kind -> Word Bool
  | .transition => [false, false, false, true]
  | .tick => [false, false, true, false]
  | .done => [false, false, true, true]
  | .blank => [false, true, false, false]
  | .zero => [false, true, false, true]
  | .one => [false, true, true, false]

inductive Phase where
  | layoutHeader
  | inputLength
  | inputCells
  | stage
  | initialize
deriving DecidableEq, Repr

def phaseIndex : Phase -> Nat
  | .layoutHeader => 0
  | .inputLength => 1
  | .inputCells => 2
  | .stage => 3
  | .initialize => 4

def tokenBlockSize : Nat := 40

def tokenBase (phase : Phase) : Nat :=
  tokenBlockSize * phaseIndex phase

def pendingBase : Nat := 5 * tokenBlockSize

def boolNat : Bool -> Nat
  | false => 0
  | true => 1

def pendingIndex (b0 b1 b2 b3 : Bool) : Nat :=
  8 * boolNat b0 + 4 * boolNat b1 + 2 * boolNat b2 + boolNat b3

def pendingState (b0 b1 b2 b3 : Bool) : Nat :=
  pendingBase + 5 * pendingIndex b0 b1 b2 b3

def halt : Nat := pendingBase + 5 * 16

def route (phase : Phase) (kind : Kind) : Nat :=
  match phase, kind with
  | .layoutHeader, .transition => tokenBase .inputLength
  | .inputLength, .tick => tokenBase .inputLength
  | .inputLength, .done => tokenBase .inputCells
  | .inputCells, .zero => tokenBase .inputCells
  | .inputCells, .one => tokenBase .inputCells
  | .inputCells, .tick => tokenBase .stage
  | .inputCells, .done => tokenBase .initialize
  | .stage, .tick => tokenBase .stage
  | .stage, .done => tokenBase .initialize
  | .initialize, .tick => pendingState false false true false
  | .initialize, .done => pendingState false false true true
  | _, _ => halt

def rowsForSourceRead
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReadCells.map
    (fun read2 =>
      row source sourceRead none read2 action0 action1 action2 target)

def wrappedBitRows
    (source targetFalse targetTrue : Nat)
    (action2 : TapeAction := keepS) : List Transition :=
  [ rowsForSourceRead source (some false) keepR keepS keepS (source + 1)
  , rowsForSourceRead (source + 1) (some true) keepR keepS action2 (source + 2)
  , rowsForSourceRead (source + 2) (some false) keepR keepS keepS (source + 3)
  , rowsForSourceRead (source + 2) (some true) keepR keepS keepS (source + 4)
  , rowsForSourceRead (source + 3) (some true) keepR keepS keepS targetFalse
  , rowsForSourceRead (source + 4) (some false) keepR keepS keepS targetTrue ].flatten

def tokenBlockRows (phase : Phase) : List Transition :=
  let base := tokenBase phase
  [ wrappedBitRows base (base + 5) halt
  , wrappedBitRows (base + 5) (base + 10) (base + 15)
  , wrappedBitRows (base + 10) (base + 20) (base + 25)
  , wrappedBitRows (base + 15) (base + 30) (base + 35)
  , wrappedBitRows (base + 20) halt (route phase .transition)
  , wrappedBitRows (base + 25) (route phase .tick) (route phase .done)
  , wrappedBitRows (base + 30) (route phase .blank) (route phase .zero)
  , wrappedBitRows (base + 35) (route phase .one) halt ].flatten

def pendingRows (b0 b1 b2 b3 : Bool) : List Transition :=
  let source := pendingState b0 b1 b2 b3
  [ rowsForSourceRead source (some false) keepR keepS keepS (source + 1)
  , rowsForSourceRead (source + 1) (some false) keepL keepS keepS halt
  , rowsForSourceRead (source + 1) (some true)
      keepR keepS (writeBitR b0) (source + 2)
  , rowsForSourceRead (source + 2) (some false)
      keepR keepS keepS (source + 3)
  , rowsForSourceRead (source + 2) (some true)
      keepR keepS keepS (source + 4)
  , rowsForSourceRead (source + 3) (some true)
      keepR keepS keepS (pendingState b1 b2 b3 false)
  , rowsForSourceRead (source + 4) (some false)
      keepR keepS keepS (pendingState b1 b2 b3 true) ].flatten

def bools : List Bool := [false, true]

def layoutHeaderRows : List Transition :=
  tokenBlockRows .layoutHeader

def inputLengthRows : List Transition :=
  tokenBlockRows .inputLength

def inputCellsRows : List Transition :=
  tokenBlockRows .inputCells

def stageRows : List Transition :=
  tokenBlockRows .stage

def initializeRows : List Transition :=
  tokenBlockRows .initialize

def allPendingRows : List Transition :=
  bools.flatMap (fun b0 =>
    bools.flatMap (fun b1 =>
      bools.flatMap (fun b2 =>
        bools.flatMap (fun b3 => pendingRows b0 b1 b2 b3))))

def prefixRows : List Transition :=
  List.append layoutHeaderRows
    inputLengthRows

def cellsStageRows : List Transition :=
  List.append inputCellsRows stageRows

def copyRows : List Transition :=
  List.append initializeRows allPendingRows

def prefixDescription : Description :=
  ThreeTape.description (halt + 1)
    (tokenBase .layoutHeader) (tokenBase .inputCells) prefixRows

def cellsStageDescription : Description :=
  ThreeTape.description (halt + 1)
    (tokenBase .inputCells) (tokenBase .initialize) cellsStageRows

def copyDescription : Description :=
  ThreeTape.description (halt + 1) (tokenBase .initialize) halt copyRows

syntax "copy_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| copy_step [$lemmas,*]) =>
      `(tactic|
        simp (config := { maxSteps := 1000000 }) [
          ThreeTape.row, ThreeTape.config, ThreeTape.description,
          ThreeTape.keepL, ThreeTape.keepR, ThreeTape.keepS,
          ThreeTape.writeL, ThreeTape.writeR, ThreeTape.writeS,
          ThreeTape.eraseL, ThreeTape.eraseR,
          ThreeTape.writeBitL, ThreeTape.writeBitR,
          Description.applyActions_three, Description.runConfig,
          Description.stepConfig, Description.lookupTransition,
          Description.Matches, TapeAction.apply, TapeAction.stay,
          HeadMove.apply, Tape.blank, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight, tapeAtCells,
          tokenBlockRows, wrappedBitRows,
          rowsForSourceRead, route, tokenBase, tokenBlockSize,
          phaseIndex, pendingState, pendingIndex, pendingBase,
          boolNat, halt, allReadCells, List.find?, $lemmas,*])

-- Readiness is checked after the exact run table is stable.

def scanTape
    (left : List (Option Bool)) (bits : List Bool) : Tape Bool :=
  tapeAtCells left (List.append (bits.map some) [none])

def wrappedKind (kind : Kind) : Word Bool :=
  cellsCodeBits (kind.bits.map some)

def TokenRun (D : Description) (phase : Phase) (kind : Kind) : Prop :=
  forall (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool),
    D.runConfig 16
        (config (tokenBase phase)
          (scanTape left (List.append (wrappedKind kind) rest))
          Tape.blank T2) =
      config (route phase kind)
        (scanTape
          (List.append ((wrappedKind kind).reverse.map some) left)
          rest)
        Tape.blank T2

syntax "solve_token" ident "on" ident "with"
  "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| solve_token $rest:ident on $T2:ident with [$lemmas,*]) =>
      `(tactic|
        cases $rest:ident <;>
          cases h2 : ($T2:ident).head with
          | none =>
              copy_step [h2, $lemmas,*, scanTape, wrappedKind, Kind.bits,
                cellsCodeBits, cellCodeBits, encodeCodeWordAsInput,
                encodeCodeSymbolAsInput, encodeCell, tapeAtCells,
                List.reverse_append, List.map_append, List.append_assoc]
          | some bit =>
              cases bit <;>
                copy_step [h2, $lemmas,*, scanTape, wrappedKind, Kind.bits,
                  cellsCodeBits, cellCodeBits, encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput, encodeCell, tapeAtCells,
                  List.reverse_append, List.map_append,
                  List.append_assoc])

theorem header_token_run :
    TokenRun prefixDescription .layoutHeader .transition := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [prefixDescription, prefixRows,
    layoutHeaderRows]

theorem inputLength_tick_run :
    TokenRun prefixDescription .inputLength .tick := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [prefixDescription, prefixRows,
    layoutHeaderRows, inputLengthRows]

theorem inputLength_done_run :
    TokenRun prefixDescription .inputLength .done := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [prefixDescription, prefixRows,
    layoutHeaderRows, inputLengthRows]

theorem inputCells_tick_run :
    TokenRun cellsStageDescription .inputCells .tick := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [cellsStageDescription, cellsStageRows,
    inputCellsRows]

theorem inputCells_done_run :
    TokenRun cellsStageDescription .inputCells .done := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [cellsStageDescription, cellsStageRows,
    inputCellsRows]

theorem inputCells_zero_run :
    TokenRun cellsStageDescription .inputCells .zero := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [cellsStageDescription, cellsStageRows,
    inputCellsRows]

theorem inputCells_one_run :
    TokenRun cellsStageDescription .inputCells .one := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [cellsStageDescription, cellsStageRows,
    inputCellsRows]

theorem stage_tick_run :
    TokenRun cellsStageDescription .stage .tick := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [cellsStageDescription, cellsStageRows,
    inputCellsRows, stageRows]

theorem stage_done_run :
    TokenRun cellsStageDescription .stage .done := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [cellsStageDescription, cellsStageRows,
    inputCellsRows, stageRows]

theorem initialize_tick_run :
    TokenRun copyDescription .initialize .tick := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [copyDescription, copyRows, initializeRows]

theorem initialize_done_run :
    TokenRun copyDescription .initialize .done := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [copyDescription, copyRows, initializeRows]

end AcceptConfigCopy
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
