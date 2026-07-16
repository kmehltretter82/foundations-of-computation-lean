import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.RawPairMarker
import FoC.Computability.Compiler.Dovetail.Scanner.Simulator.Definitions
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.LengthCursorAddition

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.LengthAssembly

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CanonicalLayouts.DovetailLayoutScanner
open CanonicalLayouts.SimulatorLayoutScanner
open RawPairQuoter
open DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.FiniteTransducers.CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter

/-!
Post-marker serialization identities.

The first group of lemmas fixes the exact semantic currency required by the
tape-field serializer.  In particular, the left cells must be emitted in
`Tape.left` order even though the guarded logical representation stores their
physical chunks in the reverse traversal order.
-/

theorem quoted_left_eq_cellsCodeBits (T : Tape Bool) :
    quotedPairBits (T.left.map logicalCellPair) =
      cellsCodeBits T.left := by
  exact quotedPairBits_map_logicalCellPair T.left

theorem quoted_guarded_left_eq_reverse_cellsCodeBits (T : Tape Bool) :
    quotedPairBits (T.left.reverse.map logicalCellPair) =
      cellsCodeBits T.left.reverse := by
  exact quotedPairBits_map_logicalCellPair T.left.reverse

theorem quoted_head_right_eq_cellsCodeBits (T : Tape Bool) :
    quotedPairBits
        (logicalCellPair T.head :: T.right.map logicalCellPair) =
      List.append (cellCodeBits T.head) (cellsCodeBits T.right) := by
  change
    quotedPairBits
        ((T.head :: T.right).map logicalCellPair) =
      List.append (cellCodeBits T.head) (cellsCodeBits T.right)
  rw [quotedPairBits_map_logicalCellPair]
  rfl

def exactTapeFieldBits (T : Tape Bool) (suffix : Word Bool) : Word Bool :=
  List.append (stageNatBits T.left.length)
    (List.append (cellsCodeBits T.left)
      (List.append (cellCodeBits T.head)
        (List.append (stageNatBits T.right.length)
          (List.append (cellsCodeBits T.right) suffix))))

theorem tapeFieldBits_eq_exactTapeFieldBits
    (T : Tape Bool) (suffix : Word Bool) :
    tapeFieldBits T suffix = exactTapeFieldBits T suffix := by
  rfl

theorem configurationFieldBits_eq_state_tape
    (cfg : Configuration) (suffix : Word Bool) :
    configurationFieldBits cfg suffix =
      List.append (stageNatBits cfg.state)
        (exactTapeFieldBits cfg.tape suffix) := by
  rfl

def exactFieldsBits (F : ExactCloseout.Fields) : Word Bool :=
  simulatorLayoutFieldBits F.asLayout []

theorem exactFieldsBits_eq_outputBits (F : ExactCloseout.Fields) :
    exactFieldsBits F = F.outputBits := by
  rw [exactFieldsBits, ExactCloseout.Fields.outputBits]
  symm
  simpa [SimulatorLayout.asBoolInput, SimulatorLayout.encode,
    encodeCodeWordAsInput] using
    simulatorLayoutFieldBits_eq_encodeAppend F.asLayout []

theorem exactFieldsBits_eq_fields (F : ExactCloseout.Fields) :
    exactFieldsBits F =
      List.append headerPrefixBits
        (boolWordFieldBits F.input
          (List.append (stageNatBits F.stage)
            (List.append (stageNatBits F.config.state)
              (exactTapeFieldBits F.config.tape
                (boolFieldBits F.hit []))))) := by
  rfl

theorem index_target_normalizedOutput (i : Index) :
    Tape.normalizedOutput i.target = exactFieldsBits i.fields := by
  rw [Index.target, ExactCloseout.Fields.rightScratchTape]
  rw [Tape.normalizedOutput_move]
  rw [ExactCloseout.Fields.scratchTape_normalizedOutput]
  exact (exactFieldsBits_eq_outputBits i.fields).symm

/-!
The marker endpoint exposes exactly the two cell-code blocks used above.  The
only non-semantic work between this endpoint and `exactTapeFieldBits` is:

1. reverse the order of the four-bit chunks in the left block while preserving
   each chunk internally;
2. synthesize the two unary `stageNatBits` length prefixes;
3. prepend the finite state and the preserved metadata fields.
-/

theorem marker_target_left_payload (T : Tape Bool)
    (padding : List (Option Bool)) :
    (RawPairMarker.targetTape T padding).left =
      List.append
        ((List.append (cellsCodeBits T.left.reverse)
          [false, true, true, true]).reverse.map some)
        [none] := by
  rw [RawPairMarker.targetTape]
  rw [quoted_guarded_left_eq_reverse_cellsCodeBits]
  rfl

theorem marker_target_payload (T : Tape Bool)
    (padding : List (Option Bool)) :
    RawPairMarker.targetTape T padding =
      tapeAtCells
        (List.append
          ((List.append (cellsCodeBits T.left.reverse)
            [false, true, true, true]).reverse.map some)
          [none])
        (List.append
          ((List.append (cellCodeBits T.head)
            (cellsCodeBits T.right)).map some)
          (none :: padding)) := by
  rw [RawPairMarker.targetTape]
  rw [quoted_guarded_left_eq_reverse_cellsCodeBits]
  rw [quoted_head_right_eq_cellsCodeBits]

/-!
## Runtime length fields

The shared cursor proof is now stated for every `01xy` token, rather than only
the two Boolean-cell tokens.  Mapping `logicalCellPair` therefore specializes
it to all three `Option Bool` cells used by an exact tape encoding.
-/

theorem cellTokenBits_map_logicalCellPair
    (cells : List (Option Bool)) :
    rawBoundaryLengthCursorCellTokenBits
        (cells.map logicalCellPair) =
      cellsCodeBits cells := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          simp [rawBoundaryLengthCursorCellTokenBits, logicalCellPair,
            cellsCodeBits, cellCodeBits, encodeCell,
            encodeCodeWordAsInput, encodeCodeSymbolAsInput, ih]
      | some bit =>
          cases bit <;>
            simp [rawBoundaryLengthCursorCellTokenBits, logicalCellPair,
              cellsCodeBits, cellCodeBits, encodeCell,
              encodeCodeWordAsInput, encodeCodeSymbolAsInput, ih]

theorem cellTokenOutputBits_map_logicalCellPair
    (cells : List (Option Bool)) :
    rawBoundaryLengthCursorCellTokenOutputBits
        (cells.map logicalCellPair) =
      List.append (stageNatBits cells.length)
        (cellsCodeBits cells) := by
  simp [rawBoundaryLengthCursorCellTokenOutputBits,
    cellTokenBits_map_logicalCellPair]

theorem lengthCursor_haltsFrom_cellList
    (cells : List (Option Bool)) (blankTail : Nat)
    (right : List (Option Bool)) :
    rawBoundaryLengthCursorLoopDescription.HaltsFromTapeEquiv
      (rawBoundaryLengthCursorSeparatorTape
        (cellsCodeBits cells) blankTail right)
      (rawBoundaryLengthCursorSeparatorTape
        (List.append (stageNatBits cells.length) (cellsCodeBits cells))
        blankTail right) := by
  simpa [cellTokenBits_map_logicalCellPair,
    rawBoundaryLengthCursorCellTokenTargetTape,
    cellTokenOutputBits_map_logicalCellPair] using
    rawBoundaryLengthCursorLoopDescription_haltsFrom_cellTokens
      (cells.map logicalCellPair) blankTail right

end GuardedEgress.LengthAssembly
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
