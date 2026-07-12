import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.RawPairDecoder
set_option doc.verso true
/-! # Guarded #18 head-marker split
The rewritten pair stream has four-bit cell tokens followed by the unique
{lit}`0111` head token. This scanner halts on the exact head-cell token. -/
namespace FoC
namespace Computability
open Languages
open MachineDescription
namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace GuardedEgress
namespace RawPairMarker
open CommonGround.FiniteTransducers
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open RawPairQuoter
def markerScanDescription : MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 1
    , transition 1 (some true) (some true) Direction.right 2
    , transition 2 (some false) (some false) Direction.right 3
    , transition 2 (some true) (some true) Direction.right 4
    , transition 3 (some false) (some false) Direction.right 0
    , transition 3 (some true) (some true) Direction.right 0
    , transition 4 (some false) (some false) Direction.right 0
    , transition 4 (some true) (some true) Direction.right 5 ]
theorem markerScanDescription_subroutineReady : markerScanDescription.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    markerScanDescription (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
private theorem cellsCodeBits_cons_map (cell : Option Bool) (rest : List (Option Bool)) :
    (cellsCodeBits (cell :: rest)).map some =
      List.append ((cellCodeBits cell).map some) ((cellsCodeBits rest).map some) := by
  cases cell with
  | none =>
      simp [cellsCodeBits, cellCodeBits, encodeCell, encodeCodeWordAsInput,
        encodeCodeSymbolAsInput]
  | some bit =>
      cases bit <;>
        simp [cellsCodeBits, cellCodeBits, encodeCell, encodeCodeWordAsInput,
          encodeCodeSymbolAsInput]
private theorem cellsCodeBits_cons_reverse_map (cell : Option Bool) (rest : List (Option Bool)) :
    (cellsCodeBits (cell :: rest)).reverse.map some =
      List.append ((cellsCodeBits rest).reverse.map some)
        ((cellCodeBits cell).reverse.map some) := by
  cases cell with
  | none =>
      simp [cellsCodeBits, cellCodeBits, encodeCell, encodeCodeWordAsInput,
        encodeCodeSymbolAsInput, List.map_append]
  | some bit =>
      cases bit <;>
        simp [cellsCodeBits, cellCodeBits, encodeCell, encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, List.map_append]
private theorem cellMap_append_assoc (cell : Option Bool) (rest : List (Option Bool))
    (right : List (Option Bool)) :
    List.append (List.append ((cellCodeBits cell).map some)
      ((cellsCodeBits rest).map some)) right =
      List.append ((cellCodeBits cell).map some)
        (List.append ((cellsCodeBits rest).map some) right) :=
  List.append_assoc _ _ _
private theorem reverseCellMap_append_assoc (cell : Option Bool) (rest : List (Option Bool))
    (left : List (Option Bool)) :
    List.append ((cellsCodeBits rest).reverse.map some)
        (List.append ((cellCodeBits cell).reverse.map some) left) =
      List.append (List.append ((cellsCodeBits rest).reverse.map some)
        ((cellCodeBits cell).reverse.map some)) left :=
  (List.append_assoc _ _ _).symm
private theorem markerScanDescription_run_cell (cell : Option Bool)
    (left right : List (Option Bool)) :
    markerScanDescription.runConfig 4
        { state := markerScanDescription.start, tape := tapeAtCells left
            (List.append ((cellCodeBits cell).map some) right) } =
      { state := markerScanDescription.start
        tape := tapeAtCells (List.append ((cellCodeBits cell).reverse.map some) left) right } := by
  cases cell with
  | none =>
      cases right <;>
        simp [markerScanDescription, cellCodeBits, encodeCell, encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, runConfig, stepConfig, lookupTransition,
          Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | some bit =>
      cases bit <;> cases right <;>
        simp [markerScanDescription, cellCodeBits, encodeCell, encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, runConfig, stepConfig, lookupTransition,
          Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
private theorem markerScanDescription_run_cells (cells : List (Option Bool))
    (left right : List (Option Bool)) :
    markerScanDescription.runConfig (4 * cells.length)
        { state := markerScanDescription.start, tape := tapeAtCells left
            (List.append ((cellsCodeBits cells).map some) right) } =
      { state := markerScanDescription.start, tape := tapeAtCells
          (List.append ((cellsCodeBits cells).reverse.map some) left) right } := by
  induction cells generalizing left with
  | nil => simp [runConfig, cellsCodeBits]
  | cons cell rest ih =>
      rw [show 4 * (cell :: rest).length = 4 + 4 * rest.length by simp; lia]
      rw [runConfig_add]
      rw [cellsCodeBits_cons_map]
      rw [cellMap_append_assoc]
      rw [markerScanDescription_run_cell]
      rw [ih (List.append ((cellCodeBits cell).reverse.map some) left)]
      rw [cellsCodeBits_cons_reverse_map]
      rw [reverseCellMap_append_assoc]
private theorem markerScanDescription_run_marker (left right : List (Option Bool)) :
    markerScanDescription.runConfig 4
        { state := markerScanDescription.start, tape := tapeAtCells left
            (some false :: some true :: some true :: some true :: right) } =
      { state := markerScanDescription.halt, tape := tapeAtCells
          (some true :: some true :: some true :: some false :: left) right } := by
  cases right <;>
    simp [markerScanDescription, runConfig, stepConfig, lookupTransition, Matches,
      transition, tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
def sourceTape (T : Tape Bool) (padding : List (Option Bool)) : Tape Bool :=
  rightEdgeRewindTargetTape (quotedPairBits (logicalTapePairs T)) padding
def targetTape (T : Tape Bool) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append ((List.append (cellsCodeBits T.left.reverse)
      [false, true, true, true]).reverse.map some) [none])
    (List.append ((List.append (cellCodeBits T.head) (cellsCodeBits T.right)).map some)
      (none :: padding))
theorem markerScanDescription_haltsFromTape (T : Tape Bool)
    (padding : List (Option Bool)) :
    markerScanDescription.HaltsFromTape (sourceTape T padding) (targetTape T padding) := by
  refine ⟨4 * T.left.length + 4, ?_⟩
  have hrun := markerScanDescription_run_cells T.left.reverse [none]
    (some false :: some true :: some true :: some true ::
      List.append ((List.append (cellCodeBits T.head) (cellsCodeBits T.right)).map some)
        (none :: padding))
  have hfull :
      markerScanDescription.runConfig (4 * T.left.length + 4)
          { state := markerScanDescription.start, tape := sourceTape T padding } =
        { state := markerScanDescription.halt, tape := targetTape T padding } := by
    rw [show 4 * T.left.length + 4 = 4 * T.left.reverse.length + 4 by simp]
    rw [runConfig_add]
    rw [show sourceTape T padding = tapeAtCells [none]
        (List.append ((cellsCodeBits T.left.reverse).map some)
            (some false :: some true :: some true :: some true ::
              List.append ((List.append (cellCodeBits T.head)
                (cellsCodeBits T.right)).map some) (none :: padding))) by
      simp [sourceTape, rightEdgeRewindTargetTape, quotedPairBits_logicalTapePairs,
        List.map_append, List.append_assoc]]
    rw [hrun]
    rw [markerScanDescription_run_marker]
    simp [targetTape, List.reverse_append, List.map_append, List.append_assoc]
  constructor
  · simpa using congrArg MachineDescription.Configuration.state hfull
  · simpa using congrArg MachineDescription.Configuration.tape hfull
end RawPairMarker
end GuardedEgress
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
