import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.RawPairDecoder
set_option doc.verso true
/-! # Guarded #18 head-marker split
The rewritten pair stream has four-bit cell tokens followed by the unique
{lit}`0111` head token. This scanner halts on the exact head-cell token. -/
namespace FoC
namespace Computability
open Languages MachineDescription
namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace GuardedEgress
namespace RawPairMarker
open CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured.MultiTapeLowering CommonGround.FiniteTransducers.CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner RawPairQuoter RawPairDecoder
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
private theorem markerScanDescription_run_cell (cell : Option Bool)
    (left right : List (Option Bool)) :
    markerScanDescription.runConfig 4
        { state := markerScanDescription.start, tape := tapeAtCells left
            (some false :: some true :: some (logicalCellPair cell).1 ::
              some (logicalCellPair cell).2 :: right) } =
      { state := markerScanDescription.start
        tape := tapeAtCells (some (logicalCellPair cell).2 ::
          some (logicalCellPair cell).1 :: some true :: some false :: left) right } := by
  cases cell with
  | none =>
      cases right <;>
        simp [markerScanDescription, logicalCellPair, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveRight]
  | some bit =>
      cases bit <;> cases right <;>
        simp [markerScanDescription, logicalCellPair, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells, Tape.read,
          Tape.write, Tape.move, Tape.moveRight]
private theorem quotedPairBits_cons_map_append (pair : Bool × Bool)
    (rest : List (Bool × Bool)) (right : List (Option Bool)) :
    List.append ((quotedPairBits (pair :: rest)).map some) right =
      some false :: some true :: some pair.1 :: some pair.2 ::
        List.append ((quotedPairBits rest).map some) right := by
  rcases pair with ⟨first, second⟩
  rfl
private theorem quotedPairBits_cons_reverse_map_append (pair : Bool × Bool)
    (rest : List (Bool × Bool)) (left : List (Option Bool)) :
    List.append ((quotedPairBits (pair :: rest)).reverse.map some) left =
      List.append ((quotedPairBits rest).reverse.map some)
        (some pair.2 :: some pair.1 :: some true :: some false :: left) := by
  rcases pair with ⟨first, second⟩
  simp [quotedPairBits, List.map_append, List.append_assoc]
private theorem markerScanDescription_run_cells (cells : List (Option Bool))
    (left right : List (Option Bool)) :
    markerScanDescription.runConfig (4 * cells.length)
        { state := markerScanDescription.start, tape := tapeAtCells left
            (List.append ((quotedPairBits (cells.map logicalCellPair)).map some) right) } =
      { state := markerScanDescription.start, tape := tapeAtCells
          (List.append ((quotedPairBits (cells.map logicalCellPair)).reverse.map some) left) right } := by
  induction cells generalizing left with
  | nil => simp [runConfig, quotedPairBits]
  | cons cell rest ih =>
      rw [show 4 * (cell :: rest).length = 4 + 4 * rest.length by simp; lia]
      rw [runConfig_add]
      simp only [List.map_cons]
      rw [quotedPairBits_cons_map_append]
      rw [markerScanDescription_run_cell]
      rw [ih (some (logicalCellPair cell).2 :: some (logicalCellPair cell).1 ::
        some true :: some false :: left)]
      rw [quotedPairBits_cons_reverse_map_append]
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
    (List.append ((List.append (quotedPairBits (T.left.reverse.map logicalCellPair))
      [false, true, true, true]).reverse.map some) [none])
    (List.append ((quotedPairBits
      (logicalCellPair T.head :: T.right.map logicalCellPair)).map some)
      (none :: padding))
private theorem quotedPairBits_logicalTapePairs_map_split (T : Tape Bool) :
    (quotedPairBits (logicalTapePairs T)).map some =
      List.append ((quotedPairBits
        (T.left.reverse.map logicalCellPair)).map some)
        (some false :: some true :: some true :: some true ::
          (quotedPairBits
            (logicalCellPair T.head :: T.right.map logicalCellPair)).map some) := by
  have hbits : quotedPairBits (logicalTapePairs T) =
      List.append (quotedPairBits (T.left.reverse.map logicalCellPair))
        (false :: true :: true :: true :: quotedPairBits
          (logicalCellPair T.head :: T.right.map logicalCellPair)) := by
    unfold logicalTapePairs
    rw [quotedPairBits_append, quotedPairBits_append]
    rfl
  simpa [List.map_append] using
    congrArg (fun bits : Word Bool => bits.map some) hbits
theorem markerScanDescription_haltsFromTape (T : Tape Bool)
    (padding : List (Option Bool)) :
    markerScanDescription.HaltsFromTape (sourceTape T padding) (targetTape T padding) := by
  refine ⟨4 * T.left.length + 4, ?_⟩
  have hrun := markerScanDescription_run_cells T.left.reverse [none]
    (some false :: some true :: some true :: some true ::
      List.append ((quotedPairBits
        (logicalCellPair T.head :: T.right.map logicalCellPair)).map some)
        (none :: padding))
  have hfull :
      markerScanDescription.runConfig (4 * T.left.length + 4)
          { state := markerScanDescription.start, tape := sourceTape T padding } =
        { state := markerScanDescription.halt, tape := targetTape T padding } := by
    rw [show 4 * T.left.length + 4 = 4 * T.left.reverse.length + 4 by simp]
    rw [runConfig_add]
    rw [show sourceTape T padding = tapeAtCells [none]
        (List.append ((quotedPairBits (T.left.reverse.map logicalCellPair)).map some)
          (some false :: some true :: some true :: some true ::
            List.append ((quotedPairBits
              (logicalCellPair T.head :: T.right.map logicalCellPair)).map some)
              (none :: padding))) by
      rw [sourceTape, rightEdgeRewindTargetTape,
        quotedPairBits_logicalTapePairs_map_split]
      simp [List.append_assoc]]
    rw [hrun]
    rw [markerScanDescription_run_marker]
    simp [targetTape, List.reverse_append]
  constructor
  · simpa using congrArg MachineDescription.Configuration.state hfull
  · simpa using congrArg MachineDescription.Configuration.tape hfull
theorem rightBlankRewindDescription_haltsFrom_pairTarget (i : Index) :
    rightBlankRewindDescription.HaltsFromTape
      (pairRewriteTargetTape (pairList i) (rewindPadding i))
      (rightEdgeRewindSourceTapeWithBase []
        (quotedPairBits (pairList i)) (rewindPadding i)) := by
  cases hrev : (quotedPairBits (pairList i)).reverse with
  | nil =>
      cases hpairs : pairList i with
      | nil => simp [pairList, logicalTapePairs] at hpairs
      | cons pair pairs =>
          rcases pair with ⟨first, second⟩
          simp [hpairs, quotedPairBits] at hrev
  | cons first rest =>
      have hbits : (first :: rest).reverse = quotedPairBits (pairList i) := by
        rw [← hrev]
        simp
      simpa [pairRewriteTargetTape, pairRewriteBoundaryTape, pairRewriteScanTape,
        pairStream, interleavedBits, rewindPadding, List.replicate_succ,
        hrev, hbits, Tape.move, Tape.moveRight, tapeAtCells,
        List.append_assoc] using
        rightBlankRewindDescription_haltsFromTape_from_leftStack
          [] first rest 1
          (List.append (List.replicate (decoderGap i) (none : Option Bool))
            (decoderRightPadding i))
theorem rightEdgeRewindDescription_haltsFrom_pairRewind (i : Index) :
    rightEdgeRewindDescription.HaltsFromTapeEquiv
      (rightEdgeRewindSourceTapeWithBase []
        (quotedPairBits (pairList i)) (rewindPadding i))
      (sourceTape (guardLogicalTape i.finalTape) (rewindPadding i)) := by
  have hin := tapeAtCells_pad_left_none_equiv
    ((quotedPairBits (pairList i)).reverse.map some)
    (none :: rewindPadding i)
  simpa [rightEdgeRewindSourceTapeWithBase, rightEdgeRewindSourceTape,
    sourceTape, pairList] using
    MachineDescription.HaltsFromTapeEquiv_of_input_equiv hin
      (rightEdgeRewindDescription_haltsFromTape
        (quotedPairBits (pairList i)) (rewindPadding i))
end RawPairMarker
end GuardedEgress
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
