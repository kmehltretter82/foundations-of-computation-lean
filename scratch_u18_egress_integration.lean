import scratch_u18_chunk_reverse
import scratch_u18_length_assembly
import scratch_u18_right_assembly
import scratch_u18_right_length_copy

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.EgressIntegrationScratch

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.CountWindowRawSourceEncoder.RawBoundaryRightEdgeEmitter
open DovetailInitialLayoutInitializer.StageInputMarkedScanner
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open RawPairQuoter RawPairDecoder

def leftFieldBits (T : Tape Bool) : Word Bool :=
  List.append (stageNatBits T.left.length) (cellsCodeBits T.left)

def leftHeadFieldBits (T : Tape Bool) : Word Bool :=
  List.append (leftFieldBits T) (cellCodeBits T.head)

def headScratch (T : Tape Bool) : Nat :=
  4 * T.left.length + 3

theorem leftFieldBits_ne_nil (T : Tape Bool) :
    leftFieldBits T ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [leftFieldBits, stageNatBits_length] at hlength

theorem leftHeadFieldBits_ne_nil (T : Tape Bool) :
    leftHeadFieldBits T ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [leftHeadFieldBits, leftFieldBits,
    stageNatBits_length] at hlength

theorem headDescription_haltsFrom_leftTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    HeadCellExtractorScratch.description.HaltsFromTape
      (ChunkReverseScratch.leftLengthTargetTape T padding)
      (HeadCellExtractorScratch.headExtractedTape
        (leftFieldBits T) (headScratch T) T padding) := by
  simpa [ChunkReverseScratch.leftLengthTargetTape,
    ChunkReverseScratch.InstallLeftGuard.markerRightPayload,
    leftFieldBits, headScratch] using
    HeadCellExtractorScratch.description_haltsFrom_separator_cellList
      (leftFieldBits T) (headScratch T) T padding
      (leftFieldBits_ne_nil T)

def leftAndHeadDescription : MachineDescription :=
  canonicalSeqDescription ChunkReverseScratch.leftPreparedDescription
    HeadCellExtractorScratch.description

theorem leftAndHeadDescription_subroutineReady :
    leftAndHeadDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    ChunkReverseScratch.leftPreparedDescription_subroutineReady
    HeadCellExtractorScratch.description_subroutineReady

theorem leftAndHeadDescription_haltsFrom_markerTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    leftAndHeadDescription.HaltsFromTapeEquiv
      (RawPairMarker.targetTape T padding)
      (HeadCellExtractorScratch.headExtractedTape
        (leftFieldBits T) (headScratch T) T padding) := by
  have hleft :=
    ChunkReverseScratch.leftPreparedDescription_haltsFrom_markerTarget T padding
  have hhead := headDescription_haltsFrom_leftTarget T padding
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (ChunkReverseScratch.leftLengthTargetTape T padding)) =
        ChunkReverseScratch.leftLengthTargetTape T padding := by
    exact ChunkReverseScratch.separator_move_left_move_right
      (leftFieldBits T) (4 * T.left.length + 6)
      (ChunkReverseScratch.InstallLeftGuard.markerRightPayload T padding)
  exact
    canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv_haltsFromTape
      ChunkReverseScratch.leftPreparedDescription_subroutineReady
      HeadCellExtractorScratch.description_subroutineReady hleft hbridge hhead

theorem rightCellTokenBits_eq_quotedPairBits
    (cells : List (Bool × Bool)) :
    RightLengthCopyScratch.cellTokenBits cells = quotedPairBits cells := by
  induction cells with
  | nil =>
      rfl
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      simp [RightLengthCopyScratch.cellTokenBits, quotedPairBits, ih]

theorem rightCells_valid (cells : List (Option Bool)) :
    RightLengthCopyScratch.validCells (cells.map logicalCellPair) := by
  intro pair hpair
  rw [List.mem_map] at hpair
  rcases hpair with ⟨cell, _hcell, rfl⟩
  cases cell with
  | none => decide
  | some bit => cases bit <;> decide

theorem cellCodeBits_reverse_map_some (cell : Option Bool) :
    ((cellCodeBits cell).map some).reverse =
      [ some (logicalCellPair cell).2
      , some (logicalCellPair cell).1
      , some true
      , some false ] := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem headExtractedTape_eq_rightSource (i : Index) :
    let T := guardLogicalTape i.finalTape
    HeadCellExtractorScratch.headExtractedTape
        (leftFieldBits T) (headScratch T) T (rewindPadding i) =
      RightLengthCopyScratch.sourceTape
        (leftHeadFieldBits T) (headScratch T)
        (T.right.map logicalCellPair)
        (none :: none ::
          RightLengthCopyScratch.rightAssemblyPaddingTail i) := by
  dsimp only
  rw [RightLengthCopyScratch.rewindPadding_eq_rightAssemblyPrefix]
  simp [HeadCellExtractorScratch.headExtractedTape,
    HeadCellExtractorScratch.targetTape,
    RightLengthCopyScratch.sourceTape, leftHeadFieldBits,
    rightCellTokenBits_eq_quotedPairBits,
    cellCodeBits_reverse_map_some,
    headScratch, List.append_assoc]

def leftHeadRightDescription : MachineDescription :=
  canonicalSeqDescription leftAndHeadDescription
    RightLengthCopyScratch.rightLengthAssemblyDescription

theorem leftHeadRightDescription_subroutineReady :
    leftHeadRightDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    leftAndHeadDescription_subroutineReady
    RightLengthCopyScratch.rightLengthAssemblyDescription_subroutineReady

def serializedTapeFieldTarget (i : Index) : Tape Bool :=
  let T := guardLogicalTape i.finalTape
  leadingBlankLeftShiftTargetTapeWithPadding
    ((leftHeadFieldBits T).reverse.map some)
    (RightLengthCopyScratch.compactedPayloadBits
      (T.right.map logicalCellPair))
    (sentinelGapCompactorFinalPadding (headScratch T) 2
      (none :: RightLengthCopyScratch.rightAssemblyPaddingTail i))

theorem headExtractedTape_move_left_move_right (i : Index) :
    let T := guardLogicalTape i.finalTape
    Tape.move Direction.left
        (Tape.move Direction.right
          (HeadCellExtractorScratch.headExtractedTape
            (leftFieldBits T) (headScratch T) T (rewindPadding i))) =
      HeadCellExtractorScratch.headExtractedTape
        (leftFieldBits T) (headScratch T) T (rewindPadding i) := by
  dsimp only
  simp [HeadCellExtractorScratch.headExtractedTape,
    HeadCellExtractorScratch.targetTape, headScratch,
    tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
    List.replicate_succ]

theorem leftHeadRightDescription_haltsFrom_markerTarget (i : Index) :
    let T := guardLogicalTape i.finalTape
    leftHeadRightDescription.HaltsFromTapeEquiv
      (RawPairMarker.targetTape T (rewindPadding i))
      (serializedTapeFieldTarget i) := by
  dsimp only
  let T := guardLogicalTape i.finalTape
  have hfirst :=
    leftAndHeadDescription_haltsFrom_markerTarget
      T (rewindPadding i)
  have hright :=
    RightLengthCopyScratch.rightLengthAssemblyDescription_haltsFromTape
      (leftHeadFieldBits T) (headScratch T)
      (T.right.map logicalCellPair)
      (RightLengthCopyScratch.rightAssemblyPaddingTail i)
      (leftHeadFieldBits_ne_nil T)
      (rightCells_valid T.right)
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (HeadCellExtractorScratch.headExtractedTape
              (leftFieldBits T) (headScratch T) T (rewindPadding i))) =
        RightLengthCopyScratch.sourceTape
          (leftHeadFieldBits T) (headScratch T)
          (T.right.map logicalCellPair)
          (none :: none ::
            RightLengthCopyScratch.rightAssemblyPaddingTail i) := by
    rw [show
      Tape.move Direction.left
          (Tape.move Direction.right
            (HeadCellExtractorScratch.headExtractedTape
              (leftFieldBits T) (headScratch T) T (rewindPadding i))) =
        HeadCellExtractorScratch.headExtractedTape
          (leftFieldBits T) (headScratch T) T (rewindPadding i) by
      simpa [T] using headExtractedTape_move_left_move_right i]
    simpa [T] using headExtractedTape_eq_rightSource i
  simpa [leftHeadRightDescription,
    serializedTapeFieldTarget, T] using
    canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv_haltsFromTape
      leftAndHeadDescription_subroutineReady
      RightLengthCopyScratch.rightLengthAssemblyDescription_subroutineReady
      hfirst hbridge hright

/-!
## Removing the lowering guards

The guarded theorem above deliberately preserves both representation guards.
The semantic #18 target stores the original logical tape window, so the two
known `none` cell tokens must be erased before their respective length cursors
run.
-/

namespace LeftGuardRemover

def description : MachineDescription where
  stateCount := 7
  start := 0
  halt := 6
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 (some false) none Direction.left 2
    , transition 2 (some false) none Direction.left 3
    , transition 3 (some true) none Direction.left 4
    , transition 4 (some false) none Direction.right 5
    , transition 5 none none Direction.left 6 ]

theorem description_subroutineReady : description.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    description (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

def sourceTape (pre : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  rawBoundaryLengthCursorSeparatorTape
    (List.append pre (cellCodeBits none)) blankTail right

def targetTape (pre : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells (pre.reverse.map some)
    (none :: none :: none :: none :: none ::
      List.append
        (List.replicate (blankTail + 1) (none : Option Bool)) right)

theorem description_run
    (pre : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    description.runConfig 6
        { state := description.start
          tape := sourceTape pre blankTail right } =
      { state := description.halt
        tape := targetTape pre blankTail right } := by
  simp [description, sourceTape, targetTape,
    rawBoundaryLengthCursorSeparatorTape,
    cellCodeBits, encodeCell, encodeCodeWordAsInput,
    encodeCodeSymbolAsInput, runConfig, stepConfig,
    lookupTransition, Matches, transition, tapeAtCells,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
    List.reverse_append, List.map_append, List.append_assoc]

theorem description_haltsFromTape
    (pre : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    description.HaltsFromTape
      (sourceTape pre blankTail right)
      (targetTape pre blankTail right) := by
  refine ⟨6, ?_⟩
  have hrun := description_run pre blankTail right
  constructor
  · simpa using congrArg Configuration.state hrun
  · simpa using congrArg Configuration.tape hrun

theorem targetTape_eq_separator
    (pre : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    targetTape pre blankTail right =
      rawBoundaryLengthCursorSeparatorTape pre (blankTail + 4) right := by
  simp [targetTape, rawBoundaryLengthCursorSeparatorTape,
    List.replicate_succ, List.append_assoc]

end LeftGuardRemover

def guardedLeftReverseBlankTail (T : Tape Bool) : Nat :=
  4 * (guardLogicalTape T).left.length + 6

def correctedLeftBlankTail (T : Tape Bool) : Nat :=
  guardedLeftReverseBlankTail T + 4

theorem guardedLeftQuotedBits_eq
    (T : Tape Bool) :
    quotedPairBits
        (((guardLogicalTape T).left.reverse.map logicalCellPair).reverse) =
      List.append (cellsCodeBits T.left) (cellCodeBits none) := by
  have harg :
      ((guardLogicalTape T).left.reverse.map logicalCellPair).reverse =
        (guardLogicalTape T).left.map logicalCellPair := by
    simp [List.map_reverse]
  rw [harg]
  calc
    quotedPairBits ((guardLogicalTape T).left.map logicalCellPair) =
        cellsCodeBits (guardLogicalTape T).left :=
      RawPairQuoter.quotedPairBits_map_logicalCellPair _
    _ = List.append (cellsCodeBits T.left) (cellCodeBits none) := by
      have happ := cellsCodeBits_append T.left [none]
      have hsingle : cellsCodeBits [none] = cellCodeBits none := by
        rfl
      rw [hsingle] at happ
      change
        cellsCodeBits (List.append T.left [none]) =
          List.append (cellsCodeBits T.left) (cellCodeBits none)
      exact happ

theorem guardedReverseTarget_eq_leftGuardSource
    (T : Tape Bool) (padding : List (Option Bool)) :
    ChunkReverseScratch.targetTape
        ((guardLogicalTape T).left.reverse.map logicalCellPair)
        (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
          (guardLogicalTape T) padding) =
      LeftGuardRemover.sourceTape
        (cellsCodeBits T.left)
        (guardedLeftReverseBlankTail T)
        (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
          (guardLogicalTape T) padding) := by
  unfold ChunkReverseScratch.targetTape LeftGuardRemover.sourceTape
  rw [guardedLeftQuotedBits_eq]
  simp [guardedLeftReverseBlankTail, guardLogicalTape]

def setupRemoveLeftGuardDescription : MachineDescription :=
  canonicalSeqDescription ChunkReverseScratch.setupAndReverseDescription
    LeftGuardRemover.description

theorem setupRemoveLeftGuardDescription_subroutineReady :
    setupRemoveLeftGuardDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    ChunkReverseScratch.setupAndReverseDescription_subroutineReady
    LeftGuardRemover.description_subroutineReady

def leftGuardRemovedSeparatorTape
    (T : Tape Bool) (padding : List (Option Bool)) : Tape Bool :=
  rawBoundaryLengthCursorSeparatorTape
    (cellsCodeBits T.left) (correctedLeftBlankTail T)
    (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
      (guardLogicalTape T) padding)

theorem setupRemoveLeftGuardDescription_haltsFrom_markerTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    setupRemoveLeftGuardDescription.HaltsFromTapeEquiv
      (RawPairMarker.targetTape (guardLogicalTape T) padding)
      (leftGuardRemovedSeparatorTape T padding) := by
  have hsetup :=
    ChunkReverseScratch.setupAndReverseDescription_haltsFrom_markerTarget
      (guardLogicalTape T) padding
  have hremove0 :=
    LeftGuardRemover.description_haltsFromTape
      (cellsCodeBits T.left) (guardedLeftReverseBlankTail T)
      (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
        (guardLogicalTape T) padding)
  have hremove :
      LeftGuardRemover.description.HaltsFromTape
        (LeftGuardRemover.sourceTape
          (cellsCodeBits T.left) (guardedLeftReverseBlankTail T)
          (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
            (guardLogicalTape T) padding))
        (leftGuardRemovedSeparatorTape T padding) := by
    simpa [leftGuardRemovedSeparatorTape,
      correctedLeftBlankTail,
      LeftGuardRemover.targetTape_eq_separator] using hremove0
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (ChunkReverseScratch.targetTape
              ((guardLogicalTape T).left.reverse.map logicalCellPair)
              (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
                (guardLogicalTape T) padding))) =
        LeftGuardRemover.sourceTape
          (cellsCodeBits T.left) (guardedLeftReverseBlankTail T)
          (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
            (guardLogicalTape T) padding) := by
    rw [guardedReverseTarget_eq_leftGuardSource T padding]
    exact ChunkReverseScratch.separator_move_left_move_right
      (List.append (cellsCodeBits T.left) (cellCodeBits none))
      (guardedLeftReverseBlankTail T)
      (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
        (guardLogicalTape T) padding)
  exact
    canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv_haltsFromTape
      ChunkReverseScratch.setupAndReverseDescription_subroutineReady
      LeftGuardRemover.description_subroutineReady
      hsetup hbridge hremove

def correctedLeftLengthTargetTape
    (T : Tape Bool) (padding : List (Option Bool)) : Tape Bool :=
  rawBoundaryLengthCursorSeparatorTape
    (leftFieldBits T) (correctedLeftBlankTail T)
    (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
      (guardLogicalTape T) padding)

def correctedLeftPreparedDescription : MachineDescription :=
  canonicalSeqDescription setupRemoveLeftGuardDescription
    rawBoundaryLengthCursorLoopDescription

theorem correctedLeftPreparedDescription_subroutineReady :
    correctedLeftPreparedDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    setupRemoveLeftGuardDescription_subroutineReady
    rawBoundaryLengthCursorLoopDescription_subroutineReady

theorem correctedLeftPreparedDescription_haltsFrom_markerTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    correctedLeftPreparedDescription.HaltsFromTapeEquiv
      (RawPairMarker.targetTape (guardLogicalTape T) padding)
      (correctedLeftLengthTargetTape T padding) := by
  have hfirst :=
    setupRemoveLeftGuardDescription_haltsFrom_markerTarget T padding
  have hlength :=
    LengthAssemblyScratch.lengthCursor_haltsFrom_cellList
      T.left (correctedLeftBlankTail T)
      (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
        (guardLogicalTape T) padding)
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (leftGuardRemovedSeparatorTape T padding)) =
        leftGuardRemovedSeparatorTape T padding := by
    exact ChunkReverseScratch.separator_move_left_move_right
      (cellsCodeBits T.left) (correctedLeftBlankTail T)
      (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
        (guardLogicalTape T) padding)
  simpa [correctedLeftPreparedDescription,
    leftGuardRemovedSeparatorTape,
    correctedLeftLengthTargetTape, leftFieldBits] using
    canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv
      setupRemoveLeftGuardDescription_subroutineReady
      rawBoundaryLengthCursorLoopDescription_subroutineReady
      hfirst hbridge hlength

def correctedHeadScratch (T : Tape Bool) : Nat :=
  4 * T.left.length + 11

theorem correctedLeftBlankTail_eq_headScratch_add_three
    (T : Tape Bool) :
    correctedLeftBlankTail T = correctedHeadScratch T + 3 := by
  simp [correctedLeftBlankTail, guardedLeftReverseBlankTail,
    correctedHeadScratch, guardLogicalTape]
  lia

def correctedHeadExtractedTape
    (T : Tape Bool) (padding : List (Option Bool)) : Tape Bool :=
  HeadCellExtractorScratch.headExtractedTape
    (leftFieldBits T) (correctedHeadScratch T)
    (guardLogicalTape T) padding

theorem headDescription_haltsFrom_correctedLeftTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    HeadCellExtractorScratch.description.HaltsFromTape
      (correctedLeftLengthTargetTape T padding)
      (correctedHeadExtractedTape T padding) := by
  have hrun :=
    HeadCellExtractorScratch.description_haltsFrom_separator_cellList
      (leftFieldBits T) (correctedHeadScratch T)
      (guardLogicalTape T) padding (leftFieldBits_ne_nil T)
  simpa [correctedLeftLengthTargetTape,
    correctedHeadExtractedTape,
    correctedLeftBlankTail_eq_headScratch_add_three,
    ChunkReverseScratch.InstallLeftGuard.markerRightPayload,
    leftFieldBits] using hrun

def correctedLeftAndHeadDescription : MachineDescription :=
  canonicalSeqDescription correctedLeftPreparedDescription
    HeadCellExtractorScratch.description

theorem correctedLeftAndHeadDescription_subroutineReady :
    correctedLeftAndHeadDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    correctedLeftPreparedDescription_subroutineReady
    HeadCellExtractorScratch.description_subroutineReady

theorem correctedLeftAndHeadDescription_haltsFrom_markerTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    correctedLeftAndHeadDescription.HaltsFromTapeEquiv
      (RawPairMarker.targetTape (guardLogicalTape T) padding)
      (correctedHeadExtractedTape T padding) := by
  have hleft :=
    correctedLeftPreparedDescription_haltsFrom_markerTarget T padding
  have hhead :=
    headDescription_haltsFrom_correctedLeftTarget T padding
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (correctedLeftLengthTargetTape T padding)) =
        correctedLeftLengthTargetTape T padding := by
    exact ChunkReverseScratch.separator_move_left_move_right
      (leftFieldBits T) (correctedLeftBlankTail T)
      (ChunkReverseScratch.InstallLeftGuard.markerRightPayload
        (guardLogicalTape T) padding)
  simpa [correctedLeftAndHeadDescription] using
    canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv_haltsFromTape
      correctedLeftPreparedDescription_subroutineReady
      HeadCellExtractorScratch.description_subroutineReady
      hleft hbridge hhead

namespace RightGuardRemover

def markerBits : List Bool := [false, true, true, true]

def guardBits : List Bool := cellCodeBits none

def payloadBits (cells : List (Bool × Bool)) : List Bool :=
  List.append markerBits (RightLengthCopyScratch.cellTokenBits cells)

def scanTailBits (cells : List (Bool × Bool)) : List Bool :=
  List.append [true, true, true]
    (List.append (RightLengthCopyScratch.cellTokenBits cells) guardBits)

theorem presentBits_eq_false_scanTail
    (cells : List (Bool × Bool)) :
    List.append (payloadBits cells) guardBits =
      false :: scanTailBits cells := by
  rfl

def seekEraseDescription : MachineDescription where
  stateCount := 8
  start := 0
  halt := 7
  transitions :=
    [ transition 0 none none Direction.right 0
    , transition 0 (some false) (some false) Direction.right 1
    , transition 1 (some false) (some false) Direction.right 1
    , transition 1 (some true) (some true) Direction.right 1
    , transition 1 none none Direction.left 2
    , transition 2 (some false) none Direction.left 3
    , transition 3 (some false) none Direction.left 4
    , transition 4 (some true) none Direction.left 5
    , transition 5 (some false) none Direction.right 6
    , transition 6 none none Direction.left 7 ]

theorem seekEraseDescription_subroutineReady :
    seekEraseDescription.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    seekEraseDescription (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

def sourceTape (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells (base.reverse.map some)
    (none ::
      List.append (List.replicate gap (none : Option Bool))
        (List.append
          ((List.append (payloadBits cells) guardBits).map some)
          (none :: padding)))

def erasedBoundaryTape (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append ((payloadBits cells).reverse.map some)
      (List.append
        (List.replicate (gap + 1) (none : Option Bool))
        (base.reverse.map some)))
    (none :: none :: none :: none :: none :: padding)

private theorem run_seek_blanks (n : Nat)
    (left right : List (Option Bool)) :
    seekEraseDescription.runConfig n
        { state := seekEraseDescription.start
          tape := tapeAtCells left
            (List.append (List.replicate n (none : Option Bool)) right) } =
      { state := seekEraseDescription.start
        tape := tapeAtCells
          (List.append (List.replicate n none) left) right } := by
  induction n generalizing left with
  | zero =>
      rfl
  | succ n ih =>
      rw [show n + 1 = 1 + n by lia]
      rw [runConfig_add]
      rw [show List.replicate (1 + n) (none : Option Bool) =
        none :: List.replicate n none by
          rw [show 1 + n = Nat.succ n by lia]
          rfl]
      rw [show
        List.append (none :: List.replicate n (none : Option Bool)) right =
          none :: List.append (List.replicate n none) right by rfl]
      rw [show
        List.append (none :: List.replicate n (none : Option Bool)) left =
          none :: List.append (List.replicate n none) left by rfl]
      have hstep :
          seekEraseDescription.runConfig 1
              { state := seekEraseDescription.start
                tape := tapeAtCells left
                  (none :: List.append (List.replicate n none) right) } =
            { state := seekEraseDescription.start
              tape := tapeAtCells (none :: left)
                (List.append (List.replicate n none) right) } := by
        cases hrest :
            List.append (List.replicate n (none : Option Bool)) right <;>
          simp [seekEraseDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveRight, hrest]
      rw [hstep]
      have ih' := ih (none :: left)
      rw [ih']
      rw [replicate_none_append_none_cons]

private theorem run_scan_present (bits : List Bool)
    (left right : List (Option Bool)) :
    seekEraseDescription.runConfig bits.length
        { state := 1
          tape := tapeAtCells left
            (List.append (bits.map some) right) } =
      { state := 1
        tape := tapeAtCells
          (List.append (bits.reverse.map some) left) right } := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      simp only [List.map_cons]
      rw [show
        List.append (some bit :: rest.map some) right =
          some bit :: List.append (rest.map some) right by rfl]
      have hstep :
          seekEraseDescription.runConfig 1
              { state := 1
                tape := tapeAtCells left
                  (some bit ::
                    List.append (rest.map some) right) } =
            { state := 1
              tape := tapeAtCells (some bit :: left)
                (List.append (rest.map some) right) } := by
        cases bit <;>
          cases hrest : List.append (rest.map some) right <;>
          simp [seekEraseDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveRight, hrest]
      rw [hstep]
      rw [ih (some bit :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private theorem run_boundary
    (left padding : List (Option Bool)) :
    seekEraseDescription.runConfig 1
        { state := 1
          tape := tapeAtCells left (none :: padding) } =
      { state := 2
        tape := Tape.move Direction.left
          (tapeAtCells left (none :: padding)) } := by
  cases left <;>
    simp [seekEraseDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem run_erase_guard
    (left padding : List (Option Bool)) :
    seekEraseDescription.runConfig 5
        { state := 2
          tape := tapeAtCells
            (some false :: some true :: some false :: left)
            (some false :: none :: padding) } =
      { state := seekEraseDescription.halt
        tape := tapeAtCells left
          (none :: none :: none :: none :: none :: padding) } := by
  simp [seekEraseDescription, runConfig, stepConfig,
    lookupTransition, Matches, transition, tapeAtCells,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem seekEraseDescription_haltsFromTape
    (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) :
    seekEraseDescription.HaltsFromTape
      (sourceTape base gap cells padding)
      (erasedBoundaryTape base gap cells padding) := by
  let tail : List Bool := scanTailBits cells
  let blankSteps := gap + 1
  let totalSteps := blankSteps + (1 + (tail.length + (1 + 5)))
  have hseek := run_seek_blanks blankSteps
    (base.reverse.map some)
    (List.append ((false :: tail).map some) (none :: padding))
  have hstart :
      seekEraseDescription.runConfig 1
          { state := seekEraseDescription.start
            tape := tapeAtCells
              (List.append (List.replicate blankSteps none)
                (base.reverse.map some))
              (some false ::
                List.append (tail.map some) (none :: padding)) } =
        { state := 1
          tape := tapeAtCells
            (some false ::
              List.append (List.replicate blankSteps none)
                (base.reverse.map some))
            (List.append (tail.map some) (none :: padding)) } := by
    simp [seekEraseDescription, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight] <;>
      rfl
  have hscan := run_scan_present tail
    (some false ::
      List.append (List.replicate blankSteps none)
        (base.reverse.map some))
    (none :: padding)
  have hboundary := run_boundary
    (List.append (tail.reverse.map some)
      (some false ::
        List.append (List.replicate blankSteps none)
          (base.reverse.map some))) padding
  have herase := run_erase_guard
    (List.append ((payloadBits cells).reverse.map some)
      (List.append (List.replicate blankSteps none)
        (base.reverse.map some))) padding
  have hboundaryShape :
      Tape.move Direction.left
          (tapeAtCells
            (List.append (tail.reverse.map some)
              (some false ::
                List.append (List.replicate blankSteps none)
                  (base.reverse.map some)))
            (none :: padding)) =
        tapeAtCells
          (some false :: some true :: some false ::
            List.append ((payloadBits cells).reverse.map some)
              (List.append (List.replicate blankSteps none)
                (base.reverse.map some)))
          (some false :: none :: padding) := by
    simp [tail, scanTailBits, guardBits, payloadBits, markerBits,
      cellCodeBits, encodeCell, encodeCodeWordAsInput,
      encodeCodeSymbolAsInput, tapeAtCells,
      Tape.move, Tape.moveLeft,
      List.reverse_append, List.map_append, List.append_assoc]
  refine ⟨totalSteps, ?_⟩
  have hfull :
      seekEraseDescription.runConfig totalSteps
          { state := seekEraseDescription.start
            tape := sourceTape base gap cells padding } =
        { state := seekEraseDescription.halt
          tape := erasedBoundaryTape base gap cells padding } := by
    unfold totalSteps
    rw [runConfig_add]
    unfold sourceTape
    rw [presentBits_eq_false_scanTail]
    rw [show
      none ::
          List.append (List.replicate gap (none : Option Bool))
            (List.append ((false :: tail).map some) (none :: padding)) =
        List.append (List.replicate blankSteps none)
          (List.append ((false :: tail).map some) (none :: padding)) by
      simp [blankSteps, tail,
        List.replicate_succ, List.append_assoc]]
    rw [hseek]
    rw [runConfig_add]
    simp only [List.map_cons]
    rw [show
      List.append (some false :: tail.map some) (none :: padding) =
        some false :: List.append (tail.map some) (none :: padding) by rfl]
    rw [hstart]
    rw [runConfig_add]
    rw [hscan]
    rw [runConfig_add]
    rw [hboundary]
    rw [hboundaryShape]
    rw [herase]
    simp [erasedBoundaryTape, blankSteps, tail,
      payloadBits, scanTailBits, guardBits,
      cellCodeBits, encodeCell, encodeCodeWordAsInput,
      encodeCodeSymbolAsInput,
      List.reverse_append, List.map_append, List.append_assoc]
  constructor
  · simpa using congrArg Configuration.state hfull
  · simpa using congrArg Configuration.tape hfull

def gapBaseLeft (base : List Bool) (gap : Nat) :
    List (Option Bool) :=
  List.append (List.replicate gap (none : Option Bool))
    (base.reverse.map some)

def rewoundPayloadTape (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells (none :: gapBaseLeft base gap)
    (List.append ((payloadBits cells).map some)
      (none :: none :: none :: none :: none :: padding))

theorem payloadBits_ne_nil (cells : List (Bool × Bool)) :
    payloadBits cells ≠ [] := by
  simp [payloadBits, markerBits]

theorem rightEdgeRewindDescription_haltsFrom_erasedBoundary
    (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (erasedBoundaryTape base gap cells padding)
      (rewoundPayloadTape base gap cells padding) := by
  cases hrev : (payloadBits cells).reverse with
  | nil =>
      exfalso
      apply payloadBits_ne_nil cells
      have h := congrArg List.reverse hrev
      simpa using h
  | cons current rest =>
      have hpayloadBack :
          List.append rest.reverse [current] = payloadBits cells := by
        have h := congrArg List.reverse hrev
        simpa using h.symm
      have hrun :=
        rightEdgeRewindDescription_haltsFrom_rightBoundaryBase_noDelimiter
          (gapBaseLeft base gap) rest current
          (none :: none :: none :: none :: padding)
      rw [hpayloadBack] at hrun
      simpa [erasedBoundaryTape, rewoundPayloadTape,
        gapBaseLeft, hrev,
        List.replicate_succ, List.append_assoc] using hrun

def gapLocatorDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.left 1
    , transition 1 (some false) (some false) Direction.right 2
    , transition 1 (some true) (some true) Direction.right 2 ]

theorem gapLocatorDescription_subroutineReady :
    gapLocatorDescription.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    gapLocatorDescription (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

def restoredSourceTape (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells (base.reverse.map some)
    (none ::
      List.append (List.replicate gap (none : Option Bool))
        (List.append ((payloadBits cells).map some)
          (none :: none :: none :: none :: none :: padding)))

private theorem run_gap_blanks (n : Nat) (boundary : Bool)
    (left right : List (Option Bool)) :
    gapLocatorDescription.runConfig (n + 1)
        { state := 1
          tape := tapeAtCells
            (List.append (List.replicate n (none : Option Bool))
              (some boundary :: left))
            (none :: right) } =
      { state := 1
        tape := tapeAtCells left
          (some boundary ::
            List.append (List.replicate (n + 1) none) right) } := by
  induction n generalizing right with
  | zero =>
      cases boundary <;>
        simp [gapLocatorDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | succ n ih =>
      rw [show Nat.succ n + 1 = 1 + (n + 1) by lia]
      rw [runConfig_add]
      rw [show
        List.append (List.replicate (Nat.succ n) (none : Option Bool))
            (some boundary :: left) =
          none :: List.append (List.replicate n none)
            (some boundary :: left) by
        simp [List.replicate_succ]]
      have hstep :
          gapLocatorDescription.runConfig 1
              { state := 1
                tape := tapeAtCells
                  (none :: List.append (List.replicate n none)
                    (some boundary :: left))
                  (none :: right) } =
            { state := 1
              tape := tapeAtCells
                (List.append (List.replicate n none)
                  (some boundary :: left))
                (none :: none :: right) } := by
        simp [gapLocatorDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      rw [ih (none :: right)]
      rw [replicate_none_append_none_cons]
      rw [show 1 + (n + 1) = Nat.succ (n + 1) by lia]
      rfl

theorem gapLocatorDescription_haltsFrom_rewoundPayload
    (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool))
    (hbase : base ≠ []) :
    gapLocatorDescription.HaltsFromTape
      (rewoundPayloadTape base gap cells padding)
      (restoredSourceTape base gap cells padding) := by
  cases hrev : base.reverse with
  | nil =>
      exfalso
      apply hbase
      have h := congrArg List.reverse hrev
      simpa using h
  | cons boundary left =>
      let right : List (Option Bool) :=
        List.append ((payloadBits cells).map some)
          (none :: none :: none :: none :: none :: padding)
      have hstart :
          gapLocatorDescription.runConfig 1
              { state := gapLocatorDescription.start
                tape := tapeAtCells
                  (none ::
                    List.append (List.replicate gap none)
                      (some boundary :: left.map some))
                  right } =
            { state := 1
              tape := tapeAtCells
                (List.append (List.replicate gap none)
                  (some boundary :: left.map some))
                (none :: right) } := by
        simp [right, payloadBits, markerBits,
          gapLocatorDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      have hblanks := run_gap_blanks gap boundary (left.map some) right
      have hfinish :
          gapLocatorDescription.runConfig 1
              { state := 1
                tape := tapeAtCells (left.map some)
                  (some boundary ::
                    List.append (List.replicate (gap + 1) none) right) } =
            { state := gapLocatorDescription.halt
              tape := tapeAtCells (some boundary :: left.map some)
                (none ::
                  List.append (List.replicate gap none) right) } := by
        cases boundary <;>
          simp [gapLocatorDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            List.replicate_succ]
      refine ⟨gap + 3, ?_, ?_⟩
      · have hfull :
            (gapLocatorDescription.runConfig (gap + 3)
              { state := gapLocatorDescription.start
                tape := rewoundPayloadTape base gap cells padding }).state =
              gapLocatorDescription.halt := by
          rw [show gap + 3 = 1 + ((gap + 1) + 1) by lia]
          rw [runConfig_add]
          simp only [rewoundPayloadTape, gapBaseLeft, hrev, List.map_cons]
          rw [hstart]
          rw [runConfig_add]
          rw [hblanks]
          rw [hfinish]
        exact hfull
      · have hfull :
            (gapLocatorDescription.runConfig (gap + 3)
              { state := gapLocatorDescription.start
                tape := rewoundPayloadTape base gap cells padding }).tape =
              restoredSourceTape base gap cells padding := by
          rw [show gap + 3 = 1 + ((gap + 1) + 1) by lia]
          rw [runConfig_add]
          simp only [rewoundPayloadTape, gapBaseLeft, hrev, List.map_cons]
          rw [hstart]
          rw [runConfig_add]
          rw [hblanks]
          rw [hfinish]
          simp [restoredSourceTape, right, hrev,
            List.replicate_succ, List.append_assoc]
        exact hfull

def seekEraseRewindDescription : MachineDescription :=
  canonicalSeqDescription seekEraseDescription rightEdgeRewindDescription

theorem seekEraseRewindDescription_subroutineReady :
    seekEraseRewindDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    seekEraseDescription_subroutineReady
    rightEdgeRewindDescription_subroutineReady

theorem erasedBoundaryTape_move_left_move_right
    (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (erasedBoundaryTape base gap cells padding)) =
      erasedBoundaryTape base gap cells padding := by
  simp [erasedBoundaryTape, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem seekEraseRewindDescription_haltsFromTape
    (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) :
    seekEraseRewindDescription.HaltsFromTape
      (sourceTape base gap cells padding)
      (rewoundPayloadTape base gap cells padding) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      seekEraseDescription_subroutineReady
      rightEdgeRewindDescription_subroutineReady
      (seekEraseDescription_haltsFromTape base gap cells padding)
      (erasedBoundaryTape_move_left_move_right base gap cells padding)
      (rightEdgeRewindDescription_haltsFrom_erasedBoundary
        base gap cells padding)

theorem rewoundPayloadTape_move_left_move_right
    (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rewoundPayloadTape base gap cells padding)) =
      rewoundPayloadTape base gap cells padding := by
  simp [rewoundPayloadTape, gapBaseLeft,
    payloadBits, markerBits, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

def description : MachineDescription :=
  canonicalSeqDescription seekEraseRewindDescription gapLocatorDescription

theorem description_subroutineReady : description.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    seekEraseRewindDescription_subroutineReady
    gapLocatorDescription_subroutineReady

theorem description_haltsFromTape
    (base : List Bool) (gap : Nat)
    (cells : List (Bool × Bool))
    (padding : List (Option Bool))
    (hbase : base ≠ []) :
    description.HaltsFromTape
      (sourceTape base gap cells padding)
      (restoredSourceTape base gap cells padding) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      seekEraseRewindDescription_subroutineReady
      gapLocatorDescription_subroutineReady
      (seekEraseRewindDescription_haltsFromTape base gap cells padding)
      (rewoundPayloadTape_move_left_move_right base gap cells padding)
      (gapLocatorDescription_haltsFrom_rewoundPayload
        base gap cells padding hbase)

end RightGuardRemover

theorem guardedRightQuotedBits_eq
    (T : Tape Bool) :
    quotedPairBits
        ((guardLogicalTape T).right.map logicalCellPair) =
      List.append
        (RightLengthCopyScratch.cellTokenBits
          (T.right.map logicalCellPair))
        RightGuardRemover.guardBits := by
  calc
    quotedPairBits
        ((guardLogicalTape T).right.map logicalCellPair) =
        cellsCodeBits (guardLogicalTape T).right :=
      RawPairQuoter.quotedPairBits_map_logicalCellPair _
    _ = cellsCodeBits (List.append T.right [none]) := by
      rfl
    _ = List.append (cellsCodeBits T.right) (cellCodeBits none) := by
      have happ := cellsCodeBits_append T.right [none]
      have hsingle : cellsCodeBits [none] = cellCodeBits none := by
        rfl
      rw [hsingle] at happ
      exact happ
    _ = List.append
          (RightLengthCopyScratch.cellTokenBits
            (T.right.map logicalCellPair))
          RightGuardRemover.guardBits := by
      rw [rightCellTokenBits_eq_quotedPairBits]
      rw [RawPairQuoter.quotedPairBits_map_logicalCellPair]
      rfl

theorem correctedHeadExtractedTape_eq_rightGuardSource
    (T : Tape Bool) (padding : List (Option Bool)) :
    correctedHeadExtractedTape T padding =
      RightGuardRemover.sourceTape
        (leftHeadFieldBits T) (correctedHeadScratch T)
        (T.right.map logicalCellPair) padding := by
  rw [correctedHeadExtractedTape]
  unfold HeadCellExtractorScratch.headExtractedTape
  unfold HeadCellExtractorScratch.targetTape
  unfold RightGuardRemover.sourceTape
  rw [guardedRightQuotedBits_eq]
  cases hhead : T.head with
  | none =>
      simp [leftHeadFieldBits, RightGuardRemover.payloadBits,
        RightGuardRemover.markerBits, RightGuardRemover.guardBits,
        hhead, guardLogicalTape, cellCodeBits, logicalCellPair,
        encodeCell, encodeCodeWordAsInput,
        encodeCodeSymbolAsInput, List.map_append,
        List.reverse_append, List.append_assoc]
  | some bit =>
      cases bit <;>
        simp [leftHeadFieldBits, RightGuardRemover.payloadBits,
          RightGuardRemover.markerBits, RightGuardRemover.guardBits,
          hhead, guardLogicalTape, cellCodeBits, logicalCellPair,
          encodeCell, encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, List.map_append,
          List.reverse_append, List.append_assoc]

def correctedLeftHeadRightGuardRemovedDescription : MachineDescription :=
  canonicalSeqDescription correctedLeftAndHeadDescription
    RightGuardRemover.description

theorem correctedLeftHeadRightGuardRemovedDescription_subroutineReady :
    correctedLeftHeadRightGuardRemovedDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    correctedLeftAndHeadDescription_subroutineReady
    RightGuardRemover.description_subroutineReady

def rightGuardRemovedTape
    (T : Tape Bool) (padding : List (Option Bool)) : Tape Bool :=
  RightGuardRemover.restoredSourceTape
    (leftHeadFieldBits T) (correctedHeadScratch T)
    (T.right.map logicalCellPair) padding

theorem correctedHeadExtractedTape_move_left_move_right
    (T : Tape Bool) (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (correctedHeadExtractedTape T padding)) =
      RightGuardRemover.sourceTape
        (leftHeadFieldBits T) (correctedHeadScratch T)
        (T.right.map logicalCellPair) padding := by
  rw [correctedHeadExtractedTape_eq_rightGuardSource]
  simp [RightGuardRemover.sourceTape,
    RightGuardRemover.payloadBits,
    RightGuardRemover.markerBits,
    correctedHeadScratch, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight,
    List.replicate_succ]

theorem correctedLeftHeadRightGuardRemovedDescription_haltsFrom_markerTarget
    (T : Tape Bool) (padding : List (Option Bool)) :
    correctedLeftHeadRightGuardRemovedDescription.HaltsFromTapeEquiv
      (RawPairMarker.targetTape (guardLogicalTape T) padding)
      (rightGuardRemovedTape T padding) := by
  have hfirst :=
    correctedLeftAndHeadDescription_haltsFrom_markerTarget T padding
  have hremove :=
    RightGuardRemover.description_haltsFromTape
      (leftHeadFieldBits T) (correctedHeadScratch T)
      (T.right.map logicalCellPair) padding
      (leftHeadFieldBits_ne_nil T)
  simpa [correctedLeftHeadRightGuardRemovedDescription,
    rightGuardRemovedTape] using
    canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv_haltsFromTape
      correctedLeftAndHeadDescription_subroutineReady
      RightGuardRemover.description_subroutineReady
      hfirst
      (correctedHeadExtractedTape_move_left_move_right T padding)
      hremove

def correctedRightPaddingTail (i : Index) : List (Option Bool) :=
  List.append (List.replicate 8 (none : Option Bool))
    (RightLengthCopyScratch.rightAssemblyPaddingTail i)

private theorem fiveBlankPrefix_commutesAcross_noneBlock
    (n : Nat) (tail : List (Option Bool)) :
    none :: none :: none :: none :: none ::
        List.append (List.replicate n (none : Option Bool))
          (none :: none :: none :: none :: none :: none :: none :: tail) =
      none ::
        List.append (List.replicate n (none : Option Bool))
          (none :: none :: none :: none :: none :: none :: none :: none ::
            none :: none :: none :: tail) := by
  congr 1
  rw [← replicate_none_append_none_cons n]
  rw [← replicate_none_append_none_cons n]
  rw [← replicate_none_append_none_cons n]
  rw [← replicate_none_append_none_cons n]

theorem rightGuardRemovedTape_eq_rightLengthSource (i : Index) :
    rightGuardRemovedTape i.finalTape (rewindPadding i) =
      RightLengthCopyScratch.sourceTape
        (leftHeadFieldBits i.finalTape)
        (correctedHeadScratch i.finalTape)
        (i.finalTape.right.map logicalCellPair)
        (none :: none :: correctedRightPaddingTail i) := by
  rw [RightLengthCopyScratch.rewindPadding_eq_rightAssemblyPrefix]
  rw [show
    4 * (guardLogicalTape i.finalTape).right.length =
      4 * i.finalTape.right.length + 4 by
    simp [guardLogicalTape]
    lia]
  unfold rightGuardRemovedTape RightGuardRemover.restoredSourceTape
  have hsplit :
      List.append
          (List.replicate (4 * i.finalTape.right.length + 4)
            (none : Option Bool))
          (none :: none :: none ::
            RightLengthCopyScratch.rightAssemblyPaddingTail i) =
        List.append
          (List.replicate (4 * i.finalTape.right.length) none)
          (List.append (List.replicate 4 none)
            (none :: none :: none ::
              RightLengthCopyScratch.rightAssemblyPaddingTail i)) := by
    exact FoC.Computability.list_replicate_add_append
      (none : Option Bool) (4 * i.finalTape.right.length) 4 _
  rw [hsplit]
  simp [RightGuardRemover.payloadBits,
    RightGuardRemover.markerBits,
    RightLengthCopyScratch.sourceTape,
    RightLengthCopyScratch.markerBits_eq,
    correctedRightPaddingTail, guardLogicalTape,
    List.map_append, List.append_assoc,
    List.replicate_succ]
  congr 1
  exact congrArg
    (fun suffix : List (Option Bool) =>
      none ::
        List.append
          (List.replicate (correctedHeadScratch i.finalTape) none)
          (some false :: some true :: some true :: some true ::
            List.append
              ((RightLengthCopyScratch.cellTokenBits
                (i.finalTape.right.map logicalCellPair)).map some)
              suffix))
    (fiveBlankPrefix_commutesAcross_noneBlock
      (4 * i.finalTape.right.length)
      (RightLengthCopyScratch.rightAssemblyPaddingTail i))

def correctedTapeFieldDescription : MachineDescription :=
  canonicalSeqDescription correctedLeftHeadRightGuardRemovedDescription
    RightLengthCopyScratch.rightLengthAssemblyDescription

theorem correctedTapeFieldDescription_subroutineReady :
    correctedTapeFieldDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    correctedLeftHeadRightGuardRemovedDescription_subroutineReady
    RightLengthCopyScratch.rightLengthAssemblyDescription_subroutineReady

def correctedSerializedTapeFieldTarget (i : Index) : Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding
    ((leftHeadFieldBits i.finalTape).reverse.map some)
    (RightLengthCopyScratch.compactedPayloadBits
      (i.finalTape.right.map logicalCellPair))
    (sentinelGapCompactorFinalPadding
      (correctedHeadScratch i.finalTape) 2
      (none :: correctedRightPaddingTail i))

theorem rightGuardRemovedTape_move_left_move_right (i : Index) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightGuardRemovedTape i.finalTape (rewindPadding i))) =
      RightLengthCopyScratch.sourceTape
        (leftHeadFieldBits i.finalTape)
        (correctedHeadScratch i.finalTape)
        (i.finalTape.right.map logicalCellPair)
        (none :: none :: correctedRightPaddingTail i) := by
  rw [rightGuardRemovedTape_eq_rightLengthSource]
  simp [RightLengthCopyScratch.sourceTape,
    correctedHeadScratch, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight,
    List.replicate_succ]

theorem correctedTapeFieldDescription_haltsFrom_markerTarget (i : Index) :
    correctedTapeFieldDescription.HaltsFromTapeEquiv
      (RawPairMarker.targetTape
        (guardLogicalTape i.finalTape) (rewindPadding i))
      (correctedSerializedTapeFieldTarget i) := by
  have hfirst :=
    correctedLeftHeadRightGuardRemovedDescription_haltsFrom_markerTarget
      i.finalTape (rewindPadding i)
  have hright :=
    RightLengthCopyScratch.rightLengthAssemblyDescription_haltsFromTape
      (leftHeadFieldBits i.finalTape)
      (correctedHeadScratch i.finalTape)
      (i.finalTape.right.map logicalCellPair)
      (correctedRightPaddingTail i)
      (leftHeadFieldBits_ne_nil i.finalTape)
      (rightCells_valid i.finalTape.right)
  simpa [correctedTapeFieldDescription,
    correctedSerializedTapeFieldTarget] using
    canonicalSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv_haltsFromTape
      correctedLeftHeadRightGuardRemovedDescription_subroutineReady
      RightLengthCopyScratch.rightLengthAssemblyDescription_subroutineReady
      hfirst
      (rightGuardRemovedTape_move_left_move_right i)
      hright

theorem rightTicksBits_append_tickBits_commute (n : Nat) :
    List.append (RightLengthCopyScratch.ticksBits n)
        RightLengthCopyScratch.tickBits =
      List.append RightLengthCopyScratch.tickBits
        (RightLengthCopyScratch.ticksBits n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        List.append (RightLengthCopyScratch.ticksBits (Nat.succ n))
            RightLengthCopyScratch.tickBits =
          List.append
            (List.append (RightLengthCopyScratch.ticksBits n)
              RightLengthCopyScratch.tickBits)
            RightLengthCopyScratch.tickBits := by
              rfl
        _ = List.append
              (List.append RightLengthCopyScratch.tickBits
                (RightLengthCopyScratch.ticksBits n))
              RightLengthCopyScratch.tickBits := by
                rw [ih]
        _ = List.append RightLengthCopyScratch.tickBits
              (RightLengthCopyScratch.ticksBits (Nat.succ n)) := by
                simp [RightLengthCopyScratch.ticksBits,
                  List.append_assoc]

theorem rightTicksDoneBits_eq_stageNatBits (n : Nat) :
    List.append (RightLengthCopyScratch.ticksBits n)
        RightLengthCopyScratch.doneBits =
      stageNatBits n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        List.append (RightLengthCopyScratch.ticksBits (Nat.succ n))
            RightLengthCopyScratch.doneBits =
          List.append
            (List.append (RightLengthCopyScratch.ticksBits n)
              RightLengthCopyScratch.tickBits)
            RightLengthCopyScratch.doneBits := by
              rfl
        _ = List.append
              (List.append RightLengthCopyScratch.tickBits
                (RightLengthCopyScratch.ticksBits n))
              RightLengthCopyScratch.doneBits := by
                rw [rightTicksBits_append_tickBits_commute]
        _ = List.append RightLengthCopyScratch.tickBits
              (List.append (RightLengthCopyScratch.ticksBits n)
                RightLengthCopyScratch.doneBits) := by
                simp [List.append_assoc]
        _ = List.append RightLengthCopyScratch.tickBits
              (stageNatBits n) := by
                rw [ih]
        _ = stageNatBits (Nat.succ n) := by
              simpa [RightLengthCopyScratch.tickBits,
                encodeCodeSymbolAsInput] using
                (stageNatBits_succ n).symm

theorem rightCellTokenBits_map_logicalCellPair
    (cells : List (Option Bool)) :
    RightLengthCopyScratch.cellTokenBits
        (cells.map logicalCellPair) =
      cellsCodeBits cells := by
  rw [rightCellTokenBits_eq_quotedPairBits]
  exact RawPairQuoter.quotedPairBits_map_logicalCellPair cells

theorem compactedRightPayloadBits_eq_fields (T : Tape Bool) :
    RightLengthCopyScratch.compactedPayloadBits
        (T.right.map logicalCellPair) =
      List.append (stageNatBits T.right.length)
        (cellsCodeBits T.right) := by
  unfold RightLengthCopyScratch.compactedPayloadBits
  rw [rightTicksDoneBits_eq_stageNatBits]
  rw [rightCellTokenBits_map_logicalCellPair]
  simp

theorem leftHead_compactedRight_eq_exactTapeFieldBits (T : Tape Bool) :
    List.append (leftHeadFieldBits T)
        (RightLengthCopyScratch.compactedPayloadBits
          (T.right.map logicalCellPair)) =
      LengthAssemblyScratch.exactTapeFieldBits T [] := by
  rw [compactedRightPayloadBits_eq_fields]
  simp [leftHeadFieldBits, leftFieldBits,
    LengthAssemblyScratch.exactTapeFieldBits,
    List.append_assoc]

end GuardedEgress.EgressIntegrationScratch
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
