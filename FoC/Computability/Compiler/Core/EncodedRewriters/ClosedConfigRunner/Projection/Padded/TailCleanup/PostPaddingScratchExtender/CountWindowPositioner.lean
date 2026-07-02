import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountedSuffixBoundaryLocator
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchExtender.Adapters

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

def scratchCountSuffixPositionerSourceTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells [none]
    (List.append
      (pref.map some)
      (List.append
        (suffix.map some)
        (none ::
          none ::
          List.append
            (List.replicate suffix.length (none : Option Bool))
            rightTail)))

def scratchCountSuffixRestorerSourceTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (none :: pref.reverse.map some)
    (List.append
      (suffix.map some)
      (none ::
        List.append
          (List.replicate (suffix.length + 1) (none : Option Bool))
          rightTail))

def ScratchCountSuffixPositionerHandoffSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall pref suffix : Word Bool,
    forall (first : Bool) (rightTail : List (Option Bool)),
      0 < suffix.length ->
      positioner.HaltsFromTape
        (Tape.move Direction.right
          (scratchCountSuffixPositionerSourceTape pref suffix
            (some first :: rightTail)))
        (scratchCountSuffixRestorerSourceTape pref suffix
          (some first :: rightTail))

def ScratchCountSuffixPositionerHandoffConstruction : Prop :=
  exists positioner : MachineDescription,
    ScratchCountSuffixPositionerHandoffSpec positioner

def scratchCountSuffixPositionerRightEdgeTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape Bool :=
  match List.append pref suffix with
  | [] =>
      Tape.move Direction.right
        (scratchCountSuffixPositionerSourceTape pref suffix rightTail)
  | first :: rest =>
      rightEdgeScanTargetTapeFromLeft
        (some first :: [none]) rest
        (none ::
          List.append
            (List.replicate suffix.length (none : Option Bool))
            rightTail)

def ScratchCountSuffixBoundaryPositionerSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall pref suffix : Word Bool,
    forall (first : Bool) (rightTail : List (Option Bool)),
      0 < suffix.length ->
      positioner.HaltsFromTape
        (Tape.move Direction.left
          (Tape.move Direction.right
            (scratchCountSuffixPositionerRightEdgeTape
              pref suffix (some first :: rightTail))))
        (scratchCountSuffixRestorerSourceTape pref suffix
          (some first :: rightTail))

def ScratchCountSuffixBoundaryPositionerConstruction : Prop :=
  exists positioner : MachineDescription,
    ScratchCountSuffixBoundaryPositionerSpec positioner

def rightSecondCellTrueMarkerTargetTape (T : Tape Bool) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.left
      (Tape.write (some true)
        (Tape.move Direction.right (Tape.move Direction.right T))))

def rightSecondCellTrueMarkerDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 0 (some false) (some false) Direction.right 1
    , transition 0 (some true) (some true) Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 1 (some false) (some false) Direction.right 2
    , transition 1 (some true) (some true) Direction.right 2
    , transition 2 none (some true) Direction.left 3
    , transition 2 (some false) (some true) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 none none Direction.left 4
    , transition 3 (some false) (some false) Direction.left 4
    , transition 3 (some true) (some true) Direction.left 4
    ]

theorem rightSecondCellTrueMarkerDescription_wellFormed :
    rightSecondCellTrueMarkerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightSecondCellTrueMarkerDescription.transitions)
      (stateCount := rightSecondCellTrueMarkerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightSecondCellTrueMarkerDescription.transitions)
      (by decide)

theorem rightSecondCellTrueMarkerDescription_haltTransitionFree :
    rightSecondCellTrueMarkerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightSecondCellTrueMarkerDescription.transitions)
    (state := rightSecondCellTrueMarkerDescription.halt)
    (by decide)

theorem rightSecondCellTrueMarkerDescription_subroutineReady :
    rightSecondCellTrueMarkerDescription.SubroutineReady :=
  ⟨rightSecondCellTrueMarkerDescription_wellFormed,
    rightSecondCellTrueMarkerDescription_haltTransitionFree⟩

theorem rightSecondCellTrueMarkerDescription_step_start
    (T : Tape Bool) :
    rightSecondCellTrueMarkerDescription.runConfig 1
        { state := rightSecondCellTrueMarkerDescription.start
          tape := T } =
      { state := 1
        tape := Tape.move Direction.right T } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          simp [rightSecondCellTrueMarkerDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write]
      | some bit =>
          cases bit <;>
            simp [rightSecondCellTrueMarkerDescription, runConfig,
              stepConfig, lookupTransition, Matches, transition,
              Tape.read, Tape.write]

theorem rightSecondCellTrueMarkerDescription_step_second
    (T : Tape Bool) :
    rightSecondCellTrueMarkerDescription.runConfig 1
        { state := 1
          tape := T } =
      { state := 2
        tape := Tape.move Direction.right T } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          simp [rightSecondCellTrueMarkerDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write]
      | some bit =>
          cases bit <;>
            simp [rightSecondCellTrueMarkerDescription, runConfig,
              stepConfig, lookupTransition, Matches, transition,
              Tape.read, Tape.write]

theorem rightSecondCellTrueMarkerDescription_step_write
    (T : Tape Bool) :
    rightSecondCellTrueMarkerDescription.runConfig 1
        { state := 2
          tape := T } =
      { state := 3
        tape := Tape.move Direction.left (Tape.write (some true) T) } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          simp [rightSecondCellTrueMarkerDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write]
      | some bit =>
          cases bit <;>
            simp [rightSecondCellTrueMarkerDescription, runConfig,
              stepConfig, lookupTransition, Matches, transition,
              Tape.read, Tape.write]

theorem rightSecondCellTrueMarkerDescription_step_return
    (T : Tape Bool) :
    rightSecondCellTrueMarkerDescription.runConfig 1
        { state := 3
          tape := T } =
      { state := rightSecondCellTrueMarkerDescription.halt
        tape := Tape.move Direction.left T } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          simp [rightSecondCellTrueMarkerDescription, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write]
      | some bit =>
          cases bit <;>
            simp [rightSecondCellTrueMarkerDescription, runConfig,
              stepConfig, lookupTransition, Matches, transition,
              Tape.read, Tape.write]

theorem rightSecondCellTrueMarkerDescription_run
    (T : Tape Bool) :
    rightSecondCellTrueMarkerDescription.runConfig 4
        { state := rightSecondCellTrueMarkerDescription.start
          tape := T } =
      { state := rightSecondCellTrueMarkerDescription.halt
        tape := rightSecondCellTrueMarkerTargetTape T } := by
  rw [show 4 = 1 + (1 + (1 + 1)) by lia]
  rw [runConfig_add]
  rw [rightSecondCellTrueMarkerDescription_step_start]
  rw [runConfig_add]
  rw [rightSecondCellTrueMarkerDescription_step_second]
  rw [runConfig_add]
  rw [rightSecondCellTrueMarkerDescription_step_write]
  simpa [rightSecondCellTrueMarkerTargetTape] using
    rightSecondCellTrueMarkerDescription_step_return
      (Tape.move Direction.left
        (Tape.write (some true)
          (Tape.move Direction.right (Tape.move Direction.right T))))

theorem rightSecondCellTrueMarkerDescription_haltsFromTape
    (T : Tape Bool) :
    rightSecondCellTrueMarkerDescription.HaltsFromTape T
      (rightSecondCellTrueMarkerTargetTape T) := by
  refine ⟨4, ?_⟩
  constructor <;>
    rw [rightSecondCellTrueMarkerDescription_run]

def scratchCountSuffixBoundaryPositionerSourceTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.right
      (scratchCountSuffixPositionerRightEdgeTape pref suffix rightTail))

def scratchCountSuffixBoundaryMarkedTape
    (pref suffix : Word Bool) (rightTail : List (Option Bool)) :
    Tape Bool :=
  rightSecondCellTrueMarkerTargetTape
    (scratchCountSuffixBoundaryPositionerSourceTape
      pref suffix rightTail)

def ScratchCountSuffixBoundaryMarkerInitSpec
    (markerInit : MachineDescription) : Prop :=
  markerInit.SubroutineReady ∧
    forall pref suffix : Word Bool,
    forall rightTail : List (Option Bool),
      0 < suffix.length ->
      markerInit.HaltsFromTape
        (scratchCountSuffixBoundaryPositionerSourceTape
          pref suffix rightTail)
        (scratchCountSuffixBoundaryMarkedTape pref suffix rightTail)

def ScratchCountSuffixBoundaryMarkerInitConstruction : Prop :=
  exists markerInit : MachineDescription,
    ScratchCountSuffixBoundaryMarkerInitSpec markerInit

def ScratchCountSuffixMarkedBoundaryPositionerSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall pref suffix : Word Bool,
    forall (first : Bool) (rightTail : List (Option Bool)),
      0 < suffix.length ->
      positioner.HaltsFromTape
        (Tape.move Direction.left
          (Tape.move Direction.right
            (scratchCountSuffixBoundaryMarkedTape
              pref suffix (some first :: rightTail))))
        (scratchCountSuffixRestorerSourceTape pref suffix
          (some first :: rightTail))

def ScratchCountSuffixMarkedBoundaryPositionerConstruction : Prop :=
  exists positioner : MachineDescription,
    ScratchCountSuffixMarkedBoundaryPositionerSpec positioner

def scratchCountSuffixMarkedBoundaryCleanupSourceTape
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (none ::
      List.append (suffix.reverse.map some)
        (none :: pref.reverse.map some))
    (some true ::
      List.append
        (List.replicate suffix.length (none : Option Bool))
        (some first :: rightTail))

def ScratchCountSuffixMarkedBoundaryPreCleanupPositionerSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall pref suffix : Word Bool,
    forall (first : Bool) (rightTail : List (Option Bool)),
      0 < suffix.length ->
      positioner.HaltsFromTape
        (Tape.move Direction.left
          (Tape.move Direction.right
            (scratchCountSuffixBoundaryMarkedTape
              pref suffix (some first :: rightTail))))
        (scratchCountSuffixMarkedBoundaryCleanupSourceTape
          pref suffix first rightTail)

def ScratchCountSuffixMarkedBoundaryPreCleanupPositionerConstruction :
    Prop :=
  exists positioner : MachineDescription,
    ScratchCountSuffixMarkedBoundaryPreCleanupPositionerSpec positioner

def scratchCountSuffixMarkedBoundaryPrefixGapSourceTape
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    Tape Bool :=
  rightEdgeScanTargetTapeFromLeft
    (List.append (pref.reverse.map some) [none]) suffix
    (some true ::
      List.append
        (List.replicate suffix.length (none : Option Bool))
        (some first :: rightTail))

def scratchCountSuffixMarkedBoundaryPostGapTape
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    Tape Bool :=
  rightEdgeScanTargetTapeFromLeft
    (none :: pref.reverse.map some) suffix
    (some true ::
      List.append
        (List.replicate suffix.length (none : Option Bool))
        (some first :: rightTail))

def ScratchCountSuffixMarkedBoundaryPrefixGapCompactorSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall pref suffix : Word Bool,
    forall (first : Bool) (rightTail : List (Option Bool)),
      0 < suffix.length ->
      positioner.HaltsFromTape
        (Tape.move Direction.left
          (Tape.move Direction.right
            (scratchCountSuffixBoundaryMarkedTape
              pref suffix (some first :: rightTail))))
        (scratchCountSuffixMarkedBoundaryPostGapTape
          pref suffix first rightTail)

def ScratchCountSuffixMarkedBoundaryPrefixGapCompactorConstruction :
    Prop :=
  exists positioner : MachineDescription,
    ScratchCountSuffixMarkedBoundaryPrefixGapCompactorSpec positioner

def ScratchCountSuffixMarkedBoundarySeparatorMoverSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall pref suffix : Word Bool,
    forall (first : Bool) (rightTail : List (Option Bool)),
      0 < suffix.length ->
      positioner.HaltsFromTape
        (scratchCountSuffixMarkedBoundaryPrefixGapSourceTape
          pref suffix first rightTail)
        (scratchCountSuffixMarkedBoundaryPostGapTape
          pref suffix first rightTail)

def ScratchCountSuffixMarkedBoundarySeparatorMoverConstruction :
    Prop :=
  exists positioner : MachineDescription,
    ScratchCountSuffixMarkedBoundarySeparatorMoverSpec positioner

def scratchCountSuffixMarkedBoundarySeparatorPadding
    (suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) : List (Option Bool) :=
  some true ::
    List.append
      (List.replicate suffix.length (none : Option Bool))
      (some first :: rightTail)

def scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    Tape Bool :=
  rightEdgeRewindTargetTape (List.append pref suffix)
    (scratchCountSuffixMarkedBoundarySeparatorPadding
      suffix first rightTail)

def scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    Tape Bool :=
  rightEdgeScanSourceTapeFromLeft
    (none :: pref.reverse.map some) suffix
    (scratchCountSuffixMarkedBoundarySeparatorPadding
      suffix first rightTail)

def ScratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall pref suffix : Word Bool,
    forall (first : Bool) (rightTail : List (Option Bool)),
      0 < suffix.length ->
      positioner.HaltsFromTape
        (scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape
          pref suffix first rightTail)
        (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
          pref suffix first rightTail)

def ScratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterConstruction :
    Prop :=
  exists positioner : MachineDescription,
    ScratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterSpec positioner

def scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    Tape Bool :=
  rightEdgeScanTargetTapeFromLeft [none] (List.append pref suffix)
    (scratchCountSuffixMarkedBoundarySeparatorPadding
      suffix first rightTail)

def ScratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterSpec
    (positioner : MachineDescription) : Prop :=
  positioner.SubroutineReady ∧
    forall pref suffix : Word Bool,
    forall (first : Bool) (rightTail : List (Option Bool)),
      0 < suffix.length ->
      positioner.HaltsFromTape
        (scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape
          pref suffix first rightTail)
        (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
          pref suffix first rightTail)

def ScratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction :
    Prop :=
  exists positioner : MachineDescription,
    ScratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterSpec positioner

theorem scratchCountSuffixMarkedBoundarySeparatorRewind_haltsFrom
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    rightEdgeRewindDescription.HaltsFromTape
      (scratchCountSuffixMarkedBoundaryPrefixGapSourceTape
        pref suffix first rightTail)
      (scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape
        pref suffix first rightTail) := by
  cases hrev : suffix.reverse with
  | nil =>
      have hsuffix : suffix = [] := by
        rw [← List.reverse_reverse suffix, hrev]
        rfl
      simp [hsuffix] at hpos
  | cons current leftRest =>
      have hsuffix : suffix = (current :: leftRest).reverse := by
        rw [← List.reverse_reverse suffix, hrev]
      have hrun :=
        rightEdgeRewindDescription_haltsFrom_lastBitBoundary
          (leftStack := List.append leftRest pref.reverse)
          (current := current)
          (padding :=
            scratchCountSuffixMarkedBoundarySeparatorPadding
              suffix first rightTail)
      simpa [
        scratchCountSuffixMarkedBoundaryPrefixGapSourceTape,
        scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape,
        scratchCountSuffixMarkedBoundarySeparatorPadding,
        rightEdgeScanTargetTapeFromLeft,
        rightEdgeRewindTargetTape,
        hsuffix, List.reverse_append, List.map_append,
        List.append_assoc] using hrun

theorem scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape_move_left_move_right
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape
            pref suffix first rightTail)) =
      scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape
        pref suffix first rightTail := by
  cases pref with
  | nil =>
      cases suffix with
      | nil =>
          simp [scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape,
            scratchCountSuffixMarkedBoundarySeparatorPadding,
            rightEdgeRewindTargetTape, tapeAtCells, Tape.move,
            Tape.moveLeft, Tape.moveRight]
      | cons bit rest =>
          simpa [scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape,
            scratchCountSuffixMarkedBoundarySeparatorPadding] using
            rightEdgeRewindTargetTape_move_left_move_right_cons
              bit rest
              (scratchCountSuffixMarkedBoundarySeparatorPadding
                (bit :: rest) first rightTail)
  | cons bit restPref =>
      simpa [scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape,
        scratchCountSuffixMarkedBoundarySeparatorPadding,
        List.append_assoc] using
        rightEdgeRewindTargetTape_move_left_move_right_cons
          bit (List.append restPref suffix)
          (scratchCountSuffixMarkedBoundarySeparatorPadding
            suffix first rightTail)

theorem scratchCountSuffixMarkedBoundarySeparatorScanSourceTape_move_left_move_right
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
            pref suffix first rightTail)) =
      scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
        pref suffix first rightTail := by
  cases suffix with
  | nil =>
      simp at hpos
  | cons bit rest =>
      cases rest <;>
        simp [scratchCountSuffixMarkedBoundarySeparatorScanSourceTape,
          scratchCountSuffixMarkedBoundarySeparatorPadding,
          rightEdgeScanSourceTapeFromLeft, tapeAtCells, Tape.move,
          Tape.moveLeft, Tape.moveRight, List.replicate_succ]

theorem scratchCountSuffixMarkedBoundarySeparatorScan_haltsFrom
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    rightEdgeScanDescription.HaltsFromTape
      (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
        pref suffix first rightTail)
      (scratchCountSuffixMarkedBoundaryPostGapTape
        pref suffix first rightTail) := by
  simpa [scratchCountSuffixMarkedBoundarySeparatorScanSourceTape,
    scratchCountSuffixMarkedBoundaryPostGapTape,
    scratchCountSuffixMarkedBoundarySeparatorPadding] using
    rightEdgeScanDescription_haltsFromTape
      (none :: pref.reverse.map some) suffix
      (scratchCountSuffixMarkedBoundarySeparatorPadding
        suffix first rightTail)

theorem scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryScan_haltsFrom
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    rightEdgeScanDescription.HaltsFromTape
      (scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape
        pref suffix first rightTail)
      (scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape
        pref suffix first rightTail) := by
  simpa [scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape,
    scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape,
    rightEdgeRewindTargetTape, rightEdgeScanSourceTapeFromLeft] using
    rightEdgeScanDescription_haltsFromTape
      [none] (List.append pref suffix)
      (scratchCountSuffixMarkedBoundarySeparatorPadding
        suffix first rightTail)

theorem rightEdgeScanTargetTapeFromLeft_move_left_move_right
    (left : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeScanTargetTapeFromLeft left bits padding)) =
      rightEdgeScanTargetTapeFromLeft left bits padding := by
  unfold rightEdgeScanTargetTapeFromLeft
  cases hleft : List.append (bits.reverse.map some) left with
  | nil =>
      cases padding <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft,
          Tape.moveRight]
  | cons cell rest =>
      cases padding <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft,
          Tape.moveRight]

theorem scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape_move_left_move_right
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool))
    (_hpos : 0 < suffix.length) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape
            pref suffix first rightTail)) =
      scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape
        pref suffix first rightTail := by
  simpa [scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape] using
    rightEdgeScanTargetTapeFromLeft_move_left_move_right
      [none] (List.append pref suffix)
      (scratchCountSuffixMarkedBoundarySeparatorPadding
        suffix first rightTail)

theorem scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterSpec_of_rightEdgeShifter
    {positioner : MachineDescription}
    (hpositioner :
      ScratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterSpec
        positioner) :
    ScratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterSpec
      (canonicalSeqDescription rightEdgeScanDescription positioner) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        rightEdgeScanDescription_subroutineReady hpositioner.left
  · intro pref suffix first rightTail hpos
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        rightEdgeScanDescription_subroutineReady
        hpositioner.left
        (scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryScan_haltsFrom
          pref suffix first rightTail)
        (scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape_move_left_move_right
          pref suffix first rightTail hpos)
        (hpositioner.right pref suffix first rightTail hpos)

theorem scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterConstruction_of_rightEdgeShifter
    (hpositioner :
      ScratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction) :
    ScratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterConstruction := by
  rcases hpositioner with ⟨positioner, hpositionerSpec⟩
  exact
    ⟨canonicalSeqDescription rightEdgeScanDescription positioner,
      scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterSpec_of_rightEdgeShifter
        hpositionerSpec⟩

theorem scratchCountSuffixMarkedBoundarySeparatorMoverSpec_of_leftBoundaryShifter
    {positioner : MachineDescription}
    (hpositioner :
      ScratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterSpec
        positioner) :
    ScratchCountSuffixMarkedBoundarySeparatorMoverSpec
      (canonicalSeqDescription rightEdgeRewindDescription
        (canonicalSeqDescription positioner rightEdgeScanDescription)) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        rightEdgeRewindDescription_subroutineReady
        (canonicalSeqDescription_subroutineReady hpositioner.left
          rightEdgeScanDescription_subroutineReady)
  · intro pref suffix first rightTail hpos
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        rightEdgeRewindDescription_subroutineReady
        (canonicalSeqDescription_subroutineReady hpositioner.left
          rightEdgeScanDescription_subroutineReady)
        (scratchCountSuffixMarkedBoundarySeparatorRewind_haltsFrom
          pref suffix first rightTail hpos)
        (scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryTape_move_left_move_right
          pref suffix first rightTail)
        (canonicalSeqDescription_haltsFromTape_of_haltsFromTape
          hpositioner.left
          rightEdgeScanDescription_subroutineReady
          (hpositioner.right pref suffix first rightTail hpos)
          (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape_move_left_move_right
            pref suffix first rightTail hpos)
          (scratchCountSuffixMarkedBoundarySeparatorScan_haltsFrom
            pref suffix first rightTail))

theorem scratchCountSuffixMarkedBoundarySeparatorMoverConstruction_of_leftBoundaryShifter
    (hpositioner :
      ScratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterConstruction) :
    ScratchCountSuffixMarkedBoundarySeparatorMoverConstruction := by
  rcases hpositioner with ⟨positioner, hpositionerSpec⟩
  exact
    ⟨canonicalSeqDescription rightEdgeRewindDescription
        (canonicalSeqDescription positioner rightEdgeScanDescription),
      scratchCountSuffixMarkedBoundarySeparatorMoverSpec_of_leftBoundaryShifter
        hpositionerSpec⟩

theorem scratchCountSuffixMarkedBoundaryPrefixGapSourceTape_eq_boundaryMarked
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixBoundaryMarkedTape
            pref suffix (some first :: rightTail))) =
      scratchCountSuffixMarkedBoundaryPrefixGapSourceTape
        pref suffix first rightTail := by
  cases suffix with
  | nil =>
      simp at hpos
  | cons bit restSuffix =>
      cases pref with
      | nil =>
          cases hrev : (List.map some restSuffix).reverse with
          | nil =>
              simp [scratchCountSuffixMarkedBoundaryPrefixGapSourceTape,
                scratchCountSuffixBoundaryMarkedTape,
                rightSecondCellTrueMarkerTargetTape,
                scratchCountSuffixBoundaryPositionerSourceTape,
                scratchCountSuffixPositionerRightEdgeTape,
                rightEdgeScanTargetTapeFromLeft,
                tapeAtCells, Tape.move, Tape.moveLeft,
                Tape.moveRight, Tape.write, hrev, List.reverse_cons,
                List.map_append]
          | cons cell tail =>
              simp [scratchCountSuffixMarkedBoundaryPrefixGapSourceTape,
                scratchCountSuffixBoundaryMarkedTape,
                rightSecondCellTrueMarkerTargetTape,
                scratchCountSuffixBoundaryPositionerSourceTape,
                scratchCountSuffixPositionerRightEdgeTape,
                rightEdgeScanTargetTapeFromLeft,
                tapeAtCells, Tape.move, Tape.moveLeft,
                Tape.moveRight, Tape.write, hrev, List.reverse_cons,
                List.map_append]
      | cons p ps =>
          cases hrev : (List.map some restSuffix).reverse with
          | nil =>
              simp [scratchCountSuffixMarkedBoundaryPrefixGapSourceTape,
                scratchCountSuffixBoundaryMarkedTape,
                rightSecondCellTrueMarkerTargetTape,
                scratchCountSuffixBoundaryPositionerSourceTape,
                scratchCountSuffixPositionerRightEdgeTape,
                rightEdgeScanTargetTapeFromLeft,
                tapeAtCells, Tape.move, Tape.moveLeft,
                Tape.moveRight, Tape.write, hrev, List.reverse_cons,
                List.map_append, List.reverse_append, List.append_assoc]
          | cons cell tail =>
              simp [scratchCountSuffixMarkedBoundaryPrefixGapSourceTape,
                scratchCountSuffixBoundaryMarkedTape,
                rightSecondCellTrueMarkerTargetTape,
                scratchCountSuffixBoundaryPositionerSourceTape,
                scratchCountSuffixPositionerRightEdgeTape,
                rightEdgeScanTargetTapeFromLeft,
                tapeAtCells, Tape.move, Tape.moveLeft,
                Tape.moveRight, Tape.write, hrev, List.reverse_cons,
                List.map_append, List.reverse_append, List.append_assoc]

theorem scratchCountSuffixMarkedBoundaryPrefixGapCompactorSpec_of_separatorMover
    {positioner : MachineDescription}
    (hpositioner :
      ScratchCountSuffixMarkedBoundarySeparatorMoverSpec positioner) :
    ScratchCountSuffixMarkedBoundaryPrefixGapCompactorSpec positioner := by
  constructor
  · exact hpositioner.left
  · intro pref suffix first rightTail hpos
    rw [
      scratchCountSuffixMarkedBoundaryPrefixGapSourceTape_eq_boundaryMarked
        pref suffix first rightTail hpos]
    exact hpositioner.right pref suffix first rightTail hpos

theorem scratchCountSuffixMarkedBoundaryPrefixGapCompactorConstruction_of_separatorMover
    (hpositioner :
      ScratchCountSuffixMarkedBoundarySeparatorMoverConstruction) :
    ScratchCountSuffixMarkedBoundaryPrefixGapCompactorConstruction := by
  rcases hpositioner with ⟨positioner, hpositionerSpec⟩
  exact
    ⟨positioner,
      scratchCountSuffixMarkedBoundaryPrefixGapCompactorSpec_of_separatorMover
        hpositionerSpec⟩

theorem scratchCountSuffixMarkedBoundaryPostGapTape_after_one_right_stable
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.move Direction.right
            (scratchCountSuffixMarkedBoundaryPostGapTape
              pref suffix first rightTail))) =
      Tape.move Direction.right
        (scratchCountSuffixMarkedBoundaryPostGapTape
          pref suffix first rightTail) := by
  cases suffix with
  | nil =>
      simp at hpos
  | cons bit rest =>
      cases hrev : (List.map some rest).reverse with
      | nil =>
          simp [scratchCountSuffixMarkedBoundaryPostGapTape,
            rightEdgeScanTargetTapeFromLeft, tapeAtCells, Tape.move,
            Tape.moveLeft, Tape.moveRight, hrev, List.reverse_cons,
            List.map_append]
      | cons cell tail =>
          simp [scratchCountSuffixMarkedBoundaryPostGapTape,
            rightEdgeScanTargetTapeFromLeft, tapeAtCells, Tape.move,
            Tape.moveLeft, Tape.moveRight, hrev, List.reverse_cons,
            List.map_append]

theorem scratchCountSuffixMarkedBoundaryPostGapTape_move_left_move_right
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixMarkedBoundaryPostGapTape
            pref suffix first rightTail)) =
      scratchCountSuffixMarkedBoundaryPostGapTape
        pref suffix first rightTail := by
  cases suffix with
  | nil =>
      simp at hpos
  | cons bit rest =>
      cases hrev : (List.map some rest).reverse with
      | nil =>
          simp [scratchCountSuffixMarkedBoundaryPostGapTape,
            rightEdgeScanTargetTapeFromLeft, tapeAtCells, Tape.move,
            Tape.moveLeft, Tape.moveRight, hrev, List.reverse_cons,
            List.map_append]
      | cons cell tail =>
          simp [scratchCountSuffixMarkedBoundaryPostGapTape,
            rightEdgeScanTargetTapeFromLeft, tapeAtCells, Tape.move,
            Tape.moveLeft, Tape.moveRight, hrev, List.reverse_cons,
            List.map_append]

theorem scratchCountSuffixMarkedBoundaryCleanupSourceTape_eq_move_right_right_postGap
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    Tape.move Direction.right
        (Tape.move Direction.right
          (scratchCountSuffixMarkedBoundaryPostGapTape
            pref suffix first rightTail)) =
      scratchCountSuffixMarkedBoundaryCleanupSourceTape
        pref suffix first rightTail := by
  cases suffix with
  | nil =>
      simp at hpos
  | cons bit rest =>
      cases hrev : (List.map some rest).reverse with
      | nil =>
          simp [scratchCountSuffixMarkedBoundaryPostGapTape,
            scratchCountSuffixMarkedBoundaryCleanupSourceTape,
            rightEdgeScanTargetTapeFromLeft, tapeAtCells, Tape.move,
            Tape.moveLeft, Tape.moveRight, hrev, List.reverse_cons,
            List.map_append]
      | cons cell tail =>
          simp [scratchCountSuffixMarkedBoundaryPostGapTape,
            scratchCountSuffixMarkedBoundaryCleanupSourceTape,
            rightEdgeScanTargetTapeFromLeft, tapeAtCells, Tape.move,
            Tape.moveLeft, Tape.moveRight, hrev, List.reverse_cons,
            List.map_append]

theorem scratchCountSuffixMarkedBoundaryPostGap_rightMoveTwice_haltsFrom
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    (canonicalSeqDescription
      rightMoveOnceDescription rightMoveOnceDescription).HaltsFromTape
      (scratchCountSuffixMarkedBoundaryPostGapTape
        pref suffix first rightTail)
      (scratchCountSuffixMarkedBoundaryCleanupSourceTape
        pref suffix first rightTail) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightMoveOnceDescription_subroutineReady
      rightMoveOnceDescription_subroutineReady
      (rightMoveOnceDescription_haltsFromTape
        (scratchCountSuffixMarkedBoundaryPostGapTape
          pref suffix first rightTail))
      (scratchCountSuffixMarkedBoundaryPostGapTape_after_one_right_stable
        pref suffix first rightTail hpos)
      (by
        rw [←
          scratchCountSuffixMarkedBoundaryCleanupSourceTape_eq_move_right_right_postGap
            pref suffix first rightTail hpos]
        exact
          rightMoveOnceDescription_haltsFromTape
            (Tape.move Direction.right
              (scratchCountSuffixMarkedBoundaryPostGapTape
                pref suffix first rightTail)))

theorem scratchCountSuffixMarkedBoundaryPreCleanupPositionerSpec_of_prefixGapCompactor
    {positioner : MachineDescription}
    (hpositioner :
      ScratchCountSuffixMarkedBoundaryPrefixGapCompactorSpec
        positioner) :
    ScratchCountSuffixMarkedBoundaryPreCleanupPositionerSpec
      (canonicalSeqDescription positioner
        (canonicalSeqDescription
          rightMoveOnceDescription rightMoveOnceDescription)) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hpositioner.left
        (canonicalSeqDescription_subroutineReady
          rightMoveOnceDescription_subroutineReady
          rightMoveOnceDescription_subroutineReady)
  · intro pref suffix first rightTail hpos
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hpositioner.left
        (canonicalSeqDescription_subroutineReady
          rightMoveOnceDescription_subroutineReady
          rightMoveOnceDescription_subroutineReady)
        (hpositioner.right pref suffix first rightTail hpos)
        (scratchCountSuffixMarkedBoundaryPostGapTape_move_left_move_right
          pref suffix first rightTail hpos)
        (scratchCountSuffixMarkedBoundaryPostGap_rightMoveTwice_haltsFrom
          pref suffix first rightTail hpos)

theorem scratchCountSuffixMarkedBoundaryPreCleanupPositionerConstruction_of_prefixGapCompactor
    (hpositioner :
      ScratchCountSuffixMarkedBoundaryPrefixGapCompactorConstruction) :
    ScratchCountSuffixMarkedBoundaryPreCleanupPositionerConstruction := by
  rcases hpositioner with ⟨positioner, hpositionerSpec⟩
  exact
    ⟨canonicalSeqDescription positioner
        (canonicalSeqDescription
          rightMoveOnceDescription rightMoveOnceDescription),
      scratchCountSuffixMarkedBoundaryPreCleanupPositionerSpec_of_prefixGapCompactor
        hpositionerSpec⟩

theorem scratchCountSuffixMarkedBoundaryCleanupSourceTape_move_left_move_right
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixMarkedBoundaryCleanupSourceTape
            pref suffix first rightTail)) =
      scratchCountSuffixMarkedBoundaryCleanupSourceTape
        pref suffix first rightTail := by
  cases hrep : List.replicate suffix.length (none : Option Bool) with
  | nil =>
      simp [scratchCountSuffixMarkedBoundaryCleanupSourceTape, hrep,
        tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons cell rest =>
      simp [scratchCountSuffixMarkedBoundaryCleanupSourceTape, hrep,
        tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem scratchCounterMarkerCleanupLeftDescription_haltsFrom_scratchCountSuffixMarkedBoundaryCleanupSourceTape
    (pref suffix : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    scratchCounterMarkerCleanupLeftDescription.HaltsFromTape
      (scratchCountSuffixMarkedBoundaryCleanupSourceTape
        pref suffix first rightTail)
      (scratchCountSuffixRestorerSourceTape pref suffix
        (some first :: rightTail)) := by
  have h :=
    scratchCounterMarkerCleanupLeftDescription_haltsFrom_withRight
      (pref.reverse.map some) suffix 0
      (List.append
        (List.replicate suffix.length (none : Option Bool))
        (some first :: rightTail))
  simpa [scratchCountSuffixMarkedBoundaryCleanupSourceTape,
    scratchCountSuffixRestorerSourceTape, List.replicate_succ,
    Nat.add_comm, List.append_assoc] using h

theorem scratchCountSuffixMarkedBoundaryPositionerSpec_of_preCleanupPositioner
    {positioner : MachineDescription}
    (hpositioner :
      ScratchCountSuffixMarkedBoundaryPreCleanupPositionerSpec
        positioner) :
    ScratchCountSuffixMarkedBoundaryPositionerSpec
      (canonicalSeqDescription positioner
        scratchCounterMarkerCleanupLeftDescription) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hpositioner.left
        scratchCounterMarkerCleanupLeftDescription_subroutineReady
  · intro pref suffix first rightTail hpos
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hpositioner.left
        scratchCounterMarkerCleanupLeftDescription_subroutineReady
        (hpositioner.right pref suffix first rightTail hpos)
        (scratchCountSuffixMarkedBoundaryCleanupSourceTape_move_left_move_right
          pref suffix first rightTail)
        (scratchCounterMarkerCleanupLeftDescription_haltsFrom_scratchCountSuffixMarkedBoundaryCleanupSourceTape
          pref suffix first rightTail)

theorem scratchCountSuffixMarkedBoundaryPositionerConstruction_of_preCleanupPositioner
    (hpositioner :
      ScratchCountSuffixMarkedBoundaryPreCleanupPositionerConstruction) :
    ScratchCountSuffixMarkedBoundaryPositionerConstruction := by
  rcases hpositioner with ⟨positioner, hpositionerSpec⟩
  exact
    ⟨canonicalSeqDescription positioner
        scratchCounterMarkerCleanupLeftDescription,
      scratchCountSuffixMarkedBoundaryPositionerSpec_of_preCleanupPositioner
        hpositionerSpec⟩

theorem scratchCountSuffixBoundaryPositionerSpec_of_markerInitAndPositioner
    {markerInit positioner : MachineDescription}
    (hmarkerInit : ScratchCountSuffixBoundaryMarkerInitSpec markerInit)
    (hpositioner :
      ScratchCountSuffixMarkedBoundaryPositionerSpec positioner) :
    ScratchCountSuffixBoundaryPositionerSpec
      (canonicalSeqDescription markerInit positioner) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        hmarkerInit.left hpositioner.left
  · intro pref suffix first rightTail hpos
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hmarkerInit.left
        hpositioner.left
        (by
          simpa [scratchCountSuffixBoundaryPositionerSourceTape] using
            hmarkerInit.right pref suffix (some first :: rightTail) hpos)
        rfl
        (hpositioner.right pref suffix first rightTail hpos)

theorem scratchCountSuffixBoundaryPositionerConstruction_of_markerInitAndPositioner
    (hmarkerInit : ScratchCountSuffixBoundaryMarkerInitConstruction)
    (hpositioner : ScratchCountSuffixMarkedBoundaryPositionerConstruction) :
    ScratchCountSuffixBoundaryPositionerConstruction := by
  rcases hmarkerInit with ⟨markerInit, hmarkerInitSpec⟩
  rcases hpositioner with ⟨positioner, hpositionerSpec⟩
  exact
    ⟨canonicalSeqDescription markerInit positioner,
      scratchCountSuffixBoundaryPositionerSpec_of_markerInitAndPositioner
        hmarkerInitSpec hpositionerSpec⟩

theorem scratchCountSuffixBoundaryMarkerInitConstruction_core :
    ScratchCountSuffixBoundaryMarkerInitConstruction := by
  exact
    ⟨rightSecondCellTrueMarkerDescription,
      rightSecondCellTrueMarkerDescription_subroutineReady,
      fun pref suffix rightTail _hpos =>
        rightSecondCellTrueMarkerDescription_haltsFromTape
          (scratchCountSuffixBoundaryPositionerSourceTape
            pref suffix rightTail)⟩

def scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
    (pref : Word Bool) (suffixFirst : Bool) (suffixRest : Word Bool)
    (first : Bool) (rightTail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (suffixRest.reverse.map some)
      (none :: none :: pref.reverse.map some))
    (none ::
      some true ::
      some suffixFirst ::
      List.append
        (List.replicate suffixRest.length (none : Option Bool))
        (some first :: rightTail))

def ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorSpec
    (locator : MachineDescription) : Prop :=
  locator.SubroutineReady ∧
    forall (pref suffixRest : Word Bool)
      (suffixFirst first : Bool) (rightTail : List (Option Bool)),
      locator.HaltsFromTape
        (scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape
          pref (suffixFirst :: suffixRest) first rightTail)
        (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
          pref (suffixFirst :: suffixRest) first rightTail)

def ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction :
    Prop :=
  exists locator : MachineDescription,
    ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorSpec locator

def ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherSpec
    (stasher : MachineDescription) : Prop :=
  stasher.SubroutineReady ∧
    forall (pref suffixRest : Word Bool)
      (suffixFirst first : Bool) (rightTail : List (Option Bool)),
      stasher.HaltsFromTape
        (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
          pref (suffixFirst :: suffixRest) first rightTail)
        (scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
          pref suffixFirst suffixRest first rightTail)

def ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherConstruction :
    Prop :=
  exists stasher : MachineDescription,
    ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherSpec
      stasher

def ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (pref suffixRest : Word Bool)
      (suffixFirst first : Bool) (rightTail : List (Option Bool)),
      eraser.HaltsFromTape
        (scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape
          pref (suffixFirst :: suffixRest) first rightTail)
        (scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
          pref suffixFirst suffixRest first rightTail)

def ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserSpec eraser

theorem scratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserSpec_of_locatorAndLocalStasher
    {locator stasher : MachineDescription}
    (hlocator :
      ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorSpec
        locator)
    (hstasher :
      ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherSpec
        stasher) :
    ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserSpec
      (canonicalSeqDescription locator stasher) := by
  constructor
  · exact canonicalSeqDescription_subroutineReady
      hlocator.left hstasher.left
  · intro pref suffixRest suffixFirst first rightTail
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        hlocator.left
        hstasher.left
        (hlocator.right pref suffixRest suffixFirst first rightTail)
        (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape_move_left_move_right
          pref (suffixFirst :: suffixRest) first rightTail (by simp))
        (hstasher.right pref suffixRest suffixFirst first rightTail)

theorem scratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction_of_locatorAndLocalStasher
    (hlocator :
      ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction)
    (hstasher :
      ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherConstruction) :
    ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction := by
  rcases hlocator with ⟨locator, hlocatorSpec⟩
  rcases hstasher with ⟨stasher, hstasherSpec⟩
  exact
    ⟨canonicalSeqDescription locator stasher,
      scratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserSpec_of_locatorAndLocalStasher
        hlocatorSpec hstasherSpec⟩

def ScratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall (pref suffixRest : Word Bool)
      (suffixFirst first : Bool) (rightTail : List (Option Bool)),
      restorer.HaltsFromTape
        (scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
          pref suffixFirst suffixRest first rightTail)
        (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
          pref (suffixFirst :: suffixRest) first rightTail)

def ScratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerConstruction :
    Prop :=
  exists restorer : MachineDescription,
    ScratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerSpec restorer

theorem scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape_move_left_move_right
    (pref suffixRest : Word Bool) (suffixFirst first : Bool)
    (rightTail : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
            pref suffixFirst suffixRest first rightTail)) =
      scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
        pref suffixFirst suffixRest first rightTail := by
  cases suffixRest <;>
    simp [scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape,
      tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
      List.replicate_succ]

theorem scratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterSpec_of_firstSuffixEraserAndRestorer
    {eraser restorer : MachineDescription}
    (heraser :
      ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserSpec eraser)
    (hrestorer :
      ScratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerSpec
        restorer) :
    ScratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterSpec
      (canonicalSeqDescription eraser restorer) := by
  constructor
  · exact canonicalSeqDescription_subroutineReady
      heraser.left hrestorer.left
  · intro pref suffix first rightTail hpos
    cases suffix with
    | nil =>
        simp at hpos
    | cons suffixFirst suffixRest =>
        exact
          canonicalSeqDescription_haltsFromTape_of_haltsFromTape
            heraser.left
            hrestorer.left
            (heraser.right pref suffixRest suffixFirst first rightTail)
            (scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape_move_left_move_right
              pref suffixRest suffixFirst first rightTail)
            (hrestorer.right pref suffixRest suffixFirst first rightTail)

theorem scratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction_of_firstSuffixEraserAndRestorer
    (heraser :
      ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction)
    (hrestorer :
      ScratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerConstruction) :
    ScratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction := by
  rcases heraser with ⟨eraser, heraserSpec⟩
  rcases hrestorer with ⟨restorer, hrestorerSpec⟩
  exact
    ⟨canonicalSeqDescription eraser restorer,
      scratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterSpec_of_firstSuffixEraserAndRestorer
        heraserSpec hrestorerSpec⟩

def firstSuffixLocalStasherSourceTape
    (left : List (Option Bool)) (suffixFirst : Bool)
    (suffixRest : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells left
    (some suffixFirst ::
      List.append (suffixRest.map some)
        (none ::
          some true ::
          none ::
          List.append
            (List.replicate suffixRest.length (none : Option Bool))
            tail))

def firstSuffixLocalStasherTargetTape
    (left : List (Option Bool)) (suffixFirst : Bool)
    (suffixRest : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.append (suffixRest.reverse.map some) (none :: left))
    (none ::
      some true ::
      some suffixFirst ::
      List.append
        (List.replicate suffixRest.length (none : Option Bool))
        tail)

def scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherDescription :
    MachineDescription where
  stateCount := 25
  start := 0
  halt := 24
  transitions :=
    [ transition 0 (some false) none Direction.right 10
    , transition 0 (some true) none Direction.right 20

    , transition 10 (some false) (some false) Direction.right 10
    , transition 10 (some true) (some true) Direction.right 10
    , transition 10 none none Direction.right 11
    , transition 11 (some true) (some true) Direction.right 12
    , transition 12 none (some false) Direction.left 13
    , transition 13 (some true) (some true) Direction.left 24

    , transition 20 (some false) (some false) Direction.right 20
    , transition 20 (some true) (some true) Direction.right 20
    , transition 20 none none Direction.right 21
    , transition 21 (some true) (some true) Direction.right 22
    , transition 22 none (some true) Direction.left 23
    , transition 23 (some true) (some true) Direction.left 24
    ]

private abbrev FirstSuffixLocalStasher :=
  scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherDescription

theorem firstSuffixLocalStasher_wellFormed :
    FirstSuffixLocalStasher.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := FirstSuffixLocalStasher.transitions)
      (stateCount := FirstSuffixLocalStasher.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := FirstSuffixLocalStasher.transitions)
      (by decide)

theorem firstSuffixLocalStasher_haltTransitionFree :
    FirstSuffixLocalStasher.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := FirstSuffixLocalStasher.transitions)
    (state := FirstSuffixLocalStasher.halt)
    (by decide)

theorem firstSuffixLocalStasher_subroutineReady :
    FirstSuffixLocalStasher.SubroutineReady :=
  ⟨firstSuffixLocalStasher_wellFormed,
    firstSuffixLocalStasher_haltTransitionFree⟩

theorem firstSuffixLocalStasher_run_scan_false
    (left : List (Option Bool)) (suffixRest : Word Bool)
    (right : List (Option Bool)) :
    FirstSuffixLocalStasher.runConfig suffixRest.length
        { state := 10
          tape :=
            tapeAtCells left
              (List.append (suffixRest.map some) right) } =
      { state := 10
        tape :=
          tapeAtCells
            (List.append (suffixRest.reverse.map some) left)
            right } := by
  induction suffixRest generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      change FirstSuffixLocalStasher.runConfig rest.length
          (FirstSuffixLocalStasher.runConfig 1
            { state := 10
              tape :=
                tapeAtCells left
                  (some bit :: List.append (rest.map some) right) }) =
        { state := 10
          tape :=
            tapeAtCells
              (List.append ((bit :: rest).reverse.map some) left)
              right }
      have hstep :
          FirstSuffixLocalStasher.runConfig 1
              { state := 10
                tape :=
                  tapeAtCells left
                    (some bit :: List.append (rest.map some) right) } =
            { state := 10
              tape :=
                tapeAtCells (some bit :: left)
                  (List.append (rest.map some) right) } := by
        cases bit <;>
          cases hright : List.append (List.map some rest) right <;>
            simp [FirstSuffixLocalStasher,
              scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherDescription,
              runConfig, stepConfig, lookupTransition, Matches,
              transition, Tape.read, Tape.write, Tape.move,
              Tape.moveRight, tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem firstSuffixLocalStasher_run_scan_true
    (left : List (Option Bool)) (suffixRest : Word Bool)
    (right : List (Option Bool)) :
    FirstSuffixLocalStasher.runConfig suffixRest.length
        { state := 20
          tape :=
            tapeAtCells left
              (List.append (suffixRest.map some) right) } =
      { state := 20
        tape :=
          tapeAtCells
            (List.append (suffixRest.reverse.map some) left)
            right } := by
  induction suffixRest generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [runConfig_add]
      change FirstSuffixLocalStasher.runConfig rest.length
          (FirstSuffixLocalStasher.runConfig 1
            { state := 20
              tape :=
                tapeAtCells left
                  (some bit :: List.append (rest.map some) right) }) =
        { state := 20
          tape :=
            tapeAtCells
              (List.append ((bit :: rest).reverse.map some) left)
              right }
      have hstep :
          FirstSuffixLocalStasher.runConfig 1
              { state := 20
                tape :=
                  tapeAtCells left
                    (some bit :: List.append (rest.map some) right) } =
            { state := 20
              tape :=
                tapeAtCells (some bit :: left)
                  (List.append (rest.map some) right) } := by
        cases bit <;>
          cases hright : List.append (List.map some rest) right <;>
            simp [FirstSuffixLocalStasher,
              scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherDescription,
              runConfig, stepConfig, lookupTransition, Matches,
              transition, Tape.read, Tape.write, Tape.move,
              Tape.moveRight, tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem firstSuffixLocalStasher_finish_false
    (left : List (Option Bool)) (suffixRest : Word Bool)
    (tail : List (Option Bool)) :
    FirstSuffixLocalStasher.runConfig 4
        { state := 10
          tape :=
            tapeAtCells
              (List.append (suffixRest.reverse.map some) (none :: left))
              (none ::
                some true ::
                none ::
                List.append
                  (List.replicate suffixRest.length (none : Option Bool))
                  tail) } =
      { state := FirstSuffixLocalStasher.halt
        tape :=
          firstSuffixLocalStasherTargetTape left false suffixRest tail } := by
  simp [FirstSuffixLocalStasher,
    scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherDescription,
    firstSuffixLocalStasherTargetTape, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight, Tape.moveLeft, tapeAtCells]

theorem firstSuffixLocalStasher_finish_true
    (left : List (Option Bool)) (suffixRest : Word Bool)
    (tail : List (Option Bool)) :
    FirstSuffixLocalStasher.runConfig 4
        { state := 20
          tape :=
            tapeAtCells
              (List.append (suffixRest.reverse.map some) (none :: left))
              (none ::
                some true ::
                none ::
                List.append
                  (List.replicate suffixRest.length (none : Option Bool))
                  tail) } =
      { state := FirstSuffixLocalStasher.halt
        tape :=
          firstSuffixLocalStasherTargetTape left true suffixRest tail } := by
  simp [FirstSuffixLocalStasher,
    scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherDescription,
    firstSuffixLocalStasherTargetTape, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight, Tape.moveLeft, tapeAtCells]

theorem firstSuffixLocalStasher_start_false
    (left : List (Option Bool)) (suffixRest : Word Bool)
    (tail : List (Option Bool)) :
    FirstSuffixLocalStasher.runConfig 1
        { state := FirstSuffixLocalStasher.start
          tape :=
            firstSuffixLocalStasherSourceTape
              left false suffixRest tail } =
      { state := 10
        tape :=
          tapeAtCells (none :: left)
            (List.append (suffixRest.map some)
              (none ::
                some true ::
                none ::
                List.append
                  (List.replicate suffixRest.length (none : Option Bool))
                  tail)) } := by
  simp [FirstSuffixLocalStasher,
    scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherDescription,
    firstSuffixLocalStasherSourceTape, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight, tapeAtCells]
  cases List.map some suffixRest ++
    none ::
      some true ::
      none ::
      (List.replicate suffixRest.length (none : Option Bool) ++ tail) <;>
    simp

theorem firstSuffixLocalStasher_start_true
    (left : List (Option Bool)) (suffixRest : Word Bool)
    (tail : List (Option Bool)) :
    FirstSuffixLocalStasher.runConfig 1
        { state := FirstSuffixLocalStasher.start
          tape :=
            firstSuffixLocalStasherSourceTape
              left true suffixRest tail } =
      { state := 20
        tape :=
          tapeAtCells (none :: left)
            (List.append (suffixRest.map some)
              (none ::
                some true ::
                none ::
                List.append
                  (List.replicate suffixRest.length (none : Option Bool))
                  tail)) } := by
  simp [FirstSuffixLocalStasher,
    scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherDescription,
    firstSuffixLocalStasherSourceTape, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight, tapeAtCells]
  cases List.map some suffixRest ++
    none ::
      some true ::
      none ::
      (List.replicate suffixRest.length (none : Option Bool) ++ tail) <;>
    simp

theorem firstSuffixLocalStasher_run_false
    (left : List (Option Bool)) (suffixRest : Word Bool)
    (tail : List (Option Bool)) :
    FirstSuffixLocalStasher.runConfig (suffixRest.length + 5)
        { state := FirstSuffixLocalStasher.start
          tape :=
            firstSuffixLocalStasherSourceTape
              left false suffixRest tail } =
      { state := FirstSuffixLocalStasher.halt
        tape :=
          firstSuffixLocalStasherTargetTape
            left false suffixRest tail } := by
  rw [show suffixRest.length + 5 = 1 + (suffixRest.length + 4) by lia,
    runConfig_add]
  rw [firstSuffixLocalStasher_start_false]
  rw [show suffixRest.length + 4 = suffixRest.length + 4 by rfl,
    runConfig_add]
  rw [firstSuffixLocalStasher_run_scan_false]
  exact firstSuffixLocalStasher_finish_false left suffixRest tail

theorem firstSuffixLocalStasher_run_true
    (left : List (Option Bool)) (suffixRest : Word Bool)
    (tail : List (Option Bool)) :
    FirstSuffixLocalStasher.runConfig (suffixRest.length + 5)
        { state := FirstSuffixLocalStasher.start
          tape :=
            firstSuffixLocalStasherSourceTape
              left true suffixRest tail } =
      { state := FirstSuffixLocalStasher.halt
        tape :=
          firstSuffixLocalStasherTargetTape
            left true suffixRest tail } := by
  rw [show suffixRest.length + 5 = 1 + (suffixRest.length + 4) by lia,
    runConfig_add]
  rw [firstSuffixLocalStasher_start_true]
  rw [show suffixRest.length + 4 = suffixRest.length + 4 by rfl,
    runConfig_add]
  rw [firstSuffixLocalStasher_run_scan_true]
  exact firstSuffixLocalStasher_finish_true left suffixRest tail

theorem firstSuffixLocalStasher_run
    (left : List (Option Bool)) (suffixFirst : Bool)
    (suffixRest : Word Bool) (tail : List (Option Bool)) :
    FirstSuffixLocalStasher.runConfig (suffixRest.length + 5)
        { state := FirstSuffixLocalStasher.start
          tape :=
            firstSuffixLocalStasherSourceTape
              left suffixFirst suffixRest tail } =
      { state := FirstSuffixLocalStasher.halt
        tape :=
          firstSuffixLocalStasherTargetTape
            left suffixFirst suffixRest tail } := by
  cases suffixFirst <;>
    simp [firstSuffixLocalStasher_run_false,
      firstSuffixLocalStasher_run_true]

theorem firstSuffixLocalStasher_haltsFromTape
    (left : List (Option Bool)) (suffixFirst : Bool)
    (suffixRest : Word Bool) (tail : List (Option Bool)) :
    FirstSuffixLocalStasher.HaltsFromTape
      (firstSuffixLocalStasherSourceTape
        left suffixFirst suffixRest tail)
      (firstSuffixLocalStasherTargetTape
        left suffixFirst suffixRest tail) := by
  refine ⟨suffixRest.length + 5, ?_⟩
  constructor <;>
    rw [firstSuffixLocalStasher_run]

theorem firstSuffixLocalStasher_haltsFrom_scanSourceTape
    (pref suffixRest : Word Bool) (suffixFirst first : Bool)
    (rightTail : List (Option Bool)) :
    FirstSuffixLocalStasher.HaltsFromTape
      (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
        pref (suffixFirst :: suffixRest) first rightTail)
      (scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
        pref suffixFirst suffixRest first rightTail) := by
  simpa [scratchCountSuffixMarkedBoundarySeparatorScanSourceTape,
    scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape,
    scratchCountSuffixMarkedBoundarySeparatorPadding,
    rightEdgeScanSourceTapeFromLeft,
    firstSuffixLocalStasherSourceTape,
    firstSuffixLocalStasherTargetTape,
    List.map_append, List.reverse_cons, List.replicate_succ,
    List.append_assoc] using
    firstSuffixLocalStasher_haltsFromTape
      (none :: pref.reverse.map some) suffixFirst suffixRest
      (some first :: rightTail)

theorem scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape_empty_singleton_eq_scanSourceTape
    (suffixFirst first : Bool) (rightTail : List (Option Bool)) :
    scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape
        [] [suffixFirst] first rightTail =
      scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
        [] [suffixFirst] first rightTail := by
  simp [scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape,
    scratchCountSuffixMarkedBoundarySeparatorScanSourceTape,
    scratchCountSuffixMarkedBoundarySeparatorPadding,
    rightEdgeScanTargetTapeFromLeft,
    rightEdgeScanSourceTapeFromLeft,
    tapeAtCells, Tape.move, Tape.moveLeft]

theorem scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocator_haltsFrom_empty_singleton
    (suffixFirst first : Bool)
    (rightTail : List (Option Bool)) :
    ExactIdentityDescription.HaltsFromTape
      (scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape
        [] [suffixFirst] first rightTail)
      (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
        [] [suffixFirst] first rightTail) := by
  rw [
    scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape_empty_singleton_eq_scanSourceTape]
  exact
    CommonGround.Identity.exactIdentityDescription_haltsFromTape
      (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
        [] [suffixFirst] first rightTail)

theorem scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction_of_countedSuffixBoundaryLocator
    (hlocator : CountedSuffixBoundaryLocatorConstruction) :
    ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction := by
  rcases hlocator with ⟨locator, hlocatorSpec⟩
  exact
    ⟨locator,
      hlocatorSpec.left,
      fun pref suffixRest suffixFirst first rightTail => by
        simpa [scratchCountSuffixMarkedBoundarySeparatorRightEdgeTape,
          scratchCountSuffixMarkedBoundarySeparatorScanSourceTape,
          scratchCountSuffixMarkedBoundarySeparatorPadding,
          countedSuffixBoundaryLocatorSourceTape,
          countedSuffixBoundaryLocatorTargetTape,
          countedSuffixBoundaryLocatorPadding] using
          hlocatorSpec.right pref suffixRest suffixFirst (some true)
            (some first :: rightTail)⟩

theorem scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction_core :
    ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction :=
  scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction_of_countedSuffixBoundaryLocator
    countedSuffixBoundaryLocatorConstruction_core

theorem scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherConstruction_core :
    ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherConstruction := by
  exact
    ⟨FirstSuffixLocalStasher,
      firstSuffixLocalStasher_subroutineReady,
      firstSuffixLocalStasher_haltsFrom_scanSourceTape⟩

theorem scratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction_of_locator
    (hlocator :
      ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction) :
    ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction :=
  scratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction_of_locatorAndLocalStasher
    hlocator
    scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocalStasherConstruction_core

theorem scratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction_core :
    ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction :=
  scratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction_of_locator
    scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction_core

def scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription :
    MachineDescription where
  stateCount := 25
  start := 0
  halt := 24
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 (some true) (some true) Direction.right 2

    , transition 2 (some false) none Direction.left 10
    , transition 2 (some true) none Direction.left 20

    , transition 10 (some true) (some true) Direction.left 11
    , transition 11 none none Direction.left 12
    , transition 12 (some false) (some false) Direction.left 12
    , transition 12 (some true) (some true) Direction.left 12
    , transition 12 none (some false) Direction.right 13
    , transition 13 none none Direction.left 24
    , transition 13 (some false) (some false) Direction.left 24
    , transition 13 (some true) (some true) Direction.left 24

    , transition 20 (some true) (some true) Direction.left 21
    , transition 21 none none Direction.left 22
    , transition 22 (some false) (some false) Direction.left 22
    , transition 22 (some true) (some true) Direction.left 22
    , transition 22 none (some true) Direction.right 23
    , transition 23 none none Direction.left 24
    , transition 23 (some false) (some false) Direction.left 24
    , transition 23 (some true) (some true) Direction.left 24
    ]

private abbrev PrefixGapRestorer :=
  scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription

theorem prefixGapRestorer_wellFormed :
    PrefixGapRestorer.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := PrefixGapRestorer.transitions)
      (stateCount := PrefixGapRestorer.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := PrefixGapRestorer.transitions)
      (by decide)

theorem prefixGapRestorer_haltTransitionFree :
    PrefixGapRestorer.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := PrefixGapRestorer.transitions)
    (state := PrefixGapRestorer.halt)
    (by decide)

theorem prefixGapRestorer_subroutineReady :
    PrefixGapRestorer.SubroutineReady :=
  ⟨prefixGapRestorer_wellFormed,
    prefixGapRestorer_haltTransitionFree⟩

def prefixGapRestorerAfterFetchTape
    (pref suffixRest : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (suffixRest.reverse.map some)
      (none :: none :: pref.reverse.map some))
    (none ::
      some true ::
      none ::
      List.append
        (List.replicate suffixRest.length (none : Option Bool))
        (some first :: rightTail))

theorem prefixGapRestorer_run_fetch_false
    (pref suffixRest : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    PrefixGapRestorer.runConfig 4
        { state := PrefixGapRestorer.start
          tape :=
            scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
              pref false suffixRest first rightTail } =
      { state := 11
        tape := prefixGapRestorerAfterFetchTape
          pref suffixRest first rightTail } := by
  simp [PrefixGapRestorer,
    scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
    scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape,
    prefixGapRestorerAfterFetchTape, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

theorem prefixGapRestorer_run_fetch_true
    (pref suffixRest : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    PrefixGapRestorer.runConfig 4
        { state := PrefixGapRestorer.start
          tape :=
            scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
              pref true suffixRest first rightTail } =
      { state := 21
        tape := prefixGapRestorerAfterFetchTape
          pref suffixRest first rightTail } := by
  simp [PrefixGapRestorer,
    scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
    scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape,
    prefixGapRestorerAfterFetchTape, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

theorem prefixGapRestorer_run_boundary_false
    (baseLeft : List (Option Bool)) (next : Option Bool)
    (rightCells : List (Option Bool)) :
    PrefixGapRestorer.runConfig 2
        { state := 12
          tape := tapeAtCells baseLeft (none :: next :: rightCells) } =
      { state := PrefixGapRestorer.halt
        tape := tapeAtCells baseLeft (some false :: next :: rightCells) } := by
  cases next with
  | none =>
      simp [PrefixGapRestorer,
        scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
        tapeAtCells]
  | some bit =>
      cases bit <;>
        simp [PrefixGapRestorer,
          scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          tapeAtCells]

theorem prefixGapRestorer_run_scan_false
    (baseLeft : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightCells : List (Option Bool)) :
    PrefixGapRestorer.runConfig (leftStack.length + 3)
        { state := 12
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: baseLeft))
              (some current :: rightCells) } =
      { state := PrefixGapRestorer.halt
        tape :=
          tapeAtCells baseLeft
            (some false ::
              List.append (leftStack.reverse.map some)
                (some current :: rightCells)) } := by
  induction leftStack generalizing current rightCells with
  | nil =>
      change PrefixGapRestorer.runConfig (1 + 2)
          { state := 12
            tape :=
              tapeAtCells (List.append ([] : List (Option Bool))
                (none :: baseLeft)) (some current :: rightCells) } =
        { state := PrefixGapRestorer.halt
          tape :=
            tapeAtCells baseLeft
              (some false ::
                List.append (([] : Word Bool).reverse.map some)
                  (some current :: rightCells)) }
      rw [runConfig_add]
      have hstep :
          PrefixGapRestorer.runConfig 1
              { state := 12
                tape :=
                  tapeAtCells (List.append ([] : List (Option Bool))
                    (none :: baseLeft)) (some current :: rightCells) } =
            { state := 12
              tape := tapeAtCells baseLeft
                (none :: some current :: rightCells) } := by
        cases current <;>
          simp [PrefixGapRestorer,
            scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            tapeAtCells]
      rw [hstep]
      simpa using
        prefixGapRestorer_run_boundary_false
          baseLeft (some current) rightCells
  | cons next rest ih =>
      rw [show (next :: rest).length + 3 =
        1 + (rest.length + 3) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          PrefixGapRestorer.runConfig 1
              { state := 12
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some)
                      (none :: baseLeft))
                    (some current :: rightCells) } =
            { state := 12
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some next :: some current :: rightCells) } := by
        cases current <;> cases next <;>
          simp [PrefixGapRestorer,
            scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: rightCells)

theorem prefixGapRestorer_run_restore_false_from_leftStack
    (baseLeft : List (Option Bool)) (leftStack : Word Bool)
    (rightCells : List (Option Bool)) :
    PrefixGapRestorer.runConfig (leftStack.length + 3)
        { state := 11
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: baseLeft))
              (none :: rightCells) } =
      { state := PrefixGapRestorer.halt
        tape :=
          tapeAtCells baseLeft
            (some false ::
              List.append (leftStack.reverse.map some)
                (none :: rightCells)) } := by
  cases leftStack with
  | nil =>
      change PrefixGapRestorer.runConfig (1 + 2)
          { state := 11
            tape :=
              tapeAtCells (List.append ([] : List (Option Bool))
                (none :: baseLeft)) (none :: rightCells) } =
        { state := PrefixGapRestorer.halt
          tape :=
            tapeAtCells baseLeft
              (some false ::
                List.append (([] : Word Bool).reverse.map some)
                  (none :: rightCells)) }
      rw [runConfig_add]
      have hstep :
          PrefixGapRestorer.runConfig 1
              { state := 11
                tape :=
                  tapeAtCells (List.append ([] : List (Option Bool))
                    (none :: baseLeft)) (none :: rightCells) } =
            { state := 12
              tape := tapeAtCells baseLeft (none :: none :: rightCells) } := by
        simp [PrefixGapRestorer,
          scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
      rw [hstep]
      simpa using
        prefixGapRestorer_run_boundary_false
          baseLeft none rightCells
  | cons current rest =>
      rw [show (current :: rest).length + 3 =
        1 + (rest.length + 3) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          PrefixGapRestorer.runConfig 1
              { state := 11
                tape :=
                  tapeAtCells
                    (List.append ((current :: rest).map some)
                      (none :: baseLeft))
                    (none :: rightCells) } =
            { state := 12
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some current :: none :: rightCells) } := by
        cases current <;>
          simp [PrefixGapRestorer,
            scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        prefixGapRestorer_run_scan_false
          baseLeft rest current (none :: rightCells)

theorem prefixGapRestorer_restoreFromFetched_false
    (pref suffixRest : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    exists n : Nat,
      (PrefixGapRestorer.runConfig n
          { state := 11
            tape := prefixGapRestorerAfterFetchTape
              pref suffixRest first rightTail }).state =
        PrefixGapRestorer.halt ∧
      (PrefixGapRestorer.runConfig n
          { state := 11
            tape := prefixGapRestorerAfterFetchTape
              pref suffixRest first rightTail }).tape =
        scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
          pref (false :: suffixRest) first rightTail := by
  refine ⟨suffixRest.length + 3, ?_⟩
  constructor
  · rw [prefixGapRestorerAfterFetchTape]
    simpa using
      congrArg MachineDescription.Configuration.state
        (prefixGapRestorer_run_restore_false_from_leftStack
          (none :: pref.reverse.map some)
          suffixRest.reverse
          (some true ::
            none ::
            List.append
              (List.replicate suffixRest.length (none : Option Bool))
              (some first :: rightTail)))
  · rw [prefixGapRestorerAfterFetchTape]
    simpa [scratchCountSuffixMarkedBoundarySeparatorScanSourceTape,
      scratchCountSuffixMarkedBoundarySeparatorPadding,
      rightEdgeScanSourceTapeFromLeft, List.map_reverse,
      List.append_assoc] using
      congrArg MachineDescription.Configuration.tape
        (prefixGapRestorer_run_restore_false_from_leftStack
          (none :: pref.reverse.map some)
          suffixRest.reverse
          (some true ::
            none ::
            List.append
              (List.replicate suffixRest.length (none : Option Bool))
              (some first :: rightTail)))

theorem prefixGapRestorer_run_boundary_true
    (baseLeft : List (Option Bool)) (next : Option Bool)
    (rightCells : List (Option Bool)) :
    PrefixGapRestorer.runConfig 2
        { state := 22
          tape := tapeAtCells baseLeft (none :: next :: rightCells) } =
      { state := PrefixGapRestorer.halt
        tape := tapeAtCells baseLeft (some true :: next :: rightCells) } := by
  cases next with
  | none =>
      simp [PrefixGapRestorer,
        scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
        tapeAtCells]
  | some bit =>
      cases bit <;>
        simp [PrefixGapRestorer,
          scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          tapeAtCells]

theorem prefixGapRestorer_run_scan_true
    (baseLeft : List (Option Bool)) (leftStack : Word Bool)
    (current : Bool) (rightCells : List (Option Bool)) :
    PrefixGapRestorer.runConfig (leftStack.length + 3)
        { state := 22
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: baseLeft))
              (some current :: rightCells) } =
      { state := PrefixGapRestorer.halt
        tape :=
          tapeAtCells baseLeft
            (some true ::
              List.append (leftStack.reverse.map some)
                (some current :: rightCells)) } := by
  induction leftStack generalizing current rightCells with
  | nil =>
      change PrefixGapRestorer.runConfig (1 + 2)
          { state := 22
            tape :=
              tapeAtCells (List.append ([] : List (Option Bool))
                (none :: baseLeft)) (some current :: rightCells) } =
        { state := PrefixGapRestorer.halt
          tape :=
            tapeAtCells baseLeft
              (some true ::
                List.append (([] : Word Bool).reverse.map some)
                  (some current :: rightCells)) }
      rw [runConfig_add]
      have hstep :
          PrefixGapRestorer.runConfig 1
              { state := 22
                tape :=
                  tapeAtCells (List.append ([] : List (Option Bool))
                    (none :: baseLeft)) (some current :: rightCells) } =
            { state := 22
              tape := tapeAtCells baseLeft
                (none :: some current :: rightCells) } := by
        cases current <;>
          simp [PrefixGapRestorer,
            scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            tapeAtCells]
      rw [hstep]
      simpa using
        prefixGapRestorer_run_boundary_true
          baseLeft (some current) rightCells
  | cons next rest ih =>
      rw [show (next :: rest).length + 3 =
        1 + (rest.length + 3) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          PrefixGapRestorer.runConfig 1
              { state := 22
                tape :=
                  tapeAtCells
                    (List.append ((next :: rest).map some)
                      (none :: baseLeft))
                    (some current :: rightCells) } =
            { state := 22
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some next :: some current :: rightCells) } := by
        cases current <;> cases next <;>
          simp [PrefixGapRestorer,
            scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (some current :: rightCells)

theorem prefixGapRestorer_run_restore_true_from_leftStack
    (baseLeft : List (Option Bool)) (leftStack : Word Bool)
    (rightCells : List (Option Bool)) :
    PrefixGapRestorer.runConfig (leftStack.length + 3)
        { state := 21
          tape :=
            tapeAtCells
              (List.append (leftStack.map some) (none :: baseLeft))
              (none :: rightCells) } =
      { state := PrefixGapRestorer.halt
        tape :=
          tapeAtCells baseLeft
            (some true ::
              List.append (leftStack.reverse.map some)
                (none :: rightCells)) } := by
  cases leftStack with
  | nil =>
      change PrefixGapRestorer.runConfig (1 + 2)
          { state := 21
            tape :=
              tapeAtCells (List.append ([] : List (Option Bool))
                (none :: baseLeft)) (none :: rightCells) } =
        { state := PrefixGapRestorer.halt
          tape :=
            tapeAtCells baseLeft
              (some true ::
                List.append (([] : Word Bool).reverse.map some)
                  (none :: rightCells)) }
      rw [runConfig_add]
      have hstep :
          PrefixGapRestorer.runConfig 1
              { state := 21
                tape :=
                  tapeAtCells (List.append ([] : List (Option Bool))
                    (none :: baseLeft)) (none :: rightCells) } =
            { state := 22
              tape := tapeAtCells baseLeft (none :: none :: rightCells) } := by
        simp [PrefixGapRestorer,
          scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]
      rw [hstep]
      simpa using
        prefixGapRestorer_run_boundary_true
          baseLeft none rightCells
  | cons current rest =>
      rw [show (current :: rest).length + 3 =
        1 + (rest.length + 3) by
        simp
        lia]
      rw [runConfig_add]
      have hstep :
          PrefixGapRestorer.runConfig 1
              { state := 21
                tape :=
                  tapeAtCells
                    (List.append ((current :: rest).map some)
                      (none :: baseLeft))
                    (none :: rightCells) } =
            { state := 22
              tape :=
                tapeAtCells
                  (List.append (rest.map some) (none :: baseLeft))
                  (some current :: none :: rightCells) } := by
        cases current <;>
          simp [PrefixGapRestorer,
            scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            tapeAtCells]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        prefixGapRestorer_run_scan_true
          baseLeft rest current (none :: rightCells)

theorem prefixGapRestorer_restoreFromFetched_true
    (pref suffixRest : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    exists n : Nat,
      (PrefixGapRestorer.runConfig n
          { state := 21
            tape := prefixGapRestorerAfterFetchTape
              pref suffixRest first rightTail }).state =
        PrefixGapRestorer.halt ∧
      (PrefixGapRestorer.runConfig n
          { state := 21
            tape := prefixGapRestorerAfterFetchTape
              pref suffixRest first rightTail }).tape =
        scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
          pref (true :: suffixRest) first rightTail := by
  refine ⟨suffixRest.length + 3, ?_⟩
  constructor
  · rw [prefixGapRestorerAfterFetchTape]
    simpa using
      congrArg MachineDescription.Configuration.state
        (prefixGapRestorer_run_restore_true_from_leftStack
          (none :: pref.reverse.map some)
          suffixRest.reverse
          (some true ::
            none ::
            List.append
              (List.replicate suffixRest.length (none : Option Bool))
              (some first :: rightTail)))
  · rw [prefixGapRestorerAfterFetchTape]
    simpa [scratchCountSuffixMarkedBoundarySeparatorScanSourceTape,
      scratchCountSuffixMarkedBoundarySeparatorPadding,
      rightEdgeScanSourceTapeFromLeft, List.map_reverse,
      List.append_assoc] using
      congrArg MachineDescription.Configuration.tape
        (prefixGapRestorer_run_restore_true_from_leftStack
          (none :: pref.reverse.map some)
          suffixRest.reverse
          (some true ::
            none ::
            List.append
              (List.replicate suffixRest.length (none : Option Bool))
              (some first :: rightTail)))

theorem prefixGapRestorer_haltsFrom_firstSuffixErasedTape_false
    (pref suffixRest : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    PrefixGapRestorer.HaltsFromTape
      (scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
        pref false suffixRest first rightTail)
      (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
        pref (false :: suffixRest) first rightTail) := by
  rcases prefixGapRestorer_restoreFromFetched_false
      pref suffixRest first rightTail with
    ⟨n, hn⟩
  refine ⟨4 + n, ?_⟩
  constructor
  · rw [runConfig_add]
    rw [prefixGapRestorer_run_fetch_false]
    exact hn.left
  · rw [runConfig_add]
    rw [prefixGapRestorer_run_fetch_false]
    exact hn.right

theorem prefixGapRestorer_haltsFrom_firstSuffixErasedTape_true
    (pref suffixRest : Word Bool) (first : Bool)
    (rightTail : List (Option Bool)) :
    PrefixGapRestorer.HaltsFromTape
      (scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
        pref true suffixRest first rightTail)
      (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
        pref (true :: suffixRest) first rightTail) := by
  rcases prefixGapRestorer_restoreFromFetched_true
      pref suffixRest first rightTail with
    ⟨n, hn⟩
  refine ⟨4 + n, ?_⟩
  constructor
  · rw [runConfig_add]
    rw [prefixGapRestorer_run_fetch_true]
    exact hn.left
  · rw [runConfig_add]
    rw [prefixGapRestorer_run_fetch_true]
    exact hn.right

theorem prefixGapRestorer_haltsFrom_firstSuffixErasedTape
    (pref suffixRest : Word Bool) (suffixFirst first : Bool)
    (rightTail : List (Option Bool)) :
    PrefixGapRestorer.HaltsFromTape
      (scratchCountSuffixMarkedBoundarySeparatorFirstSuffixErasedTape
        pref suffixFirst suffixRest first rightTail)
      (scratchCountSuffixMarkedBoundarySeparatorScanSourceTape
        pref (suffixFirst :: suffixRest) first rightTail) := by
  cases suffixFirst
  · exact
      prefixGapRestorer_haltsFrom_firstSuffixErasedTape_false
        pref suffixRest first rightTail
  · exact
      prefixGapRestorer_haltsFrom_firstSuffixErasedTape_true
        pref suffixRest first rightTail

theorem scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerConstruction_core :
    ScratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerConstruction := by
  exact
    ⟨PrefixGapRestorer,
      prefixGapRestorer_subroutineReady,
      prefixGapRestorer_haltsFrom_firstSuffixErasedTape⟩

theorem scratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction_of_locator
    (hlocator :
      ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction) :
    ScratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction := by
  exact
    scratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction_of_firstSuffixEraserAndRestorer
      (scratchCountSuffixMarkedBoundarySeparatorFirstSuffixEraserConstruction_of_locator
        hlocator)
      scratchCountSuffixMarkedBoundarySeparatorPrefixGapRestorerConstruction_core

theorem scratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction_core :
    ScratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction := by
  exact
    scratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction_of_locator
      scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction_core

theorem scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterConstruction_core :
    ScratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterConstruction :=
  scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterConstruction_of_rightEdgeShifter
    scratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction_core

theorem scratchCountSuffixMarkedBoundarySeparatorMoverConstruction_core :
    ScratchCountSuffixMarkedBoundarySeparatorMoverConstruction :=
  scratchCountSuffixMarkedBoundarySeparatorMoverConstruction_of_leftBoundaryShifter
    scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterConstruction_core

theorem scratchCountSuffixMarkedBoundaryPrefixGapCompactorConstruction_core :
    ScratchCountSuffixMarkedBoundaryPrefixGapCompactorConstruction :=
  scratchCountSuffixMarkedBoundaryPrefixGapCompactorConstruction_of_separatorMover
    scratchCountSuffixMarkedBoundarySeparatorMoverConstruction_core

theorem scratchCountSuffixMarkedBoundaryPreCleanupPositionerConstruction_core :
    ScratchCountSuffixMarkedBoundaryPreCleanupPositionerConstruction :=
  scratchCountSuffixMarkedBoundaryPreCleanupPositionerConstruction_of_prefixGapCompactor
    scratchCountSuffixMarkedBoundaryPrefixGapCompactorConstruction_core

theorem scratchCountSuffixMarkedBoundaryPositionerConstruction_core :
    ScratchCountSuffixMarkedBoundaryPositionerConstruction :=
  scratchCountSuffixMarkedBoundaryPositionerConstruction_of_preCleanupPositioner
    scratchCountSuffixMarkedBoundaryPreCleanupPositionerConstruction_core

theorem scratchCountSuffixPositionerRightEdgeScan_haltsFrom
    (pref suffix : Word Bool) (rightTail : List (Option Bool))
    (hpos : 0 < suffix.length) :
    rightEdgeScanDescription.HaltsFromTape
      (Tape.move Direction.right
        (scratchCountSuffixPositionerSourceTape pref suffix rightTail))
      (scratchCountSuffixPositionerRightEdgeTape pref suffix rightTail) := by
  cases hbits : List.append pref suffix with
  | nil =>
      simp at hbits
      rcases hbits with ⟨_hpref, hsuffix⟩
      simp [hsuffix] at hpos
  | cons first rest =>
      rw [scratchCountSuffixPositionerRightEdgeTape, hbits]
      let padding : List (Option Bool) :=
        none ::
          List.append
            (List.replicate suffix.length (none : Option Bool))
            rightTail
      have hsource :
          Tape.move Direction.right
            (scratchCountSuffixPositionerSourceTape
              pref suffix rightTail) =
            rightEdgeScanSourceTapeFromLeft
              (some first :: [none]) rest padding := by
        have hcells :
            List.append (pref.map some)
              (List.append (suffix.map some) (none :: padding)) =
              some first ::
                List.append (rest.map some) (none :: padding) := by
          simpa [List.map_append, List.append_assoc] using
            congrArg
              (fun xs : Word Bool =>
                List.append (xs.map some) (none :: padding))
              hbits
        rw [scratchCountSuffixPositionerSourceTape,
          rightEdgeScanSourceTapeFromLeft]
        rw [show none ::
            List.append
              (List.replicate suffix.length (none : Option Bool))
              rightTail = padding by rfl]
        rw [hcells]
        cases List.append (rest.map some) (none :: padding) <;> rfl
      rw [hsource]
      exact
        rightEdgeScanDescription_haltsFromTape
          (some first :: [none]) rest padding

theorem scratchCountSuffixPositionerHandoffSpec_of_boundaryPositioner
    {positioner : MachineDescription}
    (hpositioner : ScratchCountSuffixBoundaryPositionerSpec positioner) :
    ScratchCountSuffixPositionerHandoffSpec
      (canonicalSeqDescription rightEdgeScanDescription positioner) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        rightEdgeScanDescription_subroutineReady hpositioner.left
  · intro pref suffix first rightTail hpos
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        rightEdgeScanDescription_subroutineReady
        hpositioner.left
        (scratchCountSuffixPositionerRightEdgeScan_haltsFrom
          pref suffix (some first :: rightTail) hpos)
        rfl
        (hpositioner.right pref suffix first rightTail hpos)

theorem scratchCountSuffixPositionerHandoffConstruction_of_boundaryPositioner
    (hpositioner : ScratchCountSuffixBoundaryPositionerConstruction) :
    ScratchCountSuffixPositionerHandoffConstruction := by
  rcases hpositioner with ⟨positioner, hpositionerSpec⟩
  exact
    ⟨canonicalSeqDescription rightEdgeScanDescription positioner,
      scratchCountSuffixPositionerHandoffSpec_of_boundaryPositioner
        hpositionerSpec⟩

theorem scratchCountSuffixBoundaryPositionerConstruction_core :
    ScratchCountSuffixBoundaryPositionerConstruction :=
  scratchCountSuffixBoundaryPositionerConstruction_of_markerInitAndPositioner
    scratchCountSuffixBoundaryMarkerInitConstruction_core
    scratchCountSuffixMarkedBoundaryPositionerConstruction_core

theorem scratchCountSuffixPositionerHandoffConstruction_of_firstSuffixLocator
    (hlocator :
      ScratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction) :
    ScratchCountSuffixPositionerHandoffConstruction :=
  scratchCountSuffixPositionerHandoffConstruction_of_boundaryPositioner
    (scratchCountSuffixBoundaryPositionerConstruction_of_markerInitAndPositioner
      scratchCountSuffixBoundaryMarkerInitConstruction_core
      (scratchCountSuffixMarkedBoundaryPositionerConstruction_of_preCleanupPositioner
        (scratchCountSuffixMarkedBoundaryPreCleanupPositionerConstruction_of_prefixGapCompactor
          (scratchCountSuffixMarkedBoundaryPrefixGapCompactorConstruction_of_separatorMover
            (scratchCountSuffixMarkedBoundarySeparatorMoverConstruction_of_leftBoundaryShifter
              (scratchCountSuffixMarkedBoundarySeparatorLeftBoundaryShifterConstruction_of_rightEdgeShifter
                (scratchCountSuffixMarkedBoundarySeparatorRightEdgeShifterConstruction_of_locator
                  hlocator)))))))

theorem scratchCountSuffixPositionerHandoffConstruction_core :
    ScratchCountSuffixPositionerHandoffConstruction :=
  scratchCountSuffixPositionerHandoffConstruction_of_firstSuffixLocator
    scratchCountSuffixMarkedBoundarySeparatorFirstSuffixLocatorConstruction_core

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
