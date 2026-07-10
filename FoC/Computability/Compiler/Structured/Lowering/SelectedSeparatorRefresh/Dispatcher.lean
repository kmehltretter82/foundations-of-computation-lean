import FoC.Computability.Compiler.Structured.Lowering.SelectedSeparatorRefresh.Core

set_option doc.verso true

/-!
# Selected-shape refresh dispatcher

Dispatcher branch layout for selected-separator refresh cases.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## Selected-shape dispatcher branch layout
-/

def selectedShapeRefreshFinalHalt : Nat :=
  2

def selectedShapeLeftRepairOffset : Nat :=
  3

def selectedShapeLeftRepairDescription : MachineDescription :=
  MachineDescription.offsetRetargetDescription
    selectedShapeLeftRepairOffset
    selectedShapeRefreshFinalHalt
    concreteSelectedLeftBoundaryRefreshDescription

def selectedShapeLeftRepairStart : Nat :=
  selectedShapeLeftRepairDescription.start

def selectedShapeLeftRepairLimit : Nat :=
  selectedShapeLeftRepairDescription.stateCount

def selectedShapeRightRepairOffset : Nat :=
  selectedShapeLeftRepairLimit

def selectedShapeRightRepairDescription : MachineDescription :=
  MachineDescription.offsetRetargetDescription
    selectedShapeRightRepairOffset
    selectedShapeRefreshFinalHalt
    concreteSelectedRightBoundaryRefreshDescription

def selectedShapeRightRepairStart : Nat :=
  selectedShapeRightRepairDescription.start

def selectedShapeRightRepairLimit : Nat :=
  selectedShapeRightRepairDescription.stateCount

def selectedShapeTerminalProbeOffset : Nat :=
  selectedShapeRightRepairLimit

def selectedShapeTerminalLocalCanonicalExit : Nat :=
  11

def selectedShapeTerminalLocalRightBoundaryExit : Nat :=
  12

def selectedShapeTerminalLocalUnusedExit : Nat :=
  13

def selectedShapeTerminalLocalTarget : Option Bool -> Nat
  | none => selectedShapeTerminalLocalCanonicalExit
  | some false => selectedShapeTerminalLocalRightBoundaryExit
  | some true => selectedShapeTerminalLocalUnusedExit

def selectedShapeTerminalTarget : Option Bool -> Nat
  | none => selectedShapeRefreshFinalHalt
  | some false => selectedShapeRightRepairStart
  | some true => selectedShapeRefreshFinalHalt

def selectedShapeTerminalLocalDescription : MachineDescription :=
  singletonTerminalPairProbeDescription
    selectedShapeTerminalLocalCanonicalExit
    selectedShapeTerminalLocalRightBoundaryExit

def selectedShapeTerminalProbeDescription : MachineDescription :=
  MachineDescription.offsetReadExitRetargetDescription
    selectedShapeTerminalProbeOffset
    selectedShapeTerminalLocalTarget
    selectedShapeTerminalTarget
    selectedShapeTerminalLocalDescription

def selectedShapeTerminalProbeStart : Nat :=
  selectedShapeTerminalProbeDescription.start

def selectedShapeRefreshOpeningDescription : MachineDescription :=
  singletonOpeningProbeDescription
    selectedShapeTerminalProbeStart
    selectedShapeLeftRepairStart

def selectedShapeRefreshDescription : MachineDescription where
  stateCount := selectedShapeTerminalProbeDescription.stateCount
  start := selectedShapeRefreshOpeningDescription.start
  halt := selectedShapeRefreshFinalHalt
  transitions :=
    selectedShapeRefreshOpeningDescription.transitions ++
      selectedShapeLeftRepairDescription.transitions ++
      selectedShapeRightRepairDescription.transitions ++
      selectedShapeTerminalProbeDescription.transitions

theorem selectedShapeRefreshFinalHalt_lt_leftRepairOffset :
    selectedShapeRefreshFinalHalt < selectedShapeLeftRepairOffset := by
  decide

theorem selectedShapeLeftRepairDescription_subroutineReady :
    selectedShapeLeftRepairDescription.SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    selectedShapeRefreshFinalHalt_lt_leftRepairOffset
    concreteSelectedLeftBoundaryRefreshDescription_subroutineReady.left

theorem selectedShapeLeftRepairOffset_lt_rightRepairOffset :
    selectedShapeLeftRepairOffset < selectedShapeRightRepairOffset := by
  have hstart :=
    selectedShapeLeftRepairDescription_subroutineReady.left.right.left
  simpa [selectedShapeRightRepairOffset, selectedShapeLeftRepairLimit,
    selectedShapeLeftRepairDescription,
    MachineDescription.offsetRetargetDescription] using! hstart

theorem selectedShapeRefreshFinalHalt_lt_rightRepairOffset :
    selectedShapeRefreshFinalHalt < selectedShapeRightRepairOffset :=
  Nat.lt_trans selectedShapeRefreshFinalHalt_lt_leftRepairOffset
    selectedShapeLeftRepairOffset_lt_rightRepairOffset

theorem selectedShapeRightRepairDescription_subroutineReady :
    selectedShapeRightRepairDescription.SubroutineReady :=
  MachineDescription.offsetRetargetDescription_subroutineReady
    selectedShapeRefreshFinalHalt_lt_rightRepairOffset
    concreteSelectedRightBoundaryRefreshDescription_subroutineReady.left

theorem selectedShapeTerminalLocalDescription_subroutineReady :
    selectedShapeTerminalLocalDescription.SubroutineReady :=
  singletonTerminalPairProbeDescription_subroutineReady
    selectedShapeTerminalLocalCanonicalExit
    selectedShapeTerminalLocalRightBoundaryExit

theorem selectedShapeTerminalLocalDescription_transitionFreeAt
    (cell : Option Bool) :
    selectedShapeTerminalLocalDescription.TransitionFreeAt
      (selectedShapeTerminalLocalTarget cell) := by
  cases cell with
  | none =>
      exact
        transition_notFrom_of_all
          (l := selectedShapeTerminalLocalDescription.transitions)
          (state := selectedShapeTerminalLocalTarget none)
          (by decide)
  | some bit =>
      cases bit with
      | false =>
          exact
            transition_notFrom_of_all
              (l := selectedShapeTerminalLocalDescription.transitions)
              (state := selectedShapeTerminalLocalTarget (some false))
              (by decide)
      | true =>
          exact
            transition_notFrom_of_all
              (l := selectedShapeTerminalLocalDescription.transitions)
              (state := selectedShapeTerminalLocalTarget (some true))
              (by decide)

theorem selectedShapeTerminalTarget_lt_probeOffset :
    forall cell : Option Bool,
      selectedShapeTerminalTarget cell <
        selectedShapeTerminalProbeOffset := by
  intro cell
  cases cell with
  | none =>
      have hhalt :=
        selectedShapeRightRepairDescription_subroutineReady.left.right.right.left
      simpa [selectedShapeTerminalTarget,
        selectedShapeTerminalProbeOffset,
        selectedShapeRightRepairLimit,
        selectedShapeRightRepairDescription] using! hhalt
  | some bit =>
      cases bit with
      | false =>
          have hstart :=
            selectedShapeRightRepairDescription_subroutineReady.left.right.left
          simpa [selectedShapeTerminalTarget,
            selectedShapeTerminalProbeOffset,
            selectedShapeRightRepairLimit,
            selectedShapeRightRepairStart] using hstart
      | true =>
          have hhalt :=
            selectedShapeRightRepairDescription_subroutineReady.left.right.right.left
          simpa [selectedShapeTerminalTarget,
            selectedShapeTerminalProbeOffset,
            selectedShapeRightRepairLimit,
            selectedShapeRightRepairDescription] using! hhalt

theorem selectedShapeTerminalProbeDescription_subroutineReady :
    selectedShapeTerminalProbeDescription.SubroutineReady :=
  MachineDescription.offsetReadExitRetargetDescription_subroutineReady
    selectedShapeTerminalTarget_lt_probeOffset
    selectedShapeTerminalLocalDescription_subroutineReady.left

theorem selectedShapeRefreshOpeningDescription_subroutineReady :
    selectedShapeRefreshOpeningDescription.SubroutineReady :=
  singletonOpeningProbeDescription_subroutineReady
    selectedShapeTerminalProbeStart
    selectedShapeLeftRepairStart

theorem selectedShapeRefreshOpeningDescription_sources_below_leftRepairOffset :
    forall t : TransitionDescription,
      t ∈ selectedShapeRefreshOpeningDescription.transitions ->
        t.source < selectedShapeLeftRepairOffset := by
  intro t ht
  simp [selectedShapeRefreshOpeningDescription,
    singletonOpeningProbeDescription] at ht
  rcases ht with rfl | rfl | rfl <;>
    decide

theorem selectedShapeLeftRepairDescription_sources_in_block :
    forall t : TransitionDescription,
      t ∈ selectedShapeLeftRepairDescription.transitions ->
        selectedShapeLeftRepairOffset ≤ t.source ∧
          t.source < selectedShapeLeftRepairLimit := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [selectedShapeLeftRepairDescription,
        MachineDescription.offsetRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (concreteSelectedLeftBoundaryRefreshDescription_subroutineReady.left
      |>.right.right.right.left base hbase).left
  constructor
  · simp [TransitionDescription.sharedExitRetargetStates]
  · simp [TransitionDescription.sharedExitRetargetStates,
      selectedShapeLeftRepairLimit, selectedShapeLeftRepairDescription,
      MachineDescription.offsetRetargetDescription]
    apply Nat.lt_of_lt_of_le
    · exact Nat.add_lt_add_left hsource selectedShapeLeftRepairOffset
    · exact Nat.le_max_left _ _

theorem selectedShapeRightRepairDescription_sources_in_block :
    forall t : TransitionDescription,
      t ∈ selectedShapeRightRepairDescription.transitions ->
        selectedShapeRightRepairOffset ≤ t.source ∧
          t.source < selectedShapeRightRepairLimit := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [selectedShapeRightRepairDescription,
        MachineDescription.offsetRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (concreteSelectedRightBoundaryRefreshDescription_subroutineReady.left
      |>.right.right.right.left base hbase).left
  constructor
  · simp [TransitionDescription.sharedExitRetargetStates]
  · simp [TransitionDescription.sharedExitRetargetStates,
      selectedShapeRightRepairLimit, selectedShapeRightRepairDescription,
      MachineDescription.offsetRetargetDescription]
    apply Nat.lt_of_lt_of_le
    · exact Nat.add_lt_add_left hsource selectedShapeRightRepairOffset
    · exact Nat.le_max_left _ _

theorem selectedShapeTerminalProbeDescription_sources_in_block :
    forall t : TransitionDescription,
      t ∈ selectedShapeTerminalProbeDescription.transitions ->
        selectedShapeTerminalProbeOffset ≤ t.source ∧
          t.source < selectedShapeTerminalProbeDescription.stateCount := by
  intro t ht
  rcases List.mem_map.mp (by
      simpa [selectedShapeTerminalProbeDescription,
        MachineDescription.offsetReadExitRetargetDescription] using ht) with
    ⟨base, hbase, rfl⟩
  have hsource :=
    (selectedShapeTerminalLocalDescription_subroutineReady.left
      |>.right.right.right.left base hbase).left
  constructor
  · simp [MachineDescription.readExitRetargetStates]
  · simp [MachineDescription.readExitRetargetStates,
      selectedShapeTerminalProbeDescription,
      MachineDescription.offsetReadExitRetargetDescription]
    simpa [selectedShapeTerminalLocalDescription] using
      Nat.add_lt_add_left hsource selectedShapeTerminalProbeOffset

theorem selectedShapeRightRepairOffset_lt_terminalProbeOffset :
    selectedShapeRightRepairOffset < selectedShapeTerminalProbeOffset := by
  have hstart :=
    selectedShapeRightRepairDescription_subroutineReady.left.right.left
  simpa [selectedShapeTerminalProbeOffset, selectedShapeRightRepairLimit,
    selectedShapeRightRepairDescription,
    MachineDescription.offsetRetargetDescription] using! hstart

theorem selectedShapeRightRepairOffset_le_terminalProbeOffset :
    selectedShapeRightRepairOffset ≤ selectedShapeTerminalProbeOffset :=
  Nat.le_of_lt selectedShapeRightRepairOffset_lt_terminalProbeOffset

theorem selectedShapeLeftRepairLimit_le_terminalProbeOffset :
    selectedShapeLeftRepairLimit ≤ selectedShapeTerminalProbeOffset := by
  simpa [selectedShapeRightRepairOffset] using
    selectedShapeRightRepairOffset_le_terminalProbeOffset

theorem selectedShapeLeftRepairOffset_le_terminalProbeOffset :
    selectedShapeLeftRepairOffset ≤ selectedShapeTerminalProbeOffset :=
  Nat.le_trans (Nat.le_of_lt selectedShapeLeftRepairOffset_lt_rightRepairOffset)
    selectedShapeRightRepairOffset_le_terminalProbeOffset

theorem selectedShapeRefreshFinalHalt_lt_stateCount :
    selectedShapeRefreshFinalHalt <
      selectedShapeRefreshDescription.stateCount := by
  have hhalt :=
    selectedShapeTerminalProbeDescription_subroutineReady.left.right.right.left
  simpa [selectedShapeRefreshDescription,
    selectedShapeTerminalProbeDescription,
    selectedShapeTerminalTarget] using! hhalt

theorem selectedShapeTerminalProbeOffset_lt_stateCount :
    selectedShapeTerminalProbeOffset <
      selectedShapeRefreshDescription.stateCount := by
  have hpos := selectedShapeTerminalLocalDescription_subroutineReady.left.left
  simpa [selectedShapeRefreshDescription,
    selectedShapeTerminalProbeDescription,
    MachineDescription.offsetReadExitRetargetDescription] using
    Nat.lt_add_of_pos_right (n := selectedShapeTerminalProbeOffset) hpos

theorem selectedShapeLeftRepairLimit_le_stateCount :
    selectedShapeLeftRepairLimit ≤
      selectedShapeRefreshDescription.stateCount :=
  Nat.le_trans selectedShapeLeftRepairLimit_le_terminalProbeOffset
    (Nat.le_of_lt selectedShapeTerminalProbeOffset_lt_stateCount)

theorem selectedShapeRightRepairLimit_le_stateCount :
    selectedShapeRightRepairLimit ≤
      selectedShapeRefreshDescription.stateCount :=
  Nat.le_trans (Nat.le_of_eq rfl)
    (Nat.le_of_lt selectedShapeTerminalProbeOffset_lt_stateCount)

theorem selectedShapeLeftRepairDescription_haltsFrom_leftBoundary
    (encodedPrefix : List (Option Bool))
    (head : Option Bool) (right : List (Option Bool))
    (rest : List (Tape Bool)) :
    selectedShapeLeftRepairDescription.HaltsFromTapeEquiv
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (({ left := [], head := head, right := right ++ [none] } :
            Tape Bool) :: rest)))
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (guardLogicalTape
            ({ left := [], head := head, right := right } :
              Tape Bool) :: rest))) := by
  have hcreate :=
    selectedHeadGapCreatorDescription_contract.realizes encodedPrefix
      ({ left := [], head := head, right := right ++ [none] } :
        Tape Bool)
      rest
  have hrepair :=
    leftBoundaryGuardSlackRefreshDescription_haltsFrom_selectedHeadGap
      encodedPrefix head (right ++ [none]) rest
  have hseq :
      concreteSelectedLeftBoundaryRefreshDescription.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (({ left := [], head := head, right := right ++ [none] } :
              Tape Bool) :: rest)))
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (guardLogicalTape
              ({ left := [], head := head, right := right } :
                Tape Bool) :: rest))) := by
    simpa [concreteSelectedLeftBoundaryRefreshDescription,
      selectedLeftBoundaryRefreshDescription, guardLogicalTape,
      List.append_assoc] using
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        selectedHeadGapCreatorDescription_contract.subroutineReady
        leftBoundaryGuardSlackRefreshDescription_subroutineReady
        hcreate hrepair
  rcases
      hseq with
    ⟨actual, hhalts, hequiv⟩
  refine ⟨actual, ?_, hequiv⟩
  simpa [selectedShapeLeftRepairDescription] using
    MachineDescription.offsetRetargetDescription_haltsFromTape
      selectedShapeRefreshFinalHalt_lt_leftRepairOffset
      concreteSelectedLeftBoundaryRefreshDescription_subroutineReady.right
      hhalts

theorem selectedShapeRightRepairDescription_haltsFrom_rightBoundary
    (encodedPrefix : List (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    selectedShapeRightRepairDescription.HaltsFromTapeEquiv
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (({ left := left ++ [none], head := head, right := [] } :
            Tape Bool) :: rest)))
      (tapeAtEncodedSplit encodedPrefix
        (encodedStructuredTapeCells
          (guardLogicalTape
            ({ left := left, head := head, right := [] } :
              Tape Bool) :: rest))) := by
  have hcreate :=
    selectedHeadGapCreatorDescription_contract.realizes encodedPrefix
      ({ left := left ++ [none], head := head, right := [] } :
        Tape Bool)
      rest
  have hrepair :=
    rightBoundaryGuardSlackRefreshDescription_haltsFrom_selectedHeadGap
      encodedPrefix (left ++ [none]) head rest
  have hseq :
      concreteSelectedRightBoundaryRefreshDescription.HaltsFromTapeEquiv
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (({ left := left ++ [none], head := head, right := [] } :
              Tape Bool) :: rest)))
        (tapeAtEncodedSplit encodedPrefix
          (encodedStructuredTapeCells
            (guardLogicalTape
              ({ left := left, head := head, right := [] } :
                Tape Bool) :: rest))) := by
    simpa [concreteSelectedRightBoundaryRefreshDescription,
      selectedRightBoundaryRefreshDescription, guardLogicalTape,
      List.append_assoc] using
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        selectedHeadGapCreatorDescription_contract.subroutineReady
        rightBoundaryGuardSlackRefreshDescription_subroutineReady
        hcreate hrepair
  rcases
      hseq with
    ⟨actual, hhalts, hequiv⟩
  refine ⟨actual, ?_, hequiv⟩
  simpa [selectedShapeRightRepairDescription] using
    MachineDescription.offsetRetargetDescription_haltsFromTape
      selectedShapeRefreshFinalHalt_lt_rightRepairOffset
      concreteSelectedRightBoundaryRefreshDescription_subroutineReady.right
      hhalts

theorem selectedShapeRefreshDescription_run_false_of_reads
    (physical : Tape Bool)
    (hstart : Tape.read physical = none)
    (hread : Tape.read (Tape.moveRight physical) = some false) :
    selectedShapeRefreshDescription.runConfig 2
        { state := selectedShapeRefreshDescription.start
          tape := physical } =
      { state := selectedShapeTerminalProbeStart
        tape := physical } := by
  cases physical with
  | mk left head right =>
      cases head with
      | none =>
          cases right with
          | nil =>
              simp [Tape.read, Tape.moveRight] at hread
          | cons cell rest =>
              cases cell with
              | none =>
                  simp [Tape.read, Tape.moveRight] at hread
              | some bit =>
                  cases bit
                  · simp [selectedShapeRefreshDescription,
                      selectedShapeRefreshOpeningDescription,
                      singletonOpeningProbeDescription,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches, transition,
                      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                      Tape.moveRight]
                  · simp [Tape.read, Tape.moveRight] at hread
      | some bit =>
          cases bit <;> simp [Tape.read] at hstart

theorem selectedShapeRefreshDescription_run_true_of_reads
    (physical : Tape Bool)
    (hstart : Tape.read physical = none)
    (hread : Tape.read (Tape.moveRight physical) = some true) :
    selectedShapeRefreshDescription.runConfig 2
        { state := selectedShapeRefreshDescription.start
          tape := physical } =
      { state := selectedShapeLeftRepairStart
        tape := physical } := by
  cases physical with
  | mk left head right =>
      cases head with
      | none =>
          cases right with
          | nil =>
              simp [Tape.read, Tape.moveRight] at hread
          | cons cell rest =>
              cases cell with
              | none =>
                  simp [Tape.read, Tape.moveRight] at hread
              | some bit =>
                  cases bit
                  · simp [Tape.read, Tape.moveRight] at hread
                  · simp [selectedShapeRefreshDescription,
                      selectedShapeRefreshOpeningDescription,
                      singletonOpeningProbeDescription,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches, transition,
                      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                      Tape.moveRight]
      | some bit =>
          cases bit <;> simp [Tape.read] at hstart

theorem selectedShapeRefreshDescription_run_canonical_opening
    (encodedPrefix : List (Option Bool))
    (target : Tape Bool) (rest : List (Tape Bool)) :
    selectedShapeRefreshDescription.runConfig 2
        { state := selectedShapeRefreshDescription.start
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest)) } =
      { state := selectedShapeTerminalProbeStart
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (guardLogicalTape target :: rest)) } :=
  selectedShapeRefreshDescription_run_false_of_reads
    (tapeAtEncodedSplit encodedPrefix
      (encodedStructuredTapeCells (guardLogicalTape target :: rest)))
    (tapeAtEncodedSplit_selectedSeparator_read
      encodedPrefix (guardLogicalTape target) rest)
    (tapeAtEncodedSplit_selectedCanonical_afterOpening_read
      encodedPrefix target (guardLogicalTape target) rest
      (by simp [encodedGuardedStructuredTapes, guardLogicalTapes]))

theorem selectedShapeRefreshDescription_run_leftBoundary_opening
    (encodedPrefix : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (rest : List (Tape Bool)) :
    selectedShapeRefreshDescription.runConfig 2
        { state := selectedShapeRefreshDescription.start
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (({ left := [], head := head,
                    right := right ++ [none] } : Tape Bool) :: rest)) } =
      { state := selectedShapeLeftRepairStart
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (({ left := [], head := head,
                  right := right ++ [none] } : Tape Bool) :: rest)) } :=
  selectedShapeRefreshDescription_run_true_of_reads
    (tapeAtEncodedSplit encodedPrefix
      (encodedStructuredTapeCells
        (({ left := [], head := head,
            right := right ++ [none] } : Tape Bool) :: rest)))
    (tapeAtEncodedSplit_selectedSeparator_read
      encodedPrefix
      ({ left := [], head := head, right := right ++ [none] } :
        Tape Bool)
      rest)
    (tapeAtEncodedSplit_selectedLeftBoundary_afterOpening_read
      encodedPrefix head right rest)

theorem selectedShapeRefreshDescription_run_rightBoundary_opening
    (encodedPrefix : List (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    selectedShapeRefreshDescription.runConfig 2
        { state := selectedShapeRefreshDescription.start
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (({ left := left ++ [none], head := head,
                    right := [] } : Tape Bool) :: rest)) } =
      { state := selectedShapeTerminalProbeStart
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (({ left := left ++ [none], head := head,
                  right := [] } : Tape Bool) :: rest)) } :=
  selectedShapeRefreshDescription_run_false_of_reads
    (tapeAtEncodedSplit encodedPrefix
      (encodedStructuredTapeCells
        (({ left := left ++ [none], head := head,
            right := [] } : Tape Bool) :: rest)))
    (tapeAtEncodedSplit_selectedSeparator_read
      encodedPrefix
      ({ left := left ++ [none], head := head, right := [] } :
        Tape Bool)
      rest)
    (tapeAtEncodedSplit_selectedRightBoundary_afterOpening_read
      encodedPrefix left head rest)

theorem selectedShapeTerminalProbeDescription_reaches_selectedCanonical
    (encodedPrefix : List (Option Bool))
    (target : Tape Bool) (rest : List (Tape Bool)) :
    exists steps : Nat,
      selectedShapeTerminalProbeDescription.runConfig steps
        { state := selectedShapeTerminalProbeStart
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (guardLogicalTape target :: rest)) } =
      { state := selectedShapeRefreshFinalHalt
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (guardLogicalTape target :: rest)) } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_selectedCanonical
        selectedShapeTerminalLocalCanonicalExit
        selectedShapeTerminalLocalRightBoundaryExit
        encodedPrefix target rest with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := selectedShapeTerminalProbeOffset)
      (localTarget := selectedShapeTerminalLocalTarget)
      (target := selectedShapeTerminalTarget)
      selectedShapeTerminalTarget_lt_probeOffset
      selectedShapeTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  simpa [selectedShapeTerminalProbeDescription,
    selectedShapeTerminalProbeStart, selectedShapeTerminalLocalDescription,
    selectedShapeTerminalLocalTarget, selectedShapeTerminalTarget,
    MachineDescription.readExitRetargetConfiguration,
    MachineDescription.retargetReadExitState] using! hcopy

theorem selectedShapeTerminalProbeDescription_reaches_selectedRightBoundary
    (encodedPrefix : List (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (rest : List (Tape Bool)) :
    exists steps : Nat,
      selectedShapeTerminalProbeDescription.runConfig steps
        { state := selectedShapeTerminalProbeStart
          tape :=
            tapeAtEncodedSplit encodedPrefix
              (encodedStructuredTapeCells
                (({ left := left ++ [none], head := head,
                    right := [] } : Tape Bool) :: rest)) } =
      { state := selectedShapeRightRepairStart
        tape :=
          tapeAtEncodedSplit encodedPrefix
            (encodedStructuredTapeCells
              (({ left := left ++ [none], head := head,
                  right := [] } : Tape Bool) :: rest)) } := by
  rcases
      singletonTerminalPairProbeDescription_reaches_selectedRightBoundary
        selectedShapeTerminalLocalCanonicalExit
        selectedShapeTerminalLocalRightBoundaryExit
        encodedPrefix left head rest with
    ⟨steps, hrun⟩
  refine ⟨steps, ?_⟩
  have hcopy :=
    MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
      (offset := selectedShapeTerminalProbeOffset)
      (localTarget := selectedShapeTerminalLocalTarget)
      (target := selectedShapeTerminalTarget)
      selectedShapeTerminalTarget_lt_probeOffset
      selectedShapeTerminalLocalDescription_transitionFreeAt
      (n := steps)
      hrun
  simpa [selectedShapeTerminalProbeDescription,
    selectedShapeTerminalProbeStart, selectedShapeTerminalLocalDescription,
    selectedShapeTerminalLocalTarget, selectedShapeTerminalTarget,
    MachineDescription.readExitRetargetConfiguration,
    MachineDescription.retargetReadExitState] using! hcopy


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
