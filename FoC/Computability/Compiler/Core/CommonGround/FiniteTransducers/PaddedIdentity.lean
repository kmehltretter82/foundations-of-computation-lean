import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Padded-input finite transducer contracts
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

/--
Machine-level realization contract for a finite transducer.  The source is a
canonical scratch-padded input tape and the target is the right-shifted
scratch-padded output tape.
-/
def CompiledByDescription
    (F : FiniteTransducer) (D : MachineDescription) : Prop :=
  D.SubroutineReady ∧
    forall input output : Word Bool,
    forall scratchWidth : Nat,
      F.RunsToOutput input output ->
        D.HaltsFromTape
          (inputWithTrailingBlankPadding input scratchWidth)
          (FSTTargetTape output scratchWidth)

/-- A first compiled-machine block: preserve the current cell and move right. -/
def rightMoveOnceDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ { source := 0
        read := none
        write := none
        move := Direction.right
        target := 1 }
    , { source := 0
        read := some false
        write := some false
        move := Direction.right
        target := 1 }
    , { source := 0
        read := some true
        write := some true
        move := Direction.right
        target := 1 } ]

theorem rightMoveOnceDescription_wellFormed :
    rightMoveOnceDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightMoveOnceDescription.transitions)
      (stateCount := rightMoveOnceDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightMoveOnceDescription.transitions)
      (by decide)

theorem rightMoveOnceDescription_haltTransitionFree :
    rightMoveOnceDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightMoveOnceDescription.transitions)
    (state := rightMoveOnceDescription.halt)
    (by decide)

theorem rightMoveOnceDescription_subroutineReady :
    rightMoveOnceDescription.SubroutineReady :=
  ⟨rightMoveOnceDescription_wellFormed,
    rightMoveOnceDescription_haltTransitionFree⟩

theorem rightMoveOnceDescription_run
    (T : Tape Bool) :
    rightMoveOnceDescription.runConfig 1
        { state := rightMoveOnceDescription.start
          tape := T } =
      { state := rightMoveOnceDescription.halt
        tape := Tape.move Direction.right T } := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          simp [rightMoveOnceDescription, runConfig, stepConfig,
            lookupTransition, Matches, Tape.read, Tape.write]
      | some bit =>
          cases bit <;>
            simp [rightMoveOnceDescription, runConfig, stepConfig,
              lookupTransition, Matches, Tape.read, Tape.write]

theorem rightMoveOnceDescription_haltsFromTape
    (T : Tape Bool) :
    rightMoveOnceDescription.HaltsFromTape T
      (Tape.move Direction.right T) := by
  refine ⟨1, ?_⟩
  constructor <;>
    rw [rightMoveOnceDescription_run]

theorem rightMoveOnceDescription_haltsFrom_paddedInput
    (input : Word Bool) (scratchWidth : Nat) :
    rightMoveOnceDescription.HaltsFromTape
      (inputWithTrailingBlankPadding input scratchWidth)
      (FSTTargetTape input scratchWidth) := by
  exact rightMoveOnceDescription_haltsFromTape
    (inputWithTrailingBlankPadding input scratchWidth)

def rightMoveAcrossFourBlanksDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 2 none none Direction.right 3
    , transition 3 none none Direction.right 4 ]

theorem rightMoveAcrossFourBlanksDescription_wellFormed :
    rightMoveAcrossFourBlanksDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := rightMoveAcrossFourBlanksDescription.transitions)
      (stateCount := rightMoveAcrossFourBlanksDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := rightMoveAcrossFourBlanksDescription.transitions)
      (by decide)

theorem rightMoveAcrossFourBlanksDescription_haltTransitionFree :
    rightMoveAcrossFourBlanksDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := rightMoveAcrossFourBlanksDescription.transitions)
    (state := rightMoveAcrossFourBlanksDescription.halt)
    (by decide)

theorem rightMoveAcrossFourBlanksDescription_subroutineReady :
    rightMoveAcrossFourBlanksDescription.SubroutineReady :=
  ⟨rightMoveAcrossFourBlanksDescription_wellFormed,
    rightMoveAcrossFourBlanksDescription_haltTransitionFree⟩

theorem rightMoveAcrossFourBlanksDescription_run
    (left right : List (Option Bool)) :
    rightMoveAcrossFourBlanksDescription.runConfig 4
        { state := rightMoveAcrossFourBlanksDescription.start
          tape :=
            tapeAtCells left
              (none :: none :: none :: none :: right) } =
      { state := rightMoveAcrossFourBlanksDescription.halt
        tape :=
          tapeAtCells
            (none :: none :: none :: none :: left)
            right } := by
  cases right <;>
    simp [rightMoveAcrossFourBlanksDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem rightMoveAcrossFourBlanksDescription_haltsFromTape
    (left right : List (Option Bool)) :
    rightMoveAcrossFourBlanksDescription.HaltsFromTape
      (tapeAtCells left
        (none :: none :: none :: none :: right))
      (tapeAtCells
        (none :: none :: none :: none :: left)
        right) := by
  refine ⟨4, ?_⟩
  constructor <;>
    rw [rightMoveAcrossFourBlanksDescription_run]

def leftMoveAcrossFiveBlanksDescription : MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 none none Direction.left 2
    , transition 2 none none Direction.left 3
    , transition 3 none none Direction.left 4
    , transition 4 none none Direction.left 5 ]

theorem leftMoveAcrossFiveBlanksDescription_wellFormed :
    leftMoveAcrossFiveBlanksDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := leftMoveAcrossFiveBlanksDescription.transitions)
      (stateCount := leftMoveAcrossFiveBlanksDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := leftMoveAcrossFiveBlanksDescription.transitions)
      (by decide)

theorem leftMoveAcrossFiveBlanksDescription_haltTransitionFree :
    leftMoveAcrossFiveBlanksDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := leftMoveAcrossFiveBlanksDescription.transitions)
    (state := leftMoveAcrossFiveBlanksDescription.halt)
    (by decide)

theorem leftMoveAcrossFiveBlanksDescription_subroutineReady :
    leftMoveAcrossFiveBlanksDescription.SubroutineReady :=
  ⟨leftMoveAcrossFiveBlanksDescription_wellFormed,
    leftMoveAcrossFiveBlanksDescription_haltTransitionFree⟩

theorem leftMoveAcrossFiveBlanksDescription_run
    (left right : List (Option Bool)) :
    leftMoveAcrossFiveBlanksDescription.runConfig 5
        { state := leftMoveAcrossFiveBlanksDescription.start
          tape :=
            tapeAtCells
              (none :: none :: none :: none :: none :: left)
              (none :: right) } =
      { state := leftMoveAcrossFiveBlanksDescription.halt
        tape :=
          tapeAtCells left
            (none :: none :: none :: none :: none :: none :: right) } := by
  cases right <;>
    simp [leftMoveAcrossFiveBlanksDescription, runConfig,
      stepConfig, lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem leftMoveAcrossFiveBlanksDescription_haltsFromTape
    (left right : List (Option Bool)) :
    leftMoveAcrossFiveBlanksDescription.HaltsFromTape
      (tapeAtCells
        (none :: none :: none :: none :: none :: left)
        (none :: right))
      (tapeAtCells left
        (none :: none :: none :: none :: none :: none :: right)) := by
  refine ⟨5, ?_⟩
  constructor <;>
    rw [leftMoveAcrossFiveBlanksDescription_run]

/-- The identity transducer is realized by a single right move. -/
theorem identityTransducer_compiledByDescription :
    CompiledByDescription identityTransducer rightMoveOnceDescription := by
  constructor
  · exact rightMoveOnceDescription_subroutineReady
  · intro input output scratchWidth hrun
    have hid := identityTransducer_run input
    change
      identityTransducer.runFromStart (input.length + 1) input =
        some (identityTransducer.halt, output) at hrun
    rw [hid] at hrun
    cases hrun
    exact rightMoveOnceDescription_haltsFrom_paddedInput input scratchWidth

end FiniteTransducers
end CommonGround

end Computability
end FoC
