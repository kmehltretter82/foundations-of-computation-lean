import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.LeftShiftCompactor

set_option doc.verso true

/-!
# Metadata witness marker

This finite table marks the middle cell of the three-blank boundary left by
the leading-blank compactor and parks on the new marker.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataWitnessMarker

open Languages MachineDescription
open CommonGround.FiniteTransducers

def description : MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 none (some true) Direction.right 2
    , transition 2 none none Direction.left 3 ]

theorem description_wellFormed : description.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := description.transitions) (stateCount := description.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := description.transitions) (by decide)

theorem description_haltTransitionFree : description.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := description.transitions) (state := description.halt) (by decide)

theorem description_subroutineReady : description.SubroutineReady :=
  ⟨description_wellFormed, description_haltTransitionFree⟩

private theorem description_run
    (base : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    description.runConfig 3
        { state := description.start
          tape :=
            leadingBlankLeftShiftTargetTapeWithPadding
              base bits (none :: padding) } =
      { state := description.halt
        tape := tapeAtCells
          (none :: List.append (bits.reverse.map some) base)
          (some true :: none :: padding) } := by
  rfl

theorem description_haltsFromTape
    (base : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    description.HaltsFromTape
      (leadingBlankLeftShiftTargetTapeWithPadding
        base bits (none :: padding))
      (tapeAtCells
        (none :: List.append (bits.reverse.map some) base)
        (some true :: none :: padding)) := by
  refine ⟨3, ?_⟩
  constructor <;> rw [description_run]

end GuardedEgress.MetadataWitnessMarker
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
