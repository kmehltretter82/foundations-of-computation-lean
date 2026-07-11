import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Layout
import FoC.Computability.Compiler.Core.FixedDescBoundedSim.Spec

set_option doc.verso true

/-!
# Bounded simulator seam for fuel-pair search

This module adapts the lower fixed-description simulator contract to the
candidate layouts used by fuel-pair search.  It is conditional on the #18
construction proposition, so the adapter itself remains free of
{name}`sorryAx`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace BoundedFuelPairSearch

/-- Equivalence-facing bounded simulation for every scheduled candidate. -/
def CandidateSimulatorEquivSpec
    (runner simulator : MachineDescription) : Prop :=
  simulator.SubroutineReady ∧
    forall w : Word Bool,
    forall i : ScheduleIndex,
      simulator.HaltsFromTapeEquiv
        (SimulatorLayout.tape (CandidateInitialLayout runner w i))
        (FixedDescriptionBoundedSimulatorCanonicalOutputTape runner
          (CandidateInitialLayout runner w i))

def CandidateSimulatorEquivConstruction : Prop :=
  forall runner : MachineDescription,
    exists simulator : MachineDescription,
      CandidateSimulatorEquivSpec runner simulator

/-- Exact padded bounded simulation, suitable for halt retargeting. -/
def CandidateSimulatorPaddedSpec
    (runner simulator : MachineDescription) : Prop :=
  simulator.SubroutineReady ∧
    forall w : Word Bool,
    forall i : ScheduleIndex,
      simulator.HaltsFromTape
        (Tape.input (SerializedPhaseBits .ready runner w i))
        (FixedDescriptionBoundedSimulatorPaddedOutputTape runner
          (CandidateInitialLayout runner w i))

def CandidateSimulatorPaddedConstruction : Prop :=
  forall runner : MachineDescription,
    exists simulator : MachineDescription,
      CandidateSimulatorPaddedSpec runner simulator

theorem candidateSimulatorEquivConstruction_of_fixedDescription
    (hconstruction : FixedDescriptionBoundedSimulatorEquivConstruction) :
    CandidateSimulatorEquivConstruction := by
  intro runner
  rcases hconstruction runner with ⟨simulator, hsimulator⟩
  refine ⟨simulator, hsimulator.left, ?_⟩
  intro w i
  exact hsimulator.haltsFromTapeEquiv
    (CandidateInitialLayout runner w i)

theorem candidateSimulatorPaddedConstruction_of_fixedDescription
    (hconstruction : FixedDescriptionBoundedSimulatorPaddedConstruction) :
    CandidateSimulatorPaddedConstruction := by
  intro runner
  rcases hconstruction runner with ⟨simulator, hsimulator⟩
  refine ⟨simulator, hsimulator.left, ?_⟩
  intro w i
  rcases hsimulator.right.left (CandidateInitialLayout runner w i) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [MachineDescription.HaltsWithTapeIn,
    MachineDescription.HaltsFromTapeIn,
    MachineDescription.initial,
    serializedReadyBits_eq_fixedSimulatorInput] using hsteps

end BoundedFuelPairSearch

end Computability
end FoC
