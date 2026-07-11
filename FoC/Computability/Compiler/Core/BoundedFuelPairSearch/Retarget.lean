import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Simulation
import FoC.Computability.Compiler.SeqSubroutineSemantics

set_option doc.verso true

/-!
# Retargeted bounded-simulator block

The fixed-description bounded simulator is a standalone subroutine whose local
halt is its endpoint.  Fuel-pair search instead needs a copied simulator block
that returns to a caller-owned continuation state.  This module supplies that
semantic adapter without constructing the simulator: all results are
conditional on
{name (full := FoC.Computability.BoundedFuelPairSearch.CandidateSimulatorPaddedSpec)}`CandidateSimulatorPaddedSpec`.

The caller continuation is required to lie below the copied state block.  This
both makes halt retargeting sound and gives the source-disjointness facts used
when the block is later inserted into a dispatcher union.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace BoundedFuelPairSearch

/-- Copy a candidate simulator at {lit}`offset` and redirect its local halt to
the caller-owned {lit}`continuation` state. -/
def CandidateSimulatorRetargetedBlock
    (simulator : MachineDescription) (offset continuation : Nat) :
    MachineDescription :=
  MachineDescription.offsetRetargetDescription
    offset continuation simulator

@[simp] theorem candidateSimulatorRetargetedBlock_halt
    (simulator : MachineDescription) (offset continuation : Nat) :
    (CandidateSimulatorRetargetedBlock
      simulator offset continuation).halt = continuation := by
  rfl

@[simp] theorem candidateSimulatorRetargetedBlock_stateCount
    {simulator : MachineDescription} {offset continuation : Nat}
    (hcontinuation : continuation < offset)
    (hsimulator : simulator.WellFormed) :
    (CandidateSimulatorRetargetedBlock simulator offset continuation).stateCount =
      offset + simulator.stateCount := by
  unfold CandidateSimulatorRetargetedBlock
  simp only [MachineDescription.offsetRetargetDescription]
  apply Nat.max_eq_left
  have hpositive : 0 < simulator.stateCount := hsimulator.left
  lia

/-- The retargeted simulator remains a well-formed, halt-transition-free
subroutine.  Its public halt is the caller continuation. -/
theorem candidateSimulatorRetargetedBlock_subroutineReady
    {simulator : MachineDescription} {offset continuation : Nat}
    (hcontinuation : continuation < offset)
    (hsimulator : simulator.SubroutineReady) :
    (CandidateSimulatorRetargetedBlock
      simulator offset continuation).SubroutineReady := by
  exact MachineDescription.offsetRetargetDescription_subroutineReady
    hcontinuation hsimulator.left

/-- Every transition source lies inside the copied simulator state block. -/
theorem candidateSimulatorRetargetedBlock_transition_source_bounds
    {simulator : MachineDescription} {offset continuation : Nat}
    (hsimulator : simulator.WellFormed)
    (t : TransitionDescription)
    (ht :
      t ∈ (CandidateSimulatorRetargetedBlock
        simulator offset continuation).transitions) :
    offset ≤ t.source ∧ t.source < offset + simulator.stateCount := by
  rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
  have hsource := (hsimulator.right.right.right.left base hbase).left
  simp [TransitionDescription.sharedExitRetargetStates]
  lia

/-- A copied transition either returns to the caller continuation or targets a
state inside the copied simulator block. -/
theorem candidateSimulatorRetargetedBlock_transition_target_bounds
    {simulator : MachineDescription} {offset continuation : Nat}
    (hsimulator : simulator.WellFormed)
    (t : TransitionDescription)
    (ht :
      t ∈ (CandidateSimulatorRetargetedBlock
        simulator offset continuation).transitions) :
    t.target = continuation ∨
      (offset ≤ t.target ∧
        t.target < offset + simulator.stateCount) := by
  rcases List.mem_map.mp ht with ⟨base, hbase, rfl⟩
  have htarget := (hsimulator.right.right.right.left base hbase).right
  by_cases hlocal : base.target = simulator.halt
  · left
    simp [TransitionDescription.sharedExitRetargetStates, hlocal]
  · right
    simp [TransitionDescription.sharedExitRetargetStates, hlocal]
    lia

/-- No copied transition is sourced at the caller continuation, so a later
dispatcher may safely own the outgoing continuation rows. -/
theorem candidateSimulatorRetargetedBlock_no_continuation_source
    {simulator : MachineDescription} {offset continuation : Nat}
    (hcontinuation : continuation < offset)
    (hsimulator : simulator.WellFormed)
    (t : TransitionDescription)
    (ht :
      t ∈ (CandidateSimulatorRetargetedBlock
        simulator offset continuation).transitions) :
    t.source ≠ continuation := by
  have hbounds :=
    candidateSimulatorRetargetedBlock_transition_source_bounds
      hsimulator t ht
  lia

/-- Exact candidate-simulator execution after copying and halt retargeting.
The endpoint control state is the caller continuation, while the output tape is
the exact padded tape promised by the #18-facing simulator contract. -/
theorem candidateSimulatorRetargetedBlock_runsToContinuation
    {runner simulator : MachineDescription}
    {offset continuation : Nat}
    (hcontinuation : continuation < offset)
    (hsimulator : CandidateSimulatorPaddedSpec runner simulator)
    (w : Word Bool) (i : ScheduleIndex) :
    exists steps : Nat,
      (CandidateSimulatorRetargetedBlock simulator offset continuation).runConfig
          steps
          { state :=
              (CandidateSimulatorRetargetedBlock
                simulator offset continuation).start
            tape := Tape.input (SerializedPhaseBits .ready runner w i) } =
        { state := continuation
          tape :=
            FixedDescriptionBoundedSimulatorPaddedOutputTape runner
              (CandidateInitialLayout runner w i) } := by
  have hhalts :=
    MachineDescription.offsetRetargetDescription_haltsFromTape
      hcontinuation hsimulator.left.right (hsimulator.right w i)
  exact MachineDescription.runConfig_eq_halt_of_haltsFromTape hhalts

end BoundedFuelPairSearch

end Computability
end FoC
