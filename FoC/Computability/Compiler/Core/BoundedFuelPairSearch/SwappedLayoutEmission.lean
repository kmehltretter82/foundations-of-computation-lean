import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.FusedLayoutEmission
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Tape01Swap

set_option doc.verso true

/-!
# Scratch-preserving second simulator-layout emission

The first simulator run leaves its candidate and source-fuel record on logical
tape 1.  Reusing the fused layout emitter with tapes 0 and 1 exchanged stages
the checker simulator on tape 2 while preserving that record.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets
namespace SwappedLayoutEmission

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open FusedLayoutEmission
open FuelSimulatorCore
open FuelSimulatorCore.RawLayoutEmission
open RawLayoutPreparation
open FoC.Computability.BoundedFuelPairSearch.Tape01Swap

/-- Fused layout emitter with logical tapes 0 and 1 exchanged. -/
def swappedFusedTable (start : Nat) :=
  FoC.Computability.BoundedFuelPairSearch.Tape01Swap.table
    (fusedTable start)

/-- Structured description of the exchanged fused emitter. -/
def swappedFusedD (start : Nat) :=
  (swappedFusedTable start).description

/-- Exact exchanged execution of preparation followed by raw layout emission. -/
theorem swappedFused_runs_prepare_then_rawEmission
    (attempt : MachineDescription)
    (T1 : Tape Bool) (head : Bool) (tail : Word Bool) (fuel : Nat) :
    exists steps : Nat, exists A0 A1 A2 : Tape Bool,
      (swappedFusedD attempt.start).runConfig steps
          (ThreeTape.config
            ((fusedTable attempt.start).stateId
              (Sum.inl RawLayoutPreparation.State.seekRawEnd))
            (cursorFuelSourceTape fuel) T1
            (Tape.input (head :: tail))) =
        ThreeTape.config
          ((fusedTable attempt.start).stateId
            (Sum.inr FuelSimulatorCore.State.halt))
          A0 A1 A2 ∧
      Tape.Equiv A0 (rawEmissionFinalScratch (head :: tail) fuel) ∧
      Tape.Equiv A1 T1 ∧
      Tape.Equiv A2
        (rawEmissionOutputTape attempt (head :: tail) fuel) := by
  rcases fused_runs_prepare_then_rawEmission attempt T1 head tail fuel with
    ⟨steps, U0, U1, U2, hrun, hU0, hU1, hU2⟩
  refine ⟨steps, U1, U0, U2, ?_, hU1, hU0, hU2⟩
  exact
    FoC.Computability.BoundedFuelPairSearch.Tape01Swap.runConfig_of_runConfig
      (fusedTable attempt.start) steps
    (Sum.inl RawLayoutPreparation.State.seekRawEnd)
    (fusedTable attempt.start).start_mem
    (cursorFuelSourceTape fuel) T1 (Tape.input (head :: tail))
    (Sum.inr FuelSimulatorCore.State.halt) U1 U0 U2 hrun

end SwappedLayoutEmission
end StructuredConstructionTargets

end Computability
end FoC
