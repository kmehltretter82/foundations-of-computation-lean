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

/-- Halting form of the exact exchanged fused-emitter run. -/
theorem swappedFusedD_haltsWithTapes_prepare_then_rawEmission
    (attempt : MachineDescription)
    (T1 : Tape Bool) (head : Bool) (tail : Word Bool) (fuel : Nat) :
    exists A0 A1 A2 : Tape Bool,
      (swappedFusedD attempt.start).HaltsWithTapes
        (ThreeTape.config
          ((fusedTable attempt.start).stateId
            (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          (cursorFuelSourceTape fuel) T1
          (Tape.input (head :: tail)))
        [A0, A1, A2] ∧
      Tape.Equiv A0 (rawEmissionFinalScratch (head :: tail) fuel) ∧
      Tape.Equiv A1 T1 ∧
      Tape.Equiv A2
        (rawEmissionOutputTape attempt (head :: tail) fuel) := by
  rcases swappedFused_runs_prepare_then_rawEmission
      attempt T1 head tail fuel with
    ⟨steps, A0, A1, A2, hrun, hA0, hA1, hA2⟩
  exact ⟨A0, A1, A2, ⟨steps, hrun⟩, hA0, hA1, hA2⟩

/-- Physical three-tape lowering of the scratch-preserving second emitter. -/
theorem swappedFusedLowered_haltsFromTapeEquiv_prepare_then_rawEmission
    (attempt : MachineDescription)
    (T1 : Tape Bool) (head : Bool) (tail : Word Bool) (fuel : Nat) :
    exists A0 A1 A2 : Tape Bool,
      (lowerStructured3Description (swappedFusedD attempt.start)).HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes
          (cursorFuelSourceTape fuel) T1 (Tape.input (head :: tail)))
        (encodedGuardedStructured3Tapes A0 A1 A2) ∧
      Tape.Equiv A0 (rawEmissionFinalScratch (head :: tail) fuel) ∧
      Tape.Equiv A1 T1 ∧
      Tape.Equiv A2
        (rawEmissionOutputTape attempt (head :: tail) fuel) := by
  rcases swappedFusedD_haltsWithTapes_prepare_then_rawEmission
      attempt T1 head tail fuel with
    ⟨A0, A1, A2, hhalts, hA0, hA1, hA2⟩
  have hlowered :=
    lowerStructured3Description_haltsFromConfigWithTapes
      (swappedFusedTable attempt.start).description_wellFormed
      (swappedFusedTable attempt.start).description_haltTransitionFree
      (swappedFusedTable attempt.start).description_supportsReadWriteRows3
      (c := ThreeTape.config
        ((fusedTable attempt.start).stateId
          (Sum.inl RawLayoutPreparation.State.seekRawEnd))
        (cursorFuelSourceTape fuel) T1 (Tape.input (head :: tail)))
      (tapes := [A0, A1, A2])
      rfl (by rfl) hhalts
  refine ⟨A0, A1, A2, ?_, hA0, hA1, hA2⟩
  simpa [swappedFusedD, swappedFusedTable,
    encodedGuardedStructured3Tapes, ThreeTape.config] using hlowered

end SwappedLayoutEmission
end StructuredConstructionTargets

end Computability
end FoC
