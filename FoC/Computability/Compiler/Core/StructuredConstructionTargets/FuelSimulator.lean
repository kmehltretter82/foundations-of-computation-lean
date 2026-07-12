import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorCore.Runs

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def fuelSimulatorStructuredOutputTape
    (attempt : MachineDescription)
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
    attempt i.w i.limit i.fuel

def FuelSimulatorStructuredEndpointEquivIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered : FuelSimulatorStructuredIndex -> Tape Bool,
    Structured3EndpointEquivIndexedFamilySpec
      W
      fuelSimulatorStructuredInputTape
      initialized
      lowered
      (fuelSimulatorStructuredOutputTape attempt)

/--
Equivalence-facing fuel-simulator lowered structured core data.

Logical tape 2 contains the exact simulator-layout output. Logical tapes 0 and
1 carry the concrete representatives left by the structured construction; the
endpoint projector does not observe them, so requiring the pristine input and
an exactly blank scratch tape would impose an unnecessary cleanup phase.
-/
structure FuelSimulatorStructuredEquivLoweredCoreComponents
    (attempt : MachineDescription) where
  tape0 : FuelSimulatorStructuredIndex -> Tape Bool
  tape1 : FuelSimulatorStructuredIndex -> Tape Bool
  lowered : FuelSimulatorStructuredIndex -> Tape Bool
  components :
    Structured3CanonicalEquivEndpointLoweredCoreComponents
      (fun i : FuelSimulatorStructuredIndex =>
        fuelSimulatorStructuredInitializedTape i)
      lowered
      (fun i => fuelSimulatorStructuredOutputTape attempt i)
      tape0
      tape1

/--
Existence form for the equivalence-facing fuel-simulator lowered structured
core.
-/
def FuelSimulatorStructuredEquivLoweredCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Nonempty (FuelSimulatorStructuredEquivLoweredCoreComponents attempt)

theorem fuelSimulatorStructuredLoweredCore_forward
    (attempt : MachineDescription) (i : FuelSimulatorStructuredIndex) :
    (lowerStructured3Description
        (FuelSimulatorCore.coreD attempt.start)).HaltsFromTapeEquiv
      (fuelSimulatorStructuredInitializedTape i)
      (encodedGuardedStructured3Tapes
        (FuelSimulatorCore.sourceAfterCopy i)
        (FuelSimulatorCore.finalScratchTape i)
        (fuelSimulatorStructuredOutputTape attempt i)) := by
  rcases (FuelSimulatorCore.leads_halt attempt i).to_runConfig with
    ⟨steps, hrun⟩
  have hhalts :
      (FuelSimulatorCore.coreD attempt.start).HaltsWithTapes
        (FuelSimulatorCore.coreCfg attempt.start .len0
          (Tape.input (fuelSimulatorInputBits i))
          Tape.blank Tape.blank)
        [ FuelSimulatorCore.sourceAfterCopy i
        , FuelSimulatorCore.finalScratchTape i
        , fuelSimulatorStructuredOutputTape attempt i ] := by
    refine ⟨steps, ?_⟩
    change
      (FuelSimulatorCore.coreD attempt.start).runConfig steps
          (FuelSimulatorCore.coreCfg attempt.start .len0
            (Tape.input (fuelSimulatorInputBits i)) Tape.blank Tape.blank) =
        FuelSimulatorCore.coreCfg attempt.start .halt
          (FuelSimulatorCore.sourceAfterCopy i)
          (FuelSimulatorCore.finalScratchTape i)
          (fuelSimulatorStructuredOutputTape attempt i)
    simpa [fuelSimulatorStructuredOutputTape] using hrun
  have hlowered :=
    lowerStructured3Description_haltsFromConfigWithTapes
      (FuelSimulatorCore.table attempt.start).description_wellFormed
      (FuelSimulatorCore.table attempt.start).description_haltTransitionFree
      (FuelSimulatorCore.table attempt.start).description_supportsReadWriteRows3
      (c := FuelSimulatorCore.coreCfg attempt.start .len0
        (Tape.input (fuelSimulatorInputBits i)) Tape.blank Tape.blank)
      (tapes :=
        [ FuelSimulatorCore.sourceAfterCopy i
        , FuelSimulatorCore.finalScratchTape i
        , fuelSimulatorStructuredOutputTape attempt i ])
      rfl rfl hhalts
  simpa [fuelSimulatorStructuredInitializedTape,
    fuelSimulatorStructuredInputTape, fuelSimulatorStructuredOutputBuffer,
    CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape,
    fuelSimulatorInputBits, FuelSimulatorCore.coreD,
    FuelSimulatorCore.coreCfg, TypedStateTable.config, ThreeTape.config,
    encodedGuardedStructured3Tapes] using hlowered

/--
Finite-table leaf for the lowered fuel-simulator structured core.

The concrete three-tape lowerer preserves the represented logical tapes only
up to tape equivalence, and the sole endpoint consumer uses that same currency.
Requiring an exact guarded physical representative here would add a separate
normalization problem that is not observable at the endpoint.
-/
theorem fuelSimulatorStructuredEquivLoweredCoreConstruction_core
    (attempt : MachineDescription) :
    FuelSimulatorStructuredEquivLoweredCoreConstruction attempt := by
  refine ⟨{
    tape0 := FuelSimulatorCore.sourceAfterCopy
    tape1 := FuelSimulatorCore.finalScratchTape
    lowered := fun i =>
      encodedGuardedStructured3Tapes
        (FuelSimulatorCore.sourceAfterCopy i)
        (FuelSimulatorCore.finalScratchTape i)
        (fuelSimulatorStructuredOutputTape attempt i)
    components := ?_
  }⟩
  refine {
    core := FuelSimulatorCore.coreD attempt.start
    coreWellFormed :=
      (FuelSimulatorCore.table attempt.start).description_wellFormed
    coreHaltTransitionFree :=
      (FuelSimulatorCore.table attempt.start).description_haltTransitionFree
    coreSupportsRows :=
      (FuelSimulatorCore.table attempt.start).description_supportsReadWriteRows3
    loweredShape := by intro i; rfl
    loweredCore := {
      forward := by
        intro i
        exact fuelSimulatorStructuredLoweredCore_forward attempt i
      closed := by
        intro i
        exact
          closedFromTapeEquiv_of_haltsFromTapeEquiv_of_subroutineReady
            (lowerStructured3Description_subroutineReady
              (FuelSimulatorCore.table attempt.start).description_wellFormed
              (FuelSimulatorCore.table attempt.start).description_supportsReadWriteRows3)
            (fuelSimulatorStructuredLoweredCore_forward attempt i)
    }
  }

end StructuredConstructionTargets

end Computability
end FoC
