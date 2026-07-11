import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorInputMaterializer

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
Canonical endpoint output of the lowered fuel-simulator structured core.

The core preserves the public source on logical tape 0, keeps tape 1 blank, and
writes the exact simulator-layout output tape on logical tape 2.
-/
def fuelSimulatorStructuredLoweredTape
    (attempt : MachineDescription)
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (fuelSimulatorStructuredInputTape i)
    Tape.blank
    (fuelSimulatorStructuredOutputTape attempt i)

/--
Equivalence-facing fuel-simulator lowered structured core data after input
materialization.
-/
def FuelSimulatorStructuredEquivLoweredCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalEquivEndpointLoweredCoreComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Existence form for the equivalence-facing fuel-simulator lowered structured
core.
-/
def FuelSimulatorStructuredEquivLoweredCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalEquivEndpointLoweredCoreConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Fuel-simulator parser/core components for the equivalence-facing endpoint,
before installing the shared tape-2 projector.
-/
def FuelSimulatorStructuredCanonicalEndpointEquivCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalEquivEndpointCoreComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Existence form for fuel-simulator equivalence-facing parser/core components.
-/
def FuelSimulatorStructuredCanonicalEndpointEquivCoreComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalEquivEndpointCoreComponentConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Combine the fuel-simulator equivalence-facing materializer and lowered core
into the no-projector endpoint component obligation.
-/
theorem fuelSimulatorStructuredCanonicalEndpointEquivCoreComponentConstruction_of_materializer_loweredCore
    {attempt : MachineDescription}
    (hmaterializer :
      FuelSimulatorStructuredEquivIndexedMaterializerConstruction)
    (hcore :
      FuelSimulatorStructuredEquivLoweredCoreConstruction attempt) :
    FuelSimulatorStructuredCanonicalEndpointEquivCoreComponentConstruction
      attempt := by
  simpa [FuelSimulatorStructuredEquivIndexedMaterializerConstruction,
    FuelSimulatorStructuredEquivLoweredCoreConstruction,
    FuelSimulatorStructuredCanonicalEndpointEquivCoreComponentConstruction] using
    structured3CanonicalEquivEndpointCoreComponentConstruction_of_materializer_loweredCore
      hmaterializer hcore

theorem fuelSimulatorStructuredCanonicalEndpointEquivCoreComponentConstruction_of_inputMaterializer_loweredCore
    {attempt : MachineDescription}
    (hmaterializer :
      FuelSimulatorStructuredEquivInputMaterializerConstruction)
    (hcore :
      FuelSimulatorStructuredEquivLoweredCoreConstruction attempt) :
    FuelSimulatorStructuredCanonicalEndpointEquivCoreComponentConstruction
      attempt :=
  fuelSimulatorStructuredCanonicalEndpointEquivCoreComponentConstruction_of_materializer_loweredCore
    (fuelSimulatorStructuredEquivIndexedMaterializerConstruction_of_inputMaterializer
      hmaterializer)
    hcore

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
  -- Remaining structured-core obligation: construct the initial simulator
  -- layout on logical tape 2 and lower the run up to tape equivalence.
  sorry

/--
Fuel-simulator endpoint components for the equivalence-facing prototype path,
including the shared tape-2 projector.
-/
def FuelSimulatorStructuredCanonicalEndpointEquivComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalEquivEndpointComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Existence form for the fuel-simulator equivalence-facing endpoint components.
-/
def FuelSimulatorStructuredCanonicalEndpointEquivComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalEquivEndpointComponentConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Install the shared equivalence tape-2 projector into equivalence-facing
fuel-simulator core components.
-/
theorem fuelSimulatorStructuredCanonicalEndpointEquivComponentConstruction_of_equivCoreComponents
    {attempt : MachineDescription}
    (hcore :
      FuelSimulatorStructuredCanonicalEndpointEquivCoreComponentConstruction
        attempt)
    (hprojector :
      Structured3EndpointTape2ProjectorConstruction) :
    FuelSimulatorStructuredCanonicalEndpointEquivComponentConstruction
      attempt := by
  simpa [FuelSimulatorStructuredCanonicalEndpointEquivCoreComponentConstruction,
    FuelSimulatorStructuredCanonicalEndpointEquivComponentConstruction] using
    structured3CanonicalEquivEndpointComponentConstruction_of_coreComponents
      hcore hprojector

/--
Equivalence-facing fuel-simulator components imply the equivalence indexed
endpoint family.
-/
theorem fuelSimulatorStructuredEndpointEquivIndexedConstruction_of_equivComponents
    {attempt : MachineDescription}
    (hcomponents :
      FuelSimulatorStructuredCanonicalEndpointEquivComponentConstruction
        attempt) :
    FuelSimulatorStructuredEndpointEquivIndexedConstruction attempt := by
  rcases hcomponents with ⟨C⟩
  exact
    ⟨C.wrapper,
      fuelSimulatorStructuredInitializedTape,
      fuelSimulatorStructuredLoweredTape attempt,
      C.equivIndexedFamilySpec⟩

end StructuredConstructionTargets

end Computability
end FoC
