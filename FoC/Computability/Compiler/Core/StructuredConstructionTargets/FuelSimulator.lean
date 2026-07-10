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

def FuelSimulatorStructuredEndpointExactIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered : FuelSimulatorStructuredIndex -> Tape Bool,
    Structured3EndpointExactIndexedFamilySpec
      W
      fuelSimulatorStructuredInputTape
      initialized
      lowered
      (fuelSimulatorStructuredOutputTape attempt)

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
Exact lowered-core behavior for the canonical fuel-simulator endpoint.
-/
def FuelSimulatorStructuredExactLoweredCoreSpec
    (attempt : MachineDescription)
    (lowered : MachineDescription) : Prop :=
  Structured3EndpointExactLoweredCoreSpec
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    lowered

/--
Canonical component-level fuel-simulator endpoint spec.
-/
def FuelSimulatorStructuredCanonicalEndpointSpec
    (attempt : MachineDescription)
    (W : Structured3EndpointWrapper) : Prop :=
  Structured3CanonicalExactIndexedEndpointSpec
    W
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)

/--
Canonical fuel-simulator endpoint construction with fixed materializer/core/
projector handoff tapes.
-/
def FuelSimulatorStructuredCanonicalEndpointConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    FuelSimulatorStructuredCanonicalEndpointSpec attempt W

/--
Concrete component data for the canonical fuel-simulator endpoint.

This is the finite-table construction target: an indexed public-input parser,
one three-tape structured core, and an exact tape-2 projector.
-/
def FuelSimulatorStructuredCanonicalEndpointComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)

/--
Existence form of the concrete fuel-simulator endpoint components.
-/
def FuelSimulatorStructuredCanonicalEndpointComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointComponentConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)

/--
Concrete fuel-simulator components imply the canonical wrapper endpoint
construction consumed by the public scaffold adapter.
-/
theorem fuelSimulatorStructuredCanonicalEndpointConstruction_of_components
    {attempt : MachineDescription}
    (hcomponents :
      FuelSimulatorStructuredCanonicalEndpointComponentConstruction
        attempt) :
    FuelSimulatorStructuredCanonicalEndpointConstruction attempt := by
  simpa [FuelSimulatorStructuredCanonicalEndpointConstruction,
    FuelSimulatorStructuredCanonicalEndpointSpec,
    FuelSimulatorStructuredCanonicalEndpointComponentConstruction] using!
    structured3CanonicalExactIndexedEndpointConstruction_of_components
      hcomponents

/--
Fuel-simulator component data with the output projector factored through the
shared equivalence tape-2 projector route.
-/
def FuelSimulatorStructuredCanonicalEndpointEquivSharedProjectorComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalEquivEndpointSharedProjectorComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Existence form of the equivalence shared-projector fuel-simulator endpoint
components.
-/
def FuelSimulatorStructuredCanonicalEndpointEquivSharedProjectorConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalEquivEndpointSharedProjectorConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Fuel-simulator parser/core components before installing the shared
tape-2 projector.
-/
def FuelSimulatorStructuredCanonicalEndpointCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointCoreComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Existence form for the fuel-simulator parser/core components without the
reusable endpoint projector.
-/
def FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointCoreComponentConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Fuel-simulator lowered structured core data after input materialization.
-/
def FuelSimulatorStructuredLoweredCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointLoweredCoreComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Existence form for the fuel-simulator lowered structured core.
-/
def FuelSimulatorStructuredLoweredCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointLoweredCoreConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

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
The existing exact lowered-core obligation feeds the equivalence-facing lowered
core contract.
-/
theorem fuelSimulatorStructuredEquivLoweredCoreConstruction_of_loweredCore
    {attempt : MachineDescription}
    (hcore :
      FuelSimulatorStructuredLoweredCoreConstruction attempt) :
    FuelSimulatorStructuredEquivLoweredCoreConstruction attempt := by
  simpa [FuelSimulatorStructuredLoweredCoreConstruction,
    FuelSimulatorStructuredEquivLoweredCoreConstruction] using
    structured3CanonicalEquivEndpointLoweredCoreConstruction_of_exact
      hcore

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
Combine the fuel-simulator parser/materializer and lowered core into the
no-projector endpoint component obligation.
-/
theorem fuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    {attempt : MachineDescription}
    (hmaterializer :
      FuelSimulatorStructuredIndexedMaterializerConstruction)
    (hcore :
      FuelSimulatorStructuredLoweredCoreConstruction attempt) :
    FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction
      attempt := by
  simpa [FuelSimulatorStructuredIndexedMaterializerConstruction,
    FuelSimulatorStructuredLoweredCoreConstruction,
    FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction] using
    structured3CanonicalExactEndpointCoreComponentConstruction_of_materializer_loweredCore
      hmaterializer hcore

/--
Finite-table leaf for the lowered fuel-simulator structured core.
-/
theorem fuelSimulatorStructuredLoweredCoreConstruction_core
    (attempt : MachineDescription) :
    FuelSimulatorStructuredLoweredCoreConstruction attempt := by
  -- Remaining structured-core obligation: run the simulator core and leave
  -- the exact simulator-layout output on logical tape 2.
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

/--
Install the shared equivalence tape-2 projector into fuel-simulator core
components.
-/
theorem fuelSimulatorStructuredCanonicalEndpointEquivSharedProjectorConstruction_of_coreComponents
    {attempt : MachineDescription}
    (hcore :
      FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction
        attempt)
    (hprojector :
      Structured3EndpointTape2ProjectorConstruction) :
    FuelSimulatorStructuredCanonicalEndpointEquivSharedProjectorConstruction
      attempt := by
  simpa [FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction,
    FuelSimulatorStructuredCanonicalEndpointEquivSharedProjectorConstruction] using
    structured3CanonicalEquivEndpointSharedProjectorConstruction_of_coreComponents
      hcore hprojector

/--
Equivalence shared-projector fuel-simulator components imply the equivalence
indexed endpoint family.
-/
theorem fuelSimulatorStructuredEndpointEquivIndexedConstruction_of_equivSharedProjector
    {attempt : MachineDescription}
    (hcomponents :
      FuelSimulatorStructuredCanonicalEndpointEquivSharedProjectorConstruction
        attempt) :
    FuelSimulatorStructuredEndpointEquivIndexedConstruction attempt := by
  rcases hcomponents with ⟨C⟩
  exact
    ⟨C.wrapper,
      fuelSimulatorStructuredInitializedTape,
      fuelSimulatorStructuredLoweredTape attempt,
      C.equivIndexedFamilySpec⟩

theorem fuelSimulatorStructuredExactIndexedSpec_of_canonical
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    (hspec :
      FuelSimulatorStructuredCanonicalEndpointSpec attempt W) :
    Structured3EndpointExactIndexedFamilySpec
      (ι := FuelSimulatorStructuredIndex)
      W
      (fun i => fuelSimulatorStructuredInputTape i)
      (fun i => fuelSimulatorStructuredInitializedTape i)
      (fun i => fuelSimulatorStructuredLoweredTape attempt i)
      (fun i => fuelSimulatorStructuredOutputTape attempt i) :=
  structured3EndpointExactIndexedFamilySpec_of_canonical hspec

theorem fuelSimulatorStructuredEndpointExactIndexedConstruction_of_canonical
    {attempt : MachineDescription}
    (hcanonical :
      FuelSimulatorStructuredCanonicalEndpointConstruction attempt) :
    FuelSimulatorStructuredEndpointExactIndexedConstruction attempt := by
  rcases hcanonical with ⟨W, hspec⟩
  exact
    ⟨W,
      fuelSimulatorStructuredInitializedTape,
      fuelSimulatorStructuredLoweredTape attempt,
      fuelSimulatorStructuredExactIndexedSpec_of_canonical hspec⟩

/--
Remaining structured-core endpoint obligation for the fuel-simulator parser.
The proof must build the wrapped endpoint for every compiled attempt machine.
-/
def FuelSimulatorStructuredCoreEndpointConstruction : Prop :=
  forall attempt : MachineDescription,
    FuelSimulatorStructuredEndpointExactIndexedConstruction attempt

/--
Canonical fuel-simulator endpoint obligations imply the existing flexible
exact-indexed core endpoint obligation.
-/
theorem fuelSimulatorStructuredCoreEndpointConstruction_of_canonical
    (hcanonical :
      forall attempt : MachineDescription,
        FuelSimulatorStructuredCanonicalEndpointConstruction attempt) :
    FuelSimulatorStructuredCoreEndpointConstruction := by
  intro attempt
  exact
    fuelSimulatorStructuredEndpointExactIndexedConstruction_of_canonical
      (hcanonical attempt)

theorem fuelSimulatorRightShiftedSpec_of_endpointExactIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered : FuelSimulatorStructuredIndex -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W
        fuelSimulatorStructuredInputTape
        initialized
        lowered
        (fuelSimulatorStructuredOutputTape attempt)) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpec
      attempt W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro w limit fuel
    simpa [fuelSimulatorStructuredInputTape,
      fuelSimulatorStructuredInputCode,
      fuelSimulatorStructuredOutputTape] using
      haltsWithTape_of_haltsFromTape_input
        (Structured3EndpointExactIndexedFamilySpec.forward
          hspec ⟨w, limit, fuel⟩)
  · intro code T hhalt
    have hfrom :
        W.machine.HaltsFromTape
          (Tape.input (encodeCodeWordAsInput code)) T :=
      haltsFromTape_input_of_haltsWithTape hhalt
    rcases
        Structured3EndpointExactIndexedFamilySpec.closedIndex
          hspec
          (Tape.input (encodeCodeWordAsInput code)) T
          hfrom with
      ⟨i, hinput, hT⟩
    have hcode : code = fuelSimulatorStructuredInputCode i :=
      fuelSimulatorStructuredInputCode_eq_of_inputTape_eq hinput
    exact
      ⟨i.w, i.limit, i.fuel,
        by
          simpa [fuelSimulatorStructuredInputCode] using hcode,
        by
          simpa [fuelSimulatorStructuredOutputTape] using hT⟩

end StructuredConstructionTargets

end Computability
end FoC
