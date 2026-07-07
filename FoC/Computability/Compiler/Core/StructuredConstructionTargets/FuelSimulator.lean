import FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def FuelSimulatorStructuredIndex : Type :=
  Sigma (fun _w : Word Bool => Nat × Nat)

def fuelSimulatorStructuredInputCode
    (i : FuelSimulatorStructuredIndex) : Word MachineCodeSymbol :=
  PairedRecognizerDovetailControllerStageAttemptFuelInputCode
    i.1 i.2.1 i.2.2

def fuelSimulatorStructuredInputTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  Tape.input
    (encodeCodeWordAsInput
      (fuelSimulatorStructuredInputCode i))

def fuelSimulatorStructuredOutputTape
    (attempt : MachineDescription)
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
    attempt i.1 i.2.1 i.2.2

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
Canonical blank output buffer used when materializing public fuel-simulator
parser inputs into the three-logical-tape core.
-/
def fuelSimulatorStructuredOutputBuffer
    (_i : FuelSimulatorStructuredIndex) : Tape Bool :=
  Tape.blank

/--
Canonical endpoint input to the lowered fuel-simulator structured core.

Tape 0 contains the public generated fuel-input code, tape 1 is blank scratch,
and tape 2 starts as a blank output buffer.
-/
def fuelSimulatorStructuredInitializedTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (fuelSimulatorStructuredInputTape i)
    (fuelSimulatorStructuredOutputBuffer i)

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
Exact materializer behavior needed by the canonical fuel-simulator endpoint.
-/
def FuelSimulatorStructuredExactMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointExactMaterializerSpec
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    materializer

/--
Target-specific fuel-simulator materializer obligation before deterministic
per-input exact closedness is installed by the shared endpoint infrastructure.
-/
def FuelSimulatorStructuredIndexedMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerSpec
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    materializer

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
    FuelSimulatorStructuredCanonicalEndpointComponentConstruction] using
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
Fuel-simulator input parser/materializer construction, separated from the
lowered structured simulator core.
-/
def FuelSimulatorStructuredIndexedMaterializerConstruction : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)

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
Finite-table leaf for the fuel-simulator public-input materializer.
-/
theorem fuelSimulatorStructuredIndexedMaterializerConstruction_core :
    FuelSimulatorStructuredIndexedMaterializerConstruction := by
  -- Remaining parser/materializer obligation: recognize generated fuel-input
  -- codes and materialize the guarded three-logical-tape input.
  sorry

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
Target-local parser/core obligation for the fuel-simulator target.  The
public endpoint theorem below only composes this with a shared tape-2
projector.
-/
theorem fuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction_core
    (attempt : MachineDescription) :
    FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction
      attempt :=
  fuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    fuelSimulatorStructuredIndexedMaterializerConstruction_core
    (fuelSimulatorStructuredLoweredCoreConstruction_core attempt)

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

/--
Equivalence-facing fuel-simulator endpoint assembled from the parser/core
components and the shared equivalence tape-2 projector.
-/
theorem fuelSimulatorStructuredEndpointEquivIndexedConstruction_core
    (attempt : MachineDescription) :
    FuelSimulatorStructuredEndpointEquivIndexedConstruction attempt :=
  fuelSimulatorStructuredEndpointEquivIndexedConstruction_of_equivSharedProjector
    (fuelSimulatorStructuredCanonicalEndpointEquivSharedProjectorConstruction_of_coreComponents
      (fuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction_core
        attempt)
      structured3EndpointTape2ProjectorConstruction_core)

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

theorem fuelSimulatorStructuredInputCode_eq_of_inputTape_eq
    {code : Word MachineCodeSymbol}
    {i : FuelSimulatorStructuredIndex}
    (h :
      Tape.input (encodeCodeWordAsInput code) =
        fuelSimulatorStructuredInputTape i) :
    code = fuelSimulatorStructuredInputCode i := by
  apply encodeCodeWordAsInput_injective
  exact
    Tape.input_injective
      (by
        simpa [fuelSimulatorStructuredInputTape] using h)

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
          hspec ⟨w, (limit, fuel)⟩)
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
      ⟨i.1, i.2.1, i.2.2,
        by
          simpa [fuelSimulatorStructuredInputCode] using hcode,
        by
          simpa [fuelSimulatorStructuredOutputTape] using hT⟩

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction :
    Prop :=
  forall attempt : MachineDescription,
    Structured3EndpointWrappedConstruction
      (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpec
        attempt)

theorem fuelSimulatorStructuredConstruction_of_endpointExactIndexed
    (h :
      forall attempt : MachineDescription,
        FuelSimulatorStructuredEndpointExactIndexedConstruction attempt) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction := by
  intro attempt
  rcases h attempt with ⟨W, initialized, lowered, hspec⟩
  exact
    ⟨W,
      fuelSimulatorRightShiftedSpec_of_endpointExactIndexed
        (attempt := attempt)
        (W := W)
        (initialized := initialized)
        (lowered := lowered)
        hspec⟩

theorem fuelSimulatorStructuredConstruction_of_coreEndpoint
    (h : FuelSimulatorStructuredCoreEndpointConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction :=
  fuelSimulatorStructuredConstruction_of_endpointExactIndexed h

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction := by
  exact
    pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction_of_spec
      (by
        intro attempt
        rcases h attempt with ⟨W, hspec⟩
        exact ⟨W.machine, hspec⟩)

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction_structuredLeaf :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction := by
  -- Legacy exact-output public leaf.  The cleanup route now has
  -- `fuelSimulatorStructuredEndpointEquivIndexedConstruction_core`; closing
  -- this equality-based public contract needs either a restricted exact
  -- projector for this target family or a public contract migration.
  sorry


end StructuredConstructionTargets

end Computability
end FoC
