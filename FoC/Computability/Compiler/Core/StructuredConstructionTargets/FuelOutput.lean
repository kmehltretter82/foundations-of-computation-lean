import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def fuelOutputStructuredInputTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  Tape.input
    (encodeCodeWordAsInput
      (PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
        i))

def FuelOutputStructuredEndpointExactIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt -> Tape Bool,
    Structured3EndpointExactIndexedFamilySpec
      W
      fuelOutputStructuredInputTape
      initialized
      lowered
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape

def FuelOutputStructuredEndpointEquivIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt -> Tape Bool,
    Structured3EndpointEquivIndexedFamilySpec
      W
      fuelOutputStructuredInputTape
      initialized
      lowered
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape

/--
Canonical blank output buffer used when materializing a public simulator-layout
input into the three-logical-tape fuel-output extractor core.
-/
def fuelOutputStructuredOutputBuffer
    {attempt : MachineDescription}
    (_i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  Tape.blank

/--
Canonical endpoint input to the lowered fuel-output structured core.

Tape 0 contains the public simulator-layout code, tape 1 is blank scratch, and
tape 2 starts as a blank output buffer.
-/
def fuelOutputStructuredInitializedTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (fuelOutputStructuredInputTape i)
    (fuelOutputStructuredOutputBuffer i)

/--
Canonical endpoint output of the lowered fuel-output structured core.

The structured core preserves the source code on tape 0 for debugging and
closedness accounting, keeps tape 1 blank, and writes the exact public output
tape on logical tape 2.  The endpoint projector then exposes tape 2 as the
public final tape.
-/
def fuelOutputStructuredLoweredTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (fuelOutputStructuredInputTape i)
    Tape.blank
    (PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)

/--
Exact materializer behavior needed by the canonical fuel-output endpoint.
-/
def FuelOutputStructuredExactMaterializerSpec
    (attempt : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointExactMaterializerSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    materializer

/--
Target-specific fuel-output materializer obligation before deterministic
per-input exact closedness is installed by the shared endpoint infrastructure.
-/
def FuelOutputStructuredIndexedMaterializerSpec
    (attempt : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    materializer

/--
Exact lowered-core behavior for the canonical fuel-output endpoint.
-/
def FuelOutputStructuredExactLoweredCoreSpec
    (attempt : MachineDescription)
    (lowered : MachineDescription) : Prop :=
  Structured3EndpointExactLoweredCoreSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    lowered

/--
Canonical component-level fuel-output endpoint spec.

This fixes the endpoint tapes that the remaining structured finite-table proof
must target, while still exposing the reusable exact-indexed endpoint API to
the public scaffold adapters.
-/
def FuelOutputStructuredCanonicalEndpointSpec
    (attempt : MachineDescription)
    (W : Structured3EndpointWrapper) : Prop :=
  Structured3CanonicalExactIndexedEndpointSpec
    W
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)

/--
Canonical fuel-output endpoint construction with fixed materializer/core/
projector handoff tapes.
-/
def FuelOutputStructuredCanonicalEndpointConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    FuelOutputStructuredCanonicalEndpointSpec attempt W

/--
Concrete component data for the canonical fuel-output endpoint.

This is the current first real extractor target from the middle-path plan:
the parser validates a public halted simulator layout, the three-tape core
extracts the result code onto logical tape 2, and the projector exposes that
exact tape as the public output.
-/
def FuelOutputStructuredCanonicalEndpointComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)

/--
Existence form of the concrete fuel-output endpoint components.
-/
def FuelOutputStructuredCanonicalEndpointComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointComponentConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)

/--
Concrete fuel-output components imply the canonical wrapper endpoint
construction consumed by the public scaffold adapter.
-/
theorem fuelOutputStructuredCanonicalEndpointConstruction_of_components
    {attempt : MachineDescription}
    (hcomponents :
      FuelOutputStructuredCanonicalEndpointComponentConstruction
        attempt) :
    FuelOutputStructuredCanonicalEndpointConstruction attempt := by
  simpa [FuelOutputStructuredCanonicalEndpointConstruction,
    FuelOutputStructuredCanonicalEndpointSpec,
    FuelOutputStructuredCanonicalEndpointComponentConstruction] using
    structured3CanonicalExactIndexedEndpointConstruction_of_components
      hcomponents

/--
Fuel-output component data with the output projector factored through the
shared equivalence tape-2 projector route.
-/
def FuelOutputStructuredCanonicalEndpointEquivSharedProjectorComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalEquivEndpointSharedProjectorComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Existence form of the equivalence shared-projector fuel-output endpoint
components.
-/
def FuelOutputStructuredCanonicalEndpointEquivSharedProjectorConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalEquivEndpointSharedProjectorConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Fuel-output parser/core components before installing the shared tape-2
projector.
-/
def FuelOutputStructuredCanonicalEndpointCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointCoreComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Existence form for fuel-output parser/core components without the reusable
endpoint projector.
-/
def FuelOutputStructuredCanonicalEndpointCoreComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointCoreComponentConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Fuel-output input parser/materializer construction, separated from the lowered
structured extractor core.
-/
def FuelOutputStructuredIndexedMaterializerConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)

/--
Fuel-output lowered structured extractor core data after input materialization.
-/
def FuelOutputStructuredLoweredCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointLoweredCoreComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Existence form for the fuel-output lowered structured extractor core.
-/
def FuelOutputStructuredLoweredCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointLoweredCoreConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Combine the fuel-output parser/materializer and lowered extractor core into
the no-projector endpoint component obligation.
-/
theorem fuelOutputStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    {attempt : MachineDescription}
    (hmaterializer :
      FuelOutputStructuredIndexedMaterializerConstruction
        attempt)
    (hcore :
      FuelOutputStructuredLoweredCoreConstruction attempt) :
    FuelOutputStructuredCanonicalEndpointCoreComponentConstruction
      attempt := by
  simpa [FuelOutputStructuredIndexedMaterializerConstruction,
    FuelOutputStructuredLoweredCoreConstruction,
    FuelOutputStructuredCanonicalEndpointCoreComponentConstruction] using
    structured3CanonicalExactEndpointCoreComponentConstruction_of_materializer_loweredCore
      hmaterializer hcore

/--
Finite-table leaf for the fuel-output public-input materializer.
-/
theorem fuelOutputStructuredIndexedMaterializerConstruction_core
    (attempt : MachineDescription) :
    FuelOutputStructuredIndexedMaterializerConstruction
      attempt := by
  -- Remaining parser/materializer obligation: recognize halted simulator
  -- layouts and materialize the guarded three-logical-tape input.
  sorry

/--
Finite-table leaf for the lowered fuel-output structured core.
-/
theorem fuelOutputStructuredLoweredCoreConstruction_core
    (attempt : MachineDescription) :
    FuelOutputStructuredLoweredCoreConstruction attempt := by
  -- Remaining structured-core obligation: extract the normalized
  -- boolean-word result code onto logical tape 2.
  sorry

/--
Target-local parser/core obligation for the fuel-output target.  The public
endpoint theorem below only composes this with a shared tape-2
projector.
-/
theorem fuelOutputStructuredCanonicalEndpointCoreComponentConstruction_core
    (attempt : MachineDescription) :
    FuelOutputStructuredCanonicalEndpointCoreComponentConstruction
      attempt :=
  fuelOutputStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    (fuelOutputStructuredIndexedMaterializerConstruction_core attempt)
    (fuelOutputStructuredLoweredCoreConstruction_core attempt)

/--
Install the shared equivalence tape-2 projector into fuel-output core
components.
-/
theorem fuelOutputStructuredCanonicalEndpointEquivSharedProjectorConstruction_of_coreComponents
    {attempt : MachineDescription}
    (hcore :
      FuelOutputStructuredCanonicalEndpointCoreComponentConstruction
        attempt)
    (hprojector :
      Structured3EndpointTape2ProjectorConstruction) :
    FuelOutputStructuredCanonicalEndpointEquivSharedProjectorConstruction
      attempt := by
  simpa [FuelOutputStructuredCanonicalEndpointCoreComponentConstruction,
    FuelOutputStructuredCanonicalEndpointEquivSharedProjectorConstruction] using
    structured3CanonicalEquivEndpointSharedProjectorConstruction_of_coreComponents
      hcore hprojector

/--
Equivalence shared-projector fuel-output components imply the equivalence
indexed endpoint family.
-/
theorem fuelOutputStructuredEndpointEquivIndexedConstruction_of_equivSharedProjector
    {attempt : MachineDescription}
    (hcomponents :
      FuelOutputStructuredCanonicalEndpointEquivSharedProjectorConstruction
        attempt) :
    FuelOutputStructuredEndpointEquivIndexedConstruction attempt := by
  rcases hcomponents with ⟨C⟩
  exact
    ⟨C.wrapper,
      fuelOutputStructuredInitializedTape,
      fuelOutputStructuredLoweredTape,
      C.equivIndexedFamilySpec⟩

/--
Equivalence-facing fuel-output endpoint assembled from the parser/core
components and the shared equivalence tape-2 projector.
-/
theorem fuelOutputStructuredEndpointEquivIndexedConstruction_core
    (attempt : MachineDescription) :
    FuelOutputStructuredEndpointEquivIndexedConstruction attempt :=
  fuelOutputStructuredEndpointEquivIndexedConstruction_of_equivSharedProjector
    (fuelOutputStructuredCanonicalEndpointEquivSharedProjectorConstruction_of_coreComponents
      (fuelOutputStructuredCanonicalEndpointCoreComponentConstruction_core
        attempt)
      structured3EndpointTape2ProjectorConstruction_core)

theorem fuelOutputStructuredExactIndexedSpec_of_canonical
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    (hspec :
      FuelOutputStructuredCanonicalEndpointSpec attempt W) :
    Structured3EndpointExactIndexedFamilySpec
      (ι :=
        PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
          attempt)
      W
      (fun i => fuelOutputStructuredInputTape i)
      (fun i => fuelOutputStructuredInitializedTape i)
      (fun i => fuelOutputStructuredLoweredTape i)
      (fun i =>
        PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i) :=
  structured3EndpointExactIndexedFamilySpec_of_canonical hspec

theorem fuelOutputStructuredEndpointExactIndexedConstruction_of_canonical
    {attempt : MachineDescription}
    (hcanonical :
      FuelOutputStructuredCanonicalEndpointConstruction attempt) :
    FuelOutputStructuredEndpointExactIndexedConstruction attempt := by
  rcases hcanonical with ⟨W, hspec⟩
  exact
    ⟨W,
      fuelOutputStructuredInitializedTape,
      fuelOutputStructuredLoweredTape,
      fuelOutputStructuredExactIndexedSpec_of_canonical hspec⟩

/--
Remaining structured-core endpoint obligation for the simulator-output
extractor, indexed by halted simulator layouts and their exact output code.
-/
def FuelOutputStructuredCoreEndpointConstruction : Prop :=
  forall attempt : MachineDescription,
    FuelOutputStructuredEndpointExactIndexedConstruction attempt

/--
Canonical fuel-output endpoint obligations imply the existing flexible
exact-indexed core endpoint obligation.
-/
theorem fuelOutputStructuredCoreEndpointConstruction_of_canonical
    (hcanonical :
      forall attempt : MachineDescription,
        FuelOutputStructuredCanonicalEndpointConstruction attempt) :
    FuelOutputStructuredCoreEndpointConstruction := by
  intro attempt
  exact
    fuelOutputStructuredEndpointExactIndexedConstruction_of_canonical
      (hcanonical attempt)

theorem fuelOutputInputCode_eq_of_inputTape_eq
    {attempt : MachineDescription}
    {code : Word MachineCodeSymbol}
    {i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt}
    (h :
      Tape.input (encodeCodeWordAsInput code) =
        fuelOutputStructuredInputTape i) :
    code =
      PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
        i := by
  apply encodeCodeWordAsInput_injective
  exact
    Tape.input_injective
      (by
        simpa [fuelOutputStructuredInputTape] using h)

theorem fuelOutputCodeSubroutineSpec_of_endpointExactIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W
        fuelOutputStructuredInputTape
        initialized
        lowered
        PairedRecognizerDovetailControllerStageAttemptFuelOutputTape) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
      attempt W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro i
    simpa [fuelOutputStructuredInputTape] using
      haltsWithTape_of_haltsFromTape_input
        (Structured3EndpointExactIndexedFamilySpec.forward hspec i)
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
    have hcode :
        code =
          PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
            i :=
      fuelOutputInputCode_eq_of_inputTape_eq hinput
    exact ⟨i, hcode, hT⟩

def PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction :
    Prop :=
  forall attempt : MachineDescription,
    Structured3EndpointWrappedConstruction
      (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
        attempt)

theorem fuelOutputStructuredConstruction_of_endpointExactIndexed
    (h :
      forall attempt : MachineDescription,
        FuelOutputStructuredEndpointExactIndexedConstruction attempt) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction := by
  intro attempt
  rcases h attempt with ⟨W, initialized, lowered, hspec⟩
  exact
    ⟨W,
      fuelOutputCodeSubroutineSpec_of_endpointExactIndexed
        (attempt := attempt)
        (W := W)
        (initialized := initialized)
        (lowered := lowered)
        hspec⟩

theorem fuelOutputStructuredConstruction_of_coreEndpoint
    (h : FuelOutputStructuredCoreEndpointConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction :=
  fuelOutputStructuredConstruction_of_endpointExactIndexed h

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction := by
  exact
    pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_spec
      (by
        intro attempt
        rcases h attempt with ⟨W, hspec⟩
        exact ⟨W.machine, hspec⟩)

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction_structuredLeaf :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction := by
  -- Legacy exact-output public leaf.  The cleanup route now has
  -- `fuelOutputStructuredEndpointEquivIndexedConstruction_core`; closing this
  -- equality-based public contract needs either a restricted exact projector
  -- for this target family or a public contract migration.
  sorry


end StructuredConstructionTargets

end Computability
end FoC
