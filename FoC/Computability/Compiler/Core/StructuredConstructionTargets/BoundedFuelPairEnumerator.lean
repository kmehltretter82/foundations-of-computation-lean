import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutput

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def boundedFuelPairEnumeratorStructuredInputTape
    {runner : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  Tape.input i.input

def BoundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction
    (runner : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner -> Tape Bool,
    Structured3EndpointExactIndexedFamilySpec
      W
      boundedFuelPairEnumeratorStructuredInputTape
      initialized
      lowered
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape

/--
Canonical blank output buffer used when materializing bounded fuel-pair
enumerator inputs into the three-logical-tape core.
-/
def boundedFuelPairEnumeratorStructuredOutputBuffer
    {runner : MachineDescription}
    (_i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  Tape.blank

/--
Canonical endpoint input to the lowered bounded fuel-pair enumerator core.

Tape 0 contains the public right-shifted enumerator input, tape 1 is blank
scratch, and tape 2 starts as a blank output buffer.
-/
def boundedFuelPairEnumeratorStructuredInitializedTape
    {runner : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (boundedFuelPairEnumeratorStructuredInputTape i)
    (boundedFuelPairEnumeratorStructuredOutputBuffer i)

/--
Canonical endpoint output of the lowered bounded fuel-pair enumerator core.

The core preserves the public source on logical tape 0, keeps tape 1 blank, and
writes the exact right-shifted enumerator output tape on logical tape 2.
-/
def boundedFuelPairEnumeratorStructuredLoweredTape
    {runner : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (boundedFuelPairEnumeratorStructuredInputTape i)
    Tape.blank
    (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
      i)

/--
Exact materializer behavior needed by the canonical bounded enumerator endpoint.
-/
def BoundedFuelPairEnumeratorStructuredExactMaterializerSpec
    (runner : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointExactMaterializerSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    materializer

/--
Target-specific bounded-enumerator materializer obligation before deterministic
per-input exact closedness is installed by the shared endpoint infrastructure.
-/
def BoundedFuelPairEnumeratorStructuredIndexedMaterializerSpec
    (runner : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    materializer

/--
Exact lowered-core behavior for the canonical bounded enumerator endpoint.
-/
def BoundedFuelPairEnumeratorStructuredExactLoweredCoreSpec
    (runner : MachineDescription)
    (lowered : MachineDescription) : Prop :=
  Structured3EndpointExactLoweredCoreSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    lowered

/--
Exact projector behavior for the canonical bounded enumerator endpoint.
-/
def BoundedFuelPairEnumeratorStructuredExactProjectorSpec
    (runner : MachineDescription)
    (projector : MachineDescription) : Prop :=
  Structured3EndpointExactProjectorSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    projector

/--
Canonical component-level bounded fuel-pair enumerator endpoint spec.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointSpec
    (runner : MachineDescription)
    (W : Structured3EndpointWrapper) : Prop :=
  Structured3CanonicalExactIndexedEndpointSpec
    W
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)

/--
Canonical bounded fuel-pair enumerator endpoint construction with fixed
materializer/core/projector handoff tapes.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction
    (runner : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointSpec runner W

/--
Concrete component data for the canonical bounded fuel-pair enumerator
endpoint.

The structured core is allowed to use the ready exact-fuel runner supplied by
the surrounding leaf obligation, but the public wrapper still has one fixed
parser/core/projector endpoint shape.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponents
    (runner : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)

/--
Existence form of the concrete bounded fuel-pair enumerator endpoint
components.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction
    (runner : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointComponentConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)

/--
Concrete bounded fuel-pair enumerator components imply the canonical wrapper
endpoint construction consumed by the public scaffold adapter.
-/
theorem boundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction_of_components
    {runner : MachineDescription}
    (hcomponents :
      BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction
        runner) :
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction
      runner := by
  simpa [BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointSpec,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction] using
    structured3CanonicalExactIndexedEndpointConstruction_of_components
      hcomponents

/--
Bounded fuel-pair enumerator component data with the output projector factored
through the shared exact tape-2 projector route.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorComponents
    (runner : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointSharedProjectorComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Existence form of the shared-projector bounded fuel-pair enumerator endpoint
components.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction
    (runner : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointSharedProjectorConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Bounded fuel-pair enumerator parser/core components before installing the
shared exact tape-2 projector.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponents
    (runner : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointCoreComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Existence form for bounded fuel-pair enumerator parser/core components without
the reusable endpoint projector.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction
    (runner : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointCoreComponentConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Bounded-enumerator input parser/materializer construction, separated from the
lowered structured enumerator core.
-/
def BoundedFuelPairEnumeratorStructuredIndexedMaterializerConstruction
    (runner : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)

/--
Bounded-enumerator lowered structured core data after input materialization.
-/
def BoundedFuelPairEnumeratorStructuredLoweredCoreComponents
    (runner : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointLoweredCoreComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Existence form for the bounded-enumerator lowered structured core.
-/
def BoundedFuelPairEnumeratorStructuredLoweredCoreConstruction
    (runner : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointLoweredCoreConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Combine the bounded-enumerator parser/materializer and lowered core into the
no-projector endpoint component obligation.
-/
theorem boundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    {runner : MachineDescription}
    (hmaterializer :
      BoundedFuelPairEnumeratorStructuredIndexedMaterializerConstruction
        runner)
    (hcore :
      BoundedFuelPairEnumeratorStructuredLoweredCoreConstruction
        runner) :
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction
      runner := by
  simpa [
    BoundedFuelPairEnumeratorStructuredIndexedMaterializerConstruction,
    BoundedFuelPairEnumeratorStructuredLoweredCoreConstruction,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction] using
    structured3CanonicalExactEndpointCoreComponentConstruction_of_materializer_loweredCore
      hmaterializer hcore

/--
Finite-table leaf for the bounded fuel-pair enumerator target.  This is the
only target-local parser/core obligation; the public endpoint theorem below
only composes it with the shared exact tape-2 projector.
-/
theorem boundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction_core
    (runner : MachineDescription)
    (_hrunner : runner.SubroutineReady) :
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction
      runner := by
  -- Remaining structured finite-table obligation: build the bounded fuel-pair
  -- parser/materializer and structured core that enumerates bounded fuel
  -- pairs, invokes the exact-fuel runner endpoint, and leaves the
  -- right-shifted classifier handoff tape on logical tape 2.
  sorry

/--
Install the shared exact tape-2 projector into bounded fuel-pair enumerator
core components.
-/
theorem boundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
    {runner : MachineDescription}
    (hcore :
      BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction
        runner)
    (hprojector :
      Structured3EndpointExactTape2ProjectorConstruction) :
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction
      runner := by
  simpa [
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointSharedProjectorConstruction_of_coreComponents
      hcore hprojector

/--
Shared-projector bounded fuel-pair enumerator components imply ordinary
concrete endpoint components.
-/
theorem boundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
    {runner : MachineDescription}
    (hcomponents :
      BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction
        runner) :
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction
      runner := by
  simpa [
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointComponentConstruction_of_sharedProjector
      hcomponents

theorem boundedFuelPairEnumeratorStructuredExactIndexedSpec_of_canonical
    {runner : MachineDescription}
    {W : Structured3EndpointWrapper}
    (hspec :
      BoundedFuelPairEnumeratorStructuredCanonicalEndpointSpec runner W) :
    Structured3EndpointExactIndexedFamilySpec
      (ι :=
        PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
          runner)
      W
      (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
      (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
      (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
      (fun i =>
        PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
          i) :=
  structured3EndpointExactIndexedFamilySpec_of_canonical hspec

theorem boundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction_of_canonical
    {runner : MachineDescription}
    (hcanonical :
      BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction
        runner) :
    BoundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction
      runner := by
  rcases hcanonical with ⟨W, hspec⟩
  exact
    ⟨W,
      boundedFuelPairEnumeratorStructuredInitializedTape,
      boundedFuelPairEnumeratorStructuredLoweredTape,
      boundedFuelPairEnumeratorStructuredExactIndexedSpec_of_canonical
        hspec⟩

/--
Remaining structured-core endpoint obligation for bounded {lit}`(limit, fuel)`
enumeration against a ready exact-fuel runner.
-/
def BoundedFuelPairEnumeratorStructuredCoreEndpointConstruction
    (runner : MachineDescription) : Prop :=
    runner.SubroutineReady ->
    BoundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction
      runner

/--
Canonical bounded fuel-pair enumerator endpoint obligations imply the existing
flexible exact-indexed core endpoint obligation.
-/
theorem boundedFuelPairEnumeratorStructuredCoreEndpointConstruction_of_canonical
    (hcanonical :
      forall runner : MachineDescription,
        runner.SubroutineReady ->
          BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction
            runner) :
    forall runner : MachineDescription,
      BoundedFuelPairEnumeratorStructuredCoreEndpointConstruction runner := by
  intro runner hrunner
  exact
    boundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction_of_canonical
      (hcanonical runner hrunner)

theorem boundedFuelPairEnumeratorInput_eq_of_inputTape_eq
    {runner : MachineDescription}
    {w : Word Bool}
    {i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner}
    (h :
      Tape.input w =
        boundedFuelPairEnumeratorStructuredInputTape i) :
    w = i.input := by
  exact
    Tape.input_injective
      (by
        simpa [boundedFuelPairEnumeratorStructuredInputTape] using h)

theorem boundedFuelPairEnumeratorRightShiftedSpec_of_endpointExactIndexed
    {runner : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W
        boundedFuelPairEnumeratorStructuredInputTape
        initialized
        lowered
        PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpec
      runner W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro i
    simpa [boundedFuelPairEnumeratorStructuredInputTape] using
      haltsWithTape_of_haltsFromTape_input
        (Structured3EndpointExactIndexedFamilySpec.forward hspec i)
  · intro w T hhalt
    have hfrom :
        W.machine.HaltsFromTape (Tape.input w) T :=
      haltsFromTape_input_of_haltsWithTape hhalt
    rcases
        Structured3EndpointExactIndexedFamilySpec.closedIndex
          hspec (Tape.input w) T hfrom with
      ⟨i, hinput, hT⟩
    have hw : w = i.input :=
      boundedFuelPairEnumeratorInput_eq_of_inputTape_eq hinput
    exact ⟨i, hw, hT⟩

def PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction :
    Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      Structured3EndpointWrappedConstruction
        (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpec
          runner)

theorem boundedFuelPairEnumeratorStructuredConstruction_of_endpointExactIndexed
    (h :
      forall runner : MachineDescription,
        runner.SubroutineReady ->
          BoundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction
            runner) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction := by
  intro runner hrunner
  rcases h runner hrunner with ⟨W, initialized, lowered, hspec⟩
  exact
    ⟨W,
      boundedFuelPairEnumeratorRightShiftedSpec_of_endpointExactIndexed
        (runner := runner)
        (W := W)
        (initialized := initialized)
        (lowered := lowered)
        hspec⟩

theorem boundedFuelPairEnumeratorStructuredConstruction_of_coreEndpoint
    (h :
      forall runner : MachineDescription,
        BoundedFuelPairEnumeratorStructuredCoreEndpointConstruction
          runner) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction :=
  boundedFuelPairEnumeratorStructuredConstruction_of_endpointExactIndexed h

theorem pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction := by
  intro runner hrunner
  rcases h runner hrunner with ⟨W, hspec⟩
  exact ⟨W.machine, hspec⟩

theorem pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction_structuredLeaf :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction := by
  exact
    boundedFuelPairEnumeratorStructuredConstruction_of_coreEndpoint
      (boundedFuelPairEnumeratorStructuredCoreEndpointConstruction_of_canonical
        (by
          intro runner hrunner
          exact
            boundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction_of_components
              (boundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
                (boundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
                  (boundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction_core
                    runner hrunner)
                  structured3EndpointExactTape2ProjectorConstruction_core))))


end StructuredConstructionTargets

end Computability
end FoC
