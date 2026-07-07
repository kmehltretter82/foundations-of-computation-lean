import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulator

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      Structured3EndpointWrappedConstruction
        (CommonGround.ControllerInvocation.StageAttemptFramedExactSpec
          attempt)

/--
Index for framed invocation endpoint runs: a controller layout, a boolean-word
result, and a concrete fuel witness for the underlying attempt run.
-/
structure StageAttemptFramedStructuredIndex
    (attempt : MachineDescription) where
  C : DovetailControllerLayout
  result : Word Bool
  fuel : Nat
  attempt_halts :
    attempt.HaltsWithOutputIn fuel
      (encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageInputCode C))
      (encodeCodeWordAsInput (encodeBoolWord result))

def stageAttemptFramedStructuredInputTape
    {attempt : MachineDescription}
    (i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  Tape.input
    (encodeCodeWordAsInput
      (DovetailControllerLayout.encode i.C))

def stageAttemptFramedStructuredOutputTape
    {attempt : MachineDescription}
    (i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
    i.C i.result

def StageAttemptFramedStructuredEndpointExactIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered :
      StageAttemptFramedStructuredIndex attempt -> Tape Bool,
    Structured3EndpointExactIndexedFamilySpec
      W
      stageAttemptFramedStructuredInputTape
      initialized
      lowered
      stageAttemptFramedStructuredOutputTape

/--
Canonical blank output buffer used when materializing framed-invocation public
inputs into the three-logical-tape core.
-/
def stageAttemptFramedStructuredOutputBuffer
    {attempt : MachineDescription}
    (_i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  Tape.blank

/--
Canonical endpoint input to the lowered framed-invocation structured core.

Tape 0 contains the public controller-layout input, tape 1 is blank scratch,
and tape 2 starts as a blank output buffer.
-/
def stageAttemptFramedStructuredInitializedTape
    {attempt : MachineDescription}
    (i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (stageAttemptFramedStructuredInputTape i)
    (stageAttemptFramedStructuredOutputBuffer i)

/--
Canonical endpoint output of the lowered framed-invocation structured core.

The core preserves the source layout on logical tape 0, keeps tape 1 blank, and
writes the exact framed controller-output tape on logical tape 2.
-/
def stageAttemptFramedStructuredLoweredTape
    {attempt : MachineDescription}
    (i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (stageAttemptFramedStructuredInputTape i)
    Tape.blank
    (stageAttemptFramedStructuredOutputTape i)

/--
Exact materializer behavior needed by the canonical framed-invocation endpoint.
-/
def StageAttemptFramedStructuredExactMaterializerSpec
    (attempt : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointExactMaterializerSpec
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    materializer

/--
Target-specific framed-invocation materializer obligation before deterministic
per-input exact closedness is installed by the shared endpoint infrastructure.
-/
def StageAttemptFramedStructuredIndexedMaterializerSpec
    (attempt : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerSpec
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    materializer

/--
Exact lowered-core behavior for the canonical framed-invocation endpoint.
-/
def StageAttemptFramedStructuredExactLoweredCoreSpec
    (attempt : MachineDescription)
    (lowered : MachineDescription) : Prop :=
  Structured3EndpointExactLoweredCoreSpec
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    lowered

/--
Exact projector behavior for the canonical framed-invocation endpoint.
-/
def StageAttemptFramedStructuredExactProjectorSpec
    (attempt : MachineDescription)
    (projector : MachineDescription) : Prop :=
  Structured3EndpointExactProjectorSpec
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    projector

/--
Canonical component-level framed-invocation endpoint spec.
-/
def StageAttemptFramedStructuredCanonicalEndpointSpec
    (attempt : MachineDescription)
    (W : Structured3EndpointWrapper) : Prop :=
  Structured3CanonicalExactIndexedEndpointSpec
    W
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)

/--
Canonical framed-invocation endpoint construction with fixed
materializer/core/projector handoff tapes.
-/
def StageAttemptFramedStructuredCanonicalEndpointConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    StageAttemptFramedStructuredCanonicalEndpointSpec attempt W

/--
Concrete component data for the canonical framed-invocation endpoint.

The indexed input family includes the proof that the delegated attempt halts
with the boolean-word result, so the structured core only has to handle the
closed framed wrapper contract at that witnessed endpoint.
-/
def StageAttemptFramedStructuredCanonicalEndpointComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointComponents
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)

/--
Existence form of the concrete framed-invocation endpoint components.
-/
def StageAttemptFramedStructuredCanonicalEndpointComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointComponentConstruction
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)

/--
Concrete framed-invocation components imply the canonical wrapper endpoint
construction consumed by the public scaffold adapter.
-/
theorem stageAttemptFramedStructuredCanonicalEndpointConstruction_of_components
    {attempt : MachineDescription}
    (hcomponents :
      StageAttemptFramedStructuredCanonicalEndpointComponentConstruction
        attempt) :
    StageAttemptFramedStructuredCanonicalEndpointConstruction
      attempt := by
  simpa [StageAttemptFramedStructuredCanonicalEndpointConstruction,
    StageAttemptFramedStructuredCanonicalEndpointSpec,
    StageAttemptFramedStructuredCanonicalEndpointComponentConstruction] using
    structured3CanonicalExactIndexedEndpointConstruction_of_components
      hcomponents

/--
Framed-invocation component data with the output projector factored through
the shared exact tape-2 projector route.
-/
def StageAttemptFramedStructuredCanonicalEndpointSharedProjectorComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointSharedProjectorComponents
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Existence form of the shared-projector framed-invocation endpoint components.
-/
def StageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointSharedProjectorConstruction
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Framed-invocation parser/core components before installing the shared exact
tape-2 projector.
-/
def StageAttemptFramedStructuredCanonicalEndpointCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointCoreComponents
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Existence form for framed-invocation parser/core components without the
reusable endpoint projector.
-/
def StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointCoreComponentConstruction
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Framed-invocation input parser/materializer construction, separated from the
lowered structured framed wrapper core.
-/
def StageAttemptFramedStructuredIndexedMaterializerConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)

/--
Framed-invocation lowered structured core data after input materialization.
-/
def StageAttemptFramedStructuredLoweredCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointLoweredCoreComponents
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Existence form for the framed-invocation lowered structured core.
-/
def StageAttemptFramedStructuredLoweredCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointLoweredCoreConstruction
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Combine the framed-invocation parser/materializer and lowered core into the
no-projector endpoint component obligation.
-/
theorem stageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    {attempt : MachineDescription}
    (hmaterializer :
      StageAttemptFramedStructuredIndexedMaterializerConstruction
        attempt)
    (hcore :
      StageAttemptFramedStructuredLoweredCoreConstruction attempt) :
    StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction
      attempt := by
  simpa [StageAttemptFramedStructuredIndexedMaterializerConstruction,
    StageAttemptFramedStructuredLoweredCoreConstruction,
    StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction] using
    structured3CanonicalExactEndpointCoreComponentConstruction_of_materializer_loweredCore
      hmaterializer hcore

/--
Finite-table leaf for the framed-invocation public-input materializer.
-/
theorem stageAttemptFramedStructuredIndexedMaterializerConstruction_core
    (attempt : MachineDescription) :
    StageAttemptFramedStructuredIndexedMaterializerConstruction
      attempt := by
  -- Remaining parser/materializer obligation: recognize controller layout
  -- inputs and materialize the guarded three-logical-tape input.
  sorry

/--
Finite-table leaf for the lowered framed-invocation structured core.
-/
theorem stageAttemptFramedStructuredLoweredCoreConstruction_core
    (attempt : MachineDescription)
    (_hattempt : attempt.SubroutineReady) :
    StageAttemptFramedStructuredLoweredCoreConstruction attempt := by
  -- Remaining structured-core obligation: install the witnessed
  -- boolean-word result on logical tape 2.
  sorry

/--
Target-local parser/core obligation for the framed-invocation target.  The
public endpoint theorem below only composes this with the shared exact tape-2
projector.
-/
theorem stageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction_core
    (attempt : MachineDescription)
    (hattempt : attempt.SubroutineReady) :
    StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction
      attempt :=
  stageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    (stageAttemptFramedStructuredIndexedMaterializerConstruction_core
      attempt)
    (stageAttemptFramedStructuredLoweredCoreConstruction_core
      attempt hattempt)

/--
Install the shared exact tape-2 projector into framed-invocation core
components.
-/
theorem stageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
    {attempt : MachineDescription}
    (hcore :
      StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction
        attempt)
    (hprojector :
      Structured3EndpointExactTape2ProjectorConstruction) :
    StageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction
      attempt := by
  simpa [
    StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction,
    StageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointSharedProjectorConstruction_of_coreComponents
      hcore hprojector

/--
Shared-projector framed-invocation components imply ordinary concrete
endpoint components.
-/
theorem stageAttemptFramedStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
    {attempt : MachineDescription}
    (hcomponents :
      StageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction
        attempt) :
    StageAttemptFramedStructuredCanonicalEndpointComponentConstruction
      attempt := by
  simpa [StageAttemptFramedStructuredCanonicalEndpointComponentConstruction,
    StageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointComponentConstruction_of_sharedProjector
      hcomponents

theorem stageAttemptFramedStructuredExactIndexedSpec_of_canonical
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    (hspec :
      StageAttemptFramedStructuredCanonicalEndpointSpec attempt W) :
    Structured3EndpointExactIndexedFamilySpec
      (ι := StageAttemptFramedStructuredIndex attempt)
      W
      (fun i => stageAttemptFramedStructuredInputTape i)
      (fun i => stageAttemptFramedStructuredInitializedTape i)
      (fun i => stageAttemptFramedStructuredLoweredTape i)
      (fun i => stageAttemptFramedStructuredOutputTape i) :=
  structured3EndpointExactIndexedFamilySpec_of_canonical hspec

theorem stageAttemptFramedStructuredEndpointExactIndexedConstruction_of_canonical
    {attempt : MachineDescription}
    (hcanonical :
      StageAttemptFramedStructuredCanonicalEndpointConstruction attempt) :
    StageAttemptFramedStructuredEndpointExactIndexedConstruction
      attempt := by
  rcases hcanonical with ⟨W, hspec⟩
  exact
    ⟨W,
      stageAttemptFramedStructuredInitializedTape,
      stageAttemptFramedStructuredLoweredTape,
      stageAttemptFramedStructuredExactIndexedSpec_of_canonical hspec⟩

/--
Remaining structured-core endpoint obligation for framed stage-attempt
invocation.  The attempt readiness hypothesis is part of the target contract.
-/
def StageAttemptFramedStructuredCoreEndpointConstruction : Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      StageAttemptFramedStructuredEndpointExactIndexedConstruction attempt

/--
Canonical framed-invocation endpoint obligations imply the existing flexible
exact-indexed core endpoint obligation.
-/
theorem stageAttemptFramedStructuredCoreEndpointConstruction_of_canonical
    (hcanonical :
      forall attempt : MachineDescription,
        attempt.SubroutineReady ->
          StageAttemptFramedStructuredCanonicalEndpointConstruction
            attempt) :
    StageAttemptFramedStructuredCoreEndpointConstruction := by
  intro attempt hattempt
  exact
    stageAttemptFramedStructuredEndpointExactIndexedConstruction_of_canonical
      (hcanonical attempt hattempt)

theorem stageAttemptFramedInput_layout_eq_of_inputTape_eq
    {attempt : MachineDescription}
    {C : DovetailControllerLayout}
    {i : StageAttemptFramedStructuredIndex attempt}
    (h :
      Tape.input
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C)) =
        stageAttemptFramedStructuredInputTape i) :
    C = i.C := by
  apply DovetailControllerLayout.encode_injective
  apply encodeCodeWordAsInput_injective
  exact
    Tape.input_injective
      (by
        simpa [stageAttemptFramedStructuredInputTape] using h)

theorem stageAttemptFramedOutput_result_eq_of_tape_eq
    {attempt : MachineDescription}
    {C : DovetailControllerLayout}
    {result : Word Bool}
    {i : StageAttemptFramedStructuredIndex attempt}
    {T : Tape Bool}
    (hT : T = stageAttemptFramedStructuredOutputTape i)
    (houtput :
      Tape.normalizedOutput T =
        encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult C result)))
    (hC : C = i.C) :
    i.result = result := by
  have hout :
      Tape.normalizedOutput
          (stageAttemptFramedStructuredOutputTape i) =
        encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult i.C i.result)) := by
    simpa [stageAttemptFramedStructuredOutputTape] using
      CommonGround.ControllerInvocation.stageAttemptFramedOutputTape_normalizedOutput
        i.C i.result
  have hbits :
      encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult i.C i.result)) =
        encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult i.C result)) := by
    rw [← hout, ← hT, houtput, hC]
  have hcode :
      DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult i.C i.result) =
        DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult i.C result) :=
    encodeCodeWordAsInput_injective hbits
  have hlayout :
      DovetailControllerLayout.withResult i.C i.result =
        DovetailControllerLayout.withResult i.C result :=
    DovetailControllerLayout.encode_injective hcode
  have hresult := congrArg DovetailControllerLayout.result hlayout
  simpa [DovetailControllerLayout.withResult] using hresult

theorem stageAttemptFramedExactSpec_of_endpointExactIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered :
      StageAttemptFramedStructuredIndex attempt -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W
        stageAttemptFramedStructuredInputTape
        initialized
        lowered
        stageAttemptFramedStructuredOutputTape) :
    CommonGround.ControllerInvocation.StageAttemptFramedExactSpec
      attempt W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro C result fuel hattempt
    let i : StageAttemptFramedStructuredIndex attempt :=
      { C := C
        result := result
        fuel := fuel
        attempt_halts := hattempt }
    simpa [stageAttemptFramedStructuredInputTape,
      stageAttemptFramedStructuredOutputTape, i] using
      haltsWithTape_of_haltsFromTape_input
        (Structured3EndpointExactIndexedFamilySpec.forward hspec i)
  · intro C result hhalt
    let inputBits :=
      encodeCodeWordAsInput
        (DovetailControllerLayout.encode C)
    let outputBits :=
      encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult C result))
    rcases hhalt with ⟨fuel, hhaltFuel⟩
    let T :=
      (W.machine.runConfig fuel (W.machine.initial inputBits)).tape
    have hfrom :
        W.machine.HaltsFromTape (Tape.input inputBits) T := by
      exact
        ⟨fuel,
          by
            rcases hhaltFuel with ⟨hstate, _houtput⟩
            exact ⟨hstate, rfl⟩⟩
    rcases
        Structured3EndpointExactIndexedFamilySpec.closedIndex
          hspec (Tape.input inputBits) T hfrom with
      ⟨i, hinput, hT⟩
    have hC : C = i.C := by
      exact
        stageAttemptFramedInput_layout_eq_of_inputTape_eq
          (attempt := attempt)
          (C := C)
          (i := i)
          (by
            simpa [inputBits] using hinput)
    have houtput :
        Tape.normalizedOutput T =
          encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.withResult C result)) := by
      rcases hhaltFuel with ⟨_hstate, hnormalized⟩
      simpa [T, outputBits] using hnormalized
    have hresult : i.result = result :=
      stageAttemptFramedOutput_result_eq_of_tape_eq
        (attempt := attempt)
        (C := C)
        (result := result)
        (i := i)
        (T := T)
        hT houtput hC
    exact
      ⟨i.fuel,
        by
          simpa [hC, hresult] using i.attempt_halts⟩

theorem stageAttemptFramedStructuredConstruction_of_endpointExactIndexed
    (h :
      forall attempt : MachineDescription,
        attempt.SubroutineReady ->
          StageAttemptFramedStructuredEndpointExactIndexedConstruction
            attempt) :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨W, initialized, lowered, hspec⟩
  exact
    ⟨W,
      stageAttemptFramedExactSpec_of_endpointExactIndexed
        (attempt := attempt)
        (W := W)
        (initialized := initialized)
        (lowered := lowered)
        hspec⟩

theorem stageAttemptFramedStructuredConstruction_of_coreEndpoint
    (h : StageAttemptFramedStructuredCoreEndpointConstruction) :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData :=
  stageAttemptFramedStructuredConstruction_of_endpointExactIndexed h

theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_of_structured
    (h :
      PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData) :
    CommonGround.ControllerInvocation.StageAttemptFramedConstruction := by
  exact
    CommonGround.ControllerInvocation.stageAttemptFramedConstruction_of_exact
      (by
        intro attempt hattempt
        rcases h attempt hattempt with ⟨W, hspec⟩
        exact ⟨W.machine, hspec⟩)

theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData_structuredLeaf :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData := by
  -- Pending migration: rebuild this public exact-output leaf through the
  -- equivalence-facing shared tape-2 projector route instead of the refuted
  -- exact shared projector core.
  sorry


end StructuredConstructionTargets

end Computability
end FoC
