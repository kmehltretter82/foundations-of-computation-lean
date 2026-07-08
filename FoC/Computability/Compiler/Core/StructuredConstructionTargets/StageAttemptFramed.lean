import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulator
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.EndpointMacro

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

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

declare_structured_endpoint
  Prefix: StageAttemptFramedStructured
  lowerPrefix: stageAttemptFramedStructured
  Param: (attempt : MachineDescription)
  Index: StageAttemptFramedStructuredIndex attempt
  InputTape: stageAttemptFramedStructuredInputTape
  OutputTape: stageAttemptFramedStructuredOutputTape

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
public endpoint theorem below only composes this with a shared tape-2
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

theorem stageAttemptFramedOutput_result_eq_of_tape_equiv
    {attempt : MachineDescription}
    {C : DovetailControllerLayout}
    {result : Word Bool}
    {i : StageAttemptFramedStructuredIndex attempt}
    {T : Tape Bool}
    (hT : Tape.Equiv T (stageAttemptFramedStructuredOutputTape i))
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
    rw [← hout, ← Tape.Equiv.normalizedOutput_eq hT, houtput, hC]
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

theorem stageAttemptFramedRealizes_of_endpointEquivIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered :
      StageAttemptFramedStructuredIndex attempt -> Tape Bool}
    (hspec :
      Structured3EndpointEquivIndexedFamilySpec
        W
        stageAttemptFramedStructuredInputTape
        initialized
        lowered
        stageAttemptFramedStructuredOutputTape) :
    CommonGround.ControllerInvocation.StageAttemptFramedRealizes
      attempt W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro C result hrun
    rcases hrun with ⟨fuel, hattempt⟩
    let i : StageAttemptFramedStructuredIndex attempt :=
      { C := C
        result := result
        fuel := fuel
        attempt_halts := hattempt }
    have hforward :=
      MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
        (Structured3EndpointEquivIndexedFamilySpec.forward hspec i)
    simpa [MachineDescription.HaltsWithOutput,
      MachineDescription.HaltsFromTapeWithOutput,
      MachineDescription.HaltsWithOutputIn,
      MachineDescription.HaltsFromTapeWithOutputIn,
      MachineDescription.initial,
      stageAttemptFramedStructuredInputTape,
      stageAttemptFramedStructuredOutputTape,
      CommonGround.ControllerInvocation.stageAttemptFramedOutputTape_normalizedOutput,
      i] using hforward
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
        Structured3EndpointEquivIndexedFamilySpec.closedIndex
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
      stageAttemptFramedOutput_result_eq_of_tape_equiv
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

theorem stageAttemptFramedConstruction_of_endpointEquivIndexed
    (h :
      forall attempt : MachineDescription,
        attempt.SubroutineReady ->
          StageAttemptFramedStructuredEndpointEquivIndexedConstruction
            attempt) :
    CommonGround.ControllerInvocation.StageAttemptFramedConstruction := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨W, initialized, lowered, hspec⟩
  exact
    ⟨W.machine,
      stageAttemptFramedRealizes_of_endpointEquivIndexed
        (attempt := attempt)
        (W := W)
        (initialized := initialized)
        (lowered := lowered)
        hspec⟩

end StructuredConstructionTargets

end Computability
end FoC
