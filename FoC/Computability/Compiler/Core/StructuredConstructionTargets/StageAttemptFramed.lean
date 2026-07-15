import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulator
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.Materializer
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Build
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.TwoStageEndpoints

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def StageAttemptFramedStructuredMaterializerConstruction : Prop :=
  Structured3EndpointWordStartEquivMaterializerConstruction
    stageAttemptFramedStructuredInputBits
    stageAttemptFramedStructuredInitializedTape

def StageAttemptFramedStructuredEndpointEquivIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    Structured3EndpointWordStartEquivIndexedFamilySpec
      W
      (fun i : StageAttemptFramedStructuredIndex attempt =>
        stageAttemptFramedStructuredInputBits i.C)
      stageAttemptFramedStructuredOutputTape

/--
Finite-table leaf for the framed-invocation public-input materializer.
-/
theorem stageAttemptFramedStructuredMaterializerConstruction_core
    : StageAttemptFramedStructuredMaterializerConstruction := by
  unfold StageAttemptFramedStructuredMaterializerConstruction
  unfold stageAttemptFramedStructuredInitializedTape stageAttemptFramedStructuredInputBits
  exact
    StageAttemptFramedMaterializer.stageAttemptFramedWordStartEquivMaterializerConstruction_core

/--
Target-local parser/core obligation for the framed-invocation target.  The
public endpoint theorem below only composes this with a shared tape-2
projector.
-/
theorem stageAttemptFramedStructuredEndpointEquivIndexedConstruction_of_components
    (attempt : MachineDescription)
    (hmaterializer : StageAttemptFramedStructuredMaterializerConstruction)
    (hcore : StageAttemptFramedStructuredSemanticCoreConstruction attempt) :
    StageAttemptFramedStructuredEndpointEquivIndexedConstruction attempt := by
  rcases hcore with ⟨C⟩
  simpa [StageAttemptFramedStructuredEndpointEquivIndexedConstruction,
    StageAttemptFramedStructuredMaterializerConstruction] using
    structured3EndpointWordStartEquivIndexedConstruction_of_components
      hmaterializer ⟨C.components⟩
      (by
        intro i
        simpa [stageAttemptFramedStructuredOutputTape,
          CommonGround.ControllerInvocation.StageAttemptFramedOutputTape,
          Tape.output] using
          structuredTape2EndpointTape_input_word
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                (DovetailControllerLayout.withResult i.C i.result))))
      structured3EndpointTape2ProjectorConstruction_core



theorem stageAttemptFramedInput_layout_eq_of_inputBits_eq
    {attempt : MachineDescription}
    {C : DovetailControllerLayout}
    {i : StageAttemptFramedStructuredIndex attempt}
    (h :
      stageAttemptFramedStructuredInputBits C =
        stageAttemptFramedStructuredInputBits i.C) :
    C = i.C := by
  apply DovetailControllerLayout.encode_injective
  apply encodeCodeWordAsInput_injective
  simpa [stageAttemptFramedStructuredInputBits] using h

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

theorem stageAttemptFramedRealizes_of_endpointEquivIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    (hspec :
      Structured3EndpointWordStartEquivIndexedFamilySpec
        W
        (fun i : StageAttemptFramedStructuredIndex attempt =>
          stageAttemptFramedStructuredInputBits i.C)
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
        (hspec.forward i)
    simpa [MachineDescription.HaltsWithOutput,
      MachineDescription.HaltsFromTapeWithOutput,
      MachineDescription.HaltsWithOutputIn,
      MachineDescription.HaltsFromTapeWithOutputIn,
      MachineDescription.initial,
      stageAttemptFramedStructuredInputBits,
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
        hspec.closedIndex inputBits T hfrom with
      ⟨i, hinput, hT⟩
    have hC : C = i.C := by
      exact
        stageAttemptFramedInput_layout_eq_of_inputBits_eq
          (attempt := attempt)
          (C := C)
          (i := i)
          (by
            simpa [inputBits,
              stageAttemptFramedStructuredInputBits] using hinput)
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
  rcases h attempt hattempt with ⟨W, hspec⟩
  exact
    ⟨W.machine,
      stageAttemptFramedRealizes_of_endpointEquivIndexed
        (attempt := attempt)
        (W := W)
        hspec⟩

theorem stageAttemptFramedStructuredEndpointEquivIndexedConstruction_core
    (attempt : MachineDescription)
    (hattempt : attempt.SubroutineReady) :
    StageAttemptFramedStructuredEndpointEquivIndexedConstruction attempt :=
  stageAttemptFramedStructuredEndpointEquivIndexedConstruction_of_components
    attempt
    stageAttemptFramedStructuredMaterializerConstruction_core
    (StageAttemptFramed.SemanticCore.stageAttemptFramedStructuredSemanticCoreConstruction
      attempt hattempt)

end StructuredConstructionTargets

end Computability
end FoC
