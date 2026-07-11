import FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.TwoStageEndpoints
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.SimulatorLayoutInputMaterializer
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutputCore.Closed

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

def fuelOutputStructuredInputBits
    (L : SimulatorLayout) : Word Bool :=
  encodeCodeWordAsInput (SimulatorLayout.encode L)

def fuelOutputStructuredInputTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  Tape.input (fuelOutputStructuredInputBits i.1.1)

/--
Final tape-0 shape left by the fuel-output structured core: the encoded
layout input with its right-edge blank visited once.

The core must read one blank past the last encoded bit to detect the end of
the final cell-token run, and tape windows never shrink, so the honest local
tape-0 family carries exactly one trailing represented blank.  The endpoint
composition and the shared tape-2 projector quantify over arbitrary
{lit}`tape0` families, so this choice stays local to the leaf.
-/
def fuelOutputStructuredPaddedInputTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  CommonGround.FiniteTransducers.inputWithTrailingBlankPadding
    (fuelOutputStructuredInputBits i.1.1) 1

def fuelOutputStructuredInitializedTape
    (L : SimulatorLayout) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (Tape.input (fuelOutputStructuredInputBits L))
    Tape.blank

def fuelOutputStructuredLoweredTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (fuelOutputStructuredPaddedInputTape i)
    Tape.blank
    (PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)

def FuelOutputStructuredMaterializerConstruction : Prop :=
  Structured3EndpointWordStartEquivMaterializerConstruction
    fuelOutputStructuredInputBits
    fuelOutputStructuredInitializedTape

/--
Equivalence-facing semantic-core obligation for the fuel-output endpoint.

The core is a lowered structured three-tape machine, and the concrete lowerer
transfers structured runs only up to tape equivalence
({name}`RunsFromStateTapeEquiv`), so equivalence is the honest currency for
this leaf; the logical tape-2 output code itself remains exact inside the
guarded encoding.  Logical tape 0 ends as the input with one visited
right-edge blank ({name}`fuelOutputStructuredPaddedInputTape`), because the
core detects the end of the encoded layout by reading that blank and logical
tape windows never shrink.
-/
def FuelOutputStructuredEquivSemanticCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3EndpointEquivSemanticCoreConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt => i.1.1)
    fuelOutputStructuredInitializedTape
    fuelOutputStructuredLoweredTape
    PairedRecognizerDovetailControllerStageAttemptFuelOutputTape
    fuelOutputStructuredPaddedInputTape
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt => Tape.blank)

def FuelOutputStructuredEndpointEquivIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    Structured3EndpointWordStartEquivIndexedFamilySpec
      W
      (fun i :
        PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
          attempt => fuelOutputStructuredInputBits i.1.1)
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape

/--
Finite-table leaf for the fuel-output public-input materializer.
-/
theorem fuelOutputStructuredMaterializerConstruction_core :
    FuelOutputStructuredMaterializerConstruction :=
  simulatorLayoutWordStartEquivMaterializerConstruction_core

/--
Finite-table leaf for the lowered fuel-output structured core.
-/
theorem fuelOutputStructuredEquivSemanticCoreConstruction_core
    (attempt : MachineDescription) :
    FuelOutputStructuredEquivSemanticCoreConstruction attempt := by
  refine ⟨{
    core := FuelOutputCore.coreD attempt.halt
    coreWellFormed := (FuelOutputCore.table attempt.halt).description_wellFormed
    coreHaltTransitionFree :=
      (FuelOutputCore.table attempt.halt).description_haltTransitionFree
    coreSupportsRows :=
      (FuelOutputCore.table attempt.halt).description_supportsReadWriteRows3
    loweredShape := ?_
    semanticCore := ?_ }⟩
  · intro i
    rfl
  · constructor
    · intro i
      simpa [fuelOutputStructuredInitializedTape,
        fuelOutputStructuredLoweredTape,
        fuelOutputStructuredPaddedInputTape,
        fuelOutputStructuredInputBits,
        CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape,
        encodedGuardedStructured3Tapes,
        PairedRecognizerDovetailControllerStageAttemptFuelOutputTape,
        PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode,
        CommonGround.CodeWordEmitters.ExactOutputTape] using
        FuelOutputCore.lowered_halts_of_valid_code attempt.halt
          i.1.1 i.1.2 i.2.1 i.2.2
    · intro L T hhalt
      have hhalt' :
          (lowerStructured3Description
              (FuelOutputCore.coreD attempt.halt)).HaltsFromTape
            (encodedGuardedStructuredTapes
              [ Tape.input
                  (encodeCodeWordAsInput (SimulatorLayout.encode L))
              , Tape.blank
              , Tape.blank ]) T := by
        simpa [fuelOutputStructuredInitializedTape,
          fuelOutputStructuredInputBits,
          CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape,
          encodedGuardedStructured3Tapes] using hhalt
      rcases FuelOutputCore.lowered_closed attempt.halt L T hhalt' with
        ⟨out, hstate, hout, hT⟩
      let i :
          PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
            attempt :=
        ⟨(L, out), hstate, hout⟩
      refine ⟨i, rfl, ?_⟩
      simpa [i, fuelOutputStructuredLoweredTape,
        fuelOutputStructuredPaddedInputTape,
        fuelOutputStructuredInputBits,
        encodedGuardedStructured3Tapes,
        PairedRecognizerDovetailControllerStageAttemptFuelOutputTape,
        PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode,
        CommonGround.CodeWordEmitters.ExactOutputTape] using hT

/--
Target-local parser/core obligation for the fuel-output target.  The public
endpoint theorem below only composes this with a shared tape-2
projector.
-/
theorem fuelOutputStructuredEndpointEquivIndexedConstruction_of_components
    (attempt : MachineDescription) :
    FuelOutputStructuredMaterializerConstruction ->
      FuelOutputStructuredEquivSemanticCoreConstruction attempt ->
        FuelOutputStructuredEndpointEquivIndexedConstruction attempt := by
  intro hmaterializer hcore
  simpa [FuelOutputStructuredEndpointEquivIndexedConstruction,
    FuelOutputStructuredMaterializerConstruction,
    FuelOutputStructuredEquivSemanticCoreConstruction] using
    structured3EndpointWordStartEquivIndexedConstruction_of_components
      hmaterializer
      hcore
      structured3EndpointTape2ProjectorConstruction_core

/--
Equivalence-facing fuel-output endpoint assembled from the parser/core
components and the shared equivalence tape-2 projector.
-/
theorem fuelOutputStructuredEndpointEquivIndexedConstruction_core
    (attempt : MachineDescription) :
    FuelOutputStructuredEndpointEquivIndexedConstruction attempt :=
  fuelOutputStructuredEndpointEquivIndexedConstruction_of_components
    attempt
    fuelOutputStructuredMaterializerConstruction_core
    (fuelOutputStructuredEquivSemanticCoreConstruction_core attempt)

theorem fuelOutputInputCode_eq_of_inputBits_eq
    {attempt : MachineDescription}
    {code : Word MachineCodeSymbol}
    {i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt}
    (h :
      encodeCodeWordAsInput code =
        fuelOutputStructuredInputBits i.1.1) :
    code =
      PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
        i := by
  apply encodeCodeWordAsInput_injective
  simpa [fuelOutputStructuredInputBits,
    PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode] using h

theorem fuelOutputCodeSubroutineConstruction_of_endpointEquivIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    (hspec :
      Structured3EndpointWordStartEquivIndexedFamilySpec
        W
        (fun i :
          PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
            attempt => fuelOutputStructuredInputBits i.1.1)
        PairedRecognizerDovetailControllerStageAttemptFuelOutputTape) :
    exists extractor : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive
          attempt)
        extractor := by
  refine ⟨W.machine, ?_⟩
  exact
    CommonGround.CodeWordEmitters.outputCompiled_of_indexed_tape_equiv_spec
      W.machine_subroutineReady.left
      W.machine_subroutineReady.right
      PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
      PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape
      (fun i =>
        CommonGround.CodeWordEmitters.exactOutputTape_normalizedOutput
          PairedRecognizerDovetailControllerStageAttemptFuelOutputOutputCode i)
      (fun i => by
        simpa [fuelOutputStructuredInputBits,
          PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode] using
          hspec.forward i)
      (fun code T hhalt => by
        have hfrom :
            W.machine.HaltsFromTape
              (Tape.input (encodeCodeWordAsInput code)) T :=
          haltsFromTape_input_of_haltsWithTape hhalt
        rcases
            hspec.closedIndex (encodeCodeWordAsInput code) T hfrom with
          ⟨i, hinput, hT⟩
        exact
          ⟨i, fuelOutputInputCode_eq_of_inputBits_eq hinput, hT⟩)
      (by
        intro code out
        constructor
        · intro htransform
          rcases
              (pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_transform_eq_some_iff
                attempt code out).mp htransform with
            ⟨L, hcode, hstate, houtput⟩
          let i :
              PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
                attempt :=
            ⟨(L, out), ⟨hstate, houtput⟩⟩
          exact ⟨i, hcode, rfl⟩
        · intro hindexed
          rcases hindexed with ⟨i, hcode, hout⟩
          exact
            (pairedRecognizerDovetailControllerStageAttemptFuelOutputCodePrimitive_transform_eq_some_iff
              attempt code out).mpr
              ⟨i.1.1, hcode, i.2.left, by
                rw [hout]
                exact i.2.right⟩)

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_endpointEquivIndexed
    (h :
      forall attempt : MachineDescription,
        FuelOutputStructuredEndpointEquivIndexedConstruction attempt) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction := by
  intro attempt
  rcases h attempt with ⟨W, hspec⟩
  exact
    fuelOutputCodeSubroutineConstruction_of_endpointEquivIndexed
      (attempt := attempt)
      (W := W)
      hspec


end StructuredConstructionTargets

end Computability
end FoC
