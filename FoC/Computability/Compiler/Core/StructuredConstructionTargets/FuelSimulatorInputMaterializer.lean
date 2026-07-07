import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.Basic
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base

set_option doc.verso true

/-!
# Fuel-simulator structured input materializer pilot

This module is the Phase 3 pilot route for the public FuelSimulator input
materializer.  The route is intentionally decomposed into a FuelSimulator input
recognizer and a structured three-logical-tape embedding emitter, so remaining
holes identify concrete finite-machine phases instead of assuming the endpoint
materializer wholesale.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers
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
  structured3InputMaterializerTargetTape
    (fuelSimulatorStructuredInputTape i)
    (fuelSimulatorStructuredOutputBuffer i)

/--
Decoder for exactly the public FuelSimulator input-code family.

The accepted codes are stage-input prefixes with a complete unary fuel suffix:
{lit}`stageInputCodeAppend w limit (encodeNatAppend fuel [])`.
-/
def decodeFuelSimulatorStructuredInputCode
    (code : Word MachineCodeSymbol) :
    Option FuelSimulatorStructuredIndex :=
  match DovetailLayout.decodeStageInput code with
  | none => none
  | some ((w, limit), suffix) =>
      match decodeNat suffix with
      | some (fuel, []) => some ⟨w, (limit, fuel)⟩
      | _ => none

theorem decodeFuelSimulatorStructuredInputCode_encode
    (i : FuelSimulatorStructuredIndex) :
    decodeFuelSimulatorStructuredInputCode
      (fuelSimulatorStructuredInputCode i) = some i := by
  rcases i with ⟨w, limit, fuel⟩
  simp [decodeFuelSimulatorStructuredInputCode,
    fuelSimulatorStructuredInputCode,
    PairedRecognizerDovetailControllerStageAttemptFuelInputCode,
    DovetailLayout.decodeStageInput_stageInputCodeAppend,
    decodeNat_encodeNatAppend]

theorem decodeFuelSimulatorStructuredInputCode_eq_some_encode
    {code : Word MachineCodeSymbol}
    {i : FuelSimulatorStructuredIndex}
    (h :
      decodeFuelSimulatorStructuredInputCode code = some i) :
    code = fuelSimulatorStructuredInputCode i := by
  unfold decodeFuelSimulatorStructuredInputCode at h
  cases hstage : DovetailLayout.decodeStageInput code with
  | none =>
      simp [hstage] at h
  | some parsed =>
      rcases parsed with ⟨stageInput, suffix⟩
      rcases stageInput with ⟨w, limit⟩
      cases hfuel : decodeNat suffix with
      | none =>
          simp [hstage, hfuel] at h
      | some parsedFuel =>
          rcases parsedFuel with ⟨fuel, rest⟩
          cases rest with
          | nil =>
              simp [hstage, hfuel] at h
              cases h
              have hcode :
                  code =
                    DovetailLayout.stageInputCodeAppend
                      w limit suffix :=
                DovetailLayout.decodeStageInput_eq_some_stageInputCodeAppend
                  hstage
              have hsuffix :
                  suffix = encodeNatAppend fuel [] :=
                decodeNat_eq_some_encodeNatAppend hfuel
              rw [hcode, hsuffix]
              rfl
          | cons _ _ =>
              simp [hstage, hfuel] at h

theorem fuelSimulatorStructuredInputCode_injective :
    Function.Injective fuelSimulatorStructuredInputCode := by
  intro i j h
  rcases i with ⟨w1, limit1, fuel1⟩
  rcases j with ⟨w2, limit2, fuel2⟩
  simp [fuelSimulatorStructuredInputCode] at h ⊢
  rcases
      pairedRecognizerDovetailControllerStageAttemptFuelInputCode_injective
        h with
    ⟨hw, hlimit, hfuel⟩
  simp [hw, hlimit, hfuel]

theorem fuelSimulatorStructuredInputTape_injective :
    Function.Injective fuelSimulatorStructuredInputTape := by
  intro i j h
  apply fuelSimulatorStructuredInputCode_injective
  apply encodeCodeWordAsInput_injective
  exact Tape.input_injective
    (by simpa [fuelSimulatorStructuredInputTape] using h)

theorem fuelSimulatorStructuredInputCode_cons
    (i : FuelSimulatorStructuredIndex) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      fuelSimulatorStructuredInputCode i = symbol :: tail := by
  rcases i with ⟨w, limit, fuel⟩
  unfold fuelSimulatorStructuredInputCode
  unfold PairedRecognizerDovetailControllerStageAttemptFuelInputCode
  unfold DovetailLayout.stageInputCodeAppend
  unfold encodeBoolWordAppend
  unfold encodeCellListAppend
  exact
    EncRewriters.encodeNatAppend_cons
      (List.length (List.map some w))
      (encodeCellsAppend (List.map some w)
        (encodeNatAppend limit (encodeNatAppend fuel [])))

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

theorem fuelSimulatorStructuredInitializedTape_eq_materializerTarget
    (i : FuelSimulatorStructuredIndex) :
    fuelSimulatorStructuredInitializedTape i =
      structured3InputMaterializerTargetTape
        (fuelSimulatorStructuredInputTape i)
        Tape.blank := by
  rfl

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
Fuel-simulator input parser/materializer construction, separated from the
lowered structured simulator core.
-/
def FuelSimulatorStructuredIndexedMaterializerConstruction : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)

/--
Equivalence-facing fuel-simulator input parser/materializer construction.

This is the Phase 3 prototype contract for the public-input materializer: it
keeps indexed closedness, but allows the initialized guarded tape to be reached
up to tape equivalence.
-/
def FuelSimulatorStructuredEquivIndexedMaterializerConstruction :
    Prop :=
  Structured3EndpointEquivIndexedMaterializerConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)

/--
Fuel-simulator materializer through the reusable CommonGround structured-input
contract, plus the indexed closedness required by endpoint wrappers.
-/
def FuelSimulatorStructuredEquivInputMaterializerConstruction :
    Prop :=
  Structured3EndpointEquivInputMaterializerConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredOutputBuffer i)

/--
The existing exact indexed materializer obligation feeds the equivalence-facing
materializer contract.
-/
theorem fuelSimulatorStructuredEquivIndexedMaterializerConstruction_of_indexed
    (hmaterializer :
      FuelSimulatorStructuredIndexedMaterializerConstruction) :
    FuelSimulatorStructuredEquivIndexedMaterializerConstruction := by
  simpa [FuelSimulatorStructuredIndexedMaterializerConstruction,
    FuelSimulatorStructuredEquivIndexedMaterializerConstruction] using
    structured3EndpointEquivIndexedMaterializerConstruction_of_exact
      hmaterializer

theorem fuelSimulatorStructuredEquivIndexedMaterializerConstruction_of_inputMaterializer
    (hmaterializer :
      FuelSimulatorStructuredEquivInputMaterializerConstruction) :
    FuelSimulatorStructuredEquivIndexedMaterializerConstruction := by
  simpa [
    FuelSimulatorStructuredEquivInputMaterializerConstruction,
    FuelSimulatorStructuredEquivIndexedMaterializerConstruction,
    Structured3EndpointEquivInputMaterializerInitialized,
    fuelSimulatorStructuredInitializedTape] using
    structured3EndpointEquivIndexedMaterializerConstruction_of_inputMaterializer
      hmaterializer

theorem fuelSimulatorStructuredEquivInputMaterializerConstruction_of_indexed
    (hmaterializer :
      FuelSimulatorStructuredIndexedMaterializerConstruction) :
    FuelSimulatorStructuredEquivInputMaterializerConstruction := by
  simpa [FuelSimulatorStructuredIndexedMaterializerConstruction,
    FuelSimulatorStructuredEquivInputMaterializerConstruction,
    Structured3EndpointEquivInputMaterializerInitialized,
    fuelSimulatorStructuredInitializedTape] using
    structured3EndpointEquivInputMaterializerConstruction_of_indexed
      hmaterializer (fun _i => rfl)

/-- Semantic contract for the FuelSimulator-family recognizer phase. -/
def FuelSimulatorInputRecognizerSpec
    (recognizer : MachineDescription) : Prop :=
  EncRewriters.CanonicalLayouts.ClosedRecognizerSpec
    decodeFuelSimulatorStructuredInputCode
    fuelSimulatorStructuredInputCode
    recognizer

/-- Existence wrapper for the FuelSimulator-family recognizer phase. -/
def FuelSimulatorInputRecognizerConstruction : Prop :=
  EncRewriters.CanonicalLayouts.ClosedRecognizerConstruction
    decodeFuelSimulatorStructuredInputCode
    fuelSimulatorStructuredInputCode

/--
Concrete finite parser for generated FuelSimulator public-input codes.

This is the first real machine leaf left by the pilot: parse
{lit}`stageInputCodeAppend w limit suffix`, require
{lit}`suffix = encodeNatAppend fuel []`,
and preserve the source tape as the handoff tape for the embedding emitter.
-/
def fuelSimulatorInputRecognizerDescription : MachineDescription :=
  { stateCount := 1
    start := 0
    halt := 0
    transitions := [] }

theorem fuelSimulatorInputRecognizerDescription_spec :
    FuelSimulatorInputRecognizerSpec
      fuelSimulatorInputRecognizerDescription := by
  -- Remaining finite-machine obligation: replace the placeholder description
  -- with the concrete FuelSimulator-family parser and prove the closed
  -- canonical-layout recognizer spec above.
  sorry

theorem fuelSimulatorInputRecognizerConstruction_core :
    FuelSimulatorInputRecognizerConstruction :=
  ⟨fuelSimulatorInputRecognizerDescription,
    fuelSimulatorInputRecognizerDescription_spec⟩

/-- Generic embedding-emitter phase for guarded three-logical-tape inputs. -/
def Structured3InputEmbeddingEmitterConstruction : Prop :=
  Structured3InputMaterializerConstruction
    (fun source : Tape Bool => source)
    (fun _source : Tape Bool => Tape.blank)

/--
Concrete emitter that expands an arbitrary public source tape into the guarded
three-logical-tape input with blank scratch and blank output buffer.
-/
def structured3InputEmbeddingEmitterDescription : MachineDescription :=
  { stateCount := 1
    start := 0
    halt := 0
    transitions := [] }

theorem structured3InputEmbeddingEmitterDescription_spec :
    Structured3InputMaterializerSpec
      (fun source : Tape Bool => source)
      (fun _source : Tape Bool => Tape.blank)
      structured3InputEmbeddingEmitterDescription := by
  -- Remaining finite-machine obligation: build the stream transducer that
  -- emits `structured3InputMaterializerTargetTape source Tape.blank`, expanding
  -- each source cell into the guarded structured logical-tape encoding.
  sorry

theorem structured3InputEmbeddingEmitterConstruction_core :
    Structured3InputEmbeddingEmitterConstruction :=
  ⟨structured3InputEmbeddingEmitterDescription,
    structured3InputEmbeddingEmitterDescription_spec⟩

/-- The actual two-phase materializer table named by the pilot route. -/
def fuelSimulatorStructuredEquivInputMaterializerDescription
    (recognizer emitter : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine recognizer emitter
    tapeCodePrimitiveCodeWordHandoffMove

theorem fuelSimulatorStructuredEquivInputMaterializer_closedIndex_of_parts
    {recognizer emitter : MachineDescription}
    (hrecognizer : FuelSimulatorInputRecognizerSpec recognizer)
    (hemitter :
      Structured3InputMaterializerSpec
        (fun source : Tape Bool => source)
        (fun _source : Tape Bool => Tape.blank)
        emitter) :
    EquivClosedIndexedFromTape
      (fuelSimulatorStructuredEquivInputMaterializerDescription
        recognizer emitter)
      (fun i : FuelSimulatorStructuredIndex =>
        fuelSimulatorStructuredInputTape i)
      (Structured3EndpointEquivInputMaterializerInitialized
        (fun i : FuelSimulatorStructuredIndex =>
          fuelSimulatorStructuredInputTape i)
        (fun i => fuelSimulatorStructuredOutputBuffer i)) := by
  -- Remaining indexed-closedness obligation for the sequenced route:
  -- invert the recognizer phase to recover the FuelSimulator index, then use
  -- emitter determinism to transport the final tape to the guarded structured
  -- target for that index.
  sorry

theorem fuelSimulatorStructuredEquivInputMaterializerSpec_of_parts
    {recognizer emitter : MachineDescription}
    (hrecognizer : FuelSimulatorInputRecognizerSpec recognizer)
    (hemitter :
      Structured3InputMaterializerSpec
        (fun source : Tape Bool => source)
        (fun _source : Tape Bool => Tape.blank)
        emitter) :
    Structured3EndpointEquivInputMaterializerSpec
      (fun i : FuelSimulatorStructuredIndex =>
        fuelSimulatorStructuredInputTape i)
      (fun i => fuelSimulatorStructuredOutputBuffer i)
      (fuelSimulatorStructuredEquivInputMaterializerDescription
        recognizer emitter) := by
  constructor
  · constructor
    · exact
        MachineDescription.seqSubroutine_subroutineReady
          hrecognizer.left hemitter.left
    · intro i
      rcases hrecognizer.right.left i with ⟨nR, hR⟩
      let Tmid :=
        EncRewriters.CanonicalLayouts.HandoffTape
          fuelSimulatorStructuredInputCode i
      have hRfrom :
          recognizer.HaltsFromTape
            (fuelSimulatorStructuredInputTape i) Tmid := by
        refine ⟨nR, ?_⟩
        simpa [fuelSimulatorStructuredInputTape, Tmid,
          EncRewriters.CanonicalLayouts.Bits] using hR
      have hhandoff :
          Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid =
            fuelSimulatorStructuredInputTape i := by
        simpa [Tmid, fuelSimulatorStructuredInputTape,
          EncRewriters.CanonicalLayouts.InputTape,
          EncRewriters.CanonicalLayouts.Bits] using
          EncRewriters.CanonicalLayouts.handoffTape_handoff
            fuelSimulatorStructuredInputCode_cons i
      have hE :
          emitter.HaltsFromTapeEquiv
            (fuelSimulatorStructuredInputTape i)
            (structured3InputMaterializerTargetTape
              (fuelSimulatorStructuredInputTape i) Tape.blank) :=
        hemitter.right (fuelSimulatorStructuredInputTape i)
      simpa [fuelSimulatorStructuredEquivInputMaterializerDescription,
        fuelSimulatorStructuredOutputBuffer] using
        CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
          hrecognizer.left hemitter.left hRfrom hhandoff hE
  · exact
      fuelSimulatorStructuredEquivInputMaterializer_closedIndex_of_parts
        hrecognizer hemitter

theorem fuelSimulatorStructuredEquivInputMaterializerConstruction_of_parts
    (hrecognizer : FuelSimulatorInputRecognizerConstruction)
    (hemitter : Structured3InputEmbeddingEmitterConstruction) :
    FuelSimulatorStructuredEquivInputMaterializerConstruction := by
  rcases hrecognizer with ⟨recognizer, hrecognizerSpec⟩
  rcases hemitter with ⟨emitter, hemitterSpec⟩
  exact
    ⟨fuelSimulatorStructuredEquivInputMaterializerDescription
        recognizer emitter,
      fuelSimulatorStructuredEquivInputMaterializerSpec_of_parts
        hrecognizerSpec hemitterSpec⟩

/--
Finite-table leaf for the fuel-simulator public-input materializer on the
equivalence-facing endpoint route.
-/
theorem fuelSimulatorStructuredEquivInputMaterializerConstruction_core :
    FuelSimulatorStructuredEquivInputMaterializerConstruction :=
  fuelSimulatorStructuredEquivInputMaterializerConstruction_of_parts
    fuelSimulatorInputRecognizerConstruction_core
    structured3InputEmbeddingEmitterConstruction_core

end StructuredConstructionTargets

end Computability
end FoC
