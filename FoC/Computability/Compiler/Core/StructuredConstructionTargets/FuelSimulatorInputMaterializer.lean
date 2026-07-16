import FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.DovetailStagePrefix
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.DovetailStagePrefixClosed
import FoC.Computability.Compiler.Core.DovetailInitLayout.StageInputValidator
import FoC.Computability.Compiler.Core.DovetailInitLayout.StageInputMarkedScanner.Closed

set_option doc.verso true

/-!
# Fuel-simulator structured input materializer

This module implements the public FuelSimulator input materializer through a
FuelSimulator input recognizer and a structured three-logical-tape embedding
emitter.  The decomposition exposes the concrete finite-machine phases behind
the endpoint materializer.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open FoC.Computability.EncRewriters.CanonicalLayouts.DovetailStagePrefix
open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

/-- Index for the fuel-simulator structured input family: word, stage limit,
and fuel budget. -/
structure FuelSimulatorStructuredIndex where
  w     : Word Bool
  limit : Nat
  fuel  : Nat

def fuelSimulatorStructuredInputCode
    (i : FuelSimulatorStructuredIndex) : Word MachineCodeSymbol :=
  PairedRecognizerDovetailControllerStageAttemptFuelInputCode
    i.w i.limit i.fuel

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
      | some (fuel, []) => some { w, limit, fuel }
      | _ => none

theorem decodeFuelSimulatorStructuredInputCode_encode
    (i : FuelSimulatorStructuredIndex) :
    decodeFuelSimulatorStructuredInputCode
      (fuelSimulatorStructuredInputCode i) = some i := by
  cases i with | mk w limit fuel =>
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
  simp only [decodeFuelSimulatorStructuredInputCode] at h
  cases hstage : DovetailLayout.decodeStageInput code with
  | none => simp [hstage] at h
  | some parsed =>
    rcases parsed with ⟨⟨w, limit⟩, suffix⟩
    cases hfuel : decodeNat suffix with
    | none => simp [hstage, hfuel] at h
    | some parsedFuel =>
      rcases parsedFuel with ⟨fuel, rest⟩
      cases rest with
      | cons _ _ => simp [hstage, hfuel] at h
      | nil =>
        simp [hstage, hfuel] at h; cases h
        rw [DovetailLayout.decodeStageInput_eq_some_stageInputCodeAppend hstage,
            decodeNat_eq_some_encodeNatAppend hfuel]
        rfl

theorem fuelSimulatorStructuredInputCode_injective :
    Function.Injective fuelSimulatorStructuredInputCode := by
  intro i j h
  cases i with | mk w1 limit1 fuel1 =>
  cases j with | mk w2 limit2 fuel2 =>
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
    ∃ symbol : MachineCodeSymbol,
    ∃ tail : Word MachineCodeSymbol,
      fuelSimulatorStructuredInputCode i = symbol :: tail := by
  cases i with | mk w limit fuel =>
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


/--
Exact materializer behavior needed by the canonical fuel-simulator endpoint.
-/
def FuelSimulatorStructuredExactMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointExactMaterializerSpec
    fuelSimulatorStructuredInputTape
    fuelSimulatorStructuredInitializedTape
    materializer

/--
Target-specific fuel-simulator materializer obligation before deterministic
per-input exact closedness is installed by the shared endpoint infrastructure.
-/
def FuelSimulatorStructuredIndexedMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerSpec
    fuelSimulatorStructuredInputTape
    fuelSimulatorStructuredInitializedTape
    materializer

/--
Fuel-simulator input parser/materializer construction, separated from the
lowered structured simulator core.
-/
def FuelSimulatorStructuredIndexedMaterializerConstruction : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    fuelSimulatorStructuredInputTape
    fuelSimulatorStructuredInitializedTape

/--
Equivalence-facing fuel-simulator input parser/materializer construction.

The contract keeps indexed closedness while allowing the initialized guarded
tape to be reached up to tape equivalence.
-/
def FuelSimulatorStructuredEquivIndexedMaterializerConstruction :
    Prop :=
  Structured3EndpointEquivIndexedMaterializerConstruction
    fuelSimulatorStructuredInputTape
    fuelSimulatorStructuredInitializedTape

/--
Fuel-simulator materializer through the reusable CommonGround structured-input
contract, plus the indexed closedness required by endpoint wrappers.
-/
def FuelSimulatorStructuredEquivInputMaterializerConstruction :
    Prop :=
  Structured3EndpointEquivInputMaterializerConstruction
    fuelSimulatorStructuredInputTape
    fuelSimulatorStructuredOutputBuffer

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
    fuelSimulatorStructuredInitializedTape] using!
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
  recognizer.SubroutineReady ∧
    (forall i : FuelSimulatorStructuredIndex,
      recognizer.HaltsFromTapeEquiv
        (fuelSimulatorStructuredInputTape i)
        (EncRewriters.CanonicalLayouts.HandoffTape
          fuelSimulatorStructuredInputCode i)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        recognizer.HaltsWithTape
            (encodeCodeWordAsInput code) T ->
          exists i : FuelSimulatorStructuredIndex,
            decodeFuelSimulatorStructuredInputCode code = some i ∧
              Tape.Equiv T
                (EncRewriters.CanonicalLayouts.HandoffTape
                  fuelSimulatorStructuredInputCode i)

/-- Existence wrapper for the FuelSimulator-family recognizer phase. -/
def FuelSimulatorInputRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    FuelSimulatorInputRecognizerSpec recognizer

/--
Equivalence-facing finite-machine behavior for the FuelSimulator-family
recognizer.

The recognizer must accept exactly the canonical public input tapes indexed by
{name}`FuelSimulatorStructuredIndex` when started from ordinary input tapes and
hand off to a tape equivalent to moving one cell right.
-/
structure FuelSimulatorInputRecognizerEquivRunSpec
    (recognizer : MachineDescription) : Prop where
  ready : recognizer.SubroutineReady
  forward :
    forall i : FuelSimulatorStructuredIndex,
      recognizer.HaltsFromTapeEquiv
        (fuelSimulatorStructuredInputTape i)
        (EncRewriters.CanonicalLayouts.HandoffTape
          fuelSimulatorStructuredInputCode i)
  closedCanonical :
    forall code : Word MachineCodeSymbol,
    forall T : Tape Bool,
      recognizer.HaltsWithTape
        (encodeCodeWordAsInput code) T ->
        ∃ i : FuelSimulatorStructuredIndex,
          decodeFuelSimulatorStructuredInputCode code = some i ∧
            Tape.Equiv T
              (EncRewriters.CanonicalLayouts.HandoffTape
                fuelSimulatorStructuredInputCode i)

theorem fuelSimulatorInputRecognizerSpec_of_equivRunSpec
    {recognizer : MachineDescription}
    (hspec : FuelSimulatorInputRecognizerEquivRunSpec recognizer) :
    FuelSimulatorInputRecognizerSpec recognizer := by
  constructor
  · exact hspec.ready
  · constructor
    · exact hspec.forward
    · exact hspec.closedCanonical

/--
Concrete finite parser for generated FuelSimulator public-input codes.

It parses
{lit}`stageInputCodeAppend w limit suffix`, requires
{lit}`suffix = encodeNatAppend fuel []`,
and preserves the source tape as the handoff tape for the embedding emitter.
-/
def NatClosedScannerDescription : MachineDescription where
  stateCount := FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.stateCount
  start := 200
  halt := FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.halt
  transitions := FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription.transitions

theorem markStageInputSecondBitDescription_ready :
    MarkStageInputSecondBitDescription.SubroutineReady := by
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · exact
        transition_wellFormed_of_all
          (l := MarkStageInputSecondBitDescription.transitions)
          (stateCount := MarkStageInputSecondBitDescription.stateCount)
          (by decide)
    · exact
        transition_deterministic_of_all
          (l := MarkStageInputSecondBitDescription.transitions)
          (by decide)
  · exact
      transition_notFrom_of_all
        (l := MarkStageInputSecondBitDescription.transitions)
        (state := MarkStageInputSecondBitDescription.halt)
        (by decide)

theorem restoreStageInputSecondBitDescription_ready :
    RestoreStageInputSecondBitDescription.SubroutineReady := by
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · exact
        transition_wellFormed_of_all
          (l := RestoreStageInputSecondBitDescription.transitions)
          (stateCount := RestoreStageInputSecondBitDescription.stateCount)
          (by decide)
    · exact
        transition_deterministic_of_all
          (l := RestoreStageInputSecondBitDescription.transitions)
          (by decide)
  · exact
      transition_notFrom_of_all
        (l := RestoreStageInputSecondBitDescription.transitions)
        (state := RestoreStageInputSecondBitDescription.halt)
        (by decide)

theorem natClosedScannerDescription_ready :
    NatClosedScannerDescription.SubroutineReady := by
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · exact
        transition_wellFormed_of_all
          (l := NatClosedScannerDescription.transitions)
          (stateCount := NatClosedScannerDescription.stateCount)
          (by decide)
    · exact
        transition_deterministic_of_all
          (l := NatClosedScannerDescription.transitions)
          (by decide)
  · exact
      transition_notFrom_of_all
        (l := NatClosedScannerDescription.transitions)
        (state := NatClosedScannerDescription.halt)
        (by decide)

def fuelSimulatorInputRecognizerCoreDescription : MachineDescription :=
  seqSubroutine MarkedPrefixScannerDescription NatClosedScannerDescription Direction.right

theorem fuelSimulatorInputRecognizerCoreDescription_ready :
    fuelSimulatorInputRecognizerCoreDescription.SubroutineReady := by
  simpa [fuelSimulatorInputRecognizerCoreDescription] using
    seqSubroutine_subroutineReady
      markedPrefixScannerDescription_subroutineReady
      natClosedScannerDescription_ready

def fuelSimulatorInputBits
    (i : FuelSimulatorStructuredIndex) : Word Bool :=
  encodeCodeWordAsInput (fuelSimulatorStructuredInputCode i)

def fuelSimulatorInputSecondBitTail
    (i : FuelSimulatorStructuredIndex) : Word Bool :=
  match fuelSimulatorInputBits i with
  | _ :: _ :: tail => tail
  | _ => []

theorem fuelSimulatorInputBits_eq_false_false_tail
    (i : FuelSimulatorStructuredIndex) :
    fuelSimulatorInputBits i =
      false :: false :: fuelSimulatorInputSecondBitTail i := by
  cases i with | mk w limit fuel =>
  cases w with
  | nil =>
      simp [fuelSimulatorInputBits,
        fuelSimulatorInputSecondBitTail,
        fuelSimulatorStructuredInputCode,
        PairedRecognizerDovetailControllerStageAttemptFuelInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat,
        encodeCodeWordAsInput,
        encodeCodeSymbolAsInput]
  | cons b rest =>
      simp [fuelSimulatorInputBits,
        fuelSimulatorInputSecondBitTail,
        fuelSimulatorStructuredInputCode,
        PairedRecognizerDovetailControllerStageAttemptFuelInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat]

theorem fuelSimulatorInputBits_nil_shape
    (limit fuel : Nat) :
    fuelSimulatorInputBits
        { w := ([] : Word Bool), limit := limit, fuel := fuel } =
      false :: false :: true :: true ::
        List.append (stageNatBits limit) (stageNatBits fuel) := by
  simp [fuelSimulatorInputBits, fuelSimulatorStructuredInputCode,
    PairedRecognizerDovetailControllerStageAttemptFuelInputCode,
    DovetailLayout.stageInputCodeAppend,
    encodeBoolWordAppend, encodeCellListAppend,
    stageNatBits, encodeCellsAppend]
  rw [natBits_eq_encodeNatAppend 0
    (encodeNatAppend limit (encodeNatAppend fuel []))]
  rw [natBits_eq_encodeNatAppend limit (encodeNatAppend fuel [])]
  rw [natBits_eq_encodeNatAppend fuel ([] : Word MachineCodeSymbol)]
  simp [stageNatBits, encodeNat, encodeCodeWordAsInput,
    encodeCodeSymbolAsInput]

theorem fuelSimulatorInputSecondBitTail_nil_shape
    (limit fuel : Nat) :
    fuelSimulatorInputSecondBitTail
        { w := ([] : Word Bool), limit := limit, fuel := fuel } =
      true :: true ::
        List.append (stageNatBits limit) (stageNatBits fuel) := by
  unfold fuelSimulatorInputSecondBitTail
  rw [fuelSimulatorInputBits_nil_shape limit fuel]

theorem fuelSimulatorInputBits_cons_shape
    (b : Bool) (rest : Word Bool) (limit fuel : Nat) :
    fuelSimulatorInputBits
        { w := b :: rest, limit := limit, fuel := fuel } =
      false :: false :: true :: false ::
        List.append (stageNatBits rest.length)
          (List.append (cellBits b)
            (List.append (cellsBits rest)
              (List.append (stageNatBits limit)
                (stageNatBits fuel)))) := by
  cases b <;>
  simp [fuelSimulatorInputBits, fuelSimulatorStructuredInputCode,
    PairedRecognizerDovetailControllerStageAttemptFuelInputCode,
    DovetailLayout.stageInputCodeAppend,
    encodeBoolWordAppend, encodeCellListAppend,
    encodeNatAppend, encodeNat, stageNatBits,
    encodeCellAppend, encodeCell, encodeCellsAppend,
    encodeCodeSymbolAsInput, cellBits, cellsBits]
  · change
      false :: false :: true :: false ::
        encodeCodeWordAsInput
          (List.append (encodeNat rest.length)
            (MachineCodeSymbol.zero ::
              encodeCellsAppend (List.map some rest)
                (List.append (encodeNat limit) (encodeNat fuel)))) =
        false :: false :: true :: false ::
          (List.append (encodeCodeWordAsInput (encodeNat rest.length))
            (false :: true :: false :: true ::
              (List.append
                (encodeCodeWordAsInput
                  (encodeCellsAppend (List.map some rest) []))
                (List.append (encodeCodeWordAsInput (encodeNat limit))
                  (encodeCodeWordAsInput (encodeNat fuel))))))
    rw [show
        encodeCellsAppend (List.map some rest)
            (List.append (encodeNat limit) (encodeNat fuel)) =
          List.append
            (encodeCellsAppend (List.map some rest) [])
            (List.append (encodeNat limit) (encodeNat fuel)) by
        simpa using
          (encodeCellsAppend_append (List.map some rest)
            ([] : Word MachineCodeSymbol)
            (List.append (encodeNat limit) (encodeNat fuel)))]
    rw [encodeCodeWordAsInput_append]
    simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput]
    change
      encodeCodeWordAsInput
          (List.append (encodeCellsAppend (List.map some rest) [])
            (List.append (encodeNat limit) (encodeNat fuel))) =
        List.append
          (encodeCodeWordAsInput
            (encodeCellsAppend (List.map some rest) []))
          (List.append (encodeCodeWordAsInput (encodeNat limit))
            (encodeCodeWordAsInput (encodeNat fuel)))
    rw [encodeCodeWordAsInput_append]
    rw [encodeCodeWordAsInput_append]
  · change
      false :: false :: true :: false ::
        encodeCodeWordAsInput
          (List.append (encodeNat rest.length)
            (MachineCodeSymbol.one ::
              encodeCellsAppend (List.map some rest)
                (List.append (encodeNat limit) (encodeNat fuel)))) =
        false :: false :: true :: false ::
          (List.append (encodeCodeWordAsInput (encodeNat rest.length))
            (false :: true :: true :: false ::
              (List.append
                (encodeCodeWordAsInput
                  (encodeCellsAppend (List.map some rest) []))
                (List.append (encodeCodeWordAsInput (encodeNat limit))
                  (encodeCodeWordAsInput (encodeNat fuel))))))
    rw [show
        encodeCellsAppend (List.map some rest)
            (List.append (encodeNat limit) (encodeNat fuel)) =
          List.append
            (encodeCellsAppend (List.map some rest) [])
            (List.append (encodeNat limit) (encodeNat fuel)) by
        simpa using
          (encodeCellsAppend_append (List.map some rest)
            ([] : Word MachineCodeSymbol)
            (List.append (encodeNat limit) (encodeNat fuel)))]
    rw [encodeCodeWordAsInput_append]
    simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput]
    change
      encodeCodeWordAsInput
          (List.append (encodeCellsAppend (List.map some rest) [])
            (List.append (encodeNat limit) (encodeNat fuel))) =
        List.append
          (encodeCodeWordAsInput
            (encodeCellsAppend (List.map some rest) []))
          (List.append (encodeCodeWordAsInput (encodeNat limit))
            (encodeCodeWordAsInput (encodeNat fuel)))
    rw [encodeCodeWordAsInput_append]
    rw [encodeCodeWordAsInput_append]

theorem fuelSimulatorInputSecondBitTail_cons_shape
    (b : Bool) (rest : Word Bool) (limit fuel : Nat) :
    fuelSimulatorInputSecondBitTail
        { w := b :: rest, limit := limit, fuel := fuel } =
      true :: false ::
        List.append (stageNatBits rest.length)
          (List.append (cellBits b)
            (List.append (cellsBits rest)
              (List.append (stageNatBits limit)
                (stageNatBits fuel)))) := by
  unfold fuelSimulatorInputSecondBitTail
  rw [fuelSimulatorInputBits_cons_shape b rest limit fuel]

def fuelSimulatorInputSecondBitMarkedTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells [some false]
    (none :: (fuelSimulatorInputSecondBitTail i).map some)

def fuelSimulatorInputSecondBitMarkedHandoffTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  Tape.move Direction.right
    (fuelSimulatorInputSecondBitMarkedTape i)

def fuelSimulatorInputSecondBitMarkedCheckedTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells [some false]
    (List.append
      (none :: (fuelSimulatorInputSecondBitTail i).map some)
      [none])

def fuelSimulatorInputSecondBitMarkedCheckedHandoffTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  Tape.move Direction.right
    (fuelSimulatorInputSecondBitMarkedCheckedTape i)

def fuelSimulatorInputCheckedInputTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    (List.append (List.map some (fuelSimulatorInputBits i)) [none])

def fuelSimulatorInputCheckedValidatorTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  Tape.move Direction.right
    (fuelSimulatorInputCheckedInputTape i)

theorem markStageInputSecondBitDescription_run_fuel
    (i : FuelSimulatorStructuredIndex) :
    MarkStageInputSecondBitDescription.runConfig 3
        (MarkStageInputSecondBitDescription.initial
          (fuelSimulatorInputBits i)) =
      { state := MarkStageInputSecondBitDescription.halt
        tape := fuelSimulatorInputSecondBitMarkedTape i } := by
  rw [fuelSimulatorInputBits_eq_false_false_tail i]
  simp [MarkStageInputSecondBitDescription,
    fuelSimulatorInputSecondBitMarkedTape,
    fuelSimulatorInputSecondBitTail,
    DovetailInitialLayoutInitializer.tapeAtCells, initial,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.input, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem restoreStageInputSecondBitDescription_run_checked_fuel
    (i : FuelSimulatorStructuredIndex) :
    RestoreStageInputSecondBitDescription.runConfig 1
        { state := RestoreStageInputSecondBitDescription.start
          tape := fuelSimulatorInputSecondBitMarkedCheckedTape i } =
      { state := RestoreStageInputSecondBitDescription.halt
        tape := fuelSimulatorInputCheckedInputTape i } := by
  unfold fuelSimulatorInputSecondBitMarkedCheckedTape
  unfold fuelSimulatorInputCheckedInputTape
  rw [fuelSimulatorInputBits_eq_false_false_tail i]
  simp [RestoreStageInputSecondBitDescription,
    fuelSimulatorInputSecondBitTail,
    DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
    stepConfig, lookupTransition, Matches, transition,
    Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem fuelSimulatorInputSecondBitMarkedCheckedHandoffTape_move_left
    (i : FuelSimulatorStructuredIndex) :
    Tape.move Direction.left
        (fuelSimulatorInputSecondBitMarkedCheckedHandoffTape i) =
      fuelSimulatorInputSecondBitMarkedCheckedTape i := by
  unfold fuelSimulatorInputSecondBitMarkedCheckedHandoffTape
  unfold fuelSimulatorInputSecondBitMarkedCheckedTape
  cases fuelSimulatorInputSecondBitTail i <;>
    simp [DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem fuelSimulatorInputCheckedValidatorTape_equiv_handoff
    (i : FuelSimulatorStructuredIndex) :
    Tape.Equiv
      (fuelSimulatorInputCheckedValidatorTape i)
      (EncRewriters.CanonicalLayouts.HandoffTape
        fuelSimulatorStructuredInputCode i) := by
  change
    Tape.Equiv
      (fuelSimulatorInputCheckedValidatorTape i)
      (Tape.move Direction.right
        (Tape.input (fuelSimulatorInputBits i)))
  unfold fuelSimulatorInputCheckedValidatorTape
  unfold fuelSimulatorInputCheckedInputTape
  rw [fuelSimulatorInputBits_eq_false_false_tail i]
  simp [fuelSimulatorInputSecondBitTail,
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.input, Tape.move, Tape.moveRight,
    Tape.Equiv,
    FoC.Computability.dropTrailingNone_append_none]

private theorem runConfig_eq_of_transitions_eq
    (D E : MachineDescription)
    (htrans : D.transitions = E.transitions)
    (n : Nat) (c : MachineDescription.Configuration) :
    D.runConfig n c = E.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      change
        (match D.stepConfig c with
        | none => c
        | some next => D.runConfig n next) =
          match E.stepConfig c with
          | none => c
          | some next => E.runConfig n next
      have hstep : D.stepConfig c = E.stepConfig c := by
        unfold stepConfig
        unfold lookupTransition
        rw [htrans]
      rw [hstep]
      cases E.stepConfig c with
      | none =>
          rfl
      | some next =>
          exact ih next

private theorem natClosedScannerDescription_run_stageNat_closed
    (fuel : Nat) (pre : Word Bool)
    (leftTail : List (Option Bool)) :
    NatClosedScannerDescription.runConfig
        ((4 * fuel + 5) +
          ((List.append pre (stageNatBits fuel)).length + 1))
        (config 200
          (List.append (pre.reverse.map some) (none :: leftTail))
          ((stageNatBits fuel).map some)) =
      config 999 (none :: leftTail)
        (List.append
          ((List.append pre (stageNatBits fuel)).map some)
          [none]) := by
  rw [runConfig_eq_of_transitions_eq NatClosedScannerDescription
    StageInputMarkedScannerDescription (by rfl)]
  exact run_state200_stageNat_closed_to_halt fuel pre leftTail

theorem fuelSimulatorInputSecondBitMarkedCheckedHandoffTape_eq_tapeAtCells
    (i : FuelSimulatorStructuredIndex) :
    fuelSimulatorInputSecondBitMarkedCheckedHandoffTape i =
      DovetailInitialLayoutInitializer.tapeAtCells [none, some false]
        (List.append
          ((fuelSimulatorInputSecondBitTail i).map some) [none]) := by
  unfold fuelSimulatorInputSecondBitMarkedCheckedHandoffTape
  unfold fuelSimulatorInputSecondBitMarkedCheckedTape
  cases fuelSimulatorInputSecondBitTail i <;>
    simp [DovetailInitialLayoutInitializer.tapeAtCells,
      Tape.move, Tape.moveRight]

private theorem fuelSimulatorCore_forward_marked_of_tail_shape
    (tailPrefix : Word Bool) (limit fuel : Nat)
    (tail : Word Bool)
    (htail :
      tail =
        List.append tailPrefix
          (List.append (stageNatBits limit) (stageNatBits fuel)))
    (h200 :
      exists n : Nat,
        MarkedPrefixScannerDescription.runConfig n
            (markedTailStartConfig tail) =
          config 200
            (List.append (tailPrefix.reverse.map some)
              (none :: [some false]))
            (List.append ((stageNatBits limit).map some)
              ((stageNatBits fuel).map some))) :
    exists steps : Nat,
      fuelSimulatorInputRecognizerCoreDescription.runConfig steps
          { state := fuelSimulatorInputRecognizerCoreDescription.start
            tape := (markedTailStartConfig tail).tape } =
        { state := fuelSimulatorInputRecognizerCoreDescription.halt
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              [none, some false]
              (List.append (tail.map some) [none]) } := by
  rcases h200 with ⟨n1, h1⟩
  rcases stageNatBits_false_false_tail fuel with ⟨ftail, hftail⟩
  rcases run_markedPrefix_raw_to_handoff_withBase limit
      (List.append (tailPrefix.reverse.map some) (none :: [some false]))
      false (false :: ftail) with ⟨n2, h2⟩
  have hrun :
      MarkedPrefixScannerDescription.runConfig (n1 + n2)
          (markedTailStartConfig tail) =
        natSuffixHandoffConfigWithBase limit
          (List.append (tailPrefix.reverse.map some)
            (none :: [some false]))
          (false :: false :: ftail) := by
    rw [runConfig_add, h1, hftail]
    simpa using h2
  have hArun :
      MarkedPrefixScannerDescription.runConfig (n1 + n2)
          { state := MarkedPrefixScannerDescription.start
            tape := (markedTailStartConfig tail).tape } =
        { state := MarkedPrefixScannerDescription.halt
          tape :=
            (natSuffixHandoffConfigWithBase limit
              (List.append (tailPrefix.reverse.map some)
                (none :: [some false]))
              (false :: false :: ftail)).tape } := hrun
  have hmove :=
    natSuffixHandoffConfigWithBase_move_right limit
      (List.append (tailPrefix.reverse.map some) (none :: [some false]))
      false (false :: ftail)
  have hB :=
    natClosedScannerDescription_run_stageNat_closed fuel
      (List.append tailPrefix (stageNatBits limit)) [some false]
  have hleft :
      List.append
          ((List.append tailPrefix (stageNatBits limit)).reverse.map some)
          (none :: [some false]) =
        List.append ((stageNatBits limit).reverse.map some)
          (List.append (tailPrefix.reverse.map some)
            (none :: [some false])) := by
    simp [List.reverse_append, List.map_append, List.append_assoc]
  have hcells :
      List.append (List.append tailPrefix (stageNatBits limit))
          (stageNatBits fuel) = tail := by
    rw [htail]
    simp [List.append_assoc]
  rw [hleft, hcells, hftail] at hB
  have hBReach :
      exists nB : Nat,
        NatClosedScannerDescription.runConfig nB
            { state := NatClosedScannerDescription.start
              tape :=
                Tape.move Direction.right
                  ((natSuffixHandoffConfigWithBase limit
                    (List.append (tailPrefix.reverse.map some)
                      (none :: [some false]))
                    (false :: false :: ftail)).tape) } =
          { state := NatClosedScannerDescription.halt
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                [none, some false]
                (List.append (tail.map some) [none]) } := by
    refine ⟨(4 * fuel + 5) + (tail.length + 1), ?_⟩
    rw [hmove]
    exact hB
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := MarkedPrefixScannerDescription)
        (B := NatClosedScannerDescription)
        (handoffMove := Direction.right)
        markedPrefixScannerDescription_subroutineReady
        natClosedScannerDescription_ready
        hArun hBReach with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [fuelSimulatorInputRecognizerCoreDescription] using hsteps

theorem fuelSimulatorInputRecognizerCoreDescription_forward_marked
    (i : FuelSimulatorStructuredIndex) :
    exists steps : Nat,
      fuelSimulatorInputRecognizerCoreDescription.runConfig steps
          { state := fuelSimulatorInputRecognizerCoreDescription.start
            tape := fuelSimulatorInputSecondBitMarkedHandoffTape i } =
        { state := fuelSimulatorInputRecognizerCoreDescription.halt
          tape := fuelSimulatorInputSecondBitMarkedCheckedHandoffTape i } := by
  cases i with | mk w limit fuel =>
  rw [fuelSimulatorInputSecondBitMarkedCheckedHandoffTape_eq_tapeAtCells]
  have hstart :
      fuelSimulatorInputSecondBitMarkedHandoffTape
          { w := w, limit := limit, fuel := fuel } =
        (markedTailStartConfig
          (fuelSimulatorInputSecondBitTail
            { w := w, limit := limit, fuel := fuel })).tape := rfl
  rw [hstart]
  cases w with
  | nil =>
      refine
        fuelSimulatorCore_forward_marked_of_tail_shape
          [true, true] limit fuel
          (fuelSimulatorInputSecondBitTail
            { w := [], limit := limit, fuel := fuel })
          ?_ ?_
      · rw [fuelSimulatorInputSecondBitTail_nil_shape]
        rfl
      · rw [fuelSimulatorInputSecondBitTail_nil_shape]
        exact
          ⟨18, by
            simpa using
              markedPrefix_run_marked_tail_done_stageNat_to_state200 limit
                (stageNatBits fuel)⟩
  | cons b rest =>
      refine
        fuelSimulatorCore_forward_marked_of_tail_shape
          (stageInputSecondBitTailPrefix (b :: rest)) limit fuel
          (fuelSimulatorInputSecondBitTail
            { w := b :: rest, limit := limit, fuel := fuel })
          ?_ ?_
      · rw [fuelSimulatorInputSecondBitTail_cons_shape]
        simp [stageInputSecondBitTailPrefix, List.append_assoc]
      · rw [fuelSimulatorInputSecondBitTail_cons_shape]
        exact
          markedPrefix_run_marked_tail_nonempty_to_state200 b rest limit
            (stageNatBits fuel)

theorem fuelSimulatorStageInputMarkedCoreDescription_forward
    (i : FuelSimulatorStructuredIndex) :
    exists steps : Nat,
      (StageInputMarkedCoreDescription
          fuelSimulatorInputRecognizerCoreDescription).runConfig steps
          ((StageInputMarkedCoreDescription
            fuelSimulatorInputRecognizerCoreDescription).initial
              (fuelSimulatorInputBits i)) =
        { state :=
            (StageInputMarkedCoreDescription
              fuelSimulatorInputRecognizerCoreDescription).halt
          tape :=
            fuelSimulatorInputSecondBitMarkedCheckedHandoffTape i } := by
  let A := MarkStageInputSecondBitDescription
  let B := fuelSimulatorInputRecognizerCoreDescription
  have hArun :
      A.runConfig 3
          { state := A.start
            tape := Tape.input (fuelSimulatorInputBits i) } =
        { state := A.halt
          tape := fuelSimulatorInputSecondBitMarkedTape i } := by
    simpa [A, initial] using
      markStageInputSecondBitDescription_run_fuel i
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape :=
                Tape.move Direction.right
                  (fuelSimulatorInputSecondBitMarkedTape i) } =
          { state := B.halt
            tape :=
              fuelSimulatorInputSecondBitMarkedCheckedHandoffTape i } := by
    simpa [B, fuelSimulatorInputSecondBitMarkedHandoffTape] using
      fuelSimulatorInputRecognizerCoreDescription_forward_marked i
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        markStageInputSecondBitDescription_ready
        fuelSimulatorInputRecognizerCoreDescription_ready
        hArun hBReach with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [StageInputMarkedCoreDescription, A, B,
    initial] using hsteps

theorem fuelSimulatorStageInputRecognizerDescription_forward_checked
    (i : FuelSimulatorStructuredIndex) :
    exists steps : Nat,
      (StageInputRecognizerDescription
        (StageInputMarkedCoreDescription
          fuelSimulatorInputRecognizerCoreDescription)).runConfig steps
          ((StageInputRecognizerDescription
            (StageInputMarkedCoreDescription
              fuelSimulatorInputRecognizerCoreDescription)).initial
              (fuelSimulatorInputBits i)) =
        { state :=
            (StageInputRecognizerDescription
              (StageInputMarkedCoreDescription
                fuelSimulatorInputRecognizerCoreDescription)).halt
          tape := fuelSimulatorInputCheckedInputTape i } := by
  let A :=
    StageInputMarkedCoreDescription
      fuelSimulatorInputRecognizerCoreDescription
  let B := RestoreStageInputSecondBitDescription
  have hAready : A.SubroutineReady := by
    simpa [A, StageInputMarkedCoreDescription] using
      seqSubroutine_subroutineReady
        markStageInputSecondBitDescription_ready
        fuelSimulatorInputRecognizerCoreDescription_ready
  have hBready : B.SubroutineReady :=
    restoreStageInputSecondBitDescription_ready
  rcases fuelSimulatorStageInputMarkedCoreDescription_forward i with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape := Tape.input (fuelSimulatorInputBits i) } =
        { state := A.halt
          tape := fuelSimulatorInputSecondBitMarkedCheckedHandoffTape i } := by
    simpa [A, initial] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape :=
                Tape.move Direction.left
                  (fuelSimulatorInputSecondBitMarkedCheckedHandoffTape i) } =
          { state := B.halt
            tape := fuelSimulatorInputCheckedInputTape i } := by
    refine ⟨1, ?_⟩
    rw [fuelSimulatorInputSecondBitMarkedCheckedHandoffTape_move_left]
    simpa [B] using
      restoreStageInputSecondBitDescription_run_checked_fuel i
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [StageInputRecognizerDescription, A, B,
    initial] using hsteps

def fuelSimulatorInputRecognizerDescription : MachineDescription :=
  StageInputIdentityDescription
    (StageInputRecognizerDescription
      (StageInputMarkedCoreDescription fuelSimulatorInputRecognizerCoreDescription))

theorem fuelSimulatorInputRecognizerDescription_forward_checked
    (i : FuelSimulatorStructuredIndex) :
    fuelSimulatorInputRecognizerDescription.HaltsFromTape
      (fuelSimulatorStructuredInputTape i)
      (fuelSimulatorInputCheckedValidatorTape i) := by
  let A :=
    StageInputRecognizerDescription
      (StageInputMarkedCoreDescription
        fuelSimulatorInputRecognizerCoreDescription)
  let B := ExactIdentityDescription
  have hAready : A.SubroutineReady := by
    have hmarked :
        (StageInputMarkedCoreDescription
          fuelSimulatorInputRecognizerCoreDescription).SubroutineReady := by
      simpa [StageInputMarkedCoreDescription] using
        seqSubroutine_subroutineReady
          markStageInputSecondBitDescription_ready
          fuelSimulatorInputRecognizerCoreDescription_ready
    simpa [A, StageInputRecognizerDescription] using
      seqSubroutine_subroutineReady
        hmarked
        restoreStageInputSecondBitDescription_ready
  have hBready : B.SubroutineReady :=
    ⟨exactIdentityDescription_wellFormed,
      exactIdentityDescription_haltTransitionFree⟩
  rcases fuelSimulatorStageInputRecognizerDescription_forward_checked i with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape := Tape.input (fuelSimulatorInputBits i) } =
        { state := A.halt
          tape := fuelSimulatorInputCheckedInputTape i } := by
    simpa [A, initial] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape :=
                Tape.move Direction.right
                  (fuelSimulatorInputCheckedInputTape i) } =
          { state := B.halt
            tape := fuelSimulatorInputCheckedValidatorTape i } := by
    refine ⟨0, ?_⟩
    simp [B, fuelSimulatorInputCheckedValidatorTape,
      runConfig, ExactIdentityDescription]
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_, ?_⟩
  · simpa [fuelSimulatorInputRecognizerDescription,
      fuelSimulatorStructuredInputTape,
      fuelSimulatorInputBits,
      EncRewriters.CanonicalLayouts.Bits,
      A, B, initial] using!
      congrArg MachineDescription.Configuration.state hsteps
  · simpa [fuelSimulatorInputRecognizerDescription,
      fuelSimulatorStructuredInputTape,
      fuelSimulatorInputBits,
      EncRewriters.CanonicalLayouts.Bits,
      A, B, initial] using!
      congrArg Configuration.tape hsteps

theorem fuelSimulatorInputRecognizerDescription_ready :
    fuelSimulatorInputRecognizerDescription.SubroutineReady := by
  have hmarked :
      (StageInputMarkedCoreDescription
        fuelSimulatorInputRecognizerCoreDescription).SubroutineReady := by
    simpa [StageInputMarkedCoreDescription] using
      seqSubroutine_subroutineReady
        markStageInputSecondBitDescription_ready
        fuelSimulatorInputRecognizerCoreDescription_ready
  have hrecognizer :
      (StageInputRecognizerDescription
        (StageInputMarkedCoreDescription
          fuelSimulatorInputRecognizerCoreDescription)).SubroutineReady := by
    simpa [StageInputRecognizerDescription] using
      seqSubroutine_subroutineReady
        hmarked
        restoreStageInputSecondBitDescription_ready
  simpa [fuelSimulatorInputRecognizerDescription,
    StageInputIdentityDescription] using
    seqSubroutine_subroutineReady
      hrecognizer
      ⟨exactIdentityDescription_wellFormed,
        exactIdentityDescription_haltTransitionFree⟩

theorem fuelSimulatorInputRecognizerDescription_forward
    (i : FuelSimulatorStructuredIndex) :
    fuelSimulatorInputRecognizerDescription.HaltsFromTapeEquiv
      (fuelSimulatorStructuredInputTape i)
      (EncRewriters.CanonicalLayouts.HandoffTape fuelSimulatorStructuredInputCode i) := by
  exact
    ⟨fuelSimulatorInputCheckedValidatorTape i,
      fuelSimulatorInputRecognizerDescription_forward_checked i,
      fuelSimulatorInputCheckedValidatorTape_equiv_handoff i⟩

/--
Core decode inversion: if the marked stage-prefix + closed-fuel-nat scanner core
halts from the marked handoff tape of some tail, then the originating code
decodes into the FuelSimulator input family.  The proof splits on the parse of
the code: a successful parse with a nonempty suffix follows the forward run to
the fuel scanner, which forces the suffix to be an exact fuel nat; an exact
stage-input parse or a failed parse contradicts the halting run via the base
scanner's closed spec or the marking-loop leaf.
-/
theorem fuelSimulatorInputRecognizerCoreDescription_closedDecode
    (code : Word MachineCodeSymbol) (tail : Word Bool) (Tmid : Tape Bool)
    (hbits : encodeCodeWordAsInput code = false :: false :: tail)
    (hmark :
      MarkStageInputSecondBitDescription.HaltsWithTape
        (encodeCodeWordAsInput code)
        (DovetailInitialLayoutInitializer.tapeAtCells [some false]
          (none :: tail.map some)))
    (hcore :
      exists nB : Nat,
        fuelSimulatorInputRecognizerCoreDescription.runConfig nB
            { state := fuelSimulatorInputRecognizerCoreDescription.start
              tape :=
                Tape.move Direction.right
                  (DovetailInitialLayoutInitializer.tapeAtCells [some false]
                    (none :: tail.map some)) } =
          { state := fuelSimulatorInputRecognizerCoreDescription.halt
            tape := Tmid }) :
    exists i : FuelSimulatorStructuredIndex,
      decodeFuelSimulatorStructuredInputCode code = some i := by
  -- Peel the marked-prefix/fuel-suffix sequence.
  have hcoreFrom :
      fuelSimulatorInputRecognizerCoreDescription.HaltsFromTape
        (Tape.move Direction.right
          (DovetailInitialLayoutInitializer.tapeAtCells [some false]
            (none :: tail.map some))) Tmid := by
    rcases hcore with ⟨nB, hnB⟩
    refine ⟨nB, ?_, ?_⟩
    · simpa using congrArg MachineDescription.Configuration.state hnB
    · simpa using congrArg MachineDescription.Configuration.tape hnB
  obtain ⟨TmidMP, hMPFrom, nNat, hNatRun⟩ :=
    seqSubroutine_haltsFromTape_inv
      markedPrefixScannerDescription_subroutineReady
      natClosedScannerDescription_ready hcoreFrom
  obtain ⟨nA, hMPrun⟩ := runConfig_eq_halt_of_haltsFromTape hMPFrom
  rw [show ({ state := MarkedPrefixScannerDescription.start
              tape :=
                Tape.move Direction.right
                  (DovetailInitialLayoutInitializer.tapeAtCells [some false]
                    (none :: tail.map some)) } :
        MachineDescription.Configuration) = markedTailStartConfig tail
      from rfl] at hMPrun
  -- Either the marked-prefix run agrees with the base scanner run (whose
  -- closed spec pins the parse and the handoff tape), or the base run visited
  -- state 210 over a bit (and the marking-loop leaf pins a nonempty parse).
  have hdisj :=
    markedPrefix_runConfig_eq_sims_or_reaches_state210_bit nA
      (markedTailStartConfig tail)
  have hspecOf :
      MarkedPrefixScannerDescription.runConfig nA
          (markedTailStartConfig tail) =
        StageInputMarkedScannerDescription.runConfig nA
          (markedTailStartConfig tail) ->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          TmidMP = stageInputSecondBitMarkedCheckedHandoffTape w stage := by
    intro heq
    refine
      stageInputMarkedScannerDescription_spec.2.2 code
        (DovetailInitialLayoutInitializer.tapeAtCells [some false]
          (none :: tail.map some)) TmidMP hmark ⟨nA, ?_⟩
    rw [show ({ state := StageInputMarkedScannerDescription.start
                tape :=
                  Tape.move Direction.right
                    (DovetailInitialLayoutInitializer.tapeAtCells [some false]
                      (none :: tail.map some)) } :
          MachineDescription.Configuration) = markedTailStartConfig tail
        from rfl]
    rw [← heq]
    exact hMPrun
  have hleafOf :
      (exists m : Nat,
        m < nA ∧
          (StageInputMarkedScannerDescription.runConfig m
            (markedTailStartConfig tail)).state = 210 ∧
            (Tape.read
              (StageInputMarkedScannerDescription.runConfig m
                (markedTailStartConfig tail)).tape).isSome) ->
      exists w : Word Bool,
      exists limit : Nat,
      exists symbol : MachineCodeSymbol,
      exists rest : Word MachineCodeSymbol,
        DovetailLayout.decodeStageInput code =
          some ((w, limit), symbol :: rest) := by
    rintro ⟨m, -, h210, hread⟩
    exact
      sims_marked_code_tail_reach210_decodeStageInput code tail m
        hbits h210 hread
  cases hdec : DovetailLayout.decodeStageInput code with
  | none =>
      exfalso
      rcases hdisj with heq | hreach
      · obtain ⟨w', stage', hcode', -⟩ := hspecOf heq
        rw [hcode'] at hdec
        simp [PairedRecognizerDovetailStageInputCode,
          DovetailLayout.decodeStageInput_stageInputCode] at hdec
      · obtain ⟨w', limit', symbol', rest', hsome⟩ := hleafOf hreach
        rw [hdec] at hsome
        simp at hsome
  | some parsed =>
      rcases parsed with ⟨⟨w, limit⟩, suffix⟩
      have hcodeEq :
          code = DovetailLayout.stageInputCodeAppend w limit suffix :=
        DovetailLayout.decodeStageInput_eq_some_stageInputCodeAppend hdec
      cases suffix with
      | nil =>
          -- An exact stage-input code has no fuel suffix: the closed fuel
          -- scanner would have to halt from a checked handoff tape, where it
          -- is stuck within two steps.
          exfalso
          rcases hdisj with heq | hreach
          · obtain ⟨w', stage', -, hTcheck⟩ := hspecOf heq
            rw [hTcheck] at hNatRun
            have hclosed :
                StageInputMarkedScannerDescription.runConfig nNat
                    { state := 200
                      tape :=
                        Tape.move Direction.right
                          (stageInputSecondBitMarkedCheckedHandoffTape
                            w' stage') } =
                  { state := StageInputMarkedScannerDescription.halt
                    tape := Tmid } := by
              rw [← runConfig_eq_of_transitions_eq NatClosedScannerDescription
                StageInputMarkedScannerDescription (by rfl)]
              exact hNatRun
            exact
              sims_state200_checked_handoff_ne_halt w' stage' nNat
                (by
                  simpa using
                    congrArg MachineDescription.Configuration.state hclosed)
          · obtain ⟨w', limit', symbol', rest', hsome⟩ := hleafOf hreach
            rw [hdec] at hsome
            injection hsome with hsome
            injection hsome with hpair hnil
            cases hnil
      | cons symbol rest' =>
          -- The parse has a nonempty suffix: run the marked-prefix scanner
          -- forward to its handoff and let the closed fuel scanner force the
          -- suffix to be an exact fuel nat.
          obtain ⟨b0, bits0, hcons⟩ :=
            encodeCodeWordAsInput_cons_head symbol rest'
          have htail :
              tail =
                List.append (stageInputSecondBitTail w limit)
                  (encodeCodeWordAsInput (symbol :: rest')) := by
            have hb :
                encodeCodeWordAsInput code =
                  List.append (stageInputBits w limit)
                    (encodeCodeWordAsInput (symbol :: rest')) := by
              rw [hcodeEq, stageInputCodeAppend_eq_append,
                encodeCodeWordAsInput_append]
              rfl
            rw [hbits, stageInputBits_eq_false_false_tail] at hb
            injection hb with _ hb
            injection hb with _ hb
          have htail' :
              tail =
                List.append (stageInputSecondBitTailPrefix w)
                  (List.append (stageNatBits limit) (b0 :: bits0)) := by
            rw [htail, hcons, stageInputSecondBitTail_eq_prefix_stageNat]
            simp [List.append_assoc]
          obtain ⟨baseLeft, nF, hforward⟩ :
              exists baseLeft : List (Option Bool),
              exists nF : Nat,
                MarkedPrefixScannerDescription.runConfig nF
                    (markedTailStartConfig tail) =
                  config 200 baseLeft
                    (List.append ((stageNatBits limit).map some)
                      ((b0 :: bits0).map some)) := by
            cases w with
            | nil =>
                refine ⟨[some true, some true, none, some false], 18, ?_⟩
                rw [htail']
                simpa [stageInputSecondBitTailPrefix] using
                  markedPrefix_run_marked_tail_done_stageNat_to_state200
                    limit (b0 :: bits0)
            | cons wb wrest =>
                rcases markedPrefix_run_marked_tail_nonempty_to_state200 wb
                    wrest limit (b0 :: bits0) with ⟨steps, hsteps⟩
                refine
                  ⟨List.append
                      ((stageInputSecondBitTailPrefix
                        (wb :: wrest)).reverse.map some)
                      (none :: [some false]), steps, ?_⟩
                rw [htail']
                simpa [stageInputSecondBitTailPrefix, List.append_assoc]
                  using hsteps
          obtain ⟨nH, hhandoff⟩ :=
            run_markedPrefix_raw_to_handoff_withBase limit baseLeft b0 bits0
          have hMPhalt :
              MarkedPrefixScannerDescription.runConfig (nF + nH)
                  (markedTailStartConfig tail) =
                { state := MarkedPrefixScannerDescription.halt
                  tape :=
                    (natSuffixHandoffConfigWithBase limit baseLeft
                      (b0 :: bits0)).tape } := by
            rw [runConfig_add, hforward]
            rw [show
                (config 200 baseLeft
                  (List.append ((stageNatBits limit).map some)
                    ((b0 :: bits0).map some))) =
                  (config 200 baseLeft
                    (List.append ((stageNatBits limit).map some)
                      (some b0 :: bits0.map some))) from rfl]
            rw [hhandoff]
            rfl
          have hTmidEq :
              TmidMP =
                (natSuffixHandoffConfigWithBase limit baseLeft
                  (b0 :: bits0)).tape :=
            runConfig_halt_tape_functional_from_config
              markedPrefixScannerDescription_haltTransitionFree hMPrun hMPhalt
          have hmove :
              Tape.move Direction.right TmidMP =
                DovetailInitialLayoutInitializer.tapeAtCells
                  (List.append ((stageNatBits limit).reverse.map some)
                    baseLeft)
                  ((b0 :: bits0).map some) := by
            rw [hTmidEq]
            exact
              natSuffixHandoffConfigWithBase_move_right limit baseLeft b0 bits0
          rw [hmove,
            show ((b0 :: bits0 : Word Bool)) =
              encodeCodeWordAsInput (symbol :: rest') from hcons.symm]
            at hNatRun
          have hSIMS :
              StageInputMarkedScannerDescription.runConfig nNat
                  (config 200
                    (List.append ((stageNatBits limit).reverse.map some)
                      baseLeft)
                    ((encodeCodeWordAsInput (symbol :: rest')).map some)) =
                { state := StageInputMarkedScannerDescription.halt
                  tape := Tmid } := by
            rw [← runConfig_eq_of_transitions_eq NatClosedScannerDescription
              StageInputMarkedScannerDescription (by rfl)]
            exact hNatRun
          obtain ⟨fuel, hfuel⟩ :=
            state200_code_tail_nat_inv (T := Tmid) ⟨nNat, hSIMS⟩
          refine ⟨⟨w, limit, fuel⟩, ?_⟩
          have hfuel' : symbol :: rest' = encodeNatAppend fuel [] := by
            simpa [encodeNatAppend] using! hfuel
          simp [decodeFuelSimulatorStructuredInputCode, hdec, hfuel',
            decodeNat_encodeNatAppend]

/--
Peels the marker/recognizer/identity wrappers off a halting run of the full
recognizer, reducing closedness to the core decode inversion above.
-/
theorem fuelSimulatorInputRecognizerDescription_closedDecode
    (code : Word MachineCodeSymbol) (T : Tape Bool)
    (h :
      fuelSimulatorInputRecognizerDescription.HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    exists i : FuelSimulatorStructuredIndex,
      decodeFuelSimulatorStructuredInputCode code = some i := by
  have hSIMCready :
      (StageInputMarkedCoreDescription
        fuelSimulatorInputRecognizerCoreDescription).SubroutineReady := by
    simpa [StageInputMarkedCoreDescription] using
      seqSubroutine_subroutineReady
        markStageInputSecondBitDescription_ready
        fuelSimulatorInputRecognizerCoreDescription_ready
  have hSIRready :
      (StageInputRecognizerDescription
        (StageInputMarkedCoreDescription
          fuelSimulatorInputRecognizerCoreDescription)).SubroutineReady := by
    simpa [StageInputRecognizerDescription] using
      seqSubroutine_subroutineReady
        hSIMCready
        restoreStageInputSecondBitDescription_ready
  have hIdReady : ExactIdentityDescription.SubroutineReady :=
    ⟨exactIdentityDescription_wellFormed,
      exactIdentityDescription_haltTransitionFree⟩
  obtain ⟨Tmid1, hSIR, _hId⟩ :=
    seqSubroutine_haltsWithTape_inv
      (A :=
        StageInputRecognizerDescription
          (StageInputMarkedCoreDescription
            fuelSimulatorInputRecognizerCoreDescription))
      (B := ExactIdentityDescription)
      (handoffMove := Direction.right)
      hSIRready hIdReady h
  obtain ⟨Tmid2, hSIMC, _hRestore⟩ :=
    seqSubroutine_haltsWithTape_inv
      (A :=
        StageInputMarkedCoreDescription
          fuelSimulatorInputRecognizerCoreDescription)
      (B := RestoreStageInputSecondBitDescription)
      (handoffMove := Direction.left)
      hSIMCready restoreStageInputSecondBitDescription_ready hSIR
  obtain ⟨Tmark, hMSIB, nB, hcoreRun⟩ :=
    seqSubroutine_haltsWithTape_inv
      (A := MarkStageInputSecondBitDescription)
      (B := fuelSimulatorInputRecognizerCoreDescription)
      (handoffMove := Direction.right)
      markStageInputSecondBitDescription_ready
      fuelSimulatorInputRecognizerCoreDescription_ready hSIMC
  obtain ⟨tail, hbits, hTmark⟩ :=
    markStageInputSecondBitDescription_haltsWithTape_inv hMSIB
  rw [hTmark] at hMSIB hcoreRun
  exact
    fuelSimulatorInputRecognizerCoreDescription_closedDecode
      code tail Tmid2 hbits hMSIB ⟨nB, hcoreRun⟩

theorem fuelSimulatorInputRecognizerDescription_closedCanonical
    (code : Word MachineCodeSymbol) (T : Tape Bool)
    (h :
      fuelSimulatorInputRecognizerDescription.HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    ∃ i : FuelSimulatorStructuredIndex,
      decodeFuelSimulatorStructuredInputCode code = some i ∧
      Tape.Equiv T
        (EncRewriters.CanonicalLayouts.HandoffTape
          fuelSimulatorStructuredInputCode i) := by
  obtain ⟨i, hdec⟩ :=
    fuelSimulatorInputRecognizerDescription_closedDecode code T h
  refine ⟨i, hdec, ?_⟩
  have hcode : code = fuelSimulatorStructuredInputCode i :=
    decodeFuelSimulatorStructuredInputCode_eq_some_encode hdec
  have hFromTape :
      fuelSimulatorInputRecognizerDescription.HaltsFromTape
        (fuelSimulatorStructuredInputTape i) T := by
    have htape :
        fuelSimulatorStructuredInputTape i =
          Tape.input (encodeCodeWordAsInput code) := by
      rw [hcode]; rfl
    rw [htape]
    exact h
  have hT : T = fuelSimulatorInputCheckedValidatorTape i :=
    haltsFromTape_functional_of_haltTransitionFree
      fuelSimulatorInputRecognizerDescription_ready.right
      hFromTape
      (fuelSimulatorInputRecognizerDescription_forward_checked i)
  rw [hT]
  exact fuelSimulatorInputCheckedValidatorTape_equiv_handoff i

theorem fuelSimulatorInputRecognizerDescription_equivRunSpec :
    FuelSimulatorInputRecognizerEquivRunSpec
      fuelSimulatorInputRecognizerDescription := by
  constructor
  · exact fuelSimulatorInputRecognizerDescription_ready
  · exact fuelSimulatorInputRecognizerDescription_forward
  · exact fuelSimulatorInputRecognizerDescription_closedCanonical

theorem fuelSimulatorInputRecognizerDescription_spec :
    FuelSimulatorInputRecognizerSpec
      fuelSimulatorInputRecognizerDescription :=
  fuelSimulatorInputRecognizerSpec_of_equivRunSpec
    fuelSimulatorInputRecognizerDescription_equivRunSpec

theorem fuelSimulatorInputRecognizerConstruction_core :
    FuelSimulatorInputRecognizerConstruction :=
  ⟨fuelSimulatorInputRecognizerDescription,
    fuelSimulatorInputRecognizerDescription_spec⟩

end StructuredConstructionTargets

end Computability
end FoC
