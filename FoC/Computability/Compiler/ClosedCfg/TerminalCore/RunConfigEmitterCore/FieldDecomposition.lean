import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.StateClassifier
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterTheory.ScratchWidth
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoder.StructuredBody
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.OptionCellExpandAppendSpec
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutputCore.Runs
import FoC.Computability.Compiler.Dovetail.Scanner.Simulator.Definitions

set_option doc.verso true

/-!
# Simulator-layout field-decomposition boundary

After the #18 input materializer, logical tape 0 contains the complete encoded
simulator layout and logical tapes 1 and 2 are blank.  The execution loops need
a different representation: the live configuration tape on tape 0, a raw
unary stage counter on tape 1, and self-delimiting preserved metadata with the
hit bit at the head of tape 2.

This module names that exact boundary and records the clean reusable prefix of
the physical route.  The existing structured Boolean-word decoder can expose
the input field, but it does not materialize the stage counter or decode the
configuration.  Its padded source and output-buffer initialization also differ
exactly from the post-embedding boundary.  Consequently the construction
contract below remains the honest integrated parser/decomposer obligation.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CanonicalLayouts.DovetailLayoutScanner
open CanonicalLayouts.SimulatorLayoutScanner
open StructuredConstructionTargets.FuelOutputCore

/-!
## Preserved loop metadata
-/

/-- Fields that must survive counter consumption but are not the live
configuration tape.  The original raw state is retained for the generic
classifier branch; known-state execution may instead keep its changing state
in finite control. -/
structure Metadata where
  input : Word Bool
  stage : Nat
  state : Nat

/-- Canonical self-delimiting metadata code. -/
def Metadata.encodeAppend
    (M : Metadata) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  encodeBoolWordAppend M.input
    (encodeNatAppend M.stage
      (encodeNatAppend M.state suffix))

def Metadata.encode (M : Metadata) : Word MachineCodeSymbol :=
  M.encodeAppend []

/-- Executable inverse of the preserved metadata code. -/
def Metadata.decode
    (tokens : Word MachineCodeSymbol) :
    Option (Metadata × Word MachineCodeSymbol) :=
  match decodeBoolWord tokens with
  | none => none
  | some (input, rest) =>
      match decodeNat rest with
      | none => none
      | some (stage, rest) =>
          match decodeNat rest with
          | none => none
          | some (state, suffix) =>
              some (⟨input, stage, state⟩, suffix)

theorem Metadata.decode_encodeAppend
    (M : Metadata) (suffix : Word MachineCodeSymbol) :
    Metadata.decode (M.encodeAppend suffix) = some (M, suffix) := by
  cases M
  simp [Metadata.decode, Metadata.encodeAppend,
    decodeBoolWord_encodeBoolWordAppend, decodeNat_encodeNatAppend]

/-- Metadata extracted from an ordinary simulator layout. -/
def metadata (L : SimulatorLayout) : Metadata :=
  ⟨L.input, L.stage, L.config.state⟩

/-- Boolean encoding stored immediately left of the hit head. -/
def metadataBits (L : SimulatorLayout) : Word Bool :=
  encodeCodeWordAsInput (metadata L).encode

/-- Cells to the left of the live hit head.  The original-input scratch width
is carried as a raw unary block immediately left of the head, independently of
the final configuration encoding.  A blank separates it from the canonical
input/stage/raw-state metadata. -/
def metadataPrefixCells (L : SimulatorLayout) : List (Option Bool) :=
  List.append ((metadataBits L).map some)
    (none :: RunConfigEmitterTheory.scratchWidthMarkers L)

/-- Metadata tape with a caller-selected live hit value. -/
def metadataHitTapeWithHit
    (L : SimulatorLayout) (hit : Bool) : Tape Bool :=
  tapeAtCells (metadataPrefixCells L).reverse [some hit, none]

/-- Tape-2 loop layout: canonical metadata and the independent scratch-width
marker block lie to the left, the live hit bit is at the head, and one explicit
blank is retained on the right. -/
def metadataHitTape (L : SimulatorLayout) : Tape Bool :=
  metadataHitTapeWithHit L L.hit

@[simp] theorem metadataHitTape_read (L : SimulatorLayout) :
    Tape.read (metadataHitTape L) = some L.hit := by
  rfl

@[simp] theorem metadataHitTapeWithHit_read
    (L : SimulatorLayout) (hit : Bool) :
    Tape.read (metadataHitTapeWithHit L hit) = some hit := by
  rfl

@[simp] theorem writeS_apply_metadataHitTapeWithHit
    (L : SimulatorLayout) (oldHit newHit : Bool) :
    (writeS (some newHit)).apply (metadataHitTapeWithHit L oldHit) =
      metadataHitTapeWithHit L newHit := by
  rfl

theorem metadataHitTape_cells (L : SimulatorLayout) :
    Tape.cells (metadataHitTape L) =
      List.append (metadataPrefixCells L) [some L.hit, none] := by
  simp [metadataHitTape, metadataHitTapeWithHit, tapeAtCells, Tape.cells]

theorem metadataHitTape_cells_eq_fields (L : SimulatorLayout) :
    Tape.cells (metadataHitTape L) =
      List.append ((metadataBits L).map some)
        (none ::
          List.append (RunConfigEmitterTheory.scratchWidthMarkers L)
            [some L.hit, none]) := by
  rw [metadataHitTape_cells]
  simp [metadataPrefixCells, List.append_assoc]

/-- The independently carried unary block counts every original source bit
except the bit initially under the input head. -/
theorem scratchWidthMarkers_length_add_one (L : SimulatorLayout) :
    (RunConfigEmitterTheory.scratchWidthMarkers L).length + 1 =
      (SimulatorLayout.asBoolInput L).length := by
  rw [RunConfigEmitterTheory.scratchWidthMarkers_length]
  exact
    RunConfigEmitterTheory.fixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_add_one
      L

theorem metadata_decode (L : SimulatorLayout) :
    Metadata.decode (metadata L).encode = some (metadata L, []) := by
  exact Metadata.decode_encodeAppend (metadata L) []

/-!
## Exact post-decomposition layout
-/

/-- Raw stage counter consumed by either execution loop. -/
def stageCounterTape (stage : Nat) : Tape Bool :=
  tapeAtCells []
    (List.append
      (List.replicate stage (some true : Option Bool)) [none])

@[simp] theorem stageCounterTape_read_zero :
    Tape.read (stageCounterTape 0) = none := by
  rfl

@[simp] theorem stageCounterTape_read_succ (stage : Nat) :
    Tape.read (stageCounterTape (stage + 1)) = some true := by
  simp [stageCounterTape, tapeAtCells, Tape.read, List.replicate_succ]

/-- Exact logical tapes needed at the known/other dispatcher boundary. -/
def loopTapes (L : SimulatorLayout) : List (Tape Bool) :=
  [L.config.tape, stageCounterTape L.stage, metadataHitTape L]

/-- Physical post-embedding source produced by the checked #18 input
materializer. -/
def embeddedSourceTape (L : SimulatorLayout) : Tape Bool :=
  StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape
    (SimulatorLayout.asBoolInput L)

/-- Exact guarded physical target for the integrated field decomposer. -/
def loopTargetTape (L : SimulatorLayout) : Tape Bool :=
  encodedGuardedStructuredTapes (loopTapes L)

theorem embeddedSourceTape_eq_guarded (L : SimulatorLayout) :
    embeddedSourceTape L =
      encodedGuardedStructuredTapes
        [ Tape.input (SimulatorLayout.asBoolInput L)
        , Tape.blank
        , Tape.blank ] := by
  rw [embeddedSourceTape]
  rw [StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget]
  rfl

theorem loopTargetTape_eq_guarded (L : SimulatorLayout) :
    loopTargetTape L =
      encodedGuardedStructuredTapes
        [ L.config.tape
        , stageCounterTape L.stage
        , metadataHitTape L ] := by
  rfl

/-- Honest remaining physical construction boundary.  The output is stated up
to physical tape equivalence because lowering and parking may retain harmless
outer window blanks; the encoded logical fields themselves are fixed by
{name}`loopTargetTape`. -/
def Spec (decomposer : MachineDescription) : Prop :=
  decomposer.SubroutineReady ∧
    forall L : SimulatorLayout,
      decomposer.HaltsFromTapeEquiv
        (embeddedSourceTape L) (loopTargetTape L)

def Construction : Prop :=
  exists decomposer : MachineDescription, Spec decomposer

/-- Semantic dispatch available once the raw state field has been parsed. -/
theorem classify_layout_state_cases
    (D : MachineDescription) (L : SimulatorLayout) :
    (exists hstate : L.config.state ∈ fixedStepValues D,
      classifyState D L.config.state =
        StateClass.known L.config.state hstate) ∨
      classifyState D L.config.state = StateClass.other := by
  by_cases hstate : L.config.state ∈ fixedStepValues D
  · exact Or.inl ⟨hstate, classifyState_of_mem hstate⟩
  · exact Or.inr (classifyState_of_not_mem hstate)

/-!
## Clean reusable input-field prefix
-/

/-- Axiom-clean exact token decomposition supplied by the closed fuel-output
core.  Its typed phase table is the closest existing parser template: it walks
the input length/bits, stage, state, both configuration cell lists and head,
and the hit field. -/
theorem source_encode_decomp (L : SimulatorLayout) :
    SimulatorLayout.encode L =
      MachineCodeSymbol.header ::
        List.append (encodeNat (L.input.map some).length)
          (List.append ((L.input.map some).map cellTok)
            (List.append (encodeNat L.stage)
              (List.append (encodeNat L.config.state)
                (List.append (encodeNat L.config.tape.left.length)
                  (List.append (L.config.tape.left.map cellTok)
                    (cellTok L.config.tape.head ::
                      List.append (encodeNat L.config.tape.right.length)
                        (List.append (L.config.tape.right.map cellTok)
                          (List.append [cellTok (some L.hit)]
                            ([] : Word MachineCodeSymbol))))))))) :=
  encode_decomp L

/-- Encoded fields following the Boolean input word. -/
def postInputBits (L : SimulatorLayout) : Word Bool :=
  List.append (stageNatBits L.stage)
    (configurationFieldBits L.config (boolFieldBits L.hit []))

/-- Tail following the first bit of the stage field. -/
def postInputTail (L : SimulatorLayout) : Word Bool :=
  List.append (stageNatBits L.stage).tail
    (configurationFieldBits L.config (boolFieldBits L.hit []))

theorem postInputBits_eq_false_cons (L : SimulatorLayout) :
    postInputBits L = false :: postInputTail L := by
  cases hstage : L.stage with
  | zero =>
      simp [postInputBits, postInputTail, hstage, stageNatBits_zero]
  | succ stage =>
      simp [postInputBits, postInputTail, hstage, stageNatBits_succ]

/-- The complete simulator layout is exactly the source grammar consumed by
the existing structured Boolean-word decoder. -/
theorem asBoolInput_eq_boolWordDecoderFields (L : SimulatorLayout) :
    SimulatorLayout.asBoolInput L =
      List.append boolWordRawBitsDecoderHeaderBits
        (List.append
          (boolWordRawBitsDecoderEncodedFieldBits L.input)
          (false :: postInputTail L)) := by
  have hfields :
      SimulatorLayout.asBoolInput L = simulatorLayoutFieldBits L [] := by
    simpa [SimulatorLayout.asBoolInput, SimulatorLayout.encode,
      encodeCodeWordAsInput] using
      (simulatorLayoutFieldBits_eq_encodeAppend L [])
  rw [hfields]
  rw [simulatorLayoutFieldBits]
  rw [show
      List.append (stageNatBits L.stage)
          (configurationFieldBits L.config (boolFieldBits L.hit [])) =
        postInputBits L by rfl]
  rw [postInputBits_eq_false_cons]
  simp [boolWordFieldBits, cellListFieldBits,
    boolWordRawBitsDecoderHeaderBits,
    boolWordRawBitsDecoderEncodedFieldBits,
    headerPrefixBits, List.append_assoc]

/-- Exact logical tape expected by the reusable Boolean-input decoder. -/
def inputDecoderSourceTape (L : SimulatorLayout) : Tape Bool :=
  boolWordRawBitsDecoderSourceTape L.input (postInputTail L) []

theorem inputDecoderSourceTape_eq_rightEdgeRewindTarget
    (L : SimulatorLayout) :
    inputDecoderSourceTape L =
      rightEdgeRewindTargetTape (SimulatorLayout.asBoolInput L) [] := by
  unfold inputDecoderSourceTape boolWordRawBitsDecoderSourceTape
  rw [asBoolInput_eq_boolWordDecoderFields]

/-- The available decoder source differs from the embedded logical tape only
by far-edge blank padding. -/
theorem inputDecoderSourceTape_equiv_input (L : SimulatorLayout) :
    Tape.Equiv (inputDecoderSourceTape L)
      (Tape.input (SimulatorLayout.asBoolInput L)) := by
  rw [inputDecoderSourceTape_eq_rightEdgeRewindTarget]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      have hlen :=
        RunConfigEmitterTheory.simulatorLayout_asBoolInput_length_ge_two L
      simp [hbits] at hlen
  | cons bit rest =>
      simp [rightEdgeRewindTargetTape, tapeAtCells, Tape.input,
        Tape.Equiv, Tape.dropTrailingNone,
        dropTrailingNone_append_none]

/-- The padding difference is real equality-wise, so the decoder cannot be
placed immediately after the exact canonical embedding without an ingress
adapter or an equivalence transport at structured semantics. -/
theorem inputDecoderSourceTape_ne_input (L : SimulatorLayout) :
    inputDecoderSourceTape L ≠
      Tape.input (SimulatorLayout.asBoolInput L) := by
  intro heq
  have hleft := congrArg Tape.left heq
  rw [inputDecoderSourceTape_eq_rightEdgeRewindTarget] at hleft
  cases hbits : SimulatorLayout.asBoolInput L <;>
    simp [rightEdgeRewindTargetTape, tapeAtCells, Tape.input, hbits] at hleft
  change [none] = [] at hleft
  contradiction

/-- Tape 2 has the same exact ingress mismatch: the reusable decoder expects a
visited left blank, while the embedding supplies the canonical blank tape. -/
theorem inputDecoderInitialOutputTape_ne_blank :
    structuredBoolWordRawBitsDecoderInitialOutputTape ≠ Tape.blank := by
  intro heq
  have hleft := congrArg Tape.left heq
  simp [structuredBoolWordRawBitsDecoderInitialOutputTape,
    tapeAtCells, Tape.blank] at hleft

/-- Exact logical output of the reusable input-field phase.  Tape 0 retains
the encoded suffix at its head, tape 1 contains only consumed-counter blanks,
and tape 2 exposes the raw input word. -/
def inputDecoderTargetTapes (L : SimulatorLayout) : List (Tape Bool) :=
  [ structuredBoolWordRawBitsDecoderSourceTargetTape
      L.input (postInputTail L) []
  , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
      (L.input.length + 1)
  , rightEdgeScanSourceTapeFromLeft [none] L.input [] ]

/-- Checked exact run of the reusable structured input-field decoder. -/
theorem inputDecoder_run (L : SimulatorLayout) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (9 * L.input.length + 11)
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ inputDecoderSourceTape L
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTape ] } =
      { state := structuredBoolWordRawBitsDecoderDescription.halt
        tapes := inputDecoderTargetTapes L } := by
  exact
    structuredBoolWordRawBitsDecoderDescription_run
      L.input (postInputTail L) []

theorem inputDecoder_haltsWithTapes (L : SimulatorLayout) :
    structuredBoolWordRawBitsDecoderDescription.HaltsWithTapes
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ inputDecoderSourceTape L
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTape ] }
        (inputDecoderTargetTapes L) := by
  refine ⟨9 * L.input.length + 11, ?_⟩
  exact inputDecoder_run L

/-!
## Audited physical frontier

The closed fuel-output core is the best implementation template for the
remaining integrated decomposer.  Its typed states already traverse every
token phase, validate the unary state chain, mark the encoded configuration
head, and distinguish both cell-list boundaries.  The adaptation must change
three behaviors:

* emit one scratch marker for every original source bit after the first;
* retain canonical input, original stage, and raw state metadata while
  materializing the exact configuration tape, including blank cells and the
  encoded head split;
* branch through {name}`classifyState` instead of requiring one fixed halt
  state.

The existing fuel-output stream is not an exact configuration extractor:
{name (full := FoC.Computability.StructuredConstructionTargets.FuelOutputCore.layoutStream_reverse)}`FuelOutputCore.layoutStream_reverse` identifies it only with
{name}`Tape.normalizedOutput`, which discards blank cells and the left/head/right
split.  The final exact serializer must therefore operate outside the inner
structured loop, where it can decode the guarded physical representation of
logical tape 0 and recover both finite context lengths.  Importing a generic
normalized-output projector here would make the #18 target false.
-/

end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
