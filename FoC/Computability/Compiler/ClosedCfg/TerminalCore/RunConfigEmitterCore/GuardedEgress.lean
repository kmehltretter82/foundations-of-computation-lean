import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.EgressSemantics
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.PipelineContracts
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.LoopDispatcher
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterTheory.SerializationGuardrails
import FoC.Computability.Compiler.Structured.Lowering.EncodedInjectivity

set_option doc.verso true

/-!
# Exact guarded egress for #18

This module starts from the real post-dispatch data currency.  Logical tape 0
contains the exact final tape window, logical tape 1 is the consumed stage
counter, and logical tape 2 contains compact source metadata, the original
scratch-width markers, and the live final hit bit.  A known dispatcher branch
also carries the final state in finite control; an unmatched branch recovers
that state from the compact metadata.

The branch witness must be materialized before a uniform tape-only serializer
can run.  The committed dispatcher closeout appends its self-delimiting witness
to logical tape 2, after the live hit and its separating blank; logical tape 1
remains the consumed counter.  This makes the semantic target a function of
the physical source and therefore meets the determinism guardrail for the
repaired equivalence-output contract.

The semantic decoder below is executable and exact.  In particular it parses
the guarded logical-tape payload rather than using
{name (full := FoC.Computability.Tape.normalizedOutput)}`Tape.normalizedOutput`,
so stored blank cells and the left/head/right split survive.  The remaining
construction is to realize this checked parse-and-assemble transform by one
finite machine over the guarded physical representation.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace GuardedEgress

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-!
## Exact post-dispatch and witness-materialized sources
-/

/-- Complete semantic index for one guarded egress. -/
structure Index where
  description : MachineDescription
  sourceLayout : SimulatorLayout

def Index.finalLayout (i : Index) : SimulatorLayout :=
  SimulatorLayout.run i.description i.sourceLayout.stage i.sourceLayout

def Index.finalTape (i : Index) : Tape Bool :=
  i.finalLayout.config.tape

def Index.finalHit (i : Index) : Bool :=
  i.finalLayout.hit

def Index.finalState (i : Index) : Nat :=
  i.finalLayout.config.state

theorem Index.finalState_eq (i : Index) :
    i.finalState = i.finalLayout.config.state := by
  rfl

/-- Exhausted logical tape 1 before the branch witness is written. -/
def Index.consumedStageTape (i : Index) : Tape Bool :=
  loopDispatcherConsumedStageCounterTape i.sourceLayout.stage

/-- Logical tape 2 at the dispatcher endpoint. -/
def Index.metadataHitTape (i : Index) : Tape Bool :=
  FieldDecomposition.metadataHitTapeWithHit
    i.sourceLayout i.finalHit

/-- Exact logical post-dispatch tape family, before finite-control state is
made physical. -/
def Index.postDispatchLogicalTapes (i : Index) : List (Tape Bool) :=
  [i.finalTape, i.consumedStageTape, i.metadataHitTape]

theorem Index.postDispatchLogicalTapes_eq_endpoint (i : Index) :
    i.postDispatchLogicalTapes =
      (loopDispatcherEndpointConfig
        i.description i.sourceLayout).tapes := by
  rfl

/-- Canonical guarded physical endpoint of the lowered dispatcher. -/
def Index.postDispatchSource (i : Index) : Tape Bool :=
  encodedGuardedStructuredTapes i.postDispatchLogicalTapes

/-! The definitions below deliberately alias the committed dispatcher
closeout API.  There is no second witness encoding in this module. -/

/-- Logical tape 2 after the dispatcher appends the branch witness. -/
def Index.doneWitnessTape (i : Index) : Tape Bool :=
  loopDispatcherDoneWitnessTape i.description i.sourceLayout

/-- Exact logical source of the uniform guarded serializer. -/
def Index.logicalTapes (i : Index) : List (Tape Bool) :=
  loopDispatcherDoneWitnessTapes i.description i.sourceLayout

theorem Index.logicalTapes_eq_doneWitness (i : Index) :
    i.logicalTapes =
      loopDispatcherDoneWitnessTapes i.description i.sourceLayout := by
  rfl

/-- Canonical guarded physical source after branch-witness materialization. -/
def Index.source (i : Index) : Tape Bool :=
  encodedGuardedStructuredTapes i.logicalTapes

/-- Scratch width recovered from the unary marker block. -/
def Index.scratchWidth (i : Index) : Nat :=
  (RunConfigEmitterTheory.scratchWidthMarkers i.sourceLayout).length

/-- Exact four semantic fields assembled from the physical currencies. -/
def Index.fields (i : Index) : ExactCloseout.Fields :=
  EgressSemantics.fieldsFromParts
    (FieldDecomposition.metadata i.sourceLayout)
    i.finalState i.finalTape i.finalHit

/-- Exact right-shifted target expected by the final one-cell parking phase. -/
def Index.target (i : Index) : Tape Bool :=
  i.fields.rightScratchTape i.scratchWidth

theorem Index.fields_eq_semantic (i : Index) :
    i.fields = ExactCloseout.semanticFields i.description i.sourceLayout := by
  rw [Index.fields, i.finalState_eq]
  exact EgressSemantics.fieldsFromParts_semantic
    i.description i.sourceLayout

theorem Index.scratchWidth_eq_semantic (i : Index) :
    i.scratchWidth =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
        i.sourceLayout := by
  exact EgressSemantics.scratchWidth_of_markers i.sourceLayout

theorem Index.target_eq_semantic (i : Index) :
    i.target =
      (ExactCloseout.semanticFields i.description i.sourceLayout).rightScratchTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
          i.sourceLayout) := by
  rw [Index.target, i.fields_eq_semantic, i.scratchWidth_eq_semantic]

theorem Index.postDispatchSource_cells (i : Index) :
    Tape.cells i.postDispatchSource =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape i.finalTape))
          (List.append tapeSeparatorCells
            (List.append
              (logicalTapeCode (guardLogicalTape i.consumedStageTape))
              (List.append tapeSeparatorCells
                (List.append
                  (logicalTapeCode (guardLogicalTape i.metadataHitTape))
                  tapeSeparatorCells))))) := by
  exact encodedGuardedStructured3Tapes_cells
    i.finalTape i.consumedStageTape i.metadataHitTape

theorem Index.source_cells (i : Index) :
    Tape.cells i.source =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape i.finalTape))
          (List.append tapeSeparatorCells
            (List.append
              (logicalTapeCode (guardLogicalTape i.consumedStageTape))
              (List.append tapeSeparatorCells
                (List.append
                  (logicalTapeCode (guardLogicalTape i.doneWitnessTape))
                  tapeSeparatorCells))))) := by
  exact encodedGuardedStructured3Tapes_cells
    i.finalTape i.consumedStageTape i.doneWitnessTape

/-!
## Executable exact guarded-tape decoder
-/

namespace ExactLogicalTapeDecoder

/-- List-typed view of one logical cell code.  The lowering definition uses
the definitionally equal book-facing {name}`Word` type. -/
def cellBits : Option Bool -> List Bool
  | none => [false, false]
  | some false => [false, true]
  | some true => [true, false]

def cellsBits : List (Option Bool) -> List Bool
  | [] => []
  | cell :: rest => List.append (cellBits cell) (cellsBits rest)

def tapeBits (T : Tape Bool) : List Bool :=
  List.append (cellsBits T.left.reverse)
    (true :: true ::
      List.append (cellBits T.head) (cellsBits T.right))

theorem cellBits_eq_logicalCellBits (cell : Option Bool) :
    cellBits cell = logicalCellBits cell := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem cellsBits_eq_logicalCellListBits
    (cells : List (Option Bool)) :
    cellsBits cells = logicalCellListBits cells := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      rw [cellsBits, logicalCellListBits,
        cellBits_eq_logicalCellBits, ih]

theorem tapeBits_eq_logicalTapeBits (T : Tape Bool) :
    tapeBits T = logicalTapeBits T := by
  rw [tapeBits, logicalTapeBits,
    cellsBits_eq_logicalCellListBits,
    cellsBits_eq_logicalCellListBits,
    cellBits_eq_logicalCellBits]
  rfl

/-- Decode a complete sequence of two-bit logical-cell codes.  The reserved
pair {lit}`true,true` is rejected because it is the head marker. -/
def decodeCells : List Bool -> Option (List (Option Bool))
  | [] => some []
  | false :: false :: rest =>
      Option.map (fun cells => none :: cells) (decodeCells rest)
  | false :: true :: rest =>
      Option.map (fun cells => some false :: cells) (decodeCells rest)
  | true :: false :: rest =>
      Option.map (fun cells => some true :: cells) (decodeCells rest)
  | _ => none

/-- Decode logical cells up to the first pair-aligned head marker. -/
def decodeUntilHead :
    List Bool -> Option (List (Option Bool) × List Bool)
  | true :: true :: rest => some ([], rest)
  | false :: false :: rest =>
      Option.map (fun result => (none :: result.1, result.2))
        (decodeUntilHead rest)
  | false :: true :: rest =>
      Option.map (fun result => (some false :: result.1, result.2))
        (decodeUntilHead rest)
  | true :: false :: rest =>
      Option.map (fun result => (some true :: result.1, result.2))
        (decodeUntilHead rest)
  | _ => none

/-- Decode one exact logical tape, retaining its stored left list, head cell,
and stored right list. -/
def decode (bits : List Bool) : Option (Tape Bool) :=
  match decodeUntilHead bits with
  | some (leftRev, false :: false :: rest) =>
      Option.map
        (fun right =>
          { left := leftRev.reverse, head := none, right := right })
        (decodeCells rest)
  | some (leftRev, false :: true :: rest) =>
      Option.map
        (fun right =>
          { left := leftRev.reverse, head := some false, right := right })
        (decodeCells rest)
  | some (leftRev, true :: false :: rest) =>
      Option.map
        (fun right =>
          { left := leftRev.reverse, head := some true, right := right })
        (decodeCells rest)
  | _ => none

theorem decodeCells_cellsBits
    (cells : List (Option Bool)) :
    decodeCells (cellsBits cells) = some cells := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          simp [cellsBits, cellBits, decodeCells, ih]
      | some bit =>
          cases bit <;>
            simp [cellsBits, cellBits, decodeCells, ih]

theorem decodeUntilHead_cellsBits_append
    (cells : List (Option Bool)) (suffix : List Bool) :
    decodeUntilHead
        (List.append (cellsBits cells)
          (true :: true :: suffix)) =
      some (cells, suffix) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      change
        decodeUntilHead
            (cellsBits rest ++ true :: true :: suffix) =
          some (rest, suffix) at ih
      cases cell with
      | none =>
          simp [cellsBits, cellBits, decodeUntilHead, ih]
      | some bit =>
          cases bit <;>
            simp [cellsBits, cellBits, decodeUntilHead, ih]

theorem decode_logicalTapeBits (T : Tape Bool) :
    decode (logicalTapeBits T) = some T := by
  rw [← tapeBits_eq_logicalTapeBits]
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          rw [show tapeBits { left := left, head := none, right := right } =
            List.append (cellsBits left.reverse)
              (true :: true :: false :: false :: cellsBits right) by rfl]
          unfold decode
          rw [decodeUntilHead_cellsBits_append]
          simp only
          rw [decodeCells_cellsBits]
          simp
      | some bit =>
          cases bit with
          | false =>
              rw [show
                tapeBits
                    { left := left, head := some false, right := right } =
                  List.append (cellsBits left.reverse)
                    (true :: true :: false :: true :: cellsBits right) by
                rfl]
              unfold decode
              rw [decodeUntilHead_cellsBits_append]
              simp only
              rw [decodeCells_cellsBits]
              simp
          | true =>
              rw [show
                tapeBits
                    { left := left, head := some true, right := right } =
                  List.append (cellsBits left.reverse)
                    (true :: true :: true :: false :: cellsBits right) by
                rfl]
              unfold decode
              rw [decodeUntilHead_cellsBits_append]
              simp only
              rw [decodeCells_cellsBits]
              simp

/-- Remove exactly one explicit far-edge blank. -/
def stripTrailingGuard :
    List (Option Bool) -> Option (List (Option Bool))
  | [] => none
  | [none] => some []
  | [some _] => none
  | cell :: next :: rest =>
      Option.map (fun cells => cell :: cells)
        (stripTrailingGuard (next :: rest))

theorem stripTrailingGuard_append_none
    (cells : List (Option Bool)) :
    stripTrailingGuard (List.append cells [none]) = some cells := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases rest with
      | nil =>
          cases cell <;> rfl
      | cons next tail =>
          rw [show
            List.append (cell :: next :: tail) [none] =
              cell :: next :: List.append tail [none] by rfl]
          rw [stripTrailingGuard]
          change
            stripTrailingGuard (next :: List.append tail [none]) =
              some (next :: tail) at ih
          rw [ih]
          rfl

/-- Remove the two representation guards after decoding the exact logical
tape payload. -/
def unguard (T : Tape Bool) : Option (Tape Bool) :=
  match stripTrailingGuard T.left, stripTrailingGuard T.right with
  | some left, some right =>
      some { left := left, head := T.head, right := right }
  | _, _ => none

theorem unguard_guardLogicalTape (T : Tape Bool) :
    unguard (guardLogicalTape T) = some T := by
  cases T with
  | mk left head right =>
      unfold guardLogicalTape unguard
      rw [stripTrailingGuard_append_none,
        stripTrailingGuard_append_none]

/-- Decode a segment payload and remove the exact lowering guards. -/
def decodeGuarded (bits : List Bool) : Option (Tape Bool) :=
  match decode bits with
  | some guarded => unguard guarded
  | none => none

theorem decodeGuarded_logicalTapeBits_guard (T : Tape Bool) :
    decodeGuarded (logicalTapeBits (guardLogicalTape T)) = some T := by
  unfold decodeGuarded
  rw [decode_logicalTapeBits]
  exact unguard_guardLogicalTape T

/-- The exact guarded decoder is essential: no replacement that sees only an
unguarded logical tape can uniformly serialize stored window blanks. -/
theorem no_unguarded_exact_serializer :
    ¬ exists serializer : MachineDescription,
      RunConfigEmitterTheory.ExactLogicalTapeSerializerSpec serializer :=
  RunConfigEmitterTheory.not_exists_exactLogicalTapeSerializer

end ExactLogicalTapeDecoder

/-!
## Executable metadata, scratch-width, and branch-witness decoder
-/

namespace MetadataWitnessDecoder

/-- Read Boolean cells up to and including the first blank delimiter. -/
def takeBitsUntilBlank :
    List (Option Bool) -> Option (Word Bool × List (Option Bool))
  | [] => none
  | none :: rest => some ([], rest)
  | some bit :: rest =>
      Option.map (fun result => (bit :: result.1, result.2))
        (takeBitsUntilBlank rest)

theorem takeBitsUntilBlank_map_append_none
    (bits : Word Bool) (rest : List (Option Bool)) :
    takeBitsUntilBlank
        (List.append (bits.map some) (none :: rest)) =
      some (bits, rest) := by
  induction bits with
  | nil =>
      rfl
  | cons bit bits ih =>
      change
        takeBitsUntilBlank
            (bits.map some ++ none :: rest) =
          some (bits, rest) at ih
      cases bit with
      | false =>
          change
            Option.map
                (fun result => (false :: result.1, result.2))
                (takeBitsUntilBlank
                  (bits.map some ++ none :: rest)) =
              some (false :: bits, rest)
          rw [ih]
          rfl
      | true =>
          change
            Option.map
                (fun result => (true :: result.1, result.2))
                (takeBitsUntilBlank
                  (bits.map some ++ none :: rest)) =
              some (true :: bits, rest)
          rw [ih]
          rfl

/-- Validate and count a raw unary block of {lit}`some true` markers. -/
def countTrueMarkers : List (Option Bool) -> Option Nat
  | [] => some 0
  | some true :: rest => Option.map Nat.succ (countTrueMarkers rest)
  | _ => none

theorem countTrueMarkers_replicate (count : Nat) :
    countTrueMarkers
        (List.replicate count (some true : Option Bool)) =
      some count := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      simp [List.replicate_succ, countTrueMarkers, ih]

/-- Decode one complete compact metadata bit string. -/
def decodeMetadataBits
    (bits : Word Bool) : Option FieldDecomposition.Metadata :=
  match decodeCodeWordAsInput bits with
  | some tokens =>
      match FieldDecomposition.Metadata.decode tokens with
      | some (metadata, []) => some metadata
      | _ => none
  | none => none

theorem decodeMetadataBits_metadataBits (L : SimulatorLayout) :
    decodeMetadataBits (FieldDecomposition.metadataBits L) =
      some (FieldDecomposition.metadata L) := by
  unfold decodeMetadataBits FieldDecomposition.metadataBits
  rw [decodeCodeWordAsInput_encodeCodeWordAsInput]
  simp only
  rw [FieldDecomposition.metadata_decode]

/-- Decode the committed self-delimiting dispatcher branch witness. -/
def decodeDoneWitnessBits
    (bits : Word Bool) : Option LoopDispatcherDoneWitness :=
  match decodeCodeWordAsInput bits with
  | some tokens =>
      match decodeBool tokens with
      | some (true, rest) =>
          match decodeNat rest with
          | some (state, []) =>
              some (.known state)
          | _ => none
      | some (false, []) => some .other
      | _ => none
  | none => none

theorem decodeDoneWitnessBits_bits
    (witness : LoopDispatcherDoneWitness) :
    decodeDoneWitnessBits witness.bits = some witness := by
  cases witness with
  | known state =>
      change
        decodeDoneWitnessBits
            (encodeCodeWordAsInput
              (encodeBoolAppend true
                (encodeNatAppend state
                  ([] : Word MachineCodeSymbol)))) =
          some (.known state)
      unfold decodeDoneWitnessBits
      rw [decodeCodeWordAsInput_encodeCodeWordAsInput]
      simp only
      rw [decodeBool_encodeBoolAppend]
      simp only
      rw [decodeNat_encodeNatAppend]
  | other =>
      change
        decodeDoneWitnessBits
            (encodeCodeWordAsInput
              (encodeBoolAppend false
                ([] : Word MachineCodeSymbol))) =
          some .other
      unfold decodeDoneWitnessBits
      rw [decodeCodeWordAsInput_encodeCodeWordAsInput]
      simp only
      rw [decodeBool_encodeBoolAppend]

/-- Exact semantic contents recovered from logical tape 2. -/
structure Recovered where
  metadata : FieldDecomposition.Metadata
  scratchWidth : Nat
  hit : Bool
  witness : LoopDispatcherDoneWitness

/-- Decode compact metadata and its following unary scratch-width block. -/
def decodePrefix
    (cells : List (Option Bool)) :
    Option (FieldDecomposition.Metadata × Nat) :=
  match takeBitsUntilBlank cells with
  | some (metadataBits, markerCells) =>
      match decodeMetadataBits metadataBits,
          countTrueMarkers markerCells with
      | some metadata, some scratchWidth =>
          some (metadata, scratchWidth)
      | _, _ => none
  | none => none

/-- Decode the right-of-hit separator and committed branch witness. -/
def decodeWitnessRight
    (cells : List (Option Bool)) : Option LoopDispatcherDoneWitness :=
  match cells with
  | none :: witnessCells =>
      match takeBitsUntilBlank witnessCells with
      | some (witnessBits, []) =>
          decodeDoneWitnessBits witnessBits
      | _ => none
  | _ => none

/-- Parse the exact metadata/hit/witness tape emitted by the dispatcher
closeout. -/
def decode (T : Tape Bool) : Option Recovered :=
  match decodePrefix T.left.reverse, T.head,
      decodeWitnessRight T.right with
  | some (metadata, scratchWidth), some hit, some witness =>
      some
        { metadata := metadata
          scratchWidth := scratchWidth
          hit := hit
          witness := witness }
  | _, _, _ => none

def expected (D : MachineDescription) (L : SimulatorLayout) : Recovered where
  metadata := FieldDecomposition.metadata L
  scratchWidth :=
    (RunConfigEmitterTheory.scratchWidthMarkers L).length
  hit := (SimulatorLayout.run D L.stage L).hit
  witness := loopDispatcherDoneWitness D L

theorem decodePrefix_metadataPrefixCells (L : SimulatorLayout) :
    decodePrefix (FieldDecomposition.metadataPrefixCells L) =
      some
        (FieldDecomposition.metadata L,
          (RunConfigEmitterTheory.scratchWidthMarkers L).length) := by
  unfold decodePrefix
  rw [show FieldDecomposition.metadataPrefixCells L =
      List.append
        ((FieldDecomposition.metadataBits L).map some)
        (none :: RunConfigEmitterTheory.scratchWidthMarkers L) by rfl]
  rw [takeBitsUntilBlank_map_append_none]
  simp only
  rw [decodeMetadataBits_metadataBits]
  have hcount :
      countTrueMarkers
          (RunConfigEmitterTheory.scratchWidthMarkers L) =
        some (RunConfigEmitterTheory.scratchWidthMarkers L).length := by
    simpa [RunConfigEmitterTheory.scratchWidthMarkers] using
      countTrueMarkers_replicate
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
          L)
  rw [hcount]

theorem decodeWitnessRight_of_take
    {cells : List (Option Bool)} {bits : Word Bool}
    {witness : LoopDispatcherDoneWitness}
    (htake : takeBitsUntilBlank cells = some (bits, []))
    (hdecode : decodeDoneWitnessBits bits = some witness) :
    decodeWitnessRight (none :: cells) = some witness := by
  unfold decodeWitnessRight
  change
    (match takeBitsUntilBlank cells with
    | some (witnessBits, []) =>
        decodeDoneWitnessBits witnessBits
    | _ => none) = some witness
  rw [htake]
  simp only
  exact hdecode

theorem decodeWitnessRight_bits
    (witness : LoopDispatcherDoneWitness) :
    decodeWitnessRight
        (none :: List.append (witness.bits.map some) [none]) =
      some witness := by
  have htake :
      takeBitsUntilBlank
          (List.append (witness.bits.map some) [none]) =
        some (witness.bits, []) := by
    exact takeBitsUntilBlank_map_append_none witness.bits []
  exact decodeWitnessRight_of_take htake
    (decodeDoneWitnessBits_bits witness)

theorem decode_doneWitnessTape
    (D : MachineDescription) (L : SimulatorLayout) :
    decode (loopDispatcherDoneWitnessTape D L) =
      some (expected D L) := by
  unfold decode loopDispatcherDoneWitnessTape expected
  simp only [tapeAtCells]
  rw [List.reverse_reverse]
  rw [decodePrefix_metadataPrefixCells]
  rw [decodeWitnessRight_bits]

/-- Final state represented by a parsed branch witness. -/
def Recovered.finalState (r : Recovered) : Nat :=
  match r.witness with
  | .known state => state
  | .other => r.metadata.state

theorem expected_finalState
    (D : MachineDescription) (L : SimulatorLayout) :
    (expected D L).finalState =
      (SimulatorLayout.run D L.stage L).config.state := by
  cases hclass : classifyState D L.config.state with
  | known state hstate =>
      simp [expected, Recovered.finalState,
        loopDispatcherDoneWitness, hclass]
  | other =>
      simp [expected, Recovered.finalState,
        loopDispatcherDoneWitness, hclass]
      exact
        (EgressSemantics.finalState_eq_metadataState_of_other
          D L hclass).symm

end MetadataWitnessDecoder

/-!
## Exact parse-and-assemble semantics
-/

namespace SemanticAssembly

/-- Exact list-typed tape-0 segment payload present inside the guarded physical
source. -/
def tape0Payload (i : Index) : List Bool :=
  ExactLogicalTapeDecoder.tapeBits (guardLogicalTape i.finalTape)

theorem tape0Payload_eq_logicalTapeBits (i : Index) :
    tape0Payload i = logicalTapeBits (guardLogicalTape i.finalTape) := by
  exact ExactLogicalTapeDecoder.tapeBits_eq_logicalTapeBits _

theorem decodeGuarded_tape0Payload (i : Index) :
    ExactLogicalTapeDecoder.decodeGuarded (tape0Payload i) =
      some i.finalTape := by
  rw [tape0Payload_eq_logicalTapeBits]
  exact
    ExactLogicalTapeDecoder.decodeGuarded_logicalTapeBits_guard
      i.finalTape

/-- Recover the exact four closeout fields and independent scratch width from
the two meaningful guarded segments. -/
def decodeFields
    (tape0Payload : List Bool) (tape2 : Tape Bool) :
    Option (ExactCloseout.Fields × Nat) :=
  match ExactLogicalTapeDecoder.decodeGuarded tape0Payload,
      MetadataWitnessDecoder.decode tape2 with
  | some tape, some recovered =>
      some
        (EgressSemantics.fieldsFromParts
          recovered.metadata recovered.finalState tape recovered.hit,
          recovered.scratchWidth)
  | _, _ => none

/-- Assemble the exact right-shifted scratch target after parsing. -/
def assembleTarget
    (tape0Payload : List Bool) (tape2 : Tape Bool) :
    Option (Tape Bool) :=
  match decodeFields tape0Payload tape2 with
  | some (fields, scratchWidth) =>
      some (fields.rightScratchTape scratchWidth)
  | none => none

theorem decodeFields_index (i : Index) :
    decodeFields (tape0Payload i) i.doneWitnessTape =
      some (i.fields, i.scratchWidth) := by
  unfold decodeFields Index.doneWitnessTape
  rw [decodeGuarded_tape0Payload]
  rw [MetadataWitnessDecoder.decode_doneWitnessTape]
  simp only
  rw [MetadataWitnessDecoder.expected_finalState]
  rfl

/-- All semantic data needed by #18 is now recovered and assembled exactly;
only finite-machine realization of this executable transform remains. -/
theorem assembleTarget_index (i : Index) :
    assembleTarget (tape0Payload i) i.doneWitnessTape = some i.target := by
  unfold assembleTarget
  rw [decodeFields_index]
  rfl

/-- The committed guarded source contains enough exact information to satisfy
the determinism guardrail: equivalent canonical sources demand the same exact
target, even when their semantic indices use different descriptions. -/
theorem target_eq_of_source_equiv
    {i j : Index} (hsource : Tape.Equiv i.source j.source) :
    i.target = j.target := by
  change
    Tape.Equiv
        (encodedGuardedStructuredTapes
          [i.finalTape, i.consumedStageTape, i.doneWitnessTape])
        (encodedGuardedStructuredTapes
          [j.finalTape, j.consumedStageTape, j.doneWitnessTape]) at hsource
  rcases encodedGuardedStructuredTapes_three_equiv_inj hsource with
    ⟨htape, _hcounter, hwitness⟩
  have hpayload : tape0Payload i = tape0Payload j := by
    rw [tape0Payload, tape0Payload, htape]
  have hdecoded := decodeFields_index i
  rw [hpayload, hwitness, decodeFields_index j] at hdecoded
  have hpair : (j.fields, j.scratchWidth) =
      (i.fields, i.scratchWidth) :=
    Option.some.inj hdecoded
  have hfields : j.fields = i.fields := congrArg Prod.fst hpair
  have hwidth : j.scratchWidth = i.scratchWidth :=
    congrArg Prod.snd hpair
  unfold Index.target
  rw [hfields, hwidth]

end SemanticAssembly

/-!
## Honest equivalence-output contract
-/

/-- The former all-equivalent-input/exact-tape contract is impossible even
for this target-functional source family, because an equivalent source can
carry arbitrarily much invisible far-edge padding. -/
theorem exactOutputConstruction_impossible (i : Index) :
    ¬ PipelineContracts.EquivInputExactOutputConstruction
        Index.source Index.target :=
  PipelineContracts.equivInputExactOutputConstruction_impossible
    i Index.source Index.target

/-- The final normalizer accepts every far-edge-padded representative of the
guarded source and produces a tape equivalent to the exact right-scratch
target.  Equivalence retains the exact normalized output and head split while
allowing the represented blank window to remain large enough for monotonicity. -/
def Spec (normalizer : MachineDescription) : Prop :=
  PipelineContracts.EquivInputEquivOutputSpec
    Index.source Index.target normalizer

def Construction : Prop :=
  PipelineContracts.EquivInputEquivOutputConstruction
    Index.source Index.target

end GuardedEgress
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
