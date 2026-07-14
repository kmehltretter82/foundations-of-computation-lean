import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessBridge
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessMarker
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.SentinelGapCompactor
import FoC.Computability.Compiler.Structured.Lowering.DispatcherAssembly.Runs
import FoC.Computability.Compiler.Structured.Lowering.FiniteMachineTactics

set_option doc.verso true

/-!
# Metadata/witness staging for guarded #18 egress

This module realizes the finite handoff from the located guarded logical-tape
payload to the source layout consumed by the metadata-token copier.  The
physical source retains both the original raw state and the dispatcher witness;
the staging route keeps the raw state only on the {lit}`other` branch and
substitutes the witnessed final state on the {lit}`known` branch.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataWitnessStage

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CanonicalLayouts.DovetailLayoutScanner
open CanonicalLayouts.SimulatorLayoutScanner
open MetadataWitnessBridge MetadataWitnessBridgeLocate MetadataTokenCopy

/-!
## Exact physical token identities
-/

/-- Token list physically present in the compact pre-witness metadata. -/
def rawMetadataTokens (i : Index) : List MetadataTokenCopy.TokenKind :=
  List.append (MetadataWitnessBridge.boolWordTokens i.sourceLayout.input)
    (List.append (MetadataWitnessBridge.natTokens i.sourceLayout.stage)
      (MetadataWitnessBridge.natTokens i.sourceLayout.config.state))

theorem boolWord_append_nil (bits : Word Bool) :
    List.append bits [] = bits := by
  change List Bool at bits
  exact List.append_nil bits

theorem tokenBits_rawMetadataTokens (i : Index) :
    MetadataTokenCopy.tokenBits (rawMetadataTokens i) =
      FieldDecomposition.metadataBits i.sourceLayout := by
  unfold rawMetadataTokens FieldDecomposition.metadataBits
    FieldDecomposition.metadata FieldDecomposition.Metadata.encode
    FieldDecomposition.Metadata.encodeAppend
  rw [MetadataWitnessBridge.tokenBits_append,
    MetadataWitnessBridge.tokenBits_append]
  rw [MetadataWitnessBridge.tokenBits_boolWordTokens,
    MetadataWitnessBridge.tokenBits_natTokens,
    MetadataWitnessBridge.tokenBits_natTokens]
  have hstate :
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          i.sourceLayout.config.state =
        encodeCodeWordAsInput
          (encodeNatAppend i.sourceLayout.config.state []) := by
    have h :=
      EncRewriters.CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend
        i.sourceLayout.config.state []
    unfold Languages.Word at h ⊢
    exact (List.append_nil _).symm.trans h.symm
  have hstage :
      List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            i.sourceLayout.stage)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            i.sourceLayout.config.state) =
        encodeCodeWordAsInput
          (encodeNatAppend i.sourceLayout.stage
            (encodeNatAppend i.sourceLayout.config.state [])) := by
    rw [hstate]
    exact
      (EncRewriters.CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend
        i.sourceLayout.stage
        (encodeNatAppend i.sourceLayout.config.state [])).symm
  calc
    List.append (boolWordFieldBits i.sourceLayout.input [])
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            i.sourceLayout.stage)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            i.sourceLayout.config.state)) =
      boolWordFieldBits i.sourceLayout.input
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            i.sourceLayout.stage)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            i.sourceLayout.config.state)) := by
        simp [boolWordFieldBits, cellListFieldBits, List.append_assoc]
    _ = encodeCodeWordAsInput
        (encodeBoolWordAppend i.sourceLayout.input
          (encodeNatAppend i.sourceLayout.stage
            (encodeNatAppend i.sourceLayout.config.state []))) := by
      rw [boolWordFieldBits, cellListFieldBits, hstage]
      rw [List.length_map]
      exact
        (boolWordBits_eq_encodeBoolWordAppend i.sourceLayout.input
          (encodeNatAppend i.sourceLayout.stage
            (encodeNatAppend i.sourceLayout.config.state []))).symm

/-- Logical-cell encoding distributes over an appended Boolean word. -/
theorem logicalCellListBits_map_some_append
    (left right : Word Bool) :
    logicalCellListBits
        ((List.append left right).map some) =
      List.append (logicalCellListBits (left.map some))
        (logicalCellListBits (right.map some)) := by
  induction left with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases bit <;>
        simp [logicalCellListBits, List.append_assoc]

theorem logicalCellListCode_map_some_append
    (bits : Word Bool) (tail : List (Option Bool)) :
    logicalCellListCode (List.append (bits.map some) tail) =
      List.append (logicalCellListCode (bits.map some))
        (logicalCellListCode tail) := by
  change List Bool at bits
  exact logicalCellListCode_append (bits.map some) tail

theorem encodedTokenCells_eq_logicalCellListBits
    (kind : MetadataTokenCopy.TokenKind) :
    MetadataTokenCopy.encodedTokenCells kind =
      (logicalCellListBits (kind.bits.map some)).map some := by
  rfl

/-- Encoding each four-bit token as four logical present cells is exactly the
eight-cell physical token currency used by the copier. -/
theorem encodedTokens_eq_logicalCellListBits
    (tokens : List MetadataTokenCopy.TokenKind) :
    MetadataTokenCopy.encodedTokens tokens =
      (logicalCellListBits
        ((MetadataTokenCopy.tokenBits tokens).map some)).map some := by
  induction tokens with
  | nil =>
      rfl
  | cons kind rest ih =>
      rw [MetadataTokenCopy.encodedTokens_cons,
        MetadataTokenCopy.tokenBits_cons]
      rw [logicalCellListBits_map_some_append,
        CanonicalLayouts.DovetailLayoutScanner.map_some_append,
        encodedTokenCells_eq_logicalCellListBits, ih]
      rfl

theorem metadataCells_eq_encodedTokens (i : Index) :
    (logicalCellListBits
      ((FieldDecomposition.metadataBits i.sourceLayout).map some)).map some =
      MetadataTokenCopy.encodedTokens (rawMetadataTokens i) := by
  rw [← tokenBits_rawMetadataTokens]
  exact (encodedTokens_eq_logicalCellListBits _).symm

/-!
## Located source shape
-/

/-- Complete left stack after the locator has erased logical tape 1. -/
def locatedLeft (i : Index) : List (Option Bool) :=
  List.append
    (List.replicate
      ((logicalTapeBits (guardLogicalTape i.consumedStageTape)).length +
        MetadataWitnessBridgeLocate.serializerGap i + 1)
      (none : Option Bool))
    (MetadataWitnessBridgeLocate.serializerLeft i)

/-- Encoded scratch-width marker block retained between metadata and hit. -/
def scratchCells (i : Index) : List (Option Bool) :=
  logicalCellListCode
    (RunConfigEmitterTheory.scratchWidthMarkers i.sourceLayout)

/-- Encoded branch-witness payload retained to the right of the hit. -/
def witnessCells (i : Index) : List (Option Bool) :=
  logicalCellListCode
    ((loopDispatcherDoneWitness i.description i.sourceLayout).bits.map some)

/-- Exact present-cell payload of the guarded witness tape. -/
def locatedPayload (i : Index) : List (Option Bool) :=
  [some false, some false] ++
    MetadataTokenCopy.encodedTokens (rawMetadataTokens i) ++
    [some false, some false] ++
    scratchCells i ++
    [some true, some true] ++
    logicalCellCode (some i.finalHit) ++
    [some false, some false] ++
    witnessCells i ++
    [some false, some false, some false, some false]

theorem guardedDone_left_reverse (i : Index) :
    (guardLogicalTape i.doneWitnessTape).left.reverse =
      none :: FieldDecomposition.metadataPrefixCells i.sourceLayout := by
  unfold guardLogicalTape Index.doneWitnessTape
  rw [loopDispatcherDoneWitnessTape_left]
  simp [List.reverse_append]

theorem guardedDone_head (i : Index) :
    (guardLogicalTape i.doneWitnessTape).head = some i.finalHit := by
  rfl

theorem guardedDone_right (i : Index) :
    (guardLogicalTape i.doneWitnessTape).right =
      none ::
        List.append
          ((loopDispatcherDoneWitness i.description i.sourceLayout).bits.map
            some)
          [none, none] := by
  unfold guardLogicalTape Index.doneWitnessTape
  unfold loopDispatcherDoneWitnessTape tapeAtCells
  simp [List.append_assoc]

theorem logicalTapeCode_guard_doneWitness_eq (i : Index) :
    logicalTapeCode (guardLogicalTape i.doneWitnessTape) =
      locatedPayload i := by
  unfold locatedPayload scratchCells witnessCells
  unfold logicalTapeCode
  rw [guardedDone_left_reverse, guardedDone_head, guardedDone_right]
  rw [FieldDecomposition.metadataPrefixCells]
  simp only [logicalCellListCode_cons, logicalCellCode_none]
  rw [logicalCellListCode_map_some_append,
    logicalCellListCode_map_some_append]
  rw [logicalCellListCode_eq_map_some]
  rw [metadataCells_eq_encodedTokens]
  simp [headMarkerCells, logicalCellListBits, logicalCellBits,
    List.append_assoc]

theorem locatedTape_eq_payload (i : Index) :
    MetadataWitnessBridgeLocate.locatedTape i =
      tapeAtCells (locatedLeft i)
        (List.append (locatedPayload i) [none]) := by
  unfold MetadataWitnessBridgeLocate.locatedTape
    MetadataWitnessBridgeLocate.targetTape
    MetadataWitnessBridgeLocate.tape2Suffix locatedLeft
  rw [logicalTapeCode_guard_doneWitness_eq]
  simp [tapeSeparatorCells]

/-!
## Branch-specific token blocks
-/

def prefixMetadataTokens (i : Index) :
    List MetadataTokenCopy.TokenKind :=
  List.append (MetadataWitnessBridge.boolWordTokens i.sourceLayout.input)
    (MetadataWitnessBridge.natTokens i.sourceLayout.stage)

theorem rawMetadataTokens_eq_prefix_state (i : Index) :
    rawMetadataTokens i =
      List.append (prefixMetadataTokens i)
        (MetadataWitnessBridge.natTokens i.sourceLayout.config.state) := by
  simp [rawMetadataTokens, prefixMetadataTokens, List.append_assoc]

/-- Raw physical Boolean word underlying the present-cell token encoding. -/
def physicalTokenBits
    (tokens : List MetadataTokenCopy.TokenKind) : Word Bool :=
  logicalCellListBits ((MetadataTokenCopy.tokenBits tokens).map some)

theorem encodedTokens_eq_map_physicalTokenBits
    (tokens : List MetadataTokenCopy.TokenKind) :
    MetadataTokenCopy.encodedTokens tokens =
      (physicalTokenBits tokens).map some := by
  exact encodedTokens_eq_logicalCellListBits tokens

theorem physicalTokenBits_append
    (left right : List MetadataTokenCopy.TokenKind) :
    physicalTokenBits (List.append left right) =
      List.append (physicalTokenBits left) (physicalTokenBits right) := by
  unfold physicalTokenBits
  rw [MetadataWitnessBridge.tokenBits_append]
  exact logicalCellListBits_map_some_append _ _

theorem witnessBits_known (finalState : Nat) :
    (LoopDispatcherDoneWitness.known finalState).bits =
      List.append MetadataTokenCopy.TokenKind.one.bits
        (MetadataTokenCopy.tokenBits
          (MetadataWitnessBridge.natTokens finalState)) := by
  unfold LoopDispatcherDoneWitness.bits LoopDispatcherDoneWitness.code
  rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
  rw [EncRewriters.CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
  rw [MetadataWitnessBridge.tokenBits_natTokens]
  unfold Languages.Word at ⊢
  simp [cellCodeBits, encodeCell, encodeCodeWordAsInput,
    encodeCodeSymbolAsInput, MetadataTokenCopy.TokenKind.bits]

theorem witnessBits_other :
    LoopDispatcherDoneWitness.other.bits =
      MetadataTokenCopy.TokenKind.zero.bits := by
  unfold LoopDispatcherDoneWitness.bits LoopDispatcherDoneWitness.code
  rw [CanonicalLayouts.DovetailLayoutScanner.boolBits_eq_encodeBoolAppend]
  unfold Languages.Word at ⊢
  rfl

theorem witnessCells_known
    (i : Index) (finalState : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState) :
    witnessCells i =
      List.append
        (MetadataTokenCopy.encodedTokenCells .one)
        (MetadataTokenCopy.encodedTokens
          (MetadataWitnessBridge.natTokens finalState)) := by
  unfold witnessCells
  rw [hwitness, witnessBits_known]
  rw [CanonicalLayouts.DovetailLayoutScanner.map_some_append]
  rw [logicalCellListCode_map_some_append]
  rw [logicalCellListCode_eq_map_some,
    logicalCellListCode_eq_map_some]
  rw [← encodedTokenCells_eq_logicalCellListBits]
  rw [← encodedTokens_eq_logicalCellListBits]

theorem witnessCells_other
    (i : Index)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout = .other) :
    witnessCells i = MetadataTokenCopy.encodedTokenCells .zero := by
  unfold witnessCells
  rw [hwitness, witnessBits_other]
  rw [logicalCellListCode_eq_map_some]
  exact (encodedTokenCells_eq_logicalCellListBits _).symm

theorem encodedTokens_append
    (left right : List MetadataTokenCopy.TokenKind) :
    MetadataTokenCopy.encodedTokens (List.append left right) =
      List.append (MetadataTokenCopy.encodedTokens left)
        (MetadataTokenCopy.encodedTokens right) := by
  induction left with
  | nil =>
      rfl
  | cons kind rest ih =>
      simp only [List.append, MetadataTokenCopy.encodedTokens]
      calc
        List.append (MetadataTokenCopy.encodedTokenCells kind)
            (MetadataTokenCopy.encodedTokens (List.append rest right)) =
          List.append (MetadataTokenCopy.encodedTokenCells kind)
            (List.append (MetadataTokenCopy.encodedTokens rest)
              (MetadataTokenCopy.encodedTokens right)) :=
            congrArg
              (fun cells =>
                List.append (MetadataTokenCopy.encodedTokenCells kind) cells)
              ih
        _ = List.append
            (List.append (MetadataTokenCopy.encodedTokenCells kind)
              (MetadataTokenCopy.encodedTokens rest))
            (MetadataTokenCopy.encodedTokens right) :=
          (List.append_assoc _ _ _).symm

theorem natTokens_eq_ticks_done (n : Nat) :
    MetadataWitnessBridge.natTokens n =
      List.append (List.replicate n MetadataTokenCopy.TokenKind.tick)
        [MetadataTokenCopy.TokenKind.done] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [MetadataWitnessBridge.natTokens, ih]
      simp [List.replicate_succ]

theorem hitBits_eq_components (i : Index) :
    MetadataWitnessBridge.hitBits i =
      [false, true, i.finalHit, !i.finalHit] := by
  cases hhit : i.finalHit <;>
    simp [MetadataWitnessBridge.hitBits, MetadataWitnessBridge.hitToken,
      hhit, MetadataTokenCopy.TokenKind.bits]

theorem prefixEncoded_reverse_exists (i : Index) :
    exists tail : List (Option Bool),
      (MetadataTokenCopy.encodedTokens (prefixMetadataTokens i)).reverse =
        some false :: tail := by
  rw [prefixMetadataTokens, encodedTokens_append,
    natTokens_eq_ticks_done, encodedTokens_append]
  simp [List.reverse_append, MetadataTokenCopy.encodedTokenCells,
    MetadataTokenCopy.TokenKind.bits, logicalCellListBits,
    logicalCellBits]

/-!
## Common copier-ready endpoint
-/

/-- Positive blank gap left after reserving the four hit cells. -/
def readyGap (i : Index) : Nat :=
  (logicalTapeBits (guardLogicalTape i.consumedStageTape)).length +
    MetadataWitnessBridgeLocate.serializerGap i

theorem readyGap_pos (i : Index) : 0 < readyGap i := by
  unfold readyGap MetadataWitnessBridgeLocate.serializerGap
  lia

def readyGapTail (i : Index) : Nat := readyGap i - 1

theorem readyGap_eq_tail_add_one (i : Index) :
    readyGap i = readyGapTail i + 1 := by
  unfold readyGapTail
  have h := readyGap_pos i
  lia

/-- Left-of-token material retained by both witness branches. -/
def stagedBase (i : Index) : List (Option Bool) :=
  some false ::
    List.append (List.replicate (readyGap i) (none : Option Bool))
      (List.append ((MetadataWitnessBridge.hitBits i).reverse.map some)
        ((LengthAssembly.exactTapeFieldBits i.finalTape []).reverse.map some))

theorem blankPrefix_eq (gap : Nat) (tail : List (Option Bool)) :
    none ::
        List.append (List.replicate (gap + 1) (none : Option Bool))
          (none :: none :: tail) =
      List.append (List.replicate (gap + 4) none) tail := by
  calc
    none ::
        List.append (List.replicate (gap + 1) (none : Option Bool))
          (none :: none :: tail) =
      none ::
        List.append (List.replicate (gap + 3) none) tail := by
          apply congrArg (List.cons (none : Option Bool))
          rw [show gap + 3 = (gap + 1) + 2 by lia]
          exact (FoC.Computability.list_replicate_add_append
            (none : Option Bool) (gap + 1) 2 tail
            ).symm
    _ = List.append (List.replicate (gap + 4) none) tail := by
      have hprefix :
          none :: List.replicate (gap + 3) (none : Option Bool) =
            List.replicate (gap + 4) none := by
        rw [show gap + 4 = Nat.succ (gap + 3) by lia]
        rfl
      exact congrArg (fun xs => List.append xs tail) hprefix

theorem markerLocatedLeft_eq (i : Index) :
    List.append [some false, none] (locatedLeft i) =
      some false ::
        List.append
          (List.replicate (readyGap i + 4) (none : Option Bool))
          ((LengthAssembly.exactTapeFieldBits i.finalTape []).reverse.map
            some) := by
  have hlocated :
      locatedLeft i =
        List.append
          (List.replicate (readyGap i + 1) (none : Option Bool))
          (none :: none ::
            (LengthAssembly.exactTapeFieldBits
              i.finalTape []).reverse.map some) := by
    unfold locatedLeft MetadataWitnessBridgeLocate.serializerLeft readyGap
    rfl
  rw [hlocated]
  simpa only [List.append] using
    congrArg (List.cons (some false))
      (blankPrefix_eq (readyGap i)
        ((LengthAssembly.exactTapeFieldBits i.finalTape []).reverse.map some))

/-- Common endpoint immediately before installation of the right loop marker. -/
def preMarkerTape (i : Index)
    (tokens : List MetadataTokenCopy.TokenKind) (rightPadding : Nat) :
    Tape Bool :=
  leadingBlankLeftShiftTargetTapeWithPadding
    (stagedBase i) (physicalTokenBits tokens)
    (none :: List.replicate rightPadding (none : Option Bool))

/-- Exact result of the fixed right-marker installer. -/
def markedTape (i : Index)
    (tokens : List MetadataTokenCopy.TokenKind) (rightPadding : Nat) :
    Tape Bool :=
  tapeAtCells
    (none ::
      List.append ((physicalTokenBits tokens).reverse.map some)
        (stagedBase i))
    (some true :: none ::
      List.replicate rightPadding (none : Option Bool))

theorem marker_haltsFromTape
    (i : Index) (tokens : List MetadataTokenCopy.TokenKind)
    (rightPadding : Nat) :
    MetadataWitnessMarker.description.HaltsFromTape
      (preMarkerTape i tokens rightPadding)
      (markedTape i tokens rightPadding) := by
  exact MetadataWitnessMarker.description_haltsFromTape
    (stagedBase i) (physicalTokenBits tokens)
    (List.replicate rightPadding (none : Option Bool))

def stagedReadyLayout (i : Index) (rightPadding : Nat) : ReadyLayout where
  basePadding := 0
  gapTail := readyGapTail i
  rightPadding := rightPadding + 1

theorem dropTrailingNone_append_copierWorkspace
    (cells : List (Option Bool)) (tokenCount : Nat) :
    Tape.dropTrailingNone
        (List.append cells
          (List.append
            (List.replicate (4 * tokenCount) (none : Option Bool))
            [none, none, none, none])) =
      Tape.dropTrailingNone cells := by
  calc
    Tape.dropTrailingNone
        (List.append cells
          (List.append
            (List.replicate (4 * tokenCount) (none : Option Bool))
            [none, none, none, none])) =
      Tape.dropTrailingNone
        (List.append
          (List.append cells
            (List.replicate (4 * tokenCount) none))
          [none, none, none, none]) := by
        exact congrArg Tape.dropTrailingNone
          (List.append_assoc cells
            (List.replicate (4 * tokenCount) none)
            [none, none, none, none]).symm
    _ = Tape.dropTrailingNone
        (List.append cells
          (List.replicate (4 * tokenCount) none)) := by
      change
        Tape.dropTrailingNone
            (List.append
              (List.append cells
                (List.replicate (4 * tokenCount) none))
              (List.replicate 4 none)) =
          Tape.dropTrailingNone
            (List.append cells
              (List.replicate (4 * tokenCount) none))
      exact FoC.Computability.dropTrailingNone_append_replicate_none _ 4
    _ = Tape.dropTrailingNone cells :=
      FoC.Computability.dropTrailingNone_append_replicate_none _ _

theorem markedTape_equiv_readyTape
    (i : Index) (rightPadding : Nat) :
    Tape.Equiv
      (markedTape i (sourceMetadataTokens i) rightPadding)
      (readyTape i (stagedReadyLayout i rightPadding)) := by
  have hleft :
      (readyTape i (stagedReadyLayout i rightPadding)).left =
        List.append
          (markedTape i (sourceMetadataTokens i) rightPadding).left
          (List.append
            (List.replicate
              (4 * (sourceMetadataTokens i).length)
              (none : Option Bool))
            [none, none, none, none]) := by
    unfold markedTape stagedBase readyTape stagedReadyLayout ReadyLayout.gap
      MetadataTokenCopy.sourceTape MetadataTokenCopy.loopTape tapeAtCells
    rw [readyGap_eq_tail_add_one]
    rw [encodedTokens_eq_map_physicalTokenBits]
    simp [List.append_assoc]
  constructor
  · rw [hleft, dropTrailingNone_append_copierWorkspace]
  · constructor
    · rfl
    · unfold markedTape readyTape stagedReadyLayout ReadyLayout.gap
        MetadataTokenCopy.sourceTape MetadataTokenCopy.loopTape tapeAtCells
      rw [FoC.Computability.dropTrailingNone_replicate_none]
      rw [show none :: List.replicate rightPadding (none : Option Bool) =
          List.replicate (rightPadding + 1) none by
        simp [List.replicate_succ]]
      exact FoC.Computability.dropTrailingNone_replicate_none _

/-!
## Branch normalizer

The suffix reader leaves the head on the blank immediately after the guarded
payload and carries the witness branch and final hit in one of four exit
states.  The block below is entered from those exits.  Both branches first
install the four-bit hit field in the blank reservoir left of the raw metadata.
The known branch then deletes the raw-state unary suffix and invokes the
checked sentinel gap compactor to splice the witnessed unary state into place.
-/

namespace Normalizer

def otherSeekRawState : Bool -> Nat
  | false => 1
  | true => 2

def otherScanRawLeftState : Bool -> Nat
  | false => 3
  | true => 4

def knownSeekWitnessState : Bool -> Nat
  | false => 5
  | true => 6

def knownScanWitnessState : Bool -> Nat
  | false => 7
  | true => 8

def knownSeekRawState : Bool -> Nat
  | false => 9
  | true => 10

def knownScanRawLeftState : Bool -> Nat
  | false => 11
  | true => 12

def seekExactState : Bool -> Bool -> Nat
  | false, false => 13
  | false, true => 14
  | true, false => 15
  | true, true => 16

def writeZeroState : Bool -> Bool -> Nat
  | false, false => 17
  | false, true => 18
  | true, false => 19
  | true, true => 20

def writeOneState : Bool -> Bool -> Nat
  | false, false => 21
  | false, true => 22
  | true, false => 23
  | true, true => 24

def writeHitState : Bool -> Bool -> Nat
  | false, false => 25
  | false, true => 26
  | true, false => 27
  | true, true => 28

def writeLastState : Bool -> Bool -> Nat
  | false, false => 29
  | false, true => 30
  | true, false => 31
  | true, true => 32

def scanGapState : Bool -> Nat
  | false => 33
  | true => 34

def scanRawRightState : Bool -> Nat
  | false => 35
  | true => 36

def otherSecondBlankState : Nat := 37
def eraseDoneStates : List Nat := [38, 39, 40, 41, 42, 43, 44, 45]
def inspectPrecedingTokenState : Nat := 46
def seekWitnessRightState : Nat := 47
def scanWitnessRightState : Nat := 48
def crossGuardTwoState : Nat := 49
def crossGuardThreeState : Nat := 50
def crossGuardFourState : Nat := 51

def compactorOffset : Nat := 60

def compactorBranch : MachineDescription :=
  MachineDescription.offsetExitRetargetDescription
    compactorOffset sentinelGapCompactorDescription.halt 0
    sentinelGapCompactorDescription

def preservePresentLeft (source target : Nat) :
    List TransitionDescription :=
  [ transition source (some false) (some false) Direction.left target
  , transition source (some true) (some true) Direction.left target ]

def preservePresentRight (source target : Nat) :
    List TransitionDescription :=
  [ transition source (some false) (some false) Direction.right target
  , transition source (some true) (some true) Direction.right target ]

def erasePresentLeft (source target : Nat) :
    List TransitionDescription :=
  [ transition source (some false) none Direction.left target
  , transition source (some true) none Direction.left target ]

def branchTransitions (hit : Bool) : List TransitionDescription :=
  [ transition (otherSeekRawState hit) none none Direction.left
      (otherSeekRawState hit) ] ++
    preservePresentLeft (otherSeekRawState hit)
      (otherScanRawLeftState hit) ++
    preservePresentLeft (otherScanRawLeftState hit)
      (otherScanRawLeftState hit) ++
    [ transition (otherScanRawLeftState hit) none none Direction.left
        (seekExactState false hit)
    , transition (knownSeekWitnessState hit) none none Direction.left
        (knownSeekWitnessState hit) ] ++
    preservePresentLeft (knownSeekWitnessState hit)
      (knownScanWitnessState hit) ++
    preservePresentLeft (knownScanWitnessState hit)
      (knownScanWitnessState hit) ++
    [ transition (knownScanWitnessState hit) none none Direction.left
        (knownSeekRawState hit)
    , transition (knownSeekRawState hit) none none Direction.left
        (knownSeekRawState hit) ] ++
    preservePresentLeft (knownSeekRawState hit)
      (knownScanRawLeftState hit) ++
    preservePresentLeft (knownScanRawLeftState hit)
      (knownScanRawLeftState hit) ++
    [ transition (knownScanRawLeftState hit) none none Direction.left
        (seekExactState true hit) ] ++
    [false, true].flatMap (fun known =>
      [ transition (seekExactState known hit) none none Direction.left
          (seekExactState known hit) ] ++
        preservePresentRight (seekExactState known hit)
          (writeZeroState known hit) ++
        [ transition (writeZeroState known hit) none (some false)
            Direction.right (writeOneState known hit)
        , transition (writeOneState known hit) none (some true)
            Direction.right (writeHitState known hit)
        , transition (writeHitState known hit) none (some hit)
            Direction.right (writeLastState known hit)
        , transition (writeLastState known hit) none (some (!hit))
            Direction.right (scanGapState known) ])

def commonTransitions : List TransitionDescription :=
  [ transition (scanGapState false) none none Direction.right
      (scanGapState false)
  , transition (scanGapState false) (some false) (some false)
      Direction.right (scanRawRightState false)
  , transition (scanGapState true) none none Direction.right
      (scanGapState true)
  , transition (scanGapState true) (some false) (some false)
      Direction.right (scanRawRightState true) ] ++
    preservePresentRight (scanRawRightState false)
      (scanRawRightState false) ++
    preservePresentRight (scanRawRightState true)
      (scanRawRightState true) ++
    [ transition (scanRawRightState false) none none Direction.right
        otherSecondBlankState
    , transition otherSecondBlankState none none Direction.right 0
    , transition (scanRawRightState true) none none Direction.left
        (eraseDoneStates.getD 0 38) ] ++
    erasePresentLeft (eraseDoneStates.getD 0 38)
      (eraseDoneStates.getD 1 39) ++
    erasePresentLeft (eraseDoneStates.getD 1 39)
      (eraseDoneStates.getD 2 40) ++
    erasePresentLeft (eraseDoneStates.getD 2 40)
      (eraseDoneStates.getD 3 41) ++
    erasePresentLeft (eraseDoneStates.getD 3 41)
      (eraseDoneStates.getD 4 42) ++
    erasePresentLeft (eraseDoneStates.getD 4 42)
      (eraseDoneStates.getD 5 43) ++
    erasePresentLeft (eraseDoneStates.getD 5 43)
      (eraseDoneStates.getD 6 44) ++
    erasePresentLeft (eraseDoneStates.getD 6 44)
      (eraseDoneStates.getD 7 45) ++
    erasePresentLeft (eraseDoneStates.getD 7 45)
      inspectPrecedingTokenState ++
    [ transition inspectPrecedingTokenState (some true) none Direction.left
        (eraseDoneStates.getD 1 39)
    , transition inspectPrecedingTokenState (some false) (some false)
        Direction.right seekWitnessRightState
    , transition seekWitnessRightState none none Direction.right
        seekWitnessRightState ] ++
    preservePresentRight seekWitnessRightState scanWitnessRightState ++
    preservePresentRight scanWitnessRightState scanWitnessRightState ++
    [ transition scanWitnessRightState none none Direction.right
        crossGuardTwoState
    , transition crossGuardTwoState none none Direction.right
        crossGuardThreeState
    , transition crossGuardThreeState none none Direction.right
        crossGuardFourState
    , transition crossGuardFourState none none Direction.right
        compactorOffset ]

def description : MachineDescription where
  stateCount := compactorOffset + sentinelGapCompactorDescription.stateCount
  start := otherSeekRawState false
  halt := 0
  transitions :=
    branchTransitions false ++ branchTransitions true ++
      commonTransitions ++ compactorBranch.transitions

set_option maxRecDepth 100000 in
theorem description_subroutineReady : description.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    description (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem run_left_blanks
    (D : MachineDescription) (state : Nat)
    (hstep : forall (cell : Option Bool)
        (left right : List (Option Bool)),
      D.runConfig 1
          { state := state
            tape := tapeAtCells (cell :: left) (none :: right) } =
        { state := state
          tape := tapeAtCells left (cell :: none :: right) })
    (n : Nat) (boundary : Option Bool)
    (left right : List (Option Bool)) :
    D.runConfig (n + 1)
        { state := state
          tape := tapeAtCells
            (List.append (List.replicate n (none : Option Bool))
              (boundary :: left))
            (none :: right) } =
      { state := state
        tape := tapeAtCells left
          (boundary ::
            List.append (List.replicate (n + 1) none) right) } := by
  induction n generalizing right with
  | zero =>
      simpa using hstep boundary left right
  | succ n ih =>
      rw [show Nat.succ n + 1 = 1 + (n + 1) by lia]
      rw [MachineDescription.runConfig_add]
      rw [List.replicate_succ]
      change D.runConfig (n + 1)
          (D.runConfig 1
            { state := state
              tape := tapeAtCells
                (none ::
                  List.append (List.replicate n none)
                    (boundary :: left))
                (none :: right) }) = _
      rw [hstep]
      rw [ih (none :: right)]
      congr 3
      rw [show 1 + (n + 1) = (n + 1) + 1 by lia]
      exact FoC.Computability.list_replicate_append_self
        (none : Option Bool) (n + 1) right

def leftPresentScanTape
    (scan : Word Bool) (boundary : Option Bool)
    (left right : List (Option Bool)) : Tape Bool :=
  match scan with
  | [] => tapeAtCells left (boundary :: right)
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some) (boundary :: left))
        (some bit :: right)

theorem run_left_present
    (D : MachineDescription) (state : Nat)
    (hstep : forall (bit : Bool) (cell : Option Bool)
        (left right : List (Option Bool)),
      D.runConfig 1
          { state := state
            tape := tapeAtCells (cell :: left) (some bit :: right) } =
        { state := state
          tape := tapeAtCells left (cell :: some bit :: right) })
    (scan : Word Bool) (boundary : Option Bool)
    (left right : List (Option Bool)) :
    D.runConfig scan.length
        { state := state
          tape := leftPresentScanTape scan boundary left right } =
      { state := state
        tape := tapeAtCells left
          (boundary :: List.append (scan.reverse.map some) right) } := by
  induction scan generalizing right with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      cases rest with
      | nil =>
          change D.runConfig 0
              (D.runConfig 1
                { state := state
                  tape := tapeAtCells (boundary :: left)
                    (some bit :: right) }) = _
          rw [hstep]
          rfl
      | cons next tail =>
          change D.runConfig (next :: tail).length
              (D.runConfig 1
                { state := state
                  tape := tapeAtCells
                    (some next ::
                      List.append (tail.map some) (boundary :: left))
                    (some bit :: right) }) = _
          rw [hstep]
          simpa [leftPresentScanTape, List.reverse_cons,
            List.map_append, List.append_assoc] using
            ih (some bit :: right)

theorem run_right_blanks
    (D : MachineDescription) (state : Nat)
    (hstep : forall (left right : List (Option Bool)),
      D.runConfig 1
          { state := state
            tape := tapeAtCells left (none :: right) } =
        { state := state
          tape := tapeAtCells (none :: left) right })
    (n : Nat) (boundary : Option Bool)
    (left right : List (Option Bool)) :
    D.runConfig n
        { state := state
          tape := tapeAtCells left
            (List.append (List.replicate n (none : Option Bool))
              (boundary :: right)) } =
      { state := state
        tape := tapeAtCells
          (List.append (List.replicate n none) left)
          (boundary :: right) } := by
  induction n generalizing left with
  | zero =>
      rfl
  | succ n ih =>
      rw [show n + 1 = 1 + n by lia]
      rw [MachineDescription.runConfig_add]
      rw [show 1 + n = Nat.succ n by lia]
      rw [List.replicate_succ]
      change D.runConfig n
          (D.runConfig 1
            { state := state
              tape := tapeAtCells left
                (none ::
                  List.append (List.replicate n none)
                    (boundary :: right)) }) = _
      rw [hstep]
      rw [ih (none :: left)]
      rw [replicate_none_append_none_cons]
      rfl

theorem run_right_present
    (D : MachineDescription) (state : Nat)
    (hstep : forall (bit : Bool)
        (left right : List (Option Bool)),
      D.runConfig 1
          { state := state
            tape := tapeAtCells left (some bit :: right) } =
        { state := state
          tape := tapeAtCells (some bit :: left) right })
    (scan : Word Bool) (boundary : Option Bool)
    (left right : List (Option Bool)) :
    D.runConfig scan.length
        { state := state
          tape := tapeAtCells left
            (List.append (scan.map some) (boundary :: right)) } =
      { state := state
        tape := tapeAtCells
          (List.append (scan.reverse.map some) left)
          (boundary :: right) } := by
  induction scan generalizing left with
  | nil =>
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [MachineDescription.runConfig_add]
      change D.runConfig rest.length
          (D.runConfig 1
            { state := state
              tape := tapeAtCells left
                (some bit ::
                  List.append (rest.map some) (boundary :: right)) }) = _
      rw [hstep]
      rw [ih (some bit :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem step_otherSeekRaw_none
    (hit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := otherSeekRawState hit
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := otherSeekRawState hit
        tape := tapeAtCells left (cell :: none :: right) } := by
  cases hit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem step_otherScanRawLeft_present
    (hit bit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := otherScanRawLeftState hit
          tape := tapeAtCells (cell :: left) (some bit :: right) } =
      { state := otherScanRawLeftState hit
        tape := tapeAtCells left (cell :: some bit :: right) } := by
  cases hit <;> cases bit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem step_knownSeekWitness_none
    (hit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := knownSeekWitnessState hit
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := knownSeekWitnessState hit
        tape := tapeAtCells left (cell :: none :: right) } := by
  cases hit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem step_knownScanWitness_present
    (hit bit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := knownScanWitnessState hit
          tape := tapeAtCells (cell :: left) (some bit :: right) } =
      { state := knownScanWitnessState hit
        tape := tapeAtCells left (cell :: some bit :: right) } := by
  cases hit <;> cases bit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem step_knownSeekRaw_none
    (hit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := knownSeekRawState hit
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := knownSeekRawState hit
        tape := tapeAtCells left (cell :: none :: right) } := by
  cases hit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem step_knownScanRawLeft_present
    (hit bit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := knownScanRawLeftState hit
          tape := tapeAtCells (cell :: left) (some bit :: right) } =
      { state := knownScanRawLeftState hit
        tape := tapeAtCells left (cell :: some bit :: right) } := by
  cases hit <;> cases bit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem step_seekExact_none
    (known hit : Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := seekExactState known hit
          tape := tapeAtCells (cell :: left) (none :: right) } =
      { state := seekExactState known hit
        tape := tapeAtCells left (cell :: none :: right) } := by
  cases known <;> cases hit <;> cases cell <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState]

theorem step_scanGap_none
    (known : Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := scanGapState known
          tape := tapeAtCells left (none :: right) } =
      { state := scanGapState known
        tape := tapeAtCells (none :: left) right } := by
  cases known <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState,
      otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
      seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
      crossGuardThreeState, crossGuardFourState, compactorOffset]

theorem step_scanRawRight_present
    (known bit : Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := scanRawRightState known
          tape := tapeAtCells left (some bit :: right) } =
      { state := scanRawRightState known
        tape := tapeAtCells (some bit :: left) right } := by
  cases known <;> cases bit <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState,
      otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
      seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
      crossGuardThreeState, crossGuardFourState, compactorOffset]

theorem step_seekWitnessRight_none
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := seekWitnessRightState
          tape := tapeAtCells left (none :: right) } =
      { state := seekWitnessRightState
        tape := tapeAtCells (none :: left) right } := by
  cases right <;> machine_step [description, branchTransitions, commonTransitions,
    preservePresentLeft, preservePresentRight, erasePresentLeft,
    otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
    knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
    seekExactState, writeZeroState, writeOneState, writeHitState,
    writeLastState, scanGapState, scanRawRightState,
    otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
    seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
    crossGuardThreeState, crossGuardFourState, compactorOffset]

theorem step_scanWitnessRight_present
    (bit : Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        { state := scanWitnessRightState
          tape := tapeAtCells left (some bit :: right) } =
      { state := scanWitnessRightState
        tape := tapeAtCells (some bit :: left) right } := by
  cases bit <;> cases right <;>
    machine_step [description, branchTransitions, commonTransitions,
      preservePresentLeft, preservePresentRight, erasePresentLeft,
      otherSeekRawState, otherScanRawLeftState, knownSeekWitnessState,
      knownScanWitnessState, knownSeekRawState, knownScanRawLeftState,
      seekExactState, writeZeroState, writeOneState, writeHitState,
      writeLastState, scanGapState, scanRawRightState,
      otherSecondBlankState, eraseDoneStates, inspectPrecedingTokenState,
      seekWitnessRightState, scanWitnessRightState, crossGuardTwoState,
      crossGuardThreeState, crossGuardFourState, compactorOffset]

end Normalizer

end GuardedEgress.MetadataWitnessStage
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
