import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.FixedSkips
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredPrimitives
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ConcreteRefresh
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.BoolWord

set_option doc.verso true

/-!
# Boolean-word raw-bits decoder

This module packages the generic part of the encoded Boolean-word to raw-bits
materializer.  It decodes the fixed header-prefixed encoded Boolean-word field
and preserves the caller suffix deterministically after the decoded raw bits.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace CommonGround
namespace FiniteTransducers

/--
The encoded Boolean-word field as raw tape bits, without any surrounding code
symbol or caller suffix.
-/
def boolWordRawBitsDecoderEncodedFieldBits
    (bits : Word Bool) : Word Bool :=
  List.append
    (stageNatBits bits.length)
    (cellsCodeBits (bits.map some))

/-- The only caller prefix accepted by the generic decoder. -/
def boolWordRawBitsDecoderHeaderBits : Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.header

/--
Source tape for the generic Boolean-word raw-bits decoder.  The input starts
with the canonical header bit pattern, then the encoded Boolean-word field,
then the Boolean-word boundary bit, a caller suffix, and the usual right-edge
padding.
-/
def boolWordRawBitsDecoderSourceTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  rightEdgeRewindTargetTape
    (List.append boolWordRawBitsDecoderHeaderBits
      (List.append
        (boolWordRawBitsDecoderEncodedFieldBits bits)
        (false :: suffixTail)))
    rightPadding

/--
Deterministic target padding for the honest decoder: the decoded raw bits get
their scan-stop blank, then the original Boolean boundary/suffix is preserved
as option cells, followed by the original source boundary blank and right
padding.
-/
def boolWordRawBitsDecoderPreservedPadding
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    List (Option Bool) :=
  List.append ((false :: suffixTail).map some) (none :: rightPadding)

/--
Final raw-bits target: decoded Boolean bits in right-edge scan-source shape,
with the deterministic preserved suffix padding.
-/
def boolWordRawBitsDecoderTargetTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  rightEdgeScanSourceTapeFromLeft [none] bits
    (boolWordRawBitsDecoderPreservedPadding suffixTail rightPadding)

def BoolWordRawBitsDecoderSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding : List (Option Bool)),
      decoder.HaltsFromTape
        (boolWordRawBitsDecoderSourceTape
          bits suffixTail rightPadding)
        (boolWordRawBitsDecoderTargetTape
          bits suffixTail rightPadding)

def BoolWordRawBitsDecoderConstruction : Prop :=
  exists decoder : MachineDescription,
    BoolWordRawBitsDecoderSpec decoder

/-!
## Structured decoder pilot

The public one-tape contract below still needs an exact physical normalizer:
the decoded raw cells, erased scaffold blanks, and preserved suffix must all be
repacked into one tape.  The structured pilot separates the algorithmic decode
from that normalization problem.  It uses the canonical length prefix as a
real counter on a second logical tape, writes raw bits on a third logical tape,
and proves the full structured run.
-/

private def structuredBoolWordRawBitsDecoderStay :
    Structured.TapeAction :=
  Structured.TapeAction.preserveMove Structured.HeadMove.stay

private def structuredBoolWordRawBitsDecoderMoveRight :
    Structured.TapeAction :=
  Structured.TapeAction.preserveMove Structured.HeadMove.right

private def structuredBoolWordRawBitsDecoderMoveLeft :
    Structured.TapeAction :=
  Structured.TapeAction.preserveMove Structured.HeadMove.left

private def structuredBoolWordRawBitsDecoderWriteRight
    (cell : Option Bool) : Structured.TapeAction :=
  Structured.TapeAction.writeMove cell Structured.HeadMove.right

private def structuredBoolWordRawBitsDecoderEraseLeft :
    Structured.TapeAction :=
  Structured.TapeAction.writeMove none Structured.HeadMove.left

private def structuredBoolWordRawBitsDecoderRow
    (source : Nat) (sourceRead counterRead outputRead : Option Bool)
    (sourceAction counterAction outputAction : Structured.TapeAction)
    (target : Nat) : Structured.Transition where
  source := source
  reads := [sourceRead, counterRead, outputRead]
  actions := [sourceAction, counterAction, outputAction]
  target := target

private def structuredTransitionWellFormedBool
    (stateCount tapeCount : Nat) (t : Structured.Transition) : Bool :=
  decide (t.source < stateCount) &&
    decide (t.target < stateCount) &&
    decide (t.reads.length = tapeCount) &&
    decide (t.actions.length = tapeCount)

private def structuredTransitionSameKeyBool
    (t u : Structured.Transition) : Bool :=
  decide (t.source = u.source) && decide (t.reads = u.reads)

private def structuredTransitionSameActionBool
    (t u : Structured.Transition) : Bool :=
  decide (t.actions = u.actions) && decide (t.target = u.target)

private def structuredTransitionDeterministicPairBool
    (t u : Structured.Transition) : Bool :=
  !structuredTransitionSameKeyBool t u ||
    structuredTransitionSameActionBool t u

private def structuredTransitionNotFromBool
    (state : Nat) (t : Structured.Transition) : Bool :=
  decide (t.source ≠ state)

private theorem structuredTransition_wellFormed_of_all
    {stateCount tapeCount : Nat} {l : List Structured.Transition}
    (h : l.all (structuredTransitionWellFormedBool stateCount tapeCount) =
      true) :
    forall t : Structured.Transition,
      t ∈ l -> Structured.Transition.WellFormed stateCount tapeCount t := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  simpa [structuredTransitionWellFormedBool,
    Structured.Transition.WellFormed, and_assoc] using htbool

private theorem structuredTransition_deterministic_of_all
    {l : List Structured.Transition}
    (h :
      l.all (fun t =>
        l.all (fun u => structuredTransitionDeterministicPairBool t u)) =
        true) :
    forall t u : Structured.Transition,
      t ∈ l ->
      u ∈ l ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u := by
  intro t u ht hu hkey
  have htbool := (List.all_eq_true.mp h) t ht
  have hubool := (List.all_eq_true.mp htbool) u hu
  have hkeyBool :
      structuredTransitionSameKeyBool t u = true := by
    simpa [structuredTransitionSameKeyBool,
      Structured.Transition.SameKey] using hkey
  simpa [structuredTransitionDeterministicPairBool, hkeyBool,
    structuredTransitionSameActionBool, Structured.Transition.SameAction,
    and_assoc] using hubool

private theorem structuredTransition_notFrom_of_all
    {state : Nat} {l : List Structured.Transition}
    (h : l.all (structuredTransitionNotFromBool state) = true) :
    forall t : Structured.Transition, t ∈ l -> t.source ≠ state := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  simpa [structuredTransitionNotFromBool] using htbool

/--
A three-logical-tape structured decoder for the header-prefixed Boolean-word
bit stream.  Tape 0 is the public source stream, tape 1 is a unary counter
materialized from the length prefix, and tape 2 receives the decoded raw bits.
-/
def structuredBoolWordRawBitsDecoderDescription :
    Structured.Description where
  tapeCount := 3
  stateCount := 100
  start := 80
  halt := 99
  transitions :=
    [ structuredBoolWordRawBitsDecoderRow 80 (some false) none none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 81
    , structuredBoolWordRawBitsDecoderRow 81 (some false) none none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 82
    , structuredBoolWordRawBitsDecoderRow 82 (some false) none none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 83
    , structuredBoolWordRawBitsDecoderRow 83 (some false) none none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 0

    , structuredBoolWordRawBitsDecoderRow 0 (some false) none none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 1
    , structuredBoolWordRawBitsDecoderRow 1 (some false) none none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 2
    , structuredBoolWordRawBitsDecoderRow 2 (some true) none none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 3
    , structuredBoolWordRawBitsDecoderRow 3 (some false) none none
        structuredBoolWordRawBitsDecoderMoveRight
        (structuredBoolWordRawBitsDecoderWriteRight (some true))
        structuredBoolWordRawBitsDecoderStay 0
    , structuredBoolWordRawBitsDecoderRow 3 (some true) none none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderMoveLeft
        structuredBoolWordRawBitsDecoderStay 10

    , structuredBoolWordRawBitsDecoderRow 10 (some false) none none
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 49
    , structuredBoolWordRawBitsDecoderRow 10 (some false) (some true) none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 11
    , structuredBoolWordRawBitsDecoderRow 11 (some true) (some true) none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 12
    , structuredBoolWordRawBitsDecoderRow 12 (some false) (some true) none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 20
    , structuredBoolWordRawBitsDecoderRow 12 (some true) (some true) none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay 30
    , structuredBoolWordRawBitsDecoderRow 20 (some true) (some true) none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderEraseLeft
        (structuredBoolWordRawBitsDecoderWriteRight (some false)) 10
    , structuredBoolWordRawBitsDecoderRow 30 (some false) (some true) none
        structuredBoolWordRawBitsDecoderMoveRight
        structuredBoolWordRawBitsDecoderEraseLeft
        (structuredBoolWordRawBitsDecoderWriteRight (some true)) 10

    , structuredBoolWordRawBitsDecoderRow 49 (some false) none none
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderMoveLeft 50
    , structuredBoolWordRawBitsDecoderRow 50 (some false) none (some false)
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderMoveLeft 50
    , structuredBoolWordRawBitsDecoderRow 50 (some false) none (some true)
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderMoveLeft 50
    , structuredBoolWordRawBitsDecoderRow 50 (some false) none none
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderStay
        structuredBoolWordRawBitsDecoderMoveRight 99 ]

theorem structuredBoolWordRawBitsDecoderDescription_wellFormed :
    structuredBoolWordRawBitsDecoderDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact
      structuredTransition_wellFormed_of_all
        (l := structuredBoolWordRawBitsDecoderDescription.transitions)
        (stateCount :=
          structuredBoolWordRawBitsDecoderDescription.stateCount)
        (tapeCount :=
          structuredBoolWordRawBitsDecoderDescription.tapeCount)
        (by decide)
  · exact
      structuredTransition_deterministic_of_all
        (l := structuredBoolWordRawBitsDecoderDescription.transitions)
        (by decide)

theorem structuredBoolWordRawBitsDecoderDescription_haltTransitionFree :
    structuredBoolWordRawBitsDecoderDescription.HaltTransitionFree :=
  structuredTransition_notFrom_of_all
    (l := structuredBoolWordRawBitsDecoderDescription.transitions)
    (state := structuredBoolWordRawBitsDecoderDescription.halt)
    (by decide)

theorem structuredBoolWordRawBitsDecoderDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredBoolWordRawBitsDecoderDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    (by decide)

def loweredStructuredBoolWordRawBitsDecoderDescription :
    MachineDescription :=
  Structured.MultiTapeLowering.lowerStructured3Description
    structuredBoolWordRawBitsDecoderDescription

theorem loweredStructuredBoolWordRawBitsDecoderDescription_wellFormed :
    loweredStructuredBoolWordRawBitsDecoderDescription.WellFormed := by
  simpa [loweredStructuredBoolWordRawBitsDecoderDescription] using
    Structured.MultiTapeLowering.lowerStructured3Description_wellFormed
      structuredBoolWordRawBitsDecoderDescription_wellFormed
      structuredBoolWordRawBitsDecoderDescription_supportsReadWriteRows3

theorem loweredStructuredBoolWordRawBitsDecoderDescription_subroutineReady :
    loweredStructuredBoolWordRawBitsDecoderDescription.SubroutineReady := by
  simpa [loweredStructuredBoolWordRawBitsDecoderDescription] using
    Structured.MultiTapeLowering.lowerStructured3Description_subroutineReady
      structuredBoolWordRawBitsDecoderDescription_wellFormed
      structuredBoolWordRawBitsDecoderDescription_supportsReadWriteRows3

def structuredBoolWordRawBitsDecoderInitialOutputTape :
    Tape Bool :=
  tapeAtCells [none] []

def structuredBoolWordRawBitsDecoderCounterWriteTape
    (markers : Nat) : Tape Bool :=
  tapeAtCells
    (List.replicate markers (some true : Option Bool)) []

def structuredBoolWordRawBitsDecoderCounterDecodeTape
    (markers blanksRight : Nat) : Tape Bool :=
  match markers with
  | 0 =>
      tapeAtCells [] (none ::
        List.replicate blanksRight (none : Option Bool))
  | Nat.succ markers =>
      tapeAtCells
        (List.replicate markers (some true : Option Bool))
        (some true ::
          List.replicate blanksRight (none : Option Bool))

def structuredBoolWordRawBitsDecoderOutputRightBlankTape
    (bits : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (bits.reverse.map some) [none]) []

def structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
    (bitCount : Nat) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      (List.replicate (bitCount + 1) (none : Option Bool))
      padding)

def structuredBoolWordRawBitsDecoderOutputBufferTape
    (processed : Word Bool) (remainingCount : Nat)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (processed.reverse.map some) [none])
    (List.append
      (List.replicate (remainingCount + 1) (none : Option Bool))
      padding)

def structuredBoolWordRawBitsDecoderOutputRightBlankTapeWithPadding
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  structuredBoolWordRawBitsDecoderOutputBufferTape bits 0 padding

def structuredBoolWordRawBitsDecoderSourceTargetTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      ((List.append boolWordRawBitsDecoderHeaderBits
        (boolWordRawBitsDecoderEncodedFieldBits bits)).reverse.map some)
      [none])
    (some false ::
      List.append (suffixTail.map some) (none :: rightPadding))

def structuredBoolWordRawBitsDecoderAfterHeaderTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none])
    (List.append ((boolWordRawBitsDecoderEncodedFieldBits bits).map some)
      (some false ::
        List.append (suffixTail.map some) (none :: rightPadding)))

private def structuredBoolWordRawBitsDecoderOutputRewindTape
    (revRemaining : Word Bool) (right : List (Option Bool)) :
    Tape Bool :=
  match revRemaining with
  | [] =>
      tapeAtCells [] (none :: right)
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some) [none])
        (some bit :: right)

private theorem structuredBoolWordRawBitsDecoder_run_header
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    structuredBoolWordRawBitsDecoderDescription.runConfig 4
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ boolWordRawBitsDecoderSourceTape
                bits suffixTail rightPadding
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTape ] } =
      { state := 0
        tapes :=
          [ structuredBoolWordRawBitsDecoderAfterHeaderTape
              bits suffixTail rightPadding
          , Tape.blank
          , structuredBoolWordRawBitsDecoderInitialOutputTape ] } := by
  simp [structuredBoolWordRawBitsDecoderDescription,
    structuredBoolWordRawBitsDecoderRow,
    structuredBoolWordRawBitsDecoderMoveRight,
    structuredBoolWordRawBitsDecoderStay,
    boolWordRawBitsDecoderSourceTape,
    structuredBoolWordRawBitsDecoderAfterHeaderTape,
    boolWordRawBitsDecoderHeaderBits, rightEdgeRewindTargetTape,
    structuredBoolWordRawBitsDecoderInitialOutputTape,
    encodeCodeSymbolAsInput, tapeAtCells,
    Structured.Description.runConfig,
    Structured.Description.stepConfig,
    Structured.Description.lookupTransition,
    Structured.Description.Matches,
    Structured.TapeAction.apply,
    Structured.HeadMove.apply,
    Tape.blank, Tape.read, Tape.move, Tape.moveRight,
    List.map_append, List.append_assoc]
  cases htail :
      List.map some (boolWordRawBitsDecoderEncodedFieldBits bits) ++
        some false ::
          (List.map some suffixTail ++ none :: rightPadding) <;>
    rfl

private theorem structuredBoolWordRawBitsDecoder_run_prefix
    (n markers : Nat)
    (sourceLeft tail : List (Option Bool)) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (4 * n + 4)
        { state := 0
          tapes :=
            [ tapeAtCells sourceLeft
                (List.append ((stageNatBits n).map some) tail)
            , structuredBoolWordRawBitsDecoderCounterWriteTape markers
            , structuredBoolWordRawBitsDecoderInitialOutputTape ] } =
      { state := 10
        tapes :=
          [ tapeAtCells
              (List.append ((stageNatBits n).reverse.map some)
                sourceLeft)
              tail
          , structuredBoolWordRawBitsDecoderCounterDecodeTape
              (markers + n) 1
          , structuredBoolWordRawBitsDecoderInitialOutputTape ] } := by
  induction n generalizing markers sourceLeft with
  | zero =>
      cases markers <;>
        simp [structuredBoolWordRawBitsDecoderDescription,
          structuredBoolWordRawBitsDecoderRow,
          structuredBoolWordRawBitsDecoderMoveRight,
          structuredBoolWordRawBitsDecoderMoveLeft,
          structuredBoolWordRawBitsDecoderStay,
          structuredBoolWordRawBitsDecoderCounterWriteTape,
          structuredBoolWordRawBitsDecoderCounterDecodeTape,
          structuredBoolWordRawBitsDecoderInitialOutputTape,
          stageNatBits_zero,
          tapeAtCells, Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.apply,
          Structured.HeadMove.apply,
          Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight]
      all_goals
        cases tail <;> simp [List.replicate_succ]
  | succ n ih =>
      rw [show 4 * (n + 1) + 4 = 4 + (4 * n + 4) by lia]
      rw [Structured.Description.runConfig_add]
      have htick :
          structuredBoolWordRawBitsDecoderDescription.runConfig 4
            { state := 0
              tapes :=
                [ tapeAtCells sourceLeft
                    (List.append
                      ((stageNatBits (n + 1)).map some) tail)
                , structuredBoolWordRawBitsDecoderCounterWriteTape
                    markers
                , structuredBoolWordRawBitsDecoderInitialOutputTape ] } =
          { state := 0
            tapes :=
              [ tapeAtCells
                  (List.append (tickBits.reverse.map some) sourceLeft)
                  (List.append ((stageNatBits n).map some) tail)
              , structuredBoolWordRawBitsDecoderCounterWriteTape
                  (markers + 1)
              , structuredBoolWordRawBitsDecoderInitialOutputTape ] } := by
        simp [structuredBoolWordRawBitsDecoderDescription,
          structuredBoolWordRawBitsDecoderRow,
          structuredBoolWordRawBitsDecoderMoveRight,
          structuredBoolWordRawBitsDecoderWriteRight,
          structuredBoolWordRawBitsDecoderStay,
          structuredBoolWordRawBitsDecoderCounterWriteTape,
          structuredBoolWordRawBitsDecoderInitialOutputTape,
          stageNatBits_succ, tickBits, encodeCodeSymbolAsInput,
          tapeAtCells, Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.apply,
          Structured.HeadMove.apply,
          Tape.read, Tape.write, Tape.move, Tape.moveRight,
          List.replicate_succ]
        cases htail :
            List.map some (stageNatBits n) ++ tail <;>
          rfl
      rw [htick]
      simpa [stageNatBits_succ, tickBits, encodeCodeSymbolAsInput,
        List.map_append, List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (markers + 1)
          (List.append (tickBits.reverse.map some) sourceLeft)

private theorem structuredBoolWordRawBitsDecoder_run_prefix_withOutput
    (n markers : Nat)
    (sourceLeft tail : List (Option Bool)) (output : Tape Bool)
    (houtput : Tape.read output = none) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (4 * n + 4)
        { state := 0
          tapes :=
            [ tapeAtCells sourceLeft
                (List.append ((stageNatBits n).map some) tail)
            , structuredBoolWordRawBitsDecoderCounterWriteTape markers
            , output ] } =
      { state := 10
        tapes :=
          [ tapeAtCells
              (List.append ((stageNatBits n).reverse.map some)
                sourceLeft)
              tail
          , structuredBoolWordRawBitsDecoderCounterDecodeTape
              (markers + n) 1
          , output ] } := by
  change output.head = none at houtput
  induction n generalizing markers sourceLeft with
  | zero =>
      cases markers <;>
        simp [structuredBoolWordRawBitsDecoderDescription,
          structuredBoolWordRawBitsDecoderRow,
          structuredBoolWordRawBitsDecoderMoveRight,
          structuredBoolWordRawBitsDecoderMoveLeft,
          structuredBoolWordRawBitsDecoderStay,
          structuredBoolWordRawBitsDecoderCounterWriteTape,
          structuredBoolWordRawBitsDecoderCounterDecodeTape,
          stageNatBits_zero,
          tapeAtCells, Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.apply,
          Structured.HeadMove.apply,
          Tape.read, houtput, Tape.move, Tape.moveLeft, Tape.moveRight]
      all_goals
        cases tail <;> simp [List.replicate_succ]
  | succ n ih =>
      rw [show 4 * (n + 1) + 4 = 4 + (4 * n + 4) by lia]
      rw [Structured.Description.runConfig_add]
      have htick :
          structuredBoolWordRawBitsDecoderDescription.runConfig 4
            { state := 0
              tapes :=
                [ tapeAtCells sourceLeft
                    (List.append
                      ((stageNatBits (n + 1)).map some) tail)
                , structuredBoolWordRawBitsDecoderCounterWriteTape
                    markers
                , output ] } =
          { state := 0
            tapes :=
              [ tapeAtCells
                  (List.append (tickBits.reverse.map some) sourceLeft)
                  (List.append ((stageNatBits n).map some) tail)
              , structuredBoolWordRawBitsDecoderCounterWriteTape
                  (markers + 1)
              , output ] } := by
        simp [structuredBoolWordRawBitsDecoderDescription,
          structuredBoolWordRawBitsDecoderRow,
          structuredBoolWordRawBitsDecoderMoveRight,
          structuredBoolWordRawBitsDecoderWriteRight,
          structuredBoolWordRawBitsDecoderStay,
          structuredBoolWordRawBitsDecoderCounterWriteTape,
          stageNatBits_succ, tickBits, encodeCodeSymbolAsInput,
          tapeAtCells, Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.apply,
          Structured.HeadMove.apply,
          Tape.read, houtput, Tape.write, Tape.move, Tape.moveRight,
          List.replicate_succ]
        cases htail :
            List.map some (stageNatBits n) ++ tail <;>
          rfl
      rw [htick]
      simpa [stageNatBits_succ, tickBits, encodeCodeSymbolAsInput,
        List.map_append, List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (markers + 1)
          (List.append (tickBits.reverse.map some) sourceLeft)

private theorem structuredBoolWordRawBitsDecoder_run_decode_loop
    (remaining processed : Word Bool)
    (sourceLeft : List (Option Bool))
    (suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (4 * remaining.length + 1)
        { state := 10
          tapes :=
            [ tapeAtCells sourceLeft
                (List.append
                  ((cellsCodeBits (remaining.map some)).map some)
                  (some false ::
                    List.append (suffixTail.map some)
                      (none :: rightPadding)))
            , structuredBoolWordRawBitsDecoderCounterDecodeTape
                remaining.length (processed.length + 1)
            , structuredBoolWordRawBitsDecoderOutputRightBlankTape
                processed ] } =
      { state := 49
        tapes :=
          [ tapeAtCells
              (List.append
                ((cellsCodeBits (remaining.map some)).reverse.map some)
                sourceLeft)
              (some false ::
                List.append (suffixTail.map some)
                  (none :: rightPadding))
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              (processed.length + remaining.length + 1)
          , structuredBoolWordRawBitsDecoderOutputRightBlankTape
              (List.append processed remaining) ] } := by
  induction remaining generalizing processed sourceLeft with
  | nil =>
      simp [structuredBoolWordRawBitsDecoderDescription,
        structuredBoolWordRawBitsDecoderRow,
        structuredBoolWordRawBitsDecoderStay,
        structuredBoolWordRawBitsDecoderCounterDecodeTape,
        structuredBoolWordRawBitsDecoderOutputRightBlankTape,
        cellsCodeBits, tapeAtCells,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.apply,
        Structured.HeadMove.apply,
        Tape.read]
  | cons bit rest ih =>
      rw [show 4 * (bit :: rest).length + 1 =
          4 + (4 * rest.length + 1) by
        simp
        lia]
      rw [Structured.Description.runConfig_add]
      have hcell :
          structuredBoolWordRawBitsDecoderDescription.runConfig 4
            { state := 10
              tapes :=
                [ tapeAtCells sourceLeft
                    (List.append
                      ((cellsCodeBits ((bit :: rest).map some)).map some)
                      (some false ::
                        List.append (suffixTail.map some)
                          (none :: rightPadding)))
                , structuredBoolWordRawBitsDecoderCounterDecodeTape
                    (bit :: rest).length (processed.length + 1)
                , structuredBoolWordRawBitsDecoderOutputRightBlankTape
                    processed ] } =
          { state := 10
            tapes :=
              [ tapeAtCells
                  (List.append ((cellCodeBits (some bit)).reverse.map some)
                    sourceLeft)
                  (List.append
                    ((cellsCodeBits (rest.map some)).map some)
                    (some false ::
                      List.append (suffixTail.map some)
                        (none :: rightPadding)))
              , structuredBoolWordRawBitsDecoderCounterDecodeTape
                  rest.length (processed.length + 2)
              , structuredBoolWordRawBitsDecoderOutputRightBlankTape
                  (List.append processed [bit]) ] } := by
        cases bit <;>
          simp [structuredBoolWordRawBitsDecoderDescription,
            structuredBoolWordRawBitsDecoderRow,
            structuredBoolWordRawBitsDecoderMoveRight,
            structuredBoolWordRawBitsDecoderStay,
            structuredBoolWordRawBitsDecoderEraseLeft,
            structuredBoolWordRawBitsDecoderWriteRight,
            structuredBoolWordRawBitsDecoderCounterDecodeTape,
            structuredBoolWordRawBitsDecoderOutputRightBlankTape,
            cellsCodeBits, cellCodeBits, encodeCell,
            encodeCodeWordAsInput, encodeCodeSymbolAsInput,
            tapeAtCells, Structured.Description.runConfig,
            Structured.Description.stepConfig,
            Structured.Description.lookupTransition,
            Structured.Description.Matches,
            Structured.TapeAction.apply,
            Structured.HeadMove.apply,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            Tape.moveRight, List.reverse_append]
        all_goals
          constructor
          · cases htail :
              List.map some (cellsCodeBits (List.map some rest)) ++
                some false ::
                  (List.map some suffixTail ++ none :: rightPadding) <;>
              rfl
          · cases rest <;> simp [List.replicate_succ]
      rw [hcell]
      simpa [cellsCodeBits, List.map_append, List.reverse_append,
        List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        ih (List.append processed [bit])
          (List.append ((cellCodeBits (some bit)).reverse.map some)
            sourceLeft)

private theorem structuredBoolWordRawBitsDecoder_run_decode_loop_withPadding
    (remaining processed : Word Bool)
    (sourceLeft : List (Option Bool))
    (suffixTail : Word Bool)
    (rightPadding outputPadding : List (Option Bool)) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (4 * remaining.length + 1)
        { state := 10
          tapes :=
            [ tapeAtCells sourceLeft
                (List.append
                  ((cellsCodeBits (remaining.map some)).map some)
                  (some false ::
                    List.append (suffixTail.map some)
                      (none :: rightPadding)))
            , structuredBoolWordRawBitsDecoderCounterDecodeTape
                remaining.length (processed.length + 1)
            , structuredBoolWordRawBitsDecoderOutputBufferTape
                processed remaining.length outputPadding ] } =
      { state := 49
        tapes :=
          [ tapeAtCells
              (List.append
                ((cellsCodeBits (remaining.map some)).reverse.map some)
                sourceLeft)
              (some false ::
                List.append (suffixTail.map some)
                  (none :: rightPadding))
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              (processed.length + remaining.length + 1)
          , structuredBoolWordRawBitsDecoderOutputRightBlankTapeWithPadding
              (List.append processed remaining) outputPadding ] } := by
  induction remaining generalizing processed sourceLeft with
  | nil =>
      simp [structuredBoolWordRawBitsDecoderDescription,
        structuredBoolWordRawBitsDecoderRow,
        structuredBoolWordRawBitsDecoderStay,
        structuredBoolWordRawBitsDecoderCounterDecodeTape,
        structuredBoolWordRawBitsDecoderOutputBufferTape,
        structuredBoolWordRawBitsDecoderOutputRightBlankTapeWithPadding,
        cellsCodeBits, tapeAtCells,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.apply,
        Structured.HeadMove.apply,
        Tape.read]
  | cons bit rest ih =>
      rw [show 4 * (bit :: rest).length + 1 =
          4 + (4 * rest.length + 1) by
        simp
        lia]
      rw [Structured.Description.runConfig_add]
      have hcell :
          structuredBoolWordRawBitsDecoderDescription.runConfig 4
            { state := 10
              tapes :=
                [ tapeAtCells sourceLeft
                    (List.append
                      ((cellsCodeBits ((bit :: rest).map some)).map some)
                      (some false ::
                        List.append (suffixTail.map some)
                          (none :: rightPadding)))
                , structuredBoolWordRawBitsDecoderCounterDecodeTape
                    (bit :: rest).length (processed.length + 1)
                , structuredBoolWordRawBitsDecoderOutputBufferTape
                    processed (bit :: rest).length outputPadding ] } =
          { state := 10
            tapes :=
              [ tapeAtCells
                  (List.append ((cellCodeBits (some bit)).reverse.map some)
                    sourceLeft)
                  (List.append
                    ((cellsCodeBits (rest.map some)).map some)
                    (some false ::
                      List.append (suffixTail.map some)
                        (none :: rightPadding)))
              , structuredBoolWordRawBitsDecoderCounterDecodeTape
                  rest.length (processed.length + 2)
              , structuredBoolWordRawBitsDecoderOutputBufferTape
                  (List.append processed [bit]) rest.length
                  outputPadding ] } := by
        cases bit <;>
          simp [structuredBoolWordRawBitsDecoderDescription,
            structuredBoolWordRawBitsDecoderRow,
            structuredBoolWordRawBitsDecoderMoveRight,
            structuredBoolWordRawBitsDecoderStay,
            structuredBoolWordRawBitsDecoderEraseLeft,
            structuredBoolWordRawBitsDecoderWriteRight,
            structuredBoolWordRawBitsDecoderCounterDecodeTape,
            structuredBoolWordRawBitsDecoderOutputBufferTape,
            cellsCodeBits, cellCodeBits, encodeCell,
            encodeCodeWordAsInput, encodeCodeSymbolAsInput,
            tapeAtCells, Structured.Description.runConfig,
            Structured.Description.stepConfig,
            Structured.Description.lookupTransition,
            Structured.Description.Matches,
            Structured.TapeAction.apply,
            Structured.HeadMove.apply,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            Tape.moveRight, List.reverse_append,
            List.replicate_succ]
        all_goals
          constructor
          · cases htail :
              List.map some (cellsCodeBits (List.map some rest)) ++
                some false ::
                  (List.map some suffixTail ++ none :: rightPadding) <;>
              rfl
          · cases rest <;> simp [List.replicate_succ]
      rw [hcell]
      simpa [cellsCodeBits, List.map_append, List.reverse_append,
        List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        ih (List.append processed [bit])
          (List.append ((cellCodeBits (some bit)).reverse.map some)
            sourceLeft)

private theorem structuredBoolWordRawBitsDecoder_run_output_rewind_loop
    (revRemaining : Word Bool) (right : List (Option Bool))
    (sourceLeft sourceRight : List (Option Bool))
    (counterBlanks : Nat) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (revRemaining.length + 1)
        { state := 50
          tapes :=
            [ tapeAtCells sourceLeft (some false :: sourceRight)
            , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
                counterBlanks
            , structuredBoolWordRawBitsDecoderOutputRewindTape
                revRemaining right ] } =
      { state := structuredBoolWordRawBitsDecoderDescription.halt
        tapes :=
          [ tapeAtCells sourceLeft (some false :: sourceRight)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              counterBlanks
          , tapeAtCells [none]
              (List.append (revRemaining.reverse.map some)
                right) ] } := by
  induction revRemaining generalizing right with
  | nil =>
      simp [structuredBoolWordRawBitsDecoderDescription,
        structuredBoolWordRawBitsDecoderRow,
        structuredBoolWordRawBitsDecoderMoveRight,
        structuredBoolWordRawBitsDecoderStay,
        structuredBoolWordRawBitsDecoderCounterDecodeTape,
        structuredBoolWordRawBitsDecoderOutputRewindTape,
        tapeAtCells, Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.apply,
        Structured.HeadMove.apply,
        Tape.read, Tape.move, Tape.moveRight]
      cases right <;> rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 =
          1 + (rest.length + 1) by
        simp
        lia]
      rw [Structured.Description.runConfig_add]
      have hstep :
          structuredBoolWordRawBitsDecoderDescription.runConfig 1
            { state := 50
              tapes :=
                [ tapeAtCells sourceLeft (some false :: sourceRight)
                , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
                    counterBlanks
                , structuredBoolWordRawBitsDecoderOutputRewindTape
                    (bit :: rest) right ] } =
          { state := 50
            tapes :=
              [ tapeAtCells sourceLeft (some false :: sourceRight)
              , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
                  counterBlanks
              , structuredBoolWordRawBitsDecoderOutputRewindTape
                  rest (some bit :: right) ] } := by
        cases bit <;>
          simp [structuredBoolWordRawBitsDecoderDescription,
            structuredBoolWordRawBitsDecoderRow,
            structuredBoolWordRawBitsDecoderMoveLeft,
            structuredBoolWordRawBitsDecoderStay,
            structuredBoolWordRawBitsDecoderCounterDecodeTape,
            structuredBoolWordRawBitsDecoderOutputRewindTape,
            tapeAtCells, Structured.Description.runConfig,
            Structured.Description.stepConfig,
            Structured.Description.lookupTransition,
            Structured.Description.Matches,
          Structured.TapeAction.apply,
          Structured.HeadMove.apply,
          Tape.read, Tape.move, Tape.moveLeft]
        all_goals
          cases rest <;> rfl
      rw [hstep]
      simpa [List.append_assoc] using ih (some bit :: right)

private theorem structuredBoolWordRawBitsDecoder_run_output_rewind
    (bits : Word Bool) (sourceLeft sourceRight : List (Option Bool))
    (counterBlanks : Nat) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (bits.length + 2)
        { state := 49
          tapes :=
            [ tapeAtCells sourceLeft (some false :: sourceRight)
            , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
                counterBlanks
            , structuredBoolWordRawBitsDecoderOutputRightBlankTape bits ] } =
      { state := structuredBoolWordRawBitsDecoderDescription.halt
        tapes :=
          [ tapeAtCells sourceLeft (some false :: sourceRight)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              counterBlanks
          , rightEdgeScanSourceTapeFromLeft [none] bits [] ] } := by
  rw [show bits.length + 2 = 1 + (bits.reverse.length + 1) by
    simp
    lia]
  rw [Structured.Description.runConfig_add]
  have hstep :
      structuredBoolWordRawBitsDecoderDescription.runConfig 1
        { state := 49
          tapes :=
            [ tapeAtCells sourceLeft (some false :: sourceRight)
            , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
                counterBlanks
            , structuredBoolWordRawBitsDecoderOutputRightBlankTape bits ] } =
      { state := 50
        tapes :=
          [ tapeAtCells sourceLeft (some false :: sourceRight)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              counterBlanks
          , structuredBoolWordRawBitsDecoderOutputRewindTape
              bits.reverse [none] ] } := by
    cases hrev : bits.reverse with
    | nil =>
        simp [structuredBoolWordRawBitsDecoderDescription,
          structuredBoolWordRawBitsDecoderRow,
          structuredBoolWordRawBitsDecoderMoveLeft,
          structuredBoolWordRawBitsDecoderStay,
          structuredBoolWordRawBitsDecoderCounterDecodeTape,
          structuredBoolWordRawBitsDecoderOutputRightBlankTape,
          structuredBoolWordRawBitsDecoderOutputRewindTape,
          tapeAtCells, Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.apply,
          Structured.HeadMove.apply,
          Tape.read, Tape.move, Tape.moveLeft, hrev]
    | cons bit rest =>
        cases bit <;>
          simp [structuredBoolWordRawBitsDecoderDescription,
            structuredBoolWordRawBitsDecoderRow,
            structuredBoolWordRawBitsDecoderMoveLeft,
            structuredBoolWordRawBitsDecoderStay,
            structuredBoolWordRawBitsDecoderCounterDecodeTape,
            structuredBoolWordRawBitsDecoderOutputRightBlankTape,
            structuredBoolWordRawBitsDecoderOutputRewindTape,
            tapeAtCells, Structured.Description.runConfig,
            Structured.Description.stepConfig,
            Structured.Description.lookupTransition,
            Structured.Description.Matches,
            Structured.TapeAction.apply,
            Structured.HeadMove.apply,
            Tape.read, Tape.move, Tape.moveLeft, hrev]
  rw [hstep]
  simpa [rightEdgeScanSourceTapeFromLeft] using
    structuredBoolWordRawBitsDecoder_run_output_rewind_loop
      bits.reverse [none] sourceLeft sourceRight counterBlanks

private theorem structuredBoolWordRawBitsDecoder_run_output_rewind_withPadding
    (bits : Word Bool) (sourceLeft sourceRight : List (Option Bool))
    (counterBlanks : Nat) (outputPadding : List (Option Bool)) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (bits.length + 2)
        { state := 49
          tapes :=
            [ tapeAtCells sourceLeft (some false :: sourceRight)
            , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
                counterBlanks
            , structuredBoolWordRawBitsDecoderOutputRightBlankTapeWithPadding
                bits outputPadding ] } =
      { state := structuredBoolWordRawBitsDecoderDescription.halt
        tapes :=
          [ tapeAtCells sourceLeft (some false :: sourceRight)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              counterBlanks
          , rightEdgeScanSourceTapeFromLeft [none] bits
              outputPadding ] } := by
  rw [show bits.length + 2 = 1 + (bits.reverse.length + 1) by
    simp
    lia]
  rw [Structured.Description.runConfig_add]
  have hstep :
      structuredBoolWordRawBitsDecoderDescription.runConfig 1
        { state := 49
          tapes :=
            [ tapeAtCells sourceLeft (some false :: sourceRight)
            , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
                counterBlanks
            , structuredBoolWordRawBitsDecoderOutputRightBlankTapeWithPadding
                bits outputPadding ] } =
      { state := 50
        tapes :=
          [ tapeAtCells sourceLeft (some false :: sourceRight)
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              counterBlanks
          , structuredBoolWordRawBitsDecoderOutputRewindTape
              bits.reverse (none :: outputPadding) ] } := by
    cases hrev : bits.reverse with
    | nil =>
        simp [structuredBoolWordRawBitsDecoderDescription,
          structuredBoolWordRawBitsDecoderRow,
          structuredBoolWordRawBitsDecoderMoveLeft,
          structuredBoolWordRawBitsDecoderStay,
          structuredBoolWordRawBitsDecoderCounterDecodeTape,
          structuredBoolWordRawBitsDecoderOutputRightBlankTapeWithPadding,
          structuredBoolWordRawBitsDecoderOutputBufferTape,
          structuredBoolWordRawBitsDecoderOutputRewindTape,
          tapeAtCells, Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.apply,
          Structured.HeadMove.apply,
          Tape.read, Tape.move, Tape.moveLeft, hrev]
    | cons bit rest =>
        cases bit <;>
          simp [structuredBoolWordRawBitsDecoderDescription,
            structuredBoolWordRawBitsDecoderRow,
            structuredBoolWordRawBitsDecoderMoveLeft,
            structuredBoolWordRawBitsDecoderStay,
            structuredBoolWordRawBitsDecoderCounterDecodeTape,
            structuredBoolWordRawBitsDecoderOutputRightBlankTapeWithPadding,
            structuredBoolWordRawBitsDecoderOutputBufferTape,
            structuredBoolWordRawBitsDecoderOutputRewindTape,
            tapeAtCells, Structured.Description.runConfig,
            Structured.Description.stepConfig,
            Structured.Description.lookupTransition,
            Structured.Description.Matches,
            Structured.TapeAction.apply,
            Structured.HeadMove.apply,
            Tape.read, Tape.move, Tape.moveLeft, hrev]
  rw [hstep]
  simpa [rightEdgeScanSourceTapeFromLeft] using
    structuredBoolWordRawBitsDecoder_run_output_rewind_loop
      bits.reverse (none :: outputPadding) sourceLeft sourceRight
      counterBlanks

theorem structuredBoolWordRawBitsDecoderDescription_run
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (9 * bits.length + 11)
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ boolWordRawBitsDecoderSourceTape
                bits suffixTail rightPadding
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTape ] } =
      { state := structuredBoolWordRawBitsDecoderDescription.halt
        tapes :=
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              bits suffixTail rightPadding
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              (bits.length + 1)
          , rightEdgeScanSourceTapeFromLeft [none] bits [] ] } := by
  rw [show 9 * bits.length + 11 =
      4 + ((4 * bits.length + 4) +
        ((4 * bits.length + 1) + (bits.length + 2))) by
    lia]
  rw [Structured.Description.runConfig_add]
  rw [structuredBoolWordRawBitsDecoder_run_header]
  rw [Structured.Description.runConfig_add]
  have hafter :
      structuredBoolWordRawBitsDecoderAfterHeaderTape
          bits suffixTail rightPadding =
        tapeAtCells
          (List.append
            (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none])
          (List.append ((stageNatBits bits.length).map some)
            (List.append ((cellsCodeBits (bits.map some)).map some)
              (some false ::
                List.append (suffixTail.map some)
                  (none :: rightPadding)))) := by
    simp [structuredBoolWordRawBitsDecoderAfterHeaderTape,
      boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
      List.append_assoc]
  rw [hafter]
  rw [show Tape.blank =
      structuredBoolWordRawBitsDecoderCounterWriteTape 0 by rfl]
  rw [structuredBoolWordRawBitsDecoder_run_prefix]
  rw [Structured.Description.runConfig_add]
  rw [show 0 + bits.length = bits.length by simp]
  have hout :
      structuredBoolWordRawBitsDecoderInitialOutputTape =
        structuredBoolWordRawBitsDecoderOutputRightBlankTape [] := by
    simp [structuredBoolWordRawBitsDecoderInitialOutputTape,
      structuredBoolWordRawBitsDecoderOutputRightBlankTape]
  rw [hout]
  have hdecode :
      structuredBoolWordRawBitsDecoderDescription.runConfig
          (4 * bits.length + 1)
          { state := 10
            tapes :=
              [ tapeAtCells
                  (List.append ((stageNatBits bits.length).reverse.map some)
                    (List.append
                      (boolWordRawBitsDecoderHeaderBits.reverse.map some)
                      [none]))
                  (List.append
                    ((cellsCodeBits (bits.map some)).map some)
                    (some false ::
                      List.append (suffixTail.map some)
                        (none :: rightPadding)))
              , structuredBoolWordRawBitsDecoderCounterDecodeTape
                  bits.length 1
              , structuredBoolWordRawBitsDecoderOutputRightBlankTape [] ] } =
        { state := 49
          tapes :=
            [ tapeAtCells
                (List.append
                  ((cellsCodeBits (bits.map some)).reverse.map some)
                  (List.append
                    ((stageNatBits bits.length).reverse.map some)
                    (List.append
                      (boolWordRawBitsDecoderHeaderBits.reverse.map some)
                      [none])))
                (some false ::
                  List.append (suffixTail.map some)
                    (none :: rightPadding))
            , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
                (bits.length + 1)
            , structuredBoolWordRawBitsDecoderOutputRightBlankTape bits ] } := by
    simpa [List.append_assoc] using
      structuredBoolWordRawBitsDecoder_run_decode_loop
        bits ([] : Word Bool)
        (List.append ((stageNatBits bits.length).reverse.map some)
          (List.append
            (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none]))
        suffixTail rightPadding
  rw [hdecode]
  simpa [structuredBoolWordRawBitsDecoderAfterHeaderTape,
    structuredBoolWordRawBitsDecoderSourceTargetTape,
    boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
    List.reverse_append, List.append_assoc] using
    structuredBoolWordRawBitsDecoder_run_output_rewind
      bits
      (List.append
        ((cellsCodeBits (bits.map some)).reverse.map some)
        (List.append
          ((stageNatBits bits.length).reverse.map some)
          (List.append
            (boolWordRawBitsDecoderHeaderBits.reverse.map some)
            [none])))
      (List.append (suffixTail.map some) (none :: rightPadding))
      (bits.length + 1)

theorem loweredStructuredBoolWordRawBitsDecoderDescription_haltsFromTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    loweredStructuredBoolWordRawBitsDecoderDescription.HaltsFromTapeEquiv
      (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
        [ boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding
        , Tape.blank
        , structuredBoolWordRawBitsDecoderInitialOutputTape ])
      (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
        [ structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail rightPadding
        , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
            (bits.length + 1)
        , rightEdgeScanSourceTapeFromLeft [none] bits [] ]) := by
  simpa [loweredStructuredBoolWordRawBitsDecoderDescription] using
    Structured.MultiTapeLowering.lowerStructured3Description_haltsFromConfigWithTapes
      structuredBoolWordRawBitsDecoderDescription_wellFormed
      structuredBoolWordRawBitsDecoderDescription_haltTransitionFree
      structuredBoolWordRawBitsDecoderDescription_supportsReadWriteRows3
      (c :=
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTape ] })
      (tapes :=
        [ structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail rightPadding
        , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
            (bits.length + 1)
        , rightEdgeScanSourceTapeFromLeft [none] bits [] ])
      rfl
      (by simp [structuredBoolWordRawBitsDecoderDescription])
      ⟨9 * bits.length + 11,
        structuredBoolWordRawBitsDecoderDescription_run
          bits suffixTail rightPadding⟩

def LoweredStructuredBoolWordRawBitsDecoderSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding : List (Option Bool)),
      decoder.HaltsFromTapeEquiv
        (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
          [ boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding
          , Tape.blank
          , structuredBoolWordRawBitsDecoderInitialOutputTape ])
        (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              bits suffixTail rightPadding
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              (bits.length + 1)
          , rightEdgeScanSourceTapeFromLeft [none] bits [] ])

def LoweredStructuredBoolWordRawBitsDecoderConstruction : Prop :=
  exists decoder : MachineDescription,
    LoweredStructuredBoolWordRawBitsDecoderSpec decoder

theorem loweredStructuredBoolWordRawBitsDecoderConstruction_core :
    LoweredStructuredBoolWordRawBitsDecoderConstruction := by
  exact
    ⟨loweredStructuredBoolWordRawBitsDecoderDescription,
      loweredStructuredBoolWordRawBitsDecoderDescription_subroutineReady,
      loweredStructuredBoolWordRawBitsDecoderDescription_haltsFromTape⟩

theorem structuredBoolWordRawBitsDecoderDescription_run_withOutputPadding
    (bits suffixTail : Word Bool)
    (rightPadding outputPadding : List (Option Bool)) :
    structuredBoolWordRawBitsDecoderDescription.runConfig
        (9 * bits.length + 11)
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ boolWordRawBitsDecoderSourceTape
                bits suffixTail rightPadding
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
                bits.length outputPadding ] } =
      { state := structuredBoolWordRawBitsDecoderDescription.halt
        tapes :=
          [ structuredBoolWordRawBitsDecoderSourceTargetTape
              bits suffixTail rightPadding
          , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
              (bits.length + 1)
          , rightEdgeScanSourceTapeFromLeft [none] bits outputPadding ] } := by
  rw [show 9 * bits.length + 11 =
      4 + ((4 * bits.length + 4) +
        ((4 * bits.length + 1) + (bits.length + 2))) by
    lia]
  rw [Structured.Description.runConfig_add]
  have hheader :
      structuredBoolWordRawBitsDecoderDescription.runConfig 4
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
                bits.length outputPadding ] } =
        { state := 0
          tapes :=
            [ structuredBoolWordRawBitsDecoderAfterHeaderTape
                bits suffixTail rightPadding
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
                bits.length outputPadding ] } := by
    simp [structuredBoolWordRawBitsDecoderDescription,
      structuredBoolWordRawBitsDecoderRow,
      structuredBoolWordRawBitsDecoderMoveRight,
      structuredBoolWordRawBitsDecoderStay,
      boolWordRawBitsDecoderSourceTape,
      structuredBoolWordRawBitsDecoderAfterHeaderTape,
      boolWordRawBitsDecoderHeaderBits, rightEdgeRewindTargetTape,
      structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding,
      encodeCodeSymbolAsInput, tapeAtCells,
      Structured.Description.runConfig,
      Structured.Description.stepConfig,
      Structured.Description.lookupTransition,
      Tape.blank, Tape.read,
      List.map_append, List.append_assoc]
    cases htail :
        List.map some (boolWordRawBitsDecoderEncodedFieldBits bits) ++
          some false ::
            (List.map some suffixTail ++ none :: rightPadding) <;>
      rfl
  rw [hheader]
  rw [Structured.Description.runConfig_add]
  have hafter :
      structuredBoolWordRawBitsDecoderAfterHeaderTape
          bits suffixTail rightPadding =
        tapeAtCells
          (List.append
            (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none])
          (List.append ((stageNatBits bits.length).map some)
            (List.append ((cellsCodeBits (bits.map some)).map some)
              (some false ::
                List.append (suffixTail.map some)
                  (none :: rightPadding)))) := by
    simp [structuredBoolWordRawBitsDecoderAfterHeaderTape,
      boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
      List.append_assoc]
  rw [hafter]
  rw [show Tape.blank =
      structuredBoolWordRawBitsDecoderCounterWriteTape 0 by rfl]
  have houtputHead :
      Tape.read
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            bits.length outputPadding) = none := by
    simp [structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding,
      tapeAtCells, Tape.read, List.replicate_succ]
  have hprefix :
      structuredBoolWordRawBitsDecoderDescription.runConfig
          (4 * bits.length + 4)
          { state := 0
            tapes :=
              [ tapeAtCells
                  (List.append
                    (boolWordRawBitsDecoderHeaderBits.reverse.map some)
                    [none])
                  (List.append ((stageNatBits bits.length).map some)
                    (List.append
                      ((cellsCodeBits (bits.map some)).map some)
                      (some false ::
                        List.append (suffixTail.map some)
                          (none :: rightPadding))))
              , structuredBoolWordRawBitsDecoderCounterWriteTape 0
              , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
                  bits.length outputPadding ] } =
        { state := 10
          tapes :=
            [ tapeAtCells
                (List.append ((stageNatBits bits.length).reverse.map some)
                  (List.append
                    (boolWordRawBitsDecoderHeaderBits.reverse.map some)
                    [none]))
                (List.append
                  ((cellsCodeBits (bits.map some)).map some)
                  (some false ::
                    List.append (suffixTail.map some)
                      (none :: rightPadding)))
            , structuredBoolWordRawBitsDecoderCounterDecodeTape
                bits.length 1
            , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
                bits.length outputPadding ] } := by
    simpa [List.append_assoc] using
      structuredBoolWordRawBitsDecoder_run_prefix_withOutput
        bits.length 0
        (List.append
          (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none])
        (List.append
          ((cellsCodeBits (bits.map some)).map some)
          (some false ::
            List.append (suffixTail.map some)
              (none :: rightPadding)))
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          bits.length outputPadding)
        houtputHead
  rw [hprefix]
  rw [Structured.Description.runConfig_add]
  have houtput :
      structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          bits.length outputPadding =
        structuredBoolWordRawBitsDecoderOutputBufferTape
          ([] : Word Bool) bits.length outputPadding := by
    simp [structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding,
      structuredBoolWordRawBitsDecoderOutputBufferTape]
  rw [houtput]
  have hdecode :
      structuredBoolWordRawBitsDecoderDescription.runConfig
          (4 * bits.length + 1)
          { state := 10
            tapes :=
              [ tapeAtCells
                  (List.append ((stageNatBits bits.length).reverse.map some)
                    (List.append
                      (boolWordRawBitsDecoderHeaderBits.reverse.map some)
                      [none]))
                  (List.append
                    ((cellsCodeBits (bits.map some)).map some)
                    (some false ::
                      List.append (suffixTail.map some)
                        (none :: rightPadding)))
              , structuredBoolWordRawBitsDecoderCounterDecodeTape
                  bits.length 1
              , structuredBoolWordRawBitsDecoderOutputBufferTape
                  ([] : Word Bool) bits.length outputPadding ] } =
        { state := 49
          tapes :=
            [ tapeAtCells
                (List.append
                  ((cellsCodeBits (bits.map some)).reverse.map some)
                  (List.append
                    ((stageNatBits bits.length).reverse.map some)
                    (List.append
                      (boolWordRawBitsDecoderHeaderBits.reverse.map some)
                      [none])))
                (some false ::
                  List.append (suffixTail.map some)
                    (none :: rightPadding))
            , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
                (bits.length + 1)
            , structuredBoolWordRawBitsDecoderOutputRightBlankTapeWithPadding
                bits outputPadding ] } := by
    simpa [List.append_assoc] using
      structuredBoolWordRawBitsDecoder_run_decode_loop_withPadding
        bits ([] : Word Bool)
        (List.append ((stageNatBits bits.length).reverse.map some)
          (List.append
            (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none]))
        suffixTail rightPadding outputPadding
  rw [hdecode]
  simpa [structuredBoolWordRawBitsDecoderAfterHeaderTape,
    structuredBoolWordRawBitsDecoderSourceTargetTape,
    boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
    List.reverse_append, List.append_assoc] using
    structuredBoolWordRawBitsDecoder_run_output_rewind_withPadding
      bits
      (List.append
        ((cellsCodeBits (bits.map some)).reverse.map some)
        (List.append
          ((stageNatBits bits.length).reverse.map some)
          (List.append
            (boolWordRawBitsDecoderHeaderBits.reverse.map some)
            [none])))
      (List.append (suffixTail.map some) (none :: rightPadding))
      (bits.length + 1)
      outputPadding

theorem loweredStructuredBoolWordRawBitsDecoderDescription_haltsFromTapeWithOutputPadding
    (bits suffixTail : Word Bool)
    (rightPadding outputPadding : List (Option Bool)) :
    loweredStructuredBoolWordRawBitsDecoderDescription.HaltsFromTapeEquiv
      (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
        [ boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding
        , Tape.blank
        , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            bits.length outputPadding ])
      (Structured.MultiTapeLowering.encodedGuardedStructuredTapes
        [ structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail rightPadding
        , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
            (bits.length + 1)
        , rightEdgeScanSourceTapeFromLeft [none] bits outputPadding ]) := by
  simpa [loweredStructuredBoolWordRawBitsDecoderDescription] using
    Structured.MultiTapeLowering.lowerStructured3Description_haltsFromConfigWithTapes
      structuredBoolWordRawBitsDecoderDescription_wellFormed
      structuredBoolWordRawBitsDecoderDescription_haltTransitionFree
      structuredBoolWordRawBitsDecoderDescription_supportsReadWriteRows3
      (c :=
        { state := structuredBoolWordRawBitsDecoderDescription.start
          tapes :=
            [ boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding
            , Tape.blank
            , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
                bits.length outputPadding ] })
      (tapes :=
        [ structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail rightPadding
        , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
            (bits.length + 1)
        , rightEdgeScanSourceTapeFromLeft [none] bits outputPadding ])
      rfl
      (by simp [structuredBoolWordRawBitsDecoderDescription])
      ⟨9 * bits.length + 11,
        structuredBoolWordRawBitsDecoderDescription_run_withOutputPadding
          bits suffixTail rightPadding outputPadding⟩

def boolWordRawBitsDecoderHeaderBase : List (Option Bool) :=
  List.append (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none]

def boolWordRawBitsDecoderAfterHeaderTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells boolWordRawBitsDecoderHeaderBase
    (List.append ((boolWordRawBitsDecoderEncodedFieldBits bits).map some)
      (some false ::
        List.append (suffixTail.map some) (none :: rightPadding)))

def boolWordRawBitsDecoderPrefixHandoffTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  (boolWordCanonicalHandoffConfigWithBaseAndRight
    bits boolWordRawBitsDecoderHeaderBase
    (false :: suffixTail) (none :: rightPadding)).tape

def boolWordRawBitsDecoderPrefixScannerDescription :
    MachineDescription :=
  canonicalSeqDescription
    rightMoveAcrossFourBitsDescription
    BoolWordSuffixScannerDescription

theorem boolWordRawBitsDecoderPrefixScannerDescription_subroutineReady :
    boolWordRawBitsDecoderPrefixScannerDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    rightMoveAcrossFourBitsDescription_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady

theorem rightMoveAcrossFourBitsDescription_haltsFrom_rawBitsDecoderSource
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    rightMoveAcrossFourBitsDescription.HaltsFromTape
      (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
      (boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
        rightPadding) := by
  simpa [boolWordRawBitsDecoderSourceTape,
    boolWordRawBitsDecoderAfterHeaderTape,
    boolWordRawBitsDecoderHeaderBase,
    boolWordRawBitsDecoderHeaderBits,
    rightEdgeRewindTargetTape, encodeCodeSymbolAsInput,
    List.map_append, List.append_assoc] using
    rightMoveAcrossFourBitsDescription_haltsFromTape_bits
      false false false false [none]
      (List.append ((boolWordRawBitsDecoderEncodedFieldBits bits).map some)
        (some false ::
          List.append (suffixTail.map some) (none :: rightPadding)))

theorem boolWordRawBitsDecoderAfterHeaderTape_move_left_move_right
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
            rightPadding)) =
      boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
        rightPadding := by
  rcases stageNatBits_false_false_tail bits.length with
    ⟨stageTail, hstage⟩
  simp [boolWordRawBitsDecoderAfterHeaderTape,
    boolWordRawBitsDecoderEncodedFieldBits, hstage, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight, List.append_assoc]

theorem boolWordSuffixScannerDescription_haltsFrom_rawBitsDecoderAfterHeader
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    BoolWordSuffixScannerDescription.HaltsFromTape
      (boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
        rightPadding)
      (boolWordRawBitsDecoderPrefixHandoffTape bits suffixTail
        rightPadding) := by
  rcases
      run_boolWordSuffix_raw_to_canonical_handoff_withBaseAndRight
        bits boolWordRawBitsDecoderHeaderBase suffixTail
        (none :: rightPadding) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [boolWordRawBitsDecoderAfterHeaderTape,
      boolWordRawBitsDecoderPrefixHandoffTape,
      boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
      List.append_assoc] using
      congrArg Configuration.state hsteps
  · simpa [boolWordRawBitsDecoderAfterHeaderTape,
      boolWordRawBitsDecoderPrefixHandoffTape,
      boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
      List.append_assoc] using
      congrArg Configuration.tape hsteps

theorem boolWordRawBitsDecoderPrefixScannerDescription_haltsFromTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    boolWordRawBitsDecoderPrefixScannerDescription.HaltsFromTape
      (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
      (boolWordRawBitsDecoderPrefixHandoffTape bits suffixTail
        rightPadding) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightMoveAcrossFourBitsDescription_subroutineReady
      boolWordSuffixScannerDescription_subroutineReady
      (rightMoveAcrossFourBitsDescription_haltsFrom_rawBitsDecoderSource
        bits suffixTail rightPadding)
      (boolWordRawBitsDecoderAfterHeaderTape_move_left_move_right
        bits suffixTail rightPadding)
      (boolWordSuffixScannerDescription_haltsFrom_rawBitsDecoderAfterHeader
        bits suffixTail rightPadding)

end FiniteTransducers
end CommonGround

end Computability
end FoC
