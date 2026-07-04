import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.FixedSkips
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredPrimitives
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
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

def BoolWordCanonicalHandoffToRawScanSourceSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding : List (Option Bool)),
      materializer.HaltsFromTape
        (boolWordRawBitsDecoderPrefixHandoffTape
          bits suffixTail rightPadding)
        (boolWordRawBitsDecoderTargetTape
          bits suffixTail rightPadding)

def BoolWordCanonicalHandoffToRawScanSourceConstruction : Prop :=
  exists materializer : MachineDescription,
    BoolWordCanonicalHandoffToRawScanSourceSpec materializer

/--
Concrete table for the remaining materializer.

The first phase reads the restored Boolean-cell code on the left stack in the
reverse physical order produced by the canonical suffix scanner:

* {lit}`false,true,true,false` decodes a raw {lit}`true`;
* {lit}`true,false,true,false` decodes a raw {lit}`false`;
* {lit}`true,true,false,false` is the restored {name}`MachineCodeSymbol.done`
  marker and enters cleanup.

The cleanup phase erases the restored metadata/header scaffold and the final
phase is the local gap-closing pass intended to compact the decoded raw cells
toward the preserved boundary/suffix.  The run theorem below is the remaining
proof that this table realizes the exact tape contract for all canonical
inputs.
-/
def boolWordCanonicalHandoffToRawScanSourceMaterializerDescription :
    MachineDescription where
  stateCount := 80
  start := 0
  halt := 79
  transitions :=
    [ transition 0 (some false) none Direction.left 10
    , transition 0 (some true) none Direction.left 20
    , transition 0 none none Direction.right 40

    , transition 10 (some true) none Direction.left 11
    , transition 11 (some true) none Direction.left 12
    , transition 12 (some false) (some true) Direction.left 0

    , transition 20 (some false) none Direction.left 21
    , transition 21 (some true) none Direction.left 22
    , transition 22 (some false) (some false) Direction.left 0

    , transition 20 (some true) none Direction.left 30
    , transition 30 (some false) none Direction.left 31
    , transition 31 (some false) none Direction.left 40

    , transition 40 (some false) none Direction.left 40
    , transition 40 (some true) none Direction.left 40
    , transition 40 none none Direction.right 50

    , transition 50 none none Direction.right 50
    , transition 50 (some false) (some false) Direction.left 60
    , transition 50 (some true) (some true) Direction.left 60

    , transition 60 none none Direction.right 61
    , transition 61 (some false) none Direction.left 62
    , transition 61 (some true) none Direction.left 63
    , transition 61 none none Direction.left 79
    , transition 62 none (some false) Direction.right 64
    , transition 63 none (some true) Direction.right 64
    , transition 64 none none Direction.right 61
    ]

theorem boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_wellFormed :
    boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l :=
        boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.transitions)
      (stateCount :=
        boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l :=
        boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.transitions)
      (by decide)

theorem boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_haltTransitionFree :
    boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.transitions)
    (state :=
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.halt)
    (by decide)

theorem boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_subroutineReady :
    boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.SubroutineReady :=
  ⟨boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_wellFormed,
    boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_haltTransitionFree⟩

private abbrev boolWordRawBitsDecoderMaterializerTestMachine :
    MachineDescription :=
  boolWordCanonicalHandoffToRawScanSourceMaterializerDescription

private theorem boolWordRawBitsDecoderMaterializerRun_decodesFalseCell
    (right : List (Option Bool)) :
    boolWordRawBitsDecoderMaterializerTestMachine.runConfig 4
        { state := boolWordRawBitsDecoderMaterializerTestMachine.start
          tape := tapeAtCells
            [some false, some true, some false]
            (some true :: right) } =
      { state := boolWordRawBitsDecoderMaterializerTestMachine.start
        tape := tapeAtCells []
          (none :: some false :: none :: none :: none :: right) } := by
  cases right <;>
    simp [boolWordRawBitsDecoderMaterializerTestMachine,
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription,
      tapeAtCells, runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem boolWordRawBitsDecoderMaterializerRun_decodesTrueCell
    (right : List (Option Bool)) :
    boolWordRawBitsDecoderMaterializerTestMachine.runConfig 4
        { state := boolWordRawBitsDecoderMaterializerTestMachine.start
          tape := tapeAtCells
            [some true, some true, some false]
            (some false :: right) } =
      { state := boolWordRawBitsDecoderMaterializerTestMachine.start
        tape := tapeAtCells []
          (none :: some true :: none :: none :: none :: right) } := by
  cases right <;>
    simp [boolWordRawBitsDecoderMaterializerTestMachine,
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription,
      tapeAtCells, runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

private theorem boolWordRawBitsDecoderMaterializerRun_reachesCleanup
    (right : List (Option Bool)) :
    boolWordRawBitsDecoderMaterializerTestMachine.runConfig 4
        { state := boolWordRawBitsDecoderMaterializerTestMachine.start
          tape := tapeAtCells
            [some true, some false, some false]
            (some true :: right) } =
      { state := 40
        tape := tapeAtCells []
          (none :: none :: none :: none :: none :: right) } := by
  cases right <;>
    simp [boolWordRawBitsDecoderMaterializerTestMachine,
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription,
      tapeAtCells, runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

-- Exact handoff-to-target probes for these examples currently fail: the
-- cleanup phase reaches halt but leaves too many erased scaffold blanks.
private theorem boolWordRawBitsDecoderMaterializerRun_emptyWord_halts :
    (boolWordRawBitsDecoderMaterializerTestMachine.runConfig 50
        { state := boolWordRawBitsDecoderMaterializerTestMachine.start
          tape := boolWordRawBitsDecoderPrefixHandoffTape
            ([] : Word Bool) ([] : Word Bool) [] }).state =
      boolWordRawBitsDecoderMaterializerTestMachine.halt := by
  decide

private theorem boolWordRawBitsDecoderMaterializerRun_falseWord_halts :
    (boolWordRawBitsDecoderMaterializerTestMachine.runConfig 80
        { state := boolWordRawBitsDecoderMaterializerTestMachine.start
          tape := boolWordRawBitsDecoderPrefixHandoffTape
            ([false] : Word Bool) ([] : Word Bool) [] }).state =
      boolWordRawBitsDecoderMaterializerTestMachine.halt := by
  decide

private theorem boolWordRawBitsDecoderMaterializerRun_trueWord_halts :
    (boolWordRawBitsDecoderMaterializerTestMachine.runConfig 80
        { state := boolWordRawBitsDecoderMaterializerTestMachine.start
          tape := boolWordRawBitsDecoderPrefixHandoffTape
            ([true] : Word Bool) ([] : Word Bool) [] }).state =
      boolWordRawBitsDecoderMaterializerTestMachine.halt := by
  decide

private theorem boolWordRawBitsDecoderMaterializerRun_twoBitsWithSuffix_halts :
    (boolWordRawBitsDecoderMaterializerTestMachine.runConfig 120
        { state := boolWordRawBitsDecoderMaterializerTestMachine.start
          tape := boolWordRawBitsDecoderPrefixHandoffTape
            ([false, true] : Word Bool) ([true] : Word Bool) [none] }).state =
      boolWordRawBitsDecoderMaterializerTestMachine.halt := by
  decide

theorem boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_haltsFromTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.HaltsFromTape
      (boolWordRawBitsDecoderPrefixHandoffTape
        bits suffixTail rightPadding)
      (boolWordRawBitsDecoderTargetTape
        bits suffixTail rightPadding) := by
  sorry

/--
The concrete remaining finite-machine leaf.  The only unresolved proof is the
run theorem for
{name}`boolWordCanonicalHandoffToRawScanSourceMaterializerDescription`; the
existential no longer hides which table is intended.
-/
theorem boolWordCanonicalHandoffToRawScanSourceConstruction_core :
    BoolWordCanonicalHandoffToRawScanSourceConstruction := by
  exact
    ⟨boolWordCanonicalHandoffToRawScanSourceMaterializerDescription,
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_subroutineReady,
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_haltsFromTape⟩

private theorem dovetailTapeAtCells_move_left_move_right_move_left_append_cons
    (pref tail right : List (Option Bool)) (cell : Option Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells
              (List.append pref (cell :: tail)) right))) =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          (List.append pref (cell :: tail)) right) := by
  rw [show
      Tape.move Direction.right
          (Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells
              (List.append pref (cell :: tail)) right)) =
        DovetailInitialLayoutInitializer.tapeAtCells
          (List.append pref (cell :: tail)) right by
    simpa [DovetailInitialLayoutInitializer.tapeAtCells,
      tapeAtCells] using
      tapeAtCells_move_right_move_left_append_cons
        pref tail right cell]

theorem boolWordRawBitsDecoderPrefixHandoffTape_move_left_move_right
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (boolWordRawBitsDecoderPrefixHandoffTape bits suffixTail
            rightPadding)) =
      boolWordRawBitsDecoderPrefixHandoffTape bits suffixTail
        rightPadding := by
  simpa [boolWordRawBitsDecoderPrefixHandoffTape,
    boolWordCanonicalHandoffConfigWithBaseAndRight,
    cellListCanonicalHandoffConfigWithBaseAndRight,
    cellListCanonicalRestoredLeftWithBase,
    cellListCanonicalFinishStartLeftWithBase,
    boolWordRawBitsDecoderHeaderBase, boolWordRawBitsDecoderHeaderBits,
    encodeCodeSymbolAsInput, doneBits, List.append_assoc] using
    dovetailTapeAtCells_move_left_move_right_move_left_append_cons
      ((List.map some (cellsCodeBits (List.map some bits))).reverse)
      (some true :: some false :: some false ::
        List.append (cellListCanonicalLengthPrefixRev bits.length)
          boolWordRawBitsDecoderHeaderBase)
      (some false :: List.append (suffixTail.map some)
        (none :: rightPadding))
      (some true)

/--
The finite-machine leaf for the honest Boolean-word decoder.  It decodes the
header-prefixed encoded field and preserves the suffix/right-padding shape
specified above.
-/
theorem boolWordRawBitsDecoderConstruction_core :
    BoolWordRawBitsDecoderConstruction := by
  rcases boolWordCanonicalHandoffToRawScanSourceConstruction_core with
    ⟨materializer, hmaterializer⟩
  refine
    ⟨canonicalSeqDescription
      boolWordRawBitsDecoderPrefixScannerDescription
      materializer, ?_⟩
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        boolWordRawBitsDecoderPrefixScannerDescription_subroutineReady
        hmaterializer.left
  · intro bits suffixTail rightPadding
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        boolWordRawBitsDecoderPrefixScannerDescription_subroutineReady
        hmaterializer.left
        (boolWordRawBitsDecoderPrefixScannerDescription_haltsFromTape
          bits suffixTail rightPadding)
        (boolWordRawBitsDecoderPrefixHandoffTape_move_left_move_right
          bits suffixTail rightPadding)
        (hmaterializer.right bits suffixTail rightPadding)

end FiniteTransducers
end CommonGround

end Computability
end FoC
