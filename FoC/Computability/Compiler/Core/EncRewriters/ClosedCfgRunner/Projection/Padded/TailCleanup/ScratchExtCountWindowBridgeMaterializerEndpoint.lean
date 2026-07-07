import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoderInputMaterializerEndpoint
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge

set_option doc.verso true

/-!
# Count-window structured input materializer endpoint facts

This module specializes the generic and bool-word input materializer endpoint
facts to the count-window decoded-prefix bridge.  The remaining finite-machine
leaf in `ScratchExtCountWindowBridge.lean` can use these names for the exact
source, output-buffer, guarded structured target, separator positions, and
head-cell positions without unfolding the count-window layout or the generic
structured encoding in every branch.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

namespace CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpoint

/-!
## Named count-window input families
-/

def bits
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Word Bool :=
  countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
    useAccept input

def suffixTail
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Word Bool :=
  countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
    useAccept input

def sourcePadding
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : List (Option Bool) :=
  countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
    useAccept input

def outputPadding
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : List (Option Bool) :=
  countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
    useAccept input

def inputSource
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
    useAccept input

def boolWordSource
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
    useAccept input

def outputTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
    useAccept input

def encodedInputTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
    useAccept input.L input.pref input.leftBit input.deletedTail

def inputTarget
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.targetTape
    (inputSource useAccept input)
    (outputTape useAccept input)

def boolWordTarget
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedTarget
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
      useAccept)
    input

def logicalTapes
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : List (Tape Bool) :=
  StructuredInputMaterializerEndpoint.logicalTapes
    (inputSource useAccept input)
    (outputTape useAccept input)

def guardedLogicalTapes
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : List (Tape Bool) :=
  StructuredInputMaterializerEndpoint.guardedLogicalTapes
    (inputSource useAccept input)
    (outputTape useAccept input)

def guardedInputSourceTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.guardedSourceTape
    (inputSource useAccept input)

def guardedBoolWordSourceTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedGuardedSourceTape
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
      useAccept)
    (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
      useAccept)
    input

def guardedOutputTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.guardedOutputTape
    (outputTape useAccept input)

def guardedScratchTape : Tape Bool :=
  StructuredInputMaterializerEndpoint.guardedScratchTape

def separator0Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.separator0Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def separator1Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.separator1Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def separator2Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.separator2Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def headMarker0Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headMarker0Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def headMarker1Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headMarker1Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def headMarker2Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headMarker2Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def headCell0Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headCell0Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def headCell1Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headCell1Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def headCell2Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headCell2Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def segmentEnd0Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.segmentEnd0Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def segmentEnd1Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.segmentEnd1Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

def segmentEnd2Tape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) : Tape Bool :=
  StructuredInputMaterializerEndpoint.segmentEnd2Tape
    (inputSource useAccept input)
    (outputTape useAccept input)

/-!
## Source and target equalities
-/

theorem bits_eq
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    bits useAccept input = ParsedLayoutBits input.L := by
  rfl

theorem suffixTail_eq
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    suffixTail useAccept input =
      countWindowPostFieldDecodedPrefixStructuredSuffixTail
        useAccept input.L := by
  rfl

theorem sourcePadding_eq
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    sourcePadding useAccept input =
      countWindowPostFieldDecodedPrefixStructuredSourcePadding
        useAccept input.L input.deletedTail := by
  rfl

theorem outputPadding_eq
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    outputPadding useAccept input =
      postFieldDecodedPrefixScanPadding useAccept input.L := by
  rfl

theorem inputSource_eq
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    inputSource useAccept input =
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource
        useAccept input := by
  rfl

theorem boolWordSource_eq
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    boolWordSource useAccept input =
      countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
        useAccept input := by
  rfl

theorem outputTape_eq
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    outputTape useAccept input =
      countWindowPostFieldDecodedPrefixStructuredInputMaterializerOutputTape
        useAccept input := by
  rfl

theorem encodedInputTape_eq
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    encodedInputTape useAccept input =
      countWindowPostFieldDecodedPrefixStructuredEncodedInputTape
        useAccept input.L input.pref input.leftBit input.deletedTail := by
  rfl

theorem inputSource_eq_boolWordSource
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    inputSource useAccept input = boolWordSource useAccept input := by
  simpa [inputSource, boolWordSource] using
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource_eq_boolWordSource
      useAccept input

theorem boolWordSource_eq_indexedSource
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    boolWordSource useAccept input =
      BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedSource
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
          useAccept)
        input := by
  rfl

theorem outputTape_eq_indexedOutput
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    outputTape useAccept input =
      BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedOutput
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
          useAccept)
        input := by
  rfl

theorem inputTarget_eq_materializerTargetTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    inputTarget useAccept input =
      structured3InputMaterializerTargetTape
        (inputSource useAccept input)
        (outputTape useAccept input) := by
  rfl

theorem inputTarget_eq_encodedInputTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    inputTarget useAccept input = encodedInputTape useAccept input := by
  symm
  simpa [inputTarget, inputSource, outputTape, encodedInputTape,
    StructuredInputMaterializerEndpoint.targetTape] using
    countWindowPostFieldDecodedPrefixStructuredEncodedInputTape_eq_inputMaterializerTargetTape
      useAccept input

theorem boolWordTarget_eq_indexedTarget
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    boolWordTarget useAccept input =
      BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedTarget
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
          useAccept)
        input := by
  rfl

theorem boolWordTarget_eq_namedIndexedTargetTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    boolWordTarget useAccept input =
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
          useAccept)
        input := by
  exact
    BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedTarget_eq_namedTargetTape
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
          useAccept)
        (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
          useAccept)
        input

theorem boolWordTarget_eq_inputTarget
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    boolWordTarget useAccept input = inputTarget useAccept input := by
  rw [boolWordTarget_eq_namedIndexedTargetTape]
  rw [
    countWindowPostFieldDecodedPrefixStructuredBoolWordIndexedTargetTape_eq_materializerTargetTape]
  simp [inputTarget, inputSource, outputTape,
    StructuredInputMaterializerEndpoint.targetTape,
    countWindowPostFieldDecodedPrefixStructuredInputMaterializerSource_eq_boolWordSource]

theorem boolWordTarget_eq_encodedInputTape
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    boolWordTarget useAccept input = encodedInputTape useAccept input := by
  rw [boolWordTarget_eq_inputTarget, inputTarget_eq_encodedInputTape]

/-!
## Tape cells and normalized output
-/

theorem boolWordSource_cells
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.cells (boolWordSource useAccept input) =
      none ::
        List.append
          ((List.append boolWordRawBitsDecoderHeaderBits
            (List.append
              (boolWordRawBitsDecoderEncodedFieldBits
                (bits useAccept input))
              (false :: suffixTail useAccept input))).map some)
          (none :: sourcePadding useAccept input) := by
  simpa [boolWordSource, bits, suffixTail, sourcePadding] using
    BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedSource_cells
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
        useAccept)
      input

theorem inputSource_cells
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.cells (inputSource useAccept input) =
      none ::
        List.append
          ((List.append boolWordRawBitsDecoderHeaderBits
            (List.append
              (boolWordRawBitsDecoderEncodedFieldBits
                (bits useAccept input))
              (false :: suffixTail useAccept input))).map some)
          (none :: sourcePadding useAccept input) := by
  rw [inputSource_eq_boolWordSource]
  exact boolWordSource_cells useAccept input

theorem outputTape_cells
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.cells (outputTape useAccept input) =
      none ::
        List.append
          (List.replicate ((bits useAccept input).length + 1)
            (none : Option Bool))
          (outputPadding useAccept input) := by
  simpa [outputTape, bits, outputPadding] using
    BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedOutput_cells
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordOutputPadding
        useAccept)
      input

theorem inputTarget_read
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.read (inputTarget useAccept input) = none := by
  simpa [inputTarget, inputSource, outputTape] using
    StructuredInputMaterializerEndpoint.targetTape_read
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem boolWordTarget_read
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.read (boolWordTarget useAccept input) = none := by
  rw [boolWordTarget_eq_inputTarget]
  exact inputTarget_read useAccept input

theorem encodedInputTape_read
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.read (encodedInputTape useAccept input) = none := by
  rw [← inputTarget_eq_encodedInputTape]
  exact inputTarget_read useAccept input

theorem inputTarget_cells
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.cells (inputTarget useAccept input) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode
            (guardLogicalTape (inputSource useAccept input)))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode
                (guardLogicalTape Tape.blank))
              (List.append tapeSeparatorCells
                (List.append (logicalTapeCode
                    (guardLogicalTape (outputTape useAccept input)))
                  tapeSeparatorCells))))) := by
  simpa [inputTarget, inputSource, outputTape] using
    StructuredInputMaterializerEndpoint.targetTape_cells
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem boolWordTarget_cells
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.cells (boolWordTarget useAccept input) =
      Tape.cells (inputTarget useAccept input) := by
  rw [boolWordTarget_eq_inputTarget]

theorem encodedInputTape_cells
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.cells (encodedInputTape useAccept input) =
      Tape.cells (inputTarget useAccept input) := by
  rw [← inputTarget_eq_encodedInputTape]

theorem inputTarget_normalizedOutput_eq_guardedLogicalBits
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.normalizedOutput (inputTarget useAccept input) =
      List.append
        (logicalTapeBits (guardedInputSourceTape useAccept input))
        (List.append
          (logicalTapeBits guardedScratchTape)
          (logicalTapeBits (guardedOutputTape useAccept input))) := by
  simpa [inputTarget, inputSource, outputTape, guardedInputSourceTape,
    guardedScratchTape, guardedOutputTape] using
    StructuredInputMaterializerEndpoint.targetTape_normalizedOutput_eq_guardedLogicalBits
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem boolWordTarget_normalizedOutput_eq_inputTarget
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.normalizedOutput (boolWordTarget useAccept input) =
      Tape.normalizedOutput (inputTarget useAccept input) := by
  rw [boolWordTarget_eq_inputTarget]

theorem encodedInputTape_normalizedOutput_eq_inputTarget
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.normalizedOutput (encodedInputTape useAccept input) =
      Tape.normalizedOutput (inputTarget useAccept input) := by
  rw [← inputTarget_eq_encodedInputTape]

/-!
## Guarded structured endpoint predicates
-/

theorem logicalTapes_eq
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    logicalTapes useAccept input =
      [inputSource useAccept input, Tape.blank, outputTape useAccept input] := by
  rfl

theorem guardedLogicalTapes_eq
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    guardedLogicalTapes useAccept input =
      [guardedInputSourceTape useAccept input,
        guardedScratchTape,
        guardedOutputTape useAccept input] := by
  rfl

@[simp] theorem logicalTapes_length
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    (logicalTapes useAccept input).length = 3 := by
  rfl

@[simp] theorem guardedLogicalTapes_length
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    (guardedLogicalTapes useAccept input).length = 3 := by
  rfl

theorem guardedInputSourceTape_equiv
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.Equiv
      (guardedInputSourceTape useAccept input)
      (inputSource useAccept input) := by
  exact
    StructuredInputMaterializerEndpoint.guardedSourceTape_equiv
      (inputSource useAccept input)

theorem guardedBoolWordSourceTape_equiv
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.Equiv
      (guardedBoolWordSourceTape useAccept input)
      (boolWordSource useAccept input) := by
  exact
    BoolWordRawBitsDecoderInputMaterializerEndpoint.indexedGuardedSourceTape_equiv
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordBits
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSuffixTail
        useAccept)
      (countWindowPostFieldDecodedPrefixStructuredIndexedBoolWordSourcePadding
        useAccept)
      input

theorem guardedOutputTape_equiv
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    Tape.Equiv
      (guardedOutputTape useAccept input)
      (outputTape useAccept input) := by
  exact
    StructuredInputMaterializerEndpoint.guardedOutputTape_equiv
      (outputTape useAccept input)

theorem guardedScratchTape_equiv :
    Tape.Equiv guardedScratchTape Tape.blank := by
  exact StructuredInputMaterializerEndpoint.guardedScratchTape_equiv

theorem guardedLogicalTapes_haveGuardCells
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    LogicalTapesHaveGuardCells (guardedLogicalTapes useAccept input) := by
  exact
    StructuredInputMaterializerEndpoint.guardedLogicalTapes_haveGuardCells
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem inputTarget_structuredEncodedTapes
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    StructuredEncodedTapes
      (guardedLogicalTapes useAccept input)
      (inputTarget useAccept input) := by
  simpa [inputTarget, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.targetTape_structuredEncodedTapes_guarded
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem inputTarget_structuredGuardedEncodedTapes
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    StructuredGuardedEncodedTapes
      (logicalTapes useAccept input)
      (inputTarget useAccept input) := by
  simpa [inputTarget, inputSource, outputTape, logicalTapes] using
    StructuredInputMaterializerEndpoint.targetTape_structuredGuardedEncodedTapes
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem inputTarget_structuredLogicalEquivEncodedTapes
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    StructuredLogicalEquivEncodedTapes
      (logicalTapes useAccept input)
      (inputTarget useAccept input) := by
  simpa [inputTarget, inputSource, outputTape, logicalTapes] using
    StructuredInputMaterializerEndpoint.targetTape_structuredLogicalEquivEncodedTapes
      (inputSource useAccept input)
      (outputTape useAccept input)

/-!
## Separator and cursor endpoints
-/

theorem atSeparator0
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeSeparator
      (guardedLogicalTapes useAccept input) 0
      (inputTarget useAccept input) := by
  simpa [inputTarget, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSeparator0
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atSeparator1
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeSeparator
      (guardedLogicalTapes useAccept input) 1
      (separator1Tape useAccept input) := by
  simpa [separator1Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSeparator1
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atSeparator2
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeSeparator
      (guardedLogicalTapes useAccept input) 2
      (separator2Tape useAccept input) := by
  simpa [separator2Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSeparator2
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atExistingSeparator0
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtExistingTapeSeparator
      (guardedLogicalTapes useAccept input) 0
      (inputTarget useAccept input) := by
  simpa [inputTarget, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atExistingSeparator0
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atExistingSeparator1
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtExistingTapeSeparator
      (guardedLogicalTapes useAccept input) 1
      (separator1Tape useAccept input) := by
  simpa [separator1Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atExistingSeparator1
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atExistingSeparator2
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtExistingTapeSeparator
      (guardedLogicalTapes useAccept input) 2
      (separator2Tape useAccept input) := by
  simpa [separator2Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atExistingSeparator2
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atHeadMarker0
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeHeadMarker
      (guardedLogicalTapes useAccept input) 0
      (headMarker0Tape useAccept input) := by
  simpa [headMarker0Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadMarker0
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atHeadMarker1
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeHeadMarker
      (guardedLogicalTapes useAccept input) 1
      (headMarker1Tape useAccept input) := by
  simpa [headMarker1Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadMarker1
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atHeadMarker2
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeHeadMarker
      (guardedLogicalTapes useAccept input) 2
      (headMarker2Tape useAccept input) := by
  simpa [headMarker2Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadMarker2
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atHeadCell0
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeHeadCellCode
      (guardedLogicalTapes useAccept input) 0
      (headCell0Tape useAccept input) := by
  simpa [headCell0Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadCell0
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atHeadCell1
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeHeadCellCode
      (guardedLogicalTapes useAccept input) 1
      (headCell1Tape useAccept input) := by
  simpa [headCell1Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadCell1
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atHeadCell2
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeHeadCellCode
      (guardedLogicalTapes useAccept input) 2
      (headCell2Tape useAccept input) := by
  simpa [headCell2Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadCell2
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atSegmentEnd0
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeSegmentEnd
      (guardedLogicalTapes useAccept input) 0
      (segmentEnd0Tape useAccept input) := by
  simpa [segmentEnd0Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSegmentEnd0
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atSegmentEnd1
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeSegmentEnd
      (guardedLogicalTapes useAccept input) 1
      (segmentEnd1Tape useAccept input) := by
  simpa [segmentEnd1Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSegmentEnd1
      (inputSource useAccept input)
      (outputTape useAccept input)

theorem atSegmentEnd2
    (useAccept : Bool)
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput
        useAccept) :
    AtTapeSegmentEnd
      (guardedLogicalTapes useAccept input) 2
      (segmentEnd2Tape useAccept input) := by
  simpa [segmentEnd2Tape, inputSource, outputTape, guardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSegmentEnd2
      (inputSource useAccept input)
      (outputTape useAccept input)

end CountWindowPostFieldDecodedPrefixStructuredMaterializerEndpoint

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
