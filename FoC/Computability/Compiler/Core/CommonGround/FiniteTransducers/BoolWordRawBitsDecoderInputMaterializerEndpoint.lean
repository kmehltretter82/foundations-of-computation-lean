import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoder
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializerEndpoint

set_option doc.verso true

/-!
# Bool-word raw-bits input materializer endpoint facts

This module specializes the generic three-logical-tape input materializer
endpoint facts to the Boolean-word raw-bits decoder source families.  It keeps
the facts construction-free: downstream count-window and decoder bridge proofs
can use these named endpoint positions without repeatedly unfolding the
guarded structured encoding.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner

namespace CommonGround
namespace FiniteTransducers

namespace BoolWordRawBitsDecoderInputMaterializerEndpoint

open Structured.MultiTapeLowering

/-!
## Canonical source family
-/

def canonicalSource
    (bits suffixTail : Word Bool) : Tape Bool :=
  structuredBoolWordRawBitsDecoderCanonicalSourceTape bits suffixTail

def canonicalOutput
    (bits suffixTail : Word Bool) : Tape Bool :=
  structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
    (bits, suffixTail)

def canonicalTarget
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.targetTape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalLogicalTapes
    (bits suffixTail : Word Bool) : List (Tape Bool) :=
  StructuredInputMaterializerEndpoint.logicalTapes
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalGuardedLogicalTapes
    (bits suffixTail : Word Bool) : List (Tape Bool) :=
  StructuredInputMaterializerEndpoint.guardedLogicalTapes
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalGuardedSourceTape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.guardedSourceTape
    (canonicalSource bits suffixTail)

def canonicalGuardedScratchTape : Tape Bool :=
  StructuredInputMaterializerEndpoint.guardedScratchTape

def canonicalGuardedOutputTape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.guardedOutputTape
    (canonicalOutput bits suffixTail)

def canonicalSeparator0Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.separator0Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalSeparator1Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.separator1Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalSeparator2Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.separator2Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalHeadMarker0Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headMarker0Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalHeadMarker1Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headMarker1Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalHeadMarker2Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headMarker2Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalHeadCell0Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headCell0Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalHeadCell1Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headCell1Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalHeadCell2Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headCell2Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalSegmentEnd0Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.segmentEnd0Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalSegmentEnd1Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.segmentEnd1Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

def canonicalSegmentEnd2Tape
    (bits suffixTail : Word Bool) : Tape Bool :=
  StructuredInputMaterializerEndpoint.segmentEnd2Tape
    (canonicalSource bits suffixTail)
    (canonicalOutput bits suffixTail)

theorem canonicalSource_eq
    (bits suffixTail : Word Bool) :
    canonicalSource bits suffixTail =
      structuredBoolWordRawBitsDecoderCanonicalSourceTape bits suffixTail := by
  rfl

theorem canonicalOutput_eq
    (bits suffixTail : Word Bool) :
    canonicalOutput bits suffixTail =
      structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
        (bits, suffixTail) := by
  rfl

theorem canonicalOutput_eq_initialOutputTape
    (bits suffixTail : Word Bool) :
    canonicalOutput bits suffixTail =
      structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
        bits.length
        (boolWordRawBitsDecoderPreservedPadding suffixTail []) := by
  rfl

theorem canonicalTarget_eq_initializerTargetTape
    (bits suffixTail : Word Bool) :
    canonicalTarget bits suffixTail =
      structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
        bits suffixTail := by
  symm
  simpa [canonicalTarget, canonicalSource, canonicalOutput,
    StructuredInputMaterializerEndpoint.targetTape] using
    structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape_eq_materializerTargetTape
      bits suffixTail

theorem canonicalTarget_eq_materializerTargetTape
    (bits suffixTail : Word Bool) :
    canonicalTarget bits suffixTail =
      structured3InputMaterializerTargetTape
        (canonicalSource bits suffixTail)
        (canonicalOutput bits suffixTail) := by
  rfl

theorem canonicalLogicalTapes_eq
    (bits suffixTail : Word Bool) :
    canonicalLogicalTapes bits suffixTail =
      [canonicalSource bits suffixTail, Tape.blank,
        canonicalOutput bits suffixTail] := by
  rfl

theorem canonicalGuardedLogicalTapes_eq
    (bits suffixTail : Word Bool) :
    canonicalGuardedLogicalTapes bits suffixTail =
      [canonicalGuardedSourceTape bits suffixTail,
        canonicalGuardedScratchTape,
        canonicalGuardedOutputTape bits suffixTail] := by
  rfl

@[simp] theorem canonicalLogicalTapes_length
    (bits suffixTail : Word Bool) :
    (canonicalLogicalTapes bits suffixTail).length = 3 := by
  rfl

@[simp] theorem canonicalGuardedLogicalTapes_length
    (bits suffixTail : Word Bool) :
    (canonicalGuardedLogicalTapes bits suffixTail).length = 3 := by
  rfl

theorem canonicalLogicalTapes_zero
    (bits suffixTail : Word Bool) :
    (canonicalLogicalTapes bits suffixTail)[0]? =
      some (canonicalSource bits suffixTail) := by
  rfl

theorem canonicalLogicalTapes_one
    (bits suffixTail : Word Bool) :
    (canonicalLogicalTapes bits suffixTail)[1]? = some Tape.blank := by
  rfl

theorem canonicalLogicalTapes_two
    (bits suffixTail : Word Bool) :
    (canonicalLogicalTapes bits suffixTail)[2]? =
      some (canonicalOutput bits suffixTail) := by
  rfl

theorem canonicalGuardedLogicalTapes_zero
    (bits suffixTail : Word Bool) :
    (canonicalGuardedLogicalTapes bits suffixTail)[0]? =
      some (canonicalGuardedSourceTape bits suffixTail) := by
  rfl

theorem canonicalGuardedLogicalTapes_one
    (bits suffixTail : Word Bool) :
    (canonicalGuardedLogicalTapes bits suffixTail)[1]? =
      some canonicalGuardedScratchTape := by
  rfl

theorem canonicalGuardedLogicalTapes_two
    (bits suffixTail : Word Bool) :
    (canonicalGuardedLogicalTapes bits suffixTail)[2]? =
      some (canonicalGuardedOutputTape bits suffixTail) := by
  rfl

theorem canonicalSource_cells
    (bits suffixTail : Word Bool) :
    Tape.cells (canonicalSource bits suffixTail) =
      none ::
        List.append
          ((List.append boolWordRawBitsDecoderHeaderBits
            (List.append
              (boolWordRawBitsDecoderEncodedFieldBits bits)
              (false :: suffixTail))).map some)
          [none] := by
  simpa [canonicalSource] using
    structuredBoolWordRawBitsDecoderCanonicalSourceTape_cells
      bits suffixTail

theorem canonicalOutput_cells
    (bits suffixTail : Word Bool) :
    Tape.cells (canonicalOutput bits suffixTail) =
      none ::
        List.append
          (List.replicate (bits.length + 1) (none : Option Bool))
          (List.append ((false :: suffixTail).map some) [none]) := by
  simpa [canonicalOutput, canonicalOutput_eq_initialOutputTape,
    boolWordRawBitsDecoderPreservedPadding] using
    structuredBoolWordRawBitsDecoderCanonicalInitialOutputTape_cells
      bits suffixTail

theorem canonicalTarget_read
    (bits suffixTail : Word Bool) :
    Tape.read (canonicalTarget bits suffixTail) = none := by
  simpa [canonicalTarget, canonicalSource, canonicalOutput] using
    StructuredInputMaterializerEndpoint.targetTape_read
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalTarget_cells
    (bits suffixTail : Word Bool) :
    Tape.cells (canonicalTarget bits suffixTail) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode
            (guardLogicalTape (canonicalSource bits suffixTail)))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode
                (guardLogicalTape Tape.blank))
              (List.append tapeSeparatorCells
                (List.append (logicalTapeCode
                    (guardLogicalTape
                      (canonicalOutput bits suffixTail)))
                  tapeSeparatorCells))))) := by
  simpa [canonicalTarget, canonicalSource, canonicalOutput] using
    StructuredInputMaterializerEndpoint.targetTape_cells
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalTarget_cells_via_initializerTargetTape
    (bits suffixTail : Word Bool) :
    Tape.cells
        (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
          bits suffixTail) =
      Tape.cells (canonicalTarget bits suffixTail) := by
  rw [canonicalTarget_eq_initializerTargetTape]

theorem canonicalTarget_normalizedOutput_eq_guardedLogicalBits
    (bits suffixTail : Word Bool) :
    Tape.normalizedOutput (canonicalTarget bits suffixTail) =
      List.append
        (logicalTapeBits (canonicalGuardedSourceTape bits suffixTail))
        (List.append
          (logicalTapeBits canonicalGuardedScratchTape)
          (logicalTapeBits
            (canonicalGuardedOutputTape bits suffixTail))) := by
  simpa [canonicalTarget, canonicalSource, canonicalOutput,
    canonicalGuardedSourceTape, canonicalGuardedScratchTape,
    canonicalGuardedOutputTape] using
    StructuredInputMaterializerEndpoint.targetTape_normalizedOutput_eq_guardedLogicalBits
        (canonicalSource bits suffixTail)
        (canonicalOutput bits suffixTail)

theorem canonicalTarget_normalizedOutput_eq_initializerTargetTape
    (bits suffixTail : Word Bool) :
    Tape.normalizedOutput (canonicalTarget bits suffixTail) =
      Tape.normalizedOutput
        (structuredBoolWordRawBitsDecoderCanonicalInputInitializerTargetTape
          bits suffixTail) := by
  rw [canonicalTarget_eq_initializerTargetTape]

theorem canonicalTarget_structuredEncodedTapes
    (bits suffixTail : Word Bool) :
    StructuredEncodedTapes
      (canonicalGuardedLogicalTapes bits suffixTail)
      (canonicalTarget bits suffixTail) := by
  simpa [canonicalTarget, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.targetTape_structuredEncodedTapes_guarded
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalTarget_structuredGuardedEncodedTapes
    (bits suffixTail : Word Bool) :
    StructuredGuardedEncodedTapes
      (canonicalLogicalTapes bits suffixTail)
      (canonicalTarget bits suffixTail) := by
  simpa [canonicalTarget, canonicalSource, canonicalOutput,
    canonicalLogicalTapes] using
    StructuredInputMaterializerEndpoint.targetTape_structuredGuardedEncodedTapes
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalTarget_structuredLogicalEquivEncodedTapes
    (bits suffixTail : Word Bool) :
    StructuredLogicalEquivEncodedTapes
      (canonicalLogicalTapes bits suffixTail)
      (canonicalTarget bits suffixTail) := by
  simpa [canonicalTarget, canonicalSource, canonicalOutput,
    canonicalLogicalTapes] using
    StructuredInputMaterializerEndpoint.targetTape_structuredLogicalEquivEncodedTapes
        (canonicalSource bits suffixTail)
        (canonicalOutput bits suffixTail)

theorem canonicalGuardedSourceTape_equiv
    (bits suffixTail : Word Bool) :
    Tape.Equiv
      (canonicalGuardedSourceTape bits suffixTail)
      (canonicalSource bits suffixTail) := by
  exact
    StructuredInputMaterializerEndpoint.guardedSourceTape_equiv
      (canonicalSource bits suffixTail)

theorem canonicalGuardedScratchTape_equiv :
    Tape.Equiv canonicalGuardedScratchTape Tape.blank := by
  exact StructuredInputMaterializerEndpoint.guardedScratchTape_equiv

theorem canonicalGuardedOutputTape_equiv
    (bits suffixTail : Word Bool) :
    Tape.Equiv
      (canonicalGuardedOutputTape bits suffixTail)
      (canonicalOutput bits suffixTail) := by
  exact
    StructuredInputMaterializerEndpoint.guardedOutputTape_equiv
      (canonicalOutput bits suffixTail)

theorem canonicalGuardedLogicalTapes_haveGuardCells
    (bits suffixTail : Word Bool) :
    LogicalTapesHaveGuardCells
      (canonicalGuardedLogicalTapes bits suffixTail) := by
  exact
    StructuredInputMaterializerEndpoint.guardedLogicalTapes_haveGuardCells
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtSeparator0
    (bits suffixTail : Word Bool) :
    AtTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalTarget bits suffixTail) := by
  simpa [canonicalTarget, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSeparator0
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtSeparator1
    (bits suffixTail : Word Bool) :
    AtTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 1
      (canonicalSeparator1Tape bits suffixTail) := by
  simpa [canonicalSeparator1Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSeparator1
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtSeparator2
    (bits suffixTail : Word Bool) :
    AtTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalSeparator2Tape bits suffixTail) := by
  simpa [canonicalSeparator2Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSeparator2
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtExistingSeparator0
    (bits suffixTail : Word Bool) :
    AtExistingTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalTarget bits suffixTail) := by
  simpa [canonicalTarget, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atExistingSeparator0
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtExistingSeparator1
    (bits suffixTail : Word Bool) :
    AtExistingTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 1
      (canonicalSeparator1Tape bits suffixTail) := by
  simpa [canonicalSeparator1Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atExistingSeparator1
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtExistingSeparator2
    (bits suffixTail : Word Bool) :
    AtExistingTapeSeparator
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalSeparator2Tape bits suffixTail) := by
  simpa [canonicalSeparator2Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atExistingSeparator2
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtHeadMarker0
    (bits suffixTail : Word Bool) :
    AtTapeHeadMarker
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalHeadMarker0Tape bits suffixTail) := by
  simpa [canonicalHeadMarker0Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadMarker0
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtHeadMarker1
    (bits suffixTail : Word Bool) :
    AtTapeHeadMarker
      (canonicalGuardedLogicalTapes bits suffixTail) 1
      (canonicalHeadMarker1Tape bits suffixTail) := by
  simpa [canonicalHeadMarker1Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadMarker1
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtHeadMarker2
    (bits suffixTail : Word Bool) :
    AtTapeHeadMarker
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalHeadMarker2Tape bits suffixTail) := by
  simpa [canonicalHeadMarker2Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadMarker2
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtHeadCell0
    (bits suffixTail : Word Bool) :
    AtTapeHeadCellCode
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalHeadCell0Tape bits suffixTail) := by
  simpa [canonicalHeadCell0Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadCell0
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtHeadCell1
    (bits suffixTail : Word Bool) :
    AtTapeHeadCellCode
      (canonicalGuardedLogicalTapes bits suffixTail) 1
      (canonicalHeadCell1Tape bits suffixTail) := by
  simpa [canonicalHeadCell1Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadCell1
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtHeadCell2
    (bits suffixTail : Word Bool) :
    AtTapeHeadCellCode
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalHeadCell2Tape bits suffixTail) := by
  simpa [canonicalHeadCell2Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadCell2
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtSegmentEnd0
    (bits suffixTail : Word Bool) :
    AtTapeSegmentEnd
      (canonicalGuardedLogicalTapes bits suffixTail) 0
      (canonicalSegmentEnd0Tape bits suffixTail) := by
  simpa [canonicalSegmentEnd0Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSegmentEnd0
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtSegmentEnd1
    (bits suffixTail : Word Bool) :
    AtTapeSegmentEnd
      (canonicalGuardedLogicalTapes bits suffixTail) 1
      (canonicalSegmentEnd1Tape bits suffixTail) := by
  simpa [canonicalSegmentEnd1Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSegmentEnd1
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

theorem canonicalAtSegmentEnd2
    (bits suffixTail : Word Bool) :
    AtTapeSegmentEnd
      (canonicalGuardedLogicalTapes bits suffixTail) 2
      (canonicalSegmentEnd2Tape bits suffixTail) := by
  simpa [canonicalSegmentEnd2Tape, canonicalSource, canonicalOutput,
    canonicalGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSegmentEnd2
      (canonicalSource bits suffixTail)
      (canonicalOutput bits suffixTail)

/-!
## Indexed source family
-/

def indexedSource
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
    bits suffixTail rightPadding input

def indexedOutput
    {ι : Type}
    (bits : ι -> Word Bool)
    (outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
    bits outputPadding input

def indexedTarget
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.targetTape
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedLogicalTapes
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : List (Tape Bool) :=
  StructuredInputMaterializerEndpoint.logicalTapes
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedGuardedLogicalTapes
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : List (Tape Bool) :=
  StructuredInputMaterializerEndpoint.guardedLogicalTapes
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedGuardedSourceTape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.guardedSourceTape
    (indexedSource bits suffixTail rightPadding input)

def indexedGuardedOutputTape
    {ι : Type}
    (bits : ι -> Word Bool)
    (outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.guardedOutputTape
    (indexedOutput bits outputPadding input)

def indexedSeparator0Tape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.separator0Tape
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedSeparator1Tape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.separator1Tape
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedSeparator2Tape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.separator2Tape
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedHeadCell0Tape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headCell0Tape
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedHeadCell1Tape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headCell1Tape
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedHeadCell2Tape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.headCell2Tape
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedSegmentEnd0Tape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.segmentEnd0Tape
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedSegmentEnd1Tape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.segmentEnd1Tape
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

def indexedSegmentEnd2Tape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) : Tape Bool :=
  StructuredInputMaterializerEndpoint.segmentEnd2Tape
    (indexedSource bits suffixTail rightPadding input)
    (indexedOutput bits outputPadding input)

theorem indexedSource_eq
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding : ι -> List (Option Bool))
    (input : ι) :
    indexedSource bits suffixTail rightPadding input =
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource
        bits suffixTail rightPadding input := by
  rfl

theorem indexedOutput_eq
    {ι : Type}
    (bits : ι -> Word Bool)
    (outputPadding : ι -> List (Option Bool))
    (input : ι) :
    indexedOutput bits outputPadding input =
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape
        bits outputPadding input := by
  rfl

theorem indexedTarget_eq_namedTargetTape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    indexedTarget bits suffixTail rightPadding outputPadding input =
      structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
        bits suffixTail rightPadding outputPadding input := by
  symm
  simpa [indexedTarget, indexedSource, indexedOutput,
    StructuredInputMaterializerEndpoint.targetTape] using
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape_eq_materializerTargetTape
      bits suffixTail rightPadding outputPadding input

theorem indexedTarget_eq_materializerTargetTape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    indexedTarget bits suffixTail rightPadding outputPadding input =
      structured3InputMaterializerTargetTape
        (indexedSource bits suffixTail rightPadding input)
        (indexedOutput bits outputPadding input) := by
  rfl

theorem indexedLogicalTapes_eq
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    indexedLogicalTapes bits suffixTail rightPadding outputPadding input =
      [indexedSource bits suffixTail rightPadding input,
        Tape.blank,
        indexedOutput bits outputPadding input] := by
  rfl

theorem indexedGuardedLogicalTapes_eq
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input =
      [indexedGuardedSourceTape bits suffixTail rightPadding input,
        canonicalGuardedScratchTape,
        indexedGuardedOutputTape bits outputPadding input] := by
  rfl

@[simp] theorem indexedLogicalTapes_length
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    (indexedLogicalTapes
      bits suffixTail rightPadding outputPadding input).length = 3 := by
  rfl

@[simp] theorem indexedGuardedLogicalTapes_length
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    (indexedGuardedLogicalTapes
      bits suffixTail rightPadding outputPadding input).length = 3 := by
  rfl

theorem indexedSource_cells
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.cells (indexedSource bits suffixTail rightPadding input) =
      none ::
        List.append
          ((List.append boolWordRawBitsDecoderHeaderBits
            (List.append
              (boolWordRawBitsDecoderEncodedFieldBits (bits input))
              (false :: suffixTail input))).map some)
          (none :: rightPadding input) := by
  simpa [indexedSource,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerSource] using
    boolWordRawBitsDecoderSourceTape_cells
      (bits input) (suffixTail input) (rightPadding input)

theorem indexedOutput_cells
    {ι : Type}
    (bits : ι -> Word Bool)
    (outputPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.cells (indexedOutput bits outputPadding input) =
      none ::
        List.append
          (List.replicate ((bits input).length + 1)
            (none : Option Bool))
          (outputPadding input) := by
  simpa [indexedOutput,
    structuredBoolWordRawBitsDecoderIndexedInputMaterializerOutputTape] using
    structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding_cells
      (bits input).length (outputPadding input)

theorem indexedTarget_read
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.read
        (indexedTarget bits suffixTail rightPadding outputPadding input) =
      none := by
  simpa [indexedTarget, indexedSource, indexedOutput] using
    StructuredInputMaterializerEndpoint.targetTape_read
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedTarget_cells
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.cells
        (indexedTarget bits suffixTail rightPadding outputPadding input) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode
            (guardLogicalTape
              (indexedSource bits suffixTail rightPadding input)))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode
                (guardLogicalTape Tape.blank))
              (List.append tapeSeparatorCells
                (List.append (logicalTapeCode
                    (guardLogicalTape
                      (indexedOutput bits outputPadding input)))
                  tapeSeparatorCells))))) := by
  simpa [indexedTarget, indexedSource, indexedOutput] using
    StructuredInputMaterializerEndpoint.targetTape_cells
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedTarget_normalizedOutput_eq_guardedLogicalBits
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.normalizedOutput
        (indexedTarget bits suffixTail rightPadding outputPadding input) =
      List.append
        (logicalTapeBits
          (indexedGuardedSourceTape bits suffixTail rightPadding input))
        (List.append
          (logicalTapeBits canonicalGuardedScratchTape)
          (logicalTapeBits
            (indexedGuardedOutputTape bits outputPadding input))) := by
  simpa [indexedTarget, indexedSource, indexedOutput,
    indexedGuardedSourceTape, indexedGuardedOutputTape,
    canonicalGuardedScratchTape] using
    StructuredInputMaterializerEndpoint.targetTape_normalizedOutput_eq_guardedLogicalBits
        (indexedSource bits suffixTail rightPadding input)
        (indexedOutput bits outputPadding input)

theorem indexedTarget_normalizedOutput_eq_namedTargetTape
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.normalizedOutput
        (indexedTarget bits suffixTail rightPadding outputPadding input) =
      Tape.normalizedOutput
        (structuredBoolWordRawBitsDecoderIndexedInputMaterializerTargetTape
          bits suffixTail rightPadding outputPadding input) := by
  rw [indexedTarget_eq_namedTargetTape]

theorem indexedTarget_structuredEncodedTapes
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    StructuredEncodedTapes
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input)
      (indexedTarget bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedTarget, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.targetTape_structuredEncodedTapes_guarded
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedTarget_structuredGuardedEncodedTapes
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    StructuredGuardedEncodedTapes
      (indexedLogicalTapes
        bits suffixTail rightPadding outputPadding input)
      (indexedTarget bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedTarget, indexedSource, indexedOutput,
    indexedLogicalTapes] using
    StructuredInputMaterializerEndpoint.targetTape_structuredGuardedEncodedTapes
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedTarget_structuredLogicalEquivEncodedTapes
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    StructuredLogicalEquivEncodedTapes
      (indexedLogicalTapes
        bits suffixTail rightPadding outputPadding input)
      (indexedTarget bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedTarget, indexedSource, indexedOutput,
    indexedLogicalTapes] using
    StructuredInputMaterializerEndpoint.targetTape_structuredLogicalEquivEncodedTapes
        (indexedSource bits suffixTail rightPadding input)
        (indexedOutput bits outputPadding input)

theorem indexedGuardedSourceTape_equiv
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.Equiv
      (indexedGuardedSourceTape bits suffixTail rightPadding input)
      (indexedSource bits suffixTail rightPadding input) := by
  exact
    StructuredInputMaterializerEndpoint.guardedSourceTape_equiv
      (indexedSource bits suffixTail rightPadding input)

theorem indexedGuardedOutputTape_equiv
    {ι : Type}
    (bits : ι -> Word Bool)
    (outputPadding : ι -> List (Option Bool))
    (input : ι) :
    Tape.Equiv
      (indexedGuardedOutputTape bits outputPadding input)
      (indexedOutput bits outputPadding input) := by
  exact
    StructuredInputMaterializerEndpoint.guardedOutputTape_equiv
      (indexedOutput bits outputPadding input)

theorem indexedGuardedLogicalTapes_haveGuardCells
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    LogicalTapesHaveGuardCells
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) := by
  exact
    StructuredInputMaterializerEndpoint.guardedLogicalTapes_haveGuardCells
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtSeparator0
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 0
      (indexedTarget bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedTarget, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSeparator0
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtSeparator1
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 1
      (indexedSeparator1Tape
        bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedSeparator1Tape, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSeparator1
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtSeparator2
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 2
      (indexedSeparator2Tape
        bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedSeparator2Tape, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSeparator2
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtExistingSeparator0
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtExistingTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 0
      (indexedTarget bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedTarget, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atExistingSeparator0
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtExistingSeparator1
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtExistingTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 1
      (indexedSeparator1Tape
        bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedSeparator1Tape, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atExistingSeparator1
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtExistingSeparator2
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtExistingTapeSeparator
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 2
      (indexedSeparator2Tape
        bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedSeparator2Tape, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atExistingSeparator2
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtHeadCell0
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtTapeHeadCellCode
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 0
      (indexedHeadCell0Tape
        bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedHeadCell0Tape, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadCell0
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtHeadCell1
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtTapeHeadCellCode
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 1
      (indexedHeadCell1Tape
        bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedHeadCell1Tape, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadCell1
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtHeadCell2
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtTapeHeadCellCode
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 2
      (indexedHeadCell2Tape
        bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedHeadCell2Tape, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atHeadCell2
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtSegmentEnd0
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtTapeSegmentEnd
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 0
      (indexedSegmentEnd0Tape
        bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedSegmentEnd0Tape, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSegmentEnd0
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtSegmentEnd1
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtTapeSegmentEnd
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 1
      (indexedSegmentEnd1Tape
        bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedSegmentEnd1Tape, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSegmentEnd1
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

theorem indexedAtSegmentEnd2
    {ι : Type}
    (bits suffixTail : ι -> Word Bool)
    (rightPadding outputPadding : ι -> List (Option Bool))
    (input : ι) :
    AtTapeSegmentEnd
      (indexedGuardedLogicalTapes
        bits suffixTail rightPadding outputPadding input) 2
      (indexedSegmentEnd2Tape
        bits suffixTail rightPadding outputPadding input) := by
  simpa [indexedSegmentEnd2Tape, indexedSource, indexedOutput,
    indexedGuardedLogicalTapes] using
    StructuredInputMaterializerEndpoint.atSegmentEnd2
      (indexedSource bits suffixTail rightPadding input)
      (indexedOutput bits outputPadding input)

/-!
## Canonical as an indexed specialization
-/

def canonicalIndexSource
    (input : Word Bool × Word Bool) : Tape Bool :=
  canonicalSource input.1 input.2

def canonicalIndexOutput
    (input : Word Bool × Word Bool) : Tape Bool :=
  canonicalOutput input.1 input.2

def canonicalIndexTarget
    (input : Word Bool × Word Bool) : Tape Bool :=
  canonicalTarget input.1 input.2

theorem canonicalSource_eq_indexedSource
    (bits suffixTail : Word Bool) :
    canonicalSource bits suffixTail =
      indexedSource
        (fun input : Word Bool × Word Bool => input.1)
        (fun input : Word Bool × Word Bool => input.2)
        (fun _ : Word Bool × Word Bool => [])
        (bits, suffixTail) := by
  rfl

theorem canonicalOutput_eq_indexedOutput
    (bits suffixTail : Word Bool) :
    canonicalOutput bits suffixTail =
      indexedOutput
        (fun input : Word Bool × Word Bool => input.1)
        (fun input : Word Bool × Word Bool =>
          boolWordRawBitsDecoderPreservedPadding input.2 [])
        (bits, suffixTail) := by
  rfl

theorem canonicalTarget_eq_indexedTarget
    (bits suffixTail : Word Bool) :
    canonicalTarget bits suffixTail =
      indexedTarget
        (fun input : Word Bool × Word Bool => input.1)
        (fun input : Word Bool × Word Bool => input.2)
        (fun _ : Word Bool × Word Bool => [])
        (fun input : Word Bool × Word Bool =>
          boolWordRawBitsDecoderPreservedPadding input.2 [])
        (bits, suffixTail) := by
  rfl

theorem canonicalIndexSource_eq_materializerSource
    (input : Word Bool × Word Bool) :
    canonicalIndexSource input =
      structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource
        input := by
  cases input
  rfl

theorem canonicalIndexOutput_eq_materializerOutput
    (input : Word Bool × Word Bool) :
    canonicalIndexOutput input =
      structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
        input := by
  cases input
  rfl

theorem canonicalIndexTarget_eq_materializerTarget
    (input : Word Bool × Word Bool) :
    canonicalIndexTarget input =
      structured3InputMaterializerTargetTape
        (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerSource
          input)
        (structuredBoolWordRawBitsDecoderCanonicalInputMaterializerOutputTape
          input) := by
  cases input
  rfl

end BoolWordRawBitsDecoderInputMaterializerEndpoint

end FiniteTransducers
end CommonGround
end Computability
end FoC
