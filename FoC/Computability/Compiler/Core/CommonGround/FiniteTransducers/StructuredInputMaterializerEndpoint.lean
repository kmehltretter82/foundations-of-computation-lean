import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer
import FoC.Computability.Compiler.Structured.Lowering.CursorBasic

set_option doc.verso true

/-!
# Structured input materializer endpoint facts

This module records exact endpoint facts for the canonical three-logical-tape
input materializer target.  It is deliberately construction-free: later
finite-machine materializer proofs can use these named shape lemmas instead of
unfolding the guarded structured layout at every handoff.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

namespace StructuredInputMaterializerEndpoint

open Structured.MultiTapeLowering

def logicalTapes (source output : Tape Bool) : List (Tape Bool) :=
  [source, Tape.blank, output]

def guardedLogicalTapes (source output : Tape Bool) : List (Tape Bool) :=
  guardLogicalTapes (logicalTapes source output)

def targetTape (source output : Tape Bool) : Tape Bool :=
  structured3InputMaterializerTargetTape source output

def separatorTape (source output : Tape Bool) (index : Nat) : Tape Bool :=
  tapeAtEncodedSplit
    (encodedPrefixBeforeTape (guardedLogicalTapes source output) index)
    (encodedSuffixFromTape (guardedLogicalTapes source output) index)

def separator0Tape (source output : Tape Bool) : Tape Bool :=
  separatorTape source output 0

def separator1Tape (source output : Tape Bool) : Tape Bool :=
  separatorTape source output 1

def separator2Tape (source output : Tape Bool) : Tape Bool :=
  separatorTape source output 2

theorem logicalTapes_eq (source output : Tape Bool) :
    logicalTapes source output = [source, Tape.blank, output] := by
  rfl

theorem guardedLogicalTapes_eq (source output : Tape Bool) :
    guardedLogicalTapes source output =
      [guardLogicalTape source, guardLogicalTape Tape.blank,
        guardLogicalTape output] := by
  rfl

@[simp] theorem logicalTapes_length (source output : Tape Bool) :
    (logicalTapes source output).length = 3 := by
  rfl

@[simp] theorem guardedLogicalTapes_length
    (source output : Tape Bool) :
    (guardedLogicalTapes source output).length = 3 := by
  rfl

theorem logicalTapes_zero (source output : Tape Bool) :
    (logicalTapes source output)[0]? = some source := by
  rfl

theorem logicalTapes_one (source output : Tape Bool) :
    (logicalTapes source output)[1]? = some Tape.blank := by
  rfl

theorem logicalTapes_two (source output : Tape Bool) :
    (logicalTapes source output)[2]? = some output := by
  rfl

theorem guardedLogicalTapes_zero (source output : Tape Bool) :
    (guardedLogicalTapes source output)[0]? =
      some (guardLogicalTape source) := by
  rfl

theorem guardedLogicalTapes_one (source output : Tape Bool) :
    (guardedLogicalTapes source output)[1]? =
      some (guardLogicalTape Tape.blank) := by
  rfl

theorem guardedLogicalTapes_two (source output : Tape Bool) :
    (guardedLogicalTapes source output)[2]? =
      some (guardLogicalTape output) := by
  rfl

theorem targetTape_eq_encodedGuardedStructured3Tapes
    (source output : Tape Bool) :
    targetTape source output =
      encodedGuardedStructured3Tapes source Tape.blank output := by
  rfl

theorem targetTape_eq_encodedStructuredTapes_guarded
    (source output : Tape Bool) :
    targetTape source output =
      encodedStructuredTapes (guardedLogicalTapes source output) := by
  rfl

theorem targetTape_read (source output : Tape Bool) :
    Tape.read (targetTape source output) = none := by
  rfl

theorem targetTape_cells (source output : Tape Bool) :
    Tape.cells (targetTape source output) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape source))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape Tape.blank))
              (List.append tapeSeparatorCells
                (List.append (logicalTapeCode (guardLogicalTape output))
                  tapeSeparatorCells))))) := by
  simpa [targetTape, structured3InputMaterializerTargetTape,
    encodedGuardedStructured3Tapes, guardedLogicalTapes, logicalTapes] using
    encodedGuardedStructuredTapes_three_cells
      source Tape.blank output

theorem atSeparator0 (source output : Tape Bool) :
    AtTapeSeparator (guardedLogicalTapes source output) 0
      (targetTape source output) := by
  simpa [targetTape_eq_encodedStructuredTapes_guarded] using
    atTapeSeparator_zero_self (guardedLogicalTapes source output)

theorem separator0Tape_eq_targetTape (source output : Tape Bool) :
    separator0Tape source output = targetTape source output := by
  simp [separator0Tape, separatorTape,
    targetTape_eq_encodedStructuredTapes_guarded,
    encodedStructuredTapes, tapeAtEncodedSplit,
    encodedPrefixBeforeTape, encodedSuffixFromTape]

theorem atSeparator0_via_separatorTape (source output : Tape Bool) :
    AtTapeSeparator (guardedLogicalTapes source output) 0
      (separator0Tape source output) := by
  simpa [separator0Tape_eq_targetTape] using
    atSeparator0 source output

theorem atExistingSeparator0 (source output : Tape Bool) :
    AtExistingTapeSeparator (guardedLogicalTapes source output) 0
      (targetTape source output) := by
  constructor
  · exact atSeparator0 source output
  · exact
      ⟨guardLogicalTape source,
        [guardLogicalTape Tape.blank, guardLogicalTape output], rfl⟩

theorem atExistingSeparator0_via_separatorTape
    (source output : Tape Bool) :
    AtExistingTapeSeparator (guardedLogicalTapes source output) 0
      (separator0Tape source output) := by
  simpa [separator0Tape_eq_targetTape] using
    atExistingSeparator0 source output

theorem atSeparator1 (source output : Tape Bool) :
    AtTapeSeparator (guardedLogicalTapes source output) 1
      (separator1Tape source output) := by
  refine ⟨?_, rfl⟩
  simp [guardedLogicalTapes, logicalTapes]

theorem separator1Tape_eq_expanded (source output : Tape Bool) :
    separator1Tape source output =
      tapeAtEncodedSplit
        (List.append tapeSeparatorCells
          (logicalTapeCode (guardLogicalTape source)))
        (List.append tapeSeparatorCells
          (List.append (logicalTapeCode (guardLogicalTape Tape.blank))
            (List.append tapeSeparatorCells
              (List.append (logicalTapeCode (guardLogicalTape output))
                tapeSeparatorCells)))) := by
  simp [separator1Tape, separatorTape, guardedLogicalTapes, logicalTapes,
    guardLogicalTapes, encodedPrefixBeforeTape, encodedSuffixFromTape]

theorem atExistingSeparator1 (source output : Tape Bool) :
    AtExistingTapeSeparator (guardedLogicalTapes source output) 1
      (separator1Tape source output) := by
  constructor
  · exact atSeparator1 source output
  · exact ⟨guardLogicalTape Tape.blank, [guardLogicalTape output], rfl⟩

theorem atSeparator2 (source output : Tape Bool) :
    AtTapeSeparator (guardedLogicalTapes source output) 2
      (separator2Tape source output) := by
  refine ⟨?_, rfl⟩
  simp [guardedLogicalTapes, logicalTapes]

theorem separator2Tape_eq_expanded (source output : Tape Bool) :
    separator2Tape source output =
      tapeAtEncodedSplit
        (List.append
          (List.append tapeSeparatorCells
            (logicalTapeCode (guardLogicalTape source)))
          (List.append tapeSeparatorCells
            (logicalTapeCode (guardLogicalTape Tape.blank))))
        (List.append tapeSeparatorCells
          (List.append (logicalTapeCode (guardLogicalTape output))
            tapeSeparatorCells)) := by
  simp [separator2Tape, separatorTape, guardedLogicalTapes, logicalTapes,
    guardLogicalTapes, encodedPrefixBeforeTape, encodedSuffixFromTape]

theorem atExistingSeparator2 (source output : Tape Bool) :
    AtExistingTapeSeparator (guardedLogicalTapes source output) 2
      (separator2Tape source output) := by
  constructor
  · exact atSeparator2 source output
  · exact ⟨guardLogicalTape output, [], rfl⟩

/-!
## Guarded segment tapes
-/

def guardedSourceTape (source : Tape Bool) : Tape Bool :=
  guardLogicalTape source

def guardedScratchTape : Tape Bool :=
  guardLogicalTape Tape.blank

def guardedOutputTape (output : Tape Bool) : Tape Bool :=
  guardLogicalTape output

theorem guardedLogicalTapes_eq_named (source output : Tape Bool) :
    guardedLogicalTapes source output =
      [guardedSourceTape source, guardedScratchTape,
        guardedOutputTape output] := by
  rfl

theorem guardedSourceTape_equiv (source : Tape Bool) :
    Tape.Equiv (guardedSourceTape source) source := by
  exact guardLogicalTape_equiv source

theorem guardedScratchTape_equiv :
    Tape.Equiv guardedScratchTape Tape.blank := by
  exact guardLogicalTape_equiv Tape.blank

theorem guardedOutputTape_equiv (output : Tape Bool) :
    Tape.Equiv (guardedOutputTape output) output := by
  exact guardLogicalTape_equiv output

theorem guardedSourceTape_hasGuardCells (source : Tape Bool) :
    LogicalTapeHasGuardCells (guardedSourceTape source) := by
  exact guardLogicalTape_hasGuardCells source

theorem guardedScratchTape_hasGuardCells :
    LogicalTapeHasGuardCells guardedScratchTape := by
  exact guardLogicalTape_hasGuardCells Tape.blank

theorem guardedOutputTape_hasGuardCells (output : Tape Bool) :
    LogicalTapeHasGuardCells (guardedOutputTape output) := by
  exact guardLogicalTape_hasGuardCells output

theorem guardedLogicalTapes_haveGuardCells
    (source output : Tape Bool) :
    LogicalTapesHaveGuardCells (guardedLogicalTapes source output) := by
  intro T hT
  simp [guardedLogicalTapes_eq_named] at hT
  rcases hT with hT | hT | hT
  · simpa [hT] using guardedSourceTape_hasGuardCells source
  · simpa [hT] using guardedScratchTape_hasGuardCells
  · simpa [hT] using guardedOutputTape_hasGuardCells output

theorem guardedLogicalTapes_atHasGuardCells0
    (source output : Tape Bool) :
    LogicalTapeAtHasGuardCells (guardedLogicalTapes source output) 0 := by
  exact
    ⟨guardedSourceTape source,
      [guardedScratchTape, guardedOutputTape output],
      by rfl,
      guardedSourceTape_hasGuardCells source⟩

theorem guardedLogicalTapes_atHasGuardCells1
    (source output : Tape Bool) :
    LogicalTapeAtHasGuardCells (guardedLogicalTapes source output) 1 := by
  exact
    ⟨guardedScratchTape,
      [guardedOutputTape output],
      by rfl,
      guardedScratchTape_hasGuardCells⟩

theorem guardedLogicalTapes_atHasGuardCells2
    (source output : Tape Bool) :
    LogicalTapeAtHasGuardCells (guardedLogicalTapes source output) 2 := by
  exact
    ⟨guardedOutputTape output,
      [],
      by rfl,
      guardedOutputTape_hasGuardCells output⟩

theorem guardedLogicalTapes_drop0 (source output : Tape Bool) :
    (guardedLogicalTapes source output).drop 0 =
      guardedSourceTape source ::
        guardedScratchTape :: guardedOutputTape output :: [] := by
  rfl

theorem guardedLogicalTapes_drop1 (source output : Tape Bool) :
    (guardedLogicalTapes source output).drop 1 =
      guardedScratchTape :: guardedOutputTape output :: [] := by
  rfl

theorem guardedLogicalTapes_drop2 (source output : Tape Bool) :
    (guardedLogicalTapes source output).drop 2 =
      guardedOutputTape output :: [] := by
  rfl

/-!
## Head-marker and head-cell positions
-/

def headMarker0Tape (source output : Tape Bool) : Tape Bool :=
  tapeAtEncodedSplit
    (List.append
      (encodedPrefixBeforeTape (guardedLogicalTapes source output) 0)
      (List.append tapeSeparatorCells
        (logicalCellListCode
          (guardedSourceTape source).left.reverse)))
    (List.append headMarkerCells
      (List.append (logicalCellCode (guardedSourceTape source).head)
        (List.append
          (logicalCellListCode (guardedSourceTape source).right)
          (encodedStructuredTapeCells
            [guardedScratchTape, guardedOutputTape output]))))

def headMarker1Tape (source output : Tape Bool) : Tape Bool :=
  tapeAtEncodedSplit
    (List.append
      (encodedPrefixBeforeTape (guardedLogicalTapes source output) 1)
      (List.append tapeSeparatorCells
        (logicalCellListCode guardedScratchTape.left.reverse)))
    (List.append headMarkerCells
      (List.append (logicalCellCode guardedScratchTape.head)
        (List.append (logicalCellListCode guardedScratchTape.right)
          (encodedStructuredTapeCells [guardedOutputTape output]))))

def headMarker2Tape (source output : Tape Bool) : Tape Bool :=
  tapeAtEncodedSplit
    (List.append
      (encodedPrefixBeforeTape (guardedLogicalTapes source output) 2)
      (List.append tapeSeparatorCells
        (logicalCellListCode
          (guardedOutputTape output).left.reverse)))
    (List.append headMarkerCells
      (List.append (logicalCellCode (guardedOutputTape output).head)
        (List.append
          (logicalCellListCode (guardedOutputTape output).right)
          (encodedStructuredTapeCells []))))

theorem atHeadMarker0 (source output : Tape Bool) :
    AtTapeHeadMarker (guardedLogicalTapes source output) 0
      (headMarker0Tape source output) := by
  exact
    ⟨guardedSourceTape source,
      [guardedScratchTape, guardedOutputTape output],
      rfl,
      rfl⟩

theorem atHeadMarker1 (source output : Tape Bool) :
    AtTapeHeadMarker (guardedLogicalTapes source output) 1
      (headMarker1Tape source output) := by
  exact
    ⟨guardedScratchTape,
      [guardedOutputTape output],
      rfl,
      rfl⟩

theorem atHeadMarker2 (source output : Tape Bool) :
    AtTapeHeadMarker (guardedLogicalTapes source output) 2
      (headMarker2Tape source output) := by
  exact
    ⟨guardedOutputTape output,
      [],
      rfl,
      rfl⟩

def headCell0Tape (source output : Tape Bool) : Tape Bool :=
  tapeAtEncodedSplit
    (List.append
      (encodedPrefixBeforeTape (guardedLogicalTapes source output) 0)
      (List.append tapeSeparatorCells
        (List.append
          (logicalCellListCode
            (guardedSourceTape source).left.reverse)
          headMarkerCells)))
    (List.append (logicalCellCode (guardedSourceTape source).head)
      (List.append (logicalCellListCode (guardedSourceTape source).right)
        (encodedStructuredTapeCells
          [guardedScratchTape, guardedOutputTape output])))

def headCell1Tape (source output : Tape Bool) : Tape Bool :=
  tapeAtEncodedSplit
    (List.append
      (encodedPrefixBeforeTape (guardedLogicalTapes source output) 1)
      (List.append tapeSeparatorCells
        (List.append
          (logicalCellListCode guardedScratchTape.left.reverse)
          headMarkerCells)))
    (List.append (logicalCellCode guardedScratchTape.head)
      (List.append (logicalCellListCode guardedScratchTape.right)
        (encodedStructuredTapeCells [guardedOutputTape output])))

def headCell2Tape (source output : Tape Bool) : Tape Bool :=
  tapeAtEncodedSplit
    (List.append
      (encodedPrefixBeforeTape (guardedLogicalTapes source output) 2)
      (List.append tapeSeparatorCells
        (List.append
          (logicalCellListCode
            (guardedOutputTape output).left.reverse)
          headMarkerCells)))
    (List.append (logicalCellCode (guardedOutputTape output).head)
      (List.append (logicalCellListCode (guardedOutputTape output).right)
        (encodedStructuredTapeCells [])))

theorem atHeadCell0 (source output : Tape Bool) :
    AtTapeHeadCellCode (guardedLogicalTapes source output) 0
      (headCell0Tape source output) := by
  exact
    ⟨guardedSourceTape source,
      [guardedScratchTape, guardedOutputTape output],
      rfl,
      rfl⟩

theorem atHeadCell1 (source output : Tape Bool) :
    AtTapeHeadCellCode (guardedLogicalTapes source output) 1
      (headCell1Tape source output) := by
  exact
    ⟨guardedScratchTape,
      [guardedOutputTape output],
      rfl,
      rfl⟩

theorem atHeadCell2 (source output : Tape Bool) :
    AtTapeHeadCellCode (guardedLogicalTapes source output) 2
      (headCell2Tape source output) := by
  exact
    ⟨guardedOutputTape output,
      [],
      rfl,
      rfl⟩

/-!
## Segment-end positions
-/

def segmentEnd0Tape (source output : Tape Bool) : Tape Bool :=
  tapeAtEncodedSplit
    (List.append
      (encodedPrefixBeforeTape (guardedLogicalTapes source output) 0)
      (List.append tapeSeparatorCells
        (logicalTapeCode (guardedSourceTape source))))
    (encodedStructuredTapeCells
      [guardedScratchTape, guardedOutputTape output])

def segmentEnd1Tape (source output : Tape Bool) : Tape Bool :=
  tapeAtEncodedSplit
    (List.append
      (encodedPrefixBeforeTape (guardedLogicalTapes source output) 1)
      (List.append tapeSeparatorCells
        (logicalTapeCode guardedScratchTape)))
    (encodedStructuredTapeCells [guardedOutputTape output])

def segmentEnd2Tape (source output : Tape Bool) : Tape Bool :=
  tapeAtEncodedSplit
    (List.append
      (encodedPrefixBeforeTape (guardedLogicalTapes source output) 2)
      (List.append tapeSeparatorCells
        (logicalTapeCode (guardedOutputTape output))))
    (encodedStructuredTapeCells [])

theorem atSegmentEnd0 (source output : Tape Bool) :
    AtTapeSegmentEnd (guardedLogicalTapes source output) 0
      (segmentEnd0Tape source output) := by
  exact
    ⟨guardedSourceTape source,
      [guardedScratchTape, guardedOutputTape output],
      rfl,
      rfl⟩

theorem atSegmentEnd1 (source output : Tape Bool) :
    AtTapeSegmentEnd (guardedLogicalTapes source output) 1
      (segmentEnd1Tape source output) := by
  exact
    ⟨guardedScratchTape,
      [guardedOutputTape output],
      rfl,
      rfl⟩

theorem atSegmentEnd2 (source output : Tape Bool) :
    AtTapeSegmentEnd (guardedLogicalTapes source output) 2
      (segmentEnd2Tape source output) := by
  exact
    ⟨guardedOutputTape output,
      [],
      rfl,
      rfl⟩

/-!
## Structured representation views
-/

theorem targetTape_structuredEncodedTapes_guarded
    (source output : Tape Bool) :
    StructuredEncodedTapes (guardedLogicalTapes source output)
      (targetTape source output) := by
  exact targetTape_eq_encodedStructuredTapes_guarded source output

theorem targetTape_structuredGuardedEncodedTapes
    (source output : Tape Bool) :
    StructuredGuardedEncodedTapes (logicalTapes source output)
      (targetTape source output) := by
  rfl

theorem targetTape_structuredLogicalEquivEncodedTapes
    (source output : Tape Bool) :
    StructuredLogicalEquivEncodedTapes (logicalTapes source output)
      (targetTape source output) := by
  simpa [targetTape, structured3InputMaterializerTargetTape,
    logicalTapes, encodedGuardedStructured3Tapes] using
    structuredLogicalEquivEncodedTapes_guarded_self
      (logicalTapes source output)

theorem logicalTapes_equiv_guardedLogicalTapes
    (source output : Tape Bool) :
    LogicalTapeListEquiv
      (guardedLogicalTapes source output)
      (logicalTapes source output) := by
  simpa [guardedLogicalTapes, logicalTapes] using
    guardLogicalTapes_equiv (logicalTapes source output)

theorem targetTape_normalizedOutput_eq_guardedLogicalBits
    (source output : Tape Bool) :
    Tape.normalizedOutput (targetTape source output) =
      List.append
        (logicalTapeBits (guardedSourceTape source))
        (List.append
          (logicalTapeBits guardedScratchTape)
          (logicalTapeBits (guardedOutputTape output))) := by
  simpa [targetTape, structured3InputMaterializerTargetTape,
    structured3InputMaterializerTargetTape_normalizedOutput,
    guardedSourceTape, guardedScratchTape, guardedOutputTape] using
    structured3InputMaterializerTargetTape_normalizedOutput
      source output

theorem targetTape_normalizedOutput_eq_guardedLogicalTapes_bits
    (source output : Tape Bool) :
    Tape.normalizedOutput (targetTape source output) =
      List.append
        (logicalTapeBits
          ((guardedLogicalTapes source output).get
            ⟨0, by simp [guardedLogicalTapes, logicalTapes]⟩))
        (List.append
          (logicalTapeBits
            ((guardedLogicalTapes source output).get
              ⟨1, by simp [guardedLogicalTapes, logicalTapes]⟩))
          (logicalTapeBits
            ((guardedLogicalTapes source output).get
              ⟨2, by simp [guardedLogicalTapes, logicalTapes]⟩))) := by
  simpa [guardedLogicalTapes_eq_named] using
    targetTape_normalizedOutput_eq_guardedLogicalBits source output

end StructuredInputMaterializerEndpoint

end FiniteTransducers
end CommonGround
end Computability
end FoC
