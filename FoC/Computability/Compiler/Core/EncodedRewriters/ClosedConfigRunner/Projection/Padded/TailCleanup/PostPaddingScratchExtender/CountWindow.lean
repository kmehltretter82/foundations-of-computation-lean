import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchExtender.Adapters

set_option doc.verso true

/-!
# Post-padding scratch-count window construction

This module contains the exact scratch-count counter source/target tapes, the
checked core run that appends blanks once the count window is exposed, and the
remaining finite-machine construction leaf for exposing that window.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

def selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (none ::
      (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).reverse.map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).map some)
      (none ::
        none ::
        List.replicate
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length
          (none : Option Bool)))

def selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  tapeAtCells
    (none ::
      (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).reverse.map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).map some)
      (none ::
        List.replicate
          ((selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length + 1)
          (none : Option Bool)))

theorem selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape
          useAccept L) =
      ParsedLayoutBits L := by
  simpa [selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape,
    tapeAtCells_normalizedOutput, List.filterMap_append,
    Function.comp_def, List.append_assoc] using
      (selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
        useAccept L).symm

theorem selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape
          useAccept L) =
      ParsedLayoutBits L := by
  simpa [selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape,
    tapeAtCells_normalizedOutput, List.filterMap_append,
    Function.comp_def, List.append_assoc] using
      (selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
        useAccept L).symm

/--
Executable core of the post-padding scratch extender after the branch-specific
navigation has exposed the scratch-count suffix under the head.
-/
theorem scratchCounterAppendBlanksDescription_haltsFrom_scratchCountWindow
    (useAccept : Bool) (L : DovetailLayout) :
    scratchCounterAppendBlanksDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape
        useAccept L)
      (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape
        useAccept L) := by
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountCounterSourceTape,
    selectedProjectionPaddedTailCleanupScratchCountCounterTargetTape]
    using
      scratchCounterAppendBlanksDescription_haltsFrom_withRight
        ((selectedProjectionPaddedTailCleanupScratchSkippedBits
          useAccept L).reverse.map some)
        (selectedProjectionPaddedTailCleanupScratchCountBits useAccept L)
        []
        (selectedProjectionPaddedTailCleanupScratchCountBits_length_pos
          useAccept L)

/--
Finite-machine leaf that exposes the selected branch scratch-count window and
uses it to append the branch-specific scratch padding.
-/
theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction := by
  sorry

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction_of_countExtenders
    selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction :=
  selectedProjectionPaddedTailCleanupPostPaddingScratchAllocatorConstruction_of_extenders
    selectedProjectionPaddedTailCleanupPostPaddingScratchExtenderConstruction

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
