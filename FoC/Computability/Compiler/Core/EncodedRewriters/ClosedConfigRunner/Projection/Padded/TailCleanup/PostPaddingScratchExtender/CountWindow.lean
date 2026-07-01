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

def selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  tapeAtCells
    (none ::
      (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).reverse.map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).map some)
      (none ::
        none ::
        List.append
          (List.replicate
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L).length
            (none : Option Bool))
          (selectedProjectionPaddedTailCleanupPostCountTailCells
            useAccept L extraScratch)))

def selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape Bool :=
  tapeAtCells
    (none ::
      (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).reverse.map some)
    (List.append
      ((selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).map some)
      (none ::
        List.append
          (List.replicate
            ((selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L).length + 1)
            (none : Option Bool))
          (selectedProjectionPaddedTailCleanupPostCountTailCells
            useAccept L extraScratch)))

theorem selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
            useAccept L extraScratch)) =
      selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
        useAccept L extraScratch := by
  unfold selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
  cases hcount :
      selectedProjectionPaddedTailCleanupScratchCountBits useAccept L with
  | nil =>
      simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons bit rest =>
      cases rest <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail_move_left_move_right
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
            useAccept L extraScratch)) =
      selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
        useAccept L extraScratch := by
  unfold selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
  cases hcount :
      selectedProjectionPaddedTailCleanupScratchCountBits useAccept L with
  | nil =>
      simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons bit rest =>
      cases rest <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

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

theorem selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
          useAccept L extraScratch) =
      List.append (ParsedLayoutBits L)
        ((selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L extraScratch).filterMap id) := by
  have hprefix :=
    (selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
      useAccept L).symm
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail,
    tapeAtCells_normalizedOutput, List.filterMap_append,
    Function.comp_def, List.append_assoc] using
      congrArg
        (fun pref =>
          List.append pref
            ((selectedProjectionPaddedTailCleanupPostCountTailCells
              useAccept L extraScratch).filterMap id))
        hprefix

theorem selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail_normalizedOutput
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    Tape.normalizedOutput
        (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
          useAccept L extraScratch) =
      List.append (ParsedLayoutBits L)
        ((selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L extraScratch).filterMap id) := by
  have hprefix :=
    (selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
      useAccept L).symm
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail,
    tapeAtCells_normalizedOutput, List.filterMap_append,
    Function.comp_def, List.append_assoc] using
      congrArg
        (fun pref =>
          List.append pref
            ((selectedProjectionPaddedTailCleanupPostCountTailCells
              useAccept L extraScratch).filterMap id))
        hprefix

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
Executable raw-window counter with the branch-specific post-count tail
preserved as right context.  This is the shape the surrounding extender must
reach after it has decoded/exposed the selected parsed-layout count field; it
is not itself the original encoded branch source.
-/
theorem scratchCounterAppendBlanksDescription_haltsFrom_scratchCountWindowWithPostCountTail
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    scratchCounterAppendBlanksDescription.HaltsFromTape
      (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
        useAccept L extraScratch)
      (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
        useAccept L extraScratch) := by
  simpa [
    selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail,
    selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail,
    List.append_assoc]
    using
      scratchCounterAppendBlanksDescription_haltsFrom_withRight
        ((selectedProjectionPaddedTailCleanupScratchSkippedBits
          useAccept L).reverse.map some)
        (selectedProjectionPaddedTailCleanupScratchCountBits useAccept L)
        (selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L extraScratch)
        (selectedProjectionPaddedTailCleanupScratchCountBits_length_pos
          useAccept L)

def SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec
    (useAccept : Bool) (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall L : DovetailLayout,
      materializer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail
          useAccept L 0)

def SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec
    (useAccept : Bool) (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall L : DovetailLayout,
      restorer.HaltsFromTape
        (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
          useAccept L 0)
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length)

def SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction :
    Prop :=
  forall useAccept : Bool,
    exists materializer : MachineDescription,
    exists restorer : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec
        useAccept materializer ∧
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec
        useAccept restorer

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec_of_countWindowMaterializerAndRestorer
    {useAccept : Bool} {materializer restorer : MachineDescription}
    (hmaterializer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerSpec
        useAccept materializer)
    (hrestorer :
      SelectedProjectionPaddedTailCleanupScratchCountWindowRestorerSpec
        useAccept restorer) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec
      useAccept
      (canonicalSeqDescription
        (canonicalSeqDescription materializer
          scratchCounterAppendBlanksDescription)
        restorer) := by
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        (canonicalSeqDescription_subroutineReady
          hmaterializer.left
          scratchCounterAppendBlanksDescription_subroutineReady)
        hrestorer.left
  · intro L
    have hcounterSeq :
        (canonicalSeqDescription materializer
          scratchCounterAppendBlanksDescription).HaltsFromTape
          (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
            useAccept L 0)
          (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail
            useAccept L 0) := by
      exact
        canonicalSeqDescription_haltsFromTape_of_haltsFromTape
          hmaterializer.left
          scratchCounterAppendBlanksDescription_subroutineReady
          (hmaterializer.right L)
          (selectedProjectionPaddedTailCleanupScratchCountCounterSourceTapeWithPostCountTail_move_left_move_right
            useAccept L 0)
          (scratchCounterAppendBlanksDescription_haltsFrom_scratchCountWindowWithPostCountTail
            useAccept L 0)
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        (canonicalSeqDescription_subroutineReady
          hmaterializer.left
          scratchCounterAppendBlanksDescription_subroutineReady)
        hrestorer.left
        hcounterSeq
        (selectedProjectionPaddedTailCleanupScratchCountCounterTargetTapeWithPostCountTail_move_left_move_right
          useAccept L 0)
        (hrestorer.right L)

theorem selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction_of_countWindowMaterializers
    (h :
      SelectedProjectionPaddedTailCleanupScratchCountWindowMaterializerAndRestorerConstruction) :
    SelectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderConstruction := by
  intro useAccept
  rcases h useAccept with
    ⟨materializer, restorer, hmaterializer, hrestorer⟩
  exact
    ⟨canonicalSeqDescription
        (canonicalSeqDescription materializer
          scratchCounterAppendBlanksDescription)
        restorer,
      selectedProjectionPaddedTailCleanupPostPaddingScratchCountExtenderSpec_of_countWindowMaterializerAndRestorer
        hmaterializer hrestorer⟩

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
