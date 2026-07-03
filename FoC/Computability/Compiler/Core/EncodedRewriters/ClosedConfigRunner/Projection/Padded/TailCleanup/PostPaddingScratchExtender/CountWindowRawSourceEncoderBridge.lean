import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawSourceEncoder
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail.EmitterConstruction
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchExtender.CountWindow

set_option doc.verso true

/-!
# Count-window raw-source encoder bridge

This projection-side module is the intended home for proof routes that use the
selected-projection live-tail emitter to discharge the scratch-count window raw
source encoder.  Keeping this bridge here avoids importing projection/quoter
machinery into the lower-level
{module}`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.CountWindowRawSourceEncoder`.
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

theorem selectedProjectionPaddedTailCleanupPostCountTailCells_zero_append_replicate_bridge
    (useAccept : Bool) (L : DovetailLayout) (extraScratch : Nat) :
    List.append
        (selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L 0)
        (List.replicate extraScratch (none : Option Bool)) =
      selectedProjectionPaddedTailCleanupPostCountTailCells
        useAccept L extraScratch := by
  cases useAccept <;>
    simp [selectedProjectionPaddedTailCleanupPostCountTailCells,
      selectedProjectionPaddedTailCleanupAcceptPostCountTailCells,
      selectedProjectionPaddedTailCleanupRejectPostCountTailCells,
      selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
      selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
      selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
      selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
      List.append_assoc]

theorem
    selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_of_countWindowRawSourceEncoder_bridge
    (hencoder : CountWindowRawSourceEncoderEquivConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction := by
  rcases hencoder with ⟨encoder, hencoderSpec⟩
  intro useAccept
  exact
    ⟨encoder,
      hencoderSpec.left,
      fun L => by
        have hsplit :
            ParsedLayoutBits L =
              List.append
                (selectedProjectionPaddedTailCleanupScratchSkippedBits
                  useAccept L)
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L) :=
          selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
            useAccept L
        rcases
            selectedProjectionPaddedTailCleanupPostCountTailCells_cons_false
              useAccept L 0 with
          ⟨postCountTail, hpostCountTail⟩
        have htail :
            List.append
                (some false :: postCountTail)
                (List.replicate
                  (selectedProjectionPaddedTailCleanupScratchCountBits
                    useAccept L).length
                  (none : Option Bool)) =
              selectedProjectionPaddedTailCleanupPostCountTailCells
                useAccept L
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L).length := by
          rw [← hpostCountTail]
          exact
            selectedProjectionPaddedTailCleanupPostCountTailCells_zero_append_replicate_bridge
              useAccept L
              (selectedProjectionPaddedTailCleanupScratchCountBits
                useAccept L).length
        have hrun :=
          hencoderSpec.right
            (selectedProjectionPaddedTailCleanupScratchSkippedBits
              useAccept L)
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L)
            false
            postCountTail
        have hsource :
            countWindowRawSourceEncoderSourceTape
                (selectedProjectionPaddedTailCleanupScratchSkippedBits
                  useAccept L)
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L)
                (some false :: postCountTail) =
              selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithExtraCountBlank
                useAccept L 0 := by
          simp [selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithExtraCountBlank,
            countWindowRawSourceEncoderSourceTape,
            hsplit, hpostCountTail, List.map_append, List.append_assoc]
        have htarget :
            countWindowRawSourceEncoderTargetTape
                (selectedProjectionPaddedTailCleanupScratchSkippedBits
                  useAccept L)
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L)
                (some false :: postCountTail) =
              selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
                useAccept L
                (selectedProjectionPaddedTailCleanupScratchCountBits
                  useAccept L).length := by
          unfold countWindowRawSourceEncoderTargetTape
          rw [htail]
          cases useAccept <;>
            simp [
              selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch_countSplit,
              selectedProjectionPaddedTailCleanupEncodedCountWindowSourceCells,
              selectedProjectionPaddedTailCleanupEncodedHeaderCells,
              selectedProjectionPaddedTailCleanupEncodedLayoutLengthCells,
              selectedProjectionPaddedTailCleanupEncodedScratchSkippedCells,
              selectedProjectionPaddedTailCleanupEncodedScratchCountCells,
              selectedProjectionPaddedTailCleanupPostCountTailCells,
              selectedProjectionPaddedTailCleanupAcceptPostCountTailCells,
              selectedProjectionPaddedTailCleanupRejectPostCountTailCells,
              selectedProjectionPaddedTailCleanupAcceptAfterStageTailCells,
              selectedProjectionPaddedTailCleanupRejectAfterStageTailCells,
              countWindowRawSourceEncoderHeaderCells,
              countWindowRawSourceEncoderLayoutLengthCells,
              countWindowRawSourceEncoderCellFieldCells,
              hsplit]
        rw [← hsource, ← htarget]
        exact hrun⟩

def SelectedProjectionPaddedTailCleanupScratchCountWindowLiveTailEmitterSpec
    (useAccept : Bool) (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall (L : DovetailLayout) (postCountTail : List (Option Bool)),
      selectedProjectionPaddedTailCleanupPostCountTailCells
          useAccept L 0 =
        some false :: postCountTail ->
      emitter.HaltsFromTapeEquiv
        (countWindowRawSourceEncoderLiveTailEmitterSourceTape
          (selectedProjectionPaddedTailCleanupScratchSkippedBits
            useAccept L)
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L)
          false
          postCountTail)
        (selectedProjectionPaddedTailCleanupBaseSourceTapeWithExtraScratch
          useAccept L
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).length)

def SelectedProjectionPaddedTailCleanupScratchCountWindowLiveTailEmitterConstruction :
    Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionPaddedTailCleanupScratchCountWindowLiveTailEmitterSpec
        useAccept emitter

theorem
    selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_of_liveTailEmitter
    (hemitter :
      SelectedProjectionPaddedTailCleanupScratchCountWindowLiveTailEmitterConstruction) :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction := by
  intro useAccept
  rcases hemitter useAccept with ⟨emitter, hemitterSpec⟩
  refine
    ⟨seqSubroutine
        countWindowRawSourceEncoderScanToTailPastFirstDescription
        emitter Direction.right,
      ?_⟩
  constructor
  · exact
      seqSubroutine_subroutineReady
        countWindowRawSourceEncoderScanToTailPastFirstDescription_subroutineReady
        hemitterSpec.left
  · intro L
    rcases
        selectedProjectionPaddedTailCleanupPostCountTailCells_cons_false
          useAccept L 0 with
      ⟨postCountTail, hpostCountTail⟩
    have hsplit :
        ParsedLayoutBits L =
          List.append
            (selectedProjectionPaddedTailCleanupScratchSkippedBits
              useAccept L)
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L) :=
      selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
        useAccept L
    have hsource :
        countWindowRawSourceEncoderSourceTape
            (selectedProjectionPaddedTailCleanupScratchSkippedBits
              useAccept L)
            (selectedProjectionPaddedTailCleanupScratchCountBits
              useAccept L)
            (some false :: postCountTail) =
          selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithExtraCountBlank
            useAccept L 0 := by
      simp [selectedProjectionPaddedTailCleanupScratchCountRawSourceTapeWithExtraCountBlank,
        countWindowRawSourceEncoderSourceTape,
        hsplit, hpostCountTail, List.map_append, List.append_assoc]
    rw [← hsource]
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
        countWindowRawSourceEncoderScanToTailPastFirstDescription_subroutineReady
        hemitterSpec.left
        (countWindowRawSourceEncoderScanToTailPastFirstDescription_haltsFromTape
          (selectedProjectionPaddedTailCleanupScratchSkippedBits
            useAccept L)
          (selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L)
          false
          postCountTail)
        rfl
        (hemitterSpec.right L postCountTail hpostCountTail)

/--
Selected-projection live-tail emitter leaf for the scratch-count window.

This is the only remaining proof obligation for this bridge.  It is
deliberately narrower than
{name}`CountWindowRawSourceEncoderLiveTailEmitterEquivConstruction`: it only
has to handle the branch-specific tails produced by the selected-projection
post-padding cleanup.
-/
theorem
    selectedProjectionPaddedTailCleanupScratchCountWindowLiveTailEmitterConstruction_projectionLiveTail :
    SelectedProjectionPaddedTailCleanupScratchCountWindowLiveTailEmitterConstruction := by
  sorry

theorem
    selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_projectionLiveTailBridge :
    SelectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction := by
  exact
    selectedProjectionPaddedTailCleanupScratchCountWindowRawSourceEncoderConstruction_of_liveTailEmitter
      selectedProjectionPaddedTailCleanupScratchCountWindowLiveTailEmitterConstruction_projectionLiveTail

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
