import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.Specs

set_option doc.verso true

/-!
# Padded merge post-transition construction adapters

This module contains the branch-composition adapters for the padded merge
post-transition phase.  The construction-family contracts live in
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.Specs`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedMergePaddedEmitterAfterHitPaddedFromRewind
    (postRewind : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    SelectedMergePaddedEmitterCleanup.sourceRewindDescription
    postRewind

theorem SelectedMergePaddedEmitterAfterHitPaddedSpec_of_rewind
    {useAccept : Bool} {postRewind : MachineDescription}
    (hpostRewind :
      SelectedMergePaddedEmitterAfterHitRewindSpec
        useAccept postRewind) :
    SelectedMergePaddedEmitterAfterHitPaddedSpec useAccept
      (SelectedMergePaddedEmitterAfterHitPaddedFromRewind postRewind) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        SelectedMergePaddedEmitterCleanup.sourceRewindDescription_subroutineReady
        hpostRewind.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        SelectedMergePaddedEmitterCleanup.sourceRewindDescription_subroutineReady
        hpostRewind.left
        (sourceRewindDescription_haltsFrom_afterHitPaddedTape p)
        (SelectedMergePaddedEmitterCleanup.rewindTargetPaddedTape_move_left_move_right
          (SelectedMergePaddedEmitterCleanup.sourceBits p))
        (hpostRewind.right p)

def SelectedMergePaddedEmitterAfterTransitionPaddedFromSourceScanner
    (afterHit : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    SelectedMergePaddedEmitterSourceScannerDescription
    afterHit

theorem SelectedMergePaddedEmitterAfterTransitionPaddedSpec_of_afterHitPadded
    {useAccept : Bool} {afterHit : MachineDescription}
    (hafterHit :
      SelectedMergePaddedEmitterAfterHitPaddedSpec
        useAccept afterHit) :
    SelectedMergePaddedEmitterAfterTransitionPaddedSpec useAccept
      (SelectedMergePaddedEmitterAfterTransitionPaddedFromSourceScanner
        afterHit) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        selectedMergePaddedEmitterSourceScanner_subroutineReady
        hafterHit.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        selectedMergePaddedEmitterSourceScanner_subroutineReady
        hafterHit.left
        (selectedMergePaddedEmitterSourceScanner_haltsFrom_afterTransitionPadded p)
        (SelectedMergePaddedEmitterAfterHitPaddedTape_move_left_move_right
          p)
        (hafterHit.right p)

theorem SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction_of_afterHitPadded
    {useAccept : Bool}
    (h :
      SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction
        useAccept) :
    SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction
        useAccept := by
  rcases h with ⟨afterHit, hafterHit⟩
  exact
    ⟨SelectedMergePaddedEmitterAfterTransitionPaddedFromSourceScanner
        afterHit,
      SelectedMergePaddedEmitterAfterTransitionPaddedSpec_of_afterHitPadded
        hafterHit⟩

def SelectedMergePaddedEmitterAfterHitRewindFromTransition
    (afterTransition : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription
    afterTransition

theorem SelectedMergePaddedEmitterAfterHitRewindSpec_of_afterTransition
    {useAccept : Bool} {afterTransition : MachineDescription}
    (hafterTransition :
      SelectedMergePaddedEmitterAfterTransitionPaddedSpec
        useAccept afterTransition) :
    SelectedMergePaddedEmitterAfterHitRewindSpec useAccept
      (SelectedMergePaddedEmitterAfterHitRewindFromTransition
        afterTransition) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription_subroutineReady
        hafterTransition.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        SelectedMergePaddedEmitterCleanup.skipTransitionPrefixDescription_subroutineReady
        hafterTransition.left
        (skipTransitionPrefixDescription_haltsFrom_afterHitRewindSource p)
        (SelectedMergePaddedEmitterAfterTransitionPaddedTape_move_left_move_right
          p)
        (hafterTransition.right p)

theorem SelectedMergePaddedEmitterAfterHitRewindConstruction_of_afterTransition
    (h :
      SelectedMergePaddedEmitterAfterTransitionPaddedConstruction) :
    SelectedMergePaddedEmitterAfterHitRewindConstruction := by
  intro useAccept
  rcases h useAccept with ⟨afterTransition, hafterTransition⟩
  exact
    ⟨SelectedMergePaddedEmitterAfterHitRewindFromTransition
        afterTransition,
      SelectedMergePaddedEmitterAfterHitRewindSpec_of_afterTransition
        hafterTransition⟩

theorem selectedMergePaddedEmitterAfterTransitionPaddedConstruction_of_branches
    (hAccept :
      SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction true)
    (hReject :
      SelectedMergePaddedEmitterAfterTransitionPaddedBranchConstruction false) :
    SelectedMergePaddedEmitterAfterTransitionPaddedConstruction := by
  intro useAccept
  cases useAccept
  · exact hReject
  · exact hAccept

def SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsFromNestedParsed
    (parser emitter : MachineDescription) : MachineDescription :=
  SeqViaCanonical parser emitter

theorem
    selectedMergePaddedEmitterAfterHitPaddedSourceFieldsSpec_of_parsedInner
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec parser)
    (hemitter :
      SelectedMergePaddedEmitterAfterHitPaddedParsedInnerSpec
        useAccept emitter) :
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsSpec useAccept
      (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsFromNestedParsed
        parser emitter) := by
  constructor
  · exact SeqViaCanonical_subroutineReady hparser.left hemitter.left
  · intro p
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hparser.left hemitter.left
        (hparser.right p)
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_move_left_move_right
          p)
        (hemitter.right p)

theorem
    selectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsSpec_of_parsedInner
    {parser emitter : MachineDescription}
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec parser)
    (hemitter :
      SelectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerSpec emitter) :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsSpec
      (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsFromNestedParsed
        parser emitter) :=
  selectedMergePaddedEmitterAfterHitPaddedSourceFieldsSpec_of_parsedInner
    hparser hemitter

theorem
    selectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsSpec_of_parsedInner
    {parser emitter : MachineDescription}
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec parser)
    (hemitter :
      SelectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerSpec emitter) :
    SelectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsSpec
      (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsFromNestedParsed
        parser emitter) :=
  selectedMergePaddedEmitterAfterHitPaddedSourceFieldsSpec_of_parsedInner
    hparser hemitter

theorem
    selectedMergePaddedEmitterAfterHitPaddedSourceFieldsConstruction_of_parsedInner
    {useAccept : Bool}
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction)
    (hemitter :
      SelectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction
        useAccept) :
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsConstruction
      useAccept := by
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter with ⟨emitter, hemits⟩
  exact
    ⟨SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsFromNestedParsed
        parser emitter,
      selectedMergePaddedEmitterAfterHitPaddedSourceFieldsSpec_of_parsedInner
        hparser hemits⟩

theorem
    selectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction_of_parsedInner
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction)
    (hemitter :
      SelectedMergePaddedEmitterAfterHitPaddedAcceptParsedInnerConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction :=
  selectedMergePaddedEmitterAfterHitPaddedSourceFieldsConstruction_of_parsedInner
    hparser hemitter

theorem
    selectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction_of_parsedInner
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction)
    (hemitter :
      SelectedMergePaddedEmitterAfterHitPaddedRejectParsedInnerConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction :=
  selectedMergePaddedEmitterAfterHitPaddedSourceFieldsConstruction_of_parsedInner
    hparser hemitter

theorem selectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction_of_sourceFields
    (h :
      SelectedMergePaddedEmitterAfterHitPaddedAcceptSourceFieldsConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction := by
  rcases h with ⟨emitter, hemits⟩
  refine ⟨emitter, ?_⟩
  constructor
  · exact hemits.left
  · intro p
    rw [SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceFieldsTape p]
    exact hemits.right p

theorem selectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction_of_sourceFields
    (h :
      SelectedMergePaddedEmitterAfterHitPaddedRejectSourceFieldsConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction := by
  rcases h with ⟨emitter, hemits⟩
  refine ⟨emitter, ?_⟩
  constructor
  · exact hemits.left
  · intro p
    rw [SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceFieldsTape p]
    exact hemits.right p

theorem selectedMergePaddedEmitterAfterHitPaddedAcceptConstruction_of_decoded
    (h :
      SelectedMergePaddedEmitterAfterHitPaddedAcceptDecodedConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction true := by
  rcases h with ⟨emitter, hemits⟩
  refine ⟨emitter, ?_⟩
  constructor
  · exact hemits.left
  · intro p
    rw [←
      SelectedMergePaddedEmitterAcceptDecodedHandoffTape_eq_outputTape p]
    exact hemits.right p

theorem selectedMergePaddedEmitterAfterHitPaddedRejectConstruction_of_decoded
    (h :
      SelectedMergePaddedEmitterAfterHitPaddedRejectDecodedConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedBranchConstruction false := by
  rcases h with ⟨emitter, hemits⟩
  refine ⟨emitter, ?_⟩
  constructor
  · exact hemits.left
  · intro p
    rw [←
      SelectedMergePaddedEmitterRejectDecodedHandoffTape_eq_outputTape p]
    exact hemits.right p

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
