import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.ProjectionPadded.InputQuoter.Main
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.ProjectionPadded.TailCleanup

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionEquivPaddedEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  RightScratchPaddedEmitterSpec
    (fun L : DovetailLayout =>
      Tape.input (ParsedLayoutBits L))
    (fun L : DovetailLayout =>
      encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
    (fun L : DovetailLayout =>
      (ParsedLayoutBits L).length)
    (SelectedProjectionOutputTape useAccept)
    emitter

def SelectedProjectionEquivPaddedEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionEquivPaddedEmitterSpec useAccept emitter

def SelectedProjectionCheckedEquivPaddedEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  RightScratchPaddedEmitterSpec
    (fun L : DovetailLayout =>
      ParsedLayoutCheckedTape L)
    (fun L : DovetailLayout =>
      encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
    (fun L : DovetailLayout =>
      (ParsedLayoutBits L).length)
    (SelectedProjectionOutputTape useAccept)
    emitter

def SelectedProjectionCheckedEquivPaddedEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept emitter



def SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction :
    Prop :=
  SelectedProjectionInputQuoterConstruction ∧
    SelectedProjectionPaddedTailEmitterConstruction

def SelectedProjectionCheckedEquivPaddedEmitterFromComponents
    (quoter tail : MachineDescription) : MachineDescription :=
  SeqViaCanonical quoter tail

theorem selectedProjectionCheckedEquivPaddedEmitterSpec_of_components
    {useAccept : Bool}
    {quoter tail : MachineDescription}
    (hquoter : SelectedProjectionInputQuoterSpec quoter)
    (htail : SelectedProjectionPaddedTailEmitterSpec useAccept tail) :
    SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept
      (SelectedProjectionCheckedEquivPaddedEmitterFromComponents
        quoter tail) := by
  let baseLeft :=
    fun L : DovetailLayout =>
      (SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
        some
  constructor
  · exact SeqViaCanonical_subroutineReady hquoter.left htail.left
  constructor
  · intro L
    have hquoterRun :
        quoter.HaltsFromTape
          (ParsedLayoutCheckedTape L)
          (SelectedProjectionTailProjector.sourceTape L
            (baseLeft L)) :=
      hquoter.right L
    have htailRun :
        tail.HaltsFromTape
          (SelectedProjectionTailProjector.sourceTape L
            (baseLeft L))
          (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L) :=
      htail.right.left L
    have hbridge :
        Tape.move Direction.left
            (Tape.move Direction.right
              (SelectedProjectionTailProjector.sourceTape L
                (baseLeft L))) =
          SelectedProjectionTailProjector.sourceTape L
            (baseLeft L) :=
      SelectedProjectionTailProjector.sourceTape_move_left_move_right
        L (baseLeft L)
    simpa [SelectedProjectionCheckedEquivPaddedEmitterFromComponents] using
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        hquoter.left htail.left hquoterRun hbridge htailRun
  · intro L
    exact SelectedProjectionEquivEmitterPaddedOutputTape_equiv useAccept L

theorem selectedProjectionCheckedEquivPaddedEmitterConstruction_of_components
    (hcomponents :
      SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction) :
    SelectedProjectionCheckedEquivPaddedEmitterConstruction := by
  intro useAccept
  rcases hcomponents with ⟨⟨quoter, hquoter⟩, htailConstruction⟩
  rcases htailConstruction useAccept with ⟨tail, htail⟩
  exact
    ⟨SelectedProjectionCheckedEquivPaddedEmitterFromComponents quoter tail,
      selectedProjectionCheckedEquivPaddedEmitterSpec_of_components
        hquoter htail⟩

theorem selectedProjectionEquivEmitterSpec_of_padded
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits : SelectedProjectionEquivPaddedEmitterSpec useAccept emitter) :
    SelectedProjectionEquivEmitterSpec useAccept emitter := by
  constructor
  · exact hemits.left
  constructor
  · intro L
    exact PaddedEquivEmitterSpec.haltsFromTapeEquiv hemits L
  · intro L T hhalt
    exact PaddedEquivEmitterSpec.closedFromTapeEquiv hemits L T hhalt

theorem selectedProjectionEquivEmitterConstruction_of_padded
    (h : SelectedProjectionEquivPaddedEmitterConstruction) :
    SelectedProjectionEquivEmitterConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact ⟨emitter, selectedProjectionEquivEmitterSpec_of_padded hemits⟩

theorem selectedProjectionCheckedEquivEmitterSpec_of_padded
    {useAccept : Bool} {emitter : MachineDescription}
    (hemits :
      SelectedProjectionCheckedEquivPaddedEmitterSpec useAccept emitter) :
    SelectedProjectionCheckedEquivEmitterSpec useAccept emitter := by
  constructor
  · exact hemits.left
  constructor
  · intro L
    exact PaddedEquivEmitterSpec.haltsFromTapeEquiv hemits L
  · intro L T hhalt
    exact PaddedEquivEmitterSpec.closedFromTapeEquiv hemits L T hhalt

theorem selectedProjectionCheckedEquivEmitterConstruction_of_padded
    (h : SelectedProjectionCheckedEquivPaddedEmitterConstruction) :
    SelectedProjectionCheckedEquivEmitterConstruction := by
  intro useAccept
  rcases h useAccept with ⟨emitter, hemits⟩
  exact
    ⟨emitter, selectedProjectionCheckedEquivEmitterSpec_of_padded hemits⟩



theorem selectedProjectionCheckedEquivPaddedEmitterComponentConstruction_scaffold :
    SelectedProjectionCheckedEquivPaddedEmitterComponentConstruction :=
  ⟨selectedProjectionInputQuoterConstruction_scaffold,
    selectedProjectionPaddedTailEmitterConstruction_scaffold⟩

theorem selectedProjectionCheckedEquivPaddedEmitterConstruction_scaffold :
    SelectedProjectionCheckedEquivPaddedEmitterConstruction :=
  selectedProjectionCheckedEquivPaddedEmitterConstruction_of_components
    selectedProjectionCheckedEquivPaddedEmitterComponentConstruction_scaffold

theorem selectedProjectionCheckedEquivEmitterConstruction_scaffold :
    SelectedProjectionCheckedEquivEmitterConstruction :=
  selectedProjectionCheckedEquivEmitterConstruction_of_padded
    selectedProjectionCheckedEquivPaddedEmitterConstruction_scaffold

theorem selectedProjectionFiniteDescriptionConstruction_scaffold :
    SelectedProjectionFiniteDescriptionConstruction :=
  selectedProjectionFiniteDescriptionConstruction_of_checkedEquivEmitter
    selectedProjectionCheckedEquivEmitterConstruction_scaffold

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
