import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.ProjectionPadded.Shape

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionPaddedTailEmitterSpec
    (useAccept : Bool)
    (tail : MachineDescription) : Prop :=
  RightScratchPaddedEmitterSpec
    (fun L : MachineDescription.DovetailLayout =>
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)))
    (fun L : MachineDescription.DovetailLayout =>
      MachineDescription.encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
    (fun L : MachineDescription.DovetailLayout =>
      (ParsedLayoutBits L).length)
    (SelectedProjectionOutputTape useAccept)
    tail

def SelectedProjectionPaddedTailEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists tail : MachineDescription,
      SelectedProjectionPaddedTailEmitterSpec useAccept tail

def SelectedProjectionPaddedTailCleanupSpec
    (useAccept : Bool)
    (cleanup : MachineDescription) : Prop :=
  RightScratchPaddedEmitterSpec
    (fun L : MachineDescription.DovetailLayout =>
        (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)))
    (fun L : MachineDescription.DovetailLayout =>
      MachineDescription.encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
    (fun L : MachineDescription.DovetailLayout =>
      (ParsedLayoutBits L).length)
    (SelectedProjectionOutputTape useAccept)
    cleanup

def SelectedProjectionPaddedTailCleanupConstruction : Prop :=
  forall useAccept : Bool,
    exists cleanup : MachineDescription,
      SelectedProjectionPaddedTailCleanupSpec useAccept cleanup

def SelectedProjectionPaddedTailEmitterFromCleanup
    (_useAccept : Bool)
    (cleanup : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription
    cleanup Direction.right

theorem selectedProjectionPaddedTailEmitterSpec_of_cleanup
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup : SelectedProjectionPaddedTailCleanupSpec useAccept cleanup) :
    SelectedProjectionPaddedTailEmitterSpec useAccept
      (SelectedProjectionPaddedTailEmitterFromCleanup useAccept
        cleanup) := by
  let baseLeft :=
    fun L : MachineDescription.DovetailLayout =>
      (SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
        some
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        CanonicalLayouts.DovetailLayoutScanner.stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hcleanup.left
  constructor
  · intro L
    have hscanner :
        CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription.HaltsFromTape
          (SelectedProjectionTailProjector.sourceTape L (baseLeft L))
          (SelectedProjectionTailProjector.sourceScannerHandoffTape L
            (baseLeft L)) :=
      SelectedProjectionTailProjector.sourceScanner_haltsFromTape_withBase
        L (baseLeft L)
    have hcleanupRun :
        exists nB : Nat,
          cleanup.runConfig nB
              { state := cleanup.start
                tape :=
                  Tape.move Direction.right
                    (SelectedProjectionTailProjector.sourceScannerHandoffTape
                      L (baseLeft L)) } =
            { state := cleanup.halt
              tape := SelectedProjectionEquivEmitterPaddedOutputTape
                useAccept L } := by
      simpa [baseLeft,
        SelectedProjectionTailProjector.sourceScannerRightHandoffTape,
        List.map_reverse]
        using
          MachineDescription.runConfig_eq_halt_of_haltsFromTape
            (hcleanup.right.left L)
    simpa [SelectedProjectionPaddedTailEmitterFromCleanup, baseLeft,
      List.map_reverse] using
      MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
        (A :=
          CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription)
        (B := cleanup)
        (handoffMove := Direction.right)
        CanonicalLayouts.DovetailLayoutScanner.stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hcleanup.left hscanner hcleanupRun
  · intro L
    exact SelectedProjectionEquivEmitterPaddedOutputTape_equiv useAccept L

theorem selectedProjectionPaddedTailEmitterConstruction_of_cleanup
    (hcleanup : SelectedProjectionPaddedTailCleanupConstruction) :
    SelectedProjectionPaddedTailEmitterConstruction := by
  intro useAccept
  rcases hcleanup useAccept with ⟨cleanup, hcleanup⟩
  exact
    ⟨SelectedProjectionPaddedTailEmitterFromCleanup useAccept cleanup,
      selectedProjectionPaddedTailEmitterSpec_of_cleanup hcleanup⟩



/--
Finite-machine leaf for the selected-projection tail cleanup.  The reusable
stage/configuration/final-flag scanner has already consumed the remaining
layout fields and handed off one cell to the right; this cleanup may leave
trailing blank padding while emitting a tape equivalent to the right-shifted
selected simulator-layout output.
-/
theorem selectedProjectionPaddedTailCleanupConstruction_scaffold :
    SelectedProjectionPaddedTailCleanupConstruction := by
  sorry

theorem selectedProjectionPaddedTailEmitterConstruction_scaffold :
    SelectedProjectionPaddedTailEmitterConstruction :=
  selectedProjectionPaddedTailEmitterConstruction_of_cleanup
    selectedProjectionPaddedTailCleanupConstruction_scaffold

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
