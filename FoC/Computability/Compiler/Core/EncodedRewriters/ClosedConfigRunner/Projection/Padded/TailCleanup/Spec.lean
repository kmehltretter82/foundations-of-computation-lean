import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.Shape

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SelectedProjectionPaddedTailEmitterSpec
    (useAccept : Bool)
    (tail : MachineDescription) : Prop :=
  RightScratchPaddedEmitterSpec
    (fun L : DovetailLayout =>
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)))
    (fun L : DovetailLayout =>
      encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
    (fun L : DovetailLayout =>
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
    (fun L : DovetailLayout =>
        (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some)))
    (fun L : DovetailLayout =>
      encodeCodeWordAsInput
        (SelectedProjectionOutputCode useAccept L))
    (fun L : DovetailLayout =>
      (ParsedLayoutBits L).length)
    (SelectedProjectionOutputTape useAccept)
    cleanup

def SelectedProjectionPaddedTailCleanupConstruction : Prop :=
  forall useAccept : Bool,
    exists cleanup : MachineDescription,
      SelectedProjectionPaddedTailCleanupSpec useAccept cleanup

def SelectedProjectionPaddedTailCleanupExactShapeSpec
    (useAccept : Bool)
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall L : DovetailLayout,
      cleanup.HaltsFromTape
        (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionPaddedTailCleanupExactShapeConstruction : Prop :=
  forall useAccept : Bool,
    exists cleanup : MachineDescription,
      SelectedProjectionPaddedTailCleanupExactShapeSpec useAccept cleanup

theorem selectedProjectionPaddedTailCleanupSpec_of_exactShape
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup :
      SelectedProjectionPaddedTailCleanupExactShapeSpec useAccept cleanup) :
    SelectedProjectionPaddedTailCleanupSpec useAccept cleanup := by
  constructor
  · exact hcleanup.left
  constructor
  · intro L
    simpa [SelectedProjectionPaddedTailCleanupSpec,
      SelectedProjectionEquivEmitterPaddedOutputTape] using
      hcleanup.right L
  · intro L
    exact SelectedProjectionEquivEmitterPaddedOutputTape_equiv useAccept L

theorem selectedProjectionPaddedTailCleanupConstruction_of_exactShape
    (hcleanup :
      SelectedProjectionPaddedTailCleanupExactShapeConstruction) :
    SelectedProjectionPaddedTailCleanupConstruction := by
  intro useAccept
  rcases hcleanup useAccept with ⟨cleanup, hcleanup⟩
  exact
    ⟨cleanup,
      selectedProjectionPaddedTailCleanupSpec_of_exactShape hcleanup⟩

def SelectedProjectionPaddedTailEmitterFromCleanup
    (_useAccept : Bool)
    (cleanup : MachineDescription) : MachineDescription :=
  seqSubroutine
    CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription
    cleanup Direction.right

theorem selectedProjectionPaddedTailEmitterSpec_of_cleanup
    {useAccept : Bool} {cleanup : MachineDescription}
    (hcleanup : SelectedProjectionPaddedTailCleanupSpec useAccept cleanup) :
    SelectedProjectionPaddedTailEmitterSpec useAccept
      (SelectedProjectionPaddedTailEmitterFromCleanup useAccept
        cleanup) := by
  let baseLeft :=
    fun L : DovetailLayout =>
      (SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
        some
  constructor
  · exact
      seqSubroutine_subroutineReady
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
          runConfig_eq_halt_of_haltsFromTape
            (hcleanup.right.left L)
    simpa [SelectedProjectionPaddedTailEmitterFromCleanup, baseLeft,
      List.map_reverse] using
      seqSubroutine_haltsFromTape_of_haltsFromTape
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


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
