import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.Shape

set_option doc.verso true

/-!
This module states the contracts for padded selected-projection tail cleanup.
It separates the emitter-facing specification, the cleanup subroutine
specification, and the exact-shape construction that links the two.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

def SelectedProjectionPaddedTailEmitterSpec
    (useAccept : Bool)
    (tail : MachineDescription) : Prop :=
  tail.SubroutineReady ∧
    forall L : DovetailLayout,
      tail.HaltsFromTapeEquiv
        (SelectedProjectionTailProjector.sourceTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionPaddedTailEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists tail : MachineDescription,
      SelectedProjectionPaddedTailEmitterSpec useAccept tail

def SelectedProjectionPaddedTailCleanupSpec
    (useAccept : Bool)
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall L : DovetailLayout,
      cleanup.HaltsFromTapeEquiv
        (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
          ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
            some))
        (SelectedProjectionEquivEmitterPaddedOutputTape useAccept L)

def SelectedProjectionPaddedTailCleanupConstruction : Prop :=
  forall useAccept : Bool,
    exists cleanup : MachineDescription,
      SelectedProjectionPaddedTailCleanupSpec useAccept cleanup

def SelectedProjectionPaddedTailCleanupExactShapeSpec
    (useAccept : Bool)
    (cleanup : MachineDescription) : Prop :=
  cleanup.SubroutineReady ∧
    forall L : DovetailLayout,
      cleanup.HaltsFromTapeEquiv
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
  exact hcleanup

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
  · intro L
    have hscanner :
        CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription.HaltsFromTape
          (SelectedProjectionTailProjector.sourceTape L (baseLeft L))
          (SelectedProjectionTailProjector.sourceScannerHandoffTape L
            (baseLeft L)) :=
      SelectedProjectionTailProjector.sourceScanner_haltsFromTape_withBase
        L (baseLeft L)
    simpa [SelectedProjectionPaddedTailEmitterFromCleanup, baseLeft,
      List.map_reverse] using
      CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
        (A :=
          CanonicalLayouts.DovetailLayoutScanner.StageConfigurationsAndFinalFlagsScannerDescription)
        (B := cleanup)
        (handoffMove := Direction.right)
        CanonicalLayouts.DovetailLayoutScanner.stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hcleanup.left hscanner
        (by
          rfl)
        (by
          simpa [baseLeft,
            SelectedProjectionTailProjector.sourceScannerRightHandoffTape,
            List.map_reverse] using
            hcleanup.right L)

theorem selectedProjectionPaddedTailEmitterConstruction_of_cleanup
    (hcleanup : SelectedProjectionPaddedTailCleanupConstruction) :
    SelectedProjectionPaddedTailEmitterConstruction := by
  intro useAccept
  rcases hcleanup useAccept with ⟨cleanup, hcleanup⟩
  exact
    ⟨SelectedProjectionPaddedTailEmitterFromCleanup useAccept cleanup,
      selectedProjectionPaddedTailEmitterSpec_of_cleanup hcleanup⟩


end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
