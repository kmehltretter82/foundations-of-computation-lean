import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.InputMaterializer
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.MetadataPrefixRuns
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.SelectorSpliceRuns
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.PhaseAdapters

set_option doc.verso true

/-!
# Full fixed-description run-config emitter pipeline

This module composes the checked #18 phases in their dependency order.  The
configuration/hit boundary and guarded egress remain explicit components so
their finite leaves can be proved independently.  Every same-head handoff uses
the canonical right/left bounce and transports the intermediate endpoint in
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv` currency.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace FullPipeline

open Languages MachineDescription
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-!
## Checked decomposition prefix
-/

def prefixDescription (D : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    (SeqViaCanonical
      (SeqViaCanonical
        (SeqViaCanonical InputMaterializer.description
          FieldDecomposition.SourceCounter.loweredDescription)
        FieldDecomposition.StageCounter.loweredDescription)
      (FieldDecomposition.StateSelector.loweredDescription D))
    FieldDecomposition.MetadataPrefix.loweredDescription

theorem prefixDescription_subroutineReady (D : MachineDescription) :
    (prefixDescription D).SubroutineReady := by
  exact
    SeqViaCanonical_subroutineReady
      (SeqViaCanonical_subroutineReady
        (SeqViaCanonical_subroutineReady
          (SeqViaCanonical_subroutineReady
            InputMaterializer.description_subroutineReady
            FieldDecomposition.SourceCounter.loweredDescription_subroutineReady)
          FieldDecomposition.StageCounter.loweredDescription_subroutineReady)
        (FieldDecomposition.StateSelector.loweredDescription_subroutineReady D))
      FieldDecomposition.MetadataPrefix.loweredDescription_subroutineReady

theorem prefixDescription_haltsFromTapeEquiv
    (D : MachineDescription) (L : SimulatorLayout) :
    (prefixDescription D).HaltsFromTapeEquiv
      (InputMaterializer.rightEndLeftSourceTape
        (SimulatorLayout.asBoolInput L))
      (FieldDecomposition.MetadataPrefix.targetTape D L) := by
  have hmaterialize :
      InputMaterializer.description.HaltsFromTapeEquiv
        (InputMaterializer.rightEndLeftSourceTape
          (SimulatorLayout.asBoolInput L))
        (FieldDecomposition.embeddedSourceTape L) := by
    simpa [FieldDecomposition.embeddedSourceTape] using
      InputMaterializer.description_haltsFromTapeEquiv
        (SimulatorLayout.asBoolInput L)
        (RunConfigEmitterTheory.simulatorLayout_asBoolInput_ne_nil L)
  have hsource :=
    FieldDecomposition.SourceCounter.loweredDescription_haltsFromTapeEquiv L
  have hstage :=
    FieldDecomposition.StageCounter.loweredDescription_haltsFromTapeEquiv L
  have hselector :=
    FieldDecomposition.StateSelector.loweredDescription_haltsFromTapeEquiv D L
  have hmetadata :=
    FieldDecomposition.MetadataPrefix.loweredDescription_haltsFromTapeEquiv D L
  have h01 :=
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      InputMaterializer.description_subroutineReady
      FieldDecomposition.SourceCounter.loweredDescription_subroutineReady
      hmaterialize
      (moveLeft_moveRight_equiv_self
        (FieldDecomposition.embeddedSourceTape L))
      hsource
  have h012 :=
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      (SeqViaCanonical_subroutineReady
        InputMaterializer.description_subroutineReady
        FieldDecomposition.SourceCounter.loweredDescription_subroutineReady)
      FieldDecomposition.StageCounter.loweredDescription_subroutineReady
      h01
      (moveLeft_moveRight_equiv_self
        (FieldDecomposition.SourceCounter.targetTape L))
      hstage
  have h0123 :=
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      (SeqViaCanonical_subroutineReady
        (SeqViaCanonical_subroutineReady
          InputMaterializer.description_subroutineReady
          FieldDecomposition.SourceCounter.loweredDescription_subroutineReady)
        FieldDecomposition.StageCounter.loweredDescription_subroutineReady)
      (FieldDecomposition.StateSelector.loweredDescription_subroutineReady D)
      h012
      (moveLeft_moveRight_equiv_self
        (FieldDecomposition.StageCounter.targetTape L))
      hselector
  have h01234 :=
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      (SeqViaCanonical_subroutineReady
        (SeqViaCanonical_subroutineReady
          (SeqViaCanonical_subroutineReady
            InputMaterializer.description_subroutineReady
            FieldDecomposition.SourceCounter.loweredDescription_subroutineReady)
          FieldDecomposition.StageCounter.loweredDescription_subroutineReady)
        (FieldDecomposition.StateSelector.loweredDescription_subroutineReady D))
      FieldDecomposition.MetadataPrefix.loweredDescription_subroutineReady
      h0123
      (moveLeft_moveRight_equiv_self
        (FieldDecomposition.StateSelector.targetTape D L))
      hmetadata
  exact h01234

/-!
## Remaining canonical components
-/

/-- The repaired configuration/hit component ends at the exact canonical
classified source used by the selector splice. -/
def CanonicalCfgHitSpec
    (D cfgHit : MachineDescription) : Prop :=
  cfgHit.SubroutineReady ∧
    forall L : SimulatorLayout,
      cfgHit.HaltsFromTapeEquiv
        (FieldDecomposition.MetadataPrefix.targetTape D L)
        (encodedGuardedStructuredTapes
          (FieldDecomposition.ClassifiedBoundary.classifiedLoopTapes D L))

def CanonicalCfgHitConstruction : Prop :=
  forall D : MachineDescription,
    exists cfgHit : MachineDescription, CanonicalCfgHitSpec D cfgHit

structure Components (D : MachineDescription) where
  cfgHit : MachineDescription
  cfgHitSpec : CanonicalCfgHitSpec D cfgHit
  egress : MachineDescription
  egressSpec : GuardedEgress.Spec egress

def description (D : MachineDescription) (C : Components D) :
    MachineDescription :=
  SeqViaCanonical
    (SeqViaCanonical
      (SeqViaCanonical (prefixDescription D) C.cfgHit)
        (SelectorSplice.loweredDescription D))
    C.egress

theorem description_subroutineReady
    (D : MachineDescription) (C : Components D) :
    (description D C).SubroutineReady := by
  exact
    SeqViaCanonical_subroutineReady
      (SeqViaCanonical_subroutineReady
        (SeqViaCanonical_subroutineReady
          (prefixDescription_subroutineReady D) C.cfgHitSpec.left)
        (SelectorSplice.loweredDescription_subroutineReady D))
      C.egressSpec.left

theorem description_haltsFromTapeEquiv
    (D : MachineDescription) (C : Components D)
    (L : SimulatorLayout) :
    (description D C).HaltsFromTapeEquiv
      (InputMaterializer.rightEndLeftSourceTape
        (SimulatorLayout.asBoolInput L))
      (GuardedEgress.Index.target ⟨D, L⟩) := by
  let i : GuardedEgress.Index := ⟨D, L⟩
  have hprefix := prefixDescription_haltsFromTapeEquiv D L
  have hcfg := C.cfgHitSpec.right L
  have hselector := SelectorSplice.loweredDescription_haltsFromTapeEquiv D L
  have hegress := C.egressSpec.canonical i
  have hprefixCfg :=
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      (prefixDescription_subroutineReady D) C.cfgHitSpec.left
      hprefix
      (moveLeft_moveRight_equiv_self
        (FieldDecomposition.MetadataPrefix.targetTape D L))
      hcfg
  have hthroughSelector :=
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      (SeqViaCanonical_subroutineReady
        (prefixDescription_subroutineReady D) C.cfgHitSpec.left)
      (SelectorSplice.loweredDescription_subroutineReady D)
      hprefixCfg
      (moveLeft_moveRight_equiv_self
        (encodedGuardedStructuredTapes
          (FieldDecomposition.ClassifiedBoundary.classifiedLoopTapes D L)))
      (by
        simpa [FieldDecomposition.ClassifiedBoundary.classifiedLoopTapes]
          using hselector)
  have hfull :=
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      (SeqViaCanonical_subroutineReady
        (SeqViaCanonical_subroutineReady
          (prefixDescription_subroutineReady D) C.cfgHitSpec.left)
        (SelectorSplice.loweredDescription_subroutineReady D))
      C.egressSpec.left
      hthroughSelector
      (by
        simpa [i, GuardedEgress.Index.source,
          GuardedEgress.Index.logicalTapes] using
          moveLeft_moveRight_equiv_self
            (encodedGuardedStructuredTapes
              (loopDispatcherDoneWitnessTapes D L)))
      hegress
  exact hfull

def Spec
    (D runner : MachineDescription) : Prop :=
  runner.SubroutineReady ∧
    forall L : SimulatorLayout,
      runner.HaltsFromTapeEquiv
        (InputMaterializer.rightEndLeftSourceTape
          (SimulatorLayout.asBoolInput L))
        (GuardedEgress.Index.target ⟨D, L⟩)

def Construction : Prop :=
  forall D : MachineDescription,
    exists runner : MachineDescription, Spec D runner

theorem construction_of_components
    (hcfg : CanonicalCfgHitConstruction)
    (hegress : GuardedEgress.Construction) : Construction := by
  intro D
  rcases hcfg D with ⟨cfgHit, hcfgHit⟩
  rcases hegress with ⟨egress, hegressSpec⟩
  let C : Components D := ⟨cfgHit, hcfgHit, egress, hegressSpec⟩
  exact
    ⟨description D C, description_subroutineReady D C,
      description_haltsFromTapeEquiv D C⟩

end FullPipeline
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
