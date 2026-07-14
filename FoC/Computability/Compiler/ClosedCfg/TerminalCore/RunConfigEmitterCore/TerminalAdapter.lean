import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FullPipeline

set_option doc.verso true

/-!
# Terminal adapter for the fixed-description run-config pipeline

The guarded egress parks one cell to the right of the exact output word.  This
module performs the final checked left move and exposes the honest
equivalence-valued body contract consumed by the terminal wrapper.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace FullPipeline

open Languages MachineDescription
open CommonGround.FiniteTransducers

theorem target_eq_rightScratchTape
    (D : MachineDescription) (L : SimulatorLayout) :
    GuardedEgress.Index.target ⟨D, L⟩ =
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
        D L := by
  rw [GuardedEgress.Index.target_eq_semantic]
  exact ExactCloseout.semanticFields_rightScratchTape_eq D L

def terminalDescription
    (runner : MachineDescription) : MachineDescription :=
  SeqViaCanonical runner leftMoveOnceDescription

theorem terminalDescription_subroutineReady
    {runner : MachineDescription} (hrunner : runner.SubroutineReady) :
    (terminalDescription runner).SubroutineReady := by
  exact
    SeqViaCanonical_subroutineReady hrunner
      leftMoveOnceDescription_subroutineReady

theorem leftMoveOnceDescription_haltsFrom_target
    (D : MachineDescription) (L : SimulatorLayout) :
    leftMoveOnceDescription.HaltsFromTapeEquiv
      (GuardedEgress.Index.target ⟨D, L⟩)
      (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
        D L) := by
  simpa only [target_eq_rightScratchTape,
    fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_move_left_configRunner]
    using
      (leftMoveOnceDescription_haltsFromTape
        (GuardedEgress.Index.target ⟨D, L⟩)).toEquiv

theorem terminalDescription_haltsFromTapeEquiv
    {D runner : MachineDescription} (hrunner : Spec D runner)
    (L : SimulatorLayout) :
    (terminalDescription runner).HaltsFromTapeEquiv
      (InputMaterializer.rightEndLeftSourceTape
        (SimulatorLayout.asBoolInput L))
      (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
        D L) := by
  exact
    SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
      hrunner.left leftMoveOnceDescription_subroutineReady
      (hrunner.right L)
      (moveLeft_moveRight_equiv_self
        (GuardedEgress.Index.target ⟨D, L⟩))
      (leftMoveOnceDescription_haltsFrom_target D L)

def TerminalSpec
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTapeEquiv
        (InputMaterializer.rightEndLeftSourceTape
          (SimulatorLayout.asBoolInput L))
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def TerminalConstruction : Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription, TerminalSpec D body

theorem terminalConstruction_of_fullPipeline
    (hfull : Construction) : TerminalConstruction := by
  intro D
  rcases hfull D with ⟨runner, hrunner⟩
  exact
    ⟨terminalDescription runner,
      terminalDescription_subroutineReady hrunner.left,
      terminalDescription_haltsFromTapeEquiv hrunner⟩

end FullPipeline
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
