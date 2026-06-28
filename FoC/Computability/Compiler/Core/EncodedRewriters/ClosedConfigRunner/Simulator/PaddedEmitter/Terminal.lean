import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.Shape
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedParser

set_option doc.verso true

/-!
# Padded simulator scaffold emitter terminal contract
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

open CommonGround.SeqComposition

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeSpec_configRunner
    (D emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall L : SimulatorLayout,
      emitter.HaltsWithTape
        (SimulatorLayout.asBoolInput L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists emitter : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeSpec_configRunner
        D emitter

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalSpec_configRunner
    (D post : MachineDescription) : Prop :=
  post.SubroutineReady ∧
    forall L : SimulatorLayout,
      post.HaltsFromTape
        (DovetailInitialLayoutInitializer.tapeAtCells
          ((SimulatorLayout.asBoolInput L).reverse.map some) [])
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists post : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalSpec_configRunner
        D post

theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_of_terminal_configRunner
    (hterminal :
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterExactShapeConstruction_configRunner := by
  intro D
  rcases hterminal D with ⟨post, hpost⟩
  refine
    ⟨seqSubroutine
      FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner
      post Direction.right, ?_⟩
  constructor
  · exact
      seqSubroutine_subroutineReady
        fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner
        hpost.left
  · intro L
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape_eq
        fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner
        hpost.left
        (by
          simpa [FixedDescriptionBoundedSimulatorInput] using
            fixedDescriptionBoundedSimulatorLayoutScannerDescription_haltsWithTape_configRunner
              L)
        (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_move_right_eq_terminal_configRunner
          L)
        (hpost.right L)

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
