import FoC.Computability.Compiler.ClosedCfg.TerminalCore.Equiv
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Simulator.PaddedParser.Contracts

set_option doc.verso true

/-!
# Equivalence-valued padded simulator emitter

This is the live adapter route for the #18 terminal core.  It preserves the
exact normalized simulator-layout word and the required head position while
allowing harmless far-edge blank padding in the physical output tape.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

open CommonGround.SeqComposition

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterEquivSpec_configRunner
    (D emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall L : SimulatorLayout,
      emitter.HaltsWithTapeEquiv
        (SimulatorLayout.asBoolInput L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists emitter : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterEquivSpec_configRunner
        D emitter

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalEquivSpec_configRunner
    (D post : MachineDescription) : Prop :=
  post.SubroutineReady ∧
    forall L : SimulatorLayout,
      post.HaltsFromTapeEquiv
        (DovetailInitialLayoutInitializer.tapeAtCells
          ((SimulatorLayout.asBoolInput L).reverse.map some) [])
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalEquivConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists post : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalEquivSpec_configRunner
        D post

theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalEquivConstruction_of_core_configRunner
    (hcore :
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalEquivConstruction_configRunner := by
  intro D
  rcases hcore D with ⟨post, hpost⟩
  refine ⟨post, hpost.left, ?_⟩
  intro L
  simpa [fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner]
    using hpost.right false L

theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterEquivConstruction_of_terminal_configRunner
    (hterminal :
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalEquivConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterEquivConstruction_configRunner := by
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
    rcases hpost.right L with ⟨Tactual, hpostActual, hTactual⟩
    have hscanner := by
      simpa [FixedDescriptionBoundedSimulatorInput] using
        fixedDescriptionBoundedSimulatorLayoutScannerDescription_haltsWithTape_configRunner
          L
    have hseq :
        (seqSubroutine
          FixedDescriptionBoundedSimulatorLayoutScannerDescription_configRunner
          post Direction.right).HaltsWithTape
          (SimulatorLayout.asBoolInput L) Tactual :=
      seqSubroutine_haltsWithTape_of_haltsWithTape_eq
        fixedDescriptionBoundedSimulatorLayoutScannerDescription_subroutineReady_configRunner
        hpost.left hscanner
        (fixedDescriptionBoundedSimulatorLayoutScannerHandoffTapeWithBase_move_right_eq_terminal_configRunner
          L)
        hpostActual
    exact ⟨Tactual, hseq, hTactual⟩

theorem fixedDescriptionBoundedSimulatorPaddedEmitterEquivConstruction_of_scratch_configRunner
    (hemits :
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterEquivConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterEquivConstruction_configRunner := by
  intro D
  rcases hemits D with ⟨emitter, hemitsD⟩
  refine ⟨emitter, hemitsD.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_eq_outputTape_configRunner
      D L] using hemitsD.right L

theorem fixedDescriptionBoundedSimulatorEquivConstruction_of_terminalCoreEquiv_configRunner
    (hcore :
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorEquivConstruction :=
  fixedDescriptionBoundedSimulatorEquivConstruction_of_parserEquivEmitterEquiv_configRunner
    ⟨fixedDescriptionBoundedSimulatorPaddedParserEquivConstruction_scaffold_configRunner,
      fixedDescriptionBoundedSimulatorPaddedEmitterEquivConstruction_of_scratch_configRunner
        (fixedDescriptionBoundedSimulatorPaddedScratchEmitterEquivConstruction_of_terminal_configRunner
          (fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalEquivConstruction_of_core_configRunner
            hcore))⟩

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
