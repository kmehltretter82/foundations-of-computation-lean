import FoC.Computability.Compiler.ClosedCfg.TerminalCore.Adapters

set_option doc.verso true

/-!
# Equivalence-valued terminal composition

This module carries the honest terminal currency independently of the legacy
exact scratch-wrapper route.  Exact preprocessing may feed an
equivalence-valued body; far-edge blank padding is not normalized merely to
recover one physical representative.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

theorem fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_of_rewind_body_configRunner
    (hrewind :
      FixedDescriptionBoundedSimulatorPaddedEmitterTerminalRewindConstruction_configRunner)
    (hbody :
      FixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_configRunner := by
  intro D
  rcases hrewind with ⟨rewind, hrewind⟩
  rcases hbody D with ⟨body, hbodyD⟩
  refine ⟨SeqViaCanonical rewind body, ?_⟩
  constructor
  · exact SeqViaCanonical_subroutineReady hrewind.left hbodyD.left
  · intro explicitLeftBlank
    intro L
    refine
      SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
        hrewind.left hbodyD.left
        (hrewind.right explicitLeftBlank L).toEquiv ?_
        (hbodyD.right L)
    rw [fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner]
    exact Tape.Equiv.refl _

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
