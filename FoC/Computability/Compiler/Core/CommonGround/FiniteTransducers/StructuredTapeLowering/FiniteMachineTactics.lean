import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.CursorBasic
import Lean

set_option doc.verso true

/-!
# Small finite-machine proof tactics

Small opt-in tactics for concrete one-tape
{name (full := FoC.Computability.MachineDescription)}`MachineDescription` proof
scripts.  These mirror the style of the structured three-tape tactics: callers
provide machine-specific definitions or step lemmas explicitly, while the tactic
only unfolds common execution and tape-motion boilerplate.
-/

namespace FoC
namespace Computability

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
Simplify concrete finite-machine execution goals.

Use {lit}`machine_step []` when no machine-specific simp facts are needed.  This
tactic is intentionally narrow: it unfolds one-tape execution and tape-view
helpers, but does not search transition tables, split cases, or prove semantic
list invariants.
-/
syntax "machine_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| machine_step [$lemmas,*]) =>
      `(tactic|
        simp [MachineDescription.runConfig,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition,
          MachineDescription.Matches,
          MachineDescription.transition,
          Tape.blank,
          Tape.read,
          Tape.write,
          Tape.move,
          Tape.moveLeft,
          Tape.moveRight,
          tapeAtCells,
          $lemmas,*])

/--
Simplify short fixed-step runs using an explicit list of step/run lemmas.

The tactic deliberately requires callers to supply the relevant lemmas, so
failures identify which local machine step still needs a named fact.
-/
syntax "machine_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| machine_run [$lemmas,*]) =>
      `(tactic|
        simp [MachineDescription.runConfig, $lemmas,*])

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
