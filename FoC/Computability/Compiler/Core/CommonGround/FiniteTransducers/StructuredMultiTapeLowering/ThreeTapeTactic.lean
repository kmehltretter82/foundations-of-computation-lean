import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ThreeTapeHelpers
import Lean

set_option doc.verso true

/-!
# Three-tape structured proof tactics

Small opt-in tactics for lowerer-facing three-logical-tape proof scripts.
The first tactic deliberately targets local finite-control simplification:
after a row lookup has been resolved, it unfolds the three-tape row/config
constructors and tape actions used by step proofs.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
Simplify local three-tape step goals after the transition lookup has been
resolved.

This tactic is intentionally narrow.  It unfolds lowerer-facing row/config
helpers and executable tape actions, but does not try to prove semantic tape
invariants or search arbitrary transition tables.
-/
macro "three_tape_step" : tactic =>
  `(tactic|
    simp [
      Structured.MultiTapeLowering.ThreeTape.row,
      Structured.MultiTapeLowering.ThreeTape.config,
      Structured.MultiTapeLowering.ThreeTape.description,
      Structured.MultiTapeLowering.ThreeTape.keepL,
      Structured.MultiTapeLowering.ThreeTape.keepR,
      Structured.MultiTapeLowering.ThreeTape.keepS,
      Structured.MultiTapeLowering.ThreeTape.writeL,
      Structured.MultiTapeLowering.ThreeTape.writeR,
      Structured.MultiTapeLowering.ThreeTape.writeS,
      Structured.MultiTapeLowering.ThreeTape.eraseL,
      Structured.MultiTapeLowering.ThreeTape.eraseR,
      Structured.MultiTapeLowering.ThreeTape.writeBitL,
      Structured.MultiTapeLowering.ThreeTape.writeBitR,
      Structured.Description.applyActions_three,
      Structured.TapeAction.apply,
      Structured.TapeAction.stay,
      Structured.HeadMove.apply])

/--
Close one row-support branch for a row table built from
{name}`ThreeTape.allReadRows3`.

Append splitting is intentionally left to the proof script so failures expose
which branch/table does not have the expected shape.
-/
macro "three_tape_support" : tactic =>
  `(tactic|
    exact
      Structured.MultiTapeLowering.ThreeTape.allReadRows3_supportsReadWriteRow3
        _ _ _ _ _ _ ‹_›)

/--
Simplify short fixed-step runs using an explicit list of step lemmas.

The tactic intentionally requires the caller to provide the relevant step
lemmas, so it does not search the environment or unfold large transition
tables.
-/
syntax "three_tape_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| three_tape_run [$lemmas,*]) =>
      `(tactic|
        simp [Structured.Description.runConfig, $lemmas,*])

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
