import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ThreeTapeHelpers
import Lean

set_option doc.verso true

/-!
# Three-tape structured proof tactics

Small opt-in tactics for lowerer-facing three-logical-tape proof scripts.
The step tactics deliberately target local finite-control simplification:
after a row lookup has been resolved, they unfold the three-tape row/config
constructors, structured transition execution, and tape actions used by step
proofs.  Machine-specific row and configuration definitions stay explicit at
the call site.
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
resolved.  Use {lit}`three_tape_step []` when no machine-specific simp facts
are needed.

This tactic is intentionally narrow.  It unfolds lowerer-facing row/config
helpers and executable tape actions, but does not try to prove semantic tape
invariants or search arbitrary transition tables.
-/
syntax "three_tape_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| three_tape_step [$lemmas,*]) =>
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
          Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.apply,
          Structured.TapeAction.stay,
          Structured.HeadMove.apply,
          Tape.blank,
          Tape.read,
          Tape.write,
          Tape.move,
          Tape.moveLeft,
          Tape.moveRight,
          tapeAtCells,
          $lemmas,*])

/--
Simplify a step goal for a description assembled with three-tape phase helpers.

The bracketed facts should contain the concrete description, phase-local
transition tables, row constructors, configuration/tape shorthands, and any
``no transition at state`` lemmas needed to skip earlier phases.
-/
syntax "three_tape_phase_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| three_tape_phase_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [
          Structured.MultiTapeLowering.ThreeTape.outputFromBits,
          Structured.MultiTapeLowering.ThreeTape.phaseRows,
          Structured.MultiTapeLowering.ThreeTape.offsetRows,
          Structured.MultiTapeLowering.ThreeTape.offsetTransition,
          Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
          Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
          Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
          $lemmas,*])

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
