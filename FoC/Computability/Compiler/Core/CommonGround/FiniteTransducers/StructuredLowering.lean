import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Structured

set_option doc.verso true

/-!
# Structured-machine lowering

This module contains the first deliberately small compiler from structured
logical-tape machines back to ordinary
{name (full := FoC.Computability.MachineDescription)}`MachineDescription`s.

The fragment is intentionally narrow: it lowers one-logical-tape machines whose
rows have one read, one action, and a real left/right head move.  This is enough
to replace simple scanner leaves while keeping the proof obligations concrete.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace Lowering

/--
Lower the head movements supported by the first one-tape fragment.

The {lit}`stay` case is rejected for now because the target
{name}`MachineDescription` model always moves after writing.
-/
def lowerHeadMove? : HeadMove -> Option Direction
  | HeadMove.left => some Direction.left
  | HeadMove.right => some Direction.right
  | HeadMove.stay => none

/--
Lower a structured write action on a concrete read cell.  If the structured row
does not request a write, the generated machine row preserves the current cell.
-/
def lowerWrite (read : Option Bool) (action : TapeAction) : Option Bool :=
  match action.write? with
  | none => read
  | some cell => cell

/--
Lower one row of the restricted one-tape fragment.

Rows outside the fragment are skipped by the table compiler.  The caller proves
or tests that the source description belongs to the restricted fragment before
using the lowered machine as an executable replacement.
-/
def lowerTransition? (t : Transition) : Option TransitionDescription :=
  match t.reads, t.actions with
  | [read], [action] =>
      match lowerHeadMove? action.move with
      | none => none
      | some move =>
          some
            { source := t.source
              read := read
              write := lowerWrite read action
              move := move
              target := t.target }
  | _, _ => none

/--
Compile the restricted one-tape fragment to an ordinary
{name}`MachineDescription` transition table.

This definition is intentionally executable and transparent.  Initial users
prove exact lowered tables for concrete machines before adding a more general
semantic preservation theorem.
-/
def toMachineDescription (D : Description) : MachineDescription where
  stateCount := D.stateCount
  start := D.start
  halt := D.halt
  transitions := D.transitions.filterMap lowerTransition?

end Lowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
