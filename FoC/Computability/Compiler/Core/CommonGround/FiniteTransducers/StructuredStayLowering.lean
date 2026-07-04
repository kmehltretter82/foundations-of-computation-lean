import FoC.Computability.MachineDescriptionWithStay
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredLowering
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Structured

set_option doc.verso true

/-!
# Structured stay-machine lowering

This module lowers the one-logical-tape structured fragment to
{name}`FoC.Computability.MachineDescriptionWithStay`.  Unlike
{module}`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredLowering`,
this path accepts
{name (full := FoC.Computability.CommonGround.FiniteTransducers.Structured.HeadMove.stay)}`HeadMove.stay`
and then compiles through the
ordinary left/right-only {name}`FoC.Computability.MachineDescription` layer.

The final ordinary machine is therefore an equivalence-oriented lowering path:
compiled stay moves may introduce stored edge blanks, so users should prefer
{name}`FoC.Computability.MachineDescription.HaltsFromTapeEquiv` contracts when
they cross this boundary.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace StayLowering

/-- Lower a structured head move to the stay-capable intermediate layer. -/
def lowerHeadMove : HeadMove -> StayDirection
  | HeadMove.stay => StayDirection.stay
  | HeadMove.left => StayDirection.left
  | HeadMove.right => StayDirection.right

@[simp] theorem lowerHeadMove_stay :
    lowerHeadMove HeadMove.stay = StayDirection.stay := by
  rfl

@[simp] theorem lowerHeadMove_left :
    lowerHeadMove HeadMove.left = StayDirection.left := by
  rfl

@[simp] theorem lowerHeadMove_right :
    lowerHeadMove HeadMove.right = StayDirection.right := by
  rfl

/--
Lower a structured write action on a concrete read cell.  Missing writes
preserve the read cell, matching the ordinary transition-table convention.
-/
def lowerWrite (read : Option Bool) (action : TapeAction) : Option Bool :=
  match action.write? with
  | none => read
  | some cell => cell

@[simp] theorem lowerWrite_preserve
    (read : Option Bool) (move : HeadMove) :
    lowerWrite read (TapeAction.preserveMove move) = read := by
  rfl

@[simp] theorem lowerWrite_record_preserve
    (read : Option Bool) (move : HeadMove) :
    lowerWrite read ({ write? := none, move := move } : TapeAction) =
      read := by
  rfl

@[simp] theorem lowerWrite_write
    (read cell : Option Bool) (move : HeadMove) :
    lowerWrite read (TapeAction.writeMove cell move) = cell := by
  rfl

@[simp] theorem lowerWrite_record_write
    (read cell : Option Bool) (move : HeadMove) :
    lowerWrite read
        ({ write? := some cell, move := move } : TapeAction) =
      cell := by
  rfl

/--
Lower one structured one-tape row to the stay-capable transition table.

Rows outside the one-tape fragment are skipped, mirroring the exact
left/right-only lowerer.
-/
@[simp] def lowerTransition? (t : Transition) :
    Option StayTransitionDescription :=
  match t.reads, t.actions with
  | [read], [action] =>
      some
        { source := t.source
          read := read
          write := lowerWrite read action
          move := lowerHeadMove action.move
          target := t.target }
  | _, _ => none

@[simp] theorem lowerTransition_oneTape_preserve
    (source : Nat) (read : Option Bool)
    (move : HeadMove) (target : Nat) :
    lowerTransition?
        (Structured.OneTape.preserve source read move target) =
      some
        { source := source
          read := read
          write := read
          move := lowerHeadMove move
          target := target } := by
  rfl

@[simp] theorem lowerTransition_oneTape_write
    (source : Nat) (read cell : Option Bool)
    (move : HeadMove) (target : Nat) :
    lowerTransition?
        (Structured.OneTape.write source read cell move target) =
      some
        { source := source
          read := read
          write := cell
          move := lowerHeadMove move
          target := target } := by
  rfl

@[simp] theorem lowerTransition_oneTape_erase
    (source : Nat) (read : Option Bool)
    (move : HeadMove) (target : Nat) :
    lowerTransition?
        (Structured.OneTape.erase source read move target) =
      some
        { source := source
          read := read
          write := none
          move := lowerHeadMove move
          target := target } := by
  rfl

/-- Compile the supported one-tape structured fragment to the stay layer. -/
def toMachineDescriptionWithStay
    (D : Description) : MachineDescriptionWithStay where
  stateCount := D.stateCount
  start := D.start
  halt := D.halt
  transitions := D.transitions.filterMap lowerTransition?

@[simp] theorem toMachineDescriptionWithStay_stateCount
    (D : Description) :
    (toMachineDescriptionWithStay D).stateCount = D.stateCount := by
  rfl

@[simp] theorem toMachineDescriptionWithStay_start
    (D : Description) :
    (toMachineDescriptionWithStay D).start = D.start := by
  rfl

@[simp] theorem toMachineDescriptionWithStay_halt
    (D : Description) :
    (toMachineDescriptionWithStay D).halt = D.halt := by
  rfl

@[simp] theorem toMachineDescriptionWithStay_transitions
    (D : Description) :
    (toMachineDescriptionWithStay D).transitions =
      D.transitions.filterMap lowerTransition? := by
  rfl

/--
Compile through the stay-capable layer to an ordinary left/right-only
{name}`MachineDescription`.
-/
def toMachineDescription (D : Description) : MachineDescription :=
  (toMachineDescriptionWithStay D).compile

@[simp] theorem toMachineDescription_stateCount
    (D : Description) :
    (toMachineDescription D).stateCount =
      D.stateCount + (D.transitions.filterMap lowerTransition?).length := by
  rfl

@[simp] theorem toMachineDescription_start
    (D : Description) :
    (toMachineDescription D).start = D.start := by
  rfl

@[simp] theorem toMachineDescription_halt
    (D : Description) :
    (toMachineDescription D).halt = D.halt := by
  rfl

/-!
## Stay lowering smoke test
-/

/-- The structured version of the one-row stay example. -/
def oneRowStayDescription
    (read write : Option Bool) : Description where
  tapeCount := 1
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [Structured.OneTape.write 0 read write HeadMove.stay 1]

theorem oneRowStayDescription_haltsFromTapeEquiv
    (read write : Option Bool)
    (left right : List (Option Bool)) :
    (toMachineDescription (oneRowStayDescription read write)).HaltsFromTapeEquiv
        (MachineDescriptionWithStay.singleStaySourceTape read left right)
        (MachineDescriptionWithStay.singleStayTargetTape write left right) := by
  simpa [toMachineDescription, toMachineDescriptionWithStay,
    oneRowStayDescription, lowerTransition?, lowerHeadMove, lowerWrite]
    using
      MachineDescriptionWithStay.compile_singleStayDescription_haltsFromTapeEquiv
          read write left right

end StayLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
