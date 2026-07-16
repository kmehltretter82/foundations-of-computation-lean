import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.ActionState

namespace FoC
namespace Computability

open Languages

namespace Section53RuntimeTapeUpdateShapes

/-!
**Runtime tape-update shapes.** These semantic and serialized lemmas expose the
four physical motion cases without placing the runtime state or either logical
context in finite control.
-/

abbrev Action := Section53RuntimeStateCompactor.Action

def apply (action : Action) (tape : Tape Bool) : Tape Bool :=
  Tape.move action.move (Tape.write action.write tape)

def sourceWord
    (state : Nat) (tape : Tape Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend state
    (MachineDescription.encodeTapeAppend tape suffix)

def targetWord
    (state : Nat) (action : Action) (tape : Tape Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend state
    (MachineDescription.encodeTapeAppend (apply action tape) suffix)

theorem apply_left_empty
    (write head : Option Bool)
    (right : List (Option Bool)) :
    apply { write := write, move := Direction.left }
        { left := [], head := head, right := right } =
      { left := [], head := none, right := write :: right } := by
  rfl

theorem apply_left_nonempty
    (write head nextHead : Option Bool)
    (remainingLeft right : List (Option Bool)) :
    apply { write := write, move := Direction.left }
        { left := nextHead :: remainingLeft, head := head, right := right } =
      { left := remainingLeft, head := nextHead,
        right := write :: right } := by
  rfl

theorem apply_right_empty
    (write head : Option Bool)
    (left : List (Option Bool)) :
    apply { write := write, move := Direction.right }
        { left := left, head := head, right := [] } =
      { left := write :: left, head := none, right := [] } := by
  rfl

theorem apply_right_nonempty
    (write head nextHead : Option Bool)
    (left remainingRight : List (Option Bool)) :
    apply { write := write, move := Direction.right }
        { left := left, head := head, right := nextHead :: remainingRight } =
      { left := write :: left, head := nextHead,
        right := remainingRight } := by
  rfl

theorem encodeTapeAppend_left_empty_target
    (write head : Option Bool)
    (right : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeTapeAppend
        (apply { write := write, move := Direction.left }
          { left := [], head := head, right := right }) suffix =
      MachineDescription.encodeCellListAppend []
        (MachineDescription.encodeCellAppend none
          (MachineDescription.encodeCellListAppend (write :: right)
            suffix)) := by
  rfl

theorem encodeTapeAppend_left_nonempty_target
    (write head nextHead : Option Bool)
    (remainingLeft right : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeTapeAppend
        (apply { write := write, move := Direction.left }
          { left := nextHead :: remainingLeft, head := head,
            right := right }) suffix =
      MachineDescription.encodeCellListAppend remainingLeft
        (MachineDescription.encodeCellAppend nextHead
          (MachineDescription.encodeCellListAppend (write :: right)
            suffix)) := by
  rfl

theorem encodeTapeAppend_right_empty_target
    (write head : Option Bool)
    (left : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeTapeAppend
        (apply { write := write, move := Direction.right }
          { left := left, head := head, right := [] }) suffix =
      MachineDescription.encodeCellListAppend (write :: left)
        (MachineDescription.encodeCellAppend none
          (MachineDescription.encodeCellListAppend [] suffix)) := by
  rfl

theorem encodeTapeAppend_right_nonempty_target
    (write head nextHead : Option Bool)
    (left remainingRight : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeTapeAppend
        (apply { write := write, move := Direction.right }
          { left := left, head := head,
            right := nextHead :: remainingRight }) suffix =
      MachineDescription.encodeCellListAppend (write :: left)
        (MachineDescription.encodeCellAppend nextHead
          (MachineDescription.encodeCellListAppend remainingRight
            suffix)) := by
  rfl

theorem encodeCellsAppend_cons
    (cell : Option Bool) (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeCellsAppend (cell :: cells) suffix =
      MachineDescription.encodeCellAppend cell
        (MachineDescription.encodeCellsAppend cells suffix) := by
  rfl

theorem encodeCellListAppend_cons
    (cell : Option Bool) (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeCellListAppend (cell :: cells) suffix =
      MachineDescription.encodeNatAppend (cells.length + 1)
        (MachineDescription.encodeCellAppend cell
          (MachineDescription.encodeCellsAppend cells suffix)) := by
  rfl

theorem targetWord_left_empty
    (state : Nat) (write head : Option Bool)
    (right : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    targetWord state { write := write, move := Direction.left }
        { left := [], head := head, right := right } suffix =
      MachineDescription.encodeNatAppend state
        (MachineDescription.encodeCellListAppend []
          (MachineDescription.encodeCellAppend none
            (MachineDescription.encodeCellListAppend (write :: right)
              suffix))) := by
  rfl

theorem targetWord_left_nonempty
    (state : Nat) (write head nextHead : Option Bool)
    (remainingLeft right : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    targetWord state { write := write, move := Direction.left }
        { left := nextHead :: remainingLeft, head := head,
          right := right } suffix =
      MachineDescription.encodeNatAppend state
        (MachineDescription.encodeCellListAppend remainingLeft
          (MachineDescription.encodeCellAppend nextHead
            (MachineDescription.encodeCellListAppend (write :: right)
              suffix))) := by
  rfl

theorem targetWord_right_empty
    (state : Nat) (write head : Option Bool)
    (left : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    targetWord state { write := write, move := Direction.right }
        { left := left, head := head, right := [] } suffix =
      MachineDescription.encodeNatAppend state
        (MachineDescription.encodeCellListAppend (write :: left)
          (MachineDescription.encodeCellAppend none
            (MachineDescription.encodeCellListAppend [] suffix))) := by
  rfl

theorem targetWord_right_nonempty
    (state : Nat) (write head nextHead : Option Bool)
    (left remainingRight : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    targetWord state { write := write, move := Direction.right }
        { left := left, head := head,
          right := nextHead :: remainingRight } suffix =
      MachineDescription.encodeNatAppend state
        (MachineDescription.encodeCellListAppend (write :: left)
          (MachineDescription.encodeCellAppend nextHead
            (MachineDescription.encodeCellListAppend remainingRight
              suffix))) := by
  rfl


end Section53RuntimeTapeUpdateShapes

end Computability
end FoC
