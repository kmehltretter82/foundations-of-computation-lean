import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame

set_option doc.verso true

/-!
# Serialized strict-probe deletion shapes

Shared cursor and one-cell deletion control shapes used by the restaged frame
editor. The composed editor owns the executable run proofs.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace SerializedShift

/-- Tape with the head at the first token of {name}`rest`, after {name}`leftRev`. -/
def cursorTape
    (leftRev rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := leftRev.map some
        head := none
        right := [] }
  | first :: suffix =>
      { left := leftRev.map some
        head := some first
        right := suffix.map some }

namespace Delete

/-- Control for the one-cell gap-compaction pass. -/
inductive Control where
  /-- Erase the token selected for deletion and expose the moving gap. -/
  | start
  /-- Pull the next suffix token left into the gap. -/
  | pull
  /-- Carry one suffix token back to the gap. -/
  | writeBack (symbol : MachineCodeSymbol)
  /-- Cross the newly vacated cell before pulling the next token. -/
  | advance
  /-- Exit after the first far-right blank reaches the moving gap. -/
  | halt
deriving DecidableEq

namespace Control

/-- Explicit enumeration of deletion controls. -/
def elems : List Control :=
  [.start, .pull, .advance, .halt] ++
    MachineCodeSymbol.finite.elems.map Control.writeBack

/-- Finiteness witness for deletion control. -/
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | start =>
        simp [elems]
    | pull =>
        simp [elems]
    | writeBack symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
    | advance =>
        simp [elems]
    | halt =>
        simp [elems]

end Control

/-- Transition table for one-cell left compaction of an arbitrary suffix. -/
def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .start, _ =>
      some (none, Direction.right, .pull)
  | .pull, some current =>
      some (none, Direction.left, .writeBack current)
  | .pull, none =>
      some (none, Direction.left, .halt)
  | .writeBack carried, _ =>
      some (some carried, Direction.right, .advance)
  | .advance, _ =>
      some (none, Direction.right, .pull)
  | .halt, _ => none

/-- Configuration before erasing the selected token. -/
def startConfig (leftRev : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .start
  tape := cursorTape leftRev (deleted :: suffix)

/-- Tape invariant at the moving gap during compaction. -/
def pullTape
    (leftRev rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := none :: leftRev.map some
        head := none
        right := [] }
  | first :: suffix =>
      { left := none :: leftRev.map some
        head := some first
        right := suffix.map some }

/-- Configuration at the moving gap. -/
def pullConfig (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .pull
  tape := pullTape leftRev rest

/-- Physical deletion endpoint retaining the visited far-right blank. -/
def exitTape (leftRev : Word MachineCodeSymbol) : Tape MachineCodeSymbol where
  left := leftRev.map some
  head := none
  right := [none]

/-- Halting configuration after suffix compaction. -/
def exitConfig (leftRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt
  tape := exitTape leftRev

end Delete

end SerializedShift
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
