import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.MotionLayouts
namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
open Languages
namespace RewindWord
inductive Control where
  | start
  | scan
  | gate
deriving DecidableEq
namespace Control
def elems : List Control := [.start, .scan, .gate]
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .start, cell => some (cell, Direction.left, .scan)
  | .scan, some symbol =>
      some (some symbol, Direction.left, .scan)
  | .scan, none => some (none, Direction.right, .gate)
  | .gate, _ => none
def machine : TuringMachine MachineCodeSymbol Control where
  start := .start
  halt := .gate
  transition := transition
  statesFinite := Control.finite
def paddingCells (padding : Nat) : List (Option MachineCodeSymbol) := List.replicate padding none
def scanTape (remainingRev crossed : Word MachineCodeSymbol) (padding : Nat) : Tape MachineCodeSymbol := match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (crossed.map some) (none :: paddingCells padding) }
  | current :: rest =>
      { left := rest.map some
        head := some current
        right := List.append (crossed.map some) (none :: paddingCells padding) }
def scanConfig (remainingRev crossed : Word MachineCodeSymbol) (padding : Nat) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scan
  tape := scanTape remainingRev crossed padding
def gateTape (word : Word MachineCodeSymbol) (padding : Nat) : Tape MachineCodeSymbol := match word with
  | [] =>
      { left := [none]
        head := none
        right := paddingCells padding }
  | first :: rest =>
      { left := [none]
        head := some first
        right := List.append (rest.map some) (none :: paddingCells padding) }
def gateConfig (word : Word MachineCodeSymbol) (padding : Nat) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate
  tape := gateTape word padding
end RewindWord
namespace DeleteEndpointRewind
inductive Control where
  | skip0
  | skip1
  | skip2
  | skip3
  | skip4
  | skip5
  | skip6
  | skip7
  | skip8
  | skip9
  | scan
  | gate
deriving DecidableEq
namespace Control
def elems : List Control := [.skip0, .skip1, .skip2, .skip3, .skip4, .skip5, .skip6, .skip7, .skip8, .skip9, .scan, .gate]
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .skip9, cell => some (cell, Direction.left, .skip8)
  | .skip8, cell => some (cell, Direction.left, .skip7)
  | .skip7, cell => some (cell, Direction.left, .skip6)
  | .skip6, cell => some (cell, Direction.left, .skip5)
  | .skip5, cell => some (cell, Direction.left, .skip4)
  | .skip4, cell => some (cell, Direction.left, .skip3)
  | .skip3, cell => some (cell, Direction.left, .skip2)
  | .skip2, cell => some (cell, Direction.left, .skip1)
  | .skip1, cell => some (cell, Direction.left, .skip0)
  | .skip0, cell => some (cell, Direction.left, .scan)
  | .scan, some symbol =>
      some (some symbol, Direction.left, .scan)
  | .scan, none => some (none, Direction.right, .gate)
  | .gate, _ => none
def startControl : Option MachineCodeSymbol -> Control
  | none => .skip0
  | some MachineCodeSymbol.header => .skip1
  | some MachineCodeSymbol.transition => .skip2
  | some MachineCodeSymbol.tick => .skip3
  | some MachineCodeSymbol.done => .skip4
  | some MachineCodeSymbol.blank => .skip5
  | some MachineCodeSymbol.zero => .skip6
  | some MachineCodeSymbol.one => .skip7
  | some MachineCodeSymbol.moveLeft => .skip8
  | some MachineCodeSymbol.moveRight => .skip9
def trailingCells (cell : Option MachineCodeSymbol) : List (Option MachineCodeSymbol) := List.replicate (optionalCodeSymbolTag cell + 2) none
def scanTape (remainingRev crossed : Word MachineCodeSymbol) (cell : Option MachineCodeSymbol) : Tape MachineCodeSymbol := match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (crossed.map some) (trailingCells cell) }
  | current :: rest =>
      { left := rest.map some
        head := some current
        right := List.append (crossed.map some) (trailingCells cell) }
def scanConfig (remainingRev crossed : Word MachineCodeSymbol) (cell : Option MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scan
  tape := scanTape remainingRev crossed cell
def gateTape (word : Word MachineCodeSymbol) (cell : Option MachineCodeSymbol) : Tape MachineCodeSymbol := Tape.move Direction.right (scanTape [] word cell)
def gateConfig (word : Word MachineCodeSymbol) (cell : Option MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate
  tape := gateTape word cell
def runSteps (cell : Option MachineCodeSymbol) (wordRev : Word MachineCodeSymbol) : Nat := (optionalCodeSymbolTag cell + 1) + (wordRev.length + 1)
end DeleteEndpointRewind
namespace RewindWord
theorem gateTape_equiv_input (word : Word MachineCodeSymbol) (padding : Nat) : Tape.Equiv (gateTape word padding) (Tape.input word) := by
  cases word with
  | nil =>
      refine ⟨rfl, rfl, ?_⟩
      exact dropTrailingNone_replicate_none padding
  | cons first rest =>
      refine ⟨rfl, rfl, ?_⟩
      change Tape.dropTrailingNone (List.append (rest.map some) (none :: List.replicate padding none)) = Tape.dropTrailingNone (rest.map some)
      calc
        Tape.dropTrailingNone (List.append (rest.map some) (none :: List.replicate padding none)) =
          Tape.dropTrailingNone (List.append (List.append (rest.map some) [none]) (List.replicate padding none)) := by
                simp [List.append_assoc]
        _ = Tape.dropTrailingNone (List.append (rest.map some) [none]) := dropTrailingNone_append_replicate_none _ padding
        _ = Tape.dropTrailingNone (rest.map some) := dropTrailingNone_append_none _
end RewindWord
namespace DeleteEndpointRewind
theorem gateTape_equiv_input (word : Word MachineCodeSymbol) (cell : Option MachineCodeSymbol) : Tape.Equiv (gateTape word cell) (Tape.input word) := by
  cases word with
  | nil =>
      cases cell with
      | none =>
          simp [gateTape, scanTape, trailingCells, optionalCodeSymbolTag, Tape.input, Tape.blank, Tape.Equiv, Tape.move, Tape.moveRight, Tape.dropTrailingNone, ]
      | some symbol =>
          cases symbol <;> simp [gateTape, scanTape, trailingCells, optionalCodeSymbolTag, codeSymbolTag, Tape.input, Tape.blank, Tape.Equiv,
              Tape.move, Tape.moveRight, Tape.dropTrailingNone,
              ]
  | cons first rest =>
      simp [gateTape, scanTape, trailingCells, Tape.input, Tape.Equiv, Tape.move, Tape.moveRight, Tape.dropTrailingNone, dropTrailingNone_append_replicate_none]
end DeleteEndpointRewind
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
