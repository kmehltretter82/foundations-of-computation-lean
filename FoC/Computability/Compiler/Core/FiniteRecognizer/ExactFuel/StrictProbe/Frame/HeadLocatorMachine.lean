import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Serialized
namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
open Languages
namespace HeadLocator
inductive Control where
  | header
  | fuel
  | state
  | markCountBoundary
  | returnCountStart
  | countCheck
  | seekCountBoundary
  | seekCellDone
  | returnCount
  | decodeHead (count : Fin 10)
  | restoreCells (head : Option MachineCodeSymbol)
  | restoreCount (head : Option MachineCodeSymbol)
  | seekTopHeader (head : Option MachineCodeSymbol)
  | gateBounce (head : Option MachineCodeSymbol)
  | gate (head : Option MachineCodeSymbol)
deriving DecidableEq
namespace Control
def optionalSymbols : List (Option MachineCodeSymbol) := none :: MachineCodeSymbol.finite.elems.map some
theorem optionalSymbols_complete (cell : Option MachineCodeSymbol) : cell ∈ optionalSymbols := by
  cases cell with
  | none => simp [optionalSymbols]
  | some symbol =>
      simp [optionalSymbols]
      exact MachineCodeSymbol.finite.complete symbol
def elems : List Control := [ .header, .fuel, .state, .markCountBoundary, .returnCountStart
  , .countCheck, .seekCountBoundary, .seekCellDone, .returnCount ] ++ (List.finRange 10).map Control.decodeHead ++
      optionalSymbols.map Control.restoreCells ++ optionalSymbols.map Control.restoreCount ++
          optionalSymbols.map Control.seekTopHeader ++ optionalSymbols.map Control.gateBounce ++ optionalSymbols.map Control.gate
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | header => simp [elems]
    | fuel => simp [elems]
    | state => simp [elems]
    | markCountBoundary => simp [elems]
    | returnCountStart => simp [elems]
    | countCheck => simp [elems]
    | seekCountBoundary => simp [elems]
    | seekCellDone => simp [elems]
    | returnCount => simp [elems]
    | decodeHead count => simp [elems, List.mem_finRange]
    | restoreCells head =>
        simp [elems]
        exact optionalSymbols_complete head
    | restoreCount head =>
        simp [elems]
        exact optionalSymbols_complete head
    | seekTopHeader head =>
        simp [elems]
        exact optionalSymbols_complete head
    | gateBounce head =>
        simp [elems]
        exact optionalSymbols_complete head
    | gate head =>
        simp [elems]
        exact optionalSymbols_complete head
end Control
def incrementHeadCount (count : Fin 10) : Option (Fin 10) := if h : count.val + 1 < 10 then some ⟨count.val + 1, h⟩ else none
def decodedHead (count : Fin 10) : Option MachineCodeSymbol := match count.val with
  | 0 => none
  | 1 => some MachineCodeSymbol.header
  | 2 => some MachineCodeSymbol.transition
  | 3 => some MachineCodeSymbol.tick
  | 4 => some MachineCodeSymbol.done
  | 5 => some MachineCodeSymbol.blank
  | 6 => some MachineCodeSymbol.zero
  | 7 => some MachineCodeSymbol.one
  | 8 => some MachineCodeSymbol.moveLeft
  | 9 => some MachineCodeSymbol.moveRight
  | _ => none
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .header, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .fuel)
  | .fuel, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .fuel)
  | .fuel, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .state)
  | .state, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .state)
  | .state, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .markCountBoundary)
  | .markCountBoundary, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .markCountBoundary)
  | .markCountBoundary, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.blank, Direction.left, .returnCountStart)
  | .returnCountStart, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left, .returnCountStart)
  | .returnCountStart, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .countCheck)
  | .countCheck, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.transition, Direction.right, .seekCountBoundary)
  | .countCheck, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .decodeHead ⟨0, by decide⟩)
  | .seekCountBoundary, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .seekCountBoundary)
  | .seekCountBoundary, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .seekCellDone)
  | .seekCellDone, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .seekCellDone)
  | .seekCellDone, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .seekCellDone)
  | .seekCellDone, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.header, Direction.left, .returnCount)
  | .returnCount, some MachineCodeSymbol.transition =>
      some (some MachineCodeSymbol.transition, Direction.right, .countCheck)
  | .returnCount, some symbol =>
      some (some symbol, Direction.left, .returnCount)
  | .decodeHead count, some MachineCodeSymbol.tick =>
      match incrementHeadCount count with
      | none => none
      | some next =>
          some (some MachineCodeSymbol.tick, Direction.right, .decodeHead next)
  | .decodeHead _, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .decodeHead ⟨0, by decide⟩)
  | .decodeHead count, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .restoreCells (decodedHead count))
  | .restoreCells head, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.done, Direction.left, .restoreCells head)
  | .restoreCells head, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.done, Direction.left, .restoreCount head)
  | .restoreCells head, some symbol =>
      some (some symbol, Direction.left, .restoreCells head)
  | .restoreCount head, some MachineCodeSymbol.transition =>
      some (some MachineCodeSymbol.tick, Direction.left, .restoreCount head)
  | .restoreCount head, some symbol =>
      some (some symbol, Direction.left, .seekTopHeader head)
  | .seekTopHeader head, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.left, .gateBounce head)
  | .seekTopHeader head, some symbol =>
      some (some symbol, Direction.left, .seekTopHeader head)
  | .gateBounce head, none =>
      some (none, Direction.right, .gate head)
  | _, _ => none
def machine : TuringMachine MachineCodeSymbol Control where
  start := .header
  halt := .gate none
  transition := transition
  statesFinite := Control.finite
def cursorConfig (control : Control) (leftRev rest : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := SerializedShift.cursorTape leftRev rest
end HeadLocator
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
