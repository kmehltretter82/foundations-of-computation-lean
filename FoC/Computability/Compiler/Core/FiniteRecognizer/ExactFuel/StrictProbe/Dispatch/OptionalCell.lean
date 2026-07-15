import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Optional-cell cursor decoding

Finite decoding of a canonical serialized optional cell while restoring its
input cursor.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Dispatch
namespace OptionalCell

open SerializedFieldComposer

/-- Decode one canonical optional-cell word and return to its first token. -/
inductive Control where
  | decode (count : Fin 10)
  | returnLeft (cell : Option MachineCodeSymbol) (remaining : Fin 10)
  | zeroBounce (cell : Option MachineCodeSymbol)
  | gate (cell : Option MachineCodeSymbol)
deriving DecidableEq

namespace Control

def optionalSymbols : List (Option MachineCodeSymbol) :=
  HeadLocator.Control.optionalSymbols

def optionalSymbols_complete (cell : Option MachineCodeSymbol) :
    cell ∈ optionalSymbols :=
  HeadLocator.Control.optionalSymbols_complete cell

def returnFinite : Foundation.FiniteType
    (Option MachineCodeSymbol × Fin 10) :=
  Foundation.FiniteType.prod
    { elems := optionalSymbols
      complete := optionalSymbols_complete }
    (Foundation.FiniteType.fin 10)

def elems : List Control :=
  List.append
    ((List.finRange 10).map Control.decode)
    (List.append
      (returnFinite.elems.map fun payload =>
        Control.returnLeft payload.1 payload.2)
      (List.append
        (optionalSymbols.map Control.zeroBounce)
        (optionalSymbols.map Control.gate)))

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | decode count =>
        simp [elems, List.mem_finRange]
    | returnLeft cell remaining =>
        have h := returnFinite.complete (cell, remaining)
        simp [elems, h]
    | zeroBounce cell =>
        have h := optionalSymbols_complete cell
        simp [elems, h]
    | gate cell =>
        have h := optionalSymbols_complete cell
        simp [elems, h]

end Control

def pred (count : Fin 10) : Fin 10 :=
  ⟨count.val - 1,
    Nat.lt_of_le_of_lt (Nat.sub_le count.val 1) count.isLt⟩

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .decode count, some MachineCodeSymbol.tick =>
      match HeadLocator.incrementHeadCount count with
      | none => none
      | some next =>
          some
            (some MachineCodeSymbol.tick, Direction.right, .decode next)
  | .decode count, some MachineCodeSymbol.done =>
      let cell := HeadLocator.decodedHead count
      if count.val = 0 then
        some (some MachineCodeSymbol.done, Direction.left,
          .zeroBounce cell)
      else if count.val = 1 then
        some (some MachineCodeSymbol.done, Direction.left, .gate cell)
      else
        some (some MachineCodeSymbol.done, Direction.left,
          .returnLeft cell (pred count))
  | .returnLeft cell remaining, read =>
      if remaining.val = 1 then
        some (read, Direction.left, .gate cell)
      else
        some (read, Direction.left, .returnLeft cell (pred remaining))
  | .zeroBounce cell, read =>
      some (read, Direction.right, .gate cell)
  | .gate _, _ => none
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .decode ⟨0, by decide⟩
  halt := .gate none
  transition := transition
  statesFinite := Control.finite

def sourceConfig (leftRev : Word MachineCodeSymbol)
    (cell : Option MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .decode ⟨0, by decide⟩
  tape := SerializedShift.cursorTape leftRev
    (List.append (optionalCellWord cell) suffix)

def gateConfig (leftRev : Word MachineCodeSymbol)
    (cell : Option MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate cell
  tape := SerializedShift.cursorTape leftRev
    (List.append (optionalCellWord cell) suffix)

def runSteps (cell : Option MachineCodeSymbol) : Nat :=
  2 * max 1 (optionalCodeSymbolTag cell)

/-- Canonical optional cells are bounded by the ten finite tags.  From a
nonempty protected prefix, the decoder restores the literal cursor while
retaining the decoded cell in finite control. -/
theorem run_exact
    (leftRev : Word MachineCodeSymbol)
    (cell : Option MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol)
    (hleft : leftRev ≠ []) :
    machine.runConfigExact? (runSteps cell)
        (sourceConfig leftRev cell suffix) =
      some (gateConfig leftRev cell suffix) := by
  cases leftRev with
  | nil =>
      contradiction
  | cons leftHead leftTail =>
      cases cell with
      | none =>
          cases suffix <;> rfl
      | some symbol =>
          cases symbol <;> cases suffix <;> rfl

/-- The same bounded decoder runs from any padded representative of the
positioned cursor, retaining the exact decoded finite payload and an
equivalent endpoint tape. -/
theorem run_exact_of_tape_equiv
    (leftRev : Word MachineCodeSymbol)
    (cell : Option MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol)
    (hleft : leftRev ≠ [])
    (T : Tape MachineCodeSymbol)
    (hequiv : Tape.Equiv (sourceConfig leftRev cell suffix).tape T) :
    exists endpoint,
      machine.runConfigExact? (runSteps cell)
          { state := Control.decode ⟨0, by decide⟩, tape := T } =
        some endpoint ∧
      endpoint.state = Control.gate cell ∧
      Tape.Equiv (gateConfig leftRev cell suffix).tape endpoint.tape := by
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (run_exact leftRev cell suffix hleft) hequiv with
    ⟨endpoint, hrun, hstate, htape⟩
  exact ⟨endpoint, hrun, hstate, htape⟩

end OptionalCell
end Dispatch
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
