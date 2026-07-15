import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame

set_option doc.verso true

/-!
# Serialized strict-probe suffix shifts

Canonical exact-fuel fields have variable length.  Replacing such a field may
therefore require moving every later token, including the protected caller
suffix.  This module supplies the two finite one-tape mechanics needed by that
rewrite: insertion shifts a suffix one cell right, and deletion compacts a
suffix one cell left.  Their exact-run interfaces retain the copied suffix
literally; parsing and selecting the field boundary remain separate phases.
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

namespace Insert

/-- Control for the one-cell carry insertion pass. -/
inductive Control where
  /-- Write the carried token and continue carrying the overwritten token. -/
  | carry (symbol : MachineCodeSymbol)
  /-- Exit after depositing the final carried token in the first blank. -/
  | halt
deriving DecidableEq

namespace Control

/-- Explicit enumeration of insertion controls. -/
def elems : List Control :=
  List.append (MachineCodeSymbol.finite.elems.map Control.carry) [.halt]

/-- Finiteness witness for insertion control. -/
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | carry symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
    | halt =>
        simp [elems]

end Control

/-- One-cell right-shift transition carrying the token to be inserted. -/
def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .carry carried, some current =>
      some (some carried, Direction.right, .carry current)
  | .carry carried, none =>
      some (some carried, Direction.right, .halt)
  | .halt, _ => none

/-- Finite one-tape machine implementing a one-cell suffix insertion. -/
def machine (initial : MachineCodeSymbol) :
    TuringMachine MachineCodeSymbol Control where
  start := .carry initial
  halt := .halt
  transition := transition
  statesFinite := Control.finite

/-- Configuration of the insertion pass with one carried token. -/
def config (carried : MachineCodeSymbol)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .carry carried
  tape := cursorTape leftRev rest

/-- Exit configuration after depositing the final carried token. -/
def exitConfig (leftRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt
  tape := cursorTape leftRev []

/-- One insertion step crosses a nonblank suffix token. -/
theorem step_cons (initial carried current : MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine initial).stepConfig
        (config carried leftRev (current :: suffix)) =
      some (config current (carried :: leftRev) suffix) := by
  cases suffix <;>
    rfl

/-- The final insertion step deposits the carried token in the first blank. -/
theorem step_nil (initial carried : MachineCodeSymbol)
    (leftRev : Word MachineCodeSymbol) :
    (machine initial).stepConfig (config carried leftRev []) =
      some (exitConfig (carried :: leftRev)) := by
  rfl

/--
The carry pass shifts an arbitrary suffix right by one cell in exactly one
step per suffix token plus the final blank deposit.
-/
theorem run_exact (initial carried : MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine initial).runConfigExact? (suffix.length + 1)
        (config carried leftRev suffix) =
      some (exitConfig (suffix.reverse ++ carried :: leftRev)) := by
  induction suffix generalizing carried leftRev with
  | nil =>
      exact step_nil initial carried leftRev
  | cons current suffix ih =>
      change
        (machine initial).runConfigExact? ((suffix.length + 1) + 1)
            (config carried leftRev (current :: suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_cons]
      simp only
      rw [ih current (carried :: leftRev)]
      simp [List.reverse_cons, List.append_assoc]

/-- The insertion endpoint spells the original prefix, inserted token, and suffix. -/
theorem exitConfig_normalizedOutput
    (leftRev : Word MachineCodeSymbol) :
    Tape.normalizedOutput (exitConfig leftRev).tape = leftRev.reverse := by
  simp [exitConfig, cursorTape, Tape.normalizedOutput, Tape.cells,
    Function.comp_def]

/-- Insertion preserves every suffix token, including any protected caller frame. -/
theorem run_exact_normalizedOutput
    (carried : MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    Tape.normalizedOutput
        ((exitConfig (suffix.reverse ++ carried :: leftRev)).tape) =
      leftRev.reverse ++ carried :: suffix := by
  rw [exitConfig_normalizedOutput]
  simp [List.reverse_append, List.reverse_cons, List.append_assoc]

end Insert

private theorem runConfigExact?_add
    {symbol state : Type}
    (M : TuringMachine symbol state)
    (first second : Nat)
    (c : TuringMachine.Configuration symbol state) :
    M.runConfigExact? (first + second) c =
      match M.runConfigExact? first c with
      | none => none
      | some middle => M.runConfigExact? second middle := by
  induction first generalizing c with
  | zero =>
      simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add]
      rw [TuringMachine.runConfigExact?]
      rw [TuringMachine.runConfigExact?]
      cases hstep : M.stepConfig c with
      | none =>
          rfl
      | some next =>
          simp only
          exact ih next

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

/-- Finite one-tape machine implementing one-cell suffix deletion. -/
def machine : TuringMachine MachineCodeSymbol Control where
  start := .start
  halt := .halt
  transition := transition
  statesFinite := Control.finite

/-- Configuration before erasing the selected token. -/
def startConfig (leftRev : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .start
  tape := cursorTape leftRev (deleted :: suffix)

/--
Tape invariant for compaction: the blank immediately to the left of the head is
the moving gap, and the head reads the next suffix token or the terminal blank.
-/
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

/--
Physical deletion endpoint.  The right-side blank is the visited source cell
that used to hold the final suffix token.
-/
def exitTape (leftRev : Word MachineCodeSymbol) : Tape MachineCodeSymbol where
  left := leftRev.map some
  head := none
  right := [none]

/-- Halting configuration after suffix compaction. -/
def exitConfig (leftRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt
  tape := exitTape leftRev

/-- Erasing the selected token establishes the moving-gap invariant. -/
theorem start_step (leftRev : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    machine.stepConfig (startConfig leftRev deleted suffix) =
      some (pullConfig leftRev suffix) := by
  cases suffix <;>
    rfl

/-- Pulling one suffix token left advances the gap in exactly three steps. -/
theorem pull_three_steps (leftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 3 (pullConfig leftRev (current :: suffix)) =
      some (pullConfig (current :: leftRev) suffix) := by
  cases suffix <;>
    rfl

/-- The terminal blank closes the moving gap in one final step. -/
theorem pull_finish (leftRev : Word MachineCodeSymbol) :
    machine.runConfigExact? 1 (pullConfig leftRev []) =
      some (exitConfig leftRev) := by
  rfl

/--
Compacting a suffix takes three steps per copied token and one final blank
step.  Every copied token occurs literally in the endpoint.
-/
theorem pull_run_exact (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (3 * suffix.length + 1)
        (pullConfig leftRev suffix) =
      some (exitConfig (List.append suffix.reverse leftRev)) := by
  induction suffix generalizing leftRev with
  | nil =>
      exact pull_finish leftRev
  | cons current suffix ih =>
      rw [show 3 * (current :: suffix).length + 1 =
          3 + (3 * suffix.length + 1) by
        simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm]]
      rw [runConfigExact?_add]
      rw [pull_three_steps]
      simp only
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/--
Deleting one selected token and compacting its arbitrary suffix has an exact
linear run bound.
-/
theorem run_exact (leftRev : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (3 * suffix.length + 2)
        (startConfig leftRev deleted suffix) =
      some (exitConfig (List.append suffix.reverse leftRev)) := by
  change
    machine.runConfigExact? ((3 * suffix.length + 1) + 1)
        (startConfig leftRev deleted suffix) = _
  rw [TuringMachine.runConfigExact?]
  rw [start_step]
  simp only
  exact pull_run_exact leftRev suffix

/-- The compaction endpoint spells the reversed copied prefix. -/
theorem exitConfig_normalizedOutput
    (leftRev : Word MachineCodeSymbol) :
    Tape.normalizedOutput (exitConfig leftRev).tape = leftRev.reverse := by
  simp [exitConfig, exitTape, Tape.normalizedOutput, Tape.cells,
    Function.comp_def]

/-- Deletion removes only the selected token and preserves the suffix literally. -/
theorem run_exact_normalizedOutput
    (leftRev suffix : Word MachineCodeSymbol) :
    Tape.normalizedOutput
        ((exitConfig (List.append suffix.reverse leftRev)).tape) =
      List.append leftRev.reverse suffix := by
  rw [exitConfig_normalizedOutput]
  simp [List.reverse_append]

end Delete

end SerializedShift
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
