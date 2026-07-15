import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.RestagedEdits

set_option doc.verso true

/-!
# Product retained-field deletion

Delete one token from the retained raw call, compact only through the first
explicit boundary blank, and preserve every caller-owned physical cell as
opaque padding.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductCleanup

namespace DeleteOne

open SerializedFieldComposer

def startTape (leftRev : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  { left := leftRev.map some
    head := some deleted
    right := List.append (suffix.map some) (none :: padding) }

def startConfig (leftRev : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteOneRestagedMachine.Control :=
  { state := .edit .start
    tape := startTape leftRev deleted suffix padding }

def pullTape (leftRev rest : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := none :: leftRev.map some
        head := none
        right := padding }
  | current :: suffix =>
      { left := none :: leftRev.map some
        head := some current
        right := List.append (suffix.map some) (none :: padding) }

def pullConfig (leftRev rest : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteOneRestagedMachine.Control :=
  { state := .edit .pull
    tape := pullTape leftRev rest padding }

def exitConfig (wordRev : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteOneRestagedMachine.Control :=
  { state := .edit .halt
    tape :=
      { left := wordRev.map some
        head := none
        right := none :: padding } }

def scanTape (remainingRev crossed : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (crossed.map some) (none :: none :: padding) }
  | current :: rest =>
      { left := rest.map some
        head := some current
        right := List.append (crossed.map some) (none :: none :: padding) }

def scanConfig (remainingRev crossed : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteOneRestagedMachine.Control :=
  { state := .rewind .scan
    tape := scanTape remainingRev crossed padding }

def gateTape (word : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := [none]
        head := none
        right := none :: padding }
  | first :: rest =>
      { left := [none]
        head := some first
        right := List.append (rest.map some) (none :: none :: padding) }

def gateConfig (word : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteOneRestagedMachine.Control :=
  { state := .rewind .gate
    tape := gateTape word padding }

theorem start_step (leftRev : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.stepConfig
        (startConfig leftRev deleted suffix padding) =
      some (pullConfig leftRev suffix padding) := by
  cases suffix <;> cases padding <;> rfl

theorem pull_three_steps (leftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol) (suffix : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.runConfigExact? 3
        (pullConfig leftRev (current :: suffix) padding) =
      some (pullConfig (current :: leftRev) suffix padding) := by
  cases suffix <;> cases padding <;> rfl

theorem pull_finish (leftRev : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.runConfigExact? 1
        (pullConfig leftRev [] padding) =
      some (exitConfig leftRev padding) := by
  cases padding <;> rfl

theorem pull_run_exact (leftRev suffix : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.runConfigExact?
        (3 * suffix.length + 1) (pullConfig leftRev suffix padding) =
      some (exitConfig (List.append suffix.reverse leftRev) padding) := by
  induction suffix generalizing leftRev with
  | nil =>
      simpa using pull_finish leftRev padding
  | cons current suffix ih =>
      rw [show 3 * (current :: suffix).length + 1 =
          3 + (3 * suffix.length + 1) by simp; lia]
      rw [DeleteOneRestagedMachine.runConfigExact?_add]
      rw [pull_three_steps]
      simp only
      rw [ih (current :: leftRev)]
      simp [List.reverse_cons, List.append_assoc]

theorem edit_run_exact (leftRev : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.runConfigExact?
        (3 * suffix.length + 2)
        (startConfig leftRev deleted suffix padding) =
      some (exitConfig (List.append suffix.reverse leftRev) padding) := by
  change DeleteOneRestagedMachine.machine.runConfigExact?
      ((3 * suffix.length + 1) + 1)
      (startConfig leftRev deleted suffix padding) = _
  rw [TuringMachine.runConfigExact?]
  rw [start_step]
  simpa using pull_run_exact leftRev suffix padding

theorem retarget_step (wordRev : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.stepConfig
        (exitConfig wordRev padding) =
      some (scanConfig wordRev [] padding) := by
  cases wordRev <;> cases padding <;> rfl

theorem scan_step (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.stepConfig
        (scanConfig (current :: remainingRev) crossed padding) =
      some (scanConfig remainingRev (current :: crossed) padding) := by
  cases remainingRev <;> cases padding <;> rfl

theorem scan_finish (crossed : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.stepConfig
        (scanConfig [] crossed padding) =
      some (gateConfig crossed padding) := by
  cases crossed <;> cases padding <;> rfl

theorem scan_run_exact (remainingRev crossed : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.runConfigExact?
        (remainingRev.length + 1)
        (scanConfig remainingRev crossed padding) =
      some (gateConfig (List.append remainingRev.reverse crossed) padding) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact scan_finish crossed padding
  | cons current remainingRev ih =>
      change DeleteOneRestagedMachine.machine.runConfigExact?
          ((remainingRev.length + 1) + 1)
          (scanConfig (current :: remainingRev) crossed padding) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

theorem rewind_run_exact (wordRev : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.runConfigExact?
        (wordRev.length + 2) (exitConfig wordRev padding) =
      some (gateConfig wordRev.reverse padding) := by
  change DeleteOneRestagedMachine.machine.runConfigExact?
      ((wordRev.length + 1) + 1) (exitConfig wordRev padding) = _
  rw [TuringMachine.runConfigExact?]
  rw [retarget_step]
  simpa using scan_run_exact wordRev [] padding

def output (leftRev suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append leftRev.reverse suffix

def runSteps (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  (3 * suffix.length + 2) +
    ((List.append suffix.reverse leftRev).length + 2)

theorem run_exact (leftRev : Word MachineCodeSymbol)
    (deleted : MachineCodeSymbol) (suffix : Word MachineCodeSymbol)
    (padding : List (Option MachineCodeSymbol)) :
    DeleteOneRestagedMachine.machine.runConfigExact?
        (runSteps leftRev suffix)
        (startConfig leftRev deleted suffix padding) =
      some (gateConfig (output leftRev suffix) padding) := by
  unfold runSteps
  rw [DeleteOneRestagedMachine.runConfigExact?_add]
  rw [edit_run_exact]
  simp only
  rw [rewind_run_exact]
  simp [output, List.reverse_append]

end DeleteOne

end ProductCleanup
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
