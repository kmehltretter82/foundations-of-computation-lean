import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.RawTail

/-!
# Exact-fuel stage-input header installation

The final finite phase that installs the protected header and fuel field over
the materialized input body.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace InitialMaterializer

namespace HeaderLeftInstaller

inductive Control where
  | start
  | body
  | secondBoundary
  | fuelDone
  | fuelTicks
  | halt
deriving DecidableEq

namespace Control
def elems : List Control :=
  [.start, .body, .secondBoundary, .fuelDone, .fuelTicks, .halt]
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .start, none => some (none, Direction.left, .body)
  | .body, some symbol =>
      some (some symbol, Direction.left, .body)
  | .body, none =>
      some (none, Direction.left, .secondBoundary)
  | .secondBoundary, none =>
      some (none, Direction.left, .fuelDone)
  | .fuelDone, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .fuelTicks)
  | .fuelTicks, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left, .fuelTicks)
  | .fuelTicks, none =>
      some (some MachineCodeSymbol.header, Direction.right, .halt)
  | _, _ => none
def machine : TuringMachine MachineCodeSymbol Control where
  start := .start
  halt := .halt
  transition := transition
  statesFinite := Control.finite
def sourceConfig (wordRev fuelRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .start
  tape :=
    { left := List.append (wordRev.map some) (none :: none :: fuelRev.map some)
      head := none
      right := [] }
def bodyTape (fuelRev remainingRev crossed : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := none :: fuelRev.map some
        head := none
        right := List.append (crossed.map some) [none] }
  | current :: rest =>
      { left := List.append (rest.map some) (none :: none :: fuelRev.map some)
        head := some current
        right := List.append (crossed.map some) [none] }
def bodyConfig (fuelRev remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .body
  tape := bodyTape fuelRev remainingRev crossed
def secondBoundaryConfig (fuelRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .secondBoundary
  tape :=
    { left := fuelRev.map some
      head := none
      right := none :: List.append (crossed.map some) [none] }
def fuelDoneConfig (ticksRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .fuelDone
  tape :=
    { left := ticksRev.map some
      head := some MachineCodeSymbol.done
      right := none :: none :: List.append (crossed.map some) [none] }
def ticksTape (remainingRev crossed bodyWord : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (crossed.map some) (none :: none :: List.append (bodyWord.map some) [none]) }
  | current :: rest =>
      { left := rest.map some
        head := some current
        right := List.append (crossed.map some) (none :: none :: List.append (bodyWord.map some) [none]) }
def ticksConfig (remainingRev crossed bodyWord : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .fuelTicks
  tape := ticksTape remainingRev crossed bodyWord
def haltTape (fuelWord bodyWord : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match fuelWord with
  | [] =>
      { left := [some MachineCodeSymbol.header]
        head := none
        right := none :: none :: List.append (bodyWord.map some) [none] }
  | first :: rest =>
      { left := [some MachineCodeSymbol.header]
        head := some first
        right := List.append (rest.map some) (none :: none :: List.append (bodyWord.map some) [none]) }
def haltConfig (fuelWord bodyWord : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt
  tape := haltTape fuelWord bodyWord
theorem start_step (wordRev fuelRev : Word MachineCodeSymbol) : machine.stepConfig (sourceConfig wordRev fuelRev) =
      some (bodyConfig fuelRev wordRev []) := by
  cases wordRev <;> rfl
theorem body_step (fuelRev : Word MachineCodeSymbol) (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) : machine.stepConfig
        (bodyConfig fuelRev (current :: remainingRev) crossed) = some
        (bodyConfig fuelRev remainingRev (current :: crossed)) := by
  cases remainingRev <;> rfl
theorem body_finish (fuelRev crossed : Word MachineCodeSymbol) : machine.stepConfig (bodyConfig fuelRev [] crossed) =
      some (secondBoundaryConfig fuelRev crossed) := by
  cases crossed <;> rfl
theorem body_run_exact (fuelRev remainingRev crossed : Word MachineCodeSymbol) :
    machine.runConfigExact? (remainingRev.length + 1)
        (bodyConfig fuelRev remainingRev crossed) = some (secondBoundaryConfig fuelRev
          (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact body_finish fuelRev crossed
  | cons current remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1) (bodyConfig fuelRev
              (current :: remainingRev) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [body_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]
theorem second_boundary_step (ticksRev bodyWord : Word MachineCodeSymbol) : machine.stepConfig
        (secondBoundaryConfig (MachineCodeSymbol.done :: ticksRev) bodyWord) =
      some (fuelDoneConfig ticksRev bodyWord) := by
  cases bodyWord <;> rfl
theorem fuel_done_step (ticksRev bodyWord : Word MachineCodeSymbol) :
    machine.stepConfig (fuelDoneConfig ticksRev bodyWord) = some
        (ticksConfig ticksRev [MachineCodeSymbol.done] bodyWord) := by
  cases ticksRev <;> cases bodyWord <;> rfl
theorem tick_step (remainingRev crossed bodyWord : Word MachineCodeSymbol) : machine.stepConfig
        (ticksConfig (MachineCodeSymbol.tick :: remainingRev) crossed bodyWord) = some
        (ticksConfig remainingRev (MachineCodeSymbol.tick :: crossed) bodyWord) := by
  cases remainingRev <;> cases crossed <;> cases bodyWord <;> rfl
theorem tick_finish (first : MachineCodeSymbol) (rest bodyWord : Word MachineCodeSymbol) :
    machine.stepConfig (ticksConfig [] (first :: rest) bodyWord) = some (haltConfig (first :: rest) bodyWord) := by
  cases rest <;> cases bodyWord <;> rfl
theorem ticks_replicate_run_exact (count : Nat) (first : MachineCodeSymbol)
    (crossedRest bodyWord : Word MachineCodeSymbol) : machine.runConfigExact? (count + 1)
        (ticksConfig (List.replicate count MachineCodeSymbol.tick)
          (first :: crossedRest) bodyWord) = some (haltConfig (List.append
            (List.replicate count MachineCodeSymbol.tick).reverse (first :: crossedRest)) bodyWord) := by
  induction count generalizing first crossedRest with
  | zero =>
      exact tick_finish first crossedRest bodyWord
  | succ count ih =>
      change machine.runConfigExact? ((count + 1) + 1) (ticksConfig (MachineCodeSymbol.tick ::
                List.replicate count MachineCodeSymbol.tick) (first :: crossedRest) bodyWord) = _
      rw [TuringMachine.runConfigExact?]
      rw [tick_step]
      simp only
      rw [ih MachineCodeSymbol.tick (first :: crossedRest)]
      simp [List.replicate_succ, List.reverse_cons, List.append_assoc]
theorem encodeNat_reverse_eq_done_ticks (fuel : Nat) :
    (MachineDescription.encodeNat fuel).reverse = MachineCodeSymbol.done ::
        List.replicate fuel MachineCodeSymbol.tick := by
  rw [OneCellMachine.encodeNat_eq_ticks_done]
  simp
def runSteps (fuel : Nat) (wordRev : Word MachineCodeSymbol) : Nat :=
  1 + ((wordRev.length + 1) + (1 + (1 + (fuel + 1))))
theorem run_exact (fuel : Nat) (wordRev : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps fuel wordRev) (sourceConfig wordRev
          (MachineDescription.encodeNat fuel).reverse) = some (haltConfig
        (MachineDescription.encodeNat fuel) wordRev.reverse) := by
  unfold runSteps
  rw [ExactRun.append]
  rw [show machine.runConfigExact? 1 (sourceConfig wordRev (MachineDescription.encodeNat fuel).reverse) = some
          (bodyConfig (MachineDescription.encodeNat fuel).reverse wordRev []) by
    exact start_step wordRev (MachineDescription.encodeNat fuel).reverse]
  simp only
  rw [ExactRun.append]
  rw [body_run_exact]
  simp only
  have hword : List.append wordRev.reverse [] = wordRev.reverse :=
    List.append_nil wordRev.reverse
  rw [hword]
  rw [encodeNat_reverse_eq_done_ticks]
  rw [ExactRun.append]
  rw [show machine.runConfigExact? 1 (secondBoundaryConfig (MachineCodeSymbol.done ::
            List.replicate fuel MachineCodeSymbol.tick) wordRev.reverse) = some (fuelDoneConfig
            (List.replicate fuel MachineCodeSymbol.tick) wordRev.reverse) by
    rw [TuringMachine.runConfigExact?]
    rw [second_boundary_step]
    simp only [TuringMachine.runConfigExact?]]
  simp only
  rw [ExactRun.append]
  rw [show machine.runConfigExact? 1 (fuelDoneConfig
        (List.replicate fuel MachineCodeSymbol.tick) wordRev.reverse) = some (ticksConfig
            (List.replicate fuel MachineCodeSymbol.tick) [MachineCodeSymbol.done] wordRev.reverse) by
    exact fuel_done_step (List.replicate fuel MachineCodeSymbol.tick) wordRev.reverse]
  simp only
  have hticks := ticks_replicate_run_exact fuel MachineCodeSymbol.done [] wordRev.reverse
  simpa [encodeNat_reverse_eq_done_ticks, OneCellMachine.encodeNat_eq_ticks_done] using hticks
theorem halt_normalizedOutput (fuelWord bodyWord : Word MachineCodeSymbol)
    (hfuel : fuelWord ≠ []) : Tape.normalizedOutput (haltTape fuelWord bodyWord) =
      MachineCodeSymbol.header :: List.append fuelWord bodyWord := by
  cases fuelWord with
  | nil => contradiction
  | cons first rest =>
      have hfilter (word : Word MachineCodeSymbol) : List.filterMap
              ((fun cell : Option MachineCodeSymbol => cell) ∘ some) word = word := by
        induction word with
        | nil => rfl
        | cons current word ih =>
            simp [Function.comp_def]
      simp [haltTape, Tape.normalizedOutput, Tape.cells, hfilter]
end HeaderLeftInstaller

end InitialMaterializer
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
