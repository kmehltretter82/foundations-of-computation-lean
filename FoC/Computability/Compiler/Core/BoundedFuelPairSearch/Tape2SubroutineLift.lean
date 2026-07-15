import FoC.Computability.Compiler.Structured.Lowering.TypedStateTable
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh

set_option doc.verso true

/-!
# Target-local tape-2 subroutine lift

The success-only bounded fuel-pair search must run both fixed one-tape
simulators without discarding its persistent logical tapes.  This module lifts
a checked Boolean
{name (full := FoC.Computability.MachineDescription)}`MachineDescription` onto
logical tape 2 while leaving
logical tapes 0 and 1 unchanged.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace BoundedFuelPairSearch
namespace Tape2SubroutineLift

def headMoveOfDirection : Direction -> HeadMove
  | .left => .left
  | .right => .right

@[simp] theorem headMoveOfDirection_apply
    (direction : Direction) (T : Tape Bool) :
    (headMoveOfDirection direction).apply T =
      Tape.move direction T := by
  cases direction <;> rfl

def next (D : MachineDescription)
    (state : Nat) (_read0 _read1 read2 : Option Bool) :
    Option (TypedStep Nat) :=
  match D.lookupTransition state read2 with
  | none => none
  | some transition =>
      some
        { target := transition.target
          action0 := TapeAction.stay
          action1 := TapeAction.stay
          action2 :=
            TapeAction.writeMove transition.write
              (headMoveOfDirection transition.move) }

theorem next_target_mem
    (D : MachineDescription) (hD : D.WellFormed)
    (state : Nat) (_hstate : state ∈ List.range D.stateCount)
    (read0 read1 read2 : Option Bool) (step : TypedStep Nat)
    (hnext : next D state read0 read1 read2 = some step) :
    step.target ∈ List.range D.stateCount := by
  unfold next at hnext
  cases hlookup : D.lookupTransition state read2 with
  | none => simp [hlookup] at hnext
  | some transition =>
      rw [hlookup] at hnext
      injection hnext with hstep
      subst step
      apply List.mem_range.mpr
      exact (hD.right.right.right.left transition
        (MachineDescription.lookupTransition_mem hlookup)).right

theorem halt_next
    (D : MachineDescription) (hD : D.HaltTransitionFree)
    (read0 read1 read2 : Option Bool) :
    next D D.halt read0 read1 read2 = none := by
  unfold next
  cases hlookup : D.lookupTransition D.halt read2 with
  | none => rfl
  | some transition =>
      have hmem := MachineDescription.lookupTransition_mem hlookup
      have hmatches := MachineDescription.lookupTransition_matches hlookup
      exact False.elim (hD transition hmem hmatches.left)

/-- Typed three-tape table that runs {name}`D` only on logical tape 2. -/
def table (D : MachineDescription) (hD : D.SubroutineReady) :
    TypedStateTable Nat where
  states := List.range D.stateCount
  stateCount := D.stateCount
  stateId := id
  start := D.start
  halt := D.halt
  next := next D
  start_mem := List.mem_range.mpr hD.left.right.left
  halt_mem := List.mem_range.mpr hD.left.right.right.left
  stateId_lt := by
    intro state hstate
    exact List.mem_range.mp hstate
  stateId_inj := by
    intro state _ target _ heq
    exact heq
  halt_next := halt_next D hD.right
  next_target_mem := next_target_mem D hD.left

@[simp] theorem table_stateId
    (D : MachineDescription) (hD : D.SubroutineReady)
    (state : Nat) :
    (table D hD).stateId state = state := by
  rfl

/-- One lifted structured step is exactly one step of the source subroutine. -/
theorem description_stepConfig
    (D : MachineDescription) (hD : D.SubroutineReady)
    (state : Nat) (hstate : state < D.stateCount)
    (T0 T1 T2 : Tape Bool) :
    (table D hD).description.stepConfig
        (ThreeTape.config state T0 T1 T2) =
      (D.stepConfig { state := state, tape := T2 }).map
        (fun target =>
          ThreeTape.config target.state T0 T1 target.tape) := by
  change
    (table D hD).description.stepConfig
        (ThreeTape.config ((table D hD).stateId state) T0 T1 T2) = _
  rw [(table D hD).stepConfig_config
    (List.mem_range.mpr hstate) T0 T1 T2]
  change
    (next D state (Tape.read T0) (Tape.read T1) (Tape.read T2)).map
        (fun step =>
          ThreeTape.config step.target
            (step.action0.apply T0)
            (step.action1.apply T1)
            (step.action2.apply T2)) = _
  unfold next MachineDescription.stepConfig
  cases hlookup : D.lookupTransition state (Tape.read T2) with
  | none => rfl
  | some transition =>
      simp only [Option.map_some]
      change some _ = some _
      cases hmove : transition.move <;>
        simp [TapeAction.stay, TapeAction.apply, headMoveOfDirection,
          HeadMove.apply]

/-- A lifted run keeps the first two logical tapes definitionally fixed. -/
theorem description_runConfig
    (D : MachineDescription) (hD : D.SubroutineReady)
    (steps : Nat) (c : MachineDescription.Configuration)
    (hc : c.state < D.stateCount)
    (T0 T1 : Tape Bool) :
    (table D hD).description.runConfig steps
        (ThreeTape.config c.state T0 T1 c.tape) =
      let target := D.runConfig steps c
      ThreeTape.config target.state T0 T1 target.tape := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih =>
      unfold CommonGround.FiniteTransducers.Structured.Description.runConfig
      unfold MachineDescription.runConfig
      rw [description_stepConfig D hD c.state hc T0 T1 c.tape]
      cases hstep : D.stepConfig c with
      | none => rfl
      | some target =>
          simp only [Option.map_some]
          exact ih target
            (MachineDescription.stepConfig_state_bound hD.left hstep)

/-- Exact logical execution of the lifted one-tape subroutine. -/
theorem description_haltsWithTapes
    (D : MachineDescription) (hD : D.SubroutineReady)
    (T0 T1 Tin Tout : Tape Bool)
    (hhalt : D.HaltsFromTape Tin Tout) :
    (table D hD).description.HaltsWithTapes
      (ThreeTape.config D.start T0 T1 Tin)
      [T0, T1, Tout] := by
  rcases hhalt with ⟨steps, hstate, htape⟩
  refine ⟨steps, ?_⟩
  rw [description_runConfig D hD steps
    { state := D.start, tape := Tin }
    hD.left.right.left T0 T1]
  simp [hstate, htape, table, ThreeTape.config]

/-- The physical three-tape lowerer preserves the two caller-owned tapes. -/
theorem lowered_haltsFromTapeEquiv
    (D : MachineDescription) (hD : D.SubroutineReady)
    (T0 T1 Tin Tout : Tape Bool)
    (hhalt : D.HaltsFromTape Tin Tout) :
    (lowerStructured3Description (table D hD).description).HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 T1 Tin)
      (encodedGuardedStructured3Tapes T0 T1 Tout) := by
  have hlowered :=
    lowerStructured3Description_haltsFromConfigWithTapes
      (table D hD).description_wellFormed
      (table D hD).description_haltTransitionFree
      (table D hD).description_supportsReadWriteRows3
      (c := ThreeTape.config D.start T0 T1 Tin)
      (tapes := [T0, T1, Tout])
      rfl (by rfl)
      (description_haltsWithTapes D hD T0 T1 Tin Tout hhalt)
  simpa [encodedGuardedStructured3Tapes, ThreeTape.config] using hlowered

end Tape2SubroutineLift
end BoundedFuelPairSearch

end Computability
end FoC
