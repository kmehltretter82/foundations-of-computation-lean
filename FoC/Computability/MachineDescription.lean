import FoC.Computability.TuringMachine

set_option doc.verso true

/-!
# Finite machine descriptions

This module defines the executable semantics of first-order one-tape machine
descriptions.  A description stores natural-numbered states and a finite list
of transition rows; it is therefore concrete data rather than an arbitrary
Lean transition function.

The layer is deliberately independent of serialization.  Token alphabets,
description encoders, and parsers live in
{module -checked}`FoC.Computability.Encoding`; languages obtained by decoding and
running those tokens live in
{module -checked}`FoC.Computability.DescriptionLanguages`.  Concrete universal-runner
constructions belong to the compiler layer.

Missing transition rows make execution stutter. The halting predicates still
require the designated halt state, so being stuck in any other state is not
acceptance.
-/

namespace FoC
namespace Computability

open Foundation
open Languages

/-!
## Transition Tables and Well-Formedness

A description separates raw finite data from its validity conditions.  Rows
carry lookup keys and actions; well-formedness later adds state bounds and
determinism without changing the executable representation.
-/

/-- A first-order transition row for a Boolean-tape machine. -/
structure TransitionDescription where
  source : Nat
  read : Option Bool
  write : Option Bool
  move : Direction
  target : Nat
deriving DecidableEq

/--
A finite transition-table machine with natural-numbered states.

The bounds and determinism requirements are exposed separately; the raw
structure remains executable even before those properties are proved.
-/
structure MachineDescription where
  stateCount : Nat
  start : Nat
  halt : Nat
  transitions : List TransitionDescription
deriving DecidableEq

namespace TransitionDescription

/-- Both endpoints of a transition lie in the declared state range. -/
def WellFormed (stateCount : Nat) (t : TransitionDescription) : Prop :=
  t.source < stateCount ∧ t.target < stateCount

/-- Two rows inspect the same state and tape symbol. -/
def SameKey (t u : TransitionDescription) : Prop :=
  t.source = u.source ∧ t.read = u.read

/-- Two rows prescribe the same write, move, and target state. -/
def SameAction (t u : TransitionDescription) : Prop :=
  t.write = u.write ∧ t.move = u.move ∧ t.target = u.target

end TransitionDescription

namespace MachineDescription

/-- Rows with the same lookup key prescribe the same action. -/
def Deterministic (D : MachineDescription) : Prop :=
  forall t u : TransitionDescription,
    t ∈ D.transitions -> u ∈ D.transitions ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u

/--
The state range is nonempty, contains the entry and halt states, contains every
transition endpoint, and the transition table is deterministic.
-/
def WellFormed (D : MachineDescription) : Prop :=
  0 < D.stateCount ∧
    D.start < D.stateCount ∧
    D.halt < D.stateCount ∧
    (forall t : TransitionDescription,
      t ∈ D.transitions ->
        TransitionDescription.WellFormed D.stateCount t) ∧
    D.Deterministic

/-- Executable lookup-key test for a transition row. -/
def Matches (source : Nat) (read : Option Bool)
    (t : TransitionDescription) : Bool :=
  t.source == source && t.read == read

/-- Return the first transition row matching the current state and symbol. -/
def lookupTransition (D : MachineDescription)
    (source : Nat) (read : Option Bool) :
    Option TransitionDescription :=
  D.transitions.find? (Matches source read)

/-!
## Executable Configurations and Runs

The operational semantics starts from the canonical input tape, performs one
table lookup per step, and iterates for a finite fuel bound.  Acceptance means
that some such run reaches the designated halt state.
-/

/-- Runtime state and tape for a finite description. -/
structure Configuration where
  state : Nat
  tape : Tape Bool
deriving DecidableEq

/-- Start a description on the canonical tape for an input word. -/
def initial (D : MachineDescription) (w : Word Bool) :
    Configuration where
  state := D.start
  tape := Tape.input w

/-- Execute one table row, or return {lit}`none` when no row matches. -/
def stepConfig (D : MachineDescription)
    (c : Configuration) : Option Configuration :=
  match D.lookupTransition c.state (Tape.read c.tape) with
  | none => none
  | some t =>
      some
        { state := t.target
          tape := Tape.move t.move (Tape.write t.write c.tape) }

/--
Run for exactly the supplied fuel, stuttering once the description has no
matching transition.
-/
def runConfig (D : MachineDescription) :
    Nat -> Configuration -> Configuration
  | 0, c => c
  | n + 1, c =>
      match D.stepConfig c with
      | none => c
      | some next => runConfig D n next

/-- The fuel-bounded run reaches the designated halt state. -/
def HaltsIn (D : MachineDescription) (n : Nat) (w : Word Bool) : Prop :=
  (D.runConfig n (D.initial w)).state = D.halt

instance (D : MachineDescription) (n : Nat) (w : Word Bool) :
    Decidable (D.HaltsIn n w) := by
  unfold HaltsIn
  infer_instance

/-- Some finite-fuel run reaches the designated halt state. -/
def HaltsOnInput (D : MachineDescription) (w : Word Bool) : Prop :=
  exists n : Nat, D.HaltsIn n w

/-!
## Compilation to Turing Machines

Natural-numbered description states embed into a finite state type.  Successful
description steps then become steps of the ordinary {name}`TuringMachine`
semantics.
-/

/-- Embed an unbounded natural-numbered state into the compiled state type. -/
def stateOfNat (D : MachineDescription) (n : Nat) :
    Fin (D.stateCount + 1) :=
  if h : n < D.stateCount + 1 then
    ⟨n, h⟩
  else
    ⟨D.stateCount, Nat.lt_succ_self D.stateCount⟩

theorem stateOfNat_val_of_lt {D : MachineDescription} {n : Nat}
    (h : n < D.stateCount + 1) :
    (D.stateOfNat n).val = n := by
  simp [stateOfNat, h]

/-- Embed a description configuration into its compiled machine. -/
def toTMConfig (D : MachineDescription) (c : Configuration) :
    TuringMachine.Configuration Bool (Fin (D.stateCount + 1)) where
  state := D.stateOfNat c.state
  tape := c.tape

/-- Compile the finite table into the ordinary {name}`TuringMachine` model. -/
def toTuringMachine (D : MachineDescription) :
    TuringMachine Bool (Fin (D.stateCount + 1)) where
  start := D.stateOfNat D.start
  halt := D.stateOfNat D.halt
  transition := fun q cell =>
    match D.lookupTransition q.val cell with
    | none => none
    | some t => some (t.write, t.move, D.stateOfNat t.target)
  statesFinite := FiniteType.fin (D.stateCount + 1)

theorem toTuringMachine_transition_of_lookup
    {D : MachineDescription} {source : Nat} {read : Option Bool}
    {t : TransitionDescription}
    (hsource : source < D.stateCount + 1)
    (hlookup : D.lookupTransition source read = some t) :
    (D.toTuringMachine).transition (D.stateOfNat source) read =
      some (t.write, t.move, D.stateOfNat t.target) := by
  simp [toTuringMachine, stateOfNat_val_of_lt hsource, hlookup]

theorem toTuringMachine_step_of_stepConfig
    {D : MachineDescription} {c d : Configuration}
    (hsource : c.state < D.stateCount + 1)
    (hstep : D.stepConfig c = some d) :
    TuringMachine.Step D.toTuringMachine
      (D.toTMConfig c) (D.toTMConfig d) := by
  unfold stepConfig at hstep
  cases hlookup : D.lookupTransition c.state (Tape.read c.tape) with
  | none =>
      rw [hlookup] at hstep
      cases hstep
  | some t =>
      rw [hlookup] at hstep
      cases hstep
      exact TuringMachine.Step.mk
        (toTuringMachine_transition_of_lookup
          (D := D) (source := c.state)
          (read := Tape.read c.tape) hsource hlookup)

end MachineDescription

end Computability
end FoC
