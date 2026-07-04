import FoC.Computability.Compiler.DescriptionExecution

set_option doc.verso true

/-!
# Machine descriptions with stay moves

This module adds a small stay-capable intermediate machine description.  It is
not a replacement for
{name (full := FoC.Computability.MachineDescription)}`MachineDescription`: it is a proof-friendly layer
whose transitions may use a logical stay move and can be lowered to ordinary
left/right-only descriptions.

The first lowering deliberately proves only the MVP behavior for one stay row.
General structural and run-preservation theorems should be added on top of the
same compiler once concrete users need them.
-/

namespace FoC
namespace Computability

open Languages

/-- Head movement for the stay-capable description layer. -/
inductive StayDirection where
  | left : StayDirection
  | right : StayDirection
  | stay : StayDirection
deriving Repr, DecidableEq

namespace StayDirection

/-- Interpret a stay-capable move on an ordinary tape. -/
def apply : StayDirection -> Tape Bool -> Tape Bool
  | StayDirection.left, T => Tape.move Direction.left T
  | StayDirection.right, T => Tape.move Direction.right T
  | StayDirection.stay, T => T

end StayDirection

/-- One transition row for a stay-capable finite description. -/
structure StayTransitionDescription where
  source : Nat
  read : Option Bool
  write : Option Bool
  move : StayDirection
  target : Nat
deriving Repr, DecidableEq

namespace StayTransitionDescription

def WellFormed (stateCount : Nat)
    (t : StayTransitionDescription) : Prop :=
  t.source < stateCount ∧ t.target < stateCount

def SameKey (t u : StayTransitionDescription) : Prop :=
  t.source = u.source ∧ t.read = u.read

def SameAction (t u : StayTransitionDescription) : Prop :=
  t.write = u.write ∧ t.move = u.move ∧ t.target = u.target

end StayTransitionDescription

/--
A finite transition-table description that allows logical stay moves.

The shape intentionally mirrors {name}`MachineDescription` so later compiler
proofs can reuse the same concepts.
-/
structure MachineDescriptionWithStay where
  stateCount : Nat
  start : Nat
  halt : Nat
  transitions : List StayTransitionDescription
deriving Repr, DecidableEq

namespace MachineDescriptionWithStay

def Deterministic (D : MachineDescriptionWithStay) : Prop :=
  forall t u : StayTransitionDescription,
    t ∈ D.transitions -> u ∈ D.transitions ->
      StayTransitionDescription.SameKey t u ->
        StayTransitionDescription.SameAction t u

def WellFormed (D : MachineDescriptionWithStay) : Prop :=
  0 < D.stateCount ∧
    D.start < D.stateCount ∧
    D.halt < D.stateCount ∧
    (forall t : StayTransitionDescription,
      t ∈ D.transitions ->
        StayTransitionDescription.WellFormed D.stateCount t) ∧
    D.Deterministic

def HaltTransitionFree (D : MachineDescriptionWithStay) : Prop :=
  forall t : StayTransitionDescription, t ∈ D.transitions ->
    t.source ≠ D.halt

def SubroutineReady (D : MachineDescriptionWithStay) : Prop :=
  D.WellFormed ∧ D.HaltTransitionFree

def Matches (source : Nat) (read : Option Bool)
    (t : StayTransitionDescription) : Bool :=
  t.source == source && t.read == read

def lookupTransition (D : MachineDescriptionWithStay)
    (source : Nat) (read : Option Bool) :
    Option StayTransitionDescription :=
  D.transitions.find? (Matches source read)

structure Configuration where
  state : Nat
  tape : Tape Bool
deriving DecidableEq

def stepConfig (D : MachineDescriptionWithStay)
    (c : Configuration) : Option Configuration :=
  match D.lookupTransition c.state (Tape.read c.tape) with
  | none => none
  | some t =>
      some
        { state := t.target
          tape := t.move.apply (Tape.write t.write c.tape) }

def runConfig (D : MachineDescriptionWithStay) :
    Nat -> Configuration -> Configuration
  | 0, c => c
  | n + 1, c =>
      match D.stepConfig c with
      | none => c
      | some next => runConfig D n next

def HaltsFromTapeIn (D : MachineDescriptionWithStay)
    (n : Nat) (Tin Tout : Tape Bool) : Prop :=
  let final := D.runConfig n { state := D.start, tape := Tin }
  final.state = D.halt ∧ final.tape = Tout

def HaltsFromTape (D : MachineDescriptionWithStay)
    (Tin Tout : Tape Bool) : Prop :=
  exists n : Nat, D.HaltsFromTapeIn n Tin Tout

/-- Preserve the current physical cell while moving to a target state. -/
def preserveTransitions
    (source target : Nat) (move : Direction) :
    List TransitionDescription :=
  [ { source := source, read := none, write := none,
      move := move, target := target }
  , { source := source, read := some false, write := some false,
      move := move, target := target }
  , { source := source, read := some true, write := some true,
      move := move, target := target } ]

/--
Compile one stay-capable transition.

Ordinary left/right rows lower directly.  A stay row writes the requested cell,
moves right into an auxiliary state, then preserves the encountered cell and
moves left to the logical target state.
-/
def compileTransition
    (baseState index : Nat) (t : StayTransitionDescription) :
    List TransitionDescription :=
  match t.move with
  | StayDirection.left =>
      [ { source := t.source, read := t.read, write := t.write,
          move := Direction.left, target := t.target } ]
  | StayDirection.right =>
      [ { source := t.source, read := t.read, write := t.write,
          move := Direction.right, target := t.target } ]
  | StayDirection.stay =>
      let aux := baseState + index
      { source := t.source, read := t.read, write := t.write,
        move := Direction.right, target := aux } ::
        preserveTransitions aux t.target Direction.left

def compileTransitionsFrom
    (baseState index : Nat) :
    List StayTransitionDescription -> List TransitionDescription
  | [] => []
  | t :: rest =>
      compileTransition baseState index t ++
        compileTransitionsFrom baseState (index + 1) rest

/-- Compile a stay-capable description to the ordinary left/right-only model. -/
def compile (D : MachineDescriptionWithStay) : MachineDescription where
  stateCount := D.stateCount + D.transitions.length
  start := D.start
  halt := D.halt
  transitions := compileTransitionsFrom D.stateCount 0 D.transitions

@[simp] theorem compile_stateCount (D : MachineDescriptionWithStay) :
    D.compile.stateCount = D.stateCount + D.transitions.length := by
  rfl

@[simp] theorem compile_start (D : MachineDescriptionWithStay) :
    D.compile.start = D.start := by
  rfl

@[simp] theorem compile_halt (D : MachineDescriptionWithStay) :
    D.compile.halt = D.halt := by
  rfl

@[simp] theorem compile_transitions (D : MachineDescriptionWithStay) :
    D.compile.transitions =
      compileTransitionsFrom D.stateCount 0 D.transitions := by
  rfl

/-!
## MVP stay-row example
-/

/-- A one-row stay-capable machine used to validate the lowering shape. -/
def singleStayDescription
    (read write : Option Bool) : MachineDescriptionWithStay where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ { source := 0
        read := read
        write := write
        move := StayDirection.stay
        target := 1 } ]

def singleStaySourceTape
    (read : Option Bool) (left right : List (Option Bool)) :
    Tape Bool :=
  { left := left, head := read, right := right }

def singleStayTargetTape
    (write : Option Bool) (left right : List (Option Bool)) :
    Tape Bool :=
  { left := left, head := write, right := right }

theorem singleStayDescription_run
    (read write : Option Bool)
    (left right : List (Option Bool)) :
    (singleStayDescription read write).runConfig 1
        { state := (singleStayDescription read write).start
          tape := singleStaySourceTape read left right } =
      { state := (singleStayDescription read write).halt
        tape := singleStayTargetTape write left right } := by
  cases read <;>
    simp [singleStayDescription, singleStaySourceTape,
      singleStayTargetTape, runConfig, stepConfig, lookupTransition,
      Matches, StayDirection.apply, Tape.read, Tape.write]

theorem singleStayDescription_haltsFromTape
    (read write : Option Bool)
    (left right : List (Option Bool)) :
    (singleStayDescription read write).HaltsFromTape
      (singleStaySourceTape read left right)
      (singleStayTargetTape write left right) := by
  refine ⟨1, ?_⟩
  constructor <;>
    rw [singleStayDescription_run]

private theorem tape_move_left_move_right_equiv
    (T : Tape Bool) :
    Tape.Equiv
      (Tape.move Direction.left (Tape.move Direction.right T)) T := by
  cases T with
  | mk left head right =>
      cases right with
      | nil =>
          cases head <;>
            simp [Tape.Equiv, Tape.move, Tape.moveLeft,
              Tape.moveRight, Tape.dropTrailingNone]
      | cons cell rest =>
          simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem compile_singleStayDescription_run
    (read write : Option Bool)
    (left right : List (Option Bool)) :
    ((singleStayDescription read write).compile).runConfig 2
        { state := ((singleStayDescription read write).compile).start
          tape := singleStaySourceTape read left right } =
      { state := ((singleStayDescription read write).compile).halt
        tape :=
          Tape.move Direction.left
            (Tape.move Direction.right
          (singleStayTargetTape write left right)) } := by
  cases read <;> cases write <;> cases right with
  | nil =>
      simp [singleStayDescription, compile, compileTransitionsFrom,
        compileTransition, preserveTransitions, singleStaySourceTape,
        singleStayTargetTape, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons head tail =>
      cases head with
      | none =>
          simp [singleStayDescription, compile, compileTransitionsFrom,
            compileTransition, preserveTransitions, singleStaySourceTape,
            singleStayTargetTape, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            Tape.moveRight]
      | some bit =>
          cases bit <;>
            simp [singleStayDescription, compile, compileTransitionsFrom,
              compileTransition, preserveTransitions, singleStaySourceTape,
              singleStayTargetTape, MachineDescription.runConfig,
              MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, Tape.read, Tape.write,
              Tape.move, Tape.moveLeft, Tape.moveRight]

theorem compile_singleStayDescription_haltsFromTapeEquiv
    (read write : Option Bool)
    (left right : List (Option Bool)) :
    ((singleStayDescription read write).compile).HaltsFromTapeEquiv
      (singleStaySourceTape read left right)
      (singleStayTargetTape write left right) := by
  refine
    ⟨Tape.move Direction.left
        (Tape.move Direction.right
          (singleStayTargetTape write left right)), ?_, ?_⟩
  · refine ⟨2, ?_⟩
    constructor <;>
      rw [compile_singleStayDescription_run]
  · exact tape_move_left_move_right_equiv
      (singleStayTargetTape write left right)

end MachineDescriptionWithStay
end Computability
end FoC
