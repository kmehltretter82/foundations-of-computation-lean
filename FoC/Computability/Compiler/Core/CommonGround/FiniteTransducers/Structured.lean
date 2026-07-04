import FoC.Computability.Compiler.DescriptionExecution

set_option doc.verso true

/-!
# Structured logical-tape machines

This module adds an executable, finite, multi-logical-tape layer for compiler
construction leaves.  A transition reads the current cells of all logical
tapes, applies one local action to each tape, and changes finite-control state.

The layer is deliberately not a replacement for
{name}`FoC.Computability.MachineDescription`.  It is a proof-friendly
intermediate language for construction work where a one-tape layout proof would
otherwise obscure the algorithm.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured

/-- A local head movement for a logical tape. -/
inductive HeadMove where
  | stay : HeadMove
  | left : HeadMove
  | right : HeadMove
deriving Repr, DecidableEq

namespace HeadMove

/-- Interpret a structured head movement on the ordinary finite tape window. -/
def apply : HeadMove -> Tape Bool -> Tape Bool
  | HeadMove.stay, T => T
  | HeadMove.left, T => Tape.move Direction.left T
  | HeadMove.right, T => Tape.move Direction.right T

def toString : HeadMove -> String
  | HeadMove.stay => "S"
  | HeadMove.left => "L"
  | HeadMove.right => "R"

end HeadMove

/--
One action on one logical tape.  {lit}`write? = none` preserves the current
cell; {lit}`write? = some cell` writes that cell before the head move.
-/
structure TapeAction where
  write? : Option (Option Bool) := none
  move : HeadMove := HeadMove.stay
deriving Repr, DecidableEq

namespace TapeAction

/-- The no-op action used when a row omits an action for a missing tape. -/
def stay : TapeAction where
  write? := none
  move := HeadMove.stay

/-- Preserve the current cell, then move the logical head. -/
@[simp] def preserveMove (move : HeadMove) : TapeAction where
  write? := none
  move := move

/-- Write one cell, then move the logical head. -/
@[simp] def writeMove (cell : Option Bool) (move : HeadMove) : TapeAction where
  write? := some cell
  move := move

/-- Apply a local tape action: optional write first, then movement. -/
def apply (action : TapeAction) (T : Tape Bool) : Tape Bool :=
  let written :=
    match action.write? with
    | none => T
    | some cell => Tape.write cell T
  action.move.apply written

@[simp] theorem preserveMove_apply
    (move : HeadMove) (T : Tape Bool) :
    (preserveMove move).apply T = move.apply T := by
  rfl

@[simp] theorem writeMove_apply
    (cell : Option Bool) (move : HeadMove) (T : Tape Bool) :
    (writeMove cell move).apply T =
      move.apply (Tape.write cell T) := by
  rfl

def debugString (action : TapeAction) : String :=
  "write=" ++ reprStr action.write? ++ " move=" ++ action.move.toString

end TapeAction

/--
One finite transition row.  The {lit}`reads` list is the full tuple of logical
tape head cells, and {lit}`actions` contains one action per logical tape.
-/
structure Transition where
  source : Nat
  reads : List (Option Bool)
  actions : List TapeAction
  target : Nat
deriving Repr, DecidableEq

namespace Transition

/-- Build a single-logical-tape transition row. -/
@[simp] def oneTape
    (source : Nat) (read : Option Bool)
    (action : TapeAction) (target : Nat) : Transition where
  source := source
  reads := [read]
  actions := [action]
  target := target

def WellFormed (stateCount tapeCount : Nat) (t : Transition) : Prop :=
  t.source < stateCount ∧
    t.target < stateCount ∧
    t.reads.length = tapeCount ∧
    t.actions.length = tapeCount

def SameKey (t u : Transition) : Prop :=
  t.source = u.source ∧ t.reads = u.reads

def SameAction (t u : Transition) : Prop :=
  t.actions = u.actions ∧ t.target = u.target

end Transition

/-!
## One-tape table helpers
-/

namespace OneTape

/-- Build one row of a single-logical-tape structured machine. -/
@[simp] def row
    (source : Nat) (read : Option Bool)
    (write? : Option (Option Bool)) (move : HeadMove)
    (target : Nat) : Transition :=
  Transition.oneTape source read
    { write? := write?, move := move } target

/-- Preserve the current cell, then move. -/
@[simp] def preserve
    (source : Nat) (read : Option Bool)
    (move : HeadMove) (target : Nat) : Transition :=
  row source read none move target

/-- Write a cell, then move. -/
@[simp] def write
    (source : Nat) (read cell : Option Bool)
    (move : HeadMove) (target : Nat) : Transition :=
  row source read (some cell) move target

/-- Erase the current cell, then move. -/
@[simp] def erase
    (source : Nat) (read : Option Bool)
    (move : HeadMove) (target : Nat) : Transition :=
  write source read none move target

end OneTape

/--
A finite structured machine over {lit}`tapeCount` logical tapes and {name}`Nat`
control states.  The transition table is concrete data, matching the style of
{name}`FoC.Computability.MachineDescription`.
-/
structure Description where
  tapeCount : Nat
  stateCount : Nat
  start : Nat
  halt : Nat
  transitions : List Transition
deriving Repr, DecidableEq

/-- A structured-machine configuration. -/
structure Configuration where
  state : Nat
  tapes : List (Tape Bool)
deriving DecidableEq

namespace Configuration

/-- A configuration with exactly one logical tape. -/
def oneTape (state : Nat) (T : Tape Bool) : Configuration where
  state := state
  tapes := [T]

@[simp] theorem oneTape_eq
    (state : Nat) (T : Tape Bool) :
    oneTape state T = { state := state, tapes := [T] } := by
  rfl

@[simp] theorem oneTape_state (state : Nat) (T : Tape Bool) :
    (oneTape state T).state = state := by
  rfl

@[simp] theorem oneTape_tapes (state : Nat) (T : Tape Bool) :
    (oneTape state T).tapes = [T] := by
  rfl

def WellFormed (D : Description) (c : Configuration) : Prop :=
  c.state < D.stateCount ∧ c.tapes.length = D.tapeCount

end Configuration

namespace Description

def Deterministic (D : Description) : Prop :=
  forall t u : Transition,
    t ∈ D.transitions -> u ∈ D.transitions ->
      Transition.SameKey t u ->
        Transition.SameAction t u

def WellFormed (D : Description) : Prop :=
  0 < D.tapeCount ∧
    0 < D.stateCount ∧
    D.start < D.stateCount ∧
    D.halt < D.stateCount ∧
    (forall t : Transition,
      t ∈ D.transitions ->
        Transition.WellFormed D.stateCount D.tapeCount t) ∧
    D.Deterministic

def HaltTransitionFree (D : Description) : Prop :=
  forall t : Transition, t ∈ D.transitions -> t.source ≠ D.halt

def SubroutineReady (D : Description) : Prop :=
  D.WellFormed ∧ D.HaltTransitionFree

def tapeAt (tapes : List (Tape Bool)) (index : Nat) : Tape Bool :=
  tapes.getD index Tape.blank

def currentReads (D : Description) (c : Configuration) :
    List (Option Bool) :=
  (List.range D.tapeCount).map
    (fun index => Tape.read (tapeAt c.tapes index))

def applyActions
    (D : Description) (actions : List TapeAction)
    (tapes : List (Tape Bool)) : List (Tape Bool) :=
  (List.range D.tapeCount).map
    (fun index =>
      (actions.getD index TapeAction.stay).apply
        (tapeAt tapes index))

@[simp] theorem currentReads_one
    (D : Description) (h : D.tapeCount = 1)
    (state : Nat) (T : Tape Bool) :
    D.currentReads { state := state, tapes := [T] } = [Tape.read T] := by
  cases D
  cases h
  rfl

@[simp] theorem currentReads_two
    (D : Description) (h : D.tapeCount = 2)
    (state : Nat) (T U : Tape Bool) :
    D.currentReads { state := state, tapes := [T, U] } =
      [Tape.read T, Tape.read U] := by
  cases D
  cases h
  rfl

@[simp] theorem currentReads_three
    (D : Description) (h : D.tapeCount = 3)
    (state : Nat) (T U V : Tape Bool) :
    D.currentReads { state := state, tapes := [T, U, V] } =
      [Tape.read T, Tape.read U, Tape.read V] := by
  cases D
  cases h
  rfl

@[simp] theorem applyActions_one
    (D : Description) (h : D.tapeCount = 1)
    (action : TapeAction) (T : Tape Bool) :
    D.applyActions [action] [T] = [action.apply T] := by
  cases D
  cases h
  rfl

@[simp] theorem currentReads_oneTape
    (D : Description) (h : D.tapeCount = 1)
    (state : Nat) (T : Tape Bool) :
    D.currentReads (Configuration.oneTape state T) = [Tape.read T] := by
  exact currentReads_one D h state T

@[simp] theorem applyActions_oneTape
    (D : Description) (h : D.tapeCount = 1)
    (action : TapeAction) (state : Nat) (T : Tape Bool) :
    D.applyActions [action] (Configuration.oneTape state T).tapes =
      [action.apply T] := by
  exact applyActions_one D h action T

@[simp] theorem applyActions_two
    (D : Description) (h : D.tapeCount = 2)
    (first second : TapeAction) (T U : Tape Bool) :
    D.applyActions [first, second] [T, U] =
      [first.apply T, second.apply U] := by
  cases D
  cases h
  rfl

@[simp] theorem applyActions_three
    (D : Description) (h : D.tapeCount = 3)
    (first second third : TapeAction) (T U V : Tape Bool) :
    D.applyActions [first, second, third] [T, U, V] =
      [first.apply T, second.apply U, third.apply V] := by
  cases D
  cases h
  rfl

def Matches (state : Nat)
    (reads : List (Option Bool)) (t : Transition) : Bool :=
  t.source == state && t.reads == reads

def lookupTransition (D : Description) (c : Configuration) :
    Option Transition :=
  D.transitions.find? (Matches c.state (D.currentReads c))

def stepConfig (D : Description)
    (c : Configuration) : Option Configuration :=
  match D.lookupTransition c with
  | none => none
  | some t =>
      some
        { state := t.target
          tapes := D.applyActions t.actions c.tapes }

def runConfig (D : Description) :
    Nat -> Configuration -> Configuration
  | 0, c => c
  | n + 1, c =>
      match D.stepConfig c with
      | none => c
      | some next => D.runConfig n next

def initial (D : Description) (inputs : List (Word Bool)) :
    Configuration where
  state := D.start
  tapes :=
    (List.range D.tapeCount).map
      (fun index => Tape.input (inputs.getD index []))

def HaltsIn (D : Description) (n : Nat)
    (c : Configuration) : Prop :=
  (D.runConfig n c).state = D.halt

instance (D : Description) (n : Nat) (c : Configuration) :
    Decidable (D.HaltsIn n c) := by
  unfold HaltsIn
  infer_instance

def HaltsFromConfig (D : Description) (c : Configuration) : Prop :=
  exists n : Nat, D.HaltsIn n c

def HaltsWithTapes (D : Description)
    (c : Configuration) (tapes : List (Tape Bool)) : Prop :=
  exists n : Nat, D.runConfig n c = { state := D.halt, tapes := tapes }

/-- One relational structured-machine step. -/
inductive Step (D : Description) :
    Configuration -> Configuration -> Prop where
  | mk {c : Configuration} {t : Transition} :
      D.lookupTransition c = some t ->
      Step D c
        { state := t.target
          tapes := D.applyActions t.actions c.tapes }

/-- Relational exact-step execution, useful when proofs do not want to unfold
the executable bounded runner. -/
inductive ComputesIn (D : Description) :
    Nat -> Configuration -> Configuration -> Prop where
  | zero (c : Configuration) : ComputesIn D 0 c c
  | succ {n : Nat} {c next final : Configuration} :
      D.stepConfig c = some next ->
      ComputesIn D n next final ->
      ComputesIn D (n + 1) c final

def Computes (D : Description)
    (c final : Configuration) : Prop :=
  exists n : Nat, ComputesIn D n c final

theorem stepConfig_eq_some_iff_step
    {D : Description} {c d : Configuration} :
    D.stepConfig c = some d <-> Step D c d := by
  constructor
  · intro hstep
    unfold stepConfig at hstep
    cases hlookup : D.lookupTransition c with
    | none =>
        simp [hlookup] at hstep
    | some t =>
        simp [hlookup] at hstep
        cases hstep
        exact Step.mk hlookup
  · intro hstep
    cases hstep with
    | mk hlookup =>
        simp [stepConfig, hlookup]

theorem stepConfig_functional
    {D : Description} {c d e : Configuration}
    (hd : D.stepConfig c = some d)
    (he : D.stepConfig c = some e) :
    d = e := by
  rw [hd] at he
  exact Option.some.inj he

theorem runConfig_of_stepConfig_none
    {D : Description} {c : Configuration}
    (hstep : D.stepConfig c = none) :
    forall n : Nat, D.runConfig n c = c := by
  intro n
  induction n with
  | zero => rfl
  | succ n _ih =>
      simp [runConfig, hstep]

theorem lookupTransition_mem
    {D : Description} {c : Configuration} {t : Transition}
    (h : D.lookupTransition c = some t) :
    t ∈ D.transitions := by
  unfold lookupTransition at h
  let p := Matches c.state (D.currentReads c)
  have hmem :
      forall l : List Transition,
        l.find? p = some t -> t ∈ l := by
    intro l
    induction l with
    | nil =>
        intro hnil
        simp at hnil
    | cons a rest ih =>
        intro hfind
        rw [List.find?_cons] at hfind
        cases hm : p a
        · simp [hm] at hfind
          have ht : t ∈ rest := ih hfind
          simp [ht]
        · simp [hm] at hfind
          cases hfind
          simp
  exact hmem D.transitions h

theorem lookupTransition_match
    {D : Description} {c : Configuration} {t : Transition}
    (h : D.lookupTransition c = some t) :
    t.source = c.state ∧ t.reads = D.currentReads c := by
  unfold lookupTransition at h
  have hpred :
      Matches c.state (D.currentReads c) t = true := by
    exact List.find?_some h
  simpa [Matches] using hpred

theorem stepConfig_state_bound
    {D : Description} {c d : Configuration}
    (hD : D.WellFormed)
    (hstep : D.stepConfig c = some d) :
    d.state < D.stateCount := by
  unfold stepConfig at hstep
  cases hlookup : D.lookupTransition c with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      simp [hlookup] at hstep
      cases hstep
      have htmem : t ∈ D.transitions := lookupTransition_mem hlookup
      exact (hD.right.right.right.right.left t htmem).right.left

theorem stepConfig_tape_count
    {D : Description} {c d : Configuration}
    (hstep : D.stepConfig c = some d) :
    d.tapes.length = D.tapeCount := by
  unfold stepConfig at hstep
  cases hlookup : D.lookupTransition c with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      simp [hlookup, applyActions] at hstep
      cases hstep
      simp

theorem runConfig_state_bound
    {D : Description}
    (hD : D.WellFormed) {n : Nat} {c : Configuration}
    (hc : c.state < D.stateCount) :
    (D.runConfig n c).state < D.stateCount := by
  induction n generalizing c with
  | zero =>
      exact hc
  | succ n ih =>
      change
        (match D.stepConfig c with
        | none => c
        | some next => D.runConfig n next).state < D.stateCount
      cases hstep : D.stepConfig c with
      | none =>
          exact hc
      | some next =>
          exact ih (stepConfig_state_bound hD hstep)

theorem lookupTransition_halt_none
    {D : Description}
    (hD : D.HaltTransitionFree) (c : Configuration)
    (hc : c.state = D.halt) :
    D.lookupTransition c = none := by
  unfold lookupTransition
  apply (List.find?_eq_none).mpr
  intro t ht hmatch
  have hpair :
      t.source = c.state ∧ t.reads = D.currentReads c := by
    simpa [Matches] using hmatch
  exact hD t ht (hpair.left.trans hc)

theorem stepConfig_halt_none
    {D : Description}
    (hD : D.HaltTransitionFree) (c : Configuration)
    (hc : c.state = D.halt) :
    D.stepConfig c = none := by
  simp [stepConfig, lookupTransition_halt_none hD c hc]

theorem runConfig_halt
    {D : Description}
    (hD : D.HaltTransitionFree) (c : Configuration)
    (hc : c.state = D.halt) :
    forall n : Nat, D.runConfig n c = c := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n _ih =>
      simp [runConfig, stepConfig_halt_none hD c hc]

theorem runConfig_add (D : Description)
    (n m : Nat) (c : Configuration) :
    D.runConfig (n + m) c =
      D.runConfig m (D.runConfig n c) := by
  induction n generalizing c with
  | zero =>
      simp [runConfig]
  | succ n ih =>
      rw [Nat.succ_add]
      simp [runConfig]
      cases hstep : D.stepConfig c with
      | none =>
          simp [runConfig_of_stepConfig_none hstep]
      | some next =>
          simp [ih next]

theorem computesIn_runConfig
    {D : Description} {n : Nat} {c d : Configuration}
    (h : ComputesIn D n c d) :
    D.runConfig n c = d := by
  induction h with
  | zero c =>
      rfl
  | succ hstep _hrest ih =>
      simp [runConfig, hstep, ih]

end Description

/-!
## Debug views
-/

/-- Printable view of a logical tape. -/
structure TapeDebugView where
  left : List (Option Bool)
  head : Option Bool
  right : List (Option Bool)
deriving Repr, DecidableEq

/-- Printable view of a structured-machine configuration. -/
structure ConfigDebugView where
  state : Nat
  tapes : List TapeDebugView
deriving Repr, DecidableEq

/-- Printable view of a tape action. -/
structure TapeActionDebugView where
  write? : Option (Option Bool)
  move : HeadMove
deriving Repr, DecidableEq

/-- Printable view of one transition row. -/
structure TransitionDebugView where
  source : Nat
  reads : List (Option Bool)
  actions : List TapeActionDebugView
  target : Nat
deriving Repr, DecidableEq

/-- Printable view of one structured-machine step. -/
structure StepDebugView where
  step : Nat
  before : ConfigDebugView
  reads : List (Option Bool)
  transition : Option TransitionDebugView
  after : ConfigDebugView
deriving Repr, DecidableEq

def tapeDebugView (T : Tape Bool) : TapeDebugView where
  left := T.left
  head := T.head
  right := T.right

def configDebugView (c : Configuration) : ConfigDebugView where
  state := c.state
  tapes := c.tapes.map tapeDebugView

def tapeActionDebugView (action : TapeAction) : TapeActionDebugView where
  write? := action.write?
  move := action.move

def transitionDebugView (t : Transition) : TransitionDebugView where
  source := t.source
  reads := t.reads
  actions := t.actions.map tapeActionDebugView
  target := t.target

namespace Configuration

/-- Printable view of a structured-machine configuration. -/
def debugView (c : Configuration) : ConfigDebugView :=
  configDebugView c

end Configuration

namespace Description

def stepConfigDebug
    (D : Description) (c : Configuration) :
    Option Transition × Configuration :=
  match D.lookupTransition c with
  | none => (none, c)
  | some t =>
      (some t,
        { state := t.target
          tapes := D.applyActions t.actions c.tapes })

private def debugTraceAux
    (stopAtHalt : Bool) (D : Description) :
    Nat -> Nat -> Configuration -> List StepDebugView
  | 0, _, _ => []
  | fuel + 1, step, c =>
      if stopAtHalt && c.state == D.halt then
        []
      else
        let reads := D.currentReads c
        let (transition?, next) := D.stepConfigDebug c
        let row : StepDebugView :=
          { step := step
            before := c.debugView
            reads := reads
            transition := transition?.map transitionDebugView
            after := next.debugView }
        match transition? with
        | none => [row]
        | some _ =>
            row :: debugTraceAux stopAtHalt D fuel (step + 1) next

/--
Trace a structured run, stopping at halt, a stuck configuration, or exhausted
fuel.
-/
def debugTrace
    (D : Description) (fuel : Nat)
    (c : Configuration) : List StepDebugView :=
  debugTraceAux true D fuel 0 c

/--
Trace a structured run without treating the halt state specially.  This
matches the operational shape of {name}`runConfig`, which only stops early when
no transition matches.
-/
def debugTraceFixed
    (D : Description) (fuel : Nat)
    (c : Configuration) : List StepDebugView :=
  debugTraceAux false D fuel 0 c

def debugRunFinal
    (D : Description) (fuel : Nat)
    (c : Configuration) : ConfigDebugView :=
  (D.runConfig fuel c).debugView

def joinStrings (sep : String) : List String -> String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ sep ++ joinStrings sep rest

def tapeDebugString (T : TapeDebugView) : String :=
  "left=" ++ reprStr T.left ++ ", head=" ++ reprStr T.head ++
    ", right=" ++ reprStr T.right

private def tapeDebugStrings :
    Nat -> List TapeDebugView -> List String
  | _, [] => []
  | index, tape :: rest =>
      ("t" ++ reprStr index ++ "(" ++ tapeDebugString tape ++ ")") ::
        tapeDebugStrings (index + 1) rest

def configDebugString (c : ConfigDebugView) : String :=
  "state=" ++ reprStr c.state ++ ", " ++
    joinStrings ", " (tapeDebugStrings 0 c.tapes)

def tapeActionDebugString (action : TapeActionDebugView) : String :=
  "write=" ++ reprStr action.write? ++ " move=" ++ action.move.toString

private def tapeActionDebugStrings :
    Nat -> List TapeActionDebugView -> List String
  | _, [] => []
  | index, action :: rest =>
      ("t" ++ reprStr index ++ "(" ++
        tapeActionDebugString action ++ ")") ::
        tapeActionDebugStrings (index + 1) rest

def transitionDebugString (t : TransitionDebugView) : String :=
  "q" ++ reprStr t.source ++ " reads=" ++ reprStr t.reads ++
    " actions=[" ++ joinStrings ", " (tapeActionDebugStrings 0 t.actions) ++
    "] -> q" ++ reprStr t.target

def optionTransitionDebugString :
    Option TransitionDebugView -> String
  | none => "none"
  | some t => transitionDebugString t

def stepDebugString (row : StepDebugView) : String :=
  "#" ++ reprStr row.step ++
    " before(" ++ configDebugString row.before ++ ")" ++
    " reads=" ++ reprStr row.reads ++
    " transition=" ++ optionTransitionDebugString row.transition ++
    " after(" ++ configDebugString row.after ++ ")"

def debugTraceString
    (D : Description) (fuel : Nat)
    (c : Configuration) : String :=
  joinStrings "\n" ((D.debugTrace fuel c).map stepDebugString)

def debugTraceRange
    (D : Description) (fuel : Nat)
    (c : Configuration) (start stop : Nat) :
    List StepDebugView :=
  (D.debugTrace fuel c).filter
    (fun row => decide (start ≤ row.step ∧ row.step < stop))

def debugTraceFrom
    (D : Description) (fuel : Nat)
    (c : Configuration) (start : Nat) :
    List StepDebugView :=
  (D.debugTrace fuel c).filter
    (fun row => decide (start ≤ row.step))

/-- A named predicate over step-indexed structured configurations. -/
structure DebugBreakpoint where
  name : String
  predicate : Nat -> Configuration -> Bool

/-- The first structured configuration that satisfies a breakpoint. -/
structure DebugBreakpointHit where
  name : String
  step : Nat
  config : ConfigDebugView
deriving Repr, DecidableEq

private def debugBreakpointHit
    (breakpoint : DebugBreakpoint) (step : Nat)
    (c : Configuration) : DebugBreakpointHit where
  name := breakpoint.name
  step := step
  config := c.debugView

private def debugFirstBreakpointAux
    (D : Description) (breakpoint : DebugBreakpoint) :
    Nat -> Nat -> Configuration -> Option DebugBreakpointHit
  | 0, step, c =>
      if breakpoint.predicate step c then
        some (debugBreakpointHit breakpoint step c)
      else
        none
  | fuel + 1, step, c =>
      if breakpoint.predicate step c then
        some (debugBreakpointHit breakpoint step c)
      else if c.state == D.halt then
        none
      else
        match D.stepConfig c with
        | none => none
        | some next =>
            debugFirstBreakpointAux D breakpoint fuel (step + 1) next

def debugFirstBreakpoint
    (D : Description) (fuel : Nat)
    (c : Configuration) (breakpoint : DebugBreakpoint) :
    Option DebugBreakpointHit :=
  debugFirstBreakpointAux D breakpoint fuel 0 c

def debugTraceUntilBreakpoint
    (D : Description) (fuel : Nat)
    (c : Configuration) (breakpoint : DebugBreakpoint) :
    List StepDebugView :=
  match D.debugFirstBreakpoint fuel c breakpoint with
  | none => D.debugTrace fuel c
  | some hit => D.debugTraceRange fuel c 0 (hit.step + 1)

def debugTraceAroundBreakpoint
    (D : Description) (fuel : Nat)
    (c : Configuration) (breakpoint : DebugBreakpoint)
    (radius : Nat) : List StepDebugView :=
  match D.debugFirstBreakpoint fuel c breakpoint with
  | none => []
  | some hit =>
      D.debugTraceRange fuel c
        (hit.step - radius) (hit.step + radius + 1)

def breakOnState (state : Nat) : DebugBreakpoint where
  name := "state q" ++ reprStr state
  predicate := fun _ c => c.state == state

def breakOnHalt (D : Description) : DebugBreakpoint where
  name := "halt q" ++ reprStr D.halt
  predicate := fun _ c => c.state == D.halt

def breakOnTapeRead (tapeIndex : Nat) (cell : Option Bool) :
    DebugBreakpoint where
  name := "tape " ++ reprStr tapeIndex ++ " read " ++ reprStr cell
  predicate := fun _ c =>
    Tape.read (tapeAt c.tapes tapeIndex) == cell

def breakOnStuck (D : Description) : DebugBreakpoint where
  name := "stuck"
  predicate := fun _ c =>
    if c.state == D.halt then
      false
    else
      match D.lookupTransition c with
      | none => true
      | some _ => false

end Description

/-!
## Boundary comparers
-/

inductive TapeMismatch where
  | leftMismatch (actual expected : List (Option Bool))
  | headMismatch (actual expected : Option Bool)
  | rightMismatch (actual expected : List (Option Bool))
deriving Repr, DecidableEq

inductive TapeListMismatch where
  | lengthMismatch (actual expected : Nat)
  | tapeMismatch (index : Nat) (mismatch : TapeMismatch)
deriving Repr, DecidableEq

inductive ConfigMismatch where
  | stateMismatch (actual expected : Nat)
  | tapesMismatch (mismatch : TapeListMismatch)
deriving Repr, DecidableEq

def compareTapeExact
    (actual expected : Tape Bool) : Option TapeMismatch :=
  if actual.left = expected.left then
    if actual.head = expected.head then
      if actual.right = expected.right then
        none
      else
        some (TapeMismatch.rightMismatch actual.right expected.right)
    else
      some (TapeMismatch.headMismatch actual.head expected.head)
  else
    some (TapeMismatch.leftMismatch actual.left expected.left)

def compareTapeEquiv
    (actual expected : Tape Bool) : Option TapeMismatch :=
  let actualLeft := Tape.dropTrailingNone actual.left
  let expectedLeft := Tape.dropTrailingNone expected.left
  let actualRight := Tape.dropTrailingNone actual.right
  let expectedRight := Tape.dropTrailingNone expected.right
  if actualLeft = expectedLeft then
    if actual.head = expected.head then
      if actualRight = expectedRight then
        none
      else
        some (TapeMismatch.rightMismatch actualRight expectedRight)
    else
      some (TapeMismatch.headMismatch actual.head expected.head)
  else
    some (TapeMismatch.leftMismatch actualLeft expectedLeft)

private def compareTapeListsWith
    (compare : Tape Bool -> Tape Bool -> Option TapeMismatch) :
    Nat -> List (Tape Bool) -> List (Tape Bool) -> Option TapeListMismatch
  | _, [], [] => none
  | _, actual, [] =>
      some (TapeListMismatch.lengthMismatch actual.length 0)
  | _, [], expected =>
      some (TapeListMismatch.lengthMismatch 0 expected.length)
  | index, actualTape :: actualRest, expectedTape :: expectedRest =>
      match compare actualTape expectedTape with
      | none => compareTapeListsWith compare (index + 1) actualRest expectedRest
      | some mismatch => some (TapeListMismatch.tapeMismatch index mismatch)

def compareTapeListsExact
    (actual expected : List (Tape Bool)) : Option TapeListMismatch :=
  compareTapeListsWith compareTapeExact 0 actual expected

def compareTapeListsEquiv
    (actual expected : List (Tape Bool)) : Option TapeListMismatch :=
  compareTapeListsWith compareTapeEquiv 0 actual expected

def compareConfigExact
    (actual expected : Configuration) : Option ConfigMismatch :=
  if actual.state = expected.state then
    match compareTapeListsExact actual.tapes expected.tapes with
    | none => none
    | some mismatch => some (ConfigMismatch.tapesMismatch mismatch)
  else
    some (ConfigMismatch.stateMismatch actual.state expected.state)

def compareConfigEquiv
    (actual expected : Configuration) : Option ConfigMismatch :=
  if actual.state = expected.state then
    match compareTapeListsEquiv actual.tapes expected.tapes with
    | none => none
    | some mismatch => some (ConfigMismatch.tapesMismatch mismatch)
  else
    some (ConfigMismatch.stateMismatch actual.state expected.state)

structure DebugFailure where
  step : Nat
  config : ConfigDebugView
  message : String
deriving Repr, DecidableEq

structure StepExpectation where
  step : Nat
  expectedState? : Option Nat := none
  expectedTapes? : Option (List (Tape Bool)) := none
deriving DecidableEq

def tapeMismatchString : TapeMismatch -> String
  | TapeMismatch.leftMismatch actual expected =>
      "left mismatch: actual=" ++ reprStr actual ++
        ", expected=" ++ reprStr expected
  | TapeMismatch.headMismatch actual expected =>
      "head mismatch: actual=" ++ reprStr actual ++
        ", expected=" ++ reprStr expected
  | TapeMismatch.rightMismatch actual expected =>
      "right mismatch: actual=" ++ reprStr actual ++
        ", expected=" ++ reprStr expected

def tapeListMismatchString : TapeListMismatch -> String
  | TapeListMismatch.lengthMismatch actual expected =>
      "tape-count mismatch: actual=" ++ reprStr actual ++
        ", expected=" ++ reprStr expected
  | TapeListMismatch.tapeMismatch index mismatch =>
      "tape " ++ reprStr index ++ " " ++ tapeMismatchString mismatch

def configMismatchString : ConfigMismatch -> String
  | ConfigMismatch.stateMismatch actual expected =>
      "state mismatch: actual=" ++ reprStr actual ++
        ", expected=" ++ reprStr expected
  | ConfigMismatch.tapesMismatch mismatch =>
      tapeListMismatchString mismatch

private def checkTapesExpectation
    (expected? : Option (List (Tape Bool))) (c : Configuration) :
    Except String Unit :=
  match expected? with
  | none => Except.ok ()
  | some expected =>
      match compareTapeListsExact c.tapes expected with
      | none => Except.ok ()
      | some mismatch => Except.error (tapeListMismatchString mismatch)

def checkStepExpectation
    (expectation : StepExpectation)
    (step : Nat) (c : Configuration) : Except String Unit :=
  if step = expectation.step then
    match expectation.expectedState? with
    | none => checkTapesExpectation expectation.expectedTapes? c
    | some expectedState =>
        if c.state = expectedState then
          checkTapesExpectation expectation.expectedTapes? c
        else
          Except.error
            ("state mismatch: actual=" ++ reprStr c.state ++
              ", expected=" ++ reprStr expectedState)
  else
    Except.ok ()

def checkStepExpectations
    (expectations : List StepExpectation)
    (step : Nat) (c : Configuration) : Except String Unit :=
  match expectations with
  | [] => Except.ok ()
  | expectation :: rest =>
      match checkStepExpectation expectation step c with
      | Except.ok () => checkStepExpectations rest step c
      | Except.error msg => Except.error msg

namespace Description

private def debugFirstFailureAux
    (D : Description)
    (check : Nat -> Configuration -> Except String Unit) :
    Nat -> Nat -> Configuration -> Option DebugFailure
  | 0, step, c =>
      match check step c with
      | Except.ok () => none
      | Except.error msg =>
          some { step := step, config := c.debugView, message := msg }
  | fuel + 1, step, c =>
      match check step c with
      | Except.error msg =>
          some { step := step, config := c.debugView, message := msg }
      | Except.ok () =>
          if c.state == D.halt then
            none
          else
            match D.stepConfig c with
            | none => none
            | some next =>
                debugFirstFailureAux D check fuel (step + 1) next

def debugFirstFailure
    (D : Description)
    (fuel : Nat)
    (c : Configuration)
    (check : Nat -> Configuration -> Except String Unit) :
    Option DebugFailure :=
  debugFirstFailureAux D check fuel 0 c

def debugFirstExpectationFailure
    (D : Description)
    (fuel : Nat)
    (c : Configuration)
    (expectations : List StepExpectation) : Option DebugFailure :=
  D.debugFirstFailure fuel c
    (checkStepExpectations expectations)

def debugTraceAroundFirstFailure
    (D : Description)
    (fuel : Nat)
    (c : Configuration)
    (check : Nat -> Configuration -> Except String Unit)
    (radius : Nat) : List StepDebugView :=
  match D.debugFirstFailure fuel c check with
  | none => []
  | some failure =>
      D.debugTraceRange fuel c
        (failure.step - radius) (failure.step + radius + 1)

def debugTraceAroundFirstExpectationFailure
    (D : Description)
    (fuel : Nat)
    (c : Configuration)
    (expectations : List StepExpectation)
    (radius : Nat) : List StepDebugView :=
  D.debugTraceAroundFirstFailure fuel c
    (checkStepExpectations expectations) radius

end Description

/-!
## Small executable regression examples
-/

namespace Examples

private def writeTrueAndHalt : Description where
  tapeCount := 2
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ { source := 0
        reads := [some false, none]
        actions :=
          [ { write? := some (some true), move := HeadMove.right }
          , { write? := none, move := HeadMove.stay } ]
        target := 1 } ]

private def sourceConfig : Configuration where
  state := 0
  tapes := [Tape.input [false], Tape.blank]

private def targetConfig : Configuration where
  state := 1
  tapes :=
    [ Tape.move Direction.right (Tape.write (some true) (Tape.input [false]))
    , Tape.blank ]

private theorem writeTrueAndHalt_wellFormed :
    writeTrueAndHalt.WellFormed := by
  unfold Description.WellFormed Description.Deterministic
    Transition.WellFormed Transition.SameKey Transition.SameAction
    writeTrueAndHalt
  simp

private theorem writeTrueAndHalt_haltTransitionFree :
    writeTrueAndHalt.HaltTransitionFree := by
  unfold Description.HaltTransitionFree writeTrueAndHalt
  simp

private theorem writeTrueAndHalt_one_step :
    writeTrueAndHalt.runConfig 1 sourceConfig = targetConfig := by
  decide

private theorem writeTrueAndHalt_trace :
    writeTrueAndHalt.debugTrace 5 sourceConfig =
      [ { step := 0
          before :=
            { state := 0
              tapes :=
                [ { left := []
                    head := some false
                    right := [] }
                , { left := []
                    head := none
                    right := [] } ] }
          reads := [some false, none]
          transition :=
            some
              { source := 0
                reads := [some false, none]
                actions :=
                  [ { write? := some (some true)
                      move := HeadMove.right }
                  , { write? := none
                      move := HeadMove.stay } ]
                target := 1 }
          after :=
            { state := 1
              tapes :=
                [ { left := [some true]
                    head := none
                    right := [] }
                , { left := []
                    head := none
                    right := [] } ] } } ] := by
  decide

private theorem writeTrueAndHalt_breakpoint :
    (writeTrueAndHalt.debugFirstBreakpoint 5 sourceConfig
        (Description.breakOnHalt writeTrueAndHalt)).map
        (fun hit => (hit.step, hit.config.state)) =
      some (1, 1) := by
  decide

private theorem compareConfigExact_accepts_target :
    compareConfigExact
        (writeTrueAndHalt.runConfig 1 sourceConfig)
        targetConfig =
      none := by
  decide

private theorem compareTapeEquiv_ignores_trailing_blanks :
    compareTapeEquiv
        { left := [some true, none]
          head := none
          right := [none] }
        { left := [some true]
          head := none
          right := [] } =
      none := by
  decide

private theorem expectation_failure_reports_first_bad_state :
    (writeTrueAndHalt.debugFirstExpectationFailure 5 sourceConfig
        [ { step := 1
            expectedState? := some 0
            expectedTapes? := none } ]).map
        (fun failure => (failure.step, failure.config.state)) =
      some (1, 1) := by
  decide

end Examples

end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
