import FoC.Computability.Compiler.DescriptionExecution

set_option doc.verso true

/-!
# Machine descriptions with stay moves

This module adds a small stay-capable intermediate machine description.  It is
not a replacement for
{name (full := FoC.Computability.MachineDescription)}`MachineDescription`: it is a proof-friendly layer
whose transitions may use a logical stay move and can be lowered to ordinary
left/right-only descriptions.

The lowering proves structural lookup facts, a generic run-simulation theorem,
and the public halting bridge {lit}`compile_haltsFromTapeEquiv`.
-/

namespace FoC
namespace Computability

open Languages

/-!
## Stay-Capable Tables

The intermediate syntax mirrors finite machine descriptions while extending
head movement with a logical stay action. Its well-formedness and lookup
predicates remain first-order and executable.
-/

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

theorem lookupTransition_mem {D : MachineDescriptionWithStay}
    {source : Nat} {read : Option Bool} {t : StayTransitionDescription}
    (h : D.lookupTransition source read = some t) :
    t ∈ D.transitions := by
  unfold lookupTransition at h
  let p := Matches source read
  have hmem :
      forall rows : List StayTransitionDescription,
        rows.find? p = some t -> t ∈ rows := by
    intro rows
    induction rows with
    | nil =>
        intro hnil
        simp at hnil
    | cons row rest ih =>
        intro hfind
        rw [List.find?_cons] at hfind
        cases hmatch : p row
        · simp [hmatch] at hfind
          have ht : t ∈ rest := ih hfind
          simp [ht]
        · simp [hmatch] at hfind
          cases hfind
          simp
  exact hmem D.transitions h

theorem lookupTransition_match {D : MachineDescriptionWithStay}
    {source : Nat} {read : Option Bool} {t : StayTransitionDescription}
    (h : D.lookupTransition source read = some t) :
    t.source = source ∧ t.read = read := by
  unfold lookupTransition at h
  have hpred :
      Matches source read t = true := by
    exact List.find?_some h
  simpa [Matches] using hpred

/-!
## Executable Stay Semantics

Configurations and fuel-bounded runs interpret a stay row directly, before any
lowering to the left/right-only backend. The halting contracts retain both the
final state and exact output tape.
-/

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

def transitionTarget
    (t : StayTransitionDescription) (c : Configuration) :
    Configuration where
  state := t.target
  tape := t.move.apply (Tape.write t.write c.tape)

theorem stepConfig_eq_some_of_lookupTransition
    {D : MachineDescriptionWithStay} {c : Configuration}
    {t : StayTransitionDescription}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = some t) :
    D.stepConfig c = some (transitionTarget t c) := by
  simp [stepConfig, transitionTarget, hlookup]

theorem stepConfig_state_bound
    {D : MachineDescriptionWithStay} {c d : Configuration}
    (hD : D.WellFormed)
    (hstep : D.stepConfig c = some d) :
    d.state < D.stateCount := by
  unfold stepConfig at hstep
  cases hlookup : D.lookupTransition c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      simp [hlookup] at hstep
      cases hstep
      have htmem : t ∈ D.transitions := lookupTransition_mem hlookup
      exact (hD.right.right.right.left t htmem).right

def runConfig (D : MachineDescriptionWithStay) :
    Nat -> Configuration -> Configuration
  | 0, c => c
  | n + 1, c =>
      match D.stepConfig c with
      | none => c
      | some next => runConfig D n next

theorem runConfig_state_bound
    {D : MachineDescriptionWithStay}
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

def HaltsFromTapeIn (D : MachineDescriptionWithStay)
    (n : Nat) (Tin Tout : Tape Bool) : Prop :=
  let final := D.runConfig n { state := D.start, tape := Tin }
  final.state = D.halt ∧ final.tape = Tout

def HaltsFromTape (D : MachineDescriptionWithStay)
    (Tin Tout : Tape Bool) : Prop :=
  exists n : Nat, D.HaltsFromTapeIn n Tin Tout

/-!
## Lowering Stay Rows

A logical stay is implemented by moving right into a fresh auxiliary state and
then moving left while preserving the encountered physical cell. Auxiliary
states are indexed by the source state and the three possible Boolean-tape
reads.
-/

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

/-- Encode the three possible Boolean tape reads as local auxiliary slots. -/
def readAuxOffset : Option Bool -> Nat
  | none => 0
  | some false => 1
  | some true => 2

theorem readAuxOffset_lt_three (read : Option Bool) :
    readAuxOffset read < 3 := by
  cases read with
  | none => decide
  | some bit =>
      cases bit <;> decide

/--
Fresh auxiliary state for the stay compilation of one source/read key.

The state lies in the block immediately after the source state interval:
{lit}`[baseState, baseState + baseState * 3)`.
-/
def auxState (baseState source : Nat) (read : Option Bool) : Nat :=
  baseState + (source * 3 + readAuxOffset read)

theorem auxState_eq_iff
    (baseState source target : Nat)
    (read targetRead : Option Bool) :
    auxState baseState source read =
        auxState baseState target targetRead ↔
      source = target ∧ read = targetRead := by
  constructor
  · intro h
    unfold auxState at h
    have hslot :
        source * 3 + readAuxOffset read =
          target * 3 + readAuxOffset targetRead :=
      Nat.add_left_cancel h
    cases read with
    | none =>
        cases targetRead with
        | none =>
            simp [readAuxOffset] at hslot
            constructor
            · lia
            · rfl
        | some targetBit =>
            cases targetBit <;> simp [readAuxOffset] at hslot <;> lia
    | some bit =>
        cases bit with
        | false =>
            cases targetRead with
            | none =>
                simp [readAuxOffset] at hslot
                lia
            | some targetBit =>
                cases targetBit with
                | false =>
                    simp [readAuxOffset] at hslot
                    constructor
                    · lia
                    · rfl
                | true =>
                    simp [readAuxOffset] at hslot
                    lia
        | true =>
            cases targetRead with
            | none =>
                simp [readAuxOffset] at hslot
                lia
            | some targetBit =>
                cases targetBit with
                | false =>
                    simp [readAuxOffset] at hslot
                    lia
                | true =>
                    simp [readAuxOffset] at hslot
                    constructor
                    · lia
                    · rfl
  · intro h
    rcases h with ⟨hsource, hread⟩
    cases hsource
    cases hread
    rfl

theorem baseState_le_auxState
    (baseState source : Nat) (read : Option Bool) :
    baseState ≤ auxState baseState source read := by
  unfold auxState
  exact Nat.le_add_right baseState (source * 3 + readAuxOffset read)

theorem source_ne_auxState_of_lt_base
    {baseState source auxSource : Nat} {read : Option Bool}
    (hsource : source < baseState) :
    source ≠ auxState baseState auxSource read := by
  exact Nat.ne_of_lt
    (Nat.lt_of_lt_of_le hsource
      (baseState_le_auxState baseState auxSource read))

theorem auxState_lt_stateCount
    {baseState source : Nat} {read : Option Bool}
    (hsource : source < baseState) :
    auxState baseState source read < baseState + baseState * 3 := by
  unfold auxState
  have hslot : source * 3 + readAuxOffset read < baseState * 3 := by
    have hslotLt : source * 3 + readAuxOffset read < source * 3 + 3 :=
      Nat.add_lt_add_left (readAuxOffset_lt_three read) (source * 3)
    have hsucc : source + 1 ≤ baseState := Nat.succ_le_of_lt hsource
    have hmul : (source + 1) * 3 ≤ baseState * 3 :=
      Nat.mul_le_mul_right 3 hsucc
    have hrewrite : source * 3 + 3 = (source + 1) * 3 := by
      rw [Nat.succ_mul]
    exact Nat.lt_of_lt_of_le (by simpa [hrewrite] using hslotLt) hmul
  exact Nat.add_lt_add_left hslot baseState

/--
Compile one stay-capable transition.

Ordinary left/right rows lower directly.  A stay row writes the requested cell,
moves right into an auxiliary state, then preserves the encountered cell and
moves left to the logical target state.
-/
def compileTransition
    (baseState : Nat) (t : StayTransitionDescription) :
    List TransitionDescription :=
  match t.move with
  | StayDirection.left =>
      [ { source := t.source, read := t.read, write := t.write,
          move := Direction.left, target := t.target } ]
  | StayDirection.right =>
      [ { source := t.source, read := t.read, write := t.write,
          move := Direction.right, target := t.target } ]
  | StayDirection.stay =>
      let aux := auxState baseState t.source t.read
      { source := t.source, read := t.read, write := t.write,
        move := Direction.right, target := aux } ::
        preserveTransitions aux t.target Direction.left

def compileTransitions
    (baseState : Nat) :
    List StayTransitionDescription -> List TransitionDescription
  | [] => []
  | t :: rest =>
      compileTransition baseState t ++ compileTransitions baseState rest

/-- The first ordinary row emitted for a stay-capable source row. -/
def compiledSourceRow
    (baseState : Nat) (t : StayTransitionDescription) :
    TransitionDescription :=
  match t.move with
  | StayDirection.left =>
      { source := t.source, read := t.read, write := t.write,
        move := Direction.left, target := t.target }
  | StayDirection.right =>
      { source := t.source, read := t.read, write := t.write,
        move := Direction.right, target := t.target }
  | StayDirection.stay =>
      { source := t.source, read := t.read, write := t.write,
        move := Direction.right, target := auxState baseState t.source t.read }

/-- One ordinary preservation row emitted from a stay auxiliary state. -/
def preserveRow
    (source target : Nat) (move : Direction) (read : Option Bool) :
    TransitionDescription where
  source := source
  read := read
  write := read
  move := move
  target := target

theorem preserveTransitions_find?
    (source target : Nat) (move : Direction) (read : Option Bool) :
    (preserveTransitions source target move).find?
        (MachineDescription.Matches source read) =
      some (preserveRow source target move read) := by
  cases read with
  | none =>
      simp [preserveTransitions, preserveRow, MachineDescription.Matches]
  | some bit =>
      cases bit <;>
        simp [preserveTransitions, preserveRow, MachineDescription.Matches]

theorem compileTransition_find?_source_some
    {baseState source : Nat} {read : Option Bool}
    {t : StayTransitionDescription}
    (hmatch : Matches source read t = true) :
    (compileTransition baseState t).find?
        (MachineDescription.Matches source read) =
      some (compiledSourceRow baseState t) := by
  have hkey : t.source = source ∧ t.read = read := by
    simpa [Matches] using hmatch
  rcases hkey with ⟨hsource, hread⟩
  cases hsource
  cases hread
  cases t with
  | mk tsource tread twrite tmove ttarget =>
      cases tmove <;>
        simp [compileTransition, compiledSourceRow,
          MachineDescription.Matches]

theorem compileTransition_find?_source_none
    {baseState source : Nat} {read : Option Bool}
    {t : StayTransitionDescription}
    (hsource : source < baseState)
    (hmatch : Matches source read t = false) :
    (compileTransition baseState t).find?
        (MachineDescription.Matches source read) = none := by
  cases hmove : t.move
  · simp [compileTransition, hmove, MachineDescription.Matches,
      Matches] at hmatch ⊢
    exact hmatch
  · simp [compileTransition, hmove, MachineDescription.Matches,
      Matches] at hmatch ⊢
    exact hmatch
  · have hne :
        auxState baseState t.source t.read ≠ source := by
      intro h
      exact source_ne_auxState_of_lt_base hsource h.symm
    simp [compileTransition, hmove, preserveTransitions,
      MachineDescription.Matches, Matches, hne] at hmatch ⊢
    exact hmatch

theorem compileTransitions_find?_source_some
    {baseState source : Nat} {read : Option Bool}
    {rows : List StayTransitionDescription} {t : StayTransitionDescription}
    (hsource : source < baseState)
    (hlookup : rows.find? (Matches source read) = some t) :
    (compileTransitions baseState rows).find?
        (MachineDescription.Matches source read) =
      some (compiledSourceRow baseState t) := by
  induction rows with
  | nil =>
      simp at hlookup
  | cons row rest ih =>
      rw [List.find?_cons] at hlookup
      cases hmatch : Matches source read row
      · simp [hmatch] at hlookup
        simp [compileTransitions, List.find?_append,
          compileTransition_find?_source_none
            (baseState := baseState) (source := source)
            (read := read) (t := row) hsource hmatch,
          ih hlookup]
      · simp [hmatch] at hlookup
        cases hlookup
        rw [compileTransitions, List.find?_append]
        rw [compileTransition_find?_source_some
          (baseState := baseState) (source := source)
          (read := read) (t := t) hmatch]
        rfl

theorem compileTransition_find?_aux_some
    {baseState source : Nat} {read auxRead : Option Bool}
    {t : StayTransitionDescription}
    (hrowSource : t.source < baseState)
    (hmatch : Matches source read t = true)
    (hmove : t.move = StayDirection.stay) :
    (compileTransition baseState t).find?
        (MachineDescription.Matches
          (auxState baseState source read) auxRead) =
      some
        (preserveRow (auxState baseState source read)
          t.target Direction.left auxRead) := by
  have hkey : t.source = source ∧ t.read = read := by
    simpa [Matches] using hmatch
  rcases hkey with ⟨hsource, hread⟩
  cases hsource
  cases hread
  have hne :
      t.source ≠ auxState baseState t.source t.read :=
    source_ne_auxState_of_lt_base hrowSource
  cases t with
  | mk tsource tread twrite tmove ttarget =>
      cases hmove
      simp [compileTransition, preserveTransitions_find?, preserveRow,
        MachineDescription.Matches, hne]

theorem compileTransition_find?_aux_none
    {baseState source : Nat} {read auxRead : Option Bool}
    {t : StayTransitionDescription}
    (hrowSource : t.source < baseState)
    (hmatch : Matches source read t = false) :
    (compileTransition baseState t).find?
        (MachineDescription.Matches
          (auxState baseState source read) auxRead) = none := by
  have hsourceNeAux :
      t.source ≠ auxState baseState source read :=
    source_ne_auxState_of_lt_base hrowSource
  have hauxNe :
      auxState baseState t.source t.read ≠
        auxState baseState source read := by
    intro haux
    have hkey :
        t.source = source ∧ t.read = read :=
      (auxState_eq_iff baseState t.source source t.read read).mp haux
    have htrue : Matches source read t = true := by
      rcases hkey with ⟨hsource, hread⟩
      cases hsource
      cases hread
      simp [Matches]
    rw [htrue] at hmatch
    contradiction
  cases hmove : t.move
  · simp [compileTransition, hmove, MachineDescription.Matches, hsourceNeAux]
  · simp [compileTransition, hmove, MachineDescription.Matches, hsourceNeAux]
  · simp [compileTransition, hmove, preserveTransitions,
      MachineDescription.Matches, hsourceNeAux, hauxNe]

theorem compileTransitions_find?_aux_some
    {baseState source : Nat} {read auxRead : Option Bool}
    {rows : List StayTransitionDescription} {t : StayTransitionDescription}
    (hrows :
      forall u : StayTransitionDescription, u ∈ rows -> u.source < baseState)
    (hlookup : rows.find? (Matches source read) = some t)
    (hmove : t.move = StayDirection.stay) :
    (compileTransitions baseState rows).find?
        (MachineDescription.Matches
          (auxState baseState source read) auxRead) =
      some
        (preserveRow (auxState baseState source read)
          t.target Direction.left auxRead) := by
  induction rows with
  | nil =>
      simp at hlookup
  | cons row rest ih =>
      rw [List.find?_cons] at hlookup
      cases hmatch : Matches source read row
      · simp [hmatch] at hlookup
        simp [compileTransitions, List.find?_append,
          compileTransition_find?_aux_none
            (baseState := baseState) (source := source)
            (read := read) (auxRead := auxRead) (t := row)
            (hrows row (by simp)) hmatch,
          ih (fun u hu => hrows u (by simp [hu])) hlookup]
      · simp [hmatch] at hlookup
        cases hlookup
        rw [compileTransitions, List.find?_append]
        rw [compileTransition_find?_aux_some
          (baseState := baseState) (source := source)
          (read := read) (auxRead := auxRead) (t := t)
          (hrows t (by simp)) hmatch hmove]
        rfl

/-!
## Compiled Descriptions

The complete lowering allocates the auxiliary-state block, compiles every row,
and preserves the original start and halt states. Lookup and structural lemmas
connect the generated table back to each logical source row.
-/

/-- Compile a stay-capable description to the ordinary left/right-only model. -/
def compile (D : MachineDescriptionWithStay) : MachineDescription where
  stateCount := D.stateCount + D.stateCount * 3
  start := D.start
  halt := D.halt
  transitions := compileTransitions D.stateCount D.transitions

@[simp] theorem compile_stateCount (D : MachineDescriptionWithStay) :
    D.compile.stateCount = D.stateCount + D.stateCount * 3 := by
  rfl

@[simp] theorem compile_start (D : MachineDescriptionWithStay) :
    D.compile.start = D.start := by
  rfl

@[simp] theorem compile_halt (D : MachineDescriptionWithStay) :
    D.compile.halt = D.halt := by
  rfl

@[simp] theorem compile_transitions (D : MachineDescriptionWithStay) :
    D.compile.transitions =
      compileTransitions D.stateCount D.transitions := by
  rfl

theorem compile_lookupTransition_source_some
    {D : MachineDescriptionWithStay}
    {source : Nat} {read : Option Bool} {t : StayTransitionDescription}
    (hsource : source < D.stateCount)
    (hlookup : D.lookupTransition source read = some t) :
    D.compile.lookupTransition source read =
      some (compiledSourceRow D.stateCount t) := by
  exact compileTransitions_find?_source_some
    (baseState := D.stateCount) (source := source)
    (read := read) (rows := D.transitions) (t := t)
    hsource hlookup

theorem compile_lookupTransition_aux_some
    {D : MachineDescriptionWithStay}
    {source : Nat} {read auxRead : Option Bool}
    {t : StayTransitionDescription}
    (hD : D.WellFormed)
    (hlookup : D.lookupTransition source read = some t)
    (hmove : t.move = StayDirection.stay) :
    D.compile.lookupTransition
        (auxState D.stateCount source read) auxRead =
      some
        (preserveRow (auxState D.stateCount source read)
          t.target Direction.left auxRead) := by
  exact compileTransitions_find?_aux_some
    (baseState := D.stateCount) (source := source)
    (read := read) (auxRead := auxRead)
    (rows := D.transitions) (t := t)
    (fun u hu => (hD.right.right.right.left u hu).left)
    hlookup hmove

@[simp] theorem preserveTransitions_length
    (source target : Nat) (move : Direction) :
    (preserveTransitions source target move).length = 3 := by
  rfl

theorem compileTransition_length
    (baseState : Nat) (t : StayTransitionDescription) :
    (compileTransition baseState t).length =
      match t.move with
      | StayDirection.left => 1
      | StayDirection.right => 1
      | StayDirection.stay => 4 := by
  cases t with
  | mk source read write move target =>
      cases move <;> rfl

theorem compile_stateCount_pos {D : MachineDescriptionWithStay}
    (h : 0 < D.stateCount) :
    0 < D.compile.stateCount := by
  change 0 < D.stateCount + D.stateCount * 3
  exact Nat.lt_of_lt_of_le h
    (Nat.le_add_right D.stateCount (D.stateCount * 3))

theorem compile_start_lt {D : MachineDescriptionWithStay}
    (h : D.start < D.stateCount) :
    D.compile.start < D.compile.stateCount := by
  change D.start < D.stateCount + D.stateCount * 3
  exact Nat.lt_of_lt_of_le h
    (Nat.le_add_right D.stateCount (D.stateCount * 3))

theorem compile_halt_lt {D : MachineDescriptionWithStay}
    (h : D.halt < D.stateCount) :
    D.compile.halt < D.compile.stateCount := by
  change D.halt < D.stateCount + D.stateCount * 3
  exact Nat.lt_of_lt_of_le h
    (Nat.le_add_right D.stateCount (D.stateCount * 3))

theorem compile_stateCount_pos_of_wellFormed
    {D : MachineDescriptionWithStay} (hD : D.WellFormed) :
    0 < D.compile.stateCount :=
  compile_stateCount_pos hD.left

theorem compile_start_lt_of_wellFormed
    {D : MachineDescriptionWithStay} (hD : D.WellFormed) :
    D.compile.start < D.compile.stateCount :=
  compile_start_lt hD.right.left

theorem compile_halt_lt_of_wellFormed
    {D : MachineDescriptionWithStay} (hD : D.WellFormed) :
    D.compile.halt < D.compile.stateCount :=
  compile_halt_lt hD.right.right.left

theorem preserveTransitions_haltTransitionFree
    {source target halt : Nat} {move : Direction}
    (hsource : source ≠ halt) :
    forall row : TransitionDescription,
      row ∈ preserveTransitions source target move ->
        row.source ≠ halt := by
  intro row hrow
  simp [preserveTransitions] at hrow
  rcases hrow with hrow | hrow | hrow
  · cases hrow
    exact hsource
  · cases hrow
    exact hsource
  · cases hrow
    exact hsource

theorem compileTransition_haltTransitionFree
    {baseState halt : Nat} {t : StayTransitionDescription}
    (hsource : t.source ≠ halt) (hhalt : halt < baseState) :
    forall row : TransitionDescription,
      row ∈ compileTransition baseState t ->
        row.source ≠ halt := by
  intro row hrow
  cases hmove : t.move
  · simp [compileTransition, hmove] at hrow
    cases hrow
    exact hsource
  · simp [compileTransition, hmove] at hrow
    cases hrow
    exact hsource
  · simp [compileTransition, hmove] at hrow
    rcases hrow with hrow | hrow
    · cases hrow
      exact hsource
    · exact preserveTransitions_haltTransitionFree
        (source := auxState baseState t.source t.read) (target := t.target)
        (halt := halt) (move := Direction.left)
        (Nat.ne_of_gt
          (Nat.lt_of_lt_of_le hhalt
            (baseState_le_auxState baseState t.source t.read)))
        row hrow

theorem compileTransitions_haltTransitionFree
    {baseState halt : Nat}
    {rows : List StayTransitionDescription}
    (hrows :
      forall t : StayTransitionDescription,
        t ∈ rows -> t.source ≠ halt)
    (hhalt : halt < baseState) :
    forall row : TransitionDescription,
      row ∈ compileTransitions baseState rows ->
        row.source ≠ halt := by
  induction rows with
  | nil =>
      intro row hrow
      simp [compileTransitions] at hrow
  | cons t rest ih =>
      intro row hrow
      simp [compileTransitions] at hrow
      rcases hrow with hrow | hrow
      · exact compileTransition_haltTransitionFree
          (baseState := baseState) (halt := halt) (t := t)
          (hrows t (by simp)) hhalt row hrow
      · exact ih
          (fun u hu => hrows u (by simp [hu]))
          row hrow

theorem compile_haltTransitionFree
    {D : MachineDescriptionWithStay}
    (hhalt : D.halt < D.stateCount)
    (hfree : D.HaltTransitionFree) :
    D.compile.HaltTransitionFree := by
  intro row hrow
  exact compileTransitions_haltTransitionFree
    (baseState := D.stateCount)
    (halt := D.halt) (rows := D.transitions)
    hfree hhalt row hrow

theorem compile_haltTransitionFree_of_subroutineReady
    {D : MachineDescriptionWithStay}
    (hD : D.SubroutineReady) :
    D.compile.HaltTransitionFree :=
  compile_haltTransitionFree hD.left.right.right.left hD.right

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

private theorem tape_write_read_self (T : Tape Bool) :
    Tape.write (Tape.read T) T = T := by
  cases T
  rfl

/-!
## Simulation and Halting Preservation

Source steps expand to one or two backend steps. Iterating that simulation
yields the public halting bridge, which observes the lowered endpoint up to
finite-tape equivalence.
-/

theorem compile_stepConfig_simulates
    {D : MachineDescriptionWithStay} {c c' : Configuration}
    (hD : D.WellFormed)
    (hc : c.state < D.stateCount)
    (hstep : D.stepConfig c = some c') :
    exists fuel : Nat, exists actual : Tape Bool,
      0 < fuel ∧
        D.compile.runConfig fuel
            { state := c.state, tape := c.tape } =
          { state := c'.state, tape := actual } ∧
        Tape.Equiv actual c'.tape := by
  unfold stepConfig at hstep
  cases hlookup :
      D.lookupTransition c.state (Tape.read c.tape) with
  | none =>
      simp [hlookup] at hstep
  | some t =>
      simp [hlookup] at hstep
      cases hstep
      have hkey := lookupTransition_match hlookup
      cases hmove : t.move
      · refine ⟨1, Tape.move Direction.left (Tape.write t.write c.tape),
          by decide, ?_, Tape.Equiv.refl _⟩
        simp [MachineDescription.runConfig, MachineDescription.stepConfig,
          compile_lookupTransition_source_some
            (D := D) (source := c.state)
            (read := Tape.read c.tape) (t := t) hc hlookup,
          compiledSourceRow, hmove]
      · refine ⟨1, Tape.move Direction.right (Tape.write t.write c.tape),
          by decide, ?_, Tape.Equiv.refl _⟩
        simp [MachineDescription.runConfig, MachineDescription.stepConfig,
          compile_lookupTransition_source_some
            (D := D) (source := c.state)
            (read := Tape.read c.tape) (t := t) hc hlookup,
          compiledSourceRow, hmove]
      · refine
          ⟨2,
            Tape.move Direction.left
              (Tape.move Direction.right (Tape.write t.write c.tape)),
            by decide, ?_,
            tape_move_left_move_right_equiv (Tape.write t.write c.tape)⟩
        simp [MachineDescription.runConfig, MachineDescription.stepConfig,
          compile_lookupTransition_source_some
            (D := D) (source := c.state)
            (read := Tape.read c.tape) (t := t) hc hlookup,
          compile_lookupTransition_aux_some
            (D := D) (source := t.source)
            (read := t.read)
            (auxRead :=
              Tape.read
                (Tape.move Direction.right (Tape.write t.write c.tape)))
            (t := t) hD
            (by
              simpa [hkey.left, hkey.right] using hlookup)
            hmove,
          compiledSourceRow, preserveRow, tape_write_read_self, hmove]

theorem compile_runConfig_simulates
    {D : MachineDescriptionWithStay}
    (hD : D.WellFormed) (n : Nat) {c : Configuration}
    (hc : c.state < D.stateCount) :
    exists fuel : Nat, exists actual : Tape Bool,
      D.compile.runConfig fuel
          { state := c.state, tape := c.tape } =
        { state := (D.runConfig n c).state, tape := actual } ∧
      Tape.Equiv actual (D.runConfig n c).tape := by
  induction n generalizing c with
  | zero =>
      refine ⟨0, c.tape, ?_, Tape.Equiv.refl _⟩
      rfl
  | succ n ih =>
      cases hstep : D.stepConfig c with
      | none =>
          refine ⟨0, c.tape, ?_, ?_⟩
          · simp [runConfig, hstep, MachineDescription.runConfig]
          · simpa [runConfig, hstep] using Tape.Equiv.refl c.tape
      | some next =>
          rcases compile_stepConfig_simulates
              (D := D) (c := c) (c' := next) hD hc hstep with
            ⟨fuelStep, actualStep, _hpos, hrunStep, heqStep⟩
          have hnextBound : next.state < D.stateCount :=
            stepConfig_state_bound hD hstep
          rcases ih hnextBound with
            ⟨fuelRest, actualRest, hrunRest, heqRest⟩
          let actualStart : MachineDescription.Configuration :=
            { state := next.state, tape := actualStep }
          let exactStart : MachineDescription.Configuration :=
            { state := next.state, tape := next.tape }
          have hrunEquiv :=
            MachineDescription.runConfig_equiv D.compile fuelRest
              (c := actualStart) (d := exactStart)
              rfl heqStep
          refine
            ⟨fuelStep + fuelRest,
              (D.compile.runConfig fuelRest actualStart).tape,
              ?_, ?_⟩
          · rw [MachineDescription.runConfig_add, hrunStep]
            have hstate := hrunEquiv.left
            rw [hrunRest] at hstate
            cases hactual :
                D.compile.runConfig fuelRest actualStart with
            | mk state tape =>
                simp [hactual] at hstate
                simp [runConfig, hstep, hstate]
          · have htape := hrunEquiv.right
            rw [hrunRest] at htape
            exact Tape.Equiv.trans htape
              (by simpa [runConfig, hstep] using heqRest)

theorem compile_haltsFromTapeEquiv
    {D : MachineDescriptionWithStay} {Tin Tout : Tape Bool}
    (hD : D.SubroutineReady)
    (hhalt : D.HaltsFromTape Tin Tout) :
    D.compile.HaltsFromTapeEquiv Tin Tout := by
  rcases hhalt with ⟨n, hn⟩
  let startConfig : Configuration := { state := D.start, tape := Tin }
  rcases compile_runConfig_simulates
      (D := D) hD.left n (c := startConfig) hD.left.right.left with
    ⟨fuel, actual, hrun, heq⟩
  have hrunStart :
      D.compile.runConfig fuel
          { state := D.compile.start, tape := Tin } =
        { state := (D.runConfig n startConfig).state, tape := actual } := by
    simpa [startConfig] using hrun
  have hfinalState :
      (D.runConfig n startConfig).state = D.halt := by
    simpa [startConfig] using hn.left
  have hfinalTape :
      (D.runConfig n startConfig).tape = Tout := by
    simpa [startConfig] using hn.right
  refine ⟨actual, ?_, ?_⟩
  · refine ⟨fuel, ?_⟩
    constructor
    · rw [hrunStart]
      exact hfinalState
    · rw [hrunStart]
  · simpa [hfinalTape] using heq

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
  cases read with
  | none =>
      cases write <;> cases right with
      | nil =>
          simp [singleStayDescription, compile, compileTransitions,
            compileTransition, preserveTransitions, auxState, readAuxOffset,
            singleStaySourceTape, singleStayTargetTape,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
      | cons head tail =>
          cases head with
          | none =>
              simp [singleStayDescription, compile, compileTransitions,
                compileTransition, preserveTransitions, auxState,
                readAuxOffset, singleStaySourceTape, singleStayTargetTape,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition, MachineDescription.Matches,
                Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                Tape.moveRight]
          | some bit =>
              cases bit <;>
                simp [singleStayDescription, compile, compileTransitions,
                  compileTransition, preserveTransitions, auxState,
                  readAuxOffset, singleStaySourceTape, singleStayTargetTape,
                  MachineDescription.runConfig, MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches, Tape.read, Tape.write,
                  Tape.move, Tape.moveLeft, Tape.moveRight]
  | some readBit =>
      cases readBit <;> cases write <;> cases right with
      | nil =>
          simp [singleStayDescription, compile, compileTransitions,
            compileTransition, preserveTransitions, auxState, readAuxOffset,
            singleStaySourceTape, singleStayTargetTape,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
      | cons head tail =>
          cases head with
          | none =>
              simp [singleStayDescription, compile, compileTransitions,
                compileTransition, preserveTransitions, auxState,
                readAuxOffset, singleStaySourceTape, singleStayTargetTape,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition, MachineDescription.Matches,
                Tape.read, Tape.write, Tape.move, Tape.moveLeft,
                Tape.moveRight]
          | some bit =>
              cases bit <;>
                simp [singleStayDescription, compile, compileTransitions,
                  compileTransition, preserveTransitions, auxState,
                  readAuxOffset, singleStaySourceTape, singleStayTargetTape,
                  MachineDescription.runConfig, MachineDescription.stepConfig,
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
