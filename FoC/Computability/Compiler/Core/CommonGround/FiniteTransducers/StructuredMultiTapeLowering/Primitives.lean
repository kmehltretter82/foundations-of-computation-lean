import FoC.Computability.MachineDescriptionWithStay
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.Layout

set_option doc.verso true

/-!
# Structured multi-tape lowering primitives
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## Primitive physical routines
-/

/--
Replace the logical tape at an index, leaving out-of-range indices unchanged.

The primitive contracts below use this pure operation to state the logical
effect that a physical one-tape routine must realize on the encoded layout.
-/
def replaceTapeAt
    (index : Nat) (replacement : Tape Bool) :
    List (Tape Bool) -> List (Tape Bool)
  | [] => []
  | T :: rest =>
      match index with
      | 0 => replacement :: rest
      | index + 1 => T :: replaceTapeAt index replacement rest

@[simp] theorem replaceTapeAt_nil
    (index : Nat) (replacement : Tape Bool) :
    replaceTapeAt index replacement [] = [] := by
  cases index <;> rfl

@[simp] theorem replaceTapeAt_zero_cons
    (replacement T : Tape Bool) (rest : List (Tape Bool)) :
    replaceTapeAt 0 replacement (T :: rest) = replacement :: rest := by
  rfl

@[simp] theorem replaceTapeAt_succ_cons
    (index : Nat) (replacement T : Tape Bool)
    (rest : List (Tape Bool)) :
    replaceTapeAt (index + 1) replacement (T :: rest) =
      T :: replaceTapeAt index replacement rest := by
  rfl

@[simp] theorem replaceTapeAt_length
    (index : Nat) (replacement : Tape Bool)
    (logical : List (Tape Bool)) :
    (replaceTapeAt index replacement logical).length = logical.length := by
  induction index generalizing logical with
  | zero =>
      cases logical <;> rfl
  | succ index ih =>
      cases logical with
      | nil => rfl
      | cons T rest =>
          simp [replaceTapeAt, ih]

/--
One logical primitive that a physical one-tape routine can implement.

The constructors are intentionally layout-level operations, not ordinary
structured-machine transitions.  For example, {lit}`seekTape` and
{lit}`returnToBlockStart` change the physical cursor but leave the represented
logical tapes unchanged.
-/
inductive PhysicalPrimitive where
  | seekTape (index : Nat)
  | readHeadCell (index : Nat) (expected : Option Bool)
  | writeHeadCell (index : Nat) (cell : Option Bool)
  | moveHead (index : Nat) (move : HeadMove)
  | returnToBlockStart
deriving Repr, DecidableEq

namespace PhysicalPrimitive

/-- Logical endpoint effect of a primitive routine. -/
def apply :
    PhysicalPrimitive -> List (Tape Bool) -> List (Tape Bool)
  | seekTape _index, logical => logical
  | readHeadCell _index _expected, logical => logical
  | writeHeadCell index cell, logical =>
      replaceTapeAt index
        (Tape.write cell (Description.tapeAt logical index))
        logical
  | moveHead index move, logical =>
      replaceTapeAt index
        (move.apply (Description.tapeAt logical index))
        logical
  | returnToBlockStart, logical => logical

/--
Precondition for a primitive.  Read checks are partial: a physical checker is
only required to reach the normal endpoint when the encoded logical head cell
matches the expected read.
-/
def enabled :
    PhysicalPrimitive -> List (Tape Bool) -> Prop
  | seekTape index, logical => index < logical.length
  | readHeadCell index expected, logical =>
      index < logical.length ∧
        Tape.read (Description.tapeAt logical index) = expected
  | writeHeadCell index _cell, logical =>
      index < logical.length
  | moveHead index _move, logical =>
      index < logical.length
  | returnToBlockStart, _ => True

@[simp] theorem apply_seekTape
    (index : Nat) (logical : List (Tape Bool)) :
    apply (seekTape index) logical = logical := by
  rfl

@[simp] theorem apply_readHeadCell
    (index : Nat) (expected : Option Bool)
    (logical : List (Tape Bool)) :
    apply (readHeadCell index expected) logical = logical := by
  rfl

@[simp] theorem apply_returnToBlockStart
    (logical : List (Tape Bool)) :
    apply returnToBlockStart logical = logical := by
  rfl

@[simp] theorem enabled_seekTape
    (index : Nat) (logical : List (Tape Bool)) :
    enabled (seekTape index) logical ↔ index < logical.length := by
  rfl

@[simp] theorem enabled_readHeadCell
    (index : Nat) (expected : Option Bool)
    (logical : List (Tape Bool)) :
    enabled (readHeadCell index expected) logical ↔
      index < logical.length ∧
        Tape.read (Description.tapeAt logical index) = expected := by
  rfl

@[simp] theorem enabled_writeHeadCell
    (index : Nat) (cell : Option Bool)
    (logical : List (Tape Bool)) :
    enabled (writeHeadCell index cell) logical ↔
      index < logical.length := by
  rfl

@[simp] theorem enabled_moveHead
    (index : Nat) (move : HeadMove)
    (logical : List (Tape Bool)) :
    enabled (moveHead index move) logical ↔
      index < logical.length := by
  rfl

@[simp] theorem enabled_returnToBlockStart
    (logical : List (Tape Bool)) :
    enabled returnToBlockStart logical := by
  trivial

end PhysicalPrimitive

/-- Apply a sequence of physical primitive endpoint effects. -/
def applyPhysicalPrimitiveSequence :
    List PhysicalPrimitive -> List (Tape Bool) -> List (Tape Bool)
  | [], logical => logical
  | primitive :: rest, logical =>
      applyPhysicalPrimitiveSequence rest
        (primitive.apply logical)

/-- Sequential precondition for a primitive list. -/
def physicalPrimitiveSequenceEnabled :
    List PhysicalPrimitive -> List (Tape Bool) -> Prop
  | [], _logical => True
  | primitive :: rest, logical =>
      primitive.enabled logical ∧
        physicalPrimitiveSequenceEnabled rest
          (primitive.apply logical)

@[simp] theorem applyPhysicalPrimitiveSequence_nil
    (logical : List (Tape Bool)) :
    applyPhysicalPrimitiveSequence [] logical = logical := by
  rfl

@[simp] theorem applyPhysicalPrimitiveSequence_cons
    (primitive : PhysicalPrimitive) (rest : List PhysicalPrimitive)
    (logical : List (Tape Bool)) :
    applyPhysicalPrimitiveSequence (primitive :: rest) logical =
      applyPhysicalPrimitiveSequence rest (primitive.apply logical) := by
  rfl

@[simp] theorem physicalPrimitiveSequenceEnabled_nil
    (logical : List (Tape Bool)) :
    physicalPrimitiveSequenceEnabled [] logical := by
  trivial

theorem applyPhysicalPrimitiveSequence_append
    (first second : List PhysicalPrimitive)
    (logical : List (Tape Bool)) :
    applyPhysicalPrimitiveSequence (first ++ second) logical =
      applyPhysicalPrimitiveSequence second
        (applyPhysicalPrimitiveSequence first logical) := by
  induction first generalizing logical with
  | nil =>
      rfl
  | cons primitive rest ih =>
      simp [applyPhysicalPrimitiveSequence, ih]

/--
Contract for one concrete physical primitive machine.

The machine starts and ends at the canonical encoded block boundary.  Internal
head movement is hidden by the contract; only the represented logical tapes are
observable.
-/
structure PhysicalPrimitiveContract
    (primitive : PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      primitive.enabled logical ->
        machine.HaltsFromTape
          (encodedStructuredTapes logical)
          (encodedStructuredTapes (primitive.apply logical))

/--
Equivalence contract for one concrete physical primitive machine.

This is the right contract for routines compiled through stay moves or other
cursor maneuvers that may store extra edge blanks without changing the
represented logical tapes.
-/
structure PhysicalPrimitiveContractEquiv
    (primitive : PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      primitive.enabled logical ->
        machine.HaltsFromTapeEquiv
          (encodedStructuredTapes logical)
          (encodedStructuredTapes (primitive.apply logical))

/-- Exact primitive contracts can always be used at equivalence boundaries. -/
def PhysicalPrimitiveContract.toEquiv
    {primitive : PhysicalPrimitive} {machine : MachineDescription}
    (h : PhysicalPrimitiveContract primitive machine) :
    PhysicalPrimitiveContractEquiv primitive machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro logical hlogical
    exact MachineDescription.HaltsFromTape.toEquiv
      (h.realizes logical hlogical)

/--
Stay-machine contract for one concrete physical primitive.

This is the authoring-side contract for routines whose implementation naturally
uses logical stay moves.  Use {lit}`PhysicalPrimitiveContractWithStay.toCompiledEquiv`
to expose the compiled ordinary machine through an equivalence contract.
-/
structure PhysicalPrimitiveContractWithStay
    (primitive : PhysicalPrimitive)
    (machine : MachineDescriptionWithStay) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      primitive.enabled logical ->
        machine.HaltsFromTape
          (encodedStructuredTapes logical)
          (encodedStructuredTapes (primitive.apply logical))

/--
Compile a stay-machine primitive contract to an ordinary equivalence contract.

The general stay compiler currently proves behavior preservation, while the
compiled ordinary table's {lit}`SubroutineReady` proof is supplied by the concrete
machine or by a future generic compiler-ready theorem.
-/
def PhysicalPrimitiveContractWithStay.toCompiledEquiv
    {primitive : PhysicalPrimitive} {machine : MachineDescriptionWithStay}
    (h : PhysicalPrimitiveContractWithStay primitive machine)
    (hcompiled : machine.compile.SubroutineReady) :
    PhysicalPrimitiveContractEquiv primitive machine.compile where
  subroutineReady := hcompiled
  realizes := by
    intro logical hlogical
    exact MachineDescriptionWithStay.compile_haltsFromTapeEquiv
      h.subroutineReady (h.realizes logical hlogical)

/-- Contract for a compiled sequence of physical primitives. -/
structure PhysicalPrimitiveSequenceContract
    (primitives : List PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      physicalPrimitiveSequenceEnabled primitives logical ->
        machine.HaltsFromTape
          (encodedStructuredTapes logical)
          (encodedStructuredTapes
            (applyPhysicalPrimitiveSequence primitives logical))

/--
Equivalence contract for a compiled sequence of physical primitives.

The endpoint is compared by {name}`Tape.Equiv`, which is stable under the
ordinary stay compiler's right-then-left bounce at tape edges.
-/
structure PhysicalPrimitiveSequenceContractEquiv
    (primitives : List PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      physicalPrimitiveSequenceEnabled primitives logical ->
        machine.HaltsFromTapeEquiv
          (encodedStructuredTapes logical)
          (encodedStructuredTapes
            (applyPhysicalPrimitiveSequence primitives logical))

/-- Exact primitive-sequence contracts can be reused as equivalence contracts. -/
def PhysicalPrimitiveSequenceContract.toEquiv
    {primitives : List PhysicalPrimitive} {machine : MachineDescription}
    (h : PhysicalPrimitiveSequenceContract primitives machine) :
    PhysicalPrimitiveSequenceContractEquiv primitives machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro logical hlogical
    exact MachineDescription.HaltsFromTape.toEquiv
      (h.realizes logical hlogical)

/-- Stay-machine contract for a compiled sequence of physical primitives. -/
structure PhysicalPrimitiveSequenceContractWithStay
    (primitives : List PhysicalPrimitive)
    (machine : MachineDescriptionWithStay) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      physicalPrimitiveSequenceEnabled primitives logical ->
        machine.HaltsFromTape
          (encodedStructuredTapes logical)
          (encodedStructuredTapes
            (applyPhysicalPrimitiveSequence primitives logical))

/-- Compile a stay-machine primitive-sequence contract to an equivalence contract. -/
def PhysicalPrimitiveSequenceContractWithStay.toCompiledEquiv
    {primitives : List PhysicalPrimitive}
    {machine : MachineDescriptionWithStay}
    (h : PhysicalPrimitiveSequenceContractWithStay primitives machine)
    (hcompiled : machine.compile.SubroutineReady) :
    PhysicalPrimitiveSequenceContractEquiv primitives machine.compile where
  subroutineReady := hcompiled
  realizes := by
    intro logical hlogical
    exact MachineDescriptionWithStay.compile_haltsFromTapeEquiv
      h.subroutineReady (h.realizes logical hlogical)

def readCheckPrimitivesAt
    (index : Nat) (expected : Option Bool) :
    List PhysicalPrimitive :=
  [ PhysicalPrimitive.seekTape index
  , PhysicalPrimitive.readHeadCell index expected
  , PhysicalPrimitive.returnToBlockStart ]

def writePrimitivesForAction
    (index : Nat) (action : TapeAction) :
    List PhysicalPrimitive :=
  match action.write? with
  | none => []
  | some cell => [PhysicalPrimitive.writeHeadCell index cell]

def actionPrimitivesAt
    (index : Nat) (action : TapeAction) :
    List PhysicalPrimitive :=
  [PhysicalPrimitive.seekTape index] ++
    writePrimitivesForAction index action ++
      [ PhysicalPrimitive.moveHead index action.move
      , PhysicalPrimitive.returnToBlockStart ]

@[simp] theorem applyPhysicalPrimitiveSequence_readCheckPrimitivesAt
    (index : Nat) (expected : Option Bool)
    (logical : List (Tape Bool)) :
    applyPhysicalPrimitiveSequence
        (readCheckPrimitivesAt index expected) logical =
      logical := by
  rfl

theorem applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_three
    (action : TapeAction) (T U V : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (actionPrimitivesAt 0 action) [T, U, V] =
      [action.apply T, U, V] := by
  cases action with
  | mk write? move =>
      cases write? with
      | none =>
          cases move <;> rfl
      | some cell =>
          cases move <;> rfl

theorem applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_three
    (action : TapeAction) (T U V : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (actionPrimitivesAt 1 action) [T, U, V] =
      [T, action.apply U, V] := by
  cases action with
  | mk write? move =>
      cases write? with
      | none =>
          cases move <;> rfl
      | some cell =>
          cases move <;> rfl

theorem applyPhysicalPrimitiveSequence_actionPrimitivesAt_two_three
    (action : TapeAction) (T U V : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (actionPrimitivesAt 2 action) [T, U, V] =
      [T, U, action.apply V] := by
  cases action with
  | mk write? move =>
      cases write? with
      | none =>
          cases move <;> rfl
      | some cell =>
          cases move <;> rfl

def transitionPrimitiveSequence3
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction) :
    List PhysicalPrimitive :=
  readCheckPrimitivesAt 0 read0 ++
    readCheckPrimitivesAt 1 read1 ++
      readCheckPrimitivesAt 2 read2 ++
        actionPrimitivesAt 0 action0 ++
          actionPrimitivesAt 1 action1 ++
            actionPrimitivesAt 2 action2

theorem applyPhysicalPrimitiveSequence_transitionPrimitiveSequence3
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (T U V : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (transitionPrimitiveSequence3 read0 read1 read2
          action0 action1 action2) [T, U, V] =
      [action0.apply T, action1.apply U, action2.apply V] := by
  simp [transitionPrimitiveSequence3,
    applyPhysicalPrimitiveSequence_append,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_three,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_three,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_two_three]

def transitionPrimitiveSequenceOfRow3
    (t : Transition) : List PhysicalPrimitive :=
  match t.reads, t.actions with
  | [read0, read1, read2], [action0, action1, action2] =>
      transitionPrimitiveSequence3 read0 read1 read2
        action0 action1 action2
  | _, _ => []

theorem applyPhysicalPrimitiveSequence_transitionPrimitiveSequenceOfRow3
    (t : Transition)
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (T U V : Tape Bool)
    (hreads : t.reads = [read0, read1, read2])
    (hactions : t.actions = [action0, action1, action2]) :
    applyPhysicalPrimitiveSequence
        (transitionPrimitiveSequenceOfRow3 t) [T, U, V] =
      [action0.apply T, action1.apply U, action2.apply V] := by
  cases t with
  | mk source reads actions target =>
      simp [transitionPrimitiveSequenceOfRow3] at hreads hactions ⊢
      cases hreads
      cases hactions
      exact
        applyPhysicalPrimitiveSequence_transitionPrimitiveSequence3
          read0 read1 read2 action0 action1 action2 T U V

/-!
## One-transition lowering contract
-/

/--
Contract for the physical machine that lowers one structured transition row.

This is the first milestone-8 bridge.  It does not yet build the physical
transition table; instead it states exactly what such a table must do from the
canonical encoded boundary when the row's source state and read tuple match.
-/
structure LowersTransition
    (D : Description) (t : Transition)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall c : Configuration,
      c.tapes.length = D.tapeCount ->
      t.source = c.state ->
        t.reads = D.currentReads c ->
          machine.HaltsFromTape
            (encodedStructuredTapes c.tapes)
            (encodedStructuredTapes
              (D.applyActions t.actions c.tapes))

/--
Equivalence contract for the physical machine that lowers one structured row.

Use this when the row machine was compiled through stay moves, or otherwise
only preserves the encoded endpoint up to {name}`Tape.Equiv`.
-/
structure LowersTransitionEquiv
    (D : Description) (t : Transition)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall c : Configuration,
      c.tapes.length = D.tapeCount ->
      t.source = c.state ->
        t.reads = D.currentReads c ->
          machine.HaltsFromTapeEquiv
            (encodedStructuredTapes c.tapes)
            (encodedStructuredTapes
              (D.applyActions t.actions c.tapes))

/-- Exact row lowerings can be used at equivalence boundaries. -/
def LowersTransition.toEquiv
    {D : Description} {t : Transition} {machine : MachineDescription}
    (h : LowersTransition D t machine) :
    LowersTransitionEquiv D t machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro c hc hsource hreads
    exact MachineDescription.HaltsFromTape.toEquiv
      (h.realizes c hc hsource hreads)

/--
Stay-machine contract for one structured row.

This is the preferred proof target when the row implementation naturally uses
logical stay moves.  The compiled ordinary machine is exported with
{lit}`LowersTransitionWithStay.toCompiledEquiv`.
-/
structure LowersTransitionWithStay
    (D : Description) (t : Transition)
    (machine : MachineDescriptionWithStay) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall c : Configuration,
      c.tapes.length = D.tapeCount ->
      t.source = c.state ->
        t.reads = D.currentReads c ->
          machine.HaltsFromTape
            (encodedStructuredTapes c.tapes)
            (encodedStructuredTapes
              (D.applyActions t.actions c.tapes))

/--
Compile a stay-machine row contract to an ordinary equivalence row contract.

The compiled machine's {lit}`SubroutineReady` proof is explicit for now; concrete
row machines can usually prove it directly.
-/
def LowersTransitionWithStay.toCompiledEquiv
    {D : Description} {t : Transition}
    {machine : MachineDescriptionWithStay}
    (h : LowersTransitionWithStay D t machine)
    (hcompiled : machine.compile.SubroutineReady) :
    LowersTransitionEquiv D t machine.compile where
  subroutineReady := hcompiled
  realizes := by
    intro c hc hsource hreads
    exact MachineDescriptionWithStay.compile_haltsFromTapeEquiv
      h.subroutineReady (h.realizes c hc hsource hreads)

def structuredTransitionTarget
    (D : Description) (t : Transition)
    (c : Configuration) : Configuration where
  state := t.target
  tapes := D.applyActions t.actions c.tapes

theorem stepConfig_eq_some_of_lookupTransition
    {D : Description} {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t) :
    D.stepConfig c = some (structuredTransitionTarget D t c) := by
  simp [Description.stepConfig, structuredTransitionTarget, hlookup]

theorem lowersTransition_realizes_lookup
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c : Configuration}
    (h : LowersTransition D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t) :
    machine.HaltsFromTape
      (encodedStructuredTapes c.tapes)
      (encodedStructuredTapes
        (D.applyActions t.actions c.tapes)) := by
  have hmatch := Description.lookupTransition_match hlookup
  exact h.realizes c hc hmatch.left hmatch.right

theorem lowersTransitionEquiv_realizes_lookup
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c : Configuration}
    (h : LowersTransitionEquiv D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t) :
    machine.HaltsFromTapeEquiv
      (encodedStructuredTapes c.tapes)
      (encodedStructuredTapes
        (D.applyActions t.actions c.tapes)) := by
  have hmatch := Description.lookupTransition_match hlookup
  exact h.realizes c hc hmatch.left hmatch.right

theorem lowersTransition_realizes_structured_step
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c next : Configuration}
    (h : LowersTransition D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c) :
    D.stepConfig c = some next ∧
      machine.HaltsFromTape
        (encodedStructuredTapes c.tapes)
        (encodedStructuredTapes next.tapes) := by
  constructor
  · rw [hnext]
    exact stepConfig_eq_some_of_lookupTransition hlookup
  · rw [hnext]
    exact lowersTransition_realizes_lookup h hc hlookup

theorem lowersTransitionEquiv_realizes_structured_step
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c next : Configuration}
    (h : LowersTransitionEquiv D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c) :
    D.stepConfig c = some next ∧
      machine.HaltsFromTapeEquiv
        (encodedStructuredTapes c.tapes)
        (encodedStructuredTapes next.tapes) := by
  constructor
  · rw [hnext]
    exact stepConfig_eq_some_of_lookupTransition hlookup
  · rw [hnext]
    exact lowersTransitionEquiv_realizes_lookup h hc hlookup


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
