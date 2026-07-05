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

theorem headMove_apply_equiv
    (move : HeadMove) {T U : Tape Bool}
    (h : Tape.Equiv T U) :
    Tape.Equiv (move.apply T) (move.apply U) := by
  cases move with
  | stay =>
      exact h
  | left =>
      exact Tape.Equiv.move h Direction.left
  | right =>
      exact Tape.Equiv.move h Direction.right

theorem apply_preserves_logicalTapeListEquiv
    (primitive : PhysicalPrimitive)
    {actual expected : List (Tape Bool)}
    (h : LogicalTapeListEquiv actual expected) :
    LogicalTapeListEquiv
      (primitive.apply actual)
      (primitive.apply expected) := by
  cases primitive with
  | seekTape index =>
      exact h
  | readHeadCell index expectedRead =>
      exact h
  | writeHeadCell index cell =>
      exact
        logicalTapeListEquiv_replaceTapeAt h index
          (Tape.Equiv.write
            (logicalTapeListEquiv_tapeAt h index) cell)
  | moveHead index move =>
      exact
        logicalTapeListEquiv_replaceTapeAt h index
          (headMove_apply_equiv move
            (logicalTapeListEquiv_tapeAt h index))
  | returnToBlockStart =>
      exact h

theorem apply_guardLogicalTapes_equiv
    (primitive : PhysicalPrimitive)
    (logical : List (Tape Bool)) :
    LogicalTapeListEquiv
      (primitive.apply (guardLogicalTapes logical))
      (primitive.apply logical) :=
  apply_preserves_logicalTapeListEquiv primitive
    (guardLogicalTapes_equiv logical)

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

@[simp] theorem physicalPrimitiveSequenceEnabled_cons
    (primitive : PhysicalPrimitive) (rest : List PhysicalPrimitive)
    (logical : List (Tape Bool)) :
    physicalPrimitiveSequenceEnabled (primitive :: rest) logical ↔
      primitive.enabled logical ∧
        physicalPrimitiveSequenceEnabled rest
          (primitive.apply logical) := by
  rfl

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

theorem applyPhysicalPrimitiveSequence_preserves_logicalTapeListEquiv
    (primitives : List PhysicalPrimitive)
    {actual expected : List (Tape Bool)}
    (h : LogicalTapeListEquiv actual expected) :
    LogicalTapeListEquiv
      (applyPhysicalPrimitiveSequence primitives actual)
      (applyPhysicalPrimitiveSequence primitives expected) := by
  induction primitives generalizing actual expected with
  | nil =>
      exact h
  | cons primitive rest ih =>
      exact
        ih
          (PhysicalPrimitive.apply_preserves_logicalTapeListEquiv
            primitive h)

theorem applyPhysicalPrimitiveSequence_guardLogicalTapes_equiv
    (primitives : List PhysicalPrimitive)
    (logical : List (Tape Bool)) :
    LogicalTapeListEquiv
      (applyPhysicalPrimitiveSequence primitives
        (guardLogicalTapes logical))
      (applyPhysicalPrimitiveSequence primitives logical) :=
  applyPhysicalPrimitiveSequence_preserves_logicalTapeListEquiv
    primitives (guardLogicalTapes_equiv logical)

/--
Exact guard-slack endpoint produced by running a primitive sequence on the
guarded representative of a source logical tape list.

Unlike the broader {name}`StructuredLogicalEquivEncodedTapes` invariant, this
predicate records enough source information to determine the exact logical
representative that a later refresh step should re-guard.
-/
def PhysicalPrimitiveSequenceGuardSlackEndpoint
    (primitives : List PhysicalPrimitive)
    (source target : List (Tape Bool)) (physical : Tape Bool) : Prop :=
  target = applyPhysicalPrimitiveSequence primitives source ∧
    physical =
      encodedStructuredTapes
        (applyPhysicalPrimitiveSequence primitives
          (guardLogicalTapes source))

/--
Guard-slack endpoint observed up to raw tape equivalence.

This is the endpoint shape produced after composing through standard
subroutine handoffs: the machine may halt on a tape equivalent to the exact
row-produced guard-slack encoding.
-/
def PhysicalPrimitiveSequenceGuardSlackEndpointEquiv
    (primitives : List PhysicalPrimitive)
    (source target : List (Tape Bool)) (physical : Tape Bool) : Prop :=
  exists exactPhysical : Tape Bool,
    PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target
      exactPhysical ∧
      Tape.Equiv physical exactPhysical

theorem physicalPrimitiveSequenceGuardSlackEndpoint_self
    (primitives : List PhysicalPrimitive)
    (source : List (Tape Bool)) :
    PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source
      (applyPhysicalPrimitiveSequence primitives source)
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence primitives
          (guardLogicalTapes source))) := by
  exact ⟨rfl, rfl⟩

theorem PhysicalPrimitiveSequenceGuardSlackEndpoint.toStructuredLogicalEquiv
    {primitives : List PhysicalPrimitive}
    {source target : List (Tape Bool)} {physical : Tape Bool}
    (h :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target
        physical) :
    StructuredLogicalEquivEncodedTapes target physical := by
  rcases h with ⟨htarget, hphysical⟩
  rw [htarget, hphysical]
  exact
    ⟨applyPhysicalPrimitiveSequence primitives
        (guardLogicalTapes source),
      applyPhysicalPrimitiveSequence_guardLogicalTapes_equiv primitives
        source,
      rfl⟩

theorem PhysicalPrimitiveSequenceGuardSlackEndpoint.toEquiv
    {primitives : List PhysicalPrimitive}
    {source target : List (Tape Bool)} {physical : Tape Bool}
    (h :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target
        physical) :
    PhysicalPrimitiveSequenceGuardSlackEndpointEquiv primitives source target
      physical :=
  ⟨physical, h, Tape.Equiv.refl physical⟩

theorem PhysicalPrimitiveSequenceGuardSlackEndpoint.target_eq
    {primitives : List PhysicalPrimitive}
    {source target₁ target₂ : List (Tape Bool)}
    {physical₁ physical₂ : Tape Bool}
    (h₁ :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target₁
        physical₁)
    (h₂ :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target₂
        physical₂) :
    target₁ = target₂ := by
  rw [h₁.left, h₂.left]

theorem PhysicalPrimitiveSequenceGuardSlackEndpoint.physical_eq
    {primitives : List PhysicalPrimitive}
    {source target₁ target₂ : List (Tape Bool)}
    {physical₁ physical₂ : Tape Bool}
    (h₁ :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target₁
        physical₁)
    (h₂ :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target₂
        physical₂) :
    physical₁ = physical₂ := by
  rw [h₁.right, h₂.right]

theorem PhysicalPrimitiveSequenceGuardSlackEndpoint.guardedTarget_eq
    {primitives : List PhysicalPrimitive}
    {source target₁ target₂ : List (Tape Bool)}
    {physical₁ physical₂ : Tape Bool}
    (h₁ :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target₁
        physical₁)
    (h₂ :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target₂
        physical₂) :
    encodedGuardedStructuredTapes target₁ =
      encodedGuardedStructuredTapes target₂ := by
  rw [PhysicalPrimitiveSequenceGuardSlackEndpoint.target_eq h₁ h₂]

theorem PhysicalPrimitiveSequenceGuardSlackEndpointEquiv.target_eq
    {primitives : List PhysicalPrimitive}
    {source target₁ target₂ : List (Tape Bool)}
    {physical₁ physical₂ : Tape Bool}
    (h₁ :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv primitives source
        target₁ physical₁)
    (h₂ :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv primitives source
        target₂ physical₂) :
    target₁ = target₂ := by
  rcases h₁ with ⟨exact₁, hexact₁, _hequiv₁⟩
  rcases h₂ with ⟨exact₂, hexact₂, _hequiv₂⟩
  exact PhysicalPrimitiveSequenceGuardSlackEndpoint.target_eq
    hexact₁ hexact₂

theorem PhysicalPrimitiveSequenceGuardSlackEndpointEquiv.guardedTarget_eq
    {primitives : List PhysicalPrimitive}
    {source target₁ target₂ : List (Tape Bool)}
    {physical₁ physical₂ : Tape Bool}
    (h₁ :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv primitives source
        target₁ physical₁)
    (h₂ :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv primitives source
        target₂ physical₂) :
    encodedGuardedStructuredTapes target₁ =
      encodedGuardedStructuredTapes target₂ := by
  rw [PhysicalPrimitiveSequenceGuardSlackEndpointEquiv.target_eq h₁ h₂]

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

/-- Exact primitive contract over the guarded encoded layout. -/
structure PhysicalPrimitiveGuardedContract
    (primitive : PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      primitive.enabled logical ->
        machine.HaltsFromTape
          (encodedGuardedStructuredTapes logical)
          (encodedGuardedStructuredTapes (primitive.apply logical))

/--
Equivalence primitive contract over the guarded encoded layout.

This is the intended endpoint for routines that consume a guard blank and then
compare against the re-guarded logical target.
-/
structure PhysicalPrimitiveGuardedContractEquiv
    (primitive : PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      primitive.enabled logical ->
        machine.HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes logical)
          (encodedGuardedStructuredTapes (primitive.apply logical))

def PhysicalPrimitiveGuardedContract.toEquiv
    {primitive : PhysicalPrimitive} {machine : MachineDescription}
    (h : PhysicalPrimitiveGuardedContract primitive machine) :
    PhysicalPrimitiveGuardedContractEquiv primitive machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro logical hlogical
    exact MachineDescription.HaltsFromTape.toEquiv
      (h.realizes logical hlogical)

/--
Primitive contract whose output is an encoded logical tape list equivalent to
the represented target.

This is for local guarded head moves before a guard-refresh normalizer restores
the canonical guarded endpoint.  It is deliberately weaker than
{name}`PhysicalPrimitiveGuardedContractEquiv`: the physical encoded tapes need
not be equivalent as one raw tape, because encoded logical guard cells are not
physical trailing blanks.
-/
structure PhysicalPrimitiveGuardedLogicalEquivContract
    (primitive : PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      primitive.enabled logical ->
        exists actual : List (Tape Bool),
          LogicalTapeListEquiv actual (primitive.apply logical) ∧
            machine.HaltsFromTape
              (encodedGuardedStructuredTapes logical)
              (encodedStructuredTapes actual)

/-- Stay-machine primitive contract over the guarded encoded layout. -/
structure PhysicalPrimitiveGuardedContractWithStay
    (primitive : PhysicalPrimitive)
    (machine : MachineDescriptionWithStay) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      primitive.enabled logical ->
        machine.HaltsFromTape
          (encodedGuardedStructuredTapes logical)
          (encodedGuardedStructuredTapes (primitive.apply logical))

def PhysicalPrimitiveGuardedContractWithStay.toCompiledEquiv
    {primitive : PhysicalPrimitive} {machine : MachineDescriptionWithStay}
    (h : PhysicalPrimitiveGuardedContractWithStay primitive machine)
    (hcompiled : machine.compile.SubroutineReady) :
    PhysicalPrimitiveGuardedContractEquiv primitive machine.compile where
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

/-- Exact primitive-sequence contract over the guarded encoded layout. -/
structure PhysicalPrimitiveSequenceGuardedContract
    (primitives : List PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      physicalPrimitiveSequenceEnabled primitives logical ->
        machine.HaltsFromTape
          (encodedGuardedStructuredTapes logical)
          (encodedGuardedStructuredTapes
            (applyPhysicalPrimitiveSequence primitives logical))

/-- Equivalence primitive-sequence contract over the guarded encoded layout. -/
structure PhysicalPrimitiveSequenceGuardedContractEquiv
    (primitives : List PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      physicalPrimitiveSequenceEnabled primitives logical ->
        machine.HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes logical)
          (encodedGuardedStructuredTapes
            (applyPhysicalPrimitiveSequence primitives logical))

/--
Guarded sequence contract whose endpoint is the exact row-produced guard-slack
encoding, observed up to raw tape equivalence.

This is the implementable pre-refresh boundary: the source logical tapes are
known, the primitive sequence is known, and the exact logical target is
therefore determined by
{lit}`applyPhysicalPrimitiveSequence primitives logical`.
-/
structure PhysicalPrimitiveSequenceGuardSlackContractEquiv
    (primitives : List PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      physicalPrimitiveSequenceEnabled primitives logical ->
        machine.HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes logical)
          (encodedStructuredTapes
            (applyPhysicalPrimitiveSequence primitives
              (guardLogicalTapes logical)))

/--
Guarded sequence contract whose output physically encodes a logical tape list
equivalent to the represented target.

This is the sequence-level version of
{name}`PhysicalPrimitiveGuardedLogicalEquivContract`; it is intended for rows
ending in local head moves before a canonical guard-refresh endpoint exists.
-/
structure PhysicalPrimitiveSequenceGuardedLogicalEquivContract
    (primitives : List PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      physicalPrimitiveSequenceEnabled primitives logical ->
        exists actual : List (Tape Bool),
          LogicalTapeListEquiv actual
            (applyPhysicalPrimitiveSequence primitives logical) ∧
            machine.HaltsFromTape
              (encodedGuardedStructuredTapes logical)
              (encodedStructuredTapes actual)

/--
Guarded sequence contract whose output is observed through both layers of
equivalence: pointwise logical-tape equivalence and raw tape equivalence for
the physical machine endpoint.

This is the boundary used after composing through canonical right/left
subroutine handoffs, where exact physical endpoint equality is no longer the
right contract.
-/
structure PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
    (primitives : List PhysicalPrimitive)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      physicalPrimitiveSequenceEnabled primitives logical ->
        exists actual : List (Tape Bool),
          LogicalTapeListEquiv actual
            (applyPhysicalPrimitiveSequence primitives logical) ∧
            machine.HaltsFromTapeEquiv
              (encodedGuardedStructuredTapes logical)
              (encodedStructuredTapes actual)

def PhysicalPrimitiveSequenceGuardedContract.toEquiv
    {primitives : List PhysicalPrimitive} {machine : MachineDescription}
    (h : PhysicalPrimitiveSequenceGuardedContract primitives machine) :
    PhysicalPrimitiveSequenceGuardedContractEquiv primitives machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro logical hlogical
    exact MachineDescription.HaltsFromTape.toEquiv
      (h.realizes logical hlogical)

/-- Stay-machine primitive-sequence contract over the guarded layout. -/
structure PhysicalPrimitiveSequenceGuardedContractWithStay
    (primitives : List PhysicalPrimitive)
    (machine : MachineDescriptionWithStay) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall logical : List (Tape Bool),
      physicalPrimitiveSequenceEnabled primitives logical ->
        machine.HaltsFromTape
          (encodedGuardedStructuredTapes logical)
          (encodedGuardedStructuredTapes
            (applyPhysicalPrimitiveSequence primitives logical))

def PhysicalPrimitiveSequenceGuardedContractWithStay.toCompiledEquiv
    {primitives : List PhysicalPrimitive}
    {machine : MachineDescriptionWithStay}
    (h : PhysicalPrimitiveSequenceGuardedContractWithStay primitives machine)
    (hcompiled : machine.compile.SubroutineReady) :
    PhysicalPrimitiveSequenceGuardedContractEquiv primitives machine.compile where
  subroutineReady := hcompiled
  realizes := by
    intro logical hlogical
    exact MachineDescriptionWithStay.compile_haltsFromTapeEquiv
      h.subroutineReady (h.realizes logical hlogical)

def PhysicalPrimitiveGuardedContract.toSequence
    {primitive : PhysicalPrimitive} {machine : MachineDescription}
    (h : PhysicalPrimitiveGuardedContract primitive machine) :
    PhysicalPrimitiveSequenceGuardedContract [primitive] machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro logical hlogical
    exact h.realizes logical hlogical.left

def PhysicalPrimitiveGuardedContractEquiv.toSequence
    {primitive : PhysicalPrimitive} {machine : MachineDescription}
    (h : PhysicalPrimitiveGuardedContractEquiv primitive machine) :
    PhysicalPrimitiveSequenceGuardedContractEquiv [primitive] machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro logical hlogical
    exact h.realizes logical hlogical.left

def PhysicalPrimitiveGuardedContract.toSequenceEquiv
    {primitive : PhysicalPrimitive} {machine : MachineDescription}
    (h : PhysicalPrimitiveGuardedContract primitive machine) :
    PhysicalPrimitiveSequenceGuardedContractEquiv [primitive] machine :=
  h.toEquiv.toSequence

def PhysicalPrimitiveGuardedLogicalEquivContract.toSequence
    {primitive : PhysicalPrimitive} {machine : MachineDescription}
    (h : PhysicalPrimitiveGuardedLogicalEquivContract primitive machine) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContract [primitive]
      machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro logical hlogical
    exact h.realizes logical hlogical.left

def PhysicalPrimitiveSequenceGuardedLogicalEquivContract.toEquiv
    {primitives : List PhysicalPrimitive} {machine : MachineDescription}
    (h :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContract
        primitives machine) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      primitives machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro logical hlogical
    rcases h.realizes logical hlogical with
      ⟨actual, hactual, hhalts⟩
    exact ⟨actual, hactual,
      MachineDescription.HaltsFromTape.toEquiv hhalts⟩

def PhysicalPrimitiveSequenceGuardSlackContractEquiv.toLogicalEquiv
    {primitives : List PhysicalPrimitive} {machine : MachineDescription}
    (h :
      PhysicalPrimitiveSequenceGuardSlackContractEquiv
        primitives machine) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      primitives machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro logical hlogical
    exact
      ⟨applyPhysicalPrimitiveSequence primitives
          (guardLogicalTapes logical),
        applyPhysicalPrimitiveSequence_guardLogicalTapes_equiv primitives
          logical,
        h.realizes logical hlogical⟩

def PhysicalPrimitiveSequenceGuardedContractEquiv.toLogicalEquiv
    {primitives : List PhysicalPrimitive} {machine : MachineDescription}
    (h :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        primitives machine) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      primitives machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro logical hlogical
    refine
      ⟨guardLogicalTapes
          (applyPhysicalPrimitiveSequence primitives logical),
        guardLogicalTapes_equiv
          (applyPhysicalPrimitiveSequence primitives logical),
        ?_⟩
    simpa [encodedGuardedStructuredTapes] using
      h.realizes logical hlogical

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

theorem applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_singleton
    (action : TapeAction) (T : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (actionPrimitivesAt 0 action) [T] =
      [action.apply T] := by
  cases action with
  | mk write? move =>
      cases write? with
      | none =>
          cases move <;> rfl
      | some cell =>
          cases move <;> rfl

theorem actionPrimitivesAt_zero_guardSlackEndpoint_singleton
    (action : TapeAction) (T : Tape Bool) :
    PhysicalPrimitiveSequenceGuardSlackEndpoint
      (actionPrimitivesAt 0 action) [T] [action.apply T]
      (encodedStructuredTapes [action.apply (guardLogicalTape T)]) := by
  constructor
  · exact
      (applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_singleton
        action T).symm
  · simp [guardLogicalTapes,
      applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_singleton]

theorem actionPrimitivesAt_zero_structuredLogicalEquivEndpoint_singleton
    (action : TapeAction) (T : Tape Bool) :
    StructuredLogicalEquivEncodedTapes [action.apply T]
      (encodedStructuredTapes [action.apply (guardLogicalTape T)]) := by
  exact
    ⟨[action.apply (guardLogicalTape T)],
      ⟨Tape.Equiv.trans
          (guardLogicalTape_action_equiv action T)
          (guardLogicalTape_equiv (action.apply T)),
        trivial⟩,
      rfl⟩

theorem actionPrimitivesAt_zero_stay_guardSlackEndpoint_singleton
    (write? : Option (Option Bool)) (T : Tape Bool) :
    PhysicalPrimitiveSequenceGuardSlackEndpoint
      (actionPrimitivesAt 0
        ({ write? := write?, move := HeadMove.stay } : TapeAction))
      [T]
      [({ write? := write?, move := HeadMove.stay } : TapeAction).apply T]
      (encodedStructuredTapes
        [({ write? := write?, move := HeadMove.stay } : TapeAction).apply
          (guardLogicalTape T)]) :=
  actionPrimitivesAt_zero_guardSlackEndpoint_singleton
    ({ write? := write?, move := HeadMove.stay } : TapeAction) T

theorem actionPrimitivesAt_zero_stay_structuredLogicalEquivEndpoint_singleton
    (write? : Option (Option Bool)) (T : Tape Bool) :
    StructuredLogicalEquivEncodedTapes
      [({ write? := write?, move := HeadMove.stay } : TapeAction).apply T]
      (encodedStructuredTapes
        [({ write? := write?, move := HeadMove.stay } : TapeAction).apply
          (guardLogicalTape T)]) :=
  actionPrimitivesAt_zero_structuredLogicalEquivEndpoint_singleton
    ({ write? := write?, move := HeadMove.stay } : TapeAction) T

theorem actionPrimitivesAt_zero_stay_guardSlackPhysical_eq_guarded_singleton
    (write? : Option (Option Bool)) (T : Tape Bool) :
    encodedStructuredTapes
        [({ write? := write?, move := HeadMove.stay } : TapeAction).apply
          (guardLogicalTape T)] =
      encodedGuardedStructuredTapes
        [({ write? := write?, move := HeadMove.stay } : TapeAction).apply T] := by
  cases write? with
  | none =>
      rfl
  | some cell =>
      simpa [encodedGuardedStructuredTapes, guardLogicalTapes,
        TapeAction.apply, HeadMove.apply] using
        congrArg (fun U => encodedStructuredTapes [U])
          (guardLogicalTape_write cell T).symm

theorem actionPrimitivesAt_zero_stay_guardSlackEndpoint_canonical_singleton
    (write? : Option (Option Bool)) (T : Tape Bool) :
    PhysicalPrimitiveSequenceGuardSlackEndpoint
      (actionPrimitivesAt 0
        ({ write? := write?, move := HeadMove.stay } : TapeAction))
      [T]
      [({ write? := write?, move := HeadMove.stay } : TapeAction).apply T]
      (encodedGuardedStructuredTapes
        [({ write? := write?, move := HeadMove.stay } : TapeAction).apply T]) := by
  simpa [actionPrimitivesAt_zero_stay_guardSlackPhysical_eq_guarded_singleton]
    using actionPrimitivesAt_zero_stay_guardSlackEndpoint_singleton write? T

theorem tapeAction_left_apply_guardLogicalTape_eq_left_apply_guardedStay
    (write? : Option (Option Bool)) (T : Tape Bool) :
    ({ write? := write?, move := HeadMove.left } : TapeAction).apply
        (guardLogicalTape T) =
      HeadMove.left.apply
        (guardLogicalTape
          (({ write? := write?, move := HeadMove.stay } : TapeAction).apply
            T)) := by
  cases write? with
  | none =>
      rfl
  | some cell =>
      simp [TapeAction.apply, HeadMove.apply, guardLogicalTape_write]

theorem actionPrimitivesAt_zero_left_guardSlackPhysical_eq_left_guardedStay_singleton
    (write? : Option (Option Bool)) (T : Tape Bool) :
    encodedStructuredTapes
        [({ write? := write?, move := HeadMove.left } : TapeAction).apply
          (guardLogicalTape T)] =
      encodedStructuredTapes
        [HeadMove.left.apply
          (guardLogicalTape
            (({ write? := write?, move := HeadMove.stay } : TapeAction).apply
              T))] := by
  rw [tapeAction_left_apply_guardLogicalTape_eq_left_apply_guardedStay]

theorem tapeAction_left_apply_guardLogicalTape_eq_guarded_apply_of_left_cons
    (write? : Option (Option Bool))
    (cell : Option Bool) (left : List (Option Bool))
    (head : Option Bool) (right : List (Option Bool)) :
    ({ write? := write?, move := HeadMove.left } : TapeAction).apply
        (guardLogicalTape
          ({ left := cell :: left, head := head, right := right } :
            Tape Bool)) =
      guardLogicalTape
        (({ write? := write?, move := HeadMove.left } : TapeAction).apply
          ({ left := cell :: left, head := head, right := right } :
            Tape Bool)) := by
  cases write? with
  | none =>
      rfl
  | some writeCell =>
      rfl

theorem actionPrimitivesAt_zero_left_guardSlackPhysical_eq_guarded_singleton_of_left_cons
    (write? : Option (Option Bool))
    (cell : Option Bool) (left : List (Option Bool))
    (head : Option Bool) (right : List (Option Bool)) :
    encodedStructuredTapes
        [({ write? := write?, move := HeadMove.left } : TapeAction).apply
          (guardLogicalTape
            ({ left := cell :: left, head := head, right := right } :
              Tape Bool))] =
      encodedGuardedStructuredTapes
        [({ write? := write?, move := HeadMove.left } : TapeAction).apply
          ({ left := cell :: left, head := head, right := right } :
            Tape Bool)] := by
  simpa [encodedGuardedStructuredTapes, guardLogicalTapes] using
    congrArg (fun U => encodedStructuredTapes [U])
      (tapeAction_left_apply_guardLogicalTape_eq_guarded_apply_of_left_cons
        write? cell left head right)

theorem actionPrimitivesAt_zero_left_guardSlackEndpoint_singleton
    (write? : Option (Option Bool)) (T : Tape Bool) :
    PhysicalPrimitiveSequenceGuardSlackEndpoint
      (actionPrimitivesAt 0
        ({ write? := write?, move := HeadMove.left } : TapeAction))
      [T]
      [({ write? := write?, move := HeadMove.left } : TapeAction).apply T]
      (encodedStructuredTapes
        [({ write? := write?, move := HeadMove.left } : TapeAction).apply
          (guardLogicalTape T)]) :=
  actionPrimitivesAt_zero_guardSlackEndpoint_singleton
    ({ write? := write?, move := HeadMove.left } : TapeAction) T

theorem actionPrimitivesAt_zero_left_guardSlackEndpoint_canonical_singleton_of_left_cons
    (write? : Option (Option Bool))
    (cell : Option Bool) (left : List (Option Bool))
    (head : Option Bool) (right : List (Option Bool)) :
    PhysicalPrimitiveSequenceGuardSlackEndpoint
      (actionPrimitivesAt 0
        ({ write? := write?, move := HeadMove.left } : TapeAction))
      [({ left := cell :: left, head := head, right := right } : Tape Bool)]
      [({ write? := write?, move := HeadMove.left } : TapeAction).apply
        ({ left := cell :: left, head := head, right := right } : Tape Bool)]
      (encodedGuardedStructuredTapes
        [({ write? := write?, move := HeadMove.left } : TapeAction).apply
          ({ left := cell :: left, head := head, right := right } :
            Tape Bool)]) := by
  simpa [
      actionPrimitivesAt_zero_left_guardSlackPhysical_eq_guarded_singleton_of_left_cons]
    using
      actionPrimitivesAt_zero_left_guardSlackEndpoint_singleton
        write?
        ({ left := cell :: left, head := head, right := right } : Tape Bool)

theorem actionPrimitivesAt_zero_left_structuredLogicalEquivEndpoint_singleton
    (write? : Option (Option Bool)) (T : Tape Bool) :
    StructuredLogicalEquivEncodedTapes
      [({ write? := write?, move := HeadMove.left } : TapeAction).apply T]
      (encodedStructuredTapes
        [({ write? := write?, move := HeadMove.left } : TapeAction).apply
          (guardLogicalTape T)]) :=
  actionPrimitivesAt_zero_structuredLogicalEquivEndpoint_singleton
    ({ write? := write?, move := HeadMove.left } : TapeAction) T

theorem tapeAction_right_apply_guardLogicalTape_eq_right_apply_guardedStay
    (write? : Option (Option Bool)) (T : Tape Bool) :
    ({ write? := write?, move := HeadMove.right } : TapeAction).apply
        (guardLogicalTape T) =
      HeadMove.right.apply
        (guardLogicalTape
          (({ write? := write?, move := HeadMove.stay } : TapeAction).apply
            T)) := by
  cases write? with
  | none =>
      rfl
  | some cell =>
      simp [TapeAction.apply, HeadMove.apply, guardLogicalTape_write]

theorem actionPrimitivesAt_zero_right_guardSlackPhysical_eq_right_guardedStay_singleton
    (write? : Option (Option Bool)) (T : Tape Bool) :
    encodedStructuredTapes
        [({ write? := write?, move := HeadMove.right } : TapeAction).apply
          (guardLogicalTape T)] =
      encodedStructuredTapes
        [HeadMove.right.apply
          (guardLogicalTape
            (({ write? := write?, move := HeadMove.stay } : TapeAction).apply
              T))] := by
  rw [tapeAction_right_apply_guardLogicalTape_eq_right_apply_guardedStay]

theorem tapeAction_right_apply_guardLogicalTape_eq_guarded_apply_of_right_cons
    (write? : Option (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (cell : Option Bool) (right : List (Option Bool)) :
    ({ write? := write?, move := HeadMove.right } : TapeAction).apply
        (guardLogicalTape
          ({ left := left, head := head, right := cell :: right } :
            Tape Bool)) =
      guardLogicalTape
        (({ write? := write?, move := HeadMove.right } : TapeAction).apply
          ({ left := left, head := head, right := cell :: right } :
            Tape Bool)) := by
  cases write? with
  | none =>
      rfl
  | some writeCell =>
      rfl

theorem actionPrimitivesAt_zero_right_guardSlackPhysical_eq_guarded_singleton_of_right_cons
    (write? : Option (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (cell : Option Bool) (right : List (Option Bool)) :
    encodedStructuredTapes
        [({ write? := write?, move := HeadMove.right } : TapeAction).apply
          (guardLogicalTape
            ({ left := left, head := head, right := cell :: right } :
              Tape Bool))] =
      encodedGuardedStructuredTapes
        [({ write? := write?, move := HeadMove.right } : TapeAction).apply
          ({ left := left, head := head, right := cell :: right } :
            Tape Bool)] := by
  simpa [encodedGuardedStructuredTapes, guardLogicalTapes] using
    congrArg (fun U => encodedStructuredTapes [U])
      (tapeAction_right_apply_guardLogicalTape_eq_guarded_apply_of_right_cons
        write? left head cell right)

theorem actionPrimitivesAt_zero_right_guardSlackEndpoint_singleton
    (write? : Option (Option Bool)) (T : Tape Bool) :
    PhysicalPrimitiveSequenceGuardSlackEndpoint
      (actionPrimitivesAt 0
        ({ write? := write?, move := HeadMove.right } : TapeAction))
      [T]
      [({ write? := write?, move := HeadMove.right } : TapeAction).apply T]
      (encodedStructuredTapes
        [({ write? := write?, move := HeadMove.right } : TapeAction).apply
          (guardLogicalTape T)]) :=
  actionPrimitivesAt_zero_guardSlackEndpoint_singleton
    ({ write? := write?, move := HeadMove.right } : TapeAction) T

theorem actionPrimitivesAt_zero_right_guardSlackEndpoint_canonical_singleton_of_right_cons
    (write? : Option (Option Bool))
    (left : List (Option Bool)) (head : Option Bool)
    (cell : Option Bool) (right : List (Option Bool)) :
    PhysicalPrimitiveSequenceGuardSlackEndpoint
      (actionPrimitivesAt 0
        ({ write? := write?, move := HeadMove.right } : TapeAction))
      [({ left := left, head := head, right := cell :: right } : Tape Bool)]
      [({ write? := write?, move := HeadMove.right } : TapeAction).apply
        ({ left := left, head := head, right := cell :: right } : Tape Bool)]
      (encodedGuardedStructuredTapes
        [({ write? := write?, move := HeadMove.right } : TapeAction).apply
          ({ left := left, head := head, right := cell :: right } :
            Tape Bool)]) := by
  simpa [
      actionPrimitivesAt_zero_right_guardSlackPhysical_eq_guarded_singleton_of_right_cons]
    using
      actionPrimitivesAt_zero_right_guardSlackEndpoint_singleton
        write?
        ({ left := left, head := head, right := cell :: right } : Tape Bool)

theorem actionPrimitivesAt_zero_right_structuredLogicalEquivEndpoint_singleton
    (write? : Option (Option Bool)) (T : Tape Bool) :
    StructuredLogicalEquivEncodedTapes
      [({ write? := write?, move := HeadMove.right } : TapeAction).apply T]
      (encodedStructuredTapes
        [({ write? := write?, move := HeadMove.right } : TapeAction).apply
          (guardLogicalTape T)]) :=
  actionPrimitivesAt_zero_structuredLogicalEquivEndpoint_singleton
    ({ write? := write?, move := HeadMove.right } : TapeAction) T

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

def transitionPrimitiveSequence3Action1Last
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction) :
    List PhysicalPrimitive :=
  readCheckPrimitivesAt 0 read0 ++
    readCheckPrimitivesAt 1 read1 ++
      readCheckPrimitivesAt 2 read2 ++
        actionPrimitivesAt 0 action0 ++
          actionPrimitivesAt 2 action2 ++
            actionPrimitivesAt 1 action1

def transitionPrimitiveSequence3Action0Last
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction) :
    List PhysicalPrimitive :=
  readCheckPrimitivesAt 0 read0 ++
    readCheckPrimitivesAt 1 read1 ++
      readCheckPrimitivesAt 2 read2 ++
        actionPrimitivesAt 1 action1 ++
          actionPrimitivesAt 2 action2 ++
            actionPrimitivesAt 0 action0

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

theorem applyPhysicalPrimitiveSequence_transitionPrimitiveSequence3Action1Last
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (T U V : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (transitionPrimitiveSequence3Action1Last read0 read1 read2
          action0 action1 action2) [T, U, V] =
      [action0.apply T, action1.apply U, action2.apply V] := by
  simp [transitionPrimitiveSequence3Action1Last,
    applyPhysicalPrimitiveSequence_append,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_three,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_three,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_two_three]

theorem applyPhysicalPrimitiveSequence_transitionPrimitiveSequence3Action0Last
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (T U V : Tape Bool) :
    applyPhysicalPrimitiveSequence
        (transitionPrimitiveSequence3Action0Last read0 read1 read2
          action0 action1 action2) [T, U, V] =
      [action0.apply T, action1.apply U, action2.apply V] := by
  simp [transitionPrimitiveSequence3Action0Last,
    applyPhysicalPrimitiveSequence_append,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_zero_three,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_one_three,
    applyPhysicalPrimitiveSequence_actionPrimitivesAt_two_three]

theorem physicalPrimitiveSequenceEnabled_transitionPrimitiveSequence3
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (T U V : Tape Bool)
    (hread0 : Tape.read T = read0)
    (hread1 : Tape.read U = read1)
    (hread2 : Tape.read V = read2) :
    physicalPrimitiveSequenceEnabled
        (transitionPrimitiveSequence3 read0 read1 read2
          action0 action1 action2) [T, U, V] := by
  cases action0 with
  | mk write0 move0 =>
      cases write0 <;>
        cases action1 with
        | mk write1 move1 =>
            cases write1 <;>
              cases action2 with
              | mk write2 move2 =>
                  cases write2 <;>
                    simp [transitionPrimitiveSequence3,
                      readCheckPrimitivesAt, actionPrimitivesAt,
                      writePrimitivesForAction, hread0, hread1,
                      hread2, Description.tapeAt, PhysicalPrimitive.apply]

theorem physicalPrimitiveSequenceEnabled_transitionPrimitiveSequence3Action1Last
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (T U V : Tape Bool)
    (hread0 : Tape.read T = read0)
    (hread1 : Tape.read U = read1)
    (hread2 : Tape.read V = read2) :
    physicalPrimitiveSequenceEnabled
        (transitionPrimitiveSequence3Action1Last read0 read1 read2
          action0 action1 action2) [T, U, V] := by
  cases action0 with
  | mk write0 move0 =>
      cases write0 <;>
        cases action1 with
        | mk write1 move1 =>
            cases write1 <;>
              cases action2 with
              | mk write2 move2 =>
                  cases write2 <;>
                    simp [transitionPrimitiveSequence3Action1Last,
                      readCheckPrimitivesAt, actionPrimitivesAt,
                      writePrimitivesForAction, hread0, hread1,
                      hread2, Description.tapeAt, PhysicalPrimitive.apply]

theorem physicalPrimitiveSequenceEnabled_transitionPrimitiveSequence3Action0Last
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (T U V : Tape Bool)
    (hread0 : Tape.read T = read0)
    (hread1 : Tape.read U = read1)
    (hread2 : Tape.read V = read2) :
    physicalPrimitiveSequenceEnabled
        (transitionPrimitiveSequence3Action0Last read0 read1 read2
          action0 action1 action2) [T, U, V] := by
  cases action0 with
  | mk write0 move0 =>
      cases write0 <;>
        cases action1 with
        | mk write1 move1 =>
            cases write1 <;>
              cases action2 with
              | mk write2 move2 =>
                  cases write2 <;>
                    simp [transitionPrimitiveSequence3Action0Last,
                      readCheckPrimitivesAt, actionPrimitivesAt,
                      writePrimitivesForAction, hread0, hread1,
                      hread2, Description.tapeAt, PhysicalPrimitive.apply]

private theorem list_eq_three_of_length_eq_three
    {α : Type u} {xs : List α}
    (h : xs.length = 3) :
    exists a : α, exists b : α, exists c : α,
      xs = [a, b, c] := by
  cases xs with
  | nil =>
      simp at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp at h
      | cons b rest =>
          cases rest with
          | nil =>
              simp at h
          | cons c rest =>
              cases rest with
              | nil =>
                  exact ⟨a, b, c, rfl⟩
              | cons _d _rest =>
                  simp at h

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

/-!
## Guarded one-transition lowering contracts
-/

/--
Exact row-lowering contract over the guarded encoded layout.

This is the preferred exact contract once the row lowerer uses guard cells to
avoid boundary insertion in the tight layout.
-/
structure LowersGuardedTransition
    (D : Description) (t : Transition)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall c : Configuration,
      c.tapes.length = D.tapeCount ->
      t.source = c.state ->
        t.reads = D.currentReads c ->
          machine.HaltsFromTape
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes
              (D.applyActions t.actions c.tapes))

/--
Equivalence row-lowering contract over the guarded encoded layout.

Use this when a physical routine consumes a guard blank and halts on a tape
equivalent to the canonical re-guarded endpoint.
-/
structure LowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall c : Configuration,
      c.tapes.length = D.tapeCount ->
      t.source = c.state ->
        t.reads = D.currentReads c ->
          machine.HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes
              (D.applyActions t.actions c.tapes))

/--
Guarded row-lowering contract with a logical-equivalence output invariant.

The machine starts from the canonical guarded input.  Its output may be any
physical tape that encodes logical tapes pointwise equivalent to the structured
target, and the physical endpoint itself is compared with
{name}`MachineDescription.HaltsFromTapeEquiv`.  This is the row boundary for
local head moves that consume guard slack before a later normalizer restores a
canonical guarded layout.
-/
structure LowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall c : Configuration,
      c.tapes.length = D.tapeCount ->
      t.source = c.state ->
        t.reads = D.currentReads c ->
          exists physical : Tape Bool,
            StructuredLogicalEquivEncodedTapes
              (D.applyActions t.actions c.tapes) physical ∧
              machine.HaltsFromTapeEquiv
                (encodedGuardedStructuredTapes c.tapes)
                physical

/--
Guarded row-lowering contract with an exact row-produced guard-slack endpoint.

This is the endpoint-aware replacement for
{name}`LowersGuardedTransitionLogicalEquiv` when the row implementation is
known to produce the slack layout obtained by running
{name}`transitionPrimitiveSequenceOfRow3` on the guarded representative of the
source tapes.
-/
structure LowersGuardedTransitionGuardSlack
    (D : Description) (t : Transition)
    (machine : MachineDescription) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall c : Configuration,
      c.tapes.length = D.tapeCount ->
      t.source = c.state ->
        t.reads = D.currentReads c ->
          exists physical : Tape Bool,
            PhysicalPrimitiveSequenceGuardSlackEndpoint
              (transitionPrimitiveSequenceOfRow3 t)
              c.tapes
              (D.applyActions t.actions c.tapes)
              physical ∧
              machine.HaltsFromTapeEquiv
                (encodedGuardedStructuredTapes c.tapes)
                physical

def LowersGuardedTransition.toEquiv
    {D : Description} {t : Transition} {machine : MachineDescription}
    (h : LowersGuardedTransition D t machine) :
    LowersGuardedTransitionEquiv D t machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro c hc hsource hreads
    exact MachineDescription.HaltsFromTape.toEquiv
      (h.realizes c hc hsource hreads)

def LowersGuardedTransition.toLogicalEquiv
    {D : Description} {t : Transition} {machine : MachineDescription}
    (h : LowersGuardedTransition D t machine) :
    LowersGuardedTransitionLogicalEquiv D t machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro c hc hsource hreads
    refine
      ⟨encodedGuardedStructuredTapes
          (D.applyActions t.actions c.tapes),
        structuredLogicalEquivEncodedTapes_guarded_self
          (D.applyActions t.actions c.tapes),
        ?_⟩
    exact MachineDescription.HaltsFromTape.toEquiv
      (h.realizes c hc hsource hreads)

def LowersGuardedTransitionEquiv.toLogicalEquiv
    {D : Description} {t : Transition} {machine : MachineDescription}
    (h : LowersGuardedTransitionEquiv D t machine) :
    LowersGuardedTransitionLogicalEquiv D t machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro c hc hsource hreads
    exact
      ⟨encodedGuardedStructuredTapes
          (D.applyActions t.actions c.tapes),
        structuredLogicalEquivEncodedTapes_guarded_self
          (D.applyActions t.actions c.tapes),
        h.realizes c hc hsource hreads⟩

def LowersGuardedTransitionGuardSlack.toLogicalEquiv
    {D : Description} {t : Transition} {machine : MachineDescription}
    (h : LowersGuardedTransitionGuardSlack D t machine) :
    LowersGuardedTransitionLogicalEquiv D t machine where
  subroutineReady := h.subroutineReady
  realizes := by
    intro c hc hsource hreads
    rcases h.realizes c hc hsource hreads with
      ⟨physical, hendpoint, hrun⟩
    exact
      ⟨physical,
        hendpoint.toStructuredLogicalEquiv,
        hrun⟩

/-- Stay-machine row-lowering contract over the guarded encoded layout. -/
structure LowersGuardedTransitionWithStay
    (D : Description) (t : Transition)
    (machine : MachineDescriptionWithStay) : Prop where
  subroutineReady : machine.SubroutineReady
  realizes :
    forall c : Configuration,
      c.tapes.length = D.tapeCount ->
      t.source = c.state ->
        t.reads = D.currentReads c ->
          machine.HaltsFromTape
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes
              (D.applyActions t.actions c.tapes))

def LowersGuardedTransitionWithStay.toCompiledEquiv
    {D : Description} {t : Transition}
    {machine : MachineDescriptionWithStay}
    (h : LowersGuardedTransitionWithStay D t machine)
    (hcompiled : machine.compile.SubroutineReady) :
    LowersGuardedTransitionEquiv D t machine.compile where
  subroutineReady := hcompiled
  realizes := by
    intro c hc hsource hreads
    exact MachineDescriptionWithStay.compile_haltsFromTapeEquiv
      h.subroutineReady (h.realizes c hc hsource hreads)

theorem guardedPrimitiveSequence3_lowersGuardedTransitionEquiv
    {D : Description} {t : Transition}
    {machine : MachineDescription}
    (hsequence :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (transitionPrimitiveSequenceOfRow3 t) machine)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (hreads : t.reads = [read0, read1, read2])
    (hactions : t.actions = [action0, action1, action2]) :
    LowersGuardedTransitionEquiv D t machine where
  subroutineReady := hsequence.subroutineReady
  realizes := by
    intro c hc _hsource hcurrentReads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        have hreadsEq :
            [read0, read1, read2] =
              [Tape.read T, Tape.read U, Tape.read V] := by
          simpa [hreads, hD] using hcurrentReads
        have hreadsComponents :
            read0 = Tape.read T ∧
              read1 = Tape.read U ∧
                read2 = Tape.read V := by
          simpa using hreadsEq
        rcases hreadsComponents with ⟨hread0', hread1', hread2'⟩
        have hread0 : Tape.read T = read0 := by
          exact hread0'.symm
        have hread1 : Tape.read U = read1 := by
          exact hread1'.symm
        have hread2 : Tape.read V = read2 := by
          exact hread2'.symm
        have henabled :
            physicalPrimitiveSequenceEnabled
              (transitionPrimitiveSequenceOfRow3 t) [T, U, V] := by
          rw [show transitionPrimitiveSequenceOfRow3 t =
              transitionPrimitiveSequence3 read0 read1 read2
                action0 action1 action2 by
            cases t with
            | mk source reads actions target =>
                simp [transitionPrimitiveSequenceOfRow3] at hreads hactions ⊢
                cases hreads
                cases hactions
                rfl]
          exact
            physicalPrimitiveSequenceEnabled_transitionPrimitiveSequence3
              read0 read1 read2 action0 action1 action2 T U V
              hread0 hread1 hread2
        have hhalt := hsequence.realizes [T, U, V] henabled
        have hseqApply :
            applyPhysicalPrimitiveSequence
                (transitionPrimitiveSequenceOfRow3 t) [T, U, V] =
              D.applyActions t.actions [T, U, V] := by
          rw [applyPhysicalPrimitiveSequence_transitionPrimitiveSequenceOfRow3
            t read0 read1 read2 action0 action1 action2 T U V
            hreads hactions]
          rw [hactions]
          exact (Description.applyActions_three D hD
            action0 action1 action2 T U V).symm
        rcases hhalt with ⟨Tactual, hrun, hequiv⟩
        exact ⟨Tactual, hrun, by
          simpa [hseqApply] using hequiv⟩

theorem guardedPrimitiveSequence3_lowersGuardedTransitionLogicalEquiv
    {D : Description} {t : Transition}
    {machine : MachineDescription}
    (hsequence :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        (transitionPrimitiveSequenceOfRow3 t) machine)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (hreads : t.reads = [read0, read1, read2])
    (hactions : t.actions = [action0, action1, action2]) :
    LowersGuardedTransitionLogicalEquiv D t machine where
  subroutineReady := hsequence.subroutineReady
  realizes := by
    intro c hc _hsource hcurrentReads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        have hreadsEq :
            [read0, read1, read2] =
              [Tape.read T, Tape.read U, Tape.read V] := by
          simpa [hreads, hD] using hcurrentReads
        have hreadsComponents :
            read0 = Tape.read T ∧
              read1 = Tape.read U ∧
                read2 = Tape.read V := by
          simpa using hreadsEq
        rcases hreadsComponents with ⟨hread0', hread1', hread2'⟩
        have hread0 : Tape.read T = read0 := by
          exact hread0'.symm
        have hread1 : Tape.read U = read1 := by
          exact hread1'.symm
        have hread2 : Tape.read V = read2 := by
          exact hread2'.symm
        have henabled :
            physicalPrimitiveSequenceEnabled
              (transitionPrimitiveSequenceOfRow3 t) [T, U, V] := by
          rw [show transitionPrimitiveSequenceOfRow3 t =
              transitionPrimitiveSequence3 read0 read1 read2
                action0 action1 action2 by
            cases t with
            | mk source reads actions target =>
                simp [transitionPrimitiveSequenceOfRow3] at hreads hactions ⊢
                cases hreads
                cases hactions
                rfl]
          exact
            physicalPrimitiveSequenceEnabled_transitionPrimitiveSequence3
              read0 read1 read2 action0 action1 action2 T U V
              hread0 hread1 hread2
        have hhalt := hsequence.realizes [T, U, V] henabled
        have hseqApply :
            applyPhysicalPrimitiveSequence
                (transitionPrimitiveSequenceOfRow3 t) [T, U, V] =
              D.applyActions t.actions [T, U, V] := by
          rw [applyPhysicalPrimitiveSequence_transitionPrimitiveSequenceOfRow3
            t read0 read1 read2 action0 action1 action2 T U V
            hreads hactions]
          rw [hactions]
          exact (Description.applyActions_three D hD
            action0 action1 action2 T U V).symm
        rcases hhalt with ⟨actual, hactual, hrun⟩
        refine
          ⟨encodedStructuredTapes actual,
            ⟨actual, ?_, rfl⟩, hrun⟩
        simpa [hseqApply] using hactual

/--
Lower a three-tape row through any primitive sequence with the same pure
endpoint as the row.

This is used for reordered physical implementations: independent per-tape
actions may be scheduled so the only guard-consuming move is last, while the
logical endpoint still matches the structured row.
-/
theorem primitiveSequence3_lowersGuardedTransitionLogicalEquiv
    {D : Description} {t : Transition}
    {primitives : List PhysicalPrimitive}
    {machine : MachineDescription}
    (hsequence :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        primitives machine)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (action0 action1 action2 : TapeAction)
    (hreads : t.reads = [read0, read1, read2])
    (hactions : t.actions = [action0, action1, action2])
    (henabled :
      forall T U V : Tape Bool,
        Tape.read T = read0 ->
          Tape.read U = read1 ->
            Tape.read V = read2 ->
              physicalPrimitiveSequenceEnabled primitives [T, U, V])
    (happly :
      forall T U V : Tape Bool,
        applyPhysicalPrimitiveSequence primitives [T, U, V] =
          [action0.apply T, action1.apply U, action2.apply V]) :
    LowersGuardedTransitionLogicalEquiv D t machine where
  subroutineReady := hsequence.subroutineReady
  realizes := by
    intro c hc _hsource hcurrentReads
    have hlen : c.tapes.length = 3 := by
      simpa [hD] using hc
    rcases list_eq_three_of_length_eq_three hlen with
      ⟨T, U, V, htapes⟩
    cases c with
    | mk state tapes =>
        simp at htapes
        cases htapes
        have hreadsEq :
            [read0, read1, read2] =
              [Tape.read T, Tape.read U, Tape.read V] := by
          simpa [hreads, hD] using hcurrentReads
        have hreadsComponents :
            read0 = Tape.read T ∧
              read1 = Tape.read U ∧
                read2 = Tape.read V := by
          simpa using hreadsEq
        rcases hreadsComponents with ⟨hread0', hread1', hread2'⟩
        have hread0 : Tape.read T = read0 := by
          exact hread0'.symm
        have hread1 : Tape.read U = read1 := by
          exact hread1'.symm
        have hread2 : Tape.read V = read2 := by
          exact hread2'.symm
        have hhalt := hsequence.realizes [T, U, V]
          (henabled T U V hread0 hread1 hread2)
        have hseqApply :
            applyPhysicalPrimitiveSequence primitives [T, U, V] =
              D.applyActions t.actions [T, U, V] := by
          rw [happly T U V]
          rw [hactions]
          exact (Description.applyActions_three D hD
            action0 action1 action2 T U V).symm
        rcases hhalt with ⟨actual, hactual, hrun⟩
        refine
          ⟨encodedStructuredTapes actual,
            ⟨actual, ?_, rfl⟩, hrun⟩
        simpa [hseqApply] using hactual

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

theorem lowersGuardedTransition_realizes_lookup
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c : Configuration}
    (h : LowersGuardedTransition D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t) :
    machine.HaltsFromTape
      (encodedGuardedStructuredTapes c.tapes)
      (encodedGuardedStructuredTapes
        (D.applyActions t.actions c.tapes)) := by
  have hmatch := Description.lookupTransition_match hlookup
  exact h.realizes c hc hmatch.left hmatch.right

theorem lowersGuardedTransitionEquiv_realizes_lookup
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c : Configuration}
    (h : LowersGuardedTransitionEquiv D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t) :
    machine.HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes c.tapes)
      (encodedGuardedStructuredTapes
        (D.applyActions t.actions c.tapes)) := by
  have hmatch := Description.lookupTransition_match hlookup
  exact h.realizes c hc hmatch.left hmatch.right

theorem lowersGuardedTransitionLogicalEquiv_realizes_lookup
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c : Configuration}
    (h : LowersGuardedTransitionLogicalEquiv D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t) :
    exists physical : Tape Bool,
      StructuredLogicalEquivEncodedTapes
        (D.applyActions t.actions c.tapes) physical ∧
        machine.HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes c.tapes)
          physical := by
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

theorem lowersGuardedTransition_realizes_structured_step
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c next : Configuration}
    (h : LowersGuardedTransition D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c) :
    D.stepConfig c = some next ∧
      machine.HaltsFromTape
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes next.tapes) := by
  constructor
  · rw [hnext]
    exact stepConfig_eq_some_of_lookupTransition hlookup
  · rw [hnext]
    exact lowersGuardedTransition_realizes_lookup h hc hlookup

theorem lowersGuardedTransitionEquiv_realizes_structured_step
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c next : Configuration}
    (h : LowersGuardedTransitionEquiv D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c) :
    D.stepConfig c = some next ∧
      machine.HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes next.tapes) := by
  constructor
  · rw [hnext]
    exact stepConfig_eq_some_of_lookupTransition hlookup
  · rw [hnext]
    exact lowersGuardedTransitionEquiv_realizes_lookup h hc hlookup

theorem lowersGuardedTransitionLogicalEquiv_realizes_structured_step
    {D : Description} {t : Transition}
    {machine : MachineDescription} {c next : Configuration}
    (h : LowersGuardedTransitionLogicalEquiv D t machine)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c) :
    D.stepConfig c = some next ∧
      exists physical : Tape Bool,
        StructuredLogicalEquivEncodedTapes next.tapes physical ∧
          machine.HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            physical := by
  constructor
  · rw [hnext]
    exact stepConfig_eq_some_of_lookupTransition hlookup
  · rw [hnext]
    exact lowersGuardedTransitionLogicalEquiv_realizes_lookup h hc hlookup


end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
