import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Primitives
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition

set_option doc.verso true

/-!
# Structured multi-tape lowering composition

This module composes already-proved guarded primitive contracts.  The physical
sequence combinator inserts the standard right/left handoff bounce between
subroutines, so the exported contracts use
{name (full := FoC.Computability.MachineDescription.HaltsFromTapeEquiv)}`MachineDescription.HaltsFromTapeEquiv`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

theorem physicalPrimitiveSequenceEnabled_append
    (first second : List PhysicalPrimitive)
    (logical : List (Tape Bool)) :
    physicalPrimitiveSequenceEnabled (first ++ second) logical ↔
      physicalPrimitiveSequenceEnabled first logical ∧
        physicalPrimitiveSequenceEnabled second
          (applyPhysicalPrimitiveSequence first logical) := by
  induction first generalizing logical with
  | nil =>
      simp
  | cons primitive rest ih =>
      change
        (primitive.enabled logical ∧
            physicalPrimitiveSequenceEnabled (rest ++ second)
              (primitive.apply logical)) ↔
          (primitive.enabled logical ∧
              physicalPrimitiveSequenceEnabled rest
                (primitive.apply logical)) ∧
            physicalPrimitiveSequenceEnabled second
              (applyPhysicalPrimitiveSequence rest
                (primitive.apply logical))
      rw [ih]
      constructor
      · intro h
        exact ⟨⟨h.left, h.right.left⟩, h.right.right⟩
      · intro h
        exact ⟨h.left.left, ⟨h.left.right, h.right⟩⟩

/--
Canonical sequence for physical primitive machines.

It is the same right/left handoff pattern used elsewhere in the finite
transducer library.  The handoff may change only trailing guard blanks, so the
main composition theorem below exports an equivalence contract.
-/
def canonicalPrimitiveSeqDescription
    (A B : MachineDescription) : MachineDescription :=
  seqSubroutine
    (seqSubroutine A ExactIdentityDescription Direction.right)
    B Direction.left

def canonicalPrimitiveSeqRightStateOffset
    (A : MachineDescription) : Nat :=
  (seqSubroutine A ExactIdentityDescription Direction.right).stateCount

theorem canonicalPrimitiveSeqDescription_subroutineReady
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady) :
    (canonicalPrimitiveSeqDescription A B).SubroutineReady := by
  exact
    seqSubroutine_subroutineReady
      (seqSubroutine_subroutineReady hA
        CommonGround.Identity.exactIdentityDescription_subroutineReady)
      hB

private theorem moveLeft_moveRight_equiv_self
    (T : Tape Bool) :
    Tape.Equiv
      (Tape.move Direction.left (Tape.move Direction.right T)) T := by
  cases T with
  | mk left head right =>
      simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight]
      cases right <;> simp [Tape.dropTrailingNone]

/--
The exact tape handed to the next component by
{name}`canonicalPrimitiveSeqDescription`.

It is equivalent to the previous component's output, but not generally equal
to it; exact-output contracts must specify the receiving component on this
tape, not merely on the equivalent unbounced tape.
-/
def canonicalPrimitiveSeqHandoffTape (T : Tape Bool) : Tape Bool :=
  Tape.move Direction.left (Tape.move Direction.right T)

/--
Exact closedness from a concrete input tape to a concrete output tape.

This is stronger than
{name (full := FoC.Computability.MachineDescription.ClosedFromTapeEquiv)}`MachineDescription.ClosedFromTapeEquiv`
and is only suitable when the final tape shape, including trailing blanks and
head position, is part of the public contract.
-/
def ExactClosedFromTape
    (D : MachineDescription) (Tin Tout : Tape Bool) : Prop :=
  forall T : Tape Bool,
    D.HaltsFromTape Tin T -> T = Tout

theorem canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tout : Tape Bool}
    (hAhalts : A.HaltsFromTape Tin Tmid)
    (hBhalts :
      B.HaltsFromTape
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        Tout) :
    (canonicalPrimitiveSeqDescription A B).HaltsFromTape Tin Tout := by
  have hid : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hAid :
      (seqSubroutine A ExactIdentityDescription Direction.right).HaltsFromTape
        Tin (Tape.move Direction.right Tmid) :=
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      hA hid hAhalts rfl
      (CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (Tape.move Direction.right Tmid))
  exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      (seqSubroutine_subroutineReady hA hid)
      hB hAid rfl hBhalts

theorem canonicalPrimitiveSeqDescription_haltsFromTape_exact
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tout : Tape Bool}
    (hAhalts : A.HaltsFromTape Tin Tmid)
    (hBhalts :
      B.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape Tmid)
        Tout) :
    (canonicalPrimitiveSeqDescription A B).HaltsFromTape Tin Tout := by
  simpa [canonicalPrimitiveSeqHandoffTape] using
    canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
      hA hB hAhalts hBhalts

/--
Run a canonical primitive sequence whose right-hand component reaches an
arbitrary finite-control state instead of its distinguished halt.

The target state is the right-hand state offset into the nested canonical
sequence.  Static dispatcher branchers use this form because the observed read
is represented by the branch target state.
-/
theorem canonicalPrimitiveSeqDescription_reaches_right_state
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tout : Tape Bool} {targetState : Nat}
    (hAhalts : A.HaltsFromTape Tin Tmid)
    (hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start,
              tape := Tape.move Direction.left
                (Tape.move Direction.right Tmid) } =
          { state := targetState, tape := Tout }) :
    exists n : Nat,
      (canonicalPrimitiveSeqDescription A B).runConfig n
          { state := (canonicalPrimitiveSeqDescription A B).start,
            tape := Tin } =
        { state :=
            canonicalPrimitiveSeqRightStateOffset A + targetState,
          tape := Tout } := by
  have hid : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hAid :
      (seqSubroutine A ExactIdentityDescription Direction.right).HaltsFromTape
        Tin (Tape.move Direction.right Tmid) :=
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      hA hid hAhalts rfl
      (CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (Tape.move Direction.right Tmid))
  rcases runConfig_eq_halt_of_haltsFromTape hAid with
    ⟨nAid, hAidRun⟩
  simpa [canonicalPrimitiveSeqDescription,
    canonicalPrimitiveSeqRightStateOffset] using
    seqSubroutine_reaches_right_state_of_runConfig_eq
      (A := seqSubroutine A ExactIdentityDescription Direction.right)
      (B := B)
      (handoffMove := Direction.left)
      (seqSubroutine_subroutineReady hA hid)
      hB hAidRun hBReach

theorem canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tout : Tape Bool}
    (hAhalts : A.HaltsFromTapeEquiv Tin Tmid)
    (hBhalts : B.HaltsFromTapeEquiv Tmid Tout) :
    (canonicalPrimitiveSeqDescription A B).HaltsFromTapeEquiv Tin Tout := by
  rcases hAhalts with ⟨TmidActual, hAactual, hTmidActual⟩
  rcases hBhalts with ⟨ToutBActual, hBactual, hToutBActual⟩
  have hBounceToMid :
      Tape.Equiv
        (Tape.move Direction.left
          (Tape.move Direction.right TmidActual))
        Tmid :=
    Tape.Equiv.trans
      (moveLeft_moveRight_equiv_self TmidActual)
      hTmidActual
  have hBfromBounce :
      B.HaltsFromTapeEquiv
        (Tape.move Direction.left
          (Tape.move Direction.right TmidActual))
        ToutBActual :=
    HaltsFromTapeEquiv_of_input_equiv
      (D := B)
      (Tin := Tmid)
      (Tin' :=
        Tape.move Direction.left
          (Tape.move Direction.right TmidActual))
      (Tout := ToutBActual)
      (Tape.Equiv.symm hBounceToMid)
      hBactual
  rcases hBfromBounce with
    ⟨ToutActual, hBactualFromBounce, hToutActual⟩
  exact
    ⟨ToutActual,
      canonicalPrimitiveSeqDescription_haltsFromTape_of_haltsFromTape
        hA hB hAactual hBactualFromBounce,
      Tape.Equiv.trans hToutActual hToutBActual⟩

theorem canonicalPrimitiveSeqDescription_haltsFromTape_inv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tout : Tape Bool}
    (hseq :
      (canonicalPrimitiveSeqDescription A B).HaltsFromTape Tin Tout) :
    exists Tmid : Tape Bool,
      A.HaltsFromTape Tin Tmid ∧
        B.HaltsFromTape
          (Tape.move Direction.left
            (Tape.move Direction.right Tmid))
          Tout := by
  have hid : ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  rcases
      seqSubroutine_haltsFromTape_closed_exists_mid
        (A := seqSubroutine A ExactIdentityDescription Direction.right)
        (B := B)
        (handoffMove := Direction.left)
        (seqSubroutine_subroutineReady hA hid)
        hB
        (by
          simpa [canonicalPrimitiveSeqDescription] using hseq) with
    ⟨TafterId, hAid, hBRun⟩
  rcases
      seqSubroutine_haltsFromTape_closed_exists_mid
        (A := A)
        (B := ExactIdentityDescription)
        (handoffMove := Direction.right)
        hA hid hAid with
    ⟨Tmid, hARun, hIdRun⟩
  have hTafterId :
      TafterId = Tape.move Direction.right Tmid := by
    rcases hIdRun with ⟨nId, hnId⟩
    have hrun :=
      CommonGround.Identity.exactIdentityDescription_runConfig_from_start
        nId (Tape.move Direction.right Tmid)
    have htape :
        (ExactIdentityDescription.runConfig nId
            { state := ExactIdentityDescription.start,
              tape := Tape.move Direction.right Tmid }).tape =
          TafterId :=
      hnId.right
    rw [hrun] at htape
    exact htape.symm
  exact
    ⟨Tmid, hARun, by
      simpa [hTafterId] using hBRun⟩

theorem canonicalPrimitiveSeqDescription_exactClosedFromTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tout : Tape Bool}
    (hAclosed : ExactClosedFromTape A Tin Tmid)
    (hBclosed :
      ExactClosedFromTape B
        (canonicalPrimitiveSeqHandoffTape Tmid)
        Tout) :
    ExactClosedFromTape
      (canonicalPrimitiveSeqDescription A B) Tin Tout := by
  intro T hhalt
  rcases
      canonicalPrimitiveSeqDescription_haltsFromTape_inv
        hA hB hhalt with
    ⟨TmidActual, hAactual, hBactual⟩
  have hmid : TmidActual = Tmid :=
    hAclosed TmidActual hAactual
  subst TmidActual
  exact hBclosed T (by
    simpa [canonicalPrimitiveSeqHandoffTape] using hBactual)

theorem canonicalPrimitiveSeqDescription_closedFromTapeEquiv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid Tout : Tape Bool}
    (hAclosed : A.ClosedFromTapeEquiv Tin Tmid)
    (hBclosed : B.ClosedFromTapeEquiv Tmid Tout) :
    (canonicalPrimitiveSeqDescription A B).ClosedFromTapeEquiv
      Tin Tout := by
  intro T hhalt
  rcases
      canonicalPrimitiveSeqDescription_haltsFromTape_inv
        hA hB hhalt with
    ⟨TmidActual, hAactual, hBactual⟩
  have hTmidActual : Tape.Equiv TmidActual Tmid :=
    hAclosed TmidActual hAactual
  have hBounceToMid :
      Tape.Equiv
        (Tape.move Direction.left
          (Tape.move Direction.right TmidActual))
        Tmid :=
    Tape.Equiv.trans
      (moveLeft_moveRight_equiv_self TmidActual)
      hTmidActual
  have hBfromMid :
      B.HaltsFromTapeEquiv Tmid T :=
    HaltsFromTapeEquiv_of_input_equiv
      (D := B)
      (Tin :=
        Tape.move Direction.left
          (Tape.move Direction.right TmidActual))
      (Tin' := Tmid)
      (Tout := T)
      hBounceToMid
      hBactual
  rcases hBfromMid with
    ⟨Tactual, hBactualFromMid, hTactual⟩
  have hout : Tape.Equiv Tactual Tout :=
    hBclosed Tactual hBactualFromMid
  exact Tape.Equiv.trans (Tape.Equiv.symm hTactual) hout

/-!
## Structured endpoint bridge
-/

/--
Canonical one-tape wrapper around a lowered structured three-tape component.

The first component materializes the old source tape into a guarded structured
three-tape encoding, the middle component is the lowered structured machine,
and the final component projects the old destination tape back out.
-/
def structured3EndpointBridgeDescription
    (initializer lowered projector : MachineDescription) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription initializer lowered)
    projector

theorem structured3EndpointBridgeDescription_subroutineReady
    {initializer lowered projector : MachineDescription}
    (hinitializer : initializer.SubroutineReady)
    (hlowered : lowered.SubroutineReady)
    (hprojector : projector.SubroutineReady) :
    (structured3EndpointBridgeDescription
      initializer lowered projector).SubroutineReady :=
  canonicalPrimitiveSeqDescription_subroutineReady
    (canonicalPrimitiveSeqDescription_subroutineReady
      hinitializer hlowered)
    hprojector

/--
Compose an old one-tape endpoint through a lowered structured three-tape
machine and a final projector.

This is the reusable packaging theorem for construction leaves whose internal
implementation is structured but whose public contract remains one-tape.
-/
theorem structured3EndpointBridgeDescription_haltsFromTapeEquiv
    {initializer lowered projector : MachineDescription}
    (hinitializer : initializer.SubroutineReady)
    (hlowered : lowered.SubroutineReady)
    (hprojector : projector.SubroutineReady)
    {Tin T0 T1 T2 U0 U1 U2 Tout : Tape Bool}
    (hinitializerRun :
      initializer.HaltsFromTapeEquiv Tin
        (encodedGuardedStructured3Tapes T0 T1 T2))
    (hloweredRun :
      lowered.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        (encodedGuardedStructured3Tapes U0 U1 U2))
    (hprojectorRun :
      projector.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes U0 U1 U2)
        Tout) :
    (structured3EndpointBridgeDescription
      initializer lowered projector).HaltsFromTapeEquiv Tin Tout := by
  have hfirst :
      (canonicalPrimitiveSeqDescription initializer lowered)
          |>.HaltsFromTapeEquiv
        Tin (encodedGuardedStructured3Tapes U0 U1 U2) :=
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      hinitializer hlowered hinitializerRun hloweredRun
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        hinitializer hlowered)
      hprojector
      hfirst hprojectorRun

/--
Exact forward endpoint composition for a lowered structured core.

The middle and final components are stated on the exact handoff tapes produced
by the canonical sequence.
-/
theorem structured3EndpointBridgeDescription_haltsFromTape
    {initializer lowered projector : MachineDescription}
    (hinitializer : initializer.SubroutineReady)
    (hlowered : lowered.SubroutineReady)
    (hprojector : projector.SubroutineReady)
    {Tin Tinit Tlowered Tout : Tape Bool}
    (hinitializerRun :
      initializer.HaltsFromTape Tin Tinit)
    (hloweredRun :
      lowered.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape Tinit)
        Tlowered)
    (hprojectorRun :
      projector.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape Tlowered)
        Tout) :
    (structured3EndpointBridgeDescription
      initializer lowered projector).HaltsFromTape Tin Tout := by
  have hfirst :
      (canonicalPrimitiveSeqDescription initializer lowered)
          |>.HaltsFromTape Tin Tlowered :=
    canonicalPrimitiveSeqDescription_haltsFromTape_exact
      hinitializer hlowered hinitializerRun hloweredRun
  exact
    canonicalPrimitiveSeqDescription_haltsFromTape_exact
      (canonicalPrimitiveSeqDescription_subroutineReady
        hinitializer hlowered)
      hprojector
      hfirst hprojectorRun

/--
Closed-side endpoint composition for a lowered structured core.

Any public halt of the wrapper must pass through the initializer, lowered core,
and projector, up to the same tape equivalence used by the canonical handoff
bounce.
-/
theorem structured3EndpointBridgeDescription_closedFromTapeEquiv
    {initializer lowered projector : MachineDescription}
    (hinitializer : initializer.SubroutineReady)
    (hlowered : lowered.SubroutineReady)
    (hprojector : projector.SubroutineReady)
    {Tin T0 T1 T2 U0 U1 U2 Tout : Tape Bool}
    (hinitializerClosed :
      initializer.ClosedFromTapeEquiv Tin
        (encodedGuardedStructured3Tapes T0 T1 T2))
    (hloweredClosed :
      lowered.ClosedFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        (encodedGuardedStructured3Tapes U0 U1 U2))
    (hprojectorClosed :
      projector.ClosedFromTapeEquiv
        (encodedGuardedStructured3Tapes U0 U1 U2)
        Tout) :
    (structured3EndpointBridgeDescription
      initializer lowered projector).ClosedFromTapeEquiv Tin Tout := by
  have hfirst :
      (canonicalPrimitiveSeqDescription initializer lowered)
          |>.ClosedFromTapeEquiv
        Tin (encodedGuardedStructured3Tapes U0 U1 U2) :=
    canonicalPrimitiveSeqDescription_closedFromTapeEquiv
      hinitializer hlowered hinitializerClosed hloweredClosed
  exact
    canonicalPrimitiveSeqDescription_closedFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        hinitializer hlowered)
      hprojector
      hfirst hprojectorClosed

/--
Exact closed-side endpoint composition for a lowered structured core.

Use this only for public contracts that require a literal final tape, such as
right-shifted handoff specs.  Equivalence-based contracts should use
{name}`structured3EndpointBridgeDescription_closedFromTapeEquiv`.
-/
theorem structured3EndpointBridgeDescription_exactClosedFromTape
    {initializer lowered projector : MachineDescription}
    (hinitializer : initializer.SubroutineReady)
    (hlowered : lowered.SubroutineReady)
    (hprojector : projector.SubroutineReady)
    {Tin Tinit Tlowered Tout : Tape Bool}
    (hinitializerClosed :
      ExactClosedFromTape initializer Tin Tinit)
    (hloweredClosed :
      ExactClosedFromTape lowered
        (canonicalPrimitiveSeqHandoffTape Tinit)
        Tlowered)
    (hprojectorClosed :
      ExactClosedFromTape projector
        (canonicalPrimitiveSeqHandoffTape Tlowered)
        Tout) :
    ExactClosedFromTape
      (structured3EndpointBridgeDescription
        initializer lowered projector) Tin Tout := by
  have hfirst :
      ExactClosedFromTape
        (canonicalPrimitiveSeqDescription initializer lowered)
        Tin Tlowered :=
    canonicalPrimitiveSeqDescription_exactClosedFromTape
      hinitializer hlowered hinitializerClosed hloweredClosed
  exact
    canonicalPrimitiveSeqDescription_exactClosedFromTape
      (canonicalPrimitiveSeqDescription_subroutineReady
        hinitializer hlowered)
      hprojector
      hfirst hprojectorClosed

theorem physicalPrimitiveSequenceGuardedContractEquiv_append
    {first second : List PhysicalPrimitive}
    {A B : MachineDescription}
    (hA : PhysicalPrimitiveSequenceGuardedContractEquiv first A)
    (hB : PhysicalPrimitiveSequenceGuardedContractEquiv second B) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (first ++ second)
      (canonicalPrimitiveSeqDescription A B) where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      hA.subroutineReady hB.subroutineReady
  realizes := by
    intro logical henabled
    rcases
        (physicalPrimitiveSequenceEnabled_append
          first second logical).mp henabled with
      ⟨hfirst, hsecond⟩
    have hAhalts := hA.realizes logical hfirst
    have hBhalts :=
      hB.realizes
        (applyPhysicalPrimitiveSequence first logical)
        hsecond
    simpa [applyPhysicalPrimitiveSequence_append] using
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        hA.subroutineReady hB.subroutineReady hAhalts hBhalts

/--
Compose canonical guarded primitive work with a final fragment whose endpoint
is only a logical-tape equivalence invariant.

This is intentionally one-way: after the second fragment the endpoint may no
longer be the canonical guarded encoding, so there is no generic way to keep
executing ordinary guarded primitive contracts without a guard-refresh
normalizer.
-/
theorem physicalPrimitiveSequenceGuardedContractEquiv_append_logicalEquiv
    {first second : List PhysicalPrimitive}
    {A B : MachineDescription}
    (hA : PhysicalPrimitiveSequenceGuardedContractEquiv first A)
    (hB :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        second B) :
    PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
      (first ++ second)
      (canonicalPrimitiveSeqDescription A B) where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      hA.subroutineReady hB.subroutineReady
  realizes := by
    intro logical henabled
    rcases
        (physicalPrimitiveSequenceEnabled_append
          first second logical).mp henabled with
      ⟨hfirst, hsecond⟩
    have hAhalts := hA.realizes logical hfirst
    rcases hB.realizes
        (applyPhysicalPrimitiveSequence first logical)
        hsecond with
      ⟨actual, hactual, hBhalts⟩
    refine ⟨actual, ?_, ?_⟩
    · simpa [applyPhysicalPrimitiveSequence_append] using hactual
    · simpa [applyPhysicalPrimitiveSequence_append] using
        canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
          hA.subroutineReady hB.subroutineReady hAhalts hBhalts

/-!
## Guard refresh boundary
-/

/--
Refresh contract for exact guard-slack endpoints produced by primitive rows.

This is the implementable Milestone 1 shape: the physical input is not an
arbitrary member of {name}`StructuredLogicalEquivEncodedTapes`, but an exact
endpoint obtained by running a primitive sequence on the guarded representative
of some source logical tapes.  The endpoint predicate records the exact target
logical representative that should be re-guarded.
-/
structure GuardSlackRefreshContract
    (refresh : MachineDescription) : Prop where
  subroutineReady : refresh.SubroutineReady
  realizes :
    forall (primitives : List PhysicalPrimitive)
      (source target : List (Tape Bool)) (physical : Tape Bool),
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target
        physical ->
        refresh.HaltsFromTapeEquiv
          physical
          (encodedGuardedStructuredTapes target)

namespace GuardSlackRefreshContract

theorem realizesSelf
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh)
    (primitives : List PhysicalPrimitive)
    (source : List (Tape Bool)) :
    refresh.HaltsFromTapeEquiv
      (encodedStructuredTapes
        (applyPhysicalPrimitiveSequence primitives
          (guardLogicalTapes source)))
      (encodedGuardedStructuredTapes
        (applyPhysicalPrimitiveSequence primitives source)) :=
  hrefresh.realizes primitives source
    (applyPhysicalPrimitiveSequence primitives source)
    (encodedStructuredTapes
      (applyPhysicalPrimitiveSequence primitives
        (guardLogicalTapes source)))
    (physicalPrimitiveSequenceGuardSlackEndpoint_self primitives source)

theorem realizesOfInputEquiv
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh)
    {primitives : List PhysicalPrimitive}
    {source target : List (Tape Bool)}
    {exactPhysical physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target
        exactPhysical)
    (hequiv : Tape.Equiv physical exactPhysical) :
    refresh.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) := by
  rcases
      hrefresh.realizes primitives source target exactPhysical
        hendpoint with
    ⟨actualOut, hhalts, hout⟩
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (D := refresh)
        (Tin := exactPhysical)
        (Tin' := physical)
        (Tout := actualOut)
        (Tape.Equiv.symm hequiv)
        hhalts with
    ⟨transportedOut, htransported, htransportedEquiv⟩
  exact
    ⟨transportedOut, htransported,
      Tape.Equiv.trans htransportedEquiv hout⟩

theorem realizesEndpointEquiv
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh)
    {primitives : List PhysicalPrimitive}
    {source target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv primitives source
        target physical) :
    refresh.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) := by
  rcases hendpoint with ⟨exactPhysical, hexact, hequiv⟩
  exact hrefresh.realizesOfInputEquiv hexact hequiv

end GuardSlackRefreshContract

/--
Bundled concrete normalizer for row-produced guard-slack endpoints.

This is the endpoint-aware successor to {lit}`GuardRefreshNormalizer` for the
refreshed static-lowering route.
-/
structure GuardSlackRefreshNormalizer where
  machine : MachineDescription
  contract : GuardSlackRefreshContract machine

namespace GuardSlackRefreshNormalizer

theorem subroutineReady (refresh : GuardSlackRefreshNormalizer) :
    refresh.machine.SubroutineReady :=
  refresh.contract.subroutineReady

theorem realizes
    (refresh : GuardSlackRefreshNormalizer)
    (primitives : List PhysicalPrimitive)
    (source target : List (Tape Bool)) (physical : Tape Bool)
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target
        physical) :
    refresh.machine.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) :=
  refresh.contract.realizes primitives source target physical hendpoint

theorem realizesEndpointEquiv
    (refresh : GuardSlackRefreshNormalizer)
    {primitives : List PhysicalPrimitive}
    {source target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv primitives source
        target physical) :
    refresh.machine.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) :=
  refresh.contract.realizesEndpointEquiv hendpoint

end GuardSlackRefreshNormalizer

/--
Contract for a machine that restores the canonical guarded encoding from a
logical-equivalence endpoint.

This is the explicit normalizer required after a row consumes represented guard
slack.  The input physical tape may encode any logical tape list pointwise
equivalent to {lit}`logical`; the output is the canonical guarded encoding of
{lit}`logical`.
-/
structure LogicalEquivGuardRefreshContract
    (refresh : MachineDescription) : Prop where
  subroutineReady : refresh.SubroutineReady
  realizes :
    forall (logical : List (Tape Bool)) (physical : Tape Bool),
      StructuredLogicalEquivEncodedTapes logical physical ->
        refresh.HaltsFromTapeEquiv
          physical
          (encodedGuardedStructuredTapes logical)

/--
Bundled concrete guard-refresh normalizer for the refreshed endpoint route.

This is the Milestone 1 gate for any claim of a fully concrete static lowerer:
downstream code may stay parametric over this bundle, but a real lowered
{name}`MachineDescription` must provide an actual machine and this contract.
-/
structure GuardRefreshNormalizer where
  machine : MachineDescription
  contract : LogicalEquivGuardRefreshContract machine

namespace GuardRefreshNormalizer

theorem subroutineReady (refresh : GuardRefreshNormalizer) :
    refresh.machine.SubroutineReady :=
  refresh.contract.subroutineReady

theorem realizes
    (refresh : GuardRefreshNormalizer)
    (logical : List (Tape Bool)) (physical : Tape Bool)
    (hphysical : StructuredLogicalEquivEncodedTapes logical physical) :
    refresh.machine.HaltsFromTapeEquiv
      physical
      (encodedGuardedStructuredTapes logical) :=
  refresh.contract.realizes logical physical hphysical

end GuardRefreshNormalizer

/--
Canonical composition of a row machine with a guard-refresh normalizer.
-/
def guardedLogicalEquivThenRefreshDescription
    (row refresh : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription row refresh

/--
Turn a row-produced guard-slack endpoint into a canonical guarded endpoint by
appending an endpoint-aware refresh normalizer.
-/
theorem physicalPrimitiveSequenceGuardSlackContractEquiv_thenRefresh
    {primitives : List PhysicalPrimitive}
    {machine refresh : MachineDescription}
    (hsequence :
      PhysicalPrimitiveSequenceGuardSlackContractEquiv primitives machine)
    (hrefresh : GuardSlackRefreshContract refresh) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      primitives
      (guardedLogicalEquivThenRefreshDescription machine refresh) where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      hsequence.subroutineReady hrefresh.subroutineReady
  realizes := by
    intro logical henabled
    have hrefreshHalts :=
      hrefresh.realizesSelf primitives logical
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        hsequence.subroutineReady hrefresh.subroutineReady
        (hsequence.realizes logical henabled) hrefreshHalts

/--
Turn an endpoint-aware guard-slack row into a canonical guarded row by
appending an endpoint-aware refresh normalizer.
-/
theorem lowersGuardedTransitionGuardSlack_thenRefresh
    {D : Description} {t : Transition}
    {row refresh : MachineDescription}
    (hrow : LowersGuardedTransitionGuardSlack D t row)
    (hrefresh : GuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (guardedLogicalEquivThenRefreshDescription row refresh) where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      hrow.subroutineReady hrefresh.subroutineReady
  realizes := by
    intro c hc hsource hreads
    rcases hrow.realizes c hc hsource hreads with
      ⟨physical, hendpoint, hrowHalts⟩
    have hrefreshHalts :=
      hrefresh.realizes
        (transitionPrimitiveSequenceOfRow3 t)
        c.tapes
        (D.applyActions t.actions c.tapes)
        physical
        hendpoint
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        hrow.subroutineReady hrefresh.subroutineReady
        hrowHalts hrefreshHalts

/--
Turn a row with a logical-equivalence endpoint into a canonical guarded row
once a guard-refresh normalizer is available.

This is the reusable bridge for rows with several moving tapes: run one
guard-consuming row fragment, refresh its endpoint, then later guarded row
machines can start from the canonical guarded layout again.
-/
theorem lowersGuardedTransitionLogicalEquiv_thenRefresh
    {D : Description} {t : Transition}
    {row refresh : MachineDescription}
    (hrow : LowersGuardedTransitionLogicalEquiv D t row)
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (guardedLogicalEquivThenRefreshDescription row refresh) where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      hrow.subroutineReady hrefresh.subroutineReady
  realizes := by
    intro c hc hsource hreads
    rcases hrow.realizes c hc hsource hreads with
      ⟨physical, hphysical, hrowHalts⟩
    have hrefreshHalts :=
      hrefresh.realizes
        (D.applyActions t.actions c.tapes)
        physical hphysical
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        hrow.subroutineReady hrefresh.subroutineReady
        hrowHalts hrefreshHalts

/--
Turn a primitive sequence with a logical-equivalence endpoint into a canonical
guarded primitive-sequence endpoint by appending a guard-refresh normalizer.

This is the primitive-level counterpart of
{name}`lowersGuardedTransitionLogicalEquiv_thenRefresh`.  It lets a row
compiler run a guard-consuming action, restore the canonical guarded layout,
and then continue with the next action.
-/
theorem physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv_thenRefresh
    {primitives : List PhysicalPrimitive}
    {machine refresh : MachineDescription}
    (hsequence :
      PhysicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        primitives machine)
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      primitives
      (guardedLogicalEquivThenRefreshDescription machine refresh) where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      hsequence.subroutineReady hrefresh.subroutineReady
  realizes := by
    intro logical henabled
    rcases hsequence.realizes logical henabled with
      ⟨actual, hactual, hmachine⟩
    have hphysical :
        StructuredLogicalEquivEncodedTapes
          (applyPhysicalPrimitiveSequence primitives logical)
          (encodedStructuredTapes actual) :=
      ⟨actual, hactual, rfl⟩
    have hrefreshHalts :=
      hrefresh.realizes
        (applyPhysicalPrimitiveSequence primitives logical)
        (encodedStructuredTapes actual)
        hphysical
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        hsequence.subroutineReady hrefresh.subroutineReady
        hmachine hrefreshHalts

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
