import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.Primitives
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
