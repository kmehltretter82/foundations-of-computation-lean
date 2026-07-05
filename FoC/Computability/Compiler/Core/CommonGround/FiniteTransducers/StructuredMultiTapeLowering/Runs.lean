import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.RefreshedRows

set_option doc.verso true

/-!
# Structured run lowering

This module starts Milestone 9: composing already-proved row lowerings across
structured-machine executions.

The first bridge is deliberately trace-shaped.  Given a source configuration
and a step bound, it follows the structured machine's executable transition
choice and composes the corresponding one-tape row machines.  The endpoint uses
the existing abstract guard-refresh contract, so each row starts again from the
canonical guarded encoding.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
Trace-shaped one-tape lowering for a bounded structured execution.

If the structured machine can take a step, the selected row machine is composed
with the trace lowering for the next configuration.  If no row is selected, the
trace machine is the no-op cursor machine; the simulation theorem only uses
this branch for zero-step or impossible nonzero runs.
-/
def loweredTraceDescriptionWithRefresh
    (D : Description) (refresh : MachineDescription) :
    Nat -> Configuration -> MachineDescription
  | 0, _c => cursorNoopDescription
  | n + 1, c =>
      match D.lookupTransition c with
      | none => cursorNoopDescription
      | some t =>
          canonicalPrimitiveSeqDescription
            (readWriteRow3DescriptionOfRowWithRefresh t refresh)
            (loweredTraceDescriptionWithRefresh D refresh n
              (structuredTransitionTarget D t c))

theorem loweredTraceDescriptionWithRefresh_subroutineReady
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    forall (n : Nat) (c : Configuration),
      (loweredTraceDescriptionWithRefresh D refresh n c).SubroutineReady := by
  intro n
  induction n with
  | zero =>
      intro c
      exact cursorNoopDescription_subroutineReady
  | succ n ih =>
      intro c
      cases hlookup : D.lookupTransition c with
      | none =>
          simp [loweredTraceDescriptionWithRefresh, hlookup]
          exact cursorNoopDescription_subroutineReady
      | some t =>
          have hrow :
              LowersGuardedTransitionEquiv D t
                (readWriteRow3DescriptionOfRowWithRefresh t refresh) :=
            hD.lookup_lowersGuardedTransitionEquiv_withRefresh
              hlookup hrefresh
          simp [loweredTraceDescriptionWithRefresh, hlookup]
          exact
            canonicalPrimitiveSeqDescription_subroutineReady
              hrow.subroutineReady
              (ih (structuredTransitionTarget D t c))

/--
Bounded run simulation for the refresh-backed row lowerer.

This theorem is the first run-level Milestone 9 bridge.  It does not yet lower
a whole structured table into one static dispatcher; instead it proves that the
row lowerings compose correctly along any concrete structured execution trace.
-/
theorem loweredTraceDescriptionWithRefresh_simulates_computesIn
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    forall {n : Nat} {c final : Configuration},
      Description.ComputesIn D n c final ->
        c.tapes.length = D.tapeCount ->
          (loweredTraceDescriptionWithRefresh D refresh n c).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes final.tapes) := by
  intro n c final hcomp
  induction hcomp with
  | zero c =>
      intro _hc
      exact
        MachineDescription.HaltsFromTape.toEquiv
          (cursorNoopDescription_haltsFromTape
            (encodedGuardedStructuredTapes c.tapes))
  | succ hstep hrest ih =>
      rename_i n c next final
      intro hc
      cases hlookup : D.lookupTransition c with
      | none =>
          simp [Description.stepConfig, hlookup] at hstep
      | some t =>
          have hstepLookup :
              D.stepConfig c =
                some (structuredTransitionTarget D t c) :=
            stepConfig_eq_some_of_lookupTransition hlookup
          have hnext :
              next = structuredTransitionTarget D t c := by
            rw [hstep] at hstepLookup
            exact Option.some.inj hstepLookup
          cases hnext
          have hrowReady :
              (readWriteRow3DescriptionOfRowWithRefresh
                t refresh).SubroutineReady :=
            (hD.lookup_lowersGuardedTransitionEquiv_withRefresh
              hlookup hrefresh).subroutineReady
          have htailReady :
              (loweredTraceDescriptionWithRefresh D refresh n
                (structuredTransitionTarget D t c)).SubroutineReady :=
            loweredTraceDescriptionWithRefresh_subroutineReady
              hD hrefresh n (structuredTransitionTarget D t c)
          have hrowRun :=
            (hD.lookup_realizes_structured_step_withRefresh
              hc hlookup rfl hrefresh).right
          have htailRun :=
            ih (Description.stepConfig_tape_count hstep)
          simp [loweredTraceDescriptionWithRefresh, hlookup]
          exact
            canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
              hrowReady htailReady hrowRun htailRun

theorem loweredRun_simulates_structured_run_withRefresh
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : LogicalEquivGuardRefreshContract refresh)
    {c final : Configuration}
    (hcomp : Description.Computes D c final)
    (hc : c.tapes.length = D.tapeCount) :
    exists n : Nat,
      (loweredTraceDescriptionWithRefresh D refresh n c).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes final.tapes) := by
  rcases hcomp with ⟨n, hrun⟩
  exact
    ⟨n,
      loweredTraceDescriptionWithRefresh_simulates_computesIn
        hD hrefresh hrun hc⟩

/--
Executable bounded-run version of
{name}`loweredTraceDescriptionWithRefresh_simulates_computesIn`.

This follows {name}`Structured.Description.runConfig` directly, including its
early-stop behavior when no transition is selected.
-/
theorem loweredTraceDescriptionWithRefresh_simulates_runConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    forall (n : Nat) (c : Configuration),
      c.tapes.length = D.tapeCount ->
        (loweredTraceDescriptionWithRefresh D refresh n c).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes c.tapes)
          (encodedGuardedStructuredTapes (D.runConfig n c).tapes) := by
  intro n
  induction n with
  | zero =>
      intro c _hc
      exact
        MachineDescription.HaltsFromTape.toEquiv
          (cursorNoopDescription_haltsFromTape
            (encodedGuardedStructuredTapes c.tapes))
  | succ n ih =>
      intro c hc
      cases hlookup : D.lookupTransition c with
      | none =>
          have hstepNone : D.stepConfig c = none := by
            simp [Description.stepConfig, hlookup]
          have hrun :
              D.runConfig (n + 1) c = c := by
            simp [Description.runConfig, hstepNone]
          rw [hrun]
          simp [loweredTraceDescriptionWithRefresh, hlookup]
          exact
            MachineDescription.HaltsFromTape.toEquiv
              (cursorNoopDescription_haltsFromTape
                (encodedGuardedStructuredTapes c.tapes))
      | some t =>
          have hstep :
              D.stepConfig c =
                some (structuredTransitionTarget D t c) :=
            stepConfig_eq_some_of_lookupTransition hlookup
          have hrowReady :
              (readWriteRow3DescriptionOfRowWithRefresh
                t refresh).SubroutineReady :=
            (hD.lookup_lowersGuardedTransitionEquiv_withRefresh
              hlookup hrefresh).subroutineReady
          have htailReady :
              (loweredTraceDescriptionWithRefresh D refresh n
                (structuredTransitionTarget D t c)).SubroutineReady :=
            loweredTraceDescriptionWithRefresh_subroutineReady
              hD hrefresh n (structuredTransitionTarget D t c)
          have hrowRun :=
            (hD.lookup_realizes_structured_step_withRefresh
              hc hlookup rfl hrefresh).right
          have htailRun :=
            ih (structuredTransitionTarget D t c)
              (Description.stepConfig_tape_count hstep)
          have hrun :
              D.runConfig (n + 1) c =
                D.runConfig n (structuredTransitionTarget D t c) := by
            simp [Description.runConfig, hstep]
          rw [hrun]
          simp [loweredTraceDescriptionWithRefresh, hlookup]
          exact
            canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
              hrowReady htailReady hrowRun htailRun

theorem loweredTraceDescriptionWithRefresh_simulates_haltsWithTapes
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : LogicalEquivGuardRefreshContract refresh)
    {c : Configuration} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes c tapes)
    (hc : c.tapes.length = D.tapeCount) :
    exists n : Nat,
      (loweredTraceDescriptionWithRefresh D refresh n c).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes tapes) := by
  rcases hhalts with ⟨n, hrun⟩
  have hsim :=
    loweredTraceDescriptionWithRefresh_simulates_runConfig
      hD hrefresh n c hc
  have htapes :
      (D.runConfig n c).tapes = tapes :=
    congrArg Configuration.tapes hrun
  exact ⟨n, by simpa [htapes] using hsim⟩

theorem loweredTraceDescriptionWithRefresh_simulates_haltsFromConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : LogicalEquivGuardRefreshContract refresh)
    {c : Configuration}
    (hhalts : D.HaltsFromConfig c)
    (hc : c.tapes.length = D.tapeCount) :
    exists n : Nat,
      D.HaltsIn n c ∧
        (loweredTraceDescriptionWithRefresh D refresh n c).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes c.tapes)
          (encodedGuardedStructuredTapes (D.runConfig n c).tapes) := by
  rcases hhalts with ⟨n, hhalt⟩
  exact
    ⟨n, hhalt,
      loweredTraceDescriptionWithRefresh_simulates_runConfig
        hD hrefresh n c hc⟩

theorem description_initial_tapes_length
    (D : Description) (inputs : List (Word Bool)) :
    (D.initial inputs).tapes.length = D.tapeCount := by
  simp [Description.initial]

theorem loweredTraceDescriptionWithRefresh_simulates_initial_runConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : LogicalEquivGuardRefreshContract refresh)
    (n : Nat) (inputs : List (Word Bool)) :
    (loweredTraceDescriptionWithRefresh D refresh n
      (D.initial inputs)).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes (D.initial inputs).tapes)
      (encodedGuardedStructuredTapes
        (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithRefresh_simulates_runConfig
    hD hrefresh n (D.initial inputs)
    (description_initial_tapes_length D inputs)

theorem loweredTraceDescriptionWithRefresh_simulates_initial_haltsWithTapes
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : LogicalEquivGuardRefreshContract refresh)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      (loweredTraceDescriptionWithRefresh D refresh n
        (D.initial inputs)).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes (D.initial inputs).tapes)
        (encodedGuardedStructuredTapes tapes) :=
  loweredTraceDescriptionWithRefresh_simulates_haltsWithTapes
    hD hrefresh hhalts
    (description_initial_tapes_length D inputs)

theorem loweredTraceDescriptionWithRefresh_simulates_initial_haltsFromConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : LogicalEquivGuardRefreshContract refresh)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        (loweredTraceDescriptionWithRefresh D refresh n
          (D.initial inputs)).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithRefresh_simulates_haltsFromConfig
    hD hrefresh hhalts
    (description_initial_tapes_length D inputs)

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
