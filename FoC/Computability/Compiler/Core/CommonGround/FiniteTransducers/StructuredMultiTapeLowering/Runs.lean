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

/--
Endpoint-aware trace-shaped one-tape lowering for a bounded structured
execution.

This is the guard-slack-refresh successor to
{name}`loweredTraceDescriptionWithRefresh`.
-/
def loweredTraceDescriptionWithGuardSlackRefresh
    (D : Description) (refresh : MachineDescription) :
    Nat -> Configuration -> MachineDescription
  | 0, _c => cursorNoopDescription
  | n + 1, c =>
      match D.lookupTransition c with
      | none => cursorNoopDescription
      | some t =>
          canonicalPrimitiveSeqDescription
            (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
              t refresh)
            (loweredTraceDescriptionWithGuardSlackRefresh D refresh n
              (structuredTransitionTarget D t c))

theorem loweredTraceDescriptionWithGuardSlackRefresh_subroutineReady
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : GuardSlackRefreshContract refresh) :
    forall (n : Nat) (c : Configuration),
      (loweredTraceDescriptionWithGuardSlackRefresh
        D refresh n c).SubroutineReady := by
  intro n
  induction n with
  | zero =>
      intro c
      exact cursorNoopDescription_subroutineReady
  | succ n ih =>
      intro c
      cases hlookup : D.lookupTransition c with
      | none =>
          simp [loweredTraceDescriptionWithGuardSlackRefresh, hlookup]
          exact cursorNoopDescription_subroutineReady
      | some t =>
          have hrow :
              LowersGuardedTransitionEquiv D t
                (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
                  t refresh) :=
            hD.lookup_lowersGuardedTransitionEquiv_withGuardSlackRefresh
              hlookup hrefresh
          simp [loweredTraceDescriptionWithGuardSlackRefresh, hlookup]
          exact
            canonicalPrimitiveSeqDescription_subroutineReady
              hrow.subroutineReady
              (ih (structuredTransitionTarget D t c))

theorem loweredTraceDescriptionWithGuardSlackRefresh_simulates_computesIn
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : GuardSlackRefreshContract refresh) :
    forall {n : Nat} {c final : Configuration},
      Description.ComputesIn D n c final ->
        c.tapes.length = D.tapeCount ->
          (loweredTraceDescriptionWithGuardSlackRefresh
            D refresh n c).HaltsFromTapeEquiv
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
              (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
                t refresh).SubroutineReady :=
            (hD.lookup_lowersGuardedTransitionEquiv_withGuardSlackRefresh
              hlookup hrefresh).subroutineReady
          have htailReady :
              (loweredTraceDescriptionWithGuardSlackRefresh
                D refresh n
                (structuredTransitionTarget D t c)).SubroutineReady :=
            loweredTraceDescriptionWithGuardSlackRefresh_subroutineReady
              hD hrefresh n (structuredTransitionTarget D t c)
          have hrowRun :=
            (hD.lookup_realizes_structured_step_withGuardSlackRefresh
              hc hlookup rfl hrefresh).right
          have htailRun :=
            ih (Description.stepConfig_tape_count hstep)
          simp [loweredTraceDescriptionWithGuardSlackRefresh, hlookup]
          exact
            canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
              hrowReady htailReady hrowRun htailRun

theorem loweredTraceDescriptionWithGuardSlackRefresh_simulates_runConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : GuardSlackRefreshContract refresh) :
    forall (n : Nat) (c : Configuration),
      c.tapes.length = D.tapeCount ->
        (loweredTraceDescriptionWithGuardSlackRefresh
          D refresh n c).HaltsFromTapeEquiv
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
          simp [loweredTraceDescriptionWithGuardSlackRefresh, hlookup]
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
              (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
                t refresh).SubroutineReady :=
            (hD.lookup_lowersGuardedTransitionEquiv_withGuardSlackRefresh
              hlookup hrefresh).subroutineReady
          have htailReady :
              (loweredTraceDescriptionWithGuardSlackRefresh
                D refresh n
                (structuredTransitionTarget D t c)).SubroutineReady :=
            loweredTraceDescriptionWithGuardSlackRefresh_subroutineReady
              hD hrefresh n (structuredTransitionTarget D t c)
          have hrowRun :=
            (hD.lookup_realizes_structured_step_withGuardSlackRefresh
              hc hlookup rfl hrefresh).right
          have htailRun :=
            ih (structuredTransitionTarget D t c)
              (Description.stepConfig_tape_count hstep)
          have hrun :
              D.runConfig (n + 1) c =
                D.runConfig n (structuredTransitionTarget D t c) := by
            simp [Description.runConfig, hstep]
          rw [hrun]
          simp [loweredTraceDescriptionWithGuardSlackRefresh, hlookup]
          exact
            canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
              hrowReady htailReady hrowRun htailRun

theorem loweredTraceDescriptionWithGuardSlackRefresh_simulates_haltsWithTapes
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : GuardSlackRefreshContract refresh)
    {c : Configuration} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes c tapes)
    (hc : c.tapes.length = D.tapeCount) :
    exists n : Nat,
      (loweredTraceDescriptionWithGuardSlackRefresh
        D refresh n c).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes tapes) := by
  rcases hhalts with ⟨n, hrun⟩
  have hsim :=
    loweredTraceDescriptionWithGuardSlackRefresh_simulates_runConfig
      hD hrefresh n c hc
  have htapes :
      (D.runConfig n c).tapes = tapes :=
    congrArg Configuration.tapes hrun
  exact ⟨n, by simpa [htapes] using hsim⟩

theorem loweredTraceDescriptionWithGuardSlackRefresh_simulates_haltsFromConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : GuardSlackRefreshContract refresh)
    {c : Configuration}
    (hhalts : D.HaltsFromConfig c)
    (hc : c.tapes.length = D.tapeCount) :
    exists n : Nat,
      D.HaltsIn n c ∧
        (loweredTraceDescriptionWithGuardSlackRefresh
          D refresh n c).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes c.tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n c).tapes) := by
  rcases hhalts with ⟨n, hhalt⟩
  exact
    ⟨n, hhalt,
      loweredTraceDescriptionWithGuardSlackRefresh_simulates_runConfig
        hD hrefresh n c hc⟩

/--
Trace-shaped one-tape lowering over the structured-singleton refresh contract.

This is the Milestone 1 route that keeps the exact structured target while
requiring only row-produced singleton endpoint shapes from the refresh
normalizer.
-/
def loweredTraceDescriptionWithStructuredSingletonRefresh
    (D : Description) (refresh : MachineDescription) :
    Nat -> Configuration -> MachineDescription
  | 0, _c => cursorNoopDescription
  | n + 1, c =>
      match D.lookupTransition c with
      | none => cursorNoopDescription
      | some t =>
          canonicalPrimitiveSeqDescription
            (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
              t refresh)
            (loweredTraceDescriptionWithStructuredSingletonRefresh D refresh n
              (structuredTransitionTarget D t c))

theorem loweredTraceDescriptionWithStructuredSingletonRefresh_subroutineReady
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    forall (n : Nat) (c : Configuration),
      (loweredTraceDescriptionWithStructuredSingletonRefresh
        D refresh n c).SubroutineReady := by
  intro n
  induction n with
  | zero =>
      intro c
      exact cursorNoopDescription_subroutineReady
  | succ n ih =>
      intro c
      cases hlookup : D.lookupTransition c with
      | none =>
          simp [loweredTraceDescriptionWithStructuredSingletonRefresh,
            hlookup]
          exact cursorNoopDescription_subroutineReady
      | some t =>
          have hrow :
              LowersGuardedTransitionEquiv D t
                (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
                  t refresh) :=
            hD.lookup_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh
              hlookup hrefresh
          simp [loweredTraceDescriptionWithStructuredSingletonRefresh,
            hlookup]
          exact
            canonicalPrimitiveSeqDescription_subroutineReady
              hrow.subroutineReady
              (ih (structuredTransitionTarget D t c))

theorem loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_computesIn
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    forall {n : Nat} {c final : Configuration},
      Description.ComputesIn D n c final ->
        c.tapes.length = D.tapeCount ->
          (loweredTraceDescriptionWithStructuredSingletonRefresh
            D refresh n c).HaltsFromTapeEquiv
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
              (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
                t refresh).SubroutineReady :=
            (hD.lookup_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh
              hlookup hrefresh).subroutineReady
          have htailReady :
              (loweredTraceDescriptionWithStructuredSingletonRefresh
                D refresh n
                (structuredTransitionTarget D t c)).SubroutineReady :=
            loweredTraceDescriptionWithStructuredSingletonRefresh_subroutineReady
              hD hrefresh n (structuredTransitionTarget D t c)
          have hrowRun :=
            (hD.lookup_realizes_structured_step_withStructuredSingletonRefresh
              hc hlookup rfl hrefresh).right
          have htailRun :=
            ih (Description.stepConfig_tape_count hstep)
          simp [loweredTraceDescriptionWithStructuredSingletonRefresh,
            hlookup]
          exact
            canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
              hrowReady htailReady hrowRun htailRun

theorem loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_runConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    forall (n : Nat) (c : Configuration),
      c.tapes.length = D.tapeCount ->
        (loweredTraceDescriptionWithStructuredSingletonRefresh
          D refresh n c).HaltsFromTapeEquiv
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
          simp [loweredTraceDescriptionWithStructuredSingletonRefresh,
            hlookup]
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
              (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
                t refresh).SubroutineReady :=
            (hD.lookup_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh
              hlookup hrefresh).subroutineReady
          have htailReady :
              (loweredTraceDescriptionWithStructuredSingletonRefresh
                D refresh n
                (structuredTransitionTarget D t c)).SubroutineReady :=
            loweredTraceDescriptionWithStructuredSingletonRefresh_subroutineReady
              hD hrefresh n (structuredTransitionTarget D t c)
          have hrowRun :=
            (hD.lookup_realizes_structured_step_withStructuredSingletonRefresh
              hc hlookup rfl hrefresh).right
          have htailRun :=
            ih (structuredTransitionTarget D t c)
              (Description.stepConfig_tape_count hstep)
          have hrun :
              D.runConfig (n + 1) c =
                D.runConfig n (structuredTransitionTarget D t c) := by
            simp [Description.runConfig, hstep]
          rw [hrun]
          simp [loweredTraceDescriptionWithStructuredSingletonRefresh,
            hlookup]
          exact
            canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
              hrowReady htailReady hrowRun htailRun

theorem loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_haltsWithTapes
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh)
    {c : Configuration} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes c tapes)
    (hc : c.tapes.length = D.tapeCount) :
    exists n : Nat,
      (loweredTraceDescriptionWithStructuredSingletonRefresh
        D refresh n c).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes tapes) := by
  rcases hhalts with ⟨n, hrun⟩
  have hsim :=
    loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_runConfig
      hD hrefresh n c hc
  have htapes :
      (D.runConfig n c).tapes = tapes :=
    congrArg Configuration.tapes hrun
  exact ⟨n, by simpa [htapes] using hsim⟩

theorem loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_haltsFromConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh)
    {c : Configuration}
    (hhalts : D.HaltsFromConfig c)
    (hc : c.tapes.length = D.tapeCount) :
    exists n : Nat,
      D.HaltsIn n c ∧
        (loweredTraceDescriptionWithStructuredSingletonRefresh
          D refresh n c).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes c.tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n c).tapes) := by
  rcases hhalts with ⟨n, hhalt⟩
  exact
    ⟨n, hhalt,
      loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_runConfig
        hD hrefresh n c hc⟩

theorem description_initial_tapes_length
    (D : Description) (inputs : List (Word Bool)) :
    (D.initial inputs).tapes.length = D.tapeCount := by
  simp [Description.initial]

/-!
## Static-step run contracts

The trace lowerer above still chooses one row from Lean's structured
execution trace.  A future physical dispatcher will instead keep the
structured control state in the one-tape finite control and repeatedly run the
same ordinary {name}`MachineDescription`.

The definitions below isolate the run-composition theorem needed for that
route.  They do not build the dispatcher yet; they state the exact contract a
static dispatcher must satisfy and prove that such a dispatcher composes across
{name}`Description.runConfig`.
-/

/--
Run an ordinary one-tape description from one physical control state to another,
observing the tape endpoint up to {name}`Tape.Equiv`.

Unlike {name}`MachineDescription.HaltsFromTapeEquiv`, this relation does not
force the source state to be {lit}`D.start` or the target state to be
{lit}`D.halt`.  It is therefore suitable for static lowerers whose physical
control state encodes the structured finite-control state.
-/
def RunsFromStateTapeEquiv
    (M : MachineDescription)
    (sourceState targetState : Nat)
    (Tin Tout : Tape Bool) : Prop :=
  exists n : Nat, exists Tactual : Tape Bool,
    M.runConfig n { state := sourceState, tape := Tin } =
      { state := targetState, tape := Tactual } ∧
    Tape.Equiv Tactual Tout

theorem runsFromStateTapeEquiv_refl
    (M : MachineDescription) (state : Nat) (T : Tape Bool) :
    RunsFromStateTapeEquiv M state state T T := by
  exact ⟨0, T, rfl, Tape.Equiv.refl T⟩

theorem runsFromStateTapeEquiv_of_input_equiv
    {M : MachineDescription}
    {sourceState targetState : Nat}
    {Tin Tin' Tout : Tape Bool}
    (h : RunsFromStateTapeEquiv M sourceState targetState Tin Tout)
    (hin : Tape.Equiv Tin' Tin) :
    RunsFromStateTapeEquiv M sourceState targetState Tin' Tout := by
  rcases h with ⟨n, Tactual, hrun, hout⟩
  let final' :=
    M.runConfig n { state := sourceState, tape := Tin' }
  have hrunEquiv :=
    MachineDescription.runConfig_equiv M n
      (c := { state := sourceState, tape := Tin' })
      (d := { state := sourceState, tape := Tin })
      rfl hin
  have hstate : final'.state = targetState := by
    change
      (M.runConfig n { state := sourceState, tape := Tin' }).state =
        targetState
    simpa [hrun] using hrunEquiv.left
  have htape : Tape.Equiv final'.tape Tactual := by
    change
      Tape.Equiv
        (M.runConfig n { state := sourceState, tape := Tin' }).tape
        Tactual
    simpa [hrun] using hrunEquiv.right
  have hfinal :
      final' = { state := targetState, tape := final'.tape } := by
    cases h : final' with
    | mk state tape =>
        have hs : state = targetState := by
          simpa [h] using hstate
        simp [hs]
  exact
    ⟨n, final'.tape, hfinal,
      Tape.Equiv.trans htape hout⟩

theorem runsFromStateTapeEquiv_trans
    {M : MachineDescription}
    {sourceState middleState targetState : Nat}
    {Tin Tmid Tout : Tape Bool}
    (hfirst :
      RunsFromStateTapeEquiv M sourceState middleState Tin Tmid)
    (hsecond :
      RunsFromStateTapeEquiv M middleState targetState Tmid Tout) :
    RunsFromStateTapeEquiv M sourceState targetState Tin Tout := by
  rcases hfirst with ⟨nFirst, TmidActual, hfirstRun, hmid⟩
  have hsecondFromActual :
      RunsFromStateTapeEquiv M middleState targetState
        TmidActual Tout :=
    runsFromStateTapeEquiv_of_input_equiv hsecond hmid
  rcases hsecondFromActual with
    ⟨nSecond, ToutActual, hsecondRun, hout⟩
  refine ⟨nFirst + nSecond, ToutActual, ?_, hout⟩
  rw [MachineDescription.runConfig_add]
  rw [hfirstRun]
  exact hsecondRun

/--
Turn an arbitrary-state run into the ordinary halting predicate when the source
and target states are the machine's public start and halt states.
-/
theorem RunsFromStateTapeEquiv.toHaltsFromTapeEquiv
    {M : MachineDescription}
    {sourceState targetState : Nat}
    {Tin Tout : Tape Bool}
    (h : RunsFromStateTapeEquiv M sourceState targetState Tin Tout)
    (hstart : M.start = sourceState)
    (hhalt : targetState = M.halt) :
    M.HaltsFromTapeEquiv Tin Tout := by
  rcases h with ⟨n, Tactual, hrun, hout⟩
  have hrunHalt :
      M.runConfig n { state := M.start, tape := Tin } =
        { state := M.halt, tape := Tactual } := by
    simpa [hstart, hhalt] using hrun
  refine ⟨Tactual, ⟨n, ?_⟩, hout⟩
  constructor
  · change
      (M.runConfig n { state := M.start, tape := Tin }).state =
        M.halt
    rw [hrunHalt]
  · change
      (M.runConfig n { state := M.start, tape := Tin }).tape =
        Tactual
    rw [hrunHalt]

/-- The structured one-step target, using the executable stuck-as-self policy. -/
def oneStepOrSelf (D : Description) (c : Configuration) :
    Configuration :=
  match D.stepConfig c with
  | none => c
  | some next => next

@[simp] theorem oneStepOrSelf_of_stepConfig_none
    {D : Description} {c : Configuration}
    (hstep : D.stepConfig c = none) :
    oneStepOrSelf D c = c := by
  simp [oneStepOrSelf, hstep]

@[simp] theorem oneStepOrSelf_of_stepConfig_some
    {D : Description} {c next : Configuration}
    (hstep : D.stepConfig c = some next) :
    oneStepOrSelf D c = next := by
  simp [oneStepOrSelf, hstep]

/--
Abstract contract for a single static physical dispatcher.

The dispatcher is an ordinary one-tape description.  Its physical control
state is related to the structured state by {lit}`stateMap`; its tape boundary
uses the canonical guarded layout.  Proving this contract for a real dispatcher
is the remaining static table-lowering work.
-/
structure StaticStepLoweringWithRefresh
    (D : Description) (M : MachineDescription)
    (stateMap : Nat -> Nat) : Prop where
  wellFormed : M.WellFormed
  realizes :
    forall c : Configuration,
      c.state < D.stateCount ->
        c.tapes.length = D.tapeCount ->
          RunsFromStateTapeEquiv M
            (stateMap c.state)
            (stateMap (oneStepOrSelf D c).state)
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes (oneStepOrSelf D c).tapes)

/--
Bundled target for the eventual static lowered one-tape machine.

The step contract is separated from the start/halt hooks so intermediate
dispatcher states remain free to use a larger physical state space.
-/
structure StaticLoweredDescriptionWithRefresh
    (D : Description) : Type where
  machine : MachineDescription
  stateMap : Nat -> Nat
  start_eq : machine.start = stateMap D.start
  halt_eq : stateMap D.halt = machine.halt
  stepLowering :
    StaticStepLoweringWithRefresh D machine stateMap

/--
Prerequisites for the refreshed static-lowering route.

This bundle records the Milestone 1 endpoint-normalization decision: the
static dispatcher route may be developed over a supplied
{name}`GuardRefreshNormalizer`, but downstream users should not treat that as a
closed concrete lowerer until this field is filled by an actual normalizer.
-/
structure StaticLoweringWithRefreshPrerequisites
    (D : Description) : Type where
  wellFormed : D.WellFormed
  rows : SupportsReadWriteRows3 D
  refresh : GuardRefreshNormalizer

namespace StaticLoweringWithRefreshPrerequisites

theorem refreshSubroutineReady
    {D : Description}
    (P : StaticLoweringWithRefreshPrerequisites D) :
    P.refresh.machine.SubroutineReady :=
  P.refresh.subroutineReady

theorem refreshRealizes
    {D : Description}
    (P : StaticLoweringWithRefreshPrerequisites D)
    (logical : List (Tape Bool)) (physical : Tape Bool)
    (hphysical : StructuredLogicalEquivEncodedTapes logical physical) :
    P.refresh.machine.HaltsFromTapeEquiv
      physical
      (encodedGuardedStructuredTapes logical) :=
  P.refresh.realizes logical physical hphysical

end StaticLoweringWithRefreshPrerequisites

/--
Successor prerequisites for the refreshed static-lowering route using the
endpoint-aware guard-slack refresh contract.

This is the concrete Milestone 1 gate to use after row composition is migrated
away from the broad logical-equivalence refresh boundary.
-/
structure StaticLoweringWithGuardSlackRefreshPrerequisites
    (D : Description) : Type where
  wellFormed : D.WellFormed
  rows : SupportsReadWriteRows3 D
  refresh : GuardSlackRefreshNormalizer

namespace StaticLoweringWithGuardSlackRefreshPrerequisites

theorem refreshSubroutineReady
    {D : Description}
    (P : StaticLoweringWithGuardSlackRefreshPrerequisites D) :
    P.refresh.machine.SubroutineReady :=
  P.refresh.subroutineReady

theorem refreshRealizes
    {D : Description}
    (P : StaticLoweringWithGuardSlackRefreshPrerequisites D)
    (primitives : List PhysicalPrimitive)
    (source target : List (Tape Bool)) (physical : Tape Bool)
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpoint primitives source target
        physical) :
    P.refresh.machine.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) :=
  P.refresh.realizes primitives source target physical hendpoint

theorem refreshRealizesEndpointEquiv
    {D : Description}
    (P : StaticLoweringWithGuardSlackRefreshPrerequisites D)
    {primitives : List PhysicalPrimitive}
    {source target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      PhysicalPrimitiveSequenceGuardSlackEndpointEquiv primitives source
        target physical) :
    P.refresh.machine.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) :=
  P.refresh.realizesEndpointEquiv hendpoint

end StaticLoweringWithGuardSlackRefreshPrerequisites

/--
Milestone 1 narrowed prerequisite bundle for the structured-singleton refresh
route.

This keeps the reusable trace/static APIs away from the broader arbitrary
guard-slack endpoint contract when the only remaining concrete refresh
obligation is the row-produced, segment-wise singleton shape.
-/
structure StaticLoweringWithStructuredSingletonRefreshPrerequisites
    (D : Description) : Type where
  wellFormed : D.WellFormed
  rows : SupportsReadWriteRows3 D
  refresh : MachineDescription
  refreshContract : StructuredSingletonGuardSlackRefreshContract refresh

namespace StaticLoweringWithStructuredSingletonRefreshPrerequisites

theorem refreshSubroutineReady
    {D : Description}
    (P : StaticLoweringWithStructuredSingletonRefreshPrerequisites D) :
    P.refresh.SubroutineReady :=
  P.refreshContract.subroutineReady

theorem refreshRealizes
    {D : Description}
    (P : StaticLoweringWithStructuredSingletonRefreshPrerequisites D)
    {target : List (Tape Bool)} {physical : Tape Bool}
    (hendpoint :
      StructuredSingletonGuardSlackEndpointShape target physical) :
    P.refresh.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes target) :=
  P.refreshContract.realizes hendpoint

end StaticLoweringWithStructuredSingletonRefreshPrerequisites

theorem StaticLoweredDescriptionWithRefresh.wellFormed
    {D : Description}
    (L : StaticLoweredDescriptionWithRefresh D) :
    L.machine.WellFormed :=
  L.stepLowering.wellFormed

/--
Run-level composition theorem for a future static dispatcher.

Once a concrete one-tape dispatcher satisfies
{name}`StaticStepLoweringWithRefresh`, this theorem lifts its one-step contract
to the executable structured bounded runner.
-/
theorem StaticStepLoweringWithRefresh.simulates_runConfig
    {D : Description} {M : MachineDescription} {stateMap : Nat -> Nat}
    (hM : StaticStepLoweringWithRefresh D M stateMap)
    (hD : D.WellFormed) :
    forall (n : Nat) (c : Configuration),
      c.state < D.stateCount ->
        c.tapes.length = D.tapeCount ->
          RunsFromStateTapeEquiv M
            (stateMap c.state)
            (stateMap (D.runConfig n c).state)
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes (D.runConfig n c).tapes) := by
  intro n
  induction n with
  | zero =>
      intro c _hstate _htapes
      exact
        runsFromStateTapeEquiv_refl M
          (stateMap c.state)
          (encodedGuardedStructuredTapes c.tapes)
  | succ n ih =>
      intro c hstate htapes
      cases hstep : D.stepConfig c with
      | none =>
          have hrun : D.runConfig (n + 1) c = c := by
            simp [Description.runConfig, hstep]
          rw [hrun]
          exact
            runsFromStateTapeEquiv_refl M
              (stateMap c.state)
              (encodedGuardedStructuredTapes c.tapes)
      | some next =>
          have hfirstBase :=
            hM.realizes c hstate htapes
          have hfirst :
              RunsFromStateTapeEquiv M
                (stateMap c.state)
                (stateMap next.state)
                (encodedGuardedStructuredTapes c.tapes)
                (encodedGuardedStructuredTapes next.tapes) := by
            simpa [oneStepOrSelf, hstep] using hfirstBase
          have hnextState : next.state < D.stateCount :=
            Description.stepConfig_state_bound hD hstep
          have hnextTapes : next.tapes.length = D.tapeCount :=
            Description.stepConfig_tape_count hstep
          have htail :=
            ih next hnextState hnextTapes
          have hrun :
              D.runConfig (n + 1) c = D.runConfig n next := by
            simp [Description.runConfig, hstep]
          rw [hrun]
          exact
            runsFromStateTapeEquiv_trans hfirst htail

theorem StaticStepLoweringWithRefresh.simulates_initial_runConfig
    {D : Description} {M : MachineDescription} {stateMap : Nat -> Nat}
    (hM : StaticStepLoweringWithRefresh D M stateMap)
    (hD : D.WellFormed)
    (n : Nat) (inputs : List (Word Bool)) :
    RunsFromStateTapeEquiv M
      (stateMap D.start)
      (stateMap (D.runConfig n (D.initial inputs)).state)
      (encodedGuardedStructuredTapes (D.initial inputs).tapes)
      (encodedGuardedStructuredTapes
        (D.runConfig n (D.initial inputs)).tapes) := by
  simpa [Description.initial] using
    hM.simulates_runConfig hD n (D.initial inputs)
      hD.right.right.left
      (description_initial_tapes_length D inputs)

theorem StaticStepLoweringWithRefresh.simulates_initial_haltsFromConfig
    {D : Description} {M : MachineDescription} {stateMap : Nat -> Nat}
    (hM : StaticStepLoweringWithRefresh D M stateMap)
    (hD : D.WellFormed)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        RunsFromStateTapeEquiv M
          (stateMap D.start)
          (stateMap D.halt)
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) := by
  rcases hhalts with ⟨n, hhalt⟩
  have hsim :=
    hM.simulates_initial_runConfig hD n inputs
  have hhaltState :
      (D.runConfig n (D.initial inputs)).state = D.halt :=
    hhalt
  exact
    ⟨n, hhalt, by
      simpa [Description.HaltsIn, hhaltState] using hsim⟩

theorem StaticStepLoweringWithRefresh.simulates_initial_haltsFromTapeEquiv
    {D : Description} {M : MachineDescription} {stateMap : Nat -> Nat}
    (hM : StaticStepLoweringWithRefresh D M stateMap)
    (hD : D.WellFormed)
    (hstart : M.start = stateMap D.start)
    (hhaltMap : stateMap D.halt = M.halt)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        M.HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) := by
  rcases hM.simulates_initial_haltsFromConfig
      hD hhalts with
    ⟨n, hhalt, hrun⟩
  exact
    ⟨n, hhalt,
      hrun.toHaltsFromTapeEquiv hstart hhaltMap⟩

theorem StaticLoweredDescriptionWithRefresh.simulates_initial_runConfig
    {D : Description}
    (L : StaticLoweredDescriptionWithRefresh D)
    (hD : D.WellFormed)
    (n : Nat) (inputs : List (Word Bool)) :
    RunsFromStateTapeEquiv L.machine
      (L.stateMap D.start)
      (L.stateMap (D.runConfig n (D.initial inputs)).state)
      (encodedGuardedStructuredTapes (D.initial inputs).tapes)
      (encodedGuardedStructuredTapes
        (D.runConfig n (D.initial inputs)).tapes) :=
  L.stepLowering.simulates_initial_runConfig hD n inputs

theorem StaticLoweredDescriptionWithRefresh.simulates_initial_haltsFromConfig
    {D : Description}
    (L : StaticLoweredDescriptionWithRefresh D)
    (hD : D.WellFormed)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        L.machine.HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) :=
  L.stepLowering.simulates_initial_haltsFromTapeEquiv
    hD L.start_eq L.halt_eq hhalts

theorem StaticLoweredDescriptionWithRefresh.simulates_initial_haltsWithTapes
    {D : Description}
    (L : StaticLoweredDescriptionWithRefresh D)
    (hD : D.WellFormed)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      D.runConfig n (D.initial inputs) =
          { state := D.halt, tapes := tapes } ∧
        L.machine.HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes tapes) := by
  rcases hhalts with ⟨n, hrun⟩
  have hhalt : D.HaltsIn n (D.initial inputs) := by
    change (D.runConfig n (D.initial inputs)).state = D.halt
    rw [hrun]
  have hsim :=
    L.stepLowering.simulates_initial_runConfig hD n inputs
  have hhalting :
      L.machine.HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes (D.initial inputs).tapes)
        (encodedGuardedStructuredTapes
          (D.runConfig n (D.initial inputs)).tapes) := by
    have hrunState :
        (D.runConfig n (D.initial inputs)).state = D.halt := hhalt
    have hrunToHalt :
        RunsFromStateTapeEquiv L.machine
          (L.stateMap D.start)
          (L.stateMap D.halt)
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) := by
      simpa [Description.HaltsIn, hrunState] using hsim
    exact hrunToHalt.toHaltsFromTapeEquiv L.start_eq L.halt_eq
  exact
    ⟨n, hrun, by
      have htapes :
          (D.runConfig n (D.initial inputs)).tapes = tapes :=
        congrArg Configuration.tapes hrun
      simpa [htapes] using hhalting⟩

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

theorem loweredTraceDescriptionWithGuardSlackRefresh_simulates_initial_runConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : GuardSlackRefreshContract refresh)
    (n : Nat) (inputs : List (Word Bool)) :
    (loweredTraceDescriptionWithGuardSlackRefresh D refresh n
      (D.initial inputs)).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes (D.initial inputs).tapes)
      (encodedGuardedStructuredTapes
        (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithGuardSlackRefresh_simulates_runConfig
    hD hrefresh n (D.initial inputs)
    (description_initial_tapes_length D inputs)

theorem loweredTraceDescriptionWithGuardSlackRefresh_simulates_initial_haltsWithTapes
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : GuardSlackRefreshContract refresh)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      (loweredTraceDescriptionWithGuardSlackRefresh D refresh n
        (D.initial inputs)).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes (D.initial inputs).tapes)
        (encodedGuardedStructuredTapes tapes) :=
  loweredTraceDescriptionWithGuardSlackRefresh_simulates_haltsWithTapes
    hD hrefresh hhalts
    (description_initial_tapes_length D inputs)

theorem loweredTraceDescriptionWithGuardSlackRefresh_simulates_initial_haltsFromConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : GuardSlackRefreshContract refresh)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        (loweredTraceDescriptionWithGuardSlackRefresh D refresh n
          (D.initial inputs)).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithGuardSlackRefresh_simulates_haltsFromConfig
    hD hrefresh hhalts
    (description_initial_tapes_length D inputs)

theorem loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_initial_runConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh)
    (n : Nat) (inputs : List (Word Bool)) :
    (loweredTraceDescriptionWithStructuredSingletonRefresh D refresh n
      (D.initial inputs)).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes (D.initial inputs).tapes)
      (encodedGuardedStructuredTapes
        (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_runConfig
    hD hrefresh n (D.initial inputs)
    (description_initial_tapes_length D inputs)

theorem loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_initial_haltsWithTapes
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      (loweredTraceDescriptionWithStructuredSingletonRefresh D refresh n
        (D.initial inputs)).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes (D.initial inputs).tapes)
        (encodedGuardedStructuredTapes tapes) :=
  loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_haltsWithTapes
    hD hrefresh hhalts
    (description_initial_tapes_length D inputs)

theorem loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_initial_haltsFromConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        (loweredTraceDescriptionWithStructuredSingletonRefresh D refresh n
          (D.initial inputs)).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_haltsFromConfig
    hD hrefresh hhalts
    (description_initial_tapes_length D inputs)

/-!
## Bundled refreshed route

These wrappers use the Milestone 1 prerequisite bundle, so downstream callers
cannot accidentally describe the refreshed route as concrete without supplying
a guard-refresh normalizer.
-/

def loweredTraceDescription
    (D : Description)
    (P : StaticLoweringWithRefreshPrerequisites D) :
    Nat -> Configuration -> MachineDescription :=
  loweredTraceDescriptionWithRefresh D P.refresh.machine

theorem loweredTraceDescription_subroutineReady
    {D : Description}
    (P : StaticLoweringWithRefreshPrerequisites D)
    (n : Nat) (c : Configuration) :
    (loweredTraceDescription D P n c).SubroutineReady :=
  loweredTraceDescriptionWithRefresh_subroutineReady
    P.rows P.refresh.contract n c

theorem loweredTraceDescription_simulates_runConfig
    {D : Description}
    (P : StaticLoweringWithRefreshPrerequisites D)
    (n : Nat) (c : Configuration)
    (hc : c.tapes.length = D.tapeCount) :
    (loweredTraceDescription D P n c).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes c.tapes)
      (encodedGuardedStructuredTapes (D.runConfig n c).tapes) :=
  loweredTraceDescriptionWithRefresh_simulates_runConfig
    P.rows P.refresh.contract n c hc

theorem loweredTraceDescription_simulates_initial_haltsWithTapes
    {D : Description}
    (P : StaticLoweringWithRefreshPrerequisites D)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      (loweredTraceDescription D P n (D.initial inputs)).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes (D.initial inputs).tapes)
        (encodedGuardedStructuredTapes tapes) :=
  loweredTraceDescriptionWithRefresh_simulates_initial_haltsWithTapes
    P.rows P.refresh.contract hhalts

theorem loweredTraceDescription_simulates_initial_haltsFromConfig
    {D : Description}
    (P : StaticLoweringWithRefreshPrerequisites D)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        (loweredTraceDescription D P n
          (D.initial inputs)).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithRefresh_simulates_initial_haltsFromConfig
    P.rows P.refresh.contract hhalts

def loweredTraceDescriptionGuardSlack
    (D : Description)
    (P : StaticLoweringWithGuardSlackRefreshPrerequisites D) :
    Nat -> Configuration -> MachineDescription :=
  loweredTraceDescriptionWithGuardSlackRefresh D P.refresh.machine

theorem loweredTraceDescriptionGuardSlack_subroutineReady
    {D : Description}
    (P : StaticLoweringWithGuardSlackRefreshPrerequisites D)
    (n : Nat) (c : Configuration) :
    (loweredTraceDescriptionGuardSlack D P n c).SubroutineReady :=
  loweredTraceDescriptionWithGuardSlackRefresh_subroutineReady
    P.rows P.refresh.contract n c

theorem loweredTraceDescriptionGuardSlack_simulates_runConfig
    {D : Description}
    (P : StaticLoweringWithGuardSlackRefreshPrerequisites D)
    (n : Nat) (c : Configuration)
    (hc : c.tapes.length = D.tapeCount) :
    (loweredTraceDescriptionGuardSlack D P n c).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes c.tapes)
      (encodedGuardedStructuredTapes (D.runConfig n c).tapes) :=
  loweredTraceDescriptionWithGuardSlackRefresh_simulates_runConfig
    P.rows P.refresh.contract n c hc

theorem loweredTraceDescriptionGuardSlack_simulates_initial_runConfig
    {D : Description}
    (P : StaticLoweringWithGuardSlackRefreshPrerequisites D)
    (n : Nat) (inputs : List (Word Bool)) :
    (loweredTraceDescriptionGuardSlack D P n
      (D.initial inputs)).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes (D.initial inputs).tapes)
      (encodedGuardedStructuredTapes
        (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithGuardSlackRefresh_simulates_initial_runConfig
    P.rows P.refresh.contract n inputs

theorem loweredTraceDescriptionGuardSlack_simulates_initial_haltsWithTapes
    {D : Description}
    (P : StaticLoweringWithGuardSlackRefreshPrerequisites D)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      (loweredTraceDescriptionGuardSlack D P n
        (D.initial inputs)).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes (D.initial inputs).tapes)
        (encodedGuardedStructuredTapes tapes) :=
  loweredTraceDescriptionWithGuardSlackRefresh_simulates_initial_haltsWithTapes
    P.rows P.refresh.contract hhalts

theorem loweredTraceDescriptionGuardSlack_simulates_initial_haltsFromConfig
    {D : Description}
    (P : StaticLoweringWithGuardSlackRefreshPrerequisites D)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        (loweredTraceDescriptionGuardSlack D P n
          (D.initial inputs)).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithGuardSlackRefresh_simulates_initial_haltsFromConfig
    P.rows P.refresh.contract hhalts

def loweredTraceDescriptionStructuredSingleton
    (D : Description)
    (P : StaticLoweringWithStructuredSingletonRefreshPrerequisites D) :
    Nat -> Configuration -> MachineDescription :=
  loweredTraceDescriptionWithStructuredSingletonRefresh D P.refresh

theorem loweredTraceDescriptionStructuredSingleton_subroutineReady
    {D : Description}
    (P : StaticLoweringWithStructuredSingletonRefreshPrerequisites D)
    (n : Nat) (c : Configuration) :
    (loweredTraceDescriptionStructuredSingleton D P n c).SubroutineReady :=
  loweredTraceDescriptionWithStructuredSingletonRefresh_subroutineReady
    P.rows P.refreshContract n c

theorem loweredTraceDescriptionStructuredSingleton_simulates_runConfig
    {D : Description}
    (P : StaticLoweringWithStructuredSingletonRefreshPrerequisites D)
    (n : Nat) (c : Configuration)
    (hc : c.tapes.length = D.tapeCount) :
    (loweredTraceDescriptionStructuredSingleton D P n c).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes c.tapes)
      (encodedGuardedStructuredTapes (D.runConfig n c).tapes) :=
  loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_runConfig
    P.rows P.refreshContract n c hc

theorem loweredTraceDescriptionStructuredSingleton_simulates_initial_runConfig
    {D : Description}
    (P : StaticLoweringWithStructuredSingletonRefreshPrerequisites D)
    (n : Nat) (inputs : List (Word Bool)) :
    (loweredTraceDescriptionStructuredSingleton D P n
      (D.initial inputs)).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes (D.initial inputs).tapes)
      (encodedGuardedStructuredTapes
        (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_initial_runConfig
    P.rows P.refreshContract n inputs

theorem loweredTraceDescriptionStructuredSingleton_simulates_initial_haltsWithTapes
    {D : Description}
    (P : StaticLoweringWithStructuredSingletonRefreshPrerequisites D)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      (loweredTraceDescriptionStructuredSingleton D P n
        (D.initial inputs)).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes (D.initial inputs).tapes)
        (encodedGuardedStructuredTapes tapes) :=
  loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_initial_haltsWithTapes
    P.rows P.refreshContract hhalts

theorem loweredTraceDescriptionStructuredSingleton_simulates_initial_haltsFromConfig
    {D : Description}
    (P : StaticLoweringWithStructuredSingletonRefreshPrerequisites D)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        (loweredTraceDescriptionStructuredSingleton D P n
          (D.initial inputs)).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithStructuredSingletonRefresh_simulates_initial_haltsFromConfig
    P.rows P.refreshContract hhalts

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
