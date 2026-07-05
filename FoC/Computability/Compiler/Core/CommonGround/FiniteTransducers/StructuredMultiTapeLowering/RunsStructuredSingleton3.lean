import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.Runs

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

def loweredTraceDescriptionWithStructuredSingleton3Refresh
    (D : Description) (refresh : MachineDescription) :
    Nat -> Configuration -> MachineDescription :=
  loweredTraceDescriptionWithStructuredSingletonRefresh D refresh

theorem loweredTraceDescriptionWithStructuredSingleton3Refresh_subroutineReady
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    forall (n : Nat) (c : Configuration),
      (loweredTraceDescriptionWithStructuredSingleton3Refresh
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
          simp [loweredTraceDescriptionWithStructuredSingleton3Refresh,
            loweredTraceDescriptionWithStructuredSingletonRefresh, hlookup]
          exact cursorNoopDescription_subroutineReady
      | some t =>
          have hrow :
              LowersGuardedTransitionEquiv D t
                (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
                  t refresh) :=
            hD.lookup_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
              hlookup hrefresh
          simp [loweredTraceDescriptionWithStructuredSingleton3Refresh,
            loweredTraceDescriptionWithStructuredSingletonRefresh, hlookup]
          exact
            canonicalPrimitiveSeqDescription_subroutineReady
              hrow.subroutineReady
              (ih (structuredTransitionTarget D t c))

theorem loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_computesIn
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    forall {n : Nat} {c final : Configuration},
      Description.ComputesIn D n c final ->
        c.tapes.length = D.tapeCount ->
          (loweredTraceDescriptionWithStructuredSingleton3Refresh
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
            (hD.lookup_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
              hlookup hrefresh).subroutineReady
          have htailReady :
              (loweredTraceDescriptionWithStructuredSingleton3Refresh
                D refresh n
                (structuredTransitionTarget D t c)).SubroutineReady :=
            loweredTraceDescriptionWithStructuredSingleton3Refresh_subroutineReady
              hD hrefresh n (structuredTransitionTarget D t c)
          have hrowRun :=
            (hD.lookup_realizes_structured_step_withStructuredSingleton3Refresh
              hc hlookup rfl hrefresh).right
          have htailRun :=
            ih (Description.stepConfig_tape_count hstep)
          simp [loweredTraceDescriptionWithStructuredSingleton3Refresh,
            loweredTraceDescriptionWithStructuredSingletonRefresh, hlookup]
          exact
            canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
              hrowReady htailReady hrowRun htailRun

theorem loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_runConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    forall (n : Nat) (c : Configuration),
      c.tapes.length = D.tapeCount ->
        (loweredTraceDescriptionWithStructuredSingleton3Refresh
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
          simp [loweredTraceDescriptionWithStructuredSingleton3Refresh,
            loweredTraceDescriptionWithStructuredSingletonRefresh, hlookup]
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
            (hD.lookup_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
              hlookup hrefresh).subroutineReady
          have htailReady :
              (loweredTraceDescriptionWithStructuredSingleton3Refresh
                D refresh n
                (structuredTransitionTarget D t c)).SubroutineReady :=
            loweredTraceDescriptionWithStructuredSingleton3Refresh_subroutineReady
              hD hrefresh n (structuredTransitionTarget D t c)
          have hrowRun :=
            (hD.lookup_realizes_structured_step_withStructuredSingleton3Refresh
              hc hlookup rfl hrefresh).right
          have htailRun :=
            ih (structuredTransitionTarget D t c)
              (Description.stepConfig_tape_count hstep)
          have hrun :
              D.runConfig (n + 1) c =
                D.runConfig n (structuredTransitionTarget D t c) := by
            simp [Description.runConfig, hstep]
          rw [hrun]
          simp [loweredTraceDescriptionWithStructuredSingleton3Refresh,
            loweredTraceDescriptionWithStructuredSingletonRefresh, hlookup]
          exact
            canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
              hrowReady htailReady hrowRun htailRun

theorem loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_haltsWithTapes
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {c : Configuration} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes c tapes)
    (hc : c.tapes.length = D.tapeCount) :
    exists n : Nat,
      (loweredTraceDescriptionWithStructuredSingleton3Refresh
        D refresh n c).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes tapes) := by
  rcases hhalts with ⟨n, hrun⟩
  have hsim :=
    loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_runConfig
      hD hrefresh n c hc
  have htapes :
      (D.runConfig n c).tapes = tapes :=
    congrArg Configuration.tapes hrun
  exact ⟨n, by simpa [htapes] using hsim⟩

theorem loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_haltsFromConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {c : Configuration}
    (hhalts : D.HaltsFromConfig c)
    (hc : c.tapes.length = D.tapeCount) :
    exists n : Nat,
      D.HaltsIn n c ∧
        (loweredTraceDescriptionWithStructuredSingleton3Refresh
          D refresh n c).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes c.tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n c).tapes) := by
  rcases hhalts with ⟨n, hhalt⟩
  exact
    ⟨n, hhalt,
      loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_runConfig
        hD hrefresh n c hc⟩

theorem loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_initial_runConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    (n : Nat) (inputs : List (Word Bool)) :
    (loweredTraceDescriptionWithStructuredSingleton3Refresh D refresh n
      (D.initial inputs)).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes (D.initial inputs).tapes)
      (encodedGuardedStructuredTapes
        (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_runConfig
    hD hrefresh n (D.initial inputs)
    (description_initial_tapes_length D inputs)

theorem loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_initial_haltsWithTapes
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      (loweredTraceDescriptionWithStructuredSingleton3Refresh D refresh n
        (D.initial inputs)).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes (D.initial inputs).tapes)
        (encodedGuardedStructuredTapes tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_haltsWithTapes
    hD hrefresh hhalts
    (description_initial_tapes_length D inputs)

theorem loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_initial_haltsFromConfig
    {D : Description} {refresh : MachineDescription}
    (hD : SupportsReadWriteRows3 D)
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        (loweredTraceDescriptionWithStructuredSingleton3Refresh D refresh n
          (D.initial inputs)).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_haltsFromConfig
    hD hrefresh hhalts
    (description_initial_tapes_length D inputs)

structure StaticLoweringWithStructuredSingleton3RefreshPrerequisites
    (D : Description) : Type where
  wellFormed : D.WellFormed
  rows : SupportsReadWriteRows3 D
  refresh : MachineDescription
  refreshContract : StructuredSingletonGuardSlackRefresh3Contract refresh

namespace StaticLoweringWithStructuredSingleton3RefreshPrerequisites

theorem refreshSubroutineReady
    {D : Description}
    (P : StaticLoweringWithStructuredSingleton3RefreshPrerequisites D) :
    P.refresh.SubroutineReady :=
  P.refreshContract.subroutineReady

theorem refreshRealizes
    {D : Description}
    (P : StaticLoweringWithStructuredSingleton3RefreshPrerequisites D)
    {target0 target1 target2 : Tape Bool} {physical : Tape Bool}
    (hendpoint :
      StructuredSingletonGuardSlackEndpointShape
        [target0, target1, target2] physical) :
    P.refresh.HaltsFromTapeEquiv physical
      (encodedGuardedStructuredTapes [target0, target1, target2]) :=
  P.refreshContract.realizes hendpoint

end StaticLoweringWithStructuredSingleton3RefreshPrerequisites

def loweredTraceDescriptionStructuredSingleton3
    (D : Description)
    (P : StaticLoweringWithStructuredSingleton3RefreshPrerequisites D) :
    Nat -> Configuration -> MachineDescription :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh D P.refresh

theorem loweredTraceDescriptionStructuredSingleton3_subroutineReady
    {D : Description}
    (P : StaticLoweringWithStructuredSingleton3RefreshPrerequisites D)
    (n : Nat) (c : Configuration) :
    (loweredTraceDescriptionStructuredSingleton3 D P n c).SubroutineReady :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_subroutineReady
    P.rows P.refreshContract n c

theorem loweredTraceDescriptionStructuredSingleton3_simulates_runConfig
    {D : Description}
    (P : StaticLoweringWithStructuredSingleton3RefreshPrerequisites D)
    (n : Nat) (c : Configuration)
    (hc : c.tapes.length = D.tapeCount) :
    (loweredTraceDescriptionStructuredSingleton3 D P n c).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes c.tapes)
      (encodedGuardedStructuredTapes (D.runConfig n c).tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_runConfig
    P.rows P.refreshContract n c hc

theorem loweredTraceDescriptionStructuredSingleton3_simulates_initial_runConfig
    {D : Description}
    (P : StaticLoweringWithStructuredSingleton3RefreshPrerequisites D)
    (n : Nat) (inputs : List (Word Bool)) :
    (loweredTraceDescriptionStructuredSingleton3 D P n
      (D.initial inputs)).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes (D.initial inputs).tapes)
      (encodedGuardedStructuredTapes
        (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_initial_runConfig
    P.rows P.refreshContract n inputs

theorem loweredTraceDescriptionStructuredSingleton3_simulates_initial_haltsWithTapes
    {D : Description}
    (P : StaticLoweringWithStructuredSingleton3RefreshPrerequisites D)
    {inputs : List (Word Bool)} {tapes : List (Tape Bool)}
    (hhalts : D.HaltsWithTapes (D.initial inputs) tapes) :
    exists n : Nat,
      (loweredTraceDescriptionStructuredSingleton3 D P n
        (D.initial inputs)).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes (D.initial inputs).tapes)
        (encodedGuardedStructuredTapes tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_initial_haltsWithTapes
    P.rows P.refreshContract hhalts

theorem loweredTraceDescriptionStructuredSingleton3_simulates_initial_haltsFromConfig
    {D : Description}
    (P : StaticLoweringWithStructuredSingleton3RefreshPrerequisites D)
    {inputs : List (Word Bool)}
    (hhalts : D.HaltsFromConfig (D.initial inputs)) :
    exists n : Nat,
      D.HaltsIn n (D.initial inputs) ∧
        (loweredTraceDescriptionStructuredSingleton3 D P n
          (D.initial inputs)).HaltsFromTapeEquiv
          (encodedGuardedStructuredTapes (D.initial inputs).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig n (D.initial inputs)).tapes) :=
  loweredTraceDescriptionWithStructuredSingleton3Refresh_simulates_initial_haltsFromConfig
    P.rows P.refreshContract hhalts

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
