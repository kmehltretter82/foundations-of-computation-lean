import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh

set_option doc.verso true

/-!
# Divergence transfer through the static lowering

The static step-lowering contract transfers structured runs to lowered runs
only forward and up to tape equivalence.  For endpoint closedness a lowered
machine must also be shown NOT to halt when its structured core diverges.
This module proves that transfer at the bundle level: if the structured run
never halts and every structured step changes the canonical guarded encoding
of its tapes, then the lowered machine never reaches its halt state.

The per-step encoding-change hypothesis is what construction leaves must
arrange (for example by spinning a cursor on rejected inputs); it rules out
structured stalls about which the step contract says nothing.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
Along a diverging structured run whose canonical encodings keep changing, the
lowered machine visits the state images of the structured trajectory at
unboundedly late times.
-/
theorem staticLoweredDescriptionWithRefresh_visits_of_progress
    {D : Description}
    (L : StaticLoweredDescriptionWithRefresh D)
    (c0 : Configuration)
    (hstateBound :
      forall k : Nat, (D.runConfig k c0).state < D.stateCount)
    (htapesLen :
      forall k : Nat, (D.runConfig k c0).tapes.length = D.tapeCount)
    (hprogress :
      forall k : Nat,
        ¬ Tape.Equiv
          (encodedGuardedStructuredTapes (D.runConfig k c0).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig (k + 1) c0).tapes))
    {Tin : Tape Bool}
    (hTin :
      Tape.Equiv Tin (encodedGuardedStructuredTapes c0.tapes))
    (hc0state : c0.state = D.start) :
    forall k : Nat,
      exists N : Nat,
        k ≤ N ∧
          (L.machine.runConfig N
              { state := L.machine.start, tape := Tin }).state =
            L.stateMap (D.runConfig k c0).state ∧
          Tape.Equiv
            (L.machine.runConfig N
                { state := L.machine.start, tape := Tin }).tape
            (encodedGuardedStructuredTapes
              (D.runConfig k c0).tapes) := by
  intro k
  induction k with
  | zero =>
      refine ⟨0, Nat.le_refl 0, ?_, ?_⟩
      · show L.machine.start = L.stateMap (D.runConfig 0 c0).state
        rw [show D.runConfig 0 c0 = c0 from rfl, hc0state]
        exact L.start_eq
      · show Tape.Equiv Tin
          (encodedGuardedStructuredTapes (D.runConfig 0 c0).tapes)
        exact hTin
  | succ k ih =>
      rcases ih with ⟨N, hkN, hstateN, htapeN⟩
      have hsplit :
          D.runConfig (k + 1) c0 =
            D.runConfig 1 (D.runConfig k c0) :=
        Description.runConfig_add D k 1 c0
      cases hstep : D.stepConfig (D.runConfig k c0) with
      | none =>
          exfalso
          have hstall :
              D.runConfig (k + 1) c0 = D.runConfig k c0 := by
            rw [hsplit]
            show
              (match D.stepConfig (D.runConfig k c0) with
              | none => D.runConfig k c0
              | some next => D.runConfig 0 next) =
                D.runConfig k c0
            rw [hstep]
          exact
            hprogress k
              (by
                rw [hstall]
                exact
                  Tape.Equiv.refl
                    (encodedGuardedStructuredTapes
                      (D.runConfig k c0).tapes))
      | some next =>
          have hnext :
              D.runConfig (k + 1) c0 = next := by
            rw [hsplit]
            show
              (match D.stepConfig (D.runConfig k c0) with
              | none => D.runConfig k c0
              | some next => D.runConfig 0 next) = next
            rw [hstep]
            rfl
          have honeStep :
              oneStepOrSelf D (D.runConfig k c0) = next :=
            oneStepOrSelf_of_stepConfig_some hstep
          rcases
              L.stepLowering.realizes (D.runConfig k c0)
                (hstateBound k) (htapesLen k) with
            ⟨n, Tact, hrun, hTact⟩
          rw [honeStep] at hrun hTact
          have hbridge :=
            MachineDescription.runConfig_equiv L.machine n
              (c :=
                { state := L.stateMap (D.runConfig k c0).state
                  tape :=
                    encodedGuardedStructuredTapes
                      (D.runConfig k c0).tapes })
              (d :=
                L.machine.runConfig N
                  { state := L.machine.start, tape := Tin })
              hstateN.symm
              (Tape.Equiv.symm htapeN)
          have hcombined :
              L.machine.runConfig (N + n)
                  { state := L.machine.start, tape := Tin } =
                L.machine.runConfig n
                  (L.machine.runConfig N
                    { state := L.machine.start, tape := Tin }) :=
            MachineDescription.runConfig_add L.machine N n
              { state := L.machine.start, tape := Tin }
          have hstateFinal :
              (L.machine.runConfig (N + n)
                  { state := L.machine.start, tape := Tin }).state =
                L.stateMap next.state := by
            rw [hcombined, ← hbridge.left, hrun]
          have htapeFinal :
              Tape.Equiv
                (L.machine.runConfig (N + n)
                    { state := L.machine.start, tape := Tin }).tape
                (encodedGuardedStructuredTapes next.tapes) := by
            rw [hcombined]
            refine
              Tape.Equiv.trans
                (Tape.Equiv.symm ?_)
                (Tape.Equiv.trans
                  (show Tape.Equiv
                      (L.machine.runConfig n
                        { state :=
                            L.stateMap (D.runConfig k c0).state
                          tape :=
                            encodedGuardedStructuredTapes
                              (D.runConfig k c0).tapes }).tape
                      Tact by
                    rw [hrun]
                    exact Tape.Equiv.refl Tact)
                  hTact)

            exact hbridge.right
          have hpos : 1 ≤ n := by
            rcases Nat.eq_zero_or_pos n with hn0 | hposn
            · exfalso
              subst hn0
              have hTactEq :
                  Tact =
                    encodedGuardedStructuredTapes
                      (D.runConfig k c0).tapes := by
                have hcfg :
                    ({ state := L.stateMap (D.runConfig k c0).state
                       tape :=
                         encodedGuardedStructuredTapes
                           (D.runConfig k c0).tapes } :
                        MachineDescription.Configuration) =
                      { state := L.stateMap next.state
                        tape := Tact } := hrun
                exact
                  (congrArg
                    MachineDescription.Configuration.tape hcfg).symm
              apply hprogress k
              rw [hnext]
              rw [← hTactEq]
              exact hTact
            · exact hposn
          refine ⟨N + n, ?_, ?_, ?_⟩
          · have : k + 1 ≤ N + 1 := Nat.succ_le_succ hkN
            exact Nat.le_trans this (Nat.add_le_add_left hpos N)
          · rw [hnext]
            exact hstateFinal
          · rw [hnext]
            exact htapeFinal

/--
Divergence transfer: a structured run that never halts and changes its
canonical encoding on every step lowers to a machine run that never halts.
-/
theorem staticLoweredDescriptionWithRefresh_not_haltsFromTape_of_diverges
    {D : Description}
    (L : StaticLoweredDescriptionWithRefresh D)
    (hhtf : L.machine.HaltTransitionFree)
    (hInjHalt :
      forall s : Nat, s < D.stateCount ->
        L.stateMap s = L.machine.halt -> s = D.halt)
    (c0 : Configuration)
    (hstateBound :
      forall k : Nat, (D.runConfig k c0).state < D.stateCount)
    (htapesLen :
      forall k : Nat, (D.runConfig k c0).tapes.length = D.tapeCount)
    (hprogress :
      forall k : Nat,
        ¬ Tape.Equiv
          (encodedGuardedStructuredTapes (D.runConfig k c0).tapes)
          (encodedGuardedStructuredTapes
            (D.runConfig (k + 1) c0).tapes))
    (hneHalt :
      forall k : Nat, (D.runConfig k c0).state ≠ D.halt)
    {Tin : Tape Bool}
    (hTin :
      Tape.Equiv Tin (encodedGuardedStructuredTapes c0.tapes))
    (hc0state : c0.state = D.start)
    (T : Tape Bool) :
    ¬ L.machine.HaltsFromTape Tin T := by
  intro hhalt
  rcases hhalt with ⟨m, hmState, hmTape⟩
  rcases
      staticLoweredDescriptionWithRefresh_visits_of_progress L c0
        hstateBound htapesLen hprogress hTin hc0state m with
    ⟨N, hmN, hstateN, _htapeN⟩
  have hcfg :
      L.machine.runConfig m
          { state := L.machine.start, tape := Tin } =
        { state := L.machine.halt, tape := T } := by
    cases hrc :
        L.machine.runConfig m
          { state := L.machine.start, tape := Tin } with
    | mk st tp =>
        have h1 : st = L.machine.halt := by
          simpa [hrc] using hmState
        have h2 : tp = T := by
          simpa [hrc] using hmTape
        rw [h1, h2]
  have hpersist :
      L.machine.runConfig N
          { state := L.machine.start, tape := Tin } =
        { state := L.machine.halt, tape := T } := by
    have hsplit :
        L.machine.runConfig (m + (N - m))
            { state := L.machine.start, tape := Tin } =
          L.machine.runConfig (N - m)
            (L.machine.runConfig m
              { state := L.machine.start, tape := Tin }) :=
      MachineDescription.runConfig_add L.machine m (N - m)
        { state := L.machine.start, tape := Tin }
    rw [Nat.add_sub_cancel' hmN] at hsplit
    rw [hsplit, hcfg]
    exact
      MachineDescription.runConfig_halt hhtf T (N - m)
  have hhaltMap :
      L.stateMap (D.runConfig m c0).state = L.machine.halt := by
    rw [← hstateN, hpersist]
  exact
    hneHalt m (hInjHalt (D.runConfig m c0).state (hstateBound m) hhaltMap)

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
