import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh
import FoC.Computability.Compiler.Structured.Lowering.EncodedInjectivity

set_option doc.verso true

/-!
# Divergence transfer through the static lowering

The static step-lowering contract transfers structured runs to lowered runs
only forward and up to tape equivalence.  For endpoint closedness a lowered
machine must also be shown NOT to halt when its structured core diverges.
This module proves that transfer at the bundle level: if the structured run
never halts and every structured step changes either its mapped state or the
canonical guarded encoding of its tapes, then the lowered machine never
reaches its halt state.

The per-step progress hypothesis is what construction leaves must arrange (for
example by changing phase or spinning a cursor on rejected inputs); it rules
out structured stalls about which the step contract says nothing.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/--
Along a diverging structured run whose mapped states or canonical encodings
keep changing, the lowered machine visits the state images of the structured
trajectory at unboundedly late times.
-/
theorem staticLoweredDescriptionWithRefresh_visits_of_mapped_state_or_tape_progress
    {D : Description}
    (L : StaticLoweredDescriptionWithRefresh D)
    (c0 : Configuration)
    (hstateBound :
      forall k : Nat, (D.runConfig k c0).state < D.stateCount)
    (htapesLen :
      forall k : Nat, (D.runConfig k c0).tapes.length = D.tapeCount)
    (hprogress :
      forall k : Nat,
        L.stateMap (D.runConfig k c0).state ≠
            L.stateMap (D.runConfig (k + 1) c0).state ∨
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
          rcases hprogress k with hstateProgress | htapeProgress
          · apply hstateProgress
            rw [hstall]
          · apply htapeProgress
            rw [hstall]
            exact Tape.Equiv.refl _
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
              have hcfg :
                  ({ state := L.stateMap (D.runConfig k c0).state
                     tape :=
                       encodedGuardedStructuredTapes
                         (D.runConfig k c0).tapes } :
                      MachineDescription.Configuration) =
                    { state := L.stateMap next.state
                      tape := Tact } := hrun
              have hTactEq :
                  Tact =
                    encodedGuardedStructuredTapes
                      (D.runConfig k c0).tapes := by
                exact
                  (congrArg
                    MachineDescription.Configuration.tape hcfg).symm
              rcases hprogress k with hstateProgress | htapeProgress
              · apply hstateProgress
                rw [hnext]
                exact congrArg MachineDescription.Configuration.state hcfg
              · apply htapeProgress
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
Divergence transfer: a structured run that never halts and changes its mapped
state or canonical encoding on every step lowers to a run that never halts.
-/
theorem staticLoweredDescriptionWithRefresh_not_haltsFromTape_of_mapped_state_or_tape_progress
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
        L.stateMap (D.runConfig k c0).state ≠
            L.stateMap (D.runConfig (k + 1) c0).state ∨
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
      staticLoweredDescriptionWithRefresh_visits_of_mapped_state_or_tape_progress L c0
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

/--
Logical state changes suffice when the lowering's structured-state map is
injective along the run.
-/
theorem staticLoweredDescriptionWithRefresh_not_haltsFromTape_of_state_or_tape_progress
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
    (hstateMapInj :
      forall s t : Nat, s < D.stateCount -> t < D.stateCount ->
        L.stateMap s = L.stateMap t -> s = t)
    (hprogress :
      forall k : Nat,
        (D.runConfig k c0).state ≠ (D.runConfig (k + 1) c0).state ∨
          ¬ Tape.Equiv
            (encodedGuardedStructuredTapes (D.runConfig k c0).tapes)
            (encodedGuardedStructuredTapes
              (D.runConfig (k + 1) c0).tapes))
    (hneHalt :
      forall k : Nat, (D.runConfig k c0).state ≠ D.halt)
    {Tin : Tape Bool}
    (hTin : Tape.Equiv Tin (encodedGuardedStructuredTapes c0.tapes))
    (hc0state : c0.state = D.start)
    (T : Tape Bool) :
    ¬ L.machine.HaltsFromTape Tin T := by
  apply
    staticLoweredDescriptionWithRefresh_not_haltsFromTape_of_mapped_state_or_tape_progress
      L hhtf hInjHalt c0 hstateBound htapesLen ?_ hneHalt hTin hc0state T
  intro k
  rcases hprogress k with hstate | htape
  · left
    intro hmap
    apply hstate
    exact
      hstateMapInj _ _ (hstateBound k) (hstateBound (k + 1)) hmap
  · exact Or.inr htape

private theorem runConfig_tape_count_for_divergence
    {D : Description} {c : Configuration}
    (hc : c.tapes.length = D.tapeCount) :
    forall k : Nat, (D.runConfig k c).tapes.length = D.tapeCount := by
  intro k
  induction k generalizing c with
  | zero => exact hc
  | succ k ih =>
      change
        (match D.stepConfig c with
        | none => c
        | some next => D.runConfig k next).tapes.length = D.tapeCount
      cases hstep : D.stepConfig c with
      | none => exact hc
      | some next => exact ih (Description.stepConfig_tape_count hstep)

private theorem runConfig_succ_of_stepConfig_some_for_divergence
    {D : Description} {c d : Configuration} {k : Nat}
    (hstep : D.stepConfig (D.runConfig k c) = some d) :
    D.runConfig (k + 1) c = d := by
  rw [Description.runConfig_add D k 1 c]
  change
    (match D.stepConfig (D.runConfig k c) with
    | none => D.runConfig k c
    | some next => next) = d
  rw [hstep]

/-- A non-stationary structured tape action changes every tape representative. -/
theorem tapeAction_apply_ne_of_move_ne_stay
    (a : TapeAction) (T : Tape Bool)
    (hmove : a.move ≠ HeadMove.stay) :
    a.apply T ≠ T := by
  rcases a with ⟨write?, move⟩
  cases move with
  | stay => exact absurd rfl hmove
  | left =>
      cases T with
      | mk left head right =>
          cases write? <;> cases left <;>
            simp [TapeAction.apply, HeadMove.apply, Tape.move,
              Tape.moveLeft, Tape.write]
  | right =>
      cases T with
      | mk left head right =>
          cases write? <;> cases right <;>
            simp [TapeAction.apply, HeadMove.apply, Tape.move,
              Tape.moveRight, Tape.write]

/--
A three-tape step changes its configuration whenever its selected row changes
the logical state or moves at least one logical head.
-/
theorem stepConfig_state_ne_or_tapes_ne_of_state_or_action_moves
    {D : Description}
    (hcount : D.tapeCount = 3)
    (hchanges :
      forall t : Transition, t ∈ D.transitions ->
        exists a0 a1 a2 : TapeAction,
          t.actions = [a0, a1, a2] ∧
            (t.target ≠ t.source ∨
              a0.move ≠ HeadMove.stay ∨
                a1.move ≠ HeadMove.stay ∨
                a2.move ≠ HeadMove.stay))
    {c d : Configuration}
    (hstep : D.stepConfig c = some d) :
    c.state ≠ d.state ∨ c.tapes ≠ d.tapes := by
  unfold Description.stepConfig at hstep
  cases hlookup : D.lookupTransition c with
  | none => simp [hlookup] at hstep
  | some t =>
    simp only [hlookup] at hstep
    injection hstep with hd
    subst d
    change c.state ≠ t.target ∨ c.tapes ≠ D.applyActions t.actions c.tapes
    have ht : t ∈ D.transitions := Description.lookupTransition_mem hlookup
    have hmatch :
        Description.Matches c.state (D.currentReads c) t = true := by
      unfold Description.lookupTransition at hlookup
      exact List.find?_some hlookup
    have hsource : t.source = c.state := by
      have hmatch' :
          t.source = c.state ∧ t.reads = D.currentReads c := by
        simpa [Description.Matches] using hmatch
      exact hmatch'.left
    rcases hchanges t ht with
      ⟨a0, a1, a2, hshape, htarget | hmove0 | hmove1 | hmove2⟩
    · left
      rw [← hsource]
      exact Ne.symm htarget
    · right
      intro heq
      have hfirst := congrArg (fun ts => ts.getD 0 Tape.blank) heq
      simp [Description.applyActions, hshape, hcount] at hfirst
      exact tapeAction_apply_ne_of_move_ne_stay a0
        (c.tapes.getD 0 Tape.blank) hmove0 hfirst.symm
    · right
      intro heq
      have hsecond := congrArg (fun ts => ts.getD 1 Tape.blank) heq
      simp [Description.applyActions, hshape, hcount] at hsecond
      exact tapeAction_apply_ne_of_move_ne_stay a1
        (c.tapes.getD 1 Tape.blank) hmove1 hsecond.symm
    · right
      intro heq
      have hthird := congrArg (fun ts => ts.getD 2 Tape.blank) heq
      simp [Description.applyActions, hshape, hcount] at hthird
      exact tapeAction_apply_ne_of_move_ne_stay a2
        (c.tapes.getD 2 Tape.blank) hmove2 hthird.symm

/-- Three-tape lowering preserves divergence justified by state or tape progress. -/
theorem lowerStructured3Description_not_halts_of_state_or_tape_progress
    {D : Description}
    (hDwf : D.WellFormed)
    (hDhtf : D.HaltTransitionFree)
    (hrows : SupportsReadWriteRows3 D)
    (c : Configuration)
    (hcState : c.state = D.start)
    (hcTapes : c.tapes.length = D.tapeCount)
    (hdefined : forall k : Nat, D.stepConfig (D.runConfig k c) ≠ none)
    (hneHalt : forall k : Nat, (D.runConfig k c).state ≠ D.halt)
    (hconfigProgress :
      forall {a b : Configuration},
        D.stepConfig a = some b ->
          a.state ≠ b.state ∨ a.tapes ≠ b.tapes)
    (T : Tape Bool) :
    ¬ (lowerStructured3Description D).HaltsFromTape
      (encodedGuardedStructuredTapes c.tapes) T := by
  let L := lowerStructured3StaticDescription D hDwf hDhtf hrows
  have hLhtf : L.machine.HaltTransitionFree := by
    change (lowerStructured3Description D).HaltTransitionFree
    exact (lowerStructured3Description_subroutineReady hDwf hrows).right
  have hStateMapInj :
      forall s t : Nat, s < D.stateCount -> t < D.stateCount ->
        L.stateMap s = L.stateMap t -> s = t := by
    intro s t _hs _ht hst
    simpa [L, lowerStructured3StaticDescription,
      StaticDispatcherReaderAssembly.StaticLoweredDescription,
      StaticDispatcherState.ready] using hst
  have hInjHalt :
      forall s : Nat, s < D.stateCount ->
        L.stateMap s = L.machine.halt -> s = D.halt := by
    intro s hs hsh
    apply hStateMapInj s D.halt hs hDwf.right.right.right.left
    exact hsh.trans L.halt_eq.symm
  have hcBound : c.state < D.stateCount := by
    rw [hcState]
    exact hDwf.right.right.left
  have hprogress :
      forall k : Nat,
        (D.runConfig k c).state ≠ (D.runConfig (k + 1) c).state ∨
          ¬ Tape.Equiv
            (encodedGuardedStructuredTapes (D.runConfig k c).tapes)
            (encodedGuardedStructuredTapes
              (D.runConfig (k + 1) c).tapes) := by
    intro k
    cases hstep : D.stepConfig (D.runConfig k c) with
    | none => exact False.elim (hdefined k hstep)
    | some d =>
        rcases hconfigProgress hstep with hstate | htapes
        · left
          rw [runConfig_succ_of_stepConfig_some_for_divergence hstep]
          exact hstate
        · right
          refine
            encodedGuardedStructuredTapes_not_equiv_of_ne_of_length_three
              ?_ ?_ ?_
          · simpa [hrows.tapeCount_eq] using
              runConfig_tape_count_for_divergence hcTapes k
          · simpa [hrows.tapeCount_eq] using
              runConfig_tape_count_for_divergence hcTapes (k + 1)
          · rw [runConfig_succ_of_stepConfig_some_for_divergence hstep]
            exact htapes
  have hnot :=
    staticLoweredDescriptionWithRefresh_not_haltsFromTape_of_state_or_tape_progress
      L hLhtf hInjHalt c
      (fun k => Description.runConfig_state_bound hDwf hcBound)
      (runConfig_tape_count_for_divergence hcTapes)
      hStateMapInj hprogress hneHalt
      (Tape.Equiv.refl (encodedGuardedStructuredTapes c.tapes))
      hcState T
  change ¬ L.machine.HaltsFromTape
    (encodedGuardedStructuredTapes c.tapes) T
  exact hnot

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
