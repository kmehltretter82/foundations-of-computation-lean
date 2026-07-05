import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.DispatcherAssembly.Determinism

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace StaticDispatcherReaderAssembly

def tableMachine (stateCount start halt : Nat)
    (transitions : List TransitionDescription) : MachineDescription where
  stateCount := stateCount
  start := start
  halt := halt
  transitions := transitions

theorem tableMachine_transitionFreeAt_of_sourcesNe
    {stateCount start halt state : Nat}
    {transitions : List TransitionDescription}
    (hsource : TransitionSourcesNe state transitions) :
    (tableMachine stateCount start halt transitions).TransitionFreeAt
      state := by
  intro t ht
  exact hsource t ht

theorem tableMachine_stepConfig_eq
    (M : MachineDescription) (stateCount start halt : Nat)
    (c : MachineDescription.Configuration) :
    (tableMachine stateCount start halt M.transitions).stepConfig c =
      M.stepConfig c := by
  simp [tableMachine, MachineDescription.stepConfig,
    MachineDescription.lookupTransition]

theorem tableMachine_runConfig_eq
    (M : MachineDescription) (stateCount start halt n : Nat)
    (c : MachineDescription.Configuration) :
    (tableMachine stateCount start halt M.transitions).runConfig n c =
      M.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      simp [MachineDescription.runConfig,
        tableMachine_stepConfig_eq M stateCount start halt c]
      cases hstep : M.stepConfig c with
      | none =>
          rfl
      | some next =>
          exact ih next

theorem runsFromStateTapeEquiv_tableMachine_of_machine
    {M : MachineDescription} {stateCount start halt : Nat}
    {sourceState targetState : Nat} {Tin Tout : Tape Bool}
    (hrun : RunsFromStateTapeEquiv M sourceState targetState Tin Tout) :
    RunsFromStateTapeEquiv
      (tableMachine stateCount start halt M.transitions)
      sourceState targetState Tin Tout := by
  rcases hrun with ⟨n, actual, hrun, hequiv⟩
  exact
    ⟨n, actual, by
      rw [tableMachine_runConfig_eq M stateCount start halt n]
      exact hrun,
      hequiv⟩

theorem lookupTransition_match
    {D : MachineDescription} {source : Nat} {read : Option Bool}
    {t : TransitionDescription}
    (h : D.lookupTransition source read = some t) :
    t.source = source ∧ t.read = read := by
  unfold MachineDescription.lookupTransition at h
  have hpred :
      MachineDescription.Matches source read t = true :=
    List.find?_some h
  simpa [MachineDescription.Matches] using hpred

theorem lookupTransition_sameAction_of_subset_deterministic
    {small big : MachineDescription}
    (hsubset :
      forall t : TransitionDescription,
        t ∈ small.transitions -> t ∈ big.transitions)
    (hdet : big.Deterministic)
    {source : Nat} {read : Option Bool} {t : TransitionDescription}
    (hlookup : small.lookupTransition source read = some t) :
    exists u : TransitionDescription,
      big.lookupTransition source read = some u ∧
        TransitionDescription.SameAction t u := by
  have htmem : t ∈ small.transitions :=
    MachineDescription.lookupTransition_mem hlookup
  have htmemBig : t ∈ big.transitions :=
    hsubset t htmem
  have htmatch := lookupTransition_match hlookup
  have htmatchBool :
      MachineDescription.Matches source read t = true := by
    simp [MachineDescription.Matches, htmatch.left, htmatch.right]
  cases hbig : big.lookupTransition source read with
  | none =>
      unfold MachineDescription.lookupTransition at hbig
      have hnone :=
        List.find?_eq_none.mp hbig t htmemBig
      rw [htmatchBool] at hnone
      contradiction
  | some u =>
      have humem : u ∈ big.transitions :=
        MachineDescription.lookupTransition_mem hbig
      have humatch := lookupTransition_match hbig
      have hkey : TransitionDescription.SameKey t u := by
        exact
          ⟨htmatch.left.trans humatch.left.symm,
            htmatch.right.trans humatch.right.symm⟩
      exact ⟨u, rfl, hdet t u htmemBig humem hkey⟩

theorem stepConfig_eq_some_of_subset_deterministic
    {small big : MachineDescription}
    (hsubset :
      forall t : TransitionDescription,
        t ∈ small.transitions -> t ∈ big.transitions)
    (hdet : big.Deterministic)
    {c next : MachineDescription.Configuration}
    (hstep : small.stepConfig c = some next) :
    big.stepConfig c = some next := by
  unfold MachineDescription.stepConfig at hstep ⊢
  cases hlookup : small.lookupTransition c.state (Tape.read c.tape) with
  | none =>
      rw [hlookup] at hstep
      cases hstep
  | some t =>
      rw [hlookup] at hstep
      rcases
          lookupTransition_sameAction_of_subset_deterministic
            hsubset hdet hlookup with
        ⟨u, hbig, haction⟩
      rw [hbig]
      rcases haction with ⟨hwrite, hmove, htarget⟩
      cases hstep
      simp [hwrite, hmove, htarget]

theorem runConfig_eq_of_subset_deterministic_of_steps
    {small big : MachineDescription}
    (hsubset :
      forall t : TransitionDescription,
        t ∈ small.transitions -> t ∈ big.transitions)
    (hdet : big.Deterministic)
    {n : Nat} {c : MachineDescription.Configuration}
    (hsteps :
      forall k : Nat, k < n ->
        exists next : MachineDescription.Configuration,
          small.stepConfig (small.runConfig k c) = some next) :
    big.runConfig n c = small.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      rcases hsteps 0 (by simp) with ⟨next, hstepSmall⟩
      have hstepSmall0 : small.stepConfig c = some next := by
        simpa [MachineDescription.runConfig] using hstepSmall
      have hstepBig0 :=
        stepConfig_eq_some_of_subset_deterministic
          hsubset hdet hstepSmall0
      have htail :
          big.runConfig n next = small.runConfig n next := by
        apply ih
        intro k hk
        have hsucc : k + 1 < n + 1 := Nat.succ_lt_succ hk
        rcases hsteps (k + 1) hsucc with ⟨next', hstep'⟩
        have hrunSucc :
            small.runConfig (k + 1) c =
              small.runConfig k next := by
          simp [MachineDescription.runConfig, hstepSmall0]
        exact ⟨next', by simpa [hrunSucc] using hstep'⟩
      simpa [MachineDescription.runConfig, hstepSmall0, hstepBig0] using
        htail

theorem runsFromStateTapeEquiv_of_subset_deterministic_of_run
    {small big : MachineDescription}
    (hsubset :
      forall t : TransitionDescription,
        t ∈ small.transitions -> t ∈ big.transitions)
    (hdet : big.Deterministic)
    {sourceState targetState n : Nat} {Tin Tout actual : Tape Bool}
    (hrun :
      small.runConfig n { state := sourceState, tape := Tin } =
        { state := targetState, tape := actual })
    (hequiv : Tape.Equiv actual Tout)
    (hsteps :
      forall k : Nat, k < n ->
        exists next : MachineDescription.Configuration,
          small.stepConfig
            (small.runConfig k { state := sourceState, tape := Tin }) =
              some next) :
    RunsFromStateTapeEquiv big sourceState targetState Tin Tout := by
  exact
    ⟨n, actual, by
      rw [runConfig_eq_of_subset_deterministic_of_steps
        hsubset hdet hsteps]
      exact hrun,
      hequiv⟩

theorem tape_moveLeft_moveRight_equiv_self
    (T : Tape Bool) :
    Tape.Equiv
      (Tape.move Direction.left (Tape.move Direction.right T)) T := by
  cases T with
  | mk left head right =>
      simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight]
      cases right <;> simp [Tape.dropTrailingNone]

theorem blankHeadBounceJumpDescription_runConfig_two_fromBlankHead
    {stateCount source scratch target : Nat}
    {T : Tape Bool}
    (hsourceScratch : source ≠ scratch)
    (hread : Tape.read T = none) :
    (blankHeadBounceJumpDescription
        stateCount source scratch target).runConfig 2
      { state := source, tape := T } =
      { state := target,
        tape := Tape.move Direction.left (Tape.move Direction.right T) } := by
  cases T with
  | mk left head right =>
      simp [Tape.read] at hread
      cases hread
      cases right with
      | nil =>
          simp [MachineDescription.runConfig,
            MachineDescription.stepConfig,
            blankHeadBounceJumpDescription_lookup_source,
            blankHeadBounceJumpDescription_lookup_scratch hsourceScratch,
            Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
            Tape.write]
      | cons rightHead rightTail =>
          cases rightHead <;>
            simp [MachineDescription.runConfig,
              MachineDescription.stepConfig,
              blankHeadBounceJumpDescription_lookup_source,
              blankHeadBounceJumpDescription_lookup_scratch hsourceScratch,
              Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
              Tape.write]

theorem blankHeadBounceJumpDescription_runConfig_state_lt_bound_before_two
    {stateCount source scratch target bound : Nat}
    {T : Tape Bool}
    (hsource : source < bound)
    (hscratch : scratch < bound)
    (hread : Tape.read T = none) :
    forall k : Nat,
      k < 2 ->
        ((blankHeadBounceJumpDescription
            stateCount source scratch target).runConfig k
          { state := source, tape := T }).state < bound := by
  intro k hk
  cases k with
  | zero =>
      simpa [MachineDescription.runConfig] using hsource
  | succ k =>
      cases k with
      | zero =>
          have hstep :
              (blankHeadBounceJumpDescription
                  stateCount source scratch target).stepConfig
                { state := source, tape := T } =
                some
                  { state := scratch,
                    tape :=
                      Tape.move Direction.right (Tape.write none T) } := by
            simp [MachineDescription.stepConfig,
              blankHeadBounceJumpDescription_lookup_source, hread]
          simpa [MachineDescription.runConfig, hstep] using hscratch
      | succ k =>
          lia

theorem runConfig_transitionFreeAt
    {D : MachineDescription} {state : Nat}
    (hfree : D.TransitionFreeAt state)
    (T : Tape Bool) (n : Nat) :
    D.runConfig n { state := state, tape := T } =
      { state := state, tape := T } := by
  have hstep :
      D.stepConfig { state := state, tape := T } = none := by
    simp [MachineDescription.stepConfig,
      MachineDescription.lookupTransition_state_none hfree]
  exact MachineDescription.runConfig_of_stepConfig_none hstep n

theorem firstReaches_transitionFreeAt_of_runConfig_eq
    {D : MachineDescription} {target n : Nat}
    {c : MachineDescription.Configuration} {T : Tape Bool}
    (hfree : D.TransitionFreeAt target)
    (hrun : D.runConfig n c = { state := target, tape := T }) :
    exists m : Nat,
      m ≤ n ∧
        D.runConfig m c = { state := target, tape := T } ∧
        forall k : Nat,
          k < m -> (D.runConfig k c).state ≠ target := by
  induction n generalizing c with
  | zero =>
      exists 0
      simp [hrun]
  | succ n ih =>
      by_cases hcTarget : c.state = target
      · have hc :
            c = { state := target, tape := c.tape } := by
          cases c with
          | mk state tape =>
              simp at hcTarget ⊢
              exact hcTarget
        have hstable :
            D.runConfig (n + 1) c = c := by
          rw [hc]
          exact runConfig_transitionFreeAt hfree c.tape (n + 1)
        have hcFinal : c = { state := target, tape := T } := by
          rw [← hstable]
          exact hrun
        exists 0
        constructor
        · lia
        constructor
        · simp [hcFinal, MachineDescription.runConfig]
        · intro k hk
          lia
      · cases hstep : D.stepConfig c with
        | none =>
            have hsame : D.runConfig (n + 1) c = c := by
              simp [MachineDescription.runConfig, hstep]
            have hstate : c.state = target := by
              have hfinal : c = { state := target, tape := T } := by
                rw [← hsame]
                exact hrun
              simpa using
                congrArg (fun d : MachineDescription.Configuration =>
                  d.state) hfinal
            exact False.elim (hcTarget hstate)
        | some next =>
            have hnext :
                D.runConfig n next = { state := target, tape := T } := by
              simpa [MachineDescription.runConfig, hstep] using hrun
            rcases ih hnext with ⟨m, hmle, hmrun, hmfirst⟩
            exists m + 1
            constructor
            · lia
            constructor
            · simp [MachineDescription.runConfig, hstep, hmrun]
            · intro k hk
              cases k with
              | zero =>
                  simpa [MachineDescription.runConfig] using hcTarget
              | succ j =>
                  have hj : j < m := by
                    lia
                  simpa [MachineDescription.runConfig, hstep] using
                    hmfirst j hj

theorem stepConfig_exists_before_firstReaches
    {D : MachineDescription} {target n : Nat}
    {c : MachineDescription.Configuration} {T : Tape Bool}
    (hrun : D.runConfig n c = { state := target, tape := T })
    (hfirst :
      forall k : Nat,
        k < n -> (D.runConfig k c).state ≠ target) :
    forall k : Nat,
      k < n ->
        exists next : MachineDescription.Configuration,
          D.stepConfig (D.runConfig k c) = some next := by
  intro k hk
  cases hstep : D.stepConfig (D.runConfig k c) with
  | some next =>
      exact ⟨next, rfl⟩
  | none =>
      have hkLe : k ≤ n := Nat.le_of_lt hk
      let ck := D.runConfig k c
      have htail :
          D.runConfig (n - k) ck = ck := by
        exact MachineDescription.runConfig_of_stepConfig_none hstep (n - k)
      have hrunToCk : D.runConfig n c = ck := by
        rw [← Nat.add_sub_of_le hkLe, MachineDescription.runConfig_add]
        exact htail
      have hckTarget : ck.state = target := by
        have hfinalEq :
            { state := target, tape := T } = ck :=
          hrun.symm.trans hrunToCk
        exact
          (congrArg (fun d : MachineDescription.Configuration => d.state)
            hfinalEq).symm
      exact False.elim ((hfirst k hk) (by simpa [ck] using hckTarget))

theorem runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
    {small big : MachineDescription}
    (hsubset :
      forall t : TransitionDescription,
        t ∈ small.transitions -> t ∈ big.transitions)
    (hdet : big.Deterministic)
    {sourceState targetState : Nat} {Tin Tout : Tape Bool}
    (hfree : small.TransitionFreeAt targetState)
    (hrun :
      RunsFromStateTapeEquiv small sourceState targetState Tin Tout) :
    RunsFromStateTapeEquiv big sourceState targetState Tin Tout := by
  rcases hrun with ⟨n, actual, hrun, hequiv⟩
  rcases
      firstReaches_transitionFreeAt_of_runConfig_eq
        hfree hrun with
    ⟨m, _hmle, hmrun, hmfirst⟩
  exact
    runsFromStateTapeEquiv_of_subset_deterministic_of_run
      hsubset hdet hmrun hequiv
      (stepConfig_exists_before_firstReaches hmrun hmfirst)

theorem runConfig_state_ne_transitionFreeAt_of_final_state_ne
    {D : MachineDescription} {blocked finalState n k : Nat}
    {c : MachineDescription.Configuration} {T : Tape Bool}
    (hfree : D.TransitionFreeAt blocked)
    (hrun : D.runConfig n c = { state := finalState, tape := T })
    (hfinal : finalState ≠ blocked)
    (hk : k ≤ n) :
    (D.runConfig k c).state ≠ blocked := by
  intro hblocked
  let ck := D.runConfig k c
  have hck :
      ck = { state := blocked, tape := ck.tape } := by
    cases hconfig : ck with
    | mk state tape =>
        have hstate : state = blocked := by
          simpa [ck, hconfig] using hblocked
        simp [hstate]
  have htail :
      D.runConfig (n - k) ck = ck := by
    rw [hck]
    exact runConfig_transitionFreeAt hfree ck.tape (n - k)
  have hrunToCk : D.runConfig n c = ck := by
    rw [← Nat.add_sub_of_le hk, MachineDescription.runConfig_add]
    exact htail
  have hfinalBlocked : finalState = blocked := by
    have hfinalEqCk :
        { state := finalState, tape := T } = ck :=
      hrun.symm.trans hrunToCk
    have hstates :
        finalState = ck.state :=
      congrArg (fun d : MachineDescription.Configuration => d.state)
        hfinalEqCk
    have hckState : ck.state = blocked := by
      simpa [ck] using hblocked
    exact hstates.trans hckState
  exact hfinal hfinalBlocked

theorem BranchingHeadCellReturn.targetForRead_injective :
    Function.Injective BranchingHeadCellReturn.targetForRead := by
  intro a b h
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some bit =>
          cases bit <;>
            simp [BranchingHeadCellReturn.targetForRead,
              BranchingHeadCellReturn.noneExit,
              BranchingHeadCellReturn.falseExit,
              BranchingHeadCellReturn.trueExit,
              BranchingHeadCellReturn.noneStart,
              BranchingHeadCellReturn.falseStart,
              BranchingHeadCellReturn.trueStart] at h
  | some abit =>
      cases abit <;>
        cases b with
        | none =>
            simp [BranchingHeadCellReturn.targetForRead,
              BranchingHeadCellReturn.noneExit,
              BranchingHeadCellReturn.falseExit,
              BranchingHeadCellReturn.trueExit,
              BranchingHeadCellReturn.noneStart,
              BranchingHeadCellReturn.falseStart,
              BranchingHeadCellReturn.trueStart] at h
        | some bbit =>
            cases bbit <;>
              simp [BranchingHeadCellReturn.targetForRead,
                BranchingHeadCellReturn.falseExit,
                BranchingHeadCellReturn.trueExit,
                BranchingHeadCellReturn.falseStart,
                BranchingHeadCellReturn.trueStart] at h ⊢

theorem branchingSeparatorReadHeadCellTarget_injective :
    Function.Injective branchingSeparatorReadHeadCellTarget := by
  intro a b h
  exact BranchingHeadCellReturn.targetForRead_injective (by
    unfold branchingSeparatorReadHeadCellTarget at h
    lia)

theorem branchingTape0ReadHeadCellAndReturnToSeparatorTarget_injective :
    Function.Injective branchingTape0ReadHeadCellAndReturnToSeparatorTarget := by
  simpa [branchingTape0ReadHeadCellAndReturnToSeparatorTarget] using
    branchingSeparatorReadHeadCellTarget_injective

theorem branchingTape1ReadHeadCellAndReturnToSeparatorTarget_injective :
    Function.Injective branchingTape1ReadHeadCellAndReturnToSeparatorTarget := by
  intro a b h
  exact branchingSeparatorReadHeadCellTarget_injective (by
    unfold branchingTape1ReadHeadCellAndReturnToSeparatorTarget at h
    lia)

theorem branchingTape2ReadHeadCellAndReturnToSeparatorTarget_injective :
    Function.Injective branchingTape2ReadHeadCellAndReturnToSeparatorTarget := by
  intro a b h
  exact branchingSeparatorReadHeadCellTarget_injective (by
    unfold branchingTape2ReadHeadCellAndReturnToSeparatorTarget at h
    lia)

theorem retargetReadExitState_eq_offset_add_of_ne_targets
    {offset state : Nat} {localTarget target : Option Bool -> Nat}
    (hnone : state ≠ localTarget none)
    (hfalse : state ≠ localTarget (some false))
    (htrue : state ≠ localTarget (some true)) :
    MachineDescription.retargetReadExitState
        offset localTarget target state =
      offset + state := by
  simp [MachineDescription.retargetReadExitState,
    hnone, hfalse, htrue]

theorem offsetReadExitRetargetDescription_runConfig_state_ge_offset_before_exit
    {offset : Nat} {localTarget target : Option Bool -> Nat}
    (hbelow : forall cell : Option Bool, target cell < offset)
    {D : MachineDescription}
    (hfree :
      forall exitCell : Option Bool,
        D.TransitionFreeAt (localTarget exitCell))
    (hinj : Function.Injective localTarget)
    {observed : Option Bool} {n : Nat}
    {c : MachineDescription.Configuration} {Tout : Tape Bool}
    (hrun :
      D.runConfig n c =
        { state := localTarget observed, tape := Tout }) :
    exists m : Nat,
      m ≤ n ∧
        (MachineDescription.offsetReadExitRetargetDescription
            offset localTarget target D).runConfig m
          (MachineDescription.readExitRetargetConfiguration
            offset localTarget target c) =
          MachineDescription.readExitRetargetConfiguration
            offset localTarget target
              { state := localTarget observed, tape := Tout } ∧
        forall k : Nat,
          k < m ->
            offset ≤
              ((MachineDescription.offsetReadExitRetargetDescription
                  offset localTarget target D).runConfig k
                (MachineDescription.readExitRetargetConfiguration
                  offset localTarget target c)).state := by
  rcases
      firstReaches_transitionFreeAt_of_runConfig_eq
        (hfree observed) hrun with
    ⟨m, hmle, hmrun, hmfirst⟩
  refine ⟨m, hmle, ?_, ?_⟩
  · exact
      MachineDescription.offsetReadExitRetargetDescription_runConfig_eq
        hbelow hfree hmrun
  · intro k hk
    have hretarget :=
      MachineDescription.offsetReadExitRetargetDescription_runConfig
        (offset := offset) (localTarget := localTarget)
        (target := target) hbelow hfree k c
    rw [hretarget]
    simp only [MachineDescription.readExitRetargetConfiguration]
    have hnotExit :
        forall cell : Option Bool,
          (D.runConfig k c).state ≠ localTarget cell := by
      intro cell
      by_cases hcell : cell = observed
      · subst cell
        exact hmfirst k hk
      · exact
          runConfig_state_ne_transitionFreeAt_of_final_state_ne
            (hfree cell) hmrun
            (by
              intro heq
              exact hcell ((hinj heq).symm))
            (Nat.le_of_lt hk)
    rw [retargetReadExitState_eq_offset_add_of_ne_targets
      (hnotExit none) (hnotExit (some false)) (hnotExit (some true))]
    exact Nat.le_add_right offset (D.runConfig k c).state

theorem find?_matches_none_of_sources_below
    {bound state : Nat} {cell : Option Bool}
    {transitions : List TransitionDescription}
    (hbelow : TransitionSourcesBelow bound transitions)
    (hstate : bound ≤ state) :
    transitions.find? (MachineDescription.Matches state cell) = none := by
  rw [List.find?_eq_none]
  intro t ht hmatch
  have hmatchPair : t.source = state ∧ t.read = cell := by
    simpa [MachineDescription.Matches] using hmatch
  have hsource : t.source = state := by
    exact hmatchPair.left
  exact Nat.not_lt_of_ge hstate (by simpa [hsource] using hbelow t ht)

theorem find?_matches_none_of_sources_atLeast
    {bound state : Nat} {cell : Option Bool}
    {transitions : List TransitionDescription}
    (hatLeast : TransitionSourcesAtLeast bound transitions)
    (hstate : state < bound) :
    transitions.find? (MachineDescription.Matches state cell) = none := by
  rw [List.find?_eq_none]
  intro t ht hmatch
  have hmatchPair : t.source = state ∧ t.read = cell := by
    simpa [MachineDescription.Matches] using hmatch
  have hsource : t.source = state := by
    exact hmatchPair.left
  exact Nat.not_le_of_gt hstate (by simpa [hsource] using hatLeast t ht)

theorem find?_append_right_of_left_sources_below
    {bound state : Nat} {cell : Option Bool}
    {left right : List TransitionDescription}
    (hleft : TransitionSourcesBelow bound left)
    (hstate : bound ≤ state) :
    (left ++ right).find? (MachineDescription.Matches state cell) =
      right.find? (MachineDescription.Matches state cell) := by
  rw [List.find?_append,
    find?_matches_none_of_sources_below hleft hstate]
  simp

theorem find?_append_left_of_right_sources_atLeast
    {bound state : Nat} {cell : Option Bool}
    {left right : List TransitionDescription}
    (hright : TransitionSourcesAtLeast bound right)
    (hstate : state < bound) :
    (left ++ right).find? (MachineDescription.Matches state cell) =
      left.find? (MachineDescription.Matches state cell) := by
  rw [List.find?_append,
    find?_matches_none_of_sources_atLeast hright hstate]
  cases left.find? (MachineDescription.Matches state cell) <;> simp

theorem tableMachine_stepConfig_append_right_of_left_sources_below
    {stateCount start halt bound : Nat}
    {left right : List TransitionDescription}
    {c : MachineDescription.Configuration}
    (hleft : TransitionSourcesBelow bound left)
    (hstate : bound ≤ c.state) :
    (tableMachine stateCount start halt (left ++ right)).stepConfig c =
      (tableMachine stateCount start halt right).stepConfig c := by
  simp [tableMachine, MachineDescription.stepConfig,
    MachineDescription.lookupTransition,
    find?_append_right_of_left_sources_below hleft hstate]

theorem tableMachine_stepConfig_append_left_of_right_sources_atLeast
    {stateCount start halt bound : Nat}
    {left right : List TransitionDescription}
    {c : MachineDescription.Configuration}
    (hright : TransitionSourcesAtLeast bound right)
    (hstate : c.state < bound) :
    (tableMachine stateCount start halt (left ++ right)).stepConfig c =
      (tableMachine stateCount start halt left).stepConfig c := by
  simp [tableMachine, MachineDescription.stepConfig,
    MachineDescription.lookupTransition,
    find?_append_left_of_right_sources_atLeast hright hstate]

theorem tableMachine_runConfig_append_right_of_left_sources_below
    {stateCount start halt bound n : Nat}
    {left right : List TransitionDescription}
    {c : MachineDescription.Configuration}
    (hleft : TransitionSourcesBelow bound left)
    (hstates :
      forall k : Nat, k < n ->
        bound ≤
          ((tableMachine stateCount start halt right).runConfig k c).state) :
    (tableMachine stateCount start halt (left ++ right)).runConfig n c =
      (tableMachine stateCount start halt right).runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have hstate : bound ≤ c.state := by
        simpa [MachineDescription.runConfig] using hstates 0 (Nat.succ_pos n)
      have hstep :=
        tableMachine_stepConfig_append_right_of_left_sources_below
          (stateCount := stateCount) (start := start) (halt := halt)
          (bound := bound) (left := left) (right := right)
          (c := c) hleft hstate
      cases hrightStep :
          (tableMachine stateCount start halt right).stepConfig c with
      | none =>
          have hwholeStep :
              (tableMachine stateCount start halt (left ++ right)).stepConfig c =
                none := by
            simpa [hstep] using hrightStep
          simp [MachineDescription.runConfig, hwholeStep, hrightStep]
      | some next =>
          have hwholeStep :
              (tableMachine stateCount start halt (left ++ right)).stepConfig c =
                some next := by
            simpa [hstep] using hrightStep
          simp [MachineDescription.runConfig, hwholeStep, hrightStep]
          apply ih
          intro k hk
          have hk' : k + 1 < Nat.succ n := Nat.succ_lt_succ hk
          have h := hstates (k + 1) hk'
          simpa [MachineDescription.runConfig, hrightStep] using h

theorem tableMachine_runConfig_append_left_of_right_sources_atLeast
    {stateCount start halt bound n : Nat}
    {left right : List TransitionDescription}
    {c : MachineDescription.Configuration}
    (hright : TransitionSourcesAtLeast bound right)
    (hstates :
      forall k : Nat, k < n ->
        ((tableMachine stateCount start halt left).runConfig k c).state <
          bound) :
    (tableMachine stateCount start halt (left ++ right)).runConfig n c =
      (tableMachine stateCount start halt left).runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have hstate : c.state < bound := by
        simpa [MachineDescription.runConfig] using hstates 0 (Nat.succ_pos n)
      have hstep :=
        tableMachine_stepConfig_append_left_of_right_sources_atLeast
          (stateCount := stateCount) (start := start) (halt := halt)
          (bound := bound) (left := left) (right := right)
          (c := c) hright hstate
      cases hleftStep :
          (tableMachine stateCount start halt left).stepConfig c with
      | none =>
          have hwholeStep :
              (tableMachine stateCount start halt (left ++ right)).stepConfig c =
                none := by
            simpa [hstep] using hleftStep
          simp [MachineDescription.runConfig, hwholeStep, hleftStep]
      | some next =>
          have hwholeStep :
              (tableMachine stateCount start halt (left ++ right)).stepConfig c =
                some next := by
            simpa [hstep] using hleftStep
          simp [MachineDescription.runConfig, hwholeStep, hleftStep]
          apply ih
          intro k hk
          have hk' : k + 1 < Nat.succ n := Nat.succ_lt_succ hk
          have h := hstates (k + 1) hk'
          simpa [MachineDescription.runConfig, hleftStep] using h

theorem runsFromStateTapeEquiv_tableMachine_append_right_of_left_sources_below_of_run
    {stateCount start halt bound : Nat}
    {left right : List TransitionDescription}
    {sourceState targetState n : Nat}
    {Tin Tout : Tape Bool}
    {actual : Tape Bool}
    (hleft : TransitionSourcesBelow bound left)
    (hrun :
      (tableMachine stateCount start halt right).runConfig n
          { state := sourceState, tape := Tin } =
        { state := targetState, tape := actual })
    (hequiv : Tape.Equiv actual Tout)
    (hstates :
      forall k : Nat, k < n ->
        bound ≤
          ((tableMachine stateCount start halt right).runConfig k
            { state := sourceState, tape := Tin }).state) :
    RunsFromStateTapeEquiv
      (tableMachine stateCount start halt (left ++ right))
      sourceState targetState Tin Tout := by
  exact
    ⟨n, actual, by
      rw [tableMachine_runConfig_append_right_of_left_sources_below
        hleft hstates]
      exact hrun,
      hequiv⟩

theorem runsFromStateTapeEquiv_tableMachine_append_left_of_right_sources_atLeast_of_run
    {stateCount start halt bound : Nat}
    {left right : List TransitionDescription}
    {sourceState targetState n : Nat}
    {Tin Tout : Tape Bool}
    {actual : Tape Bool}
    (hright : TransitionSourcesAtLeast bound right)
    (hrun :
      (tableMachine stateCount start halt left).runConfig n
          { state := sourceState, tape := Tin } =
        { state := targetState, tape := actual })
    (hequiv : Tape.Equiv actual Tout)
    (hstates :
      forall k : Nat, k < n ->
        ((tableMachine stateCount start halt left).runConfig k
          { state := sourceState, tape := Tin }).state < bound) :
    RunsFromStateTapeEquiv
      (tableMachine stateCount start halt (left ++ right))
      sourceState targetState Tin Tout := by
  exact
    ⟨n, actual, by
      rw [tableMachine_runConfig_append_left_of_right_sources_atLeast
        hright hstates]
      exact hrun,
      hequiv⟩

theorem guardedDropOne_exists_of_length_three
    {logical : List (Tape Bool)} (hlength : logical.length = 3) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      (guardLogicalTapes logical).drop 1 = T :: rest := by
  cases logical with
  | nil =>
      simp at hlength
  | cons _ rest =>
      cases rest with
      | nil =>
          simp at hlength
      | cons T rest =>
          exact
            ⟨guardLogicalTape T, guardLogicalTapes rest,
              by simp [guardLogicalTapes]⟩

theorem guardedDropTwo_exists_of_length_three
    {logical : List (Tape Bool)} (hlength : logical.length = 3) :
    exists T : Tape Bool, exists rest : List (Tape Bool),
      (guardLogicalTapes logical).drop 2 = T :: rest := by
  cases logical with
  | nil =>
      simp at hlength
  | cons _ rest =>
      cases rest with
      | nil =>
          simp at hlength
      | cons _ rest =>
          cases rest with
          | nil =>
              simp at hlength
          | cons T rest =>
              exact
                ⟨guardLogicalTape T, guardLogicalTapes rest,
                  by simp [guardLogicalTapes]⟩

theorem guardedHasAtLeastThreeTapes_of_length_three
    {logical : List (Tape Bool)} (hlength : logical.length = 3) :
    HasAtLeastThreeTapes (guardLogicalTapes logical) := by
  cases logical with
  | nil =>
      simp at hlength
  | cons T rest =>
      cases rest with
      | nil =>
          simp at hlength
      | cons U rest =>
          cases rest with
          | nil =>
              simp at hlength
          | cons V rest =>
              exact
                ⟨guardLogicalTape T, guardLogicalTape U,
                  guardLogicalTape V, guardLogicalTapes rest,
                  by simp [guardLogicalTapes]⟩

theorem guardedAtExistingTapeSeparator_zero_of_length_three
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    AtExistingTapeSeparator (guardLogicalTapes logical) 0
      (encodedGuardedStructuredTapes logical) := by
  cases logical with
  | nil =>
      simp at hlength
  | cons T rest =>
      exact
        ⟨by
          simpa [encodedGuardedStructuredTapes] using
            atTapeSeparator_zero_self (guardLogicalTapes (T :: rest)),
          guardLogicalTape T, guardLogicalTapes rest,
          by simp [guardLogicalTapes]⟩

theorem readOptionValues_mem (read : Option Bool) :
    read ∈ readOptionValues := by
  cases read with
  | none =>
      simp [readOptionValues]
  | some bit =>
      cases bit <;> simp [readOptionValues]

theorem readyJumpTape0ReaderTransitions_subset_threeHeadReaderTransitions
    (D : Description) {state : Nat}
    (hstate : state ∈ activeStateValues D) :
    forall t : TransitionDescription,
      t ∈ readyJumpTape0ReaderTransitions D state ->
        t ∈ threeHeadReaderTransitions D := by
  intro t ht
  simp [threeHeadReaderTransitions, readyJumpTape0ReaderAllTransitions]
  exact Or.inl ⟨state, hstate, ht⟩

theorem afterRead0JumpTape1ReaderTransitions_subset_threeHeadReaderTransitions
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state ∈ activeStateValues D) :
    forall t : TransitionDescription,
      t ∈ afterRead0JumpTape1ReaderTransitions D state read0 ->
        t ∈ threeHeadReaderTransitions D := by
  intro t ht
  simp [threeHeadReaderTransitions,
    afterRead0JumpTape1ReaderAllTransitions]
  exact Or.inr
    (Or.inl ⟨read0, readOptionValues_mem read0,
      state, hstate, ht⟩)

theorem afterRead1JumpTape2ReaderTransitions_subset_threeHeadReaderTransitions
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state ∈ activeStateValues D) :
    forall t : TransitionDescription,
      t ∈ afterRead1JumpTape2ReaderTransitions D state read0 read1 ->
        t ∈ threeHeadReaderTransitions D := by
  intro t ht
  simp [threeHeadReaderTransitions,
    afterRead1JumpTape2ReaderAllTransitions]
  exact Or.inr
    (Or.inr ⟨read0, readOptionValues_mem read0,
      read1, readOptionValues_mem read1,
      state, hstate, ht⟩)

theorem readyJumpTape0ReaderTransitions_sources_ne_afterRead0
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionSourcesNe (StaticDispatcherState.afterRead0 D state read0)
      (readyJumpTape0ReaderTransitions D state) := by
  intro t ht
  rcases readyJumpTape0ReaderTransitions_source_cases D ht with
    hsource | hcases
  · rw [hsource]
    exact
      Nat.ne_of_lt
        (Nat.lt_of_lt_of_le
          (StaticDispatcherState.ready_lt_afterRead0Base D hstate)
          (StaticDispatcherState.afterRead0Base_le_afterRead0
            D state read0))
  · rcases hcases with hscratch | hreader
    · rw [hscratch]
      have htargetLt :
          StaticDispatcherState.afterRead0 D state read0 <
            StaticDispatcherState.readerStateLimit D :=
        Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead0_lt_afterRead1Base
            D read0 hstate)
          (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
      have hscratchGe :
          StaticDispatcherState.readerStateLimit D ≤
            readyJumpScratch D state := by
        unfold readyJumpScratch readyJumpScratchBase
        exact Nat.le_add_right _ _
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hscratchGe)).symm
    · have htargetLt :
          StaticDispatcherState.afterRead0 D state read0 <
            StaticDispatcherState.readerStateLimit D :=
        Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead0_lt_afterRead1Base
            D read0 hstate)
          (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
      have hreaderGe :
          StaticDispatcherState.readerStateLimit D ≤ t.source :=
        Nat.le_trans
          (readerStateLimit_le_tape0ReaderOffset D state)
          hreader.left
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hreaderGe)).symm

theorem afterRead0JumpTape1ReaderTransitions_sources_ne_afterRead1
    (D : Description) {state : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.afterRead1 D state read0 read1)
      (afterRead0JumpTape1ReaderTransitions D state read0) := by
  intro t ht
  rcases afterRead0JumpTape1ReaderTransitions_source_cases D read0 ht with
    hsource | hcases
  · rw [hsource]
    exact
      Nat.ne_of_lt
        (Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead0_lt_afterRead1Base
            D read0 hstate)
          (StaticDispatcherState.afterRead1Base_le_afterRead1
            D state read0 read1))
  · rcases hcases with hscratch | hreader
    · rw [hscratch]
      have htargetLt :
          StaticDispatcherState.afterRead1 D state read0 read1 <
            StaticDispatcherState.readerStateLimit D :=
        StaticDispatcherState.afterRead1_lt_readerStateLimit
          D read0 read1 hstate
      have hscratchGe :
          StaticDispatcherState.readerStateLimit D ≤
            afterRead0JumpScratch D state read0 := by
        unfold afterRead0JumpScratch afterRead0JumpScratchBase
          tape0ReaderLimit tape0ReaderBlockBase readyJumpLimit
          readyJumpScratchBase
        lia
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hscratchGe)).symm
    · have htargetLt :
          StaticDispatcherState.afterRead1 D state read0 read1 <
            StaticDispatcherState.readerStateLimit D :=
        StaticDispatcherState.afterRead1_lt_readerStateLimit
          D read0 read1 hstate
      have hreaderGe :
          StaticDispatcherState.readerStateLimit D ≤ t.source :=
        Nat.le_trans
          (readerStateLimit_le_tape1ReaderOffset D state read0)
          hreader.left
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hreaderGe)).symm

theorem afterRead1JumpTape2ReaderTransitions_sources_ne_afterRead
    (D : Description) {state : Nat}
    (read0 read1 read2 : Option Bool)
    (hstate : state < D.stateCount) :
    TransitionSourcesNe
      (StaticDispatcherState.afterRead D state
        { read0 := read0, read1 := read1, read2 := read2 })
      (afterRead1JumpTape2ReaderTransitions D state read0 read1) := by
  intro t ht
  rcases afterRead1JumpTape2ReaderTransitions_source_cases
      D read0 read1 ht with
    hsource | hcases
  · rw [hsource]
    have htargetLt :
        StaticDispatcherState.afterRead D state
            { read0 := read0, read1 := read1, read2 := read2 } <
          StaticDispatcherState.afterRead0Base D :=
      StaticDispatcherState.afterRead_lt_afterRead0Base
        D { read0 := read0, read1 := read1, read2 := read2 } hstate
    have hbaseLe :
        StaticDispatcherState.afterRead0Base D ≤
          StaticDispatcherState.afterRead1Base D := by
      unfold StaticDispatcherState.afterRead1Base
      lia
    have hsourceGe :
        StaticDispatcherState.afterRead1Base D ≤
          StaticDispatcherState.afterRead1 D state read0 read1 :=
      StaticDispatcherState.afterRead1Base_le_afterRead1
        D state read0 read1
    exact
      (Nat.ne_of_lt
        (Nat.lt_of_lt_of_le htargetLt
          (Nat.le_trans hbaseLe hsourceGe))).symm
  · rcases hcases with hscratch | hreader
    · rw [hscratch]
      have htargetLt :
          StaticDispatcherState.afterRead D state
              { read0 := read0, read1 := read1, read2 := read2 } <
            StaticDispatcherState.readerStateLimit D :=
        Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead_lt_afterRead0Base
            D { read0 := read0, read1 := read1, read2 := read2 } hstate)
          (StaticDispatcherState.afterRead0Base_le_readerStateLimit D)
      have hscratchGe :
          StaticDispatcherState.readerStateLimit D ≤
            afterRead1JumpScratch D state read0 read1 := by
        unfold afterRead1JumpScratch afterRead1JumpScratchBase
          tape1ReaderLimit tape1ReaderBlockBase afterRead0JumpLimit
          afterRead0JumpScratchBase tape0ReaderLimit
          tape0ReaderBlockBase readyJumpLimit readyJumpScratchBase
        lia
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hscratchGe)).symm
    · have htargetLt :
          StaticDispatcherState.afterRead D state
              { read0 := read0, read1 := read1, read2 := read2 } <
            StaticDispatcherState.readerStateLimit D :=
        Nat.lt_of_lt_of_le
          (StaticDispatcherState.afterRead_lt_afterRead0Base
            D { read0 := read0, read1 := read1, read2 := read2 } hstate)
          (StaticDispatcherState.afterRead0Base_le_readerStateLimit D)
      have hreaderGe :
          StaticDispatcherState.readerStateLimit D ≤ t.source :=
        Nat.le_trans
          (readerStateLimit_le_tape2ReaderOffset D state read0 read1)
          hreader.left
      exact
        (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le htargetLt hreaderGe)).symm

theorem threeHeadReaderDescription_deterministic
    (D : Description) :
    (threeHeadReaderDescription D).Deterministic := by
  simpa [threeHeadReaderDescription, MachineDescription.Deterministic] using
    threeHeadReaderTransitions_deterministic D

theorem readyJumpDescription_runsFromTapeSeparator_in_readyJumpTape0ReaderTransitions
    (D : Description) {state haltState : Nat}
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical 0 physical) :
    RunsFromStateTapeEquiv
      (tableMachine (threeHeadReaderStateLimit D)
        (StaticDispatcherState.ready state)
        haltState
        (readyJumpTape0ReaderTransitions D state))
      (StaticDispatcherState.ready state)
      (tape0ReaderStart D state)
      physical
      physical := by
  have hread : Tape.read physical = none :=
    atTapeSeparator_read hseparator
  have hreadyBelow :
      StaticDispatcherState.ready state < tape0ReaderOffset D state := by
    exact
      Nat.lt_of_lt_of_le
        (Nat.lt_trans
          (ready_lt_readyJumpScratch D hstate)
          (readyJumpScratch_lt_readyJumpLimit D hstate))
        (by
          unfold tape0ReaderOffset tape0ReaderBlockBase
          exact Nat.le_add_right _ _)
  have hscratchBelow :
      readyJumpScratch D state < tape0ReaderOffset D state := by
    exact
      Nat.lt_of_lt_of_le
        (readyJumpScratch_lt_readyJumpLimit D hstate)
        (by
          unfold tape0ReaderOffset tape0ReaderBlockBase
          exact Nat.le_add_right _ _)
  have hleftRun :
      (tableMachine (threeHeadReaderStateLimit D)
          (StaticDispatcherState.ready state)
          haltState
          (readyJumpDescription D state).transitions).runConfig 2
        { state := StaticDispatcherState.ready state,
          tape := physical } =
      { state := tape0ReaderStart D state,
        tape := Tape.move Direction.left (Tape.move Direction.right physical) } := by
    rw [tableMachine_runConfig_eq (readyJumpDescription D state)]
    simpa [readyJumpDescription] using
      blankHeadBounceJumpDescription_runConfig_two_fromBlankHead
        (stateCount := threeHeadReaderStateLimit D)
        (source := StaticDispatcherState.ready state)
        (scratch := readyJumpScratch D state)
        (target := tape0ReaderStart D state)
        (ready_ne_readyJumpScratch D hstate)
        hread
  have hleftStates :
      forall k : Nat, k < 2 ->
        ((tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.ready state)
            haltState
            (readyJumpDescription D state).transitions).runConfig k
          { state := StaticDispatcherState.ready state,
            tape := physical }).state <
          tape0ReaderOffset D state := by
    intro k hk
    rw [tableMachine_runConfig_eq (readyJumpDescription D state)]
    simpa [readyJumpDescription] using
      blankHeadBounceJumpDescription_runConfig_state_lt_bound_before_two
        (stateCount := threeHeadReaderStateLimit D)
        (source := StaticDispatcherState.ready state)
        (scratch := readyJumpScratch D state)
        (target := tape0ReaderStart D state)
        (bound := tape0ReaderOffset D state)
        hreadyBelow hscratchBelow hread k hk
  simpa [readyJumpTape0ReaderTransitions] using
    runsFromStateTapeEquiv_tableMachine_append_left_of_right_sources_atLeast_of_run
      (stateCount := threeHeadReaderStateLimit D)
      (start := StaticDispatcherState.ready state)
      (halt := haltState)
      (bound := tape0ReaderOffset D state)
      (left := (readyJumpDescription D state).transitions)
      (right := (tape0ReaderDescription D state).transitions)
      (sourceState := StaticDispatcherState.ready state)
      (targetState := tape0ReaderStart D state)
      (n := 2)
      (Tin := physical)
      (Tout := physical)
      (actual := Tape.move Direction.left (Tape.move Direction.right physical))
      (tape0ReaderDescription_sources_atLeast D state)
      hleftRun
      (tape_moveLeft_moveRight_equiv_self physical)
      hleftStates

theorem
    tape0ReaderDescription_runsFromGuardedBlockStart_in_readyJumpTape0ReaderTransitions
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 0
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.ready state)
            (StaticDispatcherState.afterRead0 D state
              (Tape.read (Description.tapeAt logical 0)))
            (readyJumpTape0ReaderTransitions D state))
          (tape0ReaderStart D state)
          (StaticDispatcherState.afterRead0 D state
            (Tape.read (Description.tapeAt logical 0)))
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  rcases
      branchingTape0ReadHeadCellAndReturnToSeparatorDescription_runsFromGuardedBlockStart
        hlength with
    ⟨separatorPhysical, hseparator,
      ⟨nBase, actual, hbaseRun, hactual⟩⟩
  rcases
      offsetReadExitRetargetDescription_runConfig_state_ge_offset_before_exit
        (offset := tape0ReaderOffset D state)
        (localTarget :=
          branchingTape0ReadHeadCellAndReturnToSeparatorTarget)
        (target := StaticDispatcherState.tape0ReaderTargets D state)
        (tape0ReaderTargets_lt_tape0ReaderOffset D hstate)
        branchingTape0ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
        branchingTape0ReadHeadCellAndReturnToSeparatorTarget_injective
        (observed := Tape.read (Description.tapeAt logical 0))
        hbaseRun with
    ⟨n, _hle, hcopyRun, hcopyStates⟩
  have hrightRun :
      (tableMachine (threeHeadReaderStateLimit D)
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.afterRead0 D state
            (Tape.read (Description.tapeAt logical 0)))
          (tape0ReaderDescription D state).transitions).runConfig n
        { state := tape0ReaderStart D state,
          tape := encodedGuardedStructuredTapes logical } =
      { state :=
          StaticDispatcherState.afterRead0 D state
            (Tape.read (Description.tapeAt logical 0)),
        tape := actual } := by
    rw [tableMachine_runConfig_eq
      (tape0ReaderDescription D state)]
    cases hread : Tape.read (Description.tapeAt logical 0) with
    | none =>
        simpa [tape0ReaderDescription, tape0ReaderStart,
          retargetedBranchingTape0ReadHeadCellAllExitsDescription,
          MachineDescription.readExitRetargetConfiguration,
          MachineDescription.retargetReadExitState,
          StaticDispatcherState.tape0ReaderTargets,
          StaticDispatcherState.tape0ReaderTarget,
          branchingTape0ReadHeadCellAndReturnToSeparatorTarget,
          branchingSeparatorReadHeadCellTarget,
          BranchingHeadCellReturn.targetForRead, hread] using hcopyRun
    | some bit =>
        cases bit with
        | false =>
            simpa [tape0ReaderDescription, tape0ReaderStart,
              retargetedBranchingTape0ReadHeadCellAllExitsDescription,
              MachineDescription.readExitRetargetConfiguration,
              MachineDescription.retargetReadExitState,
              StaticDispatcherState.tape0ReaderTargets,
              StaticDispatcherState.tape0ReaderTarget,
              branchingTape0ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopyRun
        | true =>
            simpa [tape0ReaderDescription, tape0ReaderStart,
              retargetedBranchingTape0ReadHeadCellAllExitsDescription,
              MachineDescription.readExitRetargetConfiguration,
              MachineDescription.retargetReadExitState,
              StaticDispatcherState.tape0ReaderTargets,
              StaticDispatcherState.tape0ReaderTarget,
              branchingTape0ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopyRun
  have hrightStates :
      forall k : Nat, k < n ->
        tape0ReaderOffset D state ≤
          ((tableMachine (threeHeadReaderStateLimit D)
              (StaticDispatcherState.ready state)
              (StaticDispatcherState.afterRead0 D state
                (Tape.read (Description.tapeAt logical 0)))
              (tape0ReaderDescription D state).transitions).runConfig k
            { state := tape0ReaderStart D state,
              tape := encodedGuardedStructuredTapes logical }).state := by
    intro k hk
    rw [tableMachine_runConfig_eq
      (tape0ReaderDescription D state)]
    simpa [tape0ReaderDescription, tape0ReaderStart,
      retargetedBranchingTape0ReadHeadCellAllExitsDescription,
      MachineDescription.readExitRetargetConfiguration,
      MachineDescription.retargetReadExitState] using
      hcopyStates k hk
  refine ⟨separatorPhysical, hseparator, ?_⟩
  simpa [readyJumpTape0ReaderTransitions] using
    runsFromStateTapeEquiv_tableMachine_append_right_of_left_sources_below_of_run
      (stateCount := threeHeadReaderStateLimit D)
      (start := StaticDispatcherState.ready state)
      (halt :=
        StaticDispatcherState.afterRead0 D state
          (Tape.read (Description.tapeAt logical 0)))
      (bound := tape0ReaderOffset D state)
      (left := (readyJumpDescription D state).transitions)
      (right := (tape0ReaderDescription D state).transitions)
      (sourceState := tape0ReaderStart D state)
      (targetState :=
        StaticDispatcherState.afterRead0 D state
          (Tape.read (Description.tapeAt logical 0)))
      (n := n)
      (Tin := encodedGuardedStructuredTapes logical)
      (Tout := separatorPhysical)
      (actual := actual)
      (readyJumpDescription_sources_below_tape0ReaderOffset D hstate)
      hrightRun
      hactual
      hrightStates

theorem readyJumpTape0ReaderTransitions_runsFromGuardedBlockStart
    (D : Description) {state : Nat}
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 0
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.ready state)
            (StaticDispatcherState.afterRead0 D state
              (Tape.read (Description.tapeAt logical 0)))
            (readyJumpTape0ReaderTransitions D state))
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.afterRead0 D state
            (Tape.read (Description.tapeAt logical 0)))
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  have hstart :=
    guardedAtExistingTapeSeparator_zero_of_length_three
      (logical := logical) hlength
  have hready :
      RunsFromStateTapeEquiv
        (tableMachine (threeHeadReaderStateLimit D)
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.afterRead0 D state
            (Tape.read (Description.tapeAt logical 0)))
          (readyJumpTape0ReaderTransitions D state))
        (StaticDispatcherState.ready state)
        (tape0ReaderStart D state)
        (encodedGuardedStructuredTapes logical)
        (encodedGuardedStructuredTapes logical) :=
    readyJumpDescription_runsFromTapeSeparator_in_readyJumpTape0ReaderTransitions
      (D := D) (state := state)
      (haltState :=
        StaticDispatcherState.afterRead0 D state
          (Tape.read (Description.tapeAt logical 0)))
      hstate hstart.left
  rcases
      tape0ReaderDescription_runsFromGuardedBlockStart_in_readyJumpTape0ReaderTransitions
        D hstate hlength with
    ⟨separatorPhysical, hseparator, hreader⟩
  exact
    ⟨separatorPhysical, hseparator,
      runsFromStateTapeEquiv_trans hready hreader⟩

theorem
    tape1ReaderDescription_runsFromExistingBlockStart_in_afterRead0JumpTape1ReaderTransitions
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hlength : logical.length = 3)
    (hstart :
      AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 1
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.afterRead0 D state read0)
            (StaticDispatcherState.afterRead1 D state read0
              (Tape.read (Description.tapeAt logical 1)))
            (afterRead0JumpTape1ReaderTransitions D state read0))
          (tape1ReaderStart D state read0)
          (StaticDispatcherState.afterRead1 D state read0
            (Tape.read (Description.tapeAt logical 1)))
          physical
          separatorPhysical := by
  rcases
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromBlockStart
        (logical := guardLogicalTapes logical)
        (physical := physical)
        hstart
        (guardedDropOne_exists_of_length_three hlength) with
    ⟨separatorPhysical, hseparator,
      ⟨nBase, actual, hbaseRun, hactual⟩⟩
  have hbaseRun' :
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription.runConfig
          nBase
          { state :=
              branchingTape1ReadHeadCellAndReturnToSeparatorDescription.start,
            tape := physical } =
        { state :=
            branchingTape1ReadHeadCellAndReturnToSeparatorTarget
              (Tape.read (Description.tapeAt logical 1)),
          tape := actual } := by
    simpa [tapeAt_guardLogicalTapes_read] using hbaseRun
  rcases
      offsetReadExitRetargetDescription_runConfig_state_ge_offset_before_exit
        (offset := tape1ReaderOffset D state read0)
        (localTarget :=
          branchingTape1ReadHeadCellAndReturnToSeparatorTarget)
        (target := StaticDispatcherState.tape1ReaderTargets D state read0)
        (tape1ReaderTargets_lt_tape1ReaderOffset D read0 hstate)
        branchingTape1ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
        branchingTape1ReadHeadCellAndReturnToSeparatorTarget_injective
        (observed := Tape.read (Description.tapeAt logical 1))
        hbaseRun' with
    ⟨n, _hle, hcopyRun, hcopyStates⟩
  have hrightRun :
      (tableMachine (threeHeadReaderStateLimit D)
          (StaticDispatcherState.afterRead0 D state read0)
          (StaticDispatcherState.afterRead1 D state read0
            (Tape.read (Description.tapeAt logical 1)))
          (tape1ReaderDescription D state read0).transitions).runConfig n
        { state := tape1ReaderStart D state read0,
          tape := physical } =
      { state :=
          StaticDispatcherState.afterRead1 D state read0
            (Tape.read (Description.tapeAt logical 1)),
        tape := actual } := by
    rw [tableMachine_runConfig_eq
      (tape1ReaderDescription D state read0)]
    cases hread : Tape.read (Description.tapeAt logical 1) with
    | none =>
        simpa [tape1ReaderDescription, tape1ReaderStart,
          retargetedBranchingTape1ReadHeadCellAllExitsDescription,
          MachineDescription.readExitRetargetConfiguration,
          MachineDescription.retargetReadExitState,
          StaticDispatcherState.tape1ReaderTargets,
          StaticDispatcherState.tape1ReaderTarget,
          branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
          branchingSeparatorReadHeadCellTarget,
          BranchingHeadCellReturn.targetForRead, hread] using hcopyRun
    | some bit =>
        cases bit with
        | false =>
            simpa [tape1ReaderDescription, tape1ReaderStart,
              retargetedBranchingTape1ReadHeadCellAllExitsDescription,
              MachineDescription.readExitRetargetConfiguration,
              MachineDescription.retargetReadExitState,
              StaticDispatcherState.tape1ReaderTargets,
              StaticDispatcherState.tape1ReaderTarget,
              branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopyRun
        | true =>
            simpa [tape1ReaderDescription, tape1ReaderStart,
              retargetedBranchingTape1ReadHeadCellAllExitsDescription,
              MachineDescription.readExitRetargetConfiguration,
              MachineDescription.retargetReadExitState,
              StaticDispatcherState.tape1ReaderTargets,
              StaticDispatcherState.tape1ReaderTarget,
              branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopyRun
  have hrightStates :
      forall k : Nat, k < n ->
        tape1ReaderOffset D state read0 ≤
          ((tableMachine (threeHeadReaderStateLimit D)
              (StaticDispatcherState.afterRead0 D state read0)
              (StaticDispatcherState.afterRead1 D state read0
                (Tape.read (Description.tapeAt logical 1)))
              (tape1ReaderDescription D state read0).transitions).runConfig k
            { state := tape1ReaderStart D state read0,
              tape := physical }).state := by
    intro k hk
    rw [tableMachine_runConfig_eq
      (tape1ReaderDescription D state read0)]
    simpa [tape1ReaderDescription, tape1ReaderStart,
      retargetedBranchingTape1ReadHeadCellAllExitsDescription,
      MachineDescription.readExitRetargetConfiguration,
      MachineDescription.retargetReadExitState] using
      hcopyStates k hk
  refine ⟨separatorPhysical, hseparator, ?_⟩
  simpa [afterRead0JumpTape1ReaderTransitions] using
    runsFromStateTapeEquiv_tableMachine_append_right_of_left_sources_below_of_run
      (stateCount := threeHeadReaderStateLimit D)
      (start := StaticDispatcherState.afterRead0 D state read0)
      (halt :=
        StaticDispatcherState.afterRead1 D state read0
          (Tape.read (Description.tapeAt logical 1)))
      (bound := tape1ReaderOffset D state read0)
      (left := (afterRead0JumpDescription D state read0).transitions)
      (right := (tape1ReaderDescription D state read0).transitions)
      (sourceState := tape1ReaderStart D state read0)
      (targetState :=
        StaticDispatcherState.afterRead1 D state read0
          (Tape.read (Description.tapeAt logical 1)))
      (n := n)
      (Tin := physical)
      (Tout := separatorPhysical)
      (actual := actual)
      (afterRead0JumpDescription_sources_below_tape1ReaderOffset
        D read0 hstate)
      hrightRun
      hactual
      hrightStates

theorem afterRead0JumpDescription_runsFromTapeSeparator_in_afterRead0JumpTape1ReaderTransitions
    (D : Description) {state haltState : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical tapeIndex physical) :
    RunsFromStateTapeEquiv
      (tableMachine (threeHeadReaderStateLimit D)
        (StaticDispatcherState.afterRead0 D state read0)
        haltState
        (afterRead0JumpTape1ReaderTransitions D state read0))
      (StaticDispatcherState.afterRead0 D state read0)
      (tape1ReaderStart D state read0)
      physical
      physical := by
  have hread : Tape.read physical = none :=
    atTapeSeparator_read hseparator
  have hsourceBelow :
      StaticDispatcherState.afterRead0 D state read0 <
        tape1ReaderOffset D state read0 := by
    have hlow :=
      Nat.lt_of_lt_of_le
        (StaticDispatcherState.afterRead0_lt_afterRead1Base
          D read0 hstate)
        (StaticDispatcherState.afterRead1Base_le_readerStateLimit D)
    exact Nat.lt_of_lt_of_le hlow
      (readerStateLimit_le_tape1ReaderOffset D state read0)
  have hscratchBelow :
      afterRead0JumpScratch D state read0 <
        tape1ReaderOffset D state read0 := by
    have hscratch :=
      afterRead0JumpScratch_lt_afterRead0JumpLimit
        D read0 hstate
    have hbase :
        afterRead0JumpLimit D ≤ tape1ReaderOffset D state read0 := by
      unfold tape1ReaderOffset tape1ReaderBlockBase
      lia
    exact Nat.lt_of_lt_of_le hscratch hbase
  have hleftRun :
      (tableMachine (threeHeadReaderStateLimit D)
          (StaticDispatcherState.afterRead0 D state read0)
          haltState
          (afterRead0JumpDescription D state read0).transitions).runConfig 2
        { state := StaticDispatcherState.afterRead0 D state read0,
          tape := physical } =
      { state := tape1ReaderStart D state read0,
        tape := Tape.move Direction.left (Tape.move Direction.right physical) } := by
    rw [tableMachine_runConfig_eq
      (afterRead0JumpDescription D state read0)]
    simpa [afterRead0JumpDescription] using
      blankHeadBounceJumpDescription_runConfig_two_fromBlankHead
        (stateCount := threeHeadReaderStateLimit D)
        (source := StaticDispatcherState.afterRead0 D state read0)
        (scratch := afterRead0JumpScratch D state read0)
        (target := tape1ReaderStart D state read0)
        (afterRead0_ne_afterRead0JumpScratch D read0 hstate)
        hread
  have hleftStates :
      forall k : Nat, k < 2 ->
        ((tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.afterRead0 D state read0)
            haltState
            (afterRead0JumpDescription D state read0).transitions).runConfig k
          { state := StaticDispatcherState.afterRead0 D state read0,
            tape := physical }).state <
          tape1ReaderOffset D state read0 := by
    intro k hk
    rw [tableMachine_runConfig_eq
      (afterRead0JumpDescription D state read0)]
    simpa [afterRead0JumpDescription] using
      blankHeadBounceJumpDescription_runConfig_state_lt_bound_before_two
        (stateCount := threeHeadReaderStateLimit D)
        (source := StaticDispatcherState.afterRead0 D state read0)
        (scratch := afterRead0JumpScratch D state read0)
        (target := tape1ReaderStart D state read0)
        (bound := tape1ReaderOffset D state read0)
        hsourceBelow hscratchBelow hread k hk
  simpa [afterRead0JumpTape1ReaderTransitions] using
    runsFromStateTapeEquiv_tableMachine_append_left_of_right_sources_atLeast_of_run
      (stateCount := threeHeadReaderStateLimit D)
      (start := StaticDispatcherState.afterRead0 D state read0)
      (halt := haltState)
      (bound := tape1ReaderOffset D state read0)
      (left := (afterRead0JumpDescription D state read0).transitions)
      (right := (tape1ReaderDescription D state read0).transitions)
      (sourceState := StaticDispatcherState.afterRead0 D state read0)
      (targetState := tape1ReaderStart D state read0)
      (n := 2)
      (Tin := physical)
      (Tout := physical)
      (actual := Tape.move Direction.left (Tape.move Direction.right physical))
      (tape1ReaderDescription_sources_atLeast D state read0)
      hleftRun
      (tape_moveLeft_moveRight_equiv_self physical)
      hleftStates

theorem afterRead0JumpTape1ReaderTransitions_runsFromExistingBlockStart
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hlength : logical.length = 3)
    (hstart :
      AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 1
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.afterRead0 D state read0)
            (StaticDispatcherState.afterRead1 D state read0
              (Tape.read (Description.tapeAt logical 1)))
            (afterRead0JumpTape1ReaderTransitions D state read0))
          (StaticDispatcherState.afterRead0 D state read0)
          (StaticDispatcherState.afterRead1 D state read0
            (Tape.read (Description.tapeAt logical 1)))
          physical
          separatorPhysical := by
  have hjump :
      RunsFromStateTapeEquiv
        (tableMachine (threeHeadReaderStateLimit D)
          (StaticDispatcherState.afterRead0 D state read0)
          (StaticDispatcherState.afterRead1 D state read0
            (Tape.read (Description.tapeAt logical 1)))
          (afterRead0JumpTape1ReaderTransitions D state read0))
        (StaticDispatcherState.afterRead0 D state read0)
        (tape1ReaderStart D state read0)
        physical
        physical :=
    afterRead0JumpDescription_runsFromTapeSeparator_in_afterRead0JumpTape1ReaderTransitions
      (D := D) (state := state)
      (haltState :=
        StaticDispatcherState.afterRead1 D state read0
          (Tape.read (Description.tapeAt logical 1)))
      read0 hstate hstart.left
  rcases
      tape1ReaderDescription_runsFromExistingBlockStart_in_afterRead0JumpTape1ReaderTransitions
        D read0 hstate hlength hstart with
    ⟨separatorPhysical, hseparator, hreader⟩
  exact
    ⟨separatorPhysical, hseparator,
      runsFromStateTapeEquiv_trans hjump hreader⟩

theorem tape1ReaderDescription_runsFromExistingBlockStart
    (D : Description) {state : Nat} (read0 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hlength : logical.length = 3)
    (hstart :
      AtExistingTapeSeparator (guardLogicalTapes logical) 0 physical) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 1
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tape1ReaderDescription D state read0)
          (tape1ReaderStart D state read0)
          (StaticDispatcherState.afterRead1 D state read0
            (Tape.read (Description.tapeAt logical 1)))
          physical
          separatorPhysical := by
  rcases
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromBlockStart
        (logical := guardLogicalTapes logical)
        (physical := physical)
        hstart
        (guardedDropOne_exists_of_length_three hlength) with
    ⟨separatorPhysical, hseparator, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetReadExitRetargetDescription
      (offset := tape1ReaderOffset D state read0)
      (localTarget :=
        branchingTape1ReadHeadCellAndReturnToSeparatorTarget)
      (target := StaticDispatcherState.tape1ReaderTargets D state read0)
      (tape1ReaderTargets_lt_tape1ReaderOffset D read0 hstate)
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
      (observed := Tape.read (Description.tapeAt logical 1))
      (by
        simpa [tapeAt_guardLogicalTapes_read] using hrun)
  exact
    ⟨separatorPhysical, hseparator, by
      cases hread : Tape.read (Description.tapeAt logical 1) with
      | none =>
          simpa
            [tape1ReaderDescription, tape1ReaderStart,
              retargetedBranchingTape1ReadHeadCellAllExitsDescription,
              MachineDescription.offsetReadExitRetargetDescription,
              MachineDescription.retargetReadExitState,
              StaticDispatcherState.tape1ReaderTargets,
              StaticDispatcherState.tape1ReaderTarget,
              branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopy
      | some bit =>
          cases bit with
          | false =>
              simpa
                [tape1ReaderDescription, tape1ReaderStart,
                  retargetedBranchingTape1ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  StaticDispatcherState.tape1ReaderTargets,
                  StaticDispatcherState.tape1ReaderTarget,
                  branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using hcopy
          | true =>
              simpa
                [tape1ReaderDescription, tape1ReaderStart,
                  retargetedBranchingTape1ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  StaticDispatcherState.tape1ReaderTargets,
                  StaticDispatcherState.tape1ReaderTarget,
                  branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using hcopy⟩

theorem branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromSeparator
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hstart : AtExistingTapeSeparator logical tapeIndex physical)
    (hexists :
      exists T : Tape Bool, exists rest : List (Tape Bool),
        logical.drop (tapeIndex + 1) = T :: rest) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator logical (tapeIndex + 1)
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          branchingTape1ReadHeadCellAndReturnToSeparatorDescription
          branchingTape1ReadHeadCellAndReturnToSeparatorDescription.start
          (branchingTape1ReadHeadCellAndReturnToSeparatorTarget
            (Tape.read (Description.tapeAt logical (tapeIndex + 1))))
          physical
          separatorPhysical := by
  rcases
      (cursorSeekNextSeparatorDescription_contract tapeIndex).realizes
        logical physical hstart with
    ⟨mid, hseek, hseparator⟩
  let hmid :
      AtExistingTapeSeparator logical (tapeIndex + 1) mid :=
    ⟨hseparator, hexists⟩
  rcases
      branchingSeparatorReadHeadCellDescription_runsFromSeparator hmid with
    ⟨separatorPhysical, hsep, hread⟩
  rcases hread with ⟨nRead, actual, hreadRun, hactual⟩
  have hreadReach :
      exists nRead : Nat,
        branchingSeparatorReadHeadCellDescription.runConfig nRead
            { state := branchingSeparatorReadHeadCellDescription.start
              tape :=
                Tape.move Direction.left
                  (Tape.move Direction.right mid) } =
          { state :=
              branchingSeparatorReadHeadCellTarget
                (Tape.read (Description.tapeAt logical
                  (tapeIndex + 1)))
            tape := actual } := by
    refine ⟨nRead, ?_⟩
    rw [atExistingTapeSeparator_moveLeft_moveRight hmid]
    exact hreadRun
  rcases
      canonicalPrimitiveSeqDescription_reaches_right_state
        (A := seekTape1Description)
        (B := branchingSeparatorReadHeadCellDescription)
        seekTape1Description_contract.subroutineReady
        branchingSeparatorReadHeadCellDescription_subroutineReady
        (by simpa [seekTape1Description] using hseek)
        hreadReach with
    ⟨n, hrun⟩
  exact
    ⟨separatorPhysical, ⟨hsep, hexists⟩,
      ⟨n, actual, by
        simpa [branchingTape1ReadHeadCellAndReturnToSeparatorDescription,
          branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
          seekTape1Description] using hrun,
        hactual⟩⟩

theorem tape2ReaderDescription_runsFromExistingTape1Separator
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hlength : logical.length = 3)
    (hstart :
      AtExistingTapeSeparator (guardLogicalTapes logical) 1 physical) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tape2ReaderDescription D state read0 read1)
          (tape2ReaderStart D state read0 read1)
          (StaticDispatcherState.afterRead D state
            { read0 := read0,
              read1 := read1,
              read2 := Tape.read (Description.tapeAt logical 2) })
          physical
          separatorPhysical := by
  rcases
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromSeparator
        (logical := guardLogicalTapes logical)
        (tapeIndex := 1)
        (physical := physical)
        hstart
        (guardedDropTwo_exists_of_length_three hlength) with
    ⟨separatorPhysical, hseparator, hrun⟩
  have hcopy :=
    runsFromStateTapeEquiv_offsetReadExitRetargetDescription
      (offset := tape2ReaderOffset D state read0 read1)
      (localTarget :=
        branchingTape1ReadHeadCellAndReturnToSeparatorTarget)
      (target :=
        StaticDispatcherState.tape2ReaderTargets D state read0 read1)
      (tape2ReaderTargets_lt_tape2ReaderOffset D read0 read1 hstate)
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
      (observed := Tape.read (Description.tapeAt logical 2))
      (by
        simpa [tapeAt_guardLogicalTapes_read] using hrun)
  exact
    ⟨separatorPhysical, hseparator, by
      cases hread : Tape.read (Description.tapeAt logical 2) with
      | none =>
          simpa
            [tape2ReaderDescription, tape2ReaderStart,
              retargetedBranchingTape1ReadHeadCellAllExitsDescription,
              MachineDescription.offsetReadExitRetargetDescription,
              MachineDescription.retargetReadExitState,
              StaticDispatcherState.tape2ReaderTargets,
              StaticDispatcherState.tape2ReaderTarget,
              branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopy
      | some bit =>
          cases bit with
          | false =>
              simpa
                [tape2ReaderDescription, tape2ReaderStart,
                  retargetedBranchingTape1ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  StaticDispatcherState.tape2ReaderTargets,
                  StaticDispatcherState.tape2ReaderTarget,
                  branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using hcopy
          | true =>
              simpa
                [tape2ReaderDescription, tape2ReaderStart,
                  retargetedBranchingTape1ReadHeadCellAllExitsDescription,
                  MachineDescription.offsetReadExitRetargetDescription,
                  MachineDescription.retargetReadExitState,
                  StaticDispatcherState.tape2ReaderTargets,
                  StaticDispatcherState.tape2ReaderTarget,
                  branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
                  branchingSeparatorReadHeadCellTarget,
                  BranchingHeadCellReturn.targetForRead, hread] using hcopy⟩

theorem
    tape2ReaderDescription_runsFromExistingTape1Separator_in_afterRead1JumpTape2ReaderTransitions
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hlength : logical.length = 3)
    (hstart :
      AtExistingTapeSeparator (guardLogicalTapes logical) 1 physical) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.afterRead1 D state read0 read1)
            (StaticDispatcherState.afterRead D state
              { read0 := read0,
                read1 := read1,
                read2 := Tape.read (Description.tapeAt logical 2) })
            (afterRead1JumpTape2ReaderTransitions D state read0 read1))
          (tape2ReaderStart D state read0 read1)
          (StaticDispatcherState.afterRead D state
            { read0 := read0,
              read1 := read1,
              read2 := Tape.read (Description.tapeAt logical 2) })
          physical
          separatorPhysical := by
  rcases
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription_runsFromSeparator
        (logical := guardLogicalTapes logical)
        (tapeIndex := 1)
        (physical := physical)
        hstart
        (guardedDropTwo_exists_of_length_three hlength) with
    ⟨separatorPhysical, hseparator,
      ⟨nBase, actual, hbaseRun, hactual⟩⟩
  have hbaseRun' :
      branchingTape1ReadHeadCellAndReturnToSeparatorDescription.runConfig
          nBase
          { state :=
              branchingTape1ReadHeadCellAndReturnToSeparatorDescription.start,
            tape := physical } =
        { state :=
            branchingTape1ReadHeadCellAndReturnToSeparatorTarget
              (Tape.read (Description.tapeAt logical 2)),
          tape := actual } := by
    simpa [tapeAt_guardLogicalTapes_read] using hbaseRun
  rcases
      offsetReadExitRetargetDescription_runConfig_state_ge_offset_before_exit
        (offset := tape2ReaderOffset D state read0 read1)
        (localTarget :=
          branchingTape1ReadHeadCellAndReturnToSeparatorTarget)
        (target :=
          StaticDispatcherState.tape2ReaderTargets D state read0 read1)
        (tape2ReaderTargets_lt_tape2ReaderOffset
          D read0 read1 hstate)
        branchingTape1ReadHeadCellAndReturnToSeparatorDescription_transitionFreeAt
        branchingTape1ReadHeadCellAndReturnToSeparatorTarget_injective
        (observed := Tape.read (Description.tapeAt logical 2))
        hbaseRun' with
    ⟨n, _hle, hcopyRun, hcopyStates⟩
  have hrightRun :
      (tableMachine (threeHeadReaderStateLimit D)
          (StaticDispatcherState.afterRead1 D state read0 read1)
          (StaticDispatcherState.afterRead D state
            { read0 := read0,
              read1 := read1,
              read2 := Tape.read (Description.tapeAt logical 2) })
          (tape2ReaderDescription D state read0 read1).transitions).runConfig n
        { state := tape2ReaderStart D state read0 read1,
          tape := physical } =
      { state :=
          StaticDispatcherState.afterRead D state
            { read0 := read0,
              read1 := read1,
              read2 := Tape.read (Description.tapeAt logical 2) },
        tape := actual } := by
    rw [tableMachine_runConfig_eq
      (tape2ReaderDescription D state read0 read1)]
    cases hread : Tape.read (Description.tapeAt logical 2) with
    | none =>
        simpa [tape2ReaderDescription, tape2ReaderStart,
          retargetedBranchingTape1ReadHeadCellAllExitsDescription,
          MachineDescription.readExitRetargetConfiguration,
          MachineDescription.retargetReadExitState,
          StaticDispatcherState.tape2ReaderTargets,
          StaticDispatcherState.tape2ReaderTarget,
          branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
          branchingSeparatorReadHeadCellTarget,
          BranchingHeadCellReturn.targetForRead, hread] using hcopyRun
    | some bit =>
        cases bit with
        | false =>
            simpa [tape2ReaderDescription, tape2ReaderStart,
              retargetedBranchingTape1ReadHeadCellAllExitsDescription,
              MachineDescription.readExitRetargetConfiguration,
              MachineDescription.retargetReadExitState,
              StaticDispatcherState.tape2ReaderTargets,
              StaticDispatcherState.tape2ReaderTarget,
              branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopyRun
        | true =>
            simpa [tape2ReaderDescription, tape2ReaderStart,
              retargetedBranchingTape1ReadHeadCellAllExitsDescription,
              MachineDescription.readExitRetargetConfiguration,
              MachineDescription.retargetReadExitState,
              StaticDispatcherState.tape2ReaderTargets,
              StaticDispatcherState.tape2ReaderTarget,
              branchingTape1ReadHeadCellAndReturnToSeparatorTarget,
              branchingSeparatorReadHeadCellTarget,
              BranchingHeadCellReturn.targetForRead, hread] using hcopyRun
  have hrightStates :
      forall k : Nat, k < n ->
        tape2ReaderOffset D state read0 read1 ≤
          ((tableMachine (threeHeadReaderStateLimit D)
              (StaticDispatcherState.afterRead1 D state read0 read1)
              (StaticDispatcherState.afterRead D state
                { read0 := read0,
                  read1 := read1,
                  read2 := Tape.read (Description.tapeAt logical 2) })
              (tape2ReaderDescription D state read0 read1).transitions).runConfig k
            { state := tape2ReaderStart D state read0 read1,
              tape := physical }).state := by
    intro k hk
    rw [tableMachine_runConfig_eq
      (tape2ReaderDescription D state read0 read1)]
    simpa [tape2ReaderDescription, tape2ReaderStart,
      retargetedBranchingTape1ReadHeadCellAllExitsDescription,
      MachineDescription.readExitRetargetConfiguration,
      MachineDescription.retargetReadExitState] using
      hcopyStates k hk
  refine ⟨separatorPhysical, hseparator, ?_⟩
  simpa [afterRead1JumpTape2ReaderTransitions] using
    runsFromStateTapeEquiv_tableMachine_append_right_of_left_sources_below_of_run
      (stateCount := threeHeadReaderStateLimit D)
      (start := StaticDispatcherState.afterRead1 D state read0 read1)
      (halt :=
        StaticDispatcherState.afterRead D state
          { read0 := read0,
            read1 := read1,
            read2 := Tape.read (Description.tapeAt logical 2) })
      (bound := tape2ReaderOffset D state read0 read1)
      (left := (afterRead1JumpDescription D state read0 read1).transitions)
      (right := (tape2ReaderDescription D state read0 read1).transitions)
      (sourceState := tape2ReaderStart D state read0 read1)
      (targetState :=
        StaticDispatcherState.afterRead D state
          { read0 := read0,
            read1 := read1,
            read2 := Tape.read (Description.tapeAt logical 2) })
      (n := n)
      (Tin := physical)
      (Tout := separatorPhysical)
      (actual := actual)
      (afterRead1JumpDescription_sources_below_tape2ReaderOffset
        D read0 read1 hstate)
      hrightRun
      hactual
      hrightStates

theorem afterRead1JumpDescription_runsFromTapeSeparator_in_afterRead1JumpTape2ReaderTransitions
    (D : Description) {state haltState : Nat}
    (read0 read1 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {tapeIndex : Nat}
    {physical : Tape Bool}
    (hseparator : AtTapeSeparator logical tapeIndex physical) :
    RunsFromStateTapeEquiv
      (tableMachine (threeHeadReaderStateLimit D)
        (StaticDispatcherState.afterRead1 D state read0 read1)
        haltState
        (afterRead1JumpTape2ReaderTransitions D state read0 read1))
      (StaticDispatcherState.afterRead1 D state read0 read1)
      (tape2ReaderStart D state read0 read1)
      physical
      physical := by
  have hread : Tape.read physical = none :=
    atTapeSeparator_read hseparator
  have hsourceBelow :
      StaticDispatcherState.afterRead1 D state read0 read1 <
        tape2ReaderOffset D state read0 read1 := by
    exact Nat.lt_of_lt_of_le
      (StaticDispatcherState.afterRead1_lt_readerStateLimit
        D read0 read1 hstate)
      (readerStateLimit_le_tape2ReaderOffset D state read0 read1)
  have hscratchBelow :
      afterRead1JumpScratch D state read0 read1 <
        tape2ReaderOffset D state read0 read1 := by
    have hscratch :=
      afterRead1JumpScratch_lt_afterRead1JumpLimit
        D read0 read1 hstate
    have hbase :
        afterRead1JumpLimit D ≤
          tape2ReaderOffset D state read0 read1 := by
      unfold tape2ReaderOffset tape2ReaderBlockBase
      lia
    exact Nat.lt_of_lt_of_le hscratch hbase
  have hleftRun :
      (tableMachine (threeHeadReaderStateLimit D)
          (StaticDispatcherState.afterRead1 D state read0 read1)
          haltState
          (afterRead1JumpDescription D state read0 read1).transitions).runConfig 2
        { state := StaticDispatcherState.afterRead1 D state read0 read1,
          tape := physical } =
      { state := tape2ReaderStart D state read0 read1,
        tape := Tape.move Direction.left (Tape.move Direction.right physical) } := by
    rw [tableMachine_runConfig_eq
      (afterRead1JumpDescription D state read0 read1)]
    simpa [afterRead1JumpDescription] using
      blankHeadBounceJumpDescription_runConfig_two_fromBlankHead
        (stateCount := threeHeadReaderStateLimit D)
        (source := StaticDispatcherState.afterRead1 D state read0 read1)
        (scratch := afterRead1JumpScratch D state read0 read1)
        (target := tape2ReaderStart D state read0 read1)
        (afterRead1_ne_afterRead1JumpScratch D read0 read1 hstate)
        hread
  have hleftStates :
      forall k : Nat, k < 2 ->
        ((tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.afterRead1 D state read0 read1)
            haltState
            (afterRead1JumpDescription D state read0 read1).transitions).runConfig k
          { state := StaticDispatcherState.afterRead1 D state read0 read1,
            tape := physical }).state <
          tape2ReaderOffset D state read0 read1 := by
    intro k hk
    rw [tableMachine_runConfig_eq
      (afterRead1JumpDescription D state read0 read1)]
    simpa [afterRead1JumpDescription] using
      blankHeadBounceJumpDescription_runConfig_state_lt_bound_before_two
        (stateCount := threeHeadReaderStateLimit D)
        (source := StaticDispatcherState.afterRead1 D state read0 read1)
        (scratch := afterRead1JumpScratch D state read0 read1)
        (target := tape2ReaderStart D state read0 read1)
        (bound := tape2ReaderOffset D state read0 read1)
        hsourceBelow hscratchBelow hread k hk
  simpa [afterRead1JumpTape2ReaderTransitions] using
    runsFromStateTapeEquiv_tableMachine_append_left_of_right_sources_atLeast_of_run
      (stateCount := threeHeadReaderStateLimit D)
      (start := StaticDispatcherState.afterRead1 D state read0 read1)
      (halt := haltState)
      (bound := tape2ReaderOffset D state read0 read1)
      (left := (afterRead1JumpDescription D state read0 read1).transitions)
      (right := (tape2ReaderDescription D state read0 read1).transitions)
      (sourceState := StaticDispatcherState.afterRead1 D state read0 read1)
      (targetState := tape2ReaderStart D state read0 read1)
      (n := 2)
      (Tin := physical)
      (Tout := physical)
      (actual := Tape.move Direction.left (Tape.move Direction.right physical))
      (tape2ReaderDescription_sources_atLeast D state read0 read1)
      hleftRun
      (tape_moveLeft_moveRight_equiv_self physical)
      hleftStates

theorem afterRead1JumpTape2ReaderTransitions_runsFromExistingTape1Separator
    (D : Description) {state : Nat} (read0 read1 : Option Bool)
    (hstate : state < D.stateCount)
    {logical : List (Tape Bool)} {physical : Tape Bool}
    (hlength : logical.length = 3)
    (hstart :
      AtExistingTapeSeparator (guardLogicalTapes logical) 1 physical) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.afterRead1 D state read0 read1)
            (StaticDispatcherState.afterRead D state
              { read0 := read0,
                read1 := read1,
                read2 := Tape.read (Description.tapeAt logical 2) })
            (afterRead1JumpTape2ReaderTransitions D state read0 read1))
          (StaticDispatcherState.afterRead1 D state read0 read1)
          (StaticDispatcherState.afterRead D state
            { read0 := read0,
              read1 := read1,
              read2 := Tape.read (Description.tapeAt logical 2) })
          physical
          separatorPhysical := by
  have hjump :
      RunsFromStateTapeEquiv
        (tableMachine (threeHeadReaderStateLimit D)
          (StaticDispatcherState.afterRead1 D state read0 read1)
          (StaticDispatcherState.afterRead D state
            { read0 := read0,
              read1 := read1,
              read2 := Tape.read (Description.tapeAt logical 2) })
          (afterRead1JumpTape2ReaderTransitions D state read0 read1))
        (StaticDispatcherState.afterRead1 D state read0 read1)
        (tape2ReaderStart D state read0 read1)
        physical
        physical :=
    afterRead1JumpDescription_runsFromTapeSeparator_in_afterRead1JumpTape2ReaderTransitions
      (D := D) (state := state)
      (haltState :=
        StaticDispatcherState.afterRead D state
          { read0 := read0,
            read1 := read1,
            read2 := Tape.read (Description.tapeAt logical 2) })
      read0 read1 hstate hstart.left
  rcases
      tape2ReaderDescription_runsFromExistingTape1Separator_in_afterRead1JumpTape2ReaderTransitions
        D read0 read1 hstate hlength hstart with
    ⟨separatorPhysical, hseparator, hreader⟩
  exact
    ⟨separatorPhysical, hseparator,
      runsFromStateTapeEquiv_trans hjump hreader⟩

theorem threeHeadReaderDescription_runs
    (D : Description) {state : Nat}
    (hstate : state ∈ activeStateValues D)
    {logical : List (Tape Bool)}
    (hlength : logical.length = 3) :
    exists separatorPhysical : Tape Bool,
      AtExistingTapeSeparator (guardLogicalTapes logical) 2
        separatorPhysical ∧
        RunsFromStateTapeEquiv
          (threeHeadReaderDescription D)
          (StaticDispatcherState.ready state)
          (StaticDispatcherState.afterRead D state
            { read0 := Tape.read (Description.tapeAt logical 0),
              read1 := Tape.read (Description.tapeAt logical 1),
              read2 := Tape.read (Description.tapeAt logical 2) })
          (encodedGuardedStructuredTapes logical)
          separatorPhysical := by
  have hstateLt : state < D.stateCount :=
    activeStateValues_mem_lt hstate
  let read0 := Tape.read (Description.tapeAt logical 0)
  let read1 := Tape.read (Description.tapeAt logical 1)
  let read2 := Tape.read (Description.tapeAt logical 2)
  rcases
      readyJumpTape0ReaderTransitions_runsFromGuardedBlockStart
        D hstateLt hlength with
    ⟨separator0, hseparator0, hlocal0⟩
  have hrun0 :
      RunsFromStateTapeEquiv
        (threeHeadReaderDescription D)
        (StaticDispatcherState.ready state)
        (StaticDispatcherState.afterRead0 D state read0)
        (encodedGuardedStructuredTapes logical)
        separator0 := by
    exact
      runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
        (small :=
          tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.ready state)
            (StaticDispatcherState.afterRead0 D state read0)
            (readyJumpTape0ReaderTransitions D state))
        (big := threeHeadReaderDescription D)
        (hsubset := by
          intro t ht
          simpa [tableMachine, threeHeadReaderDescription] using
            readyJumpTape0ReaderTransitions_subset_threeHeadReaderTransitions
              D hstate t ht)
        (hdet := threeHeadReaderDescription_deterministic D)
        (hfree :=
          tableMachine_transitionFreeAt_of_sourcesNe
            (readyJumpTape0ReaderTransitions_sources_ne_afterRead0
              D read0 hstateLt))
        (by
          simpa [read0] using hlocal0)
  rcases
      afterRead0JumpTape1ReaderTransitions_runsFromExistingBlockStart
        D read0 hstateLt hlength hseparator0 with
    ⟨separator1, hseparator1, hlocal1⟩
  have hrun1 :
      RunsFromStateTapeEquiv
        (threeHeadReaderDescription D)
        (StaticDispatcherState.afterRead0 D state read0)
        (StaticDispatcherState.afterRead1 D state read0 read1)
        separator0
        separator1 := by
    exact
      runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
        (small :=
          tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.afterRead0 D state read0)
            (StaticDispatcherState.afterRead1 D state read0 read1)
            (afterRead0JumpTape1ReaderTransitions D state read0))
        (big := threeHeadReaderDescription D)
        (hsubset := by
          intro t ht
          simpa [tableMachine, threeHeadReaderDescription] using
            afterRead0JumpTape1ReaderTransitions_subset_threeHeadReaderTransitions
              D read0 hstate t ht)
        (hdet := threeHeadReaderDescription_deterministic D)
        (hfree :=
          tableMachine_transitionFreeAt_of_sourcesNe
            (afterRead0JumpTape1ReaderTransitions_sources_ne_afterRead1
              D read0 read1 hstateLt))
        (by
          simpa [read1] using hlocal1)
  rcases
      afterRead1JumpTape2ReaderTransitions_runsFromExistingTape1Separator
        D read0 read1 hstateLt hlength hseparator1 with
    ⟨separator2, hseparator2, hlocal2⟩
  have hrun2 :
      RunsFromStateTapeEquiv
        (threeHeadReaderDescription D)
        (StaticDispatcherState.afterRead1 D state read0 read1)
        (StaticDispatcherState.afterRead D state
          { read0 := read0, read1 := read1, read2 := read2 })
        separator1
        separator2 := by
    exact
      runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
        (small :=
          tableMachine (threeHeadReaderStateLimit D)
            (StaticDispatcherState.afterRead1 D state read0 read1)
            (StaticDispatcherState.afterRead D state
              { read0 := read0, read1 := read1, read2 := read2 })
            (afterRead1JumpTape2ReaderTransitions D state read0 read1))
        (big := threeHeadReaderDescription D)
        (hsubset := by
          intro t ht
          simpa [tableMachine, threeHeadReaderDescription] using
            afterRead1JumpTape2ReaderTransitions_subset_threeHeadReaderTransitions
              D read0 read1 hstate t ht)
        (hdet := threeHeadReaderDescription_deterministic D)
        (hfree :=
          tableMachine_transitionFreeAt_of_sourcesNe
            (afterRead1JumpTape2ReaderTransitions_sources_ne_afterRead
              D read0 read1 read2 hstateLt))
        (by
          simpa [read2] using hlocal2)
  exact
    ⟨separator2, hseparator2, by
      simpa [read0, read1, read2] using
        runsFromStateTapeEquiv_trans
          (runsFromStateTapeEquiv_trans hrun0 hrun1) hrun2⟩

end StaticDispatcherReaderAssembly

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
