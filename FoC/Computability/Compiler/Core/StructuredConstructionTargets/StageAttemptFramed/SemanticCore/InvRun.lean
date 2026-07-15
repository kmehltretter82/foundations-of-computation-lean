import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Diverge
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Cleanup

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

theorem structured_halt_of_lower_coreD_halt
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (T0 T1 T2 Tout : Tape Bool)
    (hhalt :
      (lowerStructured3Description (coreD attempt hattempt)).HaltsFromTape
        (encodedGuardedStructuredTapes
          ((table attempt hattempt).config .header0 T0 T1 T2).tapes)
        Tout) :
    ∃ k : Nat,
      ((coreD attempt hattempt).runConfig k
        ((table attempt hattempt).config .header0 T0 T1 T2)).state =
          (coreD attempt hattempt).halt := by
  classical
  apply Classical.byContradiction
  intro hno
  have hne :
      ∀ k : Nat,
        ((coreD attempt hattempt).runConfig k
          ((table attempt hattempt).config .header0 T0 T1 T2)).state ≠
            (coreD attempt hattempt).halt := by
    intro k
    intro hk
    exact hno ⟨k, hk⟩
  exact
    (lower_coreD_not_halts_of_ne_halt attempt hattempt T0 T1 T2 Tout hne)
      hhalt

theorem target_halts_of_leads
    {M : TypedStateTable σ}
    (hhaltFree : M.description.HaltTransitionFree)
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (hlead : M.Leads c d)
    {n : Nat}
    (hhalt : (M.description.runConfig n c).state = M.description.halt) :
    ∃ m : Nat, (M.description.runConfig m d).state = M.description.halt := by
  rcases hlead with ⟨j, hj⟩
  refine ⟨n, ?_⟩
  have hpersist :
      M.description.runConfig (n + j) c =
        M.description.runConfig n c := by
    rw [Description.runConfig_add]
    exact Description.runConfig_halt hhaltFree _ hhalt j
  rw [← hj n, hpersist]
  exact hhalt

theorem runConfig_spin_state
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady) :
    ∀ n : Nat, ∀ T0 T1 T2 : Tape Bool,
      ((coreD attempt hattempt).runConfig n
        ((table attempt hattempt).config .spin T0 T1 T2)).state =
          (table attempt hattempt).stateId .spin := by
  intro n
  induction n with
  | zero =>
      intro T0 T1 T2
      rfl
  | succ n ih =>
      intro T0 T1 T2
      have hnext :
          next attempt .spin (Tape.read T0) (Tape.read T1) (Tape.read T2) =
            some progressSpin := by
        rfl
      have hrun :=
        (table attempt hattempt).runConfig_succ_config
          (T0 := T0) (T1 := T1) (T2 := T2)
          (mem_states_of_stateBounded (attempt := attempt) (s := .spin) trivial)
          hnext n
      change
        ((table attempt hattempt).description.runConfig (n + 1)
          ((table attempt hattempt).config .spin T0 T1 T2)).state = _
      unfold TypedStateTable.config at hrun ⊢
      rw [hrun]
      exact ih (progressSpin.action0.apply T0)
        (progressSpin.action1.apply T1) (progressSpin.action2.apply T2)

theorem core_run_halt_implies_attempt_halt
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady) :
    ∀ n q, q < attempt.stateCount -> ∀ T0 T1 T2 : Tape Bool,
      ((coreD attempt hattempt).runConfig n
        ((table attempt hattempt).config (.run q) T0 T1 T2)).state =
          (coreD attempt hattempt).halt ->
        ∃ fuel : Nat, ∃ Tout : Tape Bool,
          attempt.runConfig fuel { state := q, tape := T0 } =
            { state := attempt.halt, tape := Tout } := by
  intro n
  induction n with
  | zero =>
      intro q hq T0 T1 T2 hhalt
      have hid :
          (table attempt hattempt).stateId (.run q) =
            (table attempt hattempt).stateId .halt := by
        simpa [coreD, table, TypedStateTable.ofList,
          TypedStateTable.config, Description.runConfig] using hhalt
      have hstate : (.run q : CoreState) = .halt :=
        (table attempt hattempt).stateId_inj (.run q)
          (mem_states_of_stateBounded hq) .halt
          (mem_states_of_stateBounded trivial) hid
      cases hstate
  | succ n ih =>
      intro q hq T0 T1 T2 hhalt
      by_cases hqHalt : q = attempt.halt
      · subst q
        exact ⟨0, T0, rfl⟩
      · cases hlookup : attempt.lookupTransition q (Tape.read T0) with
        | none =>
            have hnext :
                next attempt (.run q) (Tape.read T0) (Tape.read T1)
                    (Tape.read T2) = some progressSpin := by
              simp [next, hqHalt, hlookup, progressSpin]
            have hrun :=
              (table attempt hattempt).runConfig_succ_config
                (T0 := T0) (T1 := T1) (T2 := T2)
                (mem_states_of_stateBounded
                  (attempt := attempt) (s := .run q) hq)
                hnext n
            unfold TypedStateTable.config at hrun
            change
              ((table attempt hattempt).description.runConfig (n + 1)
                (ThreeTape.config
                  ((table attempt hattempt).stateId (.run q))
                  T0 T1 T2)).state = _ at hhalt
            rw [hrun] at hhalt
            have hspinState :=
              runConfig_spin_state attempt hattempt n
                (progressSpin.action0.apply T0)
                (progressSpin.action1.apply T1)
                (progressSpin.action2.apply T2)
            have hid :
                (table attempt hattempt).stateId .spin =
                  (table attempt hattempt).stateId .halt := by
              rw [← hspinState]
              simpa [coreD, table, TypedStateTable.ofList,
                TypedStateTable.config, progressSpin] using hhalt
            have hstate : (.spin : CoreState) = .halt :=
              (table attempt hattempt).stateId_inj .spin
                (mem_states_of_stateBounded trivial) .halt
                (mem_states_of_stateBounded trivial) hid
            cases hstate
        | some t =>
            have hnext :
                next attempt (.run q) (Tape.read T0) (Tape.read T1)
                    (Tape.read T2) =
                  some
                    { target := .run t.target
                      action0 := workAction t
                      action1 := markerAction t.move
                      action2 := keepS } := by
              simp [next, hqHalt, hlookup, someStep]
            have hrun :=
              (table attempt hattempt).runConfig_succ_config
                (T0 := T0) (T1 := T1) (T2 := T2)
                (mem_states_of_stateBounded
                  (attempt := attempt) (s := .run q) hq)
                hnext n
            have htarget : t.target < attempt.stateCount :=
              (hattempt.left.right.right.right.left t
                (lookupTransition_mem hlookup)).right
            have hhaltTail :
                ((coreD attempt hattempt).runConfig n
                  ((table attempt hattempt).config (.run t.target)
                    ((workAction t).apply T0)
                    ((markerAction t.move).apply T1)
                    (keepS.apply T2))).state =
                  (coreD attempt hattempt).halt := by
              unfold TypedStateTable.config at hrun
              change
                ((table attempt hattempt).description.runConfig (n + 1)
                  (ThreeTape.config
                    ((table attempt hattempt).stateId (.run q))
                    T0 T1 T2)).state = _ at hhalt
              rw [hrun] at hhalt
              simpa [coreD, TypedStateTable.config] using hhalt
            rcases ih t.target htarget
                ((workAction t).apply T0)
                ((markerAction t.move).apply T1)
                (keepS.apply T2) hhaltTail with
              ⟨fuel, Tout, hattemptRun⟩
            refine ⟨fuel + 1, Tout, ?_⟩
            rw [MachineDescription.runConfig]
            have hstepAttempt :
                attempt.stepConfig { state := q, tape := T0 } =
                  some
                    { state := t.target
                      tape := (workAction t).apply T0 } := by
              rcases t with ⟨source, read, write, move, target⟩
              cases move <;>
                simp [MachineDescription.stepConfig, hlookup, workAction,
                  headMoveOfDirection, TapeAction.apply, HeadMove.apply]
            rw [hstepAttempt]
            exact hattemptRun

theorem controller_core_halt_implies_attempt_halt
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (C : DovetailControllerLayout) (n : Nat)
    (hhalt :
      ((coreD attempt hattempt).runConfig n
        ((table attempt hattempt).config .header0
          (Tape.input
            (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits C))
          Tape.blank Tape.blank)).state =
        (coreD attempt hattempt).halt) :
    ∃ fuel : Nat, ∃ Tout : Tape Bool,
      attempt.runConfig fuel
          { state := attempt.start
            tape := reconstructedTape
              (stageInputBits C) (resultBits C.result) } =
        { state := attempt.halt, tape := Tout } := by
  have hlead := leads_controller_to_run_start
    (attempt := attempt) (hattempt := hattempt) C
  have htail :
      ∃ m : Nat,
        ((coreD attempt hattempt).runConfig m
          ((table attempt hattempt).config (.run attempt.start)
            (reconstructedTape (stageInputBits C) (resultBits C.result))
            (markerTape (stageInputBits C))
            (tapeAtCells (parsedInputLeft2 C) []))).state =
          (coreD attempt hattempt).halt := by
    apply target_halts_of_leads
      ((table attempt hattempt).description_haltTransitionFree)
      (hlead := hlead)
    simpa [coreD, cfg] using hhalt
  rcases htail with ⟨m, hm⟩
  exact core_run_halt_implies_attempt_halt attempt hattempt m
    attempt.start hattempt.left.right.left
    (reconstructedTape (stageInputBits C) (resultBits C.result))
    (markerTape (stageInputBits C))
    (tapeAtCells (parsedInputLeft2 C) []) hm

theorem haltsWithOutputIn_of_reconstructed_run
    {attempt : MachineDescription}
    (C : DovetailControllerLayout) (fuel : Nat)
    (Tout : Tape Bool) (result : Word Bool)
    (hrun :
      attempt.runConfig fuel
          { state := attempt.start
            tape := reconstructedTape
              (stageInputBits C) (resultBits C.result) } =
        { state := attempt.halt, tape := Tout })
    (houtput : Tape.normalizedOutput Tout = resultBits result) :
    attempt.HaltsWithOutputIn fuel (stageInputBits C) (resultBits result) := by
  let reconstructed : MachineDescription.Configuration :=
    { state := attempt.start
      tape := reconstructedTape (stageInputBits C) (resultBits C.result) }
  let canonical := attempt.initial (stageInputBits C)
  have hequiv := MachineDescription.runConfig_equiv attempt fuel
    (c := reconstructed) (d := canonical) (by rfl)
    (reconstructedTape_equiv_input_result
      (stageInputBits C) (resultBits C.result) (stageInputBits_ne_nil C))
  have hstateReconstructed :
      (attempt.runConfig fuel reconstructed).state = attempt.halt := by
    simpa [reconstructed] using
      congrArg MachineDescription.Configuration.state hrun
  have htapeReconstructed :
      (attempt.runConfig fuel reconstructed).tape = Tout := by
    simpa [reconstructed] using
      congrArg MachineDescription.Configuration.tape hrun
  have hstateCanonical :
      (attempt.runConfig fuel canonical).state = attempt.halt :=
    hequiv.left.symm.trans hstateReconstructed
  have hnormalizedReconstructed :
      Tape.normalizedOutput (attempt.runConfig fuel reconstructed).tape =
        resultBits result := by
    rw [htapeReconstructed]
    exact houtput
  have hnormalizedCanonical :
      Tape.normalizedOutput (attempt.runConfig fuel canonical).tape =
        resultBits result :=
    (Tape.Equiv.normalizedOutput_eq hequiv.right).symm.trans
      hnormalizedReconstructed
  exact ⟨hstateCanonical, hnormalizedCanonical⟩

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
