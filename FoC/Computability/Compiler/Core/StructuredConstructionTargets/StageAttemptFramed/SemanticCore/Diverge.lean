import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Progress
import FoC.Computability.Compiler.Structured.Lowering.DivergenceTransfer

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open MachineDescription
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

theorem next_ne_none_of_ne_halt
    (attempt : MachineDescription) (s : CoreState)
    (hs : s ≠ .halt) (r0 r1 r2 : Option Bool) :
    next attempt s r0 r1 r2 ≠ none := by
  cases s with
  | run q =>
      by_cases hq : q = attempt.halt
      · simp [next, hq, someStep]
      · cases ht : attempt.lookupTransition q r0 <;>
          simp [next, hq, ht, progressSpin, someStep]
  | cell3 third =>
      cases third <;> cases r0 <;> (try cases ‹Bool›) <;>
        simp [next, copyBoth, progressSpin]
  | result phase =>
      cases phase <;>
        cases r0 <;> (try cases ‹Bool›) <;>
          cases r1 <;> (try cases ‹Bool›) <;>
            cases r2 <;> (try cases ‹Bool›) <;>
              simp [next, beginWrite, beginPendingWrite, progressSpin,
                someStep]
  | writeResult phase =>
      cases phase <;>
        cases r0 <;> (try cases ‹Bool›) <;>
          cases r1 <;> (try cases ‹Bool›) <;>
            simp [next, writePhaseTarget, writePhaseMarker, writePhaseBit,
              someStep]
  | header0 | header1 | header2 | header3 |
      inputLen0 | inputLen1 | inputLen2 | inputLen3 |
      field0 | field1 | cell2 | stage0 | stage1 | stage2 | stage3 |
      eraseRight | eraseLeft | auxLeft | reconstruct | workLeft |
      normalizeLeft | resultFirst |
      counterLeft | counterRight | checkCount |
      rewindA | rewindB | rewindC | rewindTokenFirst |
      markerSecond | rewindTrueBack | restoreThird | restoreFourth |
      restoreBackThird | restoreBackSecond | restoreFirst | spin =>
      cases r0 <;> (try cases ‹Bool›) <;>
        cases r1 <;> (try cases ‹Bool›) <;>
          cases r2 <;> (try cases ‹Bool›) <;>
            simp [next, copyExpected, copyBoth, copyOutput,
              progressSpin, someStep]
  | halt => exact absurd rfl hs

theorem stepConfig_config_ne_none_of_ne_halt
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (s : CoreState) (hsMem : s ∈ (table attempt hattempt).states)
    (hsHalt : s ≠ .halt) (T0 T1 T2 : Tape Bool) :
    (coreD attempt hattempt).stepConfig
        ((table attempt hattempt).config s T0 T1 T2) ≠ none := by
  change (table attempt hattempt).description.stepConfig
      ((table attempt hattempt).config s T0 T1 T2) ≠ none
  unfold TypedStateTable.config
  rw [(table attempt hattempt).stepConfig_config hsMem]
  cases hnext : next attempt s (Tape.read T0) (Tape.read T1) (Tape.read T2)
  · exact absurd hnext
      (next_ne_none_of_ne_halt attempt s hsHalt _ _ _)
  · simp [table, TypedStateTable.ofList, hnext]

def IsTableConfig
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (c : CommonGround.FiniteTransducers.Structured.Configuration) : Prop :=
  ∃ s : CoreState, s ∈ (table attempt hattempt).states ∧
    ∃ T0 T1 T2 : Tape Bool,
      c = (table attempt hattempt).config s T0 T1 T2

theorem runConfig_isTableConfig
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady) :
    ∀ n s, s ∈ (table attempt hattempt).states ->
      ∀ T0 T1 T2 : Tape Bool,
        IsTableConfig attempt hattempt
          ((coreD attempt hattempt).runConfig n
            ((table attempt hattempt).config s T0 T1 T2)) := by
  intro n
  induction n with
  | zero =>
      intro s hs T0 T1 T2
      exact ⟨s, hs, T0, T1, T2, rfl⟩
  | succ n ih =>
      intro s hs T0 T1 T2
      change IsTableConfig attempt hattempt
        ((table attempt hattempt).description.runConfig (n + 1)
          ((table attempt hattempt).config s T0 T1 T2))
      rw [Description.runConfig]
      have hstep :=
        (table attempt hattempt).stepConfig_config hs T0 T1 T2
      rw [show
        (table attempt hattempt).description.stepConfig
            ((table attempt hattempt).config s T0 T1 T2) =
          ((table attempt hattempt).next s
              (Tape.read T0) (Tape.read T1) (Tape.read T2)).map
            (fun st =>
              (table attempt hattempt).config st.target
                (st.action0.apply T0) (st.action1.apply T1)
                (st.action2.apply T2)) by
        simpa [TypedStateTable.config] using hstep]
      cases hnext : (table attempt hattempt).next s
          (Tape.read T0) (Tape.read T1) (Tape.read T2) with
      | none =>
          simp
          exact ⟨s, hs, T0, T1, T2, rfl⟩
      | some st =>
          simp
          exact ih st.target
            ((table attempt hattempt).next_target_mem s hs _ _ _ st hnext)
            (st.action0.apply T0) (st.action1.apply T1)
            (st.action2.apply T2)

theorem stepConfig_runConfig_ne_none_of_ne_halt
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (s0 : CoreState) (hs0 : s0 ∈ (table attempt hattempt).states)
    (T0 T1 T2 : Tape Bool)
    (hneHalt :
      ∀ k : Nat,
        ((coreD attempt hattempt).runConfig k
          ((table attempt hattempt).config s0 T0 T1 T2)).state ≠
            (coreD attempt hattempt).halt) :
    ∀ k : Nat,
      (coreD attempt hattempt).stepConfig
        ((coreD attempt hattempt).runConfig k
          ((table attempt hattempt).config s0 T0 T1 T2)) ≠ none := by
  intro k
  rcases runConfig_isTableConfig attempt hattempt k s0 hs0 T0 T1 T2 with
    ⟨s, hs, U0, U1, U2, hcfg⟩
  rw [hcfg]
  apply stepConfig_config_ne_none_of_ne_halt attempt hattempt s hs
  intro hshalt
  apply hneHalt k
  rw [hcfg, hshalt]
  rfl

theorem coreD_stepConfig_state_ne_or_tapes_ne
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (hstep : (coreD attempt hattempt).stepConfig c = some d) :
    c.state ≠ d.state ∨ c.tapes ≠ d.tapes := by
  exact
    stepConfig_state_ne_or_tapes_ne_of_state_or_action_moves
        (D := coreD attempt hattempt) rfl
        (coreD_transition_changes_state_or_some_action_moves attempt hattempt)
        hstep

theorem lower_coreD_not_halts_of_ne_halt
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (T0 T1 T2 Tout : Tape Bool)
    (hneHalt :
      ∀ k : Nat,
        ((coreD attempt hattempt).runConfig k
          ((table attempt hattempt).config .header0 T0 T1 T2)).state ≠
            (coreD attempt hattempt).halt) :
    ¬ (lowerStructured3Description (coreD attempt hattempt)).HaltsFromTape
      (encodedGuardedStructuredTapes
        ((table attempt hattempt).config .header0 T0 T1 T2).tapes)
      Tout := by
  apply
    lowerStructured3Description_not_halts_of_state_or_tape_progress
        ((table attempt hattempt).description_wellFormed)
        ((table attempt hattempt).description_haltTransitionFree)
        ((table attempt hattempt).description_supportsReadWriteRows3)
        ((table attempt hattempt).config .header0 T0 T1 T2)
  · rfl
  · rfl
  · exact
      stepConfig_runConfig_ne_none_of_ne_halt attempt hattempt .header0
        (mem_states_of_stateBounded trivial) T0 T1 T2 hneHalt
  · exact hneHalt
  · exact coreD_stepConfig_state_ne_or_tapes_ne attempt hattempt

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
