import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Machine

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open MachineDescription
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

theorem next_changes_state_or_some_action_moves
    (attempt : MachineDescription) (s : CoreState)
    (r0 r1 r2 : Option Bool) (st : TypedStep CoreState)
    (hnext : next attempt s r0 r1 r2 = some st) :
    st.target ≠ s ∨
      st.action0.move ≠ HeadMove.stay ∨
        st.action1.move ≠ HeadMove.stay ∨
        st.action2.move ≠ HeadMove.stay := by
  cases s with
  | run q =>
      by_cases hq : q = attempt.halt
      · simp [next, hq, someStep] at hnext
        subst st
        simp
      · simp [next, hq, someStep] at hnext
        cases ht : attempt.lookupTransition q r0 with
        | none =>
            simp [ht, progressSpin] at hnext
            subst st
            simp
        | some t =>
            simp [ht] at hnext
            subst st
            rcases t with ⟨source, read, write, move, target⟩
            cases move <;>
              simp [workAction, headMoveOfDirection]
  | cell3 third =>
      cases third <;> cases r0 <;> (try cases ‹Bool›) <;>
        simp [next, copyBoth, progressSpin] at hnext <;>
        subst st <;>
        simp
  | result phase =>
      cases phase <;>
        cases r0 <;> (try cases ‹Bool›) <;>
          cases r1 <;> (try cases ‹Bool›) <;>
            cases r2 <;> (try cases ‹Bool›) <;>
              simp [next, beginWrite, beginPendingWrite, progressSpin,
                someStep] at hnext <;>
                subst st <;>
                simp
  | writeResult phase =>
      cases phase <;>
        cases r0 <;> (try cases ‹Bool›) <;>
          cases r1 <;> (try cases ‹Bool›) <;>
            simp [next, writePhaseTarget, writePhaseMarker, writePhaseBit,
              someStep] at hnext <;>
              subst st <;>
              simp
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
              progressSpin, someStep] at hnext <;>
              subst st <;>
              simp
  | halt => simp [next] at hnext

theorem coreD_transition_changes_state_or_some_action_moves
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady) :
    ∀ tr, tr ∈ (coreD attempt hattempt).transitions →
      ∃ a0 a1 a2 : TapeAction,
        tr.actions = [a0, a1, a2] ∧
          (tr.target ≠ tr.source ∨
            a0.move ≠ HeadMove.stay ∨
              a1.move ≠ HeadMove.stay ∨
              a2.move ≠ HeadMove.stay) := by
  intro tr htr
  rcases (table attempt hattempt).mem_transitions htr with ⟨s, hs, hrow⟩
  rcases (table attempt hattempt).mem_rowsFor hrow with
    ⟨r0, r1, r2, st, hnext, rfl⟩
  change next attempt s r0 r1 r2 = some st at hnext
  have hchange :=
    next_changes_state_or_some_action_moves attempt s r0 r1 r2 st hnext
  refine ⟨st.action0, st.action1, st.action2, ?_, ?_⟩
  · rfl
  · rcases hchange with htarget | hmoves
    · left
      simp only [TypedStateTable.rowOf, ThreeTape.row]
      intro hid
      have htargetMem : st.target ∈ (table attempt hattempt).states :=
        (table attempt hattempt).next_target_mem s hs r0 r1 r2 st hnext
      apply htarget
      exact
        (table attempt hattempt).stateId_inj st.target htargetMem s hs hid
    · exact Or.inr hmoves

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
