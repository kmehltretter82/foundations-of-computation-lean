import FoC.Grammars.PDANormalize.Forward

set_option doc.verso true

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace PDA

theorem popNormalize_original_transition_cases
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {q : state} {a? : Option input} {pop : Word stack}
    {target : PopNormalizedState (M := M) presentation}
    {push : Word stack}
    (htransition :
      (PopNormalize M presentation).transition (Sum.inl q) a? pop
        target push) :
    (exists r : state,
      M.transition q a? pop r push ∧ target = Sum.inl r) ∨
    (exists rule : TransitionRule input stack state,
      exists A : stack, exists B : stack, exists rest : Word stack,
      exists hhelper : (rule, B :: rest) ∈
        popNormalizeHelperPairs presentation,
        M.transition q a? (A :: B :: rest) rule.target rule.push ∧
          pop = [A] ∧ push = [] ∧
            target = Sum.inr ⟨(rule, B :: rest), hhelper⟩) := by
  rcases htransition with ⟨normalizedRule, hmem, happlies⟩
  unfold popNormalizedTransitionRules at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with (hDirect | hStart) | hHelper
  · rcases List.mem_flatMap.mp hDirect with
      ⟨baseRule, hbaseRule, hnormalized⟩
    unfold popNormalizedDirectTransitionRulesForRule at hnormalized
    cases hbasePop : baseRule.pop with
    | nil =>
        simp [hbasePop] at hnormalized
        subst normalizedRule
        rcases happlies with
          ⟨hsource, hinput, hpop, htarget, hpush⟩
        have hbaseSource : baseRule.source = q := by
          exact Sum.inl.inj hsource
        have htransitionM :
            M.transition q a? pop baseRule.target push := by
          apply (presentation.transition_complete q a? pop
            baseRule.target push).mpr
          refine ⟨baseRule, hbaseRule, ?_⟩
          exact ⟨hbaseSource, hinput, hbasePop.trans hpop, rfl, hpush⟩
        left
        exact ⟨baseRule.target, htransitionM, htarget.symm⟩
    | cons A rest =>
        cases rest with
        | nil =>
            simp [hbasePop] at hnormalized
            subst normalizedRule
            rcases happlies with
              ⟨hsource, hinput, hpop, htarget, hpush⟩
            have hbaseSource : baseRule.source = q := by
              exact Sum.inl.inj hsource
            have htransitionM :
                M.transition q a? pop baseRule.target push := by
              apply (presentation.transition_complete q a? pop
                baseRule.target push).mpr
              refine ⟨baseRule, hbaseRule, ?_⟩
              exact ⟨hbaseSource, hinput, hbasePop.trans hpop, rfl, hpush⟩
            left
            exact ⟨baseRule.target, htransitionM, htarget.symm⟩
        | cons B restTail =>
            simp [hbasePop] at hnormalized
  · rcases List.mem_flatMap.mp hStart with
      ⟨baseRule, hbaseRule, hnormalized⟩
    unfold popNormalizedStartSplitTransitionRulesForRule at hnormalized
    split at hnormalized
    · simp at hnormalized
    · simp at hnormalized
    · rename_i A B rest hbasePop
      simp at hnormalized
      subst normalizedRule
      rcases happlies with
        ⟨hsource, hinput, hpop, htarget, hpush⟩
      have hbaseSource : baseRule.val.source = q := by
        exact Sum.inl.inj hsource
      have htransitionM :
          M.transition q a? (A :: B :: rest)
            baseRule.val.target baseRule.val.push := by
        apply (presentation.transition_complete q a? (A :: B :: rest)
          baseRule.val.target baseRule.val.push).mpr
        refine ⟨baseRule.val, baseRule.property, ?_⟩
        exact ⟨hbaseSource, hinput, hbasePop, rfl, rfl⟩
      right
      refine ⟨baseRule.val, A, B, rest, ?_, ?_⟩
      · have hremaining :
            B :: rest ∈ popNormalizeHelperRemainders baseRule.val.pop := by
          rw [hbasePop]
          exact suffixesWithNil_self_mem (B :: rest)
        exact popNormalizeHelperPairs_mem baseRule.property hremaining
      · constructor
        · exact htransitionM
        constructor
        · exact hpop.symm
        constructor
        · exact hpush.symm
        · exact htarget.symm
  · rcases List.mem_map.mp hHelper with ⟨helper, _hhelper, hnormalized⟩
    subst normalizedRule
    rcases happlies with ⟨hsource, _hinput, _hpop, _htarget, _hpush⟩
    unfold popNormalizedHelperTransitionRule at hsource
    split at hsource <;> cases hsource

theorem popNormalize_helper_transition_cases
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (helper : { helper : TransitionRule input stack state × Word stack //
      helper ∈ popNormalizeHelperPairs presentation })
    {a? : Option input} {pop : Word stack}
    {target : PopNormalizedState (M := M) presentation}
    {push : Word stack}
    (htransition :
      (PopNormalize M presentation).transition (Sum.inr helper) a? pop
        target push) :
    a? = none ∧
      ((helper.val.2 = [] ∧ pop = [] ∧
          target = Sum.inl helper.val.1.target ∧
          push = helper.val.1.push) ∨
        (exists A : stack, exists rest : Word stack,
          exists htail : (helper.val.1, rest) ∈
              popNormalizeHelperPairs presentation,
            helper.val.2 = A :: rest ∧ pop = [A] ∧
              target = Sum.inr ⟨(helper.val.1, rest), htail⟩ ∧
              push = [])) := by
  rcases htransition with ⟨normalizedRule, hmem, happlies⟩
  unfold popNormalizedTransitionRules at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with (hDirect | hStart) | hHelper
  · rcases List.mem_flatMap.mp hDirect with
      ⟨baseRule, _hbaseRule, hnormalized⟩
    unfold popNormalizedDirectTransitionRulesForRule at hnormalized
    cases hbasePop : baseRule.pop with
    | nil =>
        simp [hbasePop] at hnormalized
        subst normalizedRule
        rcases happlies with ⟨hsource, _hinput, _hpop, _htarget, _hpush⟩
        cases hsource
    | cons A rest =>
        cases rest with
        | nil =>
            simp [hbasePop] at hnormalized
            subst normalizedRule
            rcases happlies with
              ⟨hsource, _hinput, _hpop, _htarget, _hpush⟩
            cases hsource
        | cons B restTail =>
            simp [hbasePop] at hnormalized
  · rcases List.mem_flatMap.mp hStart with
      ⟨baseRule, _hbaseRule, hnormalized⟩
    unfold popNormalizedStartSplitTransitionRulesForRule at hnormalized
    split at hnormalized
    · simp at hnormalized
    · simp at hnormalized
    · rename_i A B rest hbasePop
      simp at hnormalized
      subst normalizedRule
      rcases happlies with ⟨hsource, _hinput, _hpop, _htarget, _hpush⟩
      cases hsource
  · rcases List.mem_map.mp hHelper with
      ⟨listedHelper, _hlistedHelper, hnormalized⟩
    subst normalizedRule
    unfold popNormalizedHelperTransitionRule at happlies
    split at happlies
    · rename_i hremaining
      rcases happlies with ⟨hsource, hinput, hpop, htarget, hpush⟩
      have hhelperEq : listedHelper = helper := Sum.inr.inj hsource
      subst listedHelper
      constructor
      · exact hinput.symm
      · left
        exact ⟨hremaining, hpop.symm, htarget.symm, hpush.symm⟩
    · rename_i A rest hremaining
      rcases happlies with ⟨hsource, hinput, hpop, htarget, hpush⟩
      have hhelperEq : listedHelper = helper := Sum.inr.inj hsource
      subst listedHelper
      constructor
      · exact hinput.symm
      · right
        refine ⟨A, rest, ?_, ?_⟩
        · have hpair :
              (helper.val.1, A :: rest) ∈
                popNormalizeHelperPairs presentation := by
            cases helper with
            | mk pair hprop =>
                cases pair with
                | mk base remaining =>
                    simp at hremaining ⊢
                    subst remaining
                    exact hprop
          exact popNormalizeHelperPairs_tail_mem hpair
        · exact ⟨hremaining, hpop.symm, htarget.symm, hpush.symm⟩

/-!
Compression is the inverse of the simulation story.  The proof proceeds by the
length of the normalized computation and proves two statements together: paths
between original states compress to genuine computations of the source PDA, and
paths that start in helper states can be reattached to the original transition
that created the helper.  Carrying both statements at once is what lets the
induction consume an arbitrary normalized path without losing the context that a
helper state encodes.
-/

theorem popNormalize_compresses_original_and_helper_computesIn
    {M : PDA input stack state} (presentation : FinitePresentation M)
    (n : Nat) :
    (forall (p q : state) (sourceInput targetInput : Word input)
        (sourceStack targetStack : Word stack),
      ComputesIn (PopNormalize M presentation) n
        { state := Sum.inl p, unread := sourceInput,
          stack := sourceStack }
        { state := Sum.inl q, unread := targetInput,
          stack := targetStack } ->
      Computes M
        { state := p, unread := sourceInput, stack := sourceStack }
        { state := q, unread := targetInput, stack := targetStack }) ∧
    (forall
        (helper : { helper : TransitionRule input stack state × Word stack //
          helper ∈ popNormalizeHelperPairs presentation })
        (q : state) (sourceInput targetInput : Word input)
        (sourceStack targetStack : Word stack),
      ComputesIn (PopNormalize M presentation) n
        { state := Sum.inr helper, unread := sourceInput,
          stack := sourceStack }
        { state := Sum.inl q, unread := targetInput,
          stack := targetStack } ->
      exists tail : Word stack,
        sourceStack = Word.Concat helper.val.2 tail ∧
          Computes M
            { state := helper.val.1.target, unread := sourceInput,
              stack := Word.Concat helper.val.1.push tail }
            { state := q, unread := targetInput,
              stack := targetStack }) := by
  induction n with
  | zero =>
      constructor
      · intro p q sourceInput targetInput sourceStack targetStack hcomp
        have hEq := computesIn_zero_eq hcomp
        injection hEq with hstate hunread hstack
        have hpq : p = q := Sum.inl.inj hstate
        subst q
        subst targetInput
        subst targetStack
        exact Computes.refl _
      · intro helper q sourceInput targetInput sourceStack targetStack hcomp
        have hEq := computesIn_zero_eq hcomp
        injection hEq with hstate _hunread _hstack
        cases hstate
  | succ n ih =>
      constructor
      · intro p q sourceInput targetInput sourceStack targetStack hcomp
        rcases computesIn_succ_inv hcomp with ⟨mid, hstep, hrest⟩
        cases hstep with
        | read htransition =>
            rcases popNormalize_original_transition_cases
              (presentation := presentation) htransition with
              hdirect | hsplit
            ·
                rcases hdirect with ⟨r, htransitionM, htarget⟩
                rw [htarget] at hrest
                have hrestComp :=
                  ih.left r q _ targetInput _ targetStack hrest
                exact Computes.step
                  (Step.read (M := M) htransitionM) hrestComp
            ·
                rcases hsplit with
                  ⟨rule, A, B, rest, hhelper, htransitionM,
                    hpop, hpush, htarget⟩
                rw [htarget, hpush] at hrest
                have hrestComp :=
                  ih.right ⟨(rule, B :: rest), hhelper⟩ q _
                    targetInput _ targetStack hrest
                rcases hrestComp with ⟨tail, hstack, htailComp⟩
                exact Computes.step
                  (by
                    have hstack' := hstack
                    simp [Word.Concat] at hstack'
                    rw [hstack']
                    simpa [hpop, Word.Concat, List.append_assoc] using
                      (Step.read (M := M) (restStack := tail)
                        htransitionM))
                  htailComp
        | epsilon htransition =>
            rcases popNormalize_original_transition_cases
              (presentation := presentation) htransition with
              hdirect | hsplit
            ·
                rcases hdirect with ⟨r, htransitionM, htarget⟩
                rw [htarget] at hrest
                have hrestComp :=
                  ih.left r q _ targetInput _ targetStack hrest
                exact Computes.step
                  (Step.epsilon (M := M) htransitionM) hrestComp
            ·
                rcases hsplit with
                  ⟨rule, A, B, rest, hhelper, htransitionM,
                    hpop, hpush, htarget⟩
                rw [htarget, hpush] at hrest
                have hrestComp :=
                  ih.right ⟨(rule, B :: rest), hhelper⟩ q _
                    targetInput _ targetStack hrest
                rcases hrestComp with ⟨tail, hstack, htailComp⟩
                exact Computes.step
                  (by
                    have hstack' := hstack
                    simp [Word.Concat] at hstack'
                    rw [hstack']
                    simpa [hpop, Word.Concat, List.append_assoc] using
                      (Step.epsilon (M := M) (restStack := tail)
                        htransitionM))
                  htailComp
      · intro helper q sourceInput targetInput sourceStack targetStack hcomp
        rcases computesIn_succ_inv hcomp with ⟨mid, hstep, hrest⟩
        cases hstep with
        | read htransition =>
            have hcases :=
              popNormalize_helper_transition_cases
                (presentation := presentation) helper htransition
            cases hcases.left
        | epsilon htransition =>
            have hcases :=
              popNormalize_helper_transition_cases
                (presentation := presentation) helper htransition
            rcases hcases with ⟨_hinput, hcase⟩
            rcases hcase with hnil | hcons
            · rcases hnil with ⟨hremaining, hpop, htarget, hpush⟩
              rw [htarget, hpush] at hrest
              have hrestComp :=
                ih.left helper.val.1.target q _ targetInput _
                  targetStack hrest
              refine ⟨_, ?_, by simpa [hpush] using hrestComp⟩
              simp [hremaining, hpop, Word.Concat]
            · rcases hcons with
                ⟨A, rest, htail, hremaining, hpop, htarget, hpush⟩
              rw [htarget, hpush] at hrest
              have hrestComp :=
                ih.right ⟨(helper.val.1, rest), htail⟩ q _
                  targetInput _ targetStack hrest
              rcases hrestComp with ⟨tail, hstack, htailComp⟩
              refine ⟨tail, ?_, htailComp⟩
              have hstack' := hstack
              simp [Word.Concat] at hstack'
              rw [hstack']
              simp [hremaining, hpop, Word.Concat]

theorem popNormalize_compresses_original_computesIn
    {M : PDA input stack state} (presentation : FinitePresentation M)
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    {sourceStack targetStack : Word stack}
    (hcomp :
      ComputesIn (PopNormalize M presentation) n
        { state := Sum.inl p, unread := sourceInput,
          stack := sourceStack }
        { state := Sum.inl q, unread := targetInput,
          stack := targetStack }) :
    Computes M
      { state := p, unread := sourceInput, stack := sourceStack }
      { state := q, unread := targetInput, stack := targetStack } :=
  (popNormalize_compresses_original_and_helper_computesIn presentation n).left
    p q sourceInput targetInput sourceStack targetStack hcomp

theorem popNormalize_compresses_original_computes
    {M : PDA input stack state} (presentation : FinitePresentation M)
    {p q : state} {sourceInput targetInput : Word input}
    {sourceStack targetStack : Word stack}
    (hcomp :
      Computes (PopNormalize M presentation)
        { state := Sum.inl p, unread := sourceInput,
          stack := sourceStack }
        { state := Sum.inl q, unread := targetInput,
          stack := targetStack }) :
    Computes M
      { state := p, unread := sourceInput, stack := sourceStack }
      { state := q, unread := targetInput, stack := targetStack } := by
  rcases computes_exists_length hcomp with ⟨n, hn⟩
  exact popNormalize_compresses_original_computesIn presentation hn

theorem popNormalize_accepts_original_of_accepts
    {M : PDA input stack state} (presentation : FinitePresentation M)
    {w : Word input}
    (h : Accepts (PopNormalize M presentation) w) :
    Accepts M w := by
  rcases h with ⟨q, haccept, hcomp⟩
  cases q with
  | inl q =>
      refine ⟨q, haccept, ?_⟩
      simpa [initial] using
        popNormalize_compresses_original_computes
          (M := M) (presentation := presentation) hcomp
  | inr helper =>
      cases haccept

theorem popNormalize_acceptedLanguage_subset_original
    {M : PDA input stack state} (presentation : FinitePresentation M) :
    Language.Subset (AcceptedLanguage (PopNormalize M presentation))
      (AcceptedLanguage M) := by
  intro w hw
  exact popNormalize_accepts_original_of_accepts presentation hw

theorem popNormalize_acceptedLanguage_exact
    {M : PDA input stack state} (presentation : FinitePresentation M) :
    Language.Equal (AcceptedLanguage (PopNormalize M presentation))
      (AcceptedLanguage M) := by
  intro w
  constructor
  · intro h
    exact popNormalize_accepts_original_of_accepts presentation h
  · intro h
    exact popNormalize_accepts_of_accepts presentation h

end PDA

end Grammars
end FoC
