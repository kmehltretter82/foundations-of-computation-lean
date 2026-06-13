import FoC.Grammars.PDANormalize.Construction

set_option doc.verso true

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace PDA

/-!
# Simulating original transitions

The remaining lemmas show that each original transition can be simulated by a
finite computation in the normalized PDA.
-/

def popNormalizeConfiguration {M : PDA input stack state}
    (presentation : FinitePresentation M)
    (c : Configuration input stack state) :
    Configuration input stack (PopNormalizedState (M := M) presentation) where
  state := Sum.inl c.state
  unread := c.unread
  stack := c.stack

theorem popNormalize_direct_transition_nil
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {rule : TransitionRule input stack state}
    (hrule : rule ∈ presentation.transitionRules)
    (hpop : rule.pop = []) :
    (PopNormalize M presentation).transition (Sum.inl rule.source)
      rule.input? [] (Sum.inl rule.target) rule.push := by
  refine ⟨
    { source := Sum.inl rule.source,
      input? := rule.input?,
      pop := [],
      target := Sum.inl rule.target,
      push := rule.push }, ?_, ?_⟩
  · unfold popNormalizedTransitionRules
    simp only [List.mem_append]
    left
    left
    apply List.mem_flatMap.mpr
    refine ⟨rule, hrule, ?_⟩
    unfold popNormalizedDirectTransitionRulesForRule
    rw [hpop]
    simp
  · simp [TransitionRule.Applies]

theorem popNormalize_direct_transition_single
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {rule : TransitionRule input stack state} {A : stack}
    (hrule : rule ∈ presentation.transitionRules)
    (hpop : rule.pop = [A]) :
    (PopNormalize M presentation).transition (Sum.inl rule.source)
      rule.input? [A] (Sum.inl rule.target) rule.push := by
  refine ⟨
    { source := Sum.inl rule.source,
      input? := rule.input?,
      pop := [A],
      target := Sum.inl rule.target,
      push := rule.push }, ?_, ?_⟩
  · unfold popNormalizedTransitionRules
    simp only [List.mem_append]
    left
    left
    apply List.mem_flatMap.mpr
    refine ⟨rule, hrule, ?_⟩
    unfold popNormalizedDirectTransitionRulesForRule
    rw [hpop]
    simp
  · simp [TransitionRule.Applies]

theorem popNormalize_start_split_transition_exists
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {rule : TransitionRule input stack state} {A B : stack}
    {rest : Word stack}
    (hrule : rule ∈ presentation.transitionRules)
    (hpop : rule.pop = A :: B :: rest) :
    exists hhelper : (rule, B :: rest) ∈ popNormalizeHelperPairs presentation,
      (PopNormalize M presentation).transition (Sum.inl rule.source)
        rule.input? [A] (Sum.inr ⟨(rule, B :: rest), hhelper⟩) [] := by
  have hremaining :
      B :: rest ∈ popNormalizeHelperRemainders rule.pop := by
    rw [hpop]
    exact suffixesWithNil_self_mem (B :: rest)
  let hhelper : (rule, B :: rest) ∈ popNormalizeHelperPairs presentation :=
    popNormalizeHelperPairs_mem hrule hremaining
  refine ⟨hhelper, ?_⟩
  refine ⟨
    { source := Sum.inl rule.source,
      input? := rule.input?,
      pop := [A],
      target := Sum.inr ⟨(rule, B :: rest), hhelper⟩,
      push := [] }, ?_, ?_⟩
  · unfold popNormalizedTransitionRules
    simp only [List.mem_append]
    left
    right
    apply List.mem_flatMap.mpr
    refine ⟨⟨rule, hrule⟩, ?_⟩
    constructor
    · exact List.mem_attach _ ⟨rule, hrule⟩
    · unfold popNormalizedStartSplitTransitionRulesForRule
      split
      · rename_i hcase
        rw [hcase] at hpop
        cases hpop
      · rename_i head hcase
        rw [hcase] at hpop
        cases hpop
      · rename_i A' B' rest' hcase
        have hsame : A' :: B' :: rest' = A :: B :: rest :=
          hcase.symm.trans hpop
        injection hsame with hA htail
        injection htail with hB hrest
        subst A'
        subst B'
        subst rest'
        simp
  · simp [TransitionRule.Applies]

theorem popNormalize_helper_transition_nil
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (helper : { helper : TransitionRule input stack state × Word stack //
      helper ∈ popNormalizeHelperPairs presentation })
    (hremaining : helper.val.2 = []) :
    (PopNormalize M presentation).transition (Sum.inr helper) none []
      (Sum.inl helper.val.1.target) helper.val.1.push := by
  cases helper with
  | mk pair hprop =>
      cases pair with
      | mk rule remaining =>
          simp at hremaining
          subst remaining
          refine ⟨
            popNormalizedHelperTransitionRule presentation ⟨(rule, []), hprop⟩,
            ?_, ?_⟩
          · unfold popNormalizedTransitionRules
            simp only [List.mem_append]
            right
            apply List.mem_map.mpr
            refine ⟨⟨(rule, []), hprop⟩, List.mem_attach _ _, rfl⟩
          · simp [popNormalizedHelperTransitionRule,
              TransitionRule.Applies]

theorem popNormalize_helper_transition_cons
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (helper : { helper : TransitionRule input stack state × Word stack //
      helper ∈ popNormalizeHelperPairs presentation })
    {A : stack} {rest : Word stack}
    (hremaining : helper.val.2 = A :: rest) :
    exists htail : (helper.val.1, rest) ∈
        popNormalizeHelperPairs presentation,
      (PopNormalize M presentation).transition (Sum.inr helper) none [A]
        (Sum.inr ⟨(helper.val.1, rest), htail⟩) [] := by
  cases helper with
  | mk pair hprop =>
      cases pair with
      | mk rule remaining =>
          simp at hremaining
          subst remaining
          have hpair :
              (rule, A :: rest) ∈ popNormalizeHelperPairs presentation :=
            hprop
          let htail : (rule, rest) ∈
              popNormalizeHelperPairs presentation :=
            popNormalizeHelperPairs_tail_mem hpair
          refine ⟨htail, ?_⟩
          refine ⟨
            popNormalizedHelperTransitionRule presentation
              ⟨(rule, A :: rest), hprop⟩, ?_, ?_⟩
          · unfold popNormalizedTransitionRules
            simp only [List.mem_append]
            right
            apply List.mem_map.mpr
            refine ⟨⟨(rule, A :: rest), hprop⟩,
              List.mem_attach _ _, rfl⟩
          · simp [popNormalizedHelperTransitionRule,
              TransitionRule.Applies]

/-!
Once the normalized machine has entered a helper state, no more input is read.
The helper state remembers the original transition rule and the part of its
pop word that still has to be consumed.  The next lemma packages that invariant:
starting with exactly the remembered suffix on top of the stack, the helper
states remove it one symbol at a time and then install the original push word.
-/

theorem popNormalize_helper_computes_aux
    {M : PDA input stack state} (presentation : FinitePresentation M)
    (rule : TransitionRule input stack state)
    (remaining : Word stack)
    (hpair : (rule, remaining) ∈ popNormalizeHelperPairs presentation) :
    forall unread tail,
      Computes (PopNormalize M presentation)
        { state := Sum.inr ⟨(rule, remaining), hpair⟩,
          unread := unread,
          stack := Word.Concat remaining tail }
        { state := Sum.inl rule.target,
          unread := unread,
          stack := Word.Concat rule.push tail } := by
  induction remaining with
  | nil =>
      intro unread tail
      let helper : { helper : TransitionRule input stack state × Word stack //
          helper ∈ popNormalizeHelperPairs presentation } :=
        ⟨(rule, []), hpair⟩
      have htransition :
          (PopNormalize M presentation).transition (Sum.inr helper) none []
            (Sum.inl rule.target) rule.push :=
        popNormalize_helper_transition_nil (M := M)
          (presentation := presentation) helper rfl
      have hstep :
          Step (PopNormalize M presentation)
            { state := Sum.inr helper, unread := unread,
              stack := Word.Concat ([] : Word stack) tail }
            { state := Sum.inl rule.target, unread := unread,
              stack := Word.Concat rule.push tail } := by
        simpa [Word.Concat] using
          Step.epsilon (M := PopNormalize M presentation)
            (unread := unread) (restStack := tail) htransition
      exact computes_of_step hstep
  | cons A rest ih =>
      intro unread tail
      let helper : { helper : TransitionRule input stack state × Word stack //
          helper ∈ popNormalizeHelperPairs presentation } :=
        ⟨(rule, A :: rest), hpair⟩
      rcases popNormalize_helper_transition_cons (M := M)
        (presentation := presentation) helper rfl with
        ⟨htail, htransition⟩
      have hstep :
          Step (PopNormalize M presentation)
            { state := Sum.inr helper, unread := unread,
              stack := Word.Concat (A :: rest) tail }
            { state := Sum.inr ⟨(rule, rest), htail⟩,
              unread := unread,
              stack := Word.Concat rest tail } := by
        simpa [Word.Concat, List.append_assoc] using
          Step.epsilon (M := PopNormalize M presentation)
            (unread := unread) (restStack := Word.Concat rest tail)
            htransition
      exact Computes.step hstep (ih htail unread tail)

theorem popNormalize_rule_computes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {rule : TransitionRule input stack state}
    (hrule : rule ∈ presentation.transitionRules) :
    forall unread tail,
      Computes (PopNormalize M presentation)
        { state := Sum.inl rule.source,
          unread :=
            match rule.input? with
            | none => unread
            | some a => a :: unread,
          stack := Word.Concat rule.pop tail }
        { state := Sum.inl rule.target,
          unread := unread,
          stack := Word.Concat rule.push tail } := by
  intro unread tail
  cases hpop : rule.pop with
  | nil =>
      have htransition :
          (PopNormalize M presentation).transition (Sum.inl rule.source)
            rule.input? [] (Sum.inl rule.target) rule.push :=
        popNormalize_direct_transition_nil hrule hpop
      cases hinput : rule.input? with
      | none =>
          have htransition' :
              (PopNormalize M presentation).transition
                (Sum.inl rule.source) none []
                (Sum.inl rule.target) rule.push := by
            simpa [hinput] using htransition
          have hstep :
              Step (PopNormalize M presentation)
                { state := Sum.inl rule.source, unread := unread,
                  stack := Word.Concat rule.pop tail }
                { state := Sum.inl rule.target, unread := unread,
                  stack := Word.Concat rule.push tail } := by
            simpa [hpop, Word.Concat] using
              Step.epsilon (M := PopNormalize M presentation)
                (unread := unread) (restStack := tail) htransition'
          simpa [hinput, hpop] using computes_of_step hstep
      | some a =>
          have htransition' :
              (PopNormalize M presentation).transition
                (Sum.inl rule.source) (some a) []
                (Sum.inl rule.target) rule.push := by
            simpa [hinput] using htransition
          have hstep :
              Step (PopNormalize M presentation)
                { state := Sum.inl rule.source, unread := a :: unread,
                  stack := Word.Concat rule.pop tail }
                { state := Sum.inl rule.target, unread := unread,
                  stack := Word.Concat rule.push tail } := by
            simpa [hpop, Word.Concat] using
              Step.read (M := PopNormalize M presentation)
                (unread := unread) (restStack := tail) htransition'
          simpa [hinput, hpop] using computes_of_step hstep
  | cons A rest =>
      cases rest with
      | nil =>
          have hsingle : rule.pop = [A] := hpop
          have htransition :
              (PopNormalize M presentation).transition (Sum.inl rule.source)
                rule.input? [A] (Sum.inl rule.target) rule.push :=
            popNormalize_direct_transition_single hrule hsingle
          cases hinput : rule.input? with
          | none =>
              have htransition' :
                  (PopNormalize M presentation).transition
                    (Sum.inl rule.source) none [A]
                    (Sum.inl rule.target) rule.push := by
                simpa [hinput] using htransition
              have hstep :
                  Step (PopNormalize M presentation)
                    { state := Sum.inl rule.source, unread := unread,
                      stack := Word.Concat rule.pop tail }
                    { state := Sum.inl rule.target, unread := unread,
                      stack := Word.Concat rule.push tail } := by
                simpa [hpop, Word.Concat] using
                  Step.epsilon (M := PopNormalize M presentation)
                    (unread := unread) (restStack := tail) htransition'
              simpa [hinput, hpop] using computes_of_step hstep
          | some a =>
              have htransition' :
                  (PopNormalize M presentation).transition
                    (Sum.inl rule.source) (some a) [A]
                    (Sum.inl rule.target) rule.push := by
                simpa [hinput] using htransition
              have hstep :
                  Step (PopNormalize M presentation)
                    { state := Sum.inl rule.source, unread := a :: unread,
                      stack := Word.Concat rule.pop tail }
                    { state := Sum.inl rule.target, unread := unread,
                      stack := Word.Concat rule.push tail } := by
                simpa [hpop, Word.Concat] using
                  Step.read (M := PopNormalize M presentation)
                    (unread := unread) (restStack := tail) htransition'
              simpa [hinput, hpop] using computes_of_step hstep
      | cons B restTail =>
          rcases popNormalize_start_split_transition_exists
            (M := M) (presentation := presentation) hrule hpop with
            ⟨hhelper, hstart⟩
          have hhelpers :=
            popNormalize_helper_computes_aux (M := M)
              (presentation := presentation) rule (B :: restTail)
              hhelper unread tail
          cases hinput : rule.input? with
          | none =>
              have hstart' :
                  (PopNormalize M presentation).transition
                    (Sum.inl rule.source) none [A]
                    (Sum.inr ⟨(rule, B :: restTail), hhelper⟩) [] := by
                simpa [hinput] using hstart
              have hstep :
                  Step (PopNormalize M presentation)
                    { state := Sum.inl rule.source, unread := unread,
                      stack := Word.Concat rule.pop tail }
                    { state := Sum.inr ⟨(rule, B :: restTail), hhelper⟩,
                      unread := unread,
                      stack := Word.Concat (B :: restTail) tail } := by
                simpa [hpop, Word.Concat, List.append_assoc] using
                  Step.epsilon (M := PopNormalize M presentation)
                    (unread := unread)
                    (restStack := Word.Concat (B :: restTail) tail)
                    hstart'
              simpa [hinput, hpop] using Computes.step hstep hhelpers
          | some a =>
              have hstart' :
                  (PopNormalize M presentation).transition
                    (Sum.inl rule.source) (some a) [A]
                    (Sum.inr ⟨(rule, B :: restTail), hhelper⟩) [] := by
                simpa [hinput] using hstart
              have hstep :
                  Step (PopNormalize M presentation)
                    { state := Sum.inl rule.source, unread := a :: unread,
                      stack := Word.Concat rule.pop tail }
                    { state := Sum.inr ⟨(rule, B :: restTail), hhelper⟩,
                      unread := unread,
                      stack := Word.Concat (B :: restTail) tail } := by
                simpa [hpop, Word.Concat, List.append_assoc] using
                  Step.read (M := PopNormalize M presentation)
                    (unread := unread)
                    (restStack := Word.Concat (B :: restTail) tail)
                    hstart'
              simpa [hinput, hpop] using Computes.step hstep hhelpers

/-!
The forward simulation is now local.  A one-symbol pop in the original machine
becomes one normalized step, while a longer pop becomes a first normalized step
into a helper state followed by the helper computation above.  This is the
point where the normalization construction changes from bookkeeping lemmas into
an actual simulation theorem.
-/

theorem popNormalize_simulates_step
    {M : PDA input stack state} (presentation : FinitePresentation M)
    {c d : Configuration input stack state}
    (hstep : Step M c d) :
    Computes (PopNormalize M presentation)
      (popNormalizeConfiguration presentation c)
      (popNormalizeConfiguration presentation d) := by
  cases hstep with
  | read htransition =>
      rcases (presentation.transition_complete _ _ _ _ _).mp
        htransition with ⟨rule, hrule, happlies⟩
      rcases happlies with
        ⟨hsource, hinput, hpop, htarget, hpush⟩
      simpa [popNormalizeConfiguration, hsource, hinput, hpop, htarget,
        hpush] using
        popNormalize_rule_computes (M := M)
          (presentation := presentation) hrule _ _
  | epsilon htransition =>
      rcases (presentation.transition_complete _ _ _ _ _).mp
        htransition with ⟨rule, hrule, happlies⟩
      rcases happlies with
        ⟨hsource, hinput, hpop, htarget, hpush⟩
      simpa [popNormalizeConfiguration, hsource, hinput, hpop, htarget,
        hpush] using
        popNormalize_rule_computes (M := M)
          (presentation := presentation) hrule _ _

theorem popNormalize_simulates_computes
    {M : PDA input stack state} (presentation : FinitePresentation M)
    {c d : Configuration input stack state}
    (h : Computes M c d) :
    Computes (PopNormalize M presentation)
      (popNormalizeConfiguration presentation c)
      (popNormalizeConfiguration presentation d) := by
  induction h with
  | refl c =>
      exact Computes.refl _
  | step hstep _ ih =>
      exact computes_trans (popNormalize_simulates_step presentation hstep) ih

theorem popNormalize_accepts_of_accepts
    {M : PDA input stack state} (presentation : FinitePresentation M)
    {w : Word input}
    (h : Accepts M w) :
    Accepts (PopNormalize M presentation) w := by
  rcases h with ⟨q, hqAccept, hcomputes⟩
  refine ⟨Sum.inl q, ?_, ?_⟩
  · exact hqAccept
  · simpa [initial, popNormalizeConfiguration] using
      popNormalize_simulates_computes (M := M)
        (presentation := presentation) hcomputes

theorem acceptedLanguage_subset_popNormalize
    {M : PDA input stack state} (presentation : FinitePresentation M) :
    Language.Subset (AcceptedLanguage M)
      (AcceptedLanguage (PopNormalize M presentation)) := by
  intro w hw
  exact popNormalize_accepts_of_accepts presentation hw

end PDA

end Grammars
end FoC
