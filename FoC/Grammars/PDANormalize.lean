import FoC.Grammars.CFG
import FoC.Grammars.PDA

set_option doc.verso true

/-!
# PDA pop normalization

The PDA-to-CFG construction in {module -checked}`FoC.Grammars.PDAToCFG` is exact for PDAs whose
transitions pop either no stack symbol or exactly one stack symbol.  A general
finite presentation can contain transitions that pop a longer stack word.  This
module builds the finite helper-state machine that splits those longer pops
into one-symbol pops while preserving the original stack alphabet.

## Helper states

Long pop words are represented by helper states that remember the original
transition rule and the remaining suffix that still has to be popped.
-/

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace PDA

/-!
# Finite helper-state enumeration

The helper states are finite because they are built from the finite list of
transition rules and the finite list of suffixes of each pop word.
-/

def suffixesWithNil : Word stack -> List (Word stack)
  | [] => [[]]
  | A :: rest => (A :: rest) :: suffixesWithNil rest

theorem suffixesWithNil_self_mem (pop : Word stack) :
    pop ∈ suffixesWithNil pop := by
  cases pop with
  | nil => simp [suffixesWithNil]
  | cons A rest => simp [suffixesWithNil]

theorem suffixesWithNil_tail_mem {A : stack} {rest pop : Word stack}
    (h : A :: rest ∈ suffixesWithNil pop) :
    rest ∈ suffixesWithNil pop := by
  induction pop with
  | nil =>
      cases h with
      | tail _ htail => cases htail
  | cons B more ih =>
      cases h with
      | head =>
          simp [suffixesWithNil]
          right
          exact suffixesWithNil_self_mem rest
      | tail _ htail =>
          simp [suffixesWithNil]
          right
          exact ih htail

def popNormalizeHelperRemainders : Word stack -> List (Word stack)
  | [] => []
  | _ :: [] => []
  | _ :: rest => suffixesWithNil rest

def popNormalizeHelperPairs {M : PDA input stack state}
    (presentation : FinitePresentation M) :
    List (TransitionRule input stack state × Word stack) :=
  presentation.transitionRules.flatMap fun rule =>
    (popNormalizeHelperRemainders rule.pop).map fun remaining =>
      (rule, remaining)

theorem popNormalizeHelperPairs_mem {M : PDA input stack state}
    {presentation : FinitePresentation M}
    {rule : TransitionRule input stack state} {remaining : Word stack}
    (hrule : rule ∈ presentation.transitionRules)
    (hremaining : remaining ∈ popNormalizeHelperRemainders rule.pop) :
    (rule, remaining) ∈ popNormalizeHelperPairs presentation := by
  unfold popNormalizeHelperPairs
  apply List.mem_flatMap.mpr
  refine ⟨rule, hrule, ?_⟩
  exact List.mem_map.mpr ⟨remaining, hremaining, rfl⟩

theorem popNormalizeHelperPairs_tail_mem {M : PDA input stack state}
    {presentation : FinitePresentation M}
    {rule : TransitionRule input stack state} {A : stack}
    {rest : Word stack}
    (h : (rule, A :: rest) ∈ popNormalizeHelperPairs presentation) :
    (rule, rest) ∈ popNormalizeHelperPairs presentation := by
  unfold popNormalizeHelperPairs at h ⊢
  rcases List.mem_flatMap.mp h with ⟨baseRule, hbase, hrem⟩
  rcases List.mem_map.mp hrem with ⟨remaining, hremaining, hpair⟩
  injection hpair with hrule hremainingEq
  subst baseRule
  subst remaining
  apply List.mem_flatMap.mpr
  refine ⟨rule, hbase, ?_⟩
  apply List.mem_map.mpr
  refine ⟨rest, ?_, rfl⟩
  generalize hpopEq : rule.pop = originalPop at hremaining ⊢
  cases originalPop with
  | nil =>
      simp [popNormalizeHelperRemainders] at hremaining
  | cons first tail =>
      cases tail with
      | nil =>
          simp [popNormalizeHelperRemainders] at hremaining
      | cons second more =>
          have htail :
              A :: rest ∈ suffixesWithNil (second :: more) := by
            simpa [popNormalizeHelperRemainders] using hremaining
          exact suffixesWithNil_tail_mem htail

abbrev PopNormalizedState {M : PDA input stack state}
    (presentation : FinitePresentation M) :=
  state ⊕ { helper : TransitionRule input stack state × Word stack //
    helper ∈ popNormalizeHelperPairs presentation }

def popNormalizedStateFinite {M : PDA input stack state}
    (presentation : FinitePresentation M) :
    FiniteType (PopNormalizedState (M := M) presentation) where
  elems := (M.statesFinite.elems.map Sum.inl) ++
    (popNormalizeHelperPairs presentation).attach.map fun helper =>
      Sum.inr helper
  complete := by
    intro s
    cases s with
    | inl q =>
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨q, M.statesFinite.complete q, rfl⟩
    | inr helper =>
        apply List.mem_append_right
        exact List.mem_map.mpr
          ⟨helper,
            List.mem_attach (popNormalizeHelperPairs presentation) helper,
            rfl⟩

/-!
# Normalized transition rules

Original rules that pop zero or one stack symbol are copied directly.  Rules
with longer pop words are split into a first real transition followed by helper
transitions that pop one symbol at a time.
-/

def popNormalizedDirectTransitionRulesForRule
    {M : PDA input stack state} (presentation : FinitePresentation M)
    (rule : TransitionRule input stack state) :
    List (TransitionRule input stack
      (PopNormalizedState (M := M) presentation)) :=
  match rule.pop with
  | [] =>
      let normalized : TransitionRule input stack
          (PopNormalizedState (M := M) presentation) :=
        { source := Sum.inl (rule.source),
          input? := rule.input?,
          pop := [],
          target := Sum.inl (rule.target),
          push := rule.push }
      [normalized]
  | A :: [] =>
      let normalized : TransitionRule input stack
          (PopNormalizedState (M := M) presentation) :=
        { source := Sum.inl (rule.source),
          input? := rule.input?,
          pop := [A],
          target := Sum.inl (rule.target),
          push := rule.push }
      [normalized]
  | _ :: _ :: _ => []

def popNormalizedStartSplitTransitionRulesForRule
    {M : PDA input stack state} (presentation : FinitePresentation M)
    (rule : { rule : TransitionRule input stack state //
      rule ∈ presentation.transitionRules }) :
    List (TransitionRule input stack
      (PopNormalizedState (M := M) presentation)) :=
  match hpop : rule.val.pop with
  | [] => []
  | _ :: [] => []
  | A :: B :: rest =>
      let remaining : Word stack := B :: rest
      have hremaining :
          remaining ∈ popNormalizeHelperRemainders rule.val.pop := by
        rw [hpop]
        simp [remaining, popNormalizeHelperRemainders, suffixesWithNil]
      have hhelper :
          (rule.val, remaining) ∈ popNormalizeHelperPairs presentation :=
        popNormalizeHelperPairs_mem rule.property hremaining
      let normalized : TransitionRule input stack
          (PopNormalizedState (M := M) presentation) :=
        { source := Sum.inl (rule.val.source),
          input? := rule.val.input?,
          pop := [A],
          target := Sum.inr ⟨(rule.val, remaining), hhelper⟩,
          push := [] }
      [normalized]

def popNormalizedHelperTransitionRule
    {M : PDA input stack state} (presentation : FinitePresentation M)
    (helper : { helper : TransitionRule input stack state × Word stack //
      helper ∈ popNormalizeHelperPairs presentation }) :
    TransitionRule input stack
      (PopNormalizedState (M := M) presentation) :=
  match hremaining : helper.val.2 with
  | [] =>
      { source := Sum.inr helper,
        input? := none,
        pop := [],
        target := Sum.inl (helper.val.1.target),
        push := helper.val.1.push }
  | A :: rest =>
      have hpair :
          (helper.val.1, A :: rest) ∈
            popNormalizeHelperPairs presentation := by
        cases helper with
        | mk pair hprop =>
            cases pair with
            | mk base remaining =>
                simp at hremaining ⊢
                subst remaining
                exact hprop
      have htail :
          (helper.val.1, rest) ∈ popNormalizeHelperPairs presentation :=
        popNormalizeHelperPairs_tail_mem hpair
      { source := Sum.inr helper,
        input? := none,
        pop := [A],
        target := Sum.inr ⟨(helper.val.1, rest), htail⟩,
        push := [] }

def popNormalizedTransitionRules {M : PDA input stack state}
    (presentation : FinitePresentation M) :
    List (TransitionRule input stack
      (PopNormalizedState (M := M) presentation)) :=
  presentation.transitionRules.flatMap
    (popNormalizedDirectTransitionRulesForRule presentation) ++
  presentation.transitionRules.attach.flatMap
    (popNormalizedStartSplitTransitionRulesForRule presentation) ++
  (popNormalizeHelperPairs presentation).attach.map
    (popNormalizedHelperTransitionRule presentation)

/-!
# Pop-bound proof

The generated finite presentation satisfies the normal-form condition: every
transition pops either no symbol or exactly one stack symbol.
-/

theorem popNormalizedDirectTransitionRulesForRule_popsAtMostOne
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {base : TransitionRule input stack state}
    {rule : TransitionRule input stack
      (PopNormalizedState (M := M) presentation)}
    (h : rule ∈
      popNormalizedDirectTransitionRulesForRule presentation base) :
    rule.pop = [] ∨ exists A : stack, rule.pop = [A] := by
  unfold popNormalizedDirectTransitionRulesForRule at h
  split at h
  · simp at h
    rw [h]
    exact Or.inl rfl
  · rename_i A hpop
    simp at h
    rw [h]
    exact Or.inr ⟨A, rfl⟩
  · simp at h

theorem popNormalizedStartSplitTransitionRulesForRule_popsAtMostOne
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {base : { rule : TransitionRule input stack state //
      rule ∈ presentation.transitionRules }}
    {rule : TransitionRule input stack
      (PopNormalizedState (M := M) presentation)}
    (h : rule ∈
      popNormalizedStartSplitTransitionRulesForRule presentation base) :
    rule.pop = [] ∨ exists A : stack, rule.pop = [A] := by
  unfold popNormalizedStartSplitTransitionRulesForRule at h
  split at h
  · simp at h
  · simp at h
  · rename_i A B rest hpop
    simp at h
    rw [h]
    exact Or.inr ⟨A, rfl⟩

theorem popNormalizedHelperTransitionRule_popsAtMostOne
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (helper : { helper : TransitionRule input stack state × Word stack //
      helper ∈ popNormalizeHelperPairs presentation }) :
    (popNormalizedHelperTransitionRule presentation helper).pop = [] ∨
      exists A : stack,
        (popNormalizedHelperTransitionRule presentation helper).pop = [A] := by
  unfold popNormalizedHelperTransitionRule
  split
  · exact Or.inl rfl
  · rename_i A rest hremaining
    exact Or.inr ⟨A, rfl⟩

theorem popNormalizedTransitionRules_popsAtMostOne
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {rule : TransitionRule input stack
      (PopNormalizedState (M := M) presentation)}
    (h : rule ∈ popNormalizedTransitionRules presentation) :
    rule.pop = [] ∨ exists A : stack, rule.pop = [A] := by
  unfold popNormalizedTransitionRules at h
  simp only [List.mem_append] at h
  rcases h with (hDirect | hStart) | hHelper
  · rcases List.mem_flatMap.mp hDirect with ⟨base, _hbase, hrule⟩
    exact popNormalizedDirectTransitionRulesForRule_popsAtMostOne hrule
  · rcases List.mem_flatMap.mp hStart with ⟨base, _hbase, hrule⟩
    exact popNormalizedStartSplitTransitionRulesForRule_popsAtMostOne hrule
  · rcases List.mem_map.mp hHelper with ⟨helper, _hhelper, hEq⟩
    rw [← hEq]
    exact popNormalizedHelperTransitionRule_popsAtMostOne helper

def PopNormalize (M : PDA input stack state)
    (presentation : FinitePresentation M) :
    PDA input stack (PopNormalizedState (M := M) presentation) where
  start := Sum.inl (M.start)
  transition := fun q a? pop r push =>
    exists rule, rule ∈ popNormalizedTransitionRules presentation ∧
      rule.Applies q a? pop r push
  accept := fun q =>
    match q with
    | Sum.inl s => M.accept s
    | Sum.inr _ => False
  statesFinite := popNormalizedStateFinite presentation

def popNormalizeFinitePresentation
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    FinitePresentation (PopNormalize M presentation) where
  stackFinite := presentation.stackFinite
  transitionRules := popNormalizedTransitionRules presentation
  transition_complete := by
    intro q a? pop r push
    rfl
  acceptingStates := presentation.acceptingStates.map Sum.inl
  accept_complete := by
    intro q
    cases q with
    | inl s =>
        constructor
        · intro hs
          exact List.mem_map.mpr
            ⟨s, (presentation.accept_complete s).mp hs, rfl⟩
        · intro hmem
          rcases List.mem_map.mp hmem with ⟨t, ht, heq⟩
          injection heq with hst
          subst t
          exact (presentation.accept_complete s).mpr ht
    | inr helper =>
        constructor
        · intro hfalse
          cases hfalse
        · intro hmem
          rcases List.mem_map.mp hmem with ⟨t, ht, heq⟩
          cases heq

theorem popNormalize_popsAtMostOne
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    PopsAtMostOne (PopNormalize M presentation) := by
  intro q a? pop r push htransition
  rcases htransition with ⟨rule, hrule, happlies⟩
  have hpop := popNormalizedTransitionRules_popsAtMostOne hrule
  rcases happlies with ⟨_hsource, _hinput, hpopEq, _htarget, _hpush⟩
  cases hpop with
  | inl hnil =>
      left
      exact hpopEq ▸ hnil
  | inr hsingle =>
      rcases hsingle with ⟨A, hA⟩
      right
      exact ⟨A, hpopEq ▸ hA⟩

theorem popNormalize_hasFinitePresentation
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    HasFinitePresentation (PopNormalize M presentation) :=
  Nonempty.intro (popNormalizeFinitePresentation M presentation)

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
