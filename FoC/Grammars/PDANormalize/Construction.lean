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

end PDA

end Grammars
end FoC
