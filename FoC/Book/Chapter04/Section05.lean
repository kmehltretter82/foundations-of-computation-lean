import FoC.Book.Chapter04.Section04
import FoC.Grammars.CFL

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section05

/-!
# Chapter 4, Section 4.5: Non-Context-Free Languages

This section develops closure and pumping-lemma machinery for separating
languages from the context-free class. It combines finite-state automata from
{module}`FoC.Languages.DFA`, pushdown automata from {module}`FoC.Grammars.PDA`,
and context-free language wrappers from {module}`FoC.Grammars.CFL`.

The section has two complementary methods. Closure under intersection with a
regular language lets us filter a context-free language by a finite-state
property. The context-free Pumping Lemma gives a direct obstruction to being
context-free, used here for the language `{ a^n b^n c^n | n >= 0 }`.
-/

open Languages
open Grammars

/-!
# Intersecting PDAs with DFAs

The product construction runs a PDA and DFA in parallel. It is the main
closure tool for intersecting a PDA language with a regular language, and for
subtracting a regular language by intersecting with a DFA complement.

The PDA component owns the stack; the DFA component tracks only finite-state
information about the same consumed input. Epsilon PDA moves leave the DFA
state unchanged, while input-consuming PDA moves also advance the DFA.
-/

def PDAIntersectDFA (P : PDA input stack pstate) (D : DFA input dstate) :
    PDA input stack (pstate × dstate) where
  start := (P.start, D.start)
  transition := fun q input pop r push =>
    match input with
    | none => P.transition q.1 none pop r.1 push ∧ r.2 = q.2
    | some a => P.transition q.1 (some a) pop r.1 push ∧ r.2 = D.step q.2 a
  accept := fun q => P.accept q.1 ∧ D.accept q.2
  statesFinite := FiniteState.Product P.statesFinite D.statesFinite

structure DFAAcceptingPresentation (D : DFA input dstate) where
  acceptingStates : List dstate
  accept_complete : forall q, D.accept q <-> q ∈ acceptingStates

/-!
The product PDA must also have a finite presentation. The next definitions turn
each transition rule of the original PDA into one rule for every DFA state. For
epsilon PDA moves the DFA coordinate stays fixed; for input-consuming moves it
updates with {lit}`D.step`.
-/

noncomputable def dfaAcceptingPresentation (D : DFA input dstate) :
    DFAAcceptingPresentation D := by
  classical
  exact {
    acceptingStates := D.statesFinite.elems.filter (fun q => D.accept q),
    accept_complete := by
      intro q
      constructor
      · intro hq
        apply List.mem_filter.mpr
        constructor
        · exact D.statesFinite.complete q
        · simpa using hq
      · intro hq
        simpa using (List.mem_filter.mp hq).2 }

noncomputable def dfaComplementAcceptingPresentation (D : DFA input dstate) :
    DFAAcceptingPresentation (DFA.Complement D) :=
  dfaAcceptingPresentation (DFA.Complement D)

def pdaIntersectDFA_transitionRule
    (D : DFA input dstate)
    (rule : PDA.TransitionRule input stack pstate)
    (q : dstate) : PDA.TransitionRule input stack (pstate × dstate) :=
  { source := (rule.source, q),
    input? := rule.input?,
    pop := rule.pop,
    target :=
      (rule.target,
        match rule.input? with
        | none => q
        | some a => D.step q a),
    push := rule.push }

def pdaIntersectDFA_transitionRulesForRule
    (D : DFA input dstate)
    (rule : PDA.TransitionRule input stack pstate) :
    List (PDA.TransitionRule input stack (pstate × dstate)) :=
  D.statesFinite.elems.map (pdaIntersectDFA_transitionRule D rule)

def pdaIntersectDFA_transitionRules
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P) :
    List (PDA.TransitionRule input stack (pstate × dstate)) :=
  presentation.transitionRules.flatMap
    (pdaIntersectDFA_transitionRulesForRule D)

def pdaIntersectDFA_acceptingStates
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (accepting : DFAAcceptingPresentation D) :
    List (pstate × dstate) :=
  presentation.acceptingStates.flatMap
    (fun p => accepting.acceptingStates.map (fun q => (p, q)))

/-!
The longest proof in this block is just the finite-presentation check. It says
that a transition of the product machine is present exactly when it came from
one of the finitely many source PDA rules and one of the finitely many DFA
states.
-/

theorem pdaIntersectDFA_transition_complete
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P) :
    forall q a? pop r push,
      (PDAIntersectDFA P D).transition q a? pop r push <->
        exists rule,
          rule ∈ pdaIntersectDFA_transitionRules P D presentation ∧
            rule.Applies q a? pop r push := by
  intro q a? pop r push
  constructor
  · intro h
    cases a? with
    | none =>
        rcases h with ⟨hP, hr⟩
        rcases (presentation.transition_complete
            q.1 none pop r.1 push).mp hP with
          ⟨baseRule, hbaseRule, hbaseApplies⟩
        refine
          ⟨pdaIntersectDFA_transitionRule D baseRule q.2, ?_, ?_⟩
        · unfold pdaIntersectDFA_transitionRules
          apply List.mem_flatMap.mpr
          refine ⟨baseRule, hbaseRule, ?_⟩
          unfold pdaIntersectDFA_transitionRulesForRule
          exact List.mem_map.mpr
            ⟨q.2, D.statesFinite.complete q.2, rfl⟩
        · rcases hbaseApplies with
            ⟨hsource, hinput, hpop, htarget, hpush⟩
          have htargetPair : (baseRule.target, q.2) = r := by
            apply Prod.ext
            · exact htarget
            · exact hr.symm
          simp [PDA.TransitionRule.Applies,
            pdaIntersectDFA_transitionRule, hsource, hinput, hpop,
            hpush, htargetPair]
    | some a =>
        rcases h with ⟨hP, hr⟩
        rcases (presentation.transition_complete
            q.1 (some a) pop r.1 push).mp hP with
          ⟨baseRule, hbaseRule, hbaseApplies⟩
        refine
          ⟨pdaIntersectDFA_transitionRule D baseRule q.2, ?_, ?_⟩
        · unfold pdaIntersectDFA_transitionRules
          apply List.mem_flatMap.mpr
          refine ⟨baseRule, hbaseRule, ?_⟩
          unfold pdaIntersectDFA_transitionRulesForRule
          exact List.mem_map.mpr
            ⟨q.2, D.statesFinite.complete q.2, rfl⟩
        · rcases hbaseApplies with
            ⟨hsource, hinput, hpop, htarget, hpush⟩
          have htargetPair : (baseRule.target, D.step q.2 a) = r := by
            apply Prod.ext
            · exact htarget
            · exact hr.symm
          simp [PDA.TransitionRule.Applies,
            pdaIntersectDFA_transitionRule, hsource, hinput, hpop,
            hpush, htargetPair]
  · intro h
    rcases h with ⟨rule, hrule, happlies⟩
    unfold pdaIntersectDFA_transitionRules at hrule
    rcases List.mem_flatMap.mp hrule with
      ⟨baseRule, hbaseRule, hgenerated⟩
    unfold pdaIntersectDFA_transitionRulesForRule at hgenerated
    rcases List.mem_map.mp hgenerated with ⟨d, _hd, hruleEq⟩
    subst rule
    rcases happlies with ⟨hsource, hinput, hpop, htarget, hpush⟩
    have hsourceP : baseRule.source = q.1 := by
      exact congrArg Prod.fst hsource
    have hd : d = q.2 := by
      exact congrArg Prod.snd hsource
    have hinputP : baseRule.input? = a? := by
      simpa [pdaIntersectDFA_transitionRule] using hinput
    have htargetP : baseRule.target = r.1 := by
      exact congrArg Prod.fst htarget
    have hP : P.transition q.1 a? pop r.1 push :=
      (presentation.transition_complete q.1 a? pop r.1 push).mpr
        ⟨baseRule, hbaseRule,
          ⟨hsourceP, hinputP, hpop, htargetP, hpush⟩⟩
    cases a? with
    | none =>
        constructor
        · exact hP
        · have htargetD : d = r.2 := by
            have htargetSecond := congrArg Prod.snd htarget
            simpa [pdaIntersectDFA_transitionRule, hinputP] using
              htargetSecond
          exact htargetD.symm.trans hd
    | some a =>
        constructor
        · exact hP
        · have htargetD : D.step d a = r.2 := by
            have htargetSecond := congrArg Prod.snd htarget
            simpa [pdaIntersectDFA_transitionRule, hinputP] using
              htargetSecond
          simpa [hd] using htargetD.symm

theorem pdaIntersectDFA_accept_complete
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (accepting : DFAAcceptingPresentation D) :
    forall q,
      (PDAIntersectDFA P D).accept q <->
        q ∈ pdaIntersectDFA_acceptingStates P D presentation accepting := by
  intro q
  constructor
  · intro h
    unfold pdaIntersectDFA_acceptingStates
    apply List.mem_flatMap.mpr
    refine ⟨q.1, (presentation.accept_complete q.1).mp h.left, ?_⟩
    exact List.mem_map.mpr
      ⟨q.2, (accepting.accept_complete q.2).mp h.right, rfl⟩
  · intro h
    unfold pdaIntersectDFA_acceptingStates at h
    rcases List.mem_flatMap.mp h with ⟨p, hp, hpair⟩
    rcases List.mem_map.mp hpair with ⟨d, hd, hq⟩
    have hpAccept : P.accept p := (presentation.accept_complete p).mpr hp
    have hdAccept : D.accept d := (accepting.accept_complete d).mpr hd
    cases hq
    exact ⟨hpAccept, hdAccept⟩

def pdaIntersectDFA_finitePresentation
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (accepting : DFAAcceptingPresentation D) :
    PDA.FinitePresentation (PDAIntersectDFA P D) where
  stackFinite := presentation.stackFinite
  transitionRules := pdaIntersectDFA_transitionRules P D presentation
  transition_complete :=
    pdaIntersectDFA_transition_complete P D presentation
  acceptingStates :=
    pdaIntersectDFA_acceptingStates P D presentation accepting
  accept_complete :=
    pdaIntersectDFA_accept_complete P D presentation accepting

/-!
# Product Exactness

The lifting and projection lemmas relate computations of the product PDA to
computations of the original PDA and runs of the DFA. Their language-level
summary is exact intersection.

Exactness has two directions. A product computation projects to a PDA
computation and a DFA run, and a PDA computation whose input is accepted by
the DFA can be lifted to a product computation.
-/

noncomputable def pdaIntersectDFA_finitePresentation_auto
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P) :
    PDA.FinitePresentation (PDAIntersectDFA P D) :=
  pdaIntersectDFA_finitePresentation P D presentation
    (dfaAcceptingPresentation D)

/-!
The first exactness direction lifts a PDA computation into the product machine.
The DFA state is not guessed: after consuming the whole input it must be
{lit}`DFA.RunFrom D r c.unread`.
-/

theorem pda_intersect_dfa_lift_to_empty
    (P : PDA input stack pstate) (D : DFA input dstate)
    {c d : PDA.Configuration input stack pstate}
    (h : PDA.Computes P c d) (hd : d.unread = [])
    (r : dstate) :
    PDA.Computes (PDAIntersectDFA P D)
      { state := (c.state, r), unread := c.unread, stack := c.stack }
      { state := (d.state, DFA.RunFrom D r c.unread),
        unread := [], stack := d.stack } := by
  induction h generalizing r with
  | refl c =>
      rw [hd]
      simp [DFA.RunFrom]
      exact PDA.Computes.refl _
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          rename_i p s a unread pop push restStack
          have hprodStep : PDA.Step (PDAIntersectDFA P D)
              { state := (p, r),
                unread := a :: unread,
                stack := Word.Concat pop restStack }
              { state := (s, D.step r a),
                unread := unread,
                stack := Word.Concat push restStack } := by
            exact PDA.Step.read (M := PDAIntersectDFA P D)
              (unread := unread) (restStack := restStack)
              (And.intro htrans rfl)
          exact PDA.Computes.step hprodStep (ih hd (D.step r a))
      | epsilon htrans =>
          rename_i p s unread pop push restStack
          have hprodStep : PDA.Step (PDAIntersectDFA P D)
              { state := (p, r),
                unread := unread,
                stack := Word.Concat pop restStack }
              { state := (s, r),
                unread := unread,
                stack := Word.Concat push restStack } := by
            exact PDA.Step.epsilon (M := PDAIntersectDFA P D)
              (unread := unread) (restStack := restStack)
              (And.intro htrans rfl)
          exact PDA.Computes.step hprodStep (ih hd r)

/-!
The projection direction forgets the DFA coordinate. A companion lemma records
that the forgotten coordinate was exactly the DFA run on the consumed input.
Together they prove the product accepts precisely the intersection language.
-/

theorem pda_intersect_dfa_project_computation
    (P : PDA input stack pstate) (D : DFA input dstate)
    {c d : PDA.Configuration input stack (pstate × dstate)}
    (h : PDA.Computes (PDAIntersectDFA P D) c d) :
    PDA.Computes P
      { state := c.state.1, unread := c.unread, stack := c.stack }
      { state := d.state.1, unread := d.unread, stack := d.stack } := by
  induction h with
  | refl c =>
      exact PDA.Computes.refl _
  | step hstep _ ih =>
      cases hstep with
      | read htrans =>
          exact PDA.Computes.step
            (PDA.Step.read (M := P) htrans.left) ih
      | epsilon htrans =>
          exact PDA.Computes.step
            (PDA.Step.epsilon (M := P) htrans.left) ih

theorem pda_intersect_dfa_final_run
    (P : PDA input stack pstate) (D : DFA input dstate)
    {c d : PDA.Configuration input stack (pstate × dstate)}
    (h : PDA.Computes (PDAIntersectDFA P D) c d) (hd : d.unread = []) :
    d.state.2 = DFA.RunFrom D c.state.2 c.unread := by
  induction h with
  | refl c =>
      rw [hd]
      rfl
  | step hstep _ ih =>
      cases hstep with
      | read htrans =>
          rw [ih hd, htrans.right]
          rfl
      | epsilon htrans =>
          rw [ih hd, htrans.right]

theorem pda_intersect_dfa_accepted_language_exact
    (P : PDA input stack pstate) (D : DFA input dstate)
    (w : Word input) :
    w ∈ PDA.AcceptedLanguage (PDAIntersectDFA P D) <->
      w ∈ Language.Inter (PDA.AcceptedLanguage P) (DFA.Language D) := by
  constructor
  · intro h
    cases h with
    | intro q hq =>
        have hpdaComp :=
          pda_intersect_dfa_project_computation P D hq.right
        have hrun :=
          pda_intersect_dfa_final_run P D hq.right rfl
        have hrun' : q.2 = DFA.Run D w := by
          simpa [PDA.initial, PDAIntersectDFA, DFA.Run] using hrun
        constructor
        · exists q.1
          constructor
          · exact hq.left.left
          · simpa [PDA.initial, PDAIntersectDFA] using hpdaComp
        · unfold DFA.Language DFA.Accepts DFA.Run
          change D.accept (DFA.Run D w)
          rw [← hrun']
          exact hq.left.right
  · intro h
    cases h.left with
    | intro q hq =>
        exists (q, DFA.Run D w)
        constructor
        · constructor
          · exact hq.left
          · exact h.right
        · simpa [PDA.initial, PDAIntersectDFA, DFA.Run] using
            pda_intersect_dfa_lift_to_empty P D hq.right rfl D.start

/-!
# Context-Free Closure

Once the product PDA has a finite presentation, the PDA-to-CFG theorem turns
intersection and difference with DFA languages into context-free languages.
Some wrappers keep the older conditional exactness target explicit, while the
later theorems use the unconditional finite-presentation theorem.
-/

theorem pda_intersect_dfa_context_free_of_empty_summary_complete
    {input stack pstate dstate : Type}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (accepting : DFAAcceptingPresentation D)
    (hcomplete :
      Section04.EmptySummaryPDAComplete (PDAIntersectDFA P D)) :
    CFL.ContextFreeLanguage
      (Language.Inter (PDA.AcceptedLanguage P) (DFA.Language D)) := by
  let productPresentation :=
    pdaIntersectDFA_finitePresentation P D presentation accepting
  have hProduct :
      CFL.ContextFreeLanguage
        (PDA.AcceptedLanguage (PDAIntersectDFA P D)) :=
    Section04.finite_presentation_pda_context_free_of_empty_summary_complete
      (M := PDAIntersectDFA P D)
      (presentation := productPresentation) hcomplete
  rcases hProduct with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · exact Language.equal_trans hEq
      (fun w => pda_intersect_dfa_accepted_language_exact P D w)

theorem pda_intersect_dfa_context_free_of_empty_summary_complete_auto
    {input stack pstate dstate : Type}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (hcomplete :
      Section04.EmptySummaryPDAComplete (PDAIntersectDFA P D)) :
    CFL.ContextFreeLanguage
      (Language.Inter (PDA.AcceptedLanguage P) (DFA.Language D)) := by
  classical
  exact pda_intersect_dfa_context_free_of_empty_summary_complete
    P D presentation (dfaAcceptingPresentation D) hcomplete

theorem pda_intersect_dfa_context_free
    {input stack pstate dstate : Type}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P) :
    CFL.ContextFreeLanguage
      (Language.Inter (PDA.AcceptedLanguage P) (DFA.Language D)) := by
  let productPresentation :=
    pdaIntersectDFA_finitePresentation_auto P D presentation
  have hProduct :
      CFL.ContextFreeLanguage
        (PDA.AcceptedLanguage (PDAIntersectDFA P D)) :=
    Section04.finite_presentation_pda_context_free
      (M := PDAIntersectDFA P D)
      (presentation := productPresentation)
  rcases hProduct with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · exact Language.equal_trans hEq
      (fun w => pda_intersect_dfa_accepted_language_exact P D w)

theorem pda_diff_dfa_context_free_of_empty_summary_complete
    {input stack pstate dstate : Type}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (acceptingComplement :
      DFAAcceptingPresentation (DFA.Complement D))
    (hcomplete :
      Section04.EmptySummaryPDAComplete
        (PDAIntersectDFA P (DFA.Complement D))) :
    CFL.ContextFreeLanguage
      (Language.Diff (PDA.AcceptedLanguage P) (DFA.Language D)) := by
  have hProduct :=
    pda_intersect_dfa_context_free_of_empty_summary_complete
      P (DFA.Complement D) presentation acceptingComplement hcomplete
  rcases hProduct with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · intro w
    constructor
    · intro hw
      have hInter := (hEq w).mp hw
      constructor
      · exact hInter.left
      · intro hD
        exact (DFA.complement_accepts D w).mp hInter.right hD
    · intro hw
      apply (hEq w).mpr
      constructor
      · exact hw.left
      · exact (DFA.complement_accepts D w).mpr hw.right

theorem pda_diff_dfa_context_free_of_empty_summary_complete_auto
    {input stack pstate dstate : Type}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (hcomplete :
      Section04.EmptySummaryPDAComplete
        (PDAIntersectDFA P (DFA.Complement D))) :
    CFL.ContextFreeLanguage
      (Language.Diff (PDA.AcceptedLanguage P) (DFA.Language D)) := by
  classical
  exact pda_diff_dfa_context_free_of_empty_summary_complete
    P D presentation (dfaComplementAcceptingPresentation D) hcomplete

theorem pda_diff_dfa_context_free
    {input stack pstate dstate : Type}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P) :
    CFL.ContextFreeLanguage
      (Language.Diff (PDA.AcceptedLanguage P) (DFA.Language D)) := by
  have hProduct :=
    pda_intersect_dfa_context_free P (DFA.Complement D) presentation
  rcases hProduct with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · intro w
    constructor
    · intro hw
      have hInter := (hEq w).mp hw
      constructor
      · exact hInter.left
      · intro hD
        exact (DFA.complement_accepts D w).mp hInter.right hD
    · intro hw
      apply (hEq w).mpr
      constructor
      · exact hw.left
      · exact (DFA.complement_accepts D w).mpr hw.right

/-!
The following language-level wrappers remove the concrete product machine from
the statement. They say: if {lit}`L` is recognized by a finite-presentation PDA
and {lit}`R` is recognized by a DFA, then {lit}`L ∩ R` and {lit}`L \\ R` are
context-free.
-/

theorem finite_presentation_pda_language_inter_dfa_context_free_of_empty_summary_complete
    {input stack pstate dstate : Type}
    {L R : Language input}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (hP : Language.Equal (PDA.AcceptedLanguage P) L)
    (hD : Language.Equal (DFA.Language D) R)
    (hcomplete :
      Section04.EmptySummaryPDAComplete (PDAIntersectDFA P D)) :
    CFL.ContextFreeLanguage (Language.Inter L R) := by
  have hBase :=
    pda_intersect_dfa_context_free_of_empty_summary_complete_auto
      P D presentation hcomplete
  rcases hBase with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · intro w
    constructor
    · intro hw
      have hprod := (hEq w).mp hw
      exact And.intro ((hP w).mp hprod.left) ((hD w).mp hprod.right)
    · intro hw
      apply (hEq w).mpr
      exact And.intro ((hP w).mpr hw.left) ((hD w).mpr hw.right)

theorem finite_presentation_pda_language_inter_dfa_context_free
    {input stack pstate dstate : Type}
    {L R : Language input}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (hP : Language.Equal (PDA.AcceptedLanguage P) L)
    (hD : Language.Equal (DFA.Language D) R) :
    CFL.ContextFreeLanguage (Language.Inter L R) := by
  have hBase := pda_intersect_dfa_context_free P D presentation
  rcases hBase with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · intro w
    constructor
    · intro hw
      have hprod := (hEq w).mp hw
      exact And.intro ((hP w).mp hprod.left) ((hD w).mp hprod.right)
    · intro hw
      apply (hEq w).mpr
      exact And.intro ((hP w).mpr hw.left) ((hD w).mpr hw.right)

theorem finite_presentation_pda_language_diff_dfa_context_free_of_empty_summary_complete
    {input stack pstate dstate : Type}
    {L R : Language input}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (hP : Language.Equal (PDA.AcceptedLanguage P) L)
    (hD : Language.Equal (DFA.Language D) R)
    (hcomplete :
      Section04.EmptySummaryPDAComplete
        (PDAIntersectDFA P (DFA.Complement D))) :
    CFL.ContextFreeLanguage (Language.Diff L R) := by
  have hBase :=
    pda_diff_dfa_context_free_of_empty_summary_complete_auto
      P D presentation hcomplete
  rcases hBase with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · intro w
    constructor
    · intro hw
      have hdiff := (hEq w).mp hw
      constructor
      · exact (hP w).mp hdiff.left
      · intro hR
        exact hdiff.right ((hD w).mpr hR)
    · intro hw
      apply (hEq w).mpr
      constructor
      · exact (hP w).mpr hw.left
      · intro hDfa
        exact hw.right ((hD w).mp hDfa)

theorem finite_presentation_pda_language_diff_dfa_context_free
    {input stack pstate dstate : Type}
    {L R : Language input}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    (hP : Language.Equal (PDA.AcceptedLanguage P) L)
    (hD : Language.Equal (DFA.Language D) R) :
    CFL.ContextFreeLanguage (Language.Diff L R) := by
  have hBase := pda_diff_dfa_context_free P D presentation
  rcases hBase with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · intro w
    constructor
    · intro hw
      have hdiff := (hEq w).mp hw
      constructor
      · exact (hP w).mp hdiff.left
      · intro hR
        exact hdiff.right ((hD w).mpr hR)
    · intro hw
      apply (hEq w).mpr
      constructor
      · exact (hP w).mpr hw.left
      · intro hDfa
        exact hw.right ((hD w).mp hDfa)

/-!
# Recognizability Wrappers

The final group states the automaton-side closure theorems: PDA-recognizable
and finite-presentation PDA-recognizable languages are closed under
intersection with, and subtraction by, regular languages.

These wrappers translate the concrete product construction into the language
classes used in the book. They are also used later to subtract finite
languages from context-free languages.
-/

theorem pda_recognizable_inter_dfa_recognizable
    {L R : Language input}
    (hL : PDA.Recognizable L) (hR : DFA.Recognizable R) :
    PDA.Recognizable (Language.Inter L R) := by
  cases hL with
  | intro stack hstack =>
      cases hstack with
      | intro pstate hpstate =>
          cases hpstate with
          | intro P hP =>
              cases hR with
              | intro dstate hdstate =>
                  cases hdstate with
                  | intro D hD =>
                      exists stack
                      exists pstate × dstate
                      exists PDAIntersectDFA P D
                      intro w
                      constructor
                      · intro hw
                        have hExact :=
                          (pda_intersect_dfa_accepted_language_exact P D w).mp hw
                        constructor
                        · exact (hP w).mp hExact.left
                        · exact (hD w).mp hExact.right
                      · intro hw
                        exact (pda_intersect_dfa_accepted_language_exact P D w).mpr
                          (And.intro ((hP w).mpr hw.left) ((hD w).mpr hw.right))

theorem finite_presentation_pda_recognizable_inter_dfa
    {L R : Language input}
    (hL : PDA.FinitePresentationRecognizable L)
    {dstate : Type} (D : DFA input dstate)
    (hR : Language.Equal (DFA.Language D) R) :
    PDA.FinitePresentationRecognizable (Language.Inter L R) := by
  classical
  rcases hL with ⟨stack, pstate, P, presentation, hP⟩
  exists stack
  exists pstate × dstate
  exists PDAIntersectDFA P D
  exists pdaIntersectDFA_finitePresentation_auto P D presentation
  intro w
  constructor
  · intro hw
    have hExact :=
      (pda_intersect_dfa_accepted_language_exact P D w).mp hw
    exact And.intro ((hP w).mp hExact.left) ((hR w).mp hExact.right)
  · intro hw
    exact (pda_intersect_dfa_accepted_language_exact P D w).mpr
      (And.intro ((hP w).mpr hw.left) ((hR w).mpr hw.right))

theorem finite_presentation_pda_recognizable_inter_dfa_recognizable
    {L R : Language input}
    (hL : PDA.FinitePresentationRecognizable L)
    (hR : DFA.Recognizable R) :
    PDA.FinitePresentationRecognizable (Language.Inter L R) := by
  rcases hR with ⟨dstate, D, hD⟩
  exact finite_presentation_pda_recognizable_inter_dfa hL D hD

theorem finite_presentation_pda_recognizable_diff_dfa
    {L R : Language input}
    (hL : PDA.FinitePresentationRecognizable L)
    {dstate : Type} (D : DFA input dstate)
    (hR : Language.Equal (DFA.Language D) R) :
    PDA.FinitePresentationRecognizable (Language.Diff L R) := by
  have hComplement :
      Language.Equal (DFA.Language (DFA.Complement D)) (Language.Compl R) := by
    intro w
    constructor
    · intro hw hRmem
      exact (DFA.complement_accepts D w).mp hw ((hR w).mpr hRmem)
    · intro hw
      exact (DFA.complement_accepts D w).mpr (by
        intro hAccept
        exact hw ((hR w).mp hAccept))
  have hInter :=
    finite_presentation_pda_recognizable_inter_dfa
      hL (DFA.Complement D) hComplement
  simpa [Language.Diff, Language.Inter, Language.Compl,
    Foundation.FSet.Diff, Foundation.FSet.Inter, Foundation.FSet.Compl]
    using hInter

theorem finite_presentation_pda_recognizable_diff_dfa_recognizable
    {L R : Language input}
    (hL : PDA.FinitePresentationRecognizable L)
    (hR : DFA.Recognizable R) :
    PDA.FinitePresentationRecognizable (Language.Diff L R) := by
  rcases hR with ⟨dstate, D, hD⟩
  exact finite_presentation_pda_recognizable_diff_dfa hL D hD

/-!
The next group switches between the two equivalent viewpoints used in the
chapter: a context-free language can be represented by a CFG, and a finite CFG
can be converted into a finite-presentation PDA using the construction from
Section 4.4.
-/

theorem finite_production_context_free_pda_recognizable {input : Type}
    {L : Language input}
    (hL : CFL.FiniteProductionContextFreeLanguage L) :
    PDA.Recognizable L := by
  cases hL with
  | intro nonterminal hnt =>
      cases hnt with
      | intro G hG =>
          exists Symbol input nonterminal
          exists CFG.ToPDAState
          exists CFG.ToPDA G
          exact Language.equal_trans (CFG.toPDA_acceptedLanguage_exact G) hG.right

theorem finite_production_context_free_finite_presentation_pda_recognizable
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L : Language input}
    (hL : CFL.FiniteProductionContextFreeLanguage L) :
    PDA.FinitePresentationRecognizable L := by
  rcases hL with ⟨nonterminal, G, hG⟩
  exists Symbol input nonterminal
  exists CFG.ToPDAState
  exists CFG.ToPDA G
  exists CFG.toPDA_finitePresentation G inputFinite hG.left
  exact Language.equal_trans (CFG.toPDA_acceptedLanguage_exact G) hG.right

theorem context_free_language_pda_recognizable {input : Type}
    {L : Language input}
    (hL : CFL.ContextFreeLanguage L) :
    PDA.Recognizable L :=
  finite_production_context_free_pda_recognizable hL

theorem context_free_language_finite_presentation_pda_recognizable
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L : Language input}
    (hL : CFL.ContextFreeLanguage L) :
    PDA.FinitePresentationRecognizable L :=
  finite_production_context_free_finite_presentation_pda_recognizable
    inputFinite hL

theorem finite_list_dfa_recognizable (ws : List (Word input)) :
    DFA.Recognizable (fun w : Word input => w ∈ ws) :=
  RegularLanguage.regular_is_dfa_recognizable
    (RegularLanguage.finite_list_regular ws)

theorem finite_language_dfa_recognizable {M : Language input}
    (hM : Language.Finite M) :
    DFA.Recognizable M := by
  cases hM with
  | intro ws hws =>
      cases finite_list_dfa_recognizable ws with
      | intro state hstate =>
          cases hstate with
          | intro D hD =>
              exists state
              exists D
              intro w
              constructor
              · intro hw
                exact Foundation.ListEnumerates.right hws ((hD w).mp hw)
              · intro hw
                exact (hD w).mpr (Foundation.ListEnumerates.left hws hw)

theorem finite_language_complement_dfa_recognizable {M : Language input}
    (hM : Language.Finite M) :
    DFA.Recognizable (Language.Compl M) :=
  DFA.recognizable_complement (finite_language_dfa_recognizable hM)

theorem finite_presentation_pda_recognizable_diff_finite_list
    {L : Language input}
    (hL : PDA.FinitePresentationRecognizable L) (ws : List (Word input)) :
    PDA.FinitePresentationRecognizable
      (Language.Diff L (fun w : Word input => w ∈ ws)) :=
  finite_presentation_pda_recognizable_diff_dfa_recognizable hL
    (finite_list_dfa_recognizable ws)

theorem finite_presentation_pda_recognizable_diff_finite_language
    {L M : Language input}
    (hL : PDA.FinitePresentationRecognizable L) (hM : Language.Finite M) :
    PDA.FinitePresentationRecognizable (Language.Diff L M) :=
  finite_presentation_pda_recognizable_diff_dfa_recognizable hL
    (finite_language_dfa_recognizable hM)

theorem pda_recognizable_diff_dfa_recognizable {L R : Language input}
    (hL : PDA.Recognizable L) (hR : DFA.Recognizable R) :
    PDA.Recognizable (Language.Diff L R) := by
  simpa [Language.Diff, Language.Inter, Language.Compl, Foundation.FSet.Diff,
    Foundation.FSet.Inter, Foundation.FSet.Compl] using
    pda_recognizable_inter_dfa_recognizable hL
      (DFA.recognizable_complement hR)

theorem pda_recognizable_diff_finite_list {L : Language input}
    (hL : PDA.Recognizable L) (ws : List (Word input)) :
    PDA.Recognizable (Language.Diff L (fun w : Word input => w ∈ ws)) :=
  pda_recognizable_diff_dfa_recognizable hL
    (finite_list_dfa_recognizable ws)

theorem pda_recognizable_diff_finite_language {L M : Language input}
    (hL : PDA.Recognizable L) (hM : Language.Finite M) :
    PDA.Recognizable (Language.Diff L M) :=
  pda_recognizable_diff_dfa_recognizable hL
    (finite_language_dfa_recognizable hM)

theorem context_free_diff_finite_language_pda_recognizable
    {input : Type}
    {L M : Language input}
    (hL : CFL.ContextFreeLanguage L) (hM : Language.Finite M) :
    PDA.Recognizable (Language.Diff L M) :=
  pda_recognizable_diff_finite_language
    (context_free_language_pda_recognizable hL) hM

theorem context_free_diff_finite_language_finite_presentation_pda_recognizable
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L M : Language input}
    (hL : CFL.ContextFreeLanguage L) (hM : Language.Finite M) :
    PDA.FinitePresentationRecognizable (Language.Diff L M) :=
  finite_presentation_pda_recognizable_diff_finite_language
    (context_free_language_finite_presentation_pda_recognizable
      inputFinite hL) hM

theorem context_free_inter_dfa_context_free
    {input dstate : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (D : DFA input dstate)
    (hR : Language.Equal (DFA.Language D) R) :
    CFL.ContextFreeLanguage (Language.Inter L R) := by
  rcases context_free_language_finite_presentation_pda_recognizable
      inputFinite hL with
    ⟨stack, pstate, P, presentation, hP⟩
  exact finite_presentation_pda_language_inter_dfa_context_free
    P D presentation hP hR

theorem context_free_inter_dfa_recognizable_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (hR : DFA.Recognizable R) :
    CFL.ContextFreeLanguage (Language.Inter L R) := by
  rcases hR with ⟨dstate, D, hD⟩
  exact context_free_inter_dfa_context_free inputFinite hL D hD

theorem context_free_diff_dfa_context_free
    {input dstate : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (D : DFA input dstate)
    (hR : Language.Equal (DFA.Language D) R) :
    CFL.ContextFreeLanguage (Language.Diff L R) := by
  rcases context_free_language_finite_presentation_pda_recognizable
      inputFinite hL with
    ⟨stack, pstate, P, presentation, hP⟩
  exact finite_presentation_pda_language_diff_dfa_context_free
    P D presentation hP hR

theorem context_free_diff_dfa_recognizable_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (hR : DFA.Recognizable R) :
    CFL.ContextFreeLanguage (Language.Diff L R) := by
  rcases hR with ⟨dstate, D, hD⟩
  exact context_free_diff_dfa_context_free inputFinite hL D hD

theorem context_free_diff_finite_list_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (ws : List (Word input)) :
    CFL.ContextFreeLanguage
      (Language.Diff L (fun w : Word input => w ∈ ws)) :=
  context_free_diff_dfa_recognizable_context_free inputFinite hL
    (finite_list_dfa_recognizable ws)

theorem context_free_diff_finite_language_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L M : Language input}
    (hL : CFL.ContextFreeLanguage L) (hM : Language.Finite M) :
    CFL.ContextFreeLanguage (Language.Diff L M) :=
  context_free_diff_dfa_recognizable_context_free inputFinite hL
    (finite_language_dfa_recognizable hM)

/-!
# The {lit}`a^n b^n c^n` Witness Setup

The language `{ a^n b^n c^n | n >= 0 }` is the standard example that is not
context-free. The auxiliary languages `{ a^n b^n c^* }` and
`{ a^* b^n c^n }` are context-free, and their intersection is exactly
`{ a^n b^n c^n }`. This gives the closure-based nonclosure argument after the
pumping proof establishes the target language is not context-free.
-/

inductive ABC where
  | a
  | b
  | c
deriving DecidableEq

def anbncnBlockWord (n : Nat) : Word ABC :=
  Word.Concat (Word.RepeatSymbol ABC.a n)
    (Word.Concat (Word.RepeatSymbol ABC.b n) (Word.RepeatSymbol ABC.c n))

def anbncnLanguage : Language ABC :=
  fun w => exists n, w = anbncnBlockWord n

def abcAnBnWord (n : Nat) : Word ABC :=
  Word.Concat (Word.RepeatSymbol ABC.a n) (Word.RepeatSymbol ABC.b n)

def abcBnCnWord (n : Nat) : Word ABC :=
  Word.Concat (Word.RepeatSymbol ABC.b n) (Word.RepeatSymbol ABC.c n)

def anbnCstarWord (n k : Nat) : Word ABC :=
  Word.Concat (abcAnBnWord n) (Word.RepeatSymbol ABC.c k)

def astarBnCnWord (k n : Nat) : Word ABC :=
  Word.Concat (Word.RepeatSymbol ABC.a k) (abcBnCnWord n)

def abcAnBnLanguage : Language ABC :=
  fun w => exists n, w = abcAnBnWord n

def abcBnCnLanguage : Language ABC :=
  fun w => exists n, w = abcBnCnWord n

def abcAstarLanguage : Language ABC :=
  fun w => exists k, w = Word.RepeatSymbol ABC.a k

def abcCstarLanguage : Language ABC :=
  fun w => exists k, w = Word.RepeatSymbol ABC.c k

def anbnCstarLanguage : Language ABC :=
  fun w => exists n k, w = anbnCstarWord n k

def astarBnCnLanguage : Language ABC :=
  fun w => exists k n, w = astarBnCnWord k n

theorem abcAnBn_wrap_word (n : Nat) :
    ABC.a :: Word.Concat (abcAnBnWord n) [ABC.b] =
      abcAnBnWord (n + 1) := by
  unfold abcAnBnWord
  simp [Word.RepeatSymbol, Word.Concat]
  rw [show List.replicate (n + 1) ABC.a =
    ABC.a :: List.replicate n ABC.a by rfl]
  rw [Section01.replicate_succ_eq_append ABC.b n]
  simp

theorem abcBnCn_wrap_word (n : Nat) :
    ABC.b :: Word.Concat (abcBnCnWord n) [ABC.c] =
      abcBnCnWord (n + 1) := by
  unfold abcBnCnWord
  simp [Word.RepeatSymbol, Word.Concat]
  rw [show List.replicate (n + 1) ABC.b =
    ABC.b :: List.replicate n ABC.b by rfl]
  rw [Section01.replicate_succ_eq_append ABC.c n]
  simp

theorem abcCstar_cons_word (k : Nat) :
    ABC.c :: Word.RepeatSymbol ABC.c k =
      Word.RepeatSymbol ABC.c (k + 1) :=
  rfl

theorem abcAstar_cons_word (k : Nat) :
    ABC.a :: Word.RepeatSymbol ABC.a k =
      Word.RepeatSymbol ABC.a (k + 1) :=
  rfl

/-!
The witness grammars below are proved exact with a reusable soundness pattern.
Instead of inspecting a final derivation directly, we assign a language meaning
to each nonterminal and prove every production is sound for that meaning.
-/

theorem cfg_yields_sound_for_symbol_language
    {G : CFG terminal nonterminal}
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hprod : forall A rhs, G.produces A rhs -> forall w,
      w ∈ CFG.FormLanguage symbolLanguage rhs ->
        w ∈ symbolLanguage (Symbol.nonterminal A))
    {x y : SententialForm terminal nonterminal} {w : Word terminal}
    (h : CFG.Yields G x y)
    (hw : w ∈ CFG.FormLanguage symbolLanguage y) :
    w ∈ CFG.FormLanguage symbolLanguage x := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprodA hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hy] at hw
                          rw [hx]
                          exact CFG.formLanguage_replace_sound symbolLanguage
                            (hprod A rhs hprodA) hw

theorem cfg_derives_sound_for_symbol_language_aux
    {G : CFG terminal nonterminal}
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hterminal : forall a,
      Word.Symbol a ∈ symbolLanguage (Symbol.terminal a))
    (hprod : forall A rhs, G.produces A rhs -> forall w,
      w ∈ CFG.FormLanguage symbolLanguage rhs ->
        w ∈ symbolLanguage (Symbol.nonterminal A))
    {x y : SententialForm terminal nonterminal} {w : Word terminal}
    (hy : y = SententialForm.terminalWord w)
    (h : CFG.Derives G x y) :
    w ∈ CFG.FormLanguage symbolLanguage x := by
  induction h generalizing w with
  | refl _ =>
      rw [hy]
      exact CFG.terminalWord_mem_formLanguage symbolLanguage hterminal w
  | step hstep _ ih =>
      exact cfg_yields_sound_for_symbol_language symbolLanguage hprod hstep
        (ih hy)

theorem cfg_derives_sound_for_symbol_language
    {G : CFG terminal nonterminal}
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hterminal : forall a,
      Word.Symbol a ∈ symbolLanguage (Symbol.terminal a))
    (hprod : forall A rhs, G.produces A rhs -> forall w,
      w ∈ CFG.FormLanguage symbolLanguage rhs ->
        w ∈ symbolLanguage (Symbol.nonterminal A))
    {x : SententialForm terminal nonterminal} {w : Word terminal}
    (h : CFG.Derives G x (SententialForm.terminalWord w)) :
    w ∈ CFG.FormLanguage symbolLanguage x :=
  cfg_derives_sound_for_symbol_language_aux symbolLanguage hterminal hprod rfl h

inductive AnBnCstarNT where
  | start
  | pair
  | ctail
deriving DecidableEq

namespace AnBnCstarNT

def finite : Foundation.FiniteType AnBnCstarNT where
  elems := [start, pair, ctail]
  complete := by
    intro x
    cases x <;> simp

end AnBnCstarNT

inductive AnBnCstarProduces :
    AnBnCstarNT -> SententialForm ABC AnBnCstarNT -> Prop where
  | startRule :
      AnBnCstarProduces AnBnCstarNT.start
        [Symbol.nonterminal AnBnCstarNT.pair,
         Symbol.nonterminal AnBnCstarNT.ctail]
  | pairWrap :
      AnBnCstarProduces AnBnCstarNT.pair
        [Symbol.terminal ABC.a, Symbol.nonterminal AnBnCstarNT.pair,
         Symbol.terminal ABC.b]
  | pairStop :
      AnBnCstarProduces AnBnCstarNT.pair []
  | cMore :
      AnBnCstarProduces AnBnCstarNT.ctail
        [Symbol.terminal ABC.c, Symbol.nonterminal AnBnCstarNT.ctail]
  | cStop :
      AnBnCstarProduces AnBnCstarNT.ctail []

def AnBnCstarGrammar : CFG ABC AnBnCstarNT where
  start := AnBnCstarNT.start
  produces := AnBnCstarProduces
  nonterminalsFinite := AnBnCstarNT.finite

def anbnCstarSymbolLanguage : Symbol ABC AnBnCstarNT -> Language ABC
  | Symbol.terminal t => Language.Singleton (Word.Symbol t)
  | Symbol.nonterminal AnBnCstarNT.start => anbnCstarLanguage
  | Symbol.nonterminal AnBnCstarNT.pair => abcAnBnLanguage
  | Symbol.nonterminal AnBnCstarNT.ctail => abcCstarLanguage

/-!
The {lit}`a^n b^n c^*` grammar has two independent phases: one nonterminal
generates the matched {lit}`a`/{lit}`b` prefix, and the other generates the
arbitrary tail of {lit}`c`s.
-/

theorem anbnCstar_pair_stop_generated :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.pair]
      (SententialForm.terminalWord (abcAnBnWord 0)) := by
  apply CFG.yields_derives
  exists []
  exists []
  exists AnBnCstarNT.pair
  exists ([] : SententialForm ABC AnBnCstarNT)
  constructor
  · exact AnBnCstarProduces.pairStop
  constructor
  · rfl
  · simp [abcAnBnWord, Word.Concat, Word.RepeatSymbol, SententialForm.terminalWord]

theorem anbnCstar_pair_wrap_generated {w : Word ABC}
    (h : CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.pair]
      (SententialForm.terminalWord w)) :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.pair]
      (SententialForm.terminalWord (ABC.a :: Word.Concat w [ABC.b])) := by
  have hStart : CFG.Yields AnBnCstarGrammar
      [Symbol.nonterminal AnBnCstarNT.pair]
      [Symbol.terminal ABC.a, Symbol.nonterminal AnBnCstarNT.pair,
       Symbol.terminal ABC.b] := by
    exists []
    exists []
    exists AnBnCstarNT.pair
    exists [Symbol.terminal ABC.a, Symbol.nonterminal AnBnCstarNT.pair,
      Symbol.terminal ABC.b]
    constructor
    · exact AnBnCstarProduces.pairWrap
    constructor <;> rfl
  have hContext :
      CFG.Derives AnBnCstarGrammar
        [Symbol.terminal ABC.a, Symbol.nonterminal AnBnCstarNT.pair,
         Symbol.terminal ABC.b]
        (Symbol.terminal ABC.a ::
          SententialForm.terminalWord w ++ [Symbol.terminal ABC.b]) := by
    simpa using CFG.derives_context h [Symbol.terminal ABC.a]
      [Symbol.terminal ABC.b]
  have hAll := CFG.Derives.step hStart hContext
  change CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.pair]
    (SententialForm.terminalWord (ABC.a :: Word.Concat w [ABC.b]))
  simpa [SententialForm.terminalWord, Word.Concat] using hAll

theorem anbnCstar_pair_words_generated (n : Nat) :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.pair]
      (SententialForm.terminalWord (abcAnBnWord n)) := by
  induction n with
  | zero => exact anbnCstar_pair_stop_generated
  | succ n ih =>
      simpa [abcAnBn_wrap_word n] using anbnCstar_pair_wrap_generated ih

theorem anbnCstar_c_stop_generated :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.ctail]
      (SententialForm.terminalWord (Word.RepeatSymbol ABC.c 0)) := by
  apply CFG.yields_derives
  exists []
  exists []
  exists AnBnCstarNT.ctail
  exists ([] : SententialForm ABC AnBnCstarNT)
  constructor
  · exact AnBnCstarProduces.cStop
  constructor
  · rfl
  · simp [Word.RepeatSymbol, SententialForm.terminalWord]

theorem anbnCstar_c_more_generated {w : Word ABC}
    (h : CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.ctail]
      (SententialForm.terminalWord w)) :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.ctail]
      (SententialForm.terminalWord (ABC.c :: w)) := by
  have hStart : CFG.Yields AnBnCstarGrammar
      [Symbol.nonterminal AnBnCstarNT.ctail]
      [Symbol.terminal ABC.c, Symbol.nonterminal AnBnCstarNT.ctail] := by
    exists []
    exists []
    exists AnBnCstarNT.ctail
    exists [Symbol.terminal ABC.c, Symbol.nonterminal AnBnCstarNT.ctail]
    constructor
    · exact AnBnCstarProduces.cMore
    constructor <;> rfl
  have hContext :
      CFG.Derives AnBnCstarGrammar
        [Symbol.terminal ABC.c, Symbol.nonterminal AnBnCstarNT.ctail]
        (Symbol.terminal ABC.c :: SententialForm.terminalWord w) := by
    simpa using CFG.derives_context h [Symbol.terminal ABC.c] []
  have hAll := CFG.Derives.step hStart hContext
  simpa [SententialForm.terminalWord] using hAll

theorem anbnCstar_c_words_generated (k : Nat) :
    CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.ctail]
      (SententialForm.terminalWord (Word.RepeatSymbol ABC.c k)) := by
  induction k with
  | zero => exact anbnCstar_c_stop_generated
  | succ k ih =>
      simpa [abcCstar_cons_word k] using anbnCstar_c_more_generated ih

theorem anbnCstar_words_generated (n k : Nat) :
    anbnCstarWord n k ∈ CFG.GeneratedLanguage AnBnCstarGrammar := by
  have hStart : CFG.Yields AnBnCstarGrammar
      [Symbol.nonterminal AnBnCstarNT.start]
      [Symbol.nonterminal AnBnCstarNT.pair,
       Symbol.nonterminal AnBnCstarNT.ctail] := by
    exists []
    exists []
    exists AnBnCstarNT.start
    exists [Symbol.nonterminal AnBnCstarNT.pair,
      Symbol.nonterminal AnBnCstarNT.ctail]
    constructor
    · exact AnBnCstarProduces.startRule
    constructor <;> rfl
  have hPair :=
    anbnCstar_pair_words_generated n
  have hTail :=
    anbnCstar_c_words_generated k
  have hPairContext :
      CFG.Derives AnBnCstarGrammar
        [Symbol.nonterminal AnBnCstarNT.pair,
         Symbol.nonterminal AnBnCstarNT.ctail]
        (SententialForm.terminalWord (abcAnBnWord n) ++
          [Symbol.nonterminal AnBnCstarNT.ctail]) := by
    simpa using CFG.derives_context hPair []
      [Symbol.nonterminal AnBnCstarNT.ctail]
  have hTailContext :
      CFG.Derives AnBnCstarGrammar
        (SententialForm.terminalWord (abcAnBnWord n) ++
          [Symbol.nonterminal AnBnCstarNT.ctail])
        (SententialForm.terminalWord (abcAnBnWord n) ++
          SententialForm.terminalWord (Word.RepeatSymbol ABC.c k)) := by
    simpa using CFG.derives_context hTail
      (SententialForm.terminalWord (abcAnBnWord n)) []
  have hAll := CFG.Derives.step hStart
    (CFG.derives_trans hPairContext hTailContext)
  change CFG.Derives AnBnCstarGrammar [Symbol.nonterminal AnBnCstarNT.start]
    (SententialForm.terminalWord (anbnCstarWord n k))
  rw [anbnCstarWord, SententialForm.terminalWord_append]
  exact hAll

theorem anbnCstar_production_sound
    (A : AnBnCstarNT) (rhs : SententialForm ABC AnBnCstarNT)
    (hprod : AnBnCstarGrammar.produces A rhs) :
    forall w, w ∈ CFG.FormLanguage anbnCstarSymbolLanguage rhs ->
      w ∈ anbnCstarSymbolLanguage (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | startRule =>
      simp [CFG.FormLanguage, anbnCstarSymbolLanguage] at hw
      rcases hw with ⟨pairWord, tail, hpair, htail, _hwEq⟩
      rcases hpair with ⟨n, hn⟩
      rcases htail with ⟨cWord, empty, hcWord, _hempty, _htailEq⟩
      rcases hcWord with ⟨k, hk⟩
      exists n
      exists k
      subst pairWord
      subst cWord
      subst empty
      subst tail
      subst w
      simp [anbnCstarWord, Word.Concat, Word.Empty]
  | pairWrap =>
      simp [CFG.FormLanguage, anbnCstarSymbolLanguage] at hw
      rcases hw with ⟨first, tail, _hfirst, htail, _hwEq⟩
      rcases htail with ⟨middle, last, hmiddle, hlast, _htailEq⟩
      rcases hmiddle with ⟨n, hn⟩
      rcases hlast with ⟨bword, empty, _hbword, _hempty, hlastEq⟩
      exists n + 1
      subst first
      subst tail
      subst middle
      subst bword
      subst empty
      subst w
      rw [hlastEq]
      exact abcAnBn_wrap_word n
  | pairStop =>
      simp [CFG.FormLanguage] at hw
      have hwEmpty : w = Word.Empty := hw
      exists 0
  | cMore =>
      simp [CFG.FormLanguage, anbnCstarSymbolLanguage] at hw
      rcases hw with ⟨first, tail, hfirst, htail, hwEq⟩
      rcases htail with ⟨middle, empty, hmiddle, hempty, htailEq⟩
      rcases hmiddle with ⟨k, hk⟩
      exists k + 1
      rw [hwEq, hfirst, htailEq, hk, hempty]
      simpa [Word.Symbol, Word.Concat, Word.Empty] using abcCstar_cons_word k
  | cStop =>
      simp [CFG.FormLanguage] at hw
      have hwEmpty : w = Word.Empty := hw
      exists 0

theorem anbnCstar_generated_only_language {w : Word ABC}
    (h : w ∈ CFG.GeneratedLanguage AnBnCstarGrammar) :
    w ∈ anbnCstarLanguage := by
  have hs := cfg_derives_sound_for_symbol_language anbnCstarSymbolLanguage
    (by intro t; rfl) anbnCstar_production_sound h
  simp [CFG.FormLanguage, anbnCstarSymbolLanguage] at hs
  rcases hs with ⟨first, empty, hfirst, hempty, hEq⟩
  rw [hEq]
  have hemptyEq : empty = Word.Empty := hempty
  rw [hemptyEq, Word.concat_empty_right]
  exact hfirst

theorem anbnCstar_generated_language_exact (w : Word ABC) :
    w ∈ CFG.GeneratedLanguage AnBnCstarGrammar <->
      w ∈ anbnCstarLanguage := by
  constructor
  · exact anbnCstar_generated_only_language
  · intro h
    rcases h with ⟨n, k, hw⟩
    rw [hw]
    exact anbnCstar_words_generated n k

theorem anbnCstar_hasFiniteProductions :
    CFG.HasFiniteProductions AnBnCstarGrammar := by
  exists [
    { lhs := AnBnCstarNT.start,
      rhs := [Symbol.nonterminal AnBnCstarNT.pair,
        Symbol.nonterminal AnBnCstarNT.ctail] },
    { lhs := AnBnCstarNT.pair,
      rhs := [Symbol.terminal ABC.a, Symbol.nonterminal AnBnCstarNT.pair,
        Symbol.terminal ABC.b] },
    { lhs := AnBnCstarNT.pair,
      rhs := [] },
    { lhs := AnBnCstarNT.ctail,
      rhs := [Symbol.terminal ABC.c, Symbol.nonterminal AnBnCstarNT.ctail] },
    { lhs := AnBnCstarNT.ctail,
      rhs := [] }]
  intro A rhs
  constructor
  · intro h
    cases h <;> simp
  · intro h
    simp at h
    rcases h with h | h | h | h | h
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AnBnCstarProduces.startRule
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AnBnCstarProduces.pairWrap
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AnBnCstarProduces.pairStop
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AnBnCstarProduces.cMore
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AnBnCstarProduces.cStop

theorem anbnCstar_finite_production_context_free :
    CFL.FiniteProductionContextFreeLanguage anbnCstarLanguage := by
  exists AnBnCstarNT
  exists AnBnCstarGrammar
  constructor
  · exact anbnCstar_hasFiniteProductions
  · exact anbnCstar_generated_language_exact

/-!
The second witness grammar is symmetric: it generates an arbitrary prefix of
{lit}`a`s followed by a matched {lit}`b`/{lit}`c` block. Intersecting this
language with the previous one forces all three counts to agree.
-/

inductive AstarBnCnNT where
  | start
  | ahead
  | pair
deriving DecidableEq

namespace AstarBnCnNT

def finite : Foundation.FiniteType AstarBnCnNT where
  elems := [start, ahead, pair]
  complete := by
    intro x
    cases x <;> simp

end AstarBnCnNT

inductive AstarBnCnProduces :
    AstarBnCnNT -> SententialForm ABC AstarBnCnNT -> Prop where
  | startRule :
      AstarBnCnProduces AstarBnCnNT.start
        [Symbol.nonterminal AstarBnCnNT.ahead,
         Symbol.nonterminal AstarBnCnNT.pair]
  | aMore :
      AstarBnCnProduces AstarBnCnNT.ahead
        [Symbol.terminal ABC.a, Symbol.nonterminal AstarBnCnNT.ahead]
  | aStop :
      AstarBnCnProduces AstarBnCnNT.ahead []
  | pairWrap :
      AstarBnCnProduces AstarBnCnNT.pair
        [Symbol.terminal ABC.b, Symbol.nonterminal AstarBnCnNT.pair,
         Symbol.terminal ABC.c]
  | pairStop :
      AstarBnCnProduces AstarBnCnNT.pair []

def AstarBnCnGrammar : CFG ABC AstarBnCnNT where
  start := AstarBnCnNT.start
  produces := AstarBnCnProduces
  nonterminalsFinite := AstarBnCnNT.finite

def astarBnCnSymbolLanguage : Symbol ABC AstarBnCnNT -> Language ABC
  | Symbol.terminal t => Language.Singleton (Word.Symbol t)
  | Symbol.nonterminal AstarBnCnNT.start => astarBnCnLanguage
  | Symbol.nonterminal AstarBnCnNT.ahead => abcAstarLanguage
  | Symbol.nonterminal AstarBnCnNT.pair => abcBnCnLanguage

theorem astarBnCn_a_stop_generated :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.ahead]
      (SententialForm.terminalWord (Word.RepeatSymbol ABC.a 0)) := by
  apply CFG.yields_derives
  exists []
  exists []
  exists AstarBnCnNT.ahead
  exists ([] : SententialForm ABC AstarBnCnNT)
  constructor
  · exact AstarBnCnProduces.aStop
  constructor
  · rfl
  · simp [Word.RepeatSymbol, SententialForm.terminalWord]

theorem astarBnCn_a_more_generated {w : Word ABC}
    (h : CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.ahead]
      (SententialForm.terminalWord w)) :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.ahead]
      (SententialForm.terminalWord (ABC.a :: w)) := by
  have hStart : CFG.Yields AstarBnCnGrammar
      [Symbol.nonterminal AstarBnCnNT.ahead]
      [Symbol.terminal ABC.a, Symbol.nonterminal AstarBnCnNT.ahead] := by
    exists []
    exists []
    exists AstarBnCnNT.ahead
    exists [Symbol.terminal ABC.a, Symbol.nonterminal AstarBnCnNT.ahead]
    constructor
    · exact AstarBnCnProduces.aMore
    constructor <;> rfl
  have hContext :
      CFG.Derives AstarBnCnGrammar
        [Symbol.terminal ABC.a, Symbol.nonterminal AstarBnCnNT.ahead]
        (Symbol.terminal ABC.a :: SententialForm.terminalWord w) := by
    simpa using CFG.derives_context h [Symbol.terminal ABC.a] []
  have hAll := CFG.Derives.step hStart hContext
  simpa [SententialForm.terminalWord] using hAll

theorem astarBnCn_a_words_generated (k : Nat) :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.ahead]
      (SententialForm.terminalWord (Word.RepeatSymbol ABC.a k)) := by
  induction k with
  | zero => exact astarBnCn_a_stop_generated
  | succ k ih =>
      simpa [abcAstar_cons_word k] using astarBnCn_a_more_generated ih

theorem astarBnCn_pair_stop_generated :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.pair]
      (SententialForm.terminalWord (abcBnCnWord 0)) := by
  apply CFG.yields_derives
  exists []
  exists []
  exists AstarBnCnNT.pair
  exists ([] : SententialForm ABC AstarBnCnNT)
  constructor
  · exact AstarBnCnProduces.pairStop
  constructor
  · rfl
  · simp [abcBnCnWord, Word.Concat, Word.RepeatSymbol, SententialForm.terminalWord]

theorem astarBnCn_pair_wrap_generated {w : Word ABC}
    (h : CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.pair]
      (SententialForm.terminalWord w)) :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.pair]
      (SententialForm.terminalWord (ABC.b :: Word.Concat w [ABC.c])) := by
  have hStart : CFG.Yields AstarBnCnGrammar
      [Symbol.nonterminal AstarBnCnNT.pair]
      [Symbol.terminal ABC.b, Symbol.nonterminal AstarBnCnNT.pair,
       Symbol.terminal ABC.c] := by
    exists []
    exists []
    exists AstarBnCnNT.pair
    exists [Symbol.terminal ABC.b, Symbol.nonterminal AstarBnCnNT.pair,
      Symbol.terminal ABC.c]
    constructor
    · exact AstarBnCnProduces.pairWrap
    constructor <;> rfl
  have hContext :
      CFG.Derives AstarBnCnGrammar
        [Symbol.terminal ABC.b, Symbol.nonterminal AstarBnCnNT.pair,
         Symbol.terminal ABC.c]
        (Symbol.terminal ABC.b ::
          SententialForm.terminalWord w ++ [Symbol.terminal ABC.c]) := by
    simpa using CFG.derives_context h [Symbol.terminal ABC.b]
      [Symbol.terminal ABC.c]
  have hAll := CFG.Derives.step hStart hContext
  change CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.pair]
    (SententialForm.terminalWord (ABC.b :: Word.Concat w [ABC.c]))
  simpa [SententialForm.terminalWord, Word.Concat] using hAll

theorem astarBnCn_pair_words_generated (n : Nat) :
    CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.pair]
      (SententialForm.terminalWord (abcBnCnWord n)) := by
  induction n with
  | zero => exact astarBnCn_pair_stop_generated
  | succ n ih =>
      simpa [abcBnCn_wrap_word n] using astarBnCn_pair_wrap_generated ih

theorem astarBnCn_words_generated (k n : Nat) :
    astarBnCnWord k n ∈ CFG.GeneratedLanguage AstarBnCnGrammar := by
  have hStart : CFG.Yields AstarBnCnGrammar
      [Symbol.nonterminal AstarBnCnNT.start]
      [Symbol.nonterminal AstarBnCnNT.ahead,
       Symbol.nonterminal AstarBnCnNT.pair] := by
    exists []
    exists []
    exists AstarBnCnNT.start
    exists [Symbol.nonterminal AstarBnCnNT.ahead,
      Symbol.nonterminal AstarBnCnNT.pair]
    constructor
    · exact AstarBnCnProduces.startRule
    constructor <;> rfl
  have hAhead :=
    astarBnCn_a_words_generated k
  have hPair :=
    astarBnCn_pair_words_generated n
  have hAheadContext :
      CFG.Derives AstarBnCnGrammar
        [Symbol.nonterminal AstarBnCnNT.ahead,
         Symbol.nonterminal AstarBnCnNT.pair]
        (SententialForm.terminalWord (Word.RepeatSymbol ABC.a k) ++
          [Symbol.nonterminal AstarBnCnNT.pair]) := by
    simpa using CFG.derives_context hAhead []
      [Symbol.nonterminal AstarBnCnNT.pair]
  have hPairContext :
      CFG.Derives AstarBnCnGrammar
        (SententialForm.terminalWord (Word.RepeatSymbol ABC.a k) ++
          [Symbol.nonterminal AstarBnCnNT.pair])
        (SententialForm.terminalWord (Word.RepeatSymbol ABC.a k) ++
          SententialForm.terminalWord (abcBnCnWord n)) := by
    simpa using CFG.derives_context hPair
      (SententialForm.terminalWord (Word.RepeatSymbol ABC.a k)) []
  have hAll := CFG.Derives.step hStart
    (CFG.derives_trans hAheadContext hPairContext)
  change CFG.Derives AstarBnCnGrammar [Symbol.nonterminal AstarBnCnNT.start]
    (SententialForm.terminalWord (astarBnCnWord k n))
  rw [astarBnCnWord, SententialForm.terminalWord_append]
  exact hAll

theorem astarBnCn_production_sound
    (A : AstarBnCnNT) (rhs : SententialForm ABC AstarBnCnNT)
    (hprod : AstarBnCnGrammar.produces A rhs) :
    forall w, w ∈ CFG.FormLanguage astarBnCnSymbolLanguage rhs ->
      w ∈ astarBnCnSymbolLanguage (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | startRule =>
      simp [CFG.FormLanguage, astarBnCnSymbolLanguage] at hw
      rcases hw with ⟨aWord, tail, haWord, htail, _hwEq⟩
      rcases haWord with ⟨k, hk⟩
      rcases htail with ⟨pairWord, empty, hpairWord, _hempty, _htailEq⟩
      rcases hpairWord with ⟨n, hn⟩
      exists k
      exists n
      subst aWord
      subst pairWord
      subst empty
      subst tail
      subst w
      simp [astarBnCnWord, Word.Concat, Word.Empty]
  | aMore =>
      simp [CFG.FormLanguage, astarBnCnSymbolLanguage] at hw
      rcases hw with ⟨first, tail, hfirst, htail, hwEq⟩
      rcases htail with ⟨middle, empty, hmiddle, hempty, htailEq⟩
      rcases hmiddle with ⟨k, hk⟩
      exists k + 1
      rw [hwEq, hfirst, htailEq, hk, hempty]
      simpa [Word.Symbol, Word.Concat, Word.Empty] using abcAstar_cons_word k
  | aStop =>
      simp [CFG.FormLanguage] at hw
      have hwEmpty : w = Word.Empty := hw
      exists 0
  | pairWrap =>
      simp [CFG.FormLanguage, astarBnCnSymbolLanguage] at hw
      rcases hw with ⟨first, tail, _hfirst, htail, _hwEq⟩
      rcases htail with ⟨middle, last, hmiddle, hlast, _htailEq⟩
      rcases hmiddle with ⟨n, hn⟩
      rcases hlast with ⟨cword, empty, _hcword, _hempty, hlastEq⟩
      exists n + 1
      subst first
      subst tail
      subst middle
      subst cword
      subst empty
      subst w
      rw [hlastEq]
      exact abcBnCn_wrap_word n
  | pairStop =>
      simp [CFG.FormLanguage] at hw
      have hwEmpty : w = Word.Empty := hw
      exists 0

theorem astarBnCn_generated_only_language {w : Word ABC}
    (h : w ∈ CFG.GeneratedLanguage AstarBnCnGrammar) :
    w ∈ astarBnCnLanguage := by
  have hs := cfg_derives_sound_for_symbol_language astarBnCnSymbolLanguage
    (by intro t; rfl) astarBnCn_production_sound h
  simp [CFG.FormLanguage, astarBnCnSymbolLanguage] at hs
  rcases hs with ⟨first, empty, hfirst, hempty, hEq⟩
  rw [hEq]
  have hemptyEq : empty = Word.Empty := hempty
  rw [hemptyEq, Word.concat_empty_right]
  exact hfirst

theorem astarBnCn_generated_language_exact (w : Word ABC) :
    w ∈ CFG.GeneratedLanguage AstarBnCnGrammar <->
      w ∈ astarBnCnLanguage := by
  constructor
  · exact astarBnCn_generated_only_language
  · intro h
    rcases h with ⟨k, n, hw⟩
    rw [hw]
    exact astarBnCn_words_generated k n

theorem astarBnCn_hasFiniteProductions :
    CFG.HasFiniteProductions AstarBnCnGrammar := by
  exists [
    { lhs := AstarBnCnNT.start,
      rhs := [Symbol.nonterminal AstarBnCnNT.ahead,
        Symbol.nonterminal AstarBnCnNT.pair] },
    { lhs := AstarBnCnNT.ahead,
      rhs := [Symbol.terminal ABC.a, Symbol.nonterminal AstarBnCnNT.ahead] },
    { lhs := AstarBnCnNT.ahead,
      rhs := [] },
    { lhs := AstarBnCnNT.pair,
      rhs := [Symbol.terminal ABC.b, Symbol.nonterminal AstarBnCnNT.pair,
        Symbol.terminal ABC.c] },
    { lhs := AstarBnCnNT.pair,
      rhs := [] }]
  intro A rhs
  constructor
  · intro h
    cases h <;> simp
  · intro h
    simp at h
    rcases h with h | h | h | h | h
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AstarBnCnProduces.startRule
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AstarBnCnProduces.aMore
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AstarBnCnProduces.aStop
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AstarBnCnProduces.pairWrap
    · rcases h with ⟨hA, hrhs⟩
      cases hA
      cases hrhs
      exact AstarBnCnProduces.pairStop

theorem astarBnCn_finite_production_context_free :
    CFL.FiniteProductionContextFreeLanguage astarBnCnLanguage := by
  exists AstarBnCnNT
  exists AstarBnCnGrammar
  constructor
  · exact astarBnCn_hasFiniteProductions
  · exact astarBnCn_generated_language_exact

/-!
The intersection proof is arithmetic on symbol counts. Membership in the first
language gives equal {lit}`a` and {lit}`b` counts; membership in the second gives
equal {lit}`b` and {lit}`c` counts. Together they identify a word of the exact
form {lit}`a^n b^n c^n`.
-/

theorem anbnCstar_word_count_a (n k : Nat) :
    Word.Count ABC.a (anbnCstarWord n k) = n := by
  unfold anbnCstarWord abcAnBnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.b)]
  rw [Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbnCstar_word_count_b (n k : Nat) :
    Word.Count ABC.b (anbnCstarWord n k) = n := by
  unfold anbnCstarWord abcAnBnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.a)]
  rw [Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbnCstar_word_count_c (n k : Nat) :
    Word.Count ABC.c (anbnCstarWord n k) = k := by
  unfold anbnCstarWord abcAnBnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.a)]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.b)]
  rw [Word.count_repeatSymbol_same]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem astarBnCn_word_count_a (k n : Nat) :
    Word.Count ABC.a (astarBnCnWord k n) = k := by
  unfold astarBnCnWord abcBnCnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.b)]
  rw [Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem astarBnCn_word_count_b (k n : Nat) :
    Word.Count ABC.b (astarBnCnWord k n) = n := by
  unfold astarBnCnWord abcBnCnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.a)]
  rw [Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem astarBnCn_word_count_c (k n : Nat) :
    Word.Count ABC.c (astarBnCnWord k n) = n := by
  unfold astarBnCnWord abcBnCnWord
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.a)]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.b)]
  rw [Word.count_repeatSymbol_same]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbnCstarWord_diagonal (n : Nat) :
    anbnCstarWord n n = anbncnBlockWord n := by
  simp [anbnCstarWord, abcAnBnWord, anbncnBlockWord, Word.Concat,
    List.append_assoc]

theorem astarBnCnWord_diagonal (n : Nat) :
    astarBnCnWord n n = anbncnBlockWord n := by
  simp [astarBnCnWord, abcBnCnWord, anbncnBlockWord, Word.Concat]

theorem anbnCstar_inter_astarBnCn_exact :
    Language.Equal (Language.Inter anbnCstarLanguage astarBnCnLanguage)
      anbncnLanguage := by
  intro w
  constructor
  · intro hw
    rcases hw.left with ⟨n, k, hleft⟩
    rcases hw.right with ⟨i, j, hright⟩
    have hEq : anbnCstarWord n k = astarBnCnWord i j := by
      rw [← hleft, ← hright]
    have hb : n = j := by
      have hcount := congrArg (Word.Count ABC.b) hEq
      rw [anbnCstar_word_count_b n k,
        astarBnCn_word_count_b i j] at hcount
      exact hcount
    have hc : k = j := by
      have hcount := congrArg (Word.Count ABC.c) hEq
      rw [anbnCstar_word_count_c n k,
        astarBnCn_word_count_c i j] at hcount
      exact hcount
    have hk : k = n := by omega
    exists n
    rw [hleft, hk, anbnCstarWord_diagonal]
  · intro hw
    rcases hw with ⟨n, hw⟩
    constructor
    · exists n
      exists n
      rw [hw]
      exact (anbnCstarWord_diagonal n).symm
    · exists n
      exists n

/-!
# Finite-Production CFLs and Pumping Vocabulary

The book-facing context-free predicate requires a finite production list. The
CFL Pumping Lemma uses a five-part decomposition `u x y z v`, where pumping
repeats the two outer middle pieces `x` and `z` together. At least one of
`x` or `z` is nonempty, and the combined middle region `x y z` is bounded by
the pumping length.
-/

def FiniteProductionContextFreeLanguage (L : Language terminal) : Prop :=
  CFL.FiniteProductionContextFreeLanguage L

def CFLPumpingDecomposition (L : Language terminal) (K : Nat) (w : Word terminal) :
    Prop :=
  CFL.PumpingDecomposition L K w

def CFLPumpingLength (L : Language terminal) (K : Nat) : Prop :=
  CFL.PumpingLength L K

def CFLHasPumpingProperty (L : Language terminal) : Prop :=
  CFL.HasPumpingProperty L

def LanguageClassExtensional (C : Language terminal -> Prop) : Prop :=
  forall L M, Language.Equal L M -> C L -> C M

def ClosedUnderIntersection (C : Language terminal -> Prop) : Prop :=
  forall L M, C L -> C M -> C (Language.Inter L M)

def ClosedUnderUnion (C : Language terminal -> Prop) : Prop :=
  forall L M, C L -> C M -> C (Language.Union L M)

def ClosedUnderComplement (C : Language terminal -> Prop) : Prop :=
  forall L, C L -> C (Language.Compl L)

theorem finite_production_context_free {L : Language terminal}
    (hL : FiniteProductionContextFreeLanguage L) :
    CFL.ContextFreeLanguage L :=
  CFL.finiteProduction_contextFree hL

theorem finite_production_context_free_of_equal {L M : Language terminal}
    (hEq : Language.Equal L M)
    (hL : FiniteProductionContextFreeLanguage L) :
    FiniteProductionContextFreeLanguage M := by
  cases hL with
  | intro nonterminal hnt =>
      cases hnt with
      | intro G hG =>
          exists nonterminal
          exists G
          constructor
          · exact hG.left
          · exact Language.equal_trans hG.right hEq

theorem finite_production_context_free_extensional :
    LanguageClassExtensional
      (FiniteProductionContextFreeLanguage (terminal := terminal)) := by
  intro L M hEq hL
  exact finite_production_context_free_of_equal hEq hL

theorem finite_production_rhs_length_bound {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    exists B : Nat,
      B > 0 ∧ forall A rhs, G.produces A rhs -> rhs.length < B :=
  CFL.finiteProduction_rhs_length_bound hG

theorem finite_production_grammar_pumping_property
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    CFLHasPumpingProperty (CFG.GeneratedLanguage G) :=
  CFL.finiteProduction_generated_hasPumpingProperty hG

theorem finite_production_pumping_property {terminal : Type}
    {L : Language terminal}
    (hL : FiniteProductionContextFreeLanguage L) :
    CFLHasPumpingProperty L :=
  CFL.finiteProduction_hasPumpingProperty hL

theorem pumping_decomposition_original_word_mem {L : Language terminal}
    {K : Nat} {w : Word terminal}
    (h : CFLPumpingDecomposition L K w) : w ∈ L :=
  CFL.pumping_decomposition_original_word_mem h

theorem pumping_decomposition_of_equal {L M : Language terminal} {K : Nat}
    {w : Word terminal}
    (hEq : Language.Equal L M) (h : CFLPumpingDecomposition L K w) :
    CFLPumpingDecomposition M K w :=
  CFL.pumping_decomposition_of_equal hEq h

theorem pumping_length_of_equal {L M : Language terminal} {K : Nat}
    (hEq : Language.Equal L M) (h : CFLPumpingLength L K) :
    CFLPumpingLength M K :=
  CFL.pumpingLength_of_equal hEq h

theorem pumping_property_of_equal {L M : Language terminal}
    (hEq : Language.Equal L M) (h : CFLHasPumpingProperty L) :
    CFLHasPumpingProperty M :=
  CFL.hasPumpingProperty_of_equal hEq h

theorem pumping_length_monotone {L : Language terminal} {K M : Nat}
    (hKM : K <= M) (h : CFLPumpingLength L K) :
    CFLPumpingLength L M :=
  CFL.pumpingLength_mono hKM h

theorem not_pumping_length_of_counterexample {L : Language terminal} {K : Nat}
    {w : Word terminal}
    (hw : w ∈ L) (hlen : K <= Word.Length w)
    (hbad :
      forall u x y z v : Word terminal,
        w = CFL.Concat5 u x y z v ->
        (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
        Word.Length (CFL.Concat3 x y z) < K ->
        exists n : Nat, ¬ CFL.Pumped u x y z v n ∈ L) :
    ¬ CFLPumpingLength L K :=
  CFL.not_pumpingLength_of_counterexample hw hlen hbad

theorem not_pumping_property_of_counterexamples {L : Language terminal}
    (hbad :
      forall K : Nat, K > 0 ->
        exists w : Word terminal,
          w ∈ L ∧
          K <= Word.Length w ∧
          forall u x y z v : Word terminal,
            w = CFL.Concat5 u x y z v ->
            (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
            Word.Length (CFL.Concat3 x y z) < K ->
            exists n : Nat, ¬ CFL.Pumped u x y z v n ∈ L) :
    ¬ CFLHasPumpingProperty L :=
  CFL.not_hasPumpingProperty_of_counterexamples hbad

/-!
These wrappers are the practical way to use the CFL Pumping Lemma on this page:
build a bad-word family for every proposed pumping length, then conclude that
the language is not context-free.
-/

theorem not_context_free_of_no_pumping_property {terminal : Type}
    {L : Language terminal}
    (hNoPump : ¬ CFLHasPumpingProperty L) :
    ¬ CFL.ContextFreeLanguage L :=
  CFL.not_context_free_of_no_pumping_property hNoPump

def CFLPumpingBadWordFamily (L : Language terminal) : Prop :=
  forall K : Nat, K > 0 ->
    exists w : Word terminal,
      w ∈ L ∧
      K <= Word.Length w ∧
      forall u x y z v : Word terminal,
        w = CFL.Concat5 u x y z v ->
        (x ≠ Word.Empty ∨ z ≠ Word.Empty) ->
        Word.Length (CFL.Concat3 x y z) < K ->
        exists n : Nat, ¬ CFL.Pumped u x y z v n ∈ L

theorem not_pumping_property_of_bad_word_family {L : Language terminal}
    (hbad : CFLPumpingBadWordFamily L) :
    ¬ CFLHasPumpingProperty L :=
  not_pumping_property_of_counterexamples hbad

theorem not_context_free_of_bad_word_family {terminal : Type}
    {L : Language terminal}
    (hbad : CFLPumpingBadWordFamily L) :
    ¬ CFL.ContextFreeLanguage L :=
  not_context_free_of_no_pumping_property
    (not_pumping_property_of_bad_word_family hbad)

theorem not_finite_production_context_free_of_bad_word_family
    {terminal : Type} {L : Language terminal}
    (hbad : CFLPumpingBadWordFamily L) :
    ¬ FiniteProductionContextFreeLanguage L := by
  intro hcf
  exact not_pumping_property_of_bad_word_family hbad
    (finite_production_pumping_property hcf)

/-!
# Pumping {lit}`a^n b^n c^n`

For a proposed CFL pumping length `K`, choose `a^K b^K c^K`. The bounded
middle region `x y z` cannot cover all three block boundaries at once, so
pumping `x` and `z` with count `2` changes at most two of the three symbol
counts. The resulting word cannot still have equal numbers of `a`, `b`, and
`c`.
-/

theorem anbncn_membership (w : Word ABC) :
    w ∈ anbncnLanguage <-> exists n, w = anbncnBlockWord n :=
  Iff.rfl

theorem anbncn_block_count_a (n : Nat) :
    Word.Count ABC.a (anbncnBlockWord n) = n := by
  unfold anbncnBlockWord
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_concat, Word.count_repeatSymbol_different,
    Word.count_repeatSymbol_different]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbncn_block_count_b (n : Nat) :
    Word.Count ABC.b (anbncnBlockWord n) = n := by
  unfold anbncnBlockWord
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.a)]
  rw [Word.count_concat, Word.count_repeatSymbol_same]
  rw [Word.count_repeatSymbol_different (a := ABC.b) (b := ABC.c)]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbncn_block_count_c (n : Nat) :
    Word.Count ABC.c (anbncnBlockWord n) = n := by
  unfold anbncnBlockWord
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.a)]
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.b)]
  rw [Word.count_repeatSymbol_same]
  · omega
  · intro h
    cases h
  · intro h
    cases h

theorem anbncn_block_length (n : Nat) :
    Word.Length (anbncnBlockWord n) = 3 * n := by
  unfold anbncnBlockWord
  simp [Word.length_concat, Word.length_repeatSymbol]
  omega

theorem anbncn_members_have_equal_counts {w : Word ABC}
    (hw : w ∈ anbncnLanguage) :
    Word.Count ABC.a w = Word.Count ABC.b w ∧
      Word.Count ABC.b w = Word.Count ABC.c w := by
  cases hw with
  | intro n hn =>
      rw [hn, anbncn_block_count_a n, anbncn_block_count_b n,
        anbncn_block_count_c n]
      exact ⟨rfl, rfl⟩

/-!
The pumping contradiction needs one combinatorial fact: because the pumpable
middle region is shorter than {lit}`K`, it cannot touch both the first
{lit}`a`-block and the final {lit}`c`-block of {lit}`a^K b^K c^K`.
-/

theorem abc_count_sum_pos_of_nonempty {w : Word ABC}
    (h : w ≠ Word.Empty) :
    0 < Word.Count ABC.a w + Word.Count ABC.b w + Word.Count ABC.c w := by
  cases w with
  | nil =>
      exact False.elim (h rfl)
  | cons head tail =>
      cases head <;> simp [Word.Count] <;> omega

theorem anbncn_drop_after_a_count_a_zero (K l : Nat) (hl : K <= l) :
    Word.Count ABC.a (List.drop l (anbncnBlockWord K)) = 0 := by
  unfold anbncnBlockWord
  change Word.Count ABC.a
      (List.drop l
        (List.append (Word.RepeatSymbol ABC.a K)
          (Word.Concat (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K)))) = 0
  simp [List.drop_append, Word.RepeatSymbol, List.drop_replicate]
  have hzero : K - l = 0 := by omega
  rw [hzero]
  change Word.Count ABC.a
      (List.drop (l - K)
        (Word.Concat (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K))) = 0
  change Word.Count ABC.a
      (List.drop (l - K)
        (List.append (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K))) = 0
  simp [List.drop_append, Word.RepeatSymbol, List.drop_replicate]
  change Word.Count ABC.a
      (Word.Concat (Word.RepeatSymbol ABC.b (K - (l - K)))
        (Word.RepeatSymbol ABC.c (K - (l - K - K)))) = 0
  have hb :
      Word.Count ABC.a (Word.RepeatSymbol ABC.b (K - (l - K))) = 0 := by
    exact Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.b)
      (by intro h; cases h) _
  have hc :
      Word.Count ABC.a (Word.RepeatSymbol ABC.c (K - (l - K - K))) = 0 := by
    exact Word.count_repeatSymbol_different (a := ABC.a) (b := ABC.c)
      (by intro h; cases h) _
  rw [Word.count_concat, hb, hc]

theorem anbncn_take_before_c_count_c_zero (K l : Nat)
    (hl : l <= 2 * K) :
    Word.Count ABC.c (List.take l (anbncnBlockWord K)) = 0 := by
  unfold anbncnBlockWord
  change Word.Count ABC.c
      (List.take l
        (List.append (Word.RepeatSymbol ABC.a K)
          (List.append (Word.RepeatSymbol ABC.b K) (Word.RepeatSymbol ABC.c K)))) = 0
  simp [List.take_append, Word.RepeatSymbol, List.take_replicate]
  have hzero : min (l - K - K) K = 0 := by omega
  rw [hzero]
  change Word.Count ABC.c
      (Word.Concat (Word.RepeatSymbol ABC.a (min l K))
        (Word.Concat (Word.RepeatSymbol ABC.b (min (l - K) K))
          (Word.RepeatSymbol ABC.c 0))) = 0
  rw [Word.count_concat, Word.count_concat]
  rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.a)]
  · rw [Word.count_repeatSymbol_different (a := ABC.c) (b := ABC.b)]
    · simp [Word.count_repeatSymbol_same]
    · intro h
      cases h
  · intro h
    cases h

theorem anbncn_middle_after_a_count_a_zero
    {u middle v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = Word.Concat u (Word.Concat middle v))
    (hu : K <= Word.Length u) :
    Word.Count ABC.a middle = 0 := by
  have htail :
      Word.Concat middle v = List.drop (Word.Length u) (anbncnBlockWord K) := by
    calc
      Word.Concat middle v =
          List.drop (Word.Length u) (Word.Concat u (Word.Concat middle v)) := by
        change Word.Concat middle v =
          List.drop (List.length u) (List.append u (Word.Concat middle v))
        exact (List.drop_left (l₁ := u) (l₂ := Word.Concat middle v)).symm
      _ = List.drop (Word.Length u) (anbncnBlockWord K) := by
        rw [← hword]
  have hcountTail :
      Word.Count ABC.a (Word.Concat middle v) = 0 := by
    rw [htail]
    exact anbncn_drop_after_a_count_a_zero K (Word.Length u) hu
  rw [Word.count_concat] at hcountTail
  omega

theorem anbncn_middle_before_c_count_c_zero
    {u middle v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = Word.Concat u (Word.Concat middle v))
    (hprefix : Word.Length (Word.Concat u middle) <= 2 * K) :
    Word.Count ABC.c middle = 0 := by
  have hprefixEq :
      Word.Concat u middle =
        List.take (Word.Length (Word.Concat u middle)) (anbncnBlockWord K) := by
    calc
      Word.Concat u middle =
          List.take (Word.Length (Word.Concat u middle))
            (Word.Concat (Word.Concat u middle) v) := by
        change Word.Concat u middle =
          List.take (List.length (Word.Concat u middle))
            (List.append (Word.Concat u middle) v)
        exact (List.take_left (l₁ := Word.Concat u middle) (l₂ := v)).symm
      _ = List.take (Word.Length (Word.Concat u middle))
            (Word.Concat u (Word.Concat middle v)) := by
        rw [Word.concat_assoc]
      _ = List.take (Word.Length (Word.Concat u middle)) (anbncnBlockWord K) := by
        rw [← hword]
  have hcountPrefix :
      Word.Count ABC.c (Word.Concat u middle) = 0 := by
    rw [hprefixEq]
    exact anbncn_take_before_c_count_c_zero K
      (Word.Length (Word.Concat u middle)) hprefix
  rw [Word.count_concat] at hcountPrefix
  omega

theorem anbncn_short_middle_count_a_or_c_zero
    {u middle v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = Word.Concat u (Word.Concat middle v))
    (hmiddle : Word.Length middle < K) :
    Word.Count ABC.a middle = 0 ∨ Word.Count ABC.c middle = 0 := by
  by_cases hu : K <= Word.Length u
  · exact Or.inl (anbncn_middle_after_a_count_a_zero hword hu)
  · apply Or.inr
    have huLt : Word.Length u < K := by omega
    have hprefix : Word.Length (Word.Concat u middle) <= 2 * K := by
      rw [Word.length_concat]
      omega
    exact anbncn_middle_before_c_count_c_zero hword hprefix

theorem cfl_pumped_two_count (s : ABC) (u x y z v : Word ABC) :
    Word.Count s (CFL.Pumped u x y z v 2) =
      Word.Count s (CFL.Concat5 u x y z v) +
        Word.Count s (Word.Concat x z) := by
  unfold CFL.Pumped CFL.Concat5
  rw [show Word.RepeatWord x 2 = Word.Concat x x by simp [Word.RepeatWord, Word.Concat]]
  rw [show Word.RepeatWord z 2 = Word.Concat z z by simp [Word.RepeatWord, Word.Concat]]
  repeat rw [Word.count_concat]
  omega

/-!
Pumping with count {lit}`2` adds one extra copy of {lit}`x` and one extra copy
of {lit}`z`. Since {lit}`x ++ z` is nonempty but misses either all {lit}`a`s or
all {lit}`c`s, at least one of the three counts changes differently from the
others.
-/

theorem anbncn_xz_count_a_or_c_zero
    {u x y z v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = CFL.Concat5 u x y z v)
    (hshort : Word.Length (CFL.Concat3 x y z) < K) :
    Word.Count ABC.a (Word.Concat x z) = 0 ∨
      Word.Count ABC.c (Word.Concat x z) = 0 := by
  have hmiddleWord :
      anbncnBlockWord K =
        Word.Concat u (Word.Concat (CFL.Concat3 x y z) v) := by
    rw [hword]
    simp [CFL.Concat5, CFL.Concat3, Word.Concat, List.append_assoc]
  cases anbncn_short_middle_count_a_or_c_zero hmiddleWord hshort with
  | inl ha =>
      apply Or.inl
      unfold CFL.Concat3 at ha
      rw [Word.count_concat, Word.count_concat] at ha
      rw [Word.count_concat]
      omega
  | inr hc =>
      apply Or.inr
      unfold CFL.Concat3 at hc
      rw [Word.count_concat, Word.count_concat] at hc
      rw [Word.count_concat]
      omega

theorem anbncn_xz_nonempty {x z : Word ABC}
    (h : x ≠ Word.Empty ∨ z ≠ Word.Empty) :
    Word.Concat x z ≠ Word.Empty := by
  intro hxz
  cases x with
  | nil =>
      cases h with
      | inl hx =>
          exact hx rfl
      | inr hz =>
          apply hz
          simpa [Word.Concat, Word.Empty] using hxz
  | cons _ _ =>
      cases hxz

theorem anbncn_pump_two_not_mem
    {u x y z v : Word ABC} {K : Nat}
    (hword : anbncnBlockWord K = CFL.Concat5 u x y z v)
    (hnonempty : x ≠ Word.Empty ∨ z ≠ Word.Empty)
    (hshort : Word.Length (CFL.Concat3 x y z) < K) :
    ¬ CFL.Pumped u x y z v 2 ∈ anbncnLanguage := by
  intro hpumped
  have hcounts := anbncn_members_have_equal_counts hpumped
  have hcountA :
      Word.Count ABC.a (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.a (Word.Concat x z) := by
    rw [cfl_pumped_two_count, ← hword, anbncn_block_count_a K]
  have hcountB :
      Word.Count ABC.b (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.b (Word.Concat x z) := by
    rw [cfl_pumped_two_count, ← hword, anbncn_block_count_b K]
  have hcountC :
      Word.Count ABC.c (CFL.Pumped u x y z v 2) =
        K + Word.Count ABC.c (Word.Concat x z) := by
    rw [cfl_pumped_two_count, ← hword, anbncn_block_count_c K]
  have hEqAB :
      K + Word.Count ABC.a (Word.Concat x z) =
        K + Word.Count ABC.b (Word.Concat x z) := by
    rw [← hcountA, ← hcountB]
    exact hcounts.left
  have hEqBC :
      K + Word.Count ABC.b (Word.Concat x z) =
        K + Word.Count ABC.c (Word.Concat x z) := by
    rw [← hcountB, ← hcountC]
    exact hcounts.right
  have hxzNonempty : Word.Concat x z ≠ Word.Empty :=
    anbncn_xz_nonempty hnonempty
  have hpos :
      0 < Word.Count ABC.a (Word.Concat x z) +
        Word.Count ABC.b (Word.Concat x z) +
        Word.Count ABC.c (Word.Concat x z) :=
    abc_count_sum_pos_of_nonempty hxzNonempty
  cases anbncn_xz_count_a_or_c_zero hword hshort with
  | inl ha0 =>
      have hb0 : Word.Count ABC.b (Word.Concat x z) = 0 := by omega
      have hc0 : Word.Count ABC.c (Word.Concat x z) = 0 := by omega
      omega
  | inr hc0 =>
      have hb0 : Word.Count ABC.b (Word.Concat x z) = 0 := by omega
      have ha0 : Word.Count ABC.a (Word.Concat x z) = 0 := by omega
      omega

theorem anbncn_no_pumping_property :
    ¬ CFLHasPumpingProperty anbncnLanguage := by
  intro hpump
  cases hpump with
  | intro K hK =>
      let w : Word ABC := anbncnBlockWord K
      have hwMem : w ∈ anbncnLanguage := by
        exists K
      have hwLength : K <= Word.Length w := by
        simp [w, anbncn_block_length]
        omega
      have hdec := hK.right w hwMem hwLength
      cases hdec with
      | intro u hu =>
          cases hu with
          | intro x hx =>
              cases hx with
              | intro y hy =>
                  cases hy with
                  | intro z hz =>
                      cases hz with
                      | intro v hv =>
                          exact anbncn_pump_two_not_mem hv.left
                            hv.right.left hv.right.right.left
                            (hv.right.right.right 2)

theorem anbncn_not_finite_production_context_free :
    ¬ FiniteProductionContextFreeLanguage anbncnLanguage := by
  intro hcf
  exact anbncn_no_pumping_property
    (finite_production_pumping_property hcf)

theorem anbncn_not_context_free :
    ¬ CFL.ContextFreeLanguage anbncnLanguage :=
  not_context_free_of_no_pumping_property anbncn_no_pumping_property

/-!
# Nonclosure Consequences

Because `{ a^n b^n c^* }` and `{ a^* b^n c^n }` are context-free but their
intersection is `{ a^n b^n c^n }`, finite-production context-free languages
are not closed under intersection. If they were closed under complement as
well as union, De Morgan's law would give intersection closure, so complement
closure fails too.
-/

theorem finite_production_cfl_intersection_nonclosure_from_anbncn_witnesses
    {L M : Language ABC}
    (hL : FiniteProductionContextFreeLanguage L)
    (hM : FiniteProductionContextFreeLanguage M)
    (hEq : Language.Equal (Language.Inter L M) anbncnLanguage) :
    ¬ ClosedUnderIntersection
      (FiniteProductionContextFreeLanguage (terminal := ABC)) := by
  intro hClosed
  have hInter : FiniteProductionContextFreeLanguage (Language.Inter L M) :=
    hClosed L M hL hM
  exact anbncn_not_finite_production_context_free
    (finite_production_context_free_of_equal hEq hInter)

theorem finite_production_cfls_not_closed_under_intersection :
    ¬ ClosedUnderIntersection
      (FiniteProductionContextFreeLanguage (terminal := ABC)) :=
  finite_production_cfl_intersection_nonclosure_from_anbncn_witnesses
    anbnCstar_finite_production_context_free
    astarBnCn_finite_production_context_free
    anbnCstar_inter_astarBnCn_exact

theorem complement_closure_and_union_closure_imply_intersection_closure
    {C : Language terminal -> Prop}
    (hExt : LanguageClassExtensional C)
    (hUnion : ClosedUnderUnion C)
    (hCompl : ClosedUnderComplement C) :
    ClosedUnderIntersection C := by
  classical
  intro L M hL hM
  let N : Language terminal :=
    Language.Compl (Language.Union (Language.Compl L) (Language.Compl M))
  have hN : C N := by
    have hUnionCompl : C (Language.Union (Language.Compl L) (Language.Compl M)) :=
      hUnion (Language.Compl L) (Language.Compl M)
      (hCompl L hL) (hCompl M hM)
    simpa [N] using hCompl
      (Language.Union (Language.Compl L) (Language.Compl M)) hUnionCompl
  apply hExt N (Language.Inter L M)
  · intro w
    constructor
    · intro hw
      change ¬ w ∈ Language.Union (Language.Compl L) (Language.Compl M) at hw
      constructor
      · by_cases hmem : w ∈ L
        · exact hmem
        · exact False.elim (hw (Or.inl hmem))
      · by_cases hmem : w ∈ M
        · exact hmem
        · exact False.elim (hw (Or.inr hmem))
    · intro hw
      change ¬ w ∈ Language.Union (Language.Compl L) (Language.Compl M)
      intro hUnionMem
      cases hUnionMem with
      | inl hnotL => exact hnotL hw.left
      | inr hnotM => exact hnotM hw.right
  · exact hN

theorem finite_production_cfl_complement_nonclosure_from_anbncn_witnesses
    {L M : Language ABC}
    (hL : FiniteProductionContextFreeLanguage L)
    (hM : FiniteProductionContextFreeLanguage M)
    (hEq : Language.Equal (Language.Inter L M) anbncnLanguage)
    (hUnion :
      ClosedUnderUnion
        (FiniteProductionContextFreeLanguage (terminal := ABC))) :
    ¬ ClosedUnderComplement
      (FiniteProductionContextFreeLanguage (terminal := ABC)) := by
  intro hCompl
  have hInterClosed :
      ClosedUnderIntersection
        (FiniteProductionContextFreeLanguage (terminal := ABC)) :=
    complement_closure_and_union_closure_imply_intersection_closure
      finite_production_context_free_extensional hUnion hCompl
  exact
    finite_production_cfl_intersection_nonclosure_from_anbncn_witnesses
      hL hM hEq hInterClosed

theorem anbncn_not_context_free_from_pumping_lemma
    (_pumpingLemma : CFL.PumpingLemmaConclusion anbncnLanguage) :
    ¬ CFL.ContextFreeLanguage anbncnLanguage :=
  anbncn_not_context_free

/-!
The concrete contradiction for `{ a^n b^n c^n | n >= 0 }` is now formalized:
no pumping length can satisfy the book's quantified CFL pumping property for
this language. Since the public {lean}`CFL.ContextFreeLanguage` predicate is
now the book-facing finite-production predicate, this gives the unconditional
{lean}`anbncn_not_context_free` theorem.
-/

end Section05
end Chapter04
end Book
end FoC
