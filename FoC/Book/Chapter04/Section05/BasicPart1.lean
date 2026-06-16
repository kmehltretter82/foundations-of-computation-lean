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

/-!
The product PDA is finite because both components are finite. The finite
presentation packages the generated transition list and accepting product states
so the closure theorems can call the generic PDA-to-CFG pipeline.
-/

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

/-!
Correctness of the product construction has two projections: the PDA component
tracks the context-free language, and the DFA component tracks the regular
language. Exactness combines those projections into intersection.
-/

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

theorem context_free_inter_regular_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (hR : RegularLanguage.Regular R) :
    CFL.ContextFreeLanguage (Language.Inter L R) :=
  context_free_inter_dfa_recognizable_context_free inputFinite hL
    (RegularLanguage.regular_is_dfa_recognizable hR)

theorem context_free_diff_regular_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (hR : RegularLanguage.Regular R) :
    CFL.ContextFreeLanguage (Language.Diff L R) :=
  context_free_diff_dfa_recognizable_context_free inputFinite hL
    (RegularLanguage.regular_is_dfa_recognizable hR)

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
{lit}`{ a^n b^n c^n }`. This gives the closure-based nonclosure argument after the
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

/-!
For the {lit}`a^n b^n c^*` grammar, generation is constructive first and
soundness second. The production-soundness theorem checks that each production
preserves the intended language of the current nonterminal.
-/

end Section05
end Chapter04
end Book
end FoC
