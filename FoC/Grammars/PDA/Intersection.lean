import FoC.Grammars.PDA
import FoC.Languages.DFA

set_option doc.verso true

namespace FoC
namespace Grammars

open Languages

/-!
# Intersecting Pushdown and Finite Automata

The product construction runs a pushdown automaton and a deterministic finite
automaton over the same input. Epsilon PDA moves leave the DFA coordinate
unchanged, while input-consuming moves advance both machines.

The construction preserves finite presentation and accepts exactly the
intersection of the PDA and DFA languages.
-/

def PDAIntersectDFA (P : PDA input stack pstate) (D : DFA input dstate) :
    PDA input stack (pstate × dstate) where
  start := (P.start, D.start)
  transition := fun q input pop r push =>
    match input with
    | none => P.transition q.1 none pop r.1 push ∧ r.2 = q.2
    | some a => P.transition q.1 (some a) pop r.1 push ∧ r.2 = D.step q.2 a
  accept := fun q => P.accept q.1 ∧ D.accept q.2
  statesFinite := Foundation.FiniteType.product P.statesFinite D.statesFinite

structure DFAAcceptingPresentation (D : DFA input dstate) where
  acceptingStates : List dstate
  accept_complete : forall q, D.accept q <-> q ∈ acceptingStates

/-!
The product PDA must also have a finite presentation. The next definitions turn
each transition rule of the original PDA into one rule for every DFA state. For
epsilon PDA moves the DFA coordinate stays fixed; for input-consuming moves it
updates with {lit}`D.step`.
-/

def dfaAcceptingPresentation
    (D : DFA input dstate) [DecidablePred D.accept] :
    DFAAcceptingPresentation D where
  acceptingStates := D.statesFinite.elems.filter (fun q => decide (D.accept q))
  accept_complete := by
    intro q
    constructor
    · intro hq
      apply List.mem_filter.mpr
      constructor
      · exact D.statesFinite.complete q
      · simpa using hq
    · intro hq
      simpa using (List.mem_filter.mp hq).2

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

def pdaIntersectDFA_finitePresentation_auto
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    [DecidablePred D.accept] :
    PDA.FinitePresentation (PDAIntersectDFA P D) :=
  pdaIntersectDFA_finitePresentation P D presentation
    (dfaAcceptingPresentation D)

/-!
## Product Exactness

The lifting and projection lemmas relate computations of the product PDA to
computations of the original PDA and runs of the DFA. Their language-level
summary is exact intersection.

Exactness has two directions. A product computation projects to a PDA
computation and a DFA run, and a PDA computation whose input is accepted by
the DFA can be lifted to a product computation.

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

end Grammars
end FoC
