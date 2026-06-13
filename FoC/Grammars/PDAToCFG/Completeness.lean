import FoC.Grammars.PDAToCFG.SummaryComputations

set_option doc.verso true

/-!
# PDA-to-CFG completeness and exactness
-/

namespace FoC
namespace Grammars

open Languages

namespace PDA

/-!
When a transition starts from an empty stack and later returns to an empty stack,
the intermediate pushed stack can be hidden inside an empty-summary witness. The
read and epsilon variants below package that first-step pattern.
-/

theorem emptySummaryComputesIn_read_of_stackThenEmptySummary
    {M : PDA input stack state}
    {n : Nat} {p r q : state} {a : input}
    {push : Word stack}
    {midInput targetInput : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hrest : StackThenEmptySummaryComputesIn M n r push midInput
      q targetInput) :
    EmptySummaryComputesIn M (n + 1) p (a :: midInput)
      q targetInput := by
  rcases hrest with
    ⟨stackSteps, emptySteps, middleState, emptyInput,
      hlen, hstack, hempty⟩
  simpa [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    EmptySummaryComputesIn.read htransition hstack hempty

theorem emptySummaryComputesIn_epsilon_of_stackThenEmptySummary
    {M : PDA input stack state}
    {n : Nat} {p r q : state}
    {push : Word stack}
    {midInput targetInput : Word input}
    (htransition : M.transition p none [] r push)
    (hrest : StackThenEmptySummaryComputesIn M n r push midInput
      q targetInput) :
    EmptySummaryComputesIn M (n + 1) p midInput q targetInput := by
  rcases hrest with
    ⟨stackSteps, emptySteps, middleState, emptyInput,
      hlen, hstack, hempty⟩
  simpa [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    EmptySummaryComputesIn.epsilon htransition hstack hempty

/-!
The following lemmas connect ordinary bounded PDA computations back to the
summary predicates. They are the reverse-direction counterpart of the earlier
soundness lemmas that interpreted CFG summaries as real computations.
-/

theorem emptySummaryComputesIn_of_emptyStackComputesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackComputesIn M n p sourceInput q targetInput) :
    EmptySummaryComputesIn M n p sourceInput q targetInput := by
  induction h with
  | zero q unread =>
      exact EmptySummaryComputesIn.zero q unread
  | read htransition htail ih =>
      rename_i p r q a midInput targetInput
      have hpush :
          StackSummaryComputesIn M 0 r ([] : Word stack) midInput r midInput :=
        StackSummaryComputesIn.nil r midInput
      simpa using
        EmptySummaryComputesIn.read htransition hpush ih
  | epsilon htransition htail ih =>
      rename_i p r q midInput targetInput
      have hpush :
          StackSummaryComputesIn M 0 r ([] : Word stack) midInput r midInput :=
        StackSummaryComputesIn.nil r midInput
      simpa using
        EmptySummaryComputesIn.epsilon htransition hpush ih

theorem emptySummaryComputesIn_of_step_emptyStack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hstep : Step M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M 1 p sourceInput q targetInput := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have hpushStack : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hpushNil : push = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpushStack
      simp [Word.Concat, hrestNil] at hlen
      omega
    have htransition' : M.transition p (some a) [] q [] := by
      simpa [hp, hq, hpopNil, hpushNil] using htransition
    have hsummary : EmptySummaryComputesIn M 1 p (a :: unread) q unread := by
      have hpushSummary :
          StackSummaryComputesIn M 0 q ([] : Word stack) unread q unread :=
        StackSummaryComputesIn.nil q unread
      have hempty :
          EmptySummaryComputesIn M 0 q unread q unread :=
        EmptySummaryComputesIn.zero q unread
      simpa using
        EmptySummaryComputesIn.read htransition' hpushSummary hempty
    simpa [hsource, htarget] using hsummary
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have hpushStack : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hpushNil : push = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpushStack
      simp [Word.Concat, hrestNil] at hlen
      omega
    have htransition' : M.transition p none [] q [] := by
      simpa [hp, hq, hpopNil, hpushNil] using htransition
    have hsummary : EmptySummaryComputesIn M 1 p unread q unread := by
      have hpushSummary :
          StackSummaryComputesIn M 0 q ([] : Word stack) unread q unread :=
        StackSummaryComputesIn.nil q unread
      have hempty :
          EmptySummaryComputesIn M 0 q unread q unread :=
        EmptySummaryComputesIn.zero q unread
      simpa using
        EmptySummaryComputesIn.epsilon htransition' hpushSummary hempty
    simpa [hsource, htarget] using hsummary

theorem emptySummaryComputesIn_of_computesIn_zero_emptyStack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : ComputesIn M 0
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M 0 p sourceInput q targetInput := by
  have hend := computesIn_zero_eq hcomp
  have hstate : p = q := by
    simpa using congrArg
      (fun c : Configuration input stack state => c.state) hend
  have hunread : sourceInput = targetInput := by
    simpa using congrArg
      (fun c : Configuration input stack state => c.unread) hend
  simpa [hstate, hunread] using
    EmptySummaryComputesIn.zero p sourceInput

theorem emptySummaryComputesIn_of_computesIn_one_emptyStack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : ComputesIn M 1
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M 1 p sourceInput q targetInput :=
  emptySummaryComputesIn_of_step_emptyStack (computesIn_one_inv hcomp)

/-!
Once the first-step reconstruction exists, the one-step top-pop summary follows
by taking an empty continuation. This gives the compact bridge used by the
bounded-computation cases below.
-/

theorem stackSummaryComputesIn_of_step_topPop
    {M : PDA input stack state}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    StackSummaryComputesIn M 1 p [A] sourceInput q targetInput := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hsourceStack : A :: tail = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have htargetStack : tail = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    rcases hnorm p' (some a) pop q' push htransition with
      hpopNil | hpopSingle
    · have hsourceLen := congrArg List.length hsourceStack
      have htargetLen := congrArg List.length htargetStack
      simp [Word.Concat, hpopNil] at hsourceLen htargetLen
      omega
    · rcases hpopSingle with ⟨B, hpopSingle⟩
      have hsourceCons : A :: tail = B :: restStack := by
        simpa [Word.Concat, hpopSingle] using hsourceStack
      have hA : A = B := (List.cons.inj hsourceCons).1
      have hrest : tail = restStack := (List.cons.inj hsourceCons).2
      have hpushNil : push = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hrestLen := congrArg List.length hrest
        have hlen := congrArg List.length htargetStack
        simp [Word.Concat] at hrestLen hlen
        omega
      have htransition' : M.transition p (some a) [A] q [] := by
        simpa [hp, hq, hpopSingle, hA, hpushNil] using htransition
      have hsummary : StackSummaryComputesIn M 1 p [A] (a :: unread) q unread := by
        simpa using
          StackSummaryComputesIn.popRead htransition'
            (StackSummaryComputesIn.nil (M := M) q unread)
      simpa [hsource, htarget] using hsummary
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hsourceStack : A :: tail = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have htargetStack : tail = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    rcases hnorm p' none pop q' push htransition with
      hpopNil | hpopSingle
    · have hsourceLen := congrArg List.length hsourceStack
      have htargetLen := congrArg List.length htargetStack
      simp [Word.Concat, hpopNil] at hsourceLen htargetLen
      omega
    · rcases hpopSingle with ⟨B, hpopSingle⟩
      have hsourceCons : A :: tail = B :: restStack := by
        simpa [Word.Concat, hpopSingle] using hsourceStack
      have hA : A = B := (List.cons.inj hsourceCons).1
      have hrest : tail = restStack := (List.cons.inj hsourceCons).2
      have hpushNil : push = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hrestLen := congrArg List.length hrest
        have hlen := congrArg List.length htargetStack
        simp [Word.Concat] at hrestLen hlen
        omega
      have htransition' : M.transition p none [A] q [] := by
        simpa [hp, hq, hpopSingle, hA, hpushNil] using htransition
      have hsummary : StackSummaryComputesIn M 1 p [A] unread q unread := by
        simpa using
          StackSummaryComputesIn.popEpsilon htransition'
            (StackSummaryComputesIn.nil (M := M) q unread)
      simpa [hsource, htarget] using hsummary

theorem stackSummaryComputesIn_of_computesIn_one_topPop
    {M : PDA input stack state}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hcomp : ComputesIn M 1
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    StackSummaryComputesIn M 1 p [A] sourceInput q targetInput :=
  stackSummaryComputesIn_of_step_topPop hnorm (computesIn_one_inv hcomp)

/-!
The two-step and at-most-two empty-stack summaries mirror the earlier direct CFG
lemmas, but now they work through summary predicates. This keeps the final CFG
generation theorem from depending on a large step-by-step case analysis.
-/

theorem emptySummaryComputesIn_of_computesIn_two_emptyStack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hcomp : ComputesIn M 2
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M 2 p sourceInput q targetInput := by
  rcases computesIn_succ_inv (M := M) (n := 1) hcomp with
    ⟨mid, hfirst, htail⟩
  have hsecond0 : Step M mid
      { state := q, unread := targetInput, stack := [] } :=
    computesIn_one_inv htail
  rcases step_cases hfirst with hread | heps
  · rcases hread with
      ⟨p', r, a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' :
        M.transition p (some a) [] r push := by
      simpa [hp, hpopNil] using htransition
    cases hd
    have hsecond : Step M
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [Word.Concat, hrestNil] using hsecond0
    rcases step_sourceStack_empty_or_single_of_step_to_emptyStack
        (M := M) hnorm hsecond with hpushNil | hpushSingle
    · have htransitionEmpty :
          M.transition p (some a) [] r [] := by
        simpa [hpushNil] using htransition'
      have hsecondEmpty : Step M
          { state := r, unread := unread, stack := [] }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushNil] using hsecond
      have hemptyTail :=
        emptySummaryComputesIn_of_step_emptyStack
          (M := M) (p := r) (q := q) hsecondEmpty
      have hpushSummary :
          StackSummaryComputesIn M 0 r ([] : Word stack) unread r unread :=
        StackSummaryComputesIn.nil r unread
      have hsummary : EmptySummaryComputesIn M 2 p (a :: unread) q targetInput := by
        simpa using
          EmptySummaryComputesIn.read htransitionEmpty hpushSummary hemptyTail
      simpa [hsource] using hsummary
    · rcases hpushSingle with ⟨A, hpushSingle⟩
      have htransitionSingle :
          M.transition p (some a) [] r [A] := by
        simpa [hpushSingle] using htransition'
      have hsecondTop : Step M
          { state := r, unread := unread, stack := A :: ([] : Word stack) }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushSingle] using hsecond
      have htopSummary :=
        stackSummaryComputesIn_of_step_topPop
          (M := M) (p := r) (q := q) (A := A)
          (tail := ([] : Word stack)) hnorm hsecondTop
      have hemptyTail :
          EmptySummaryComputesIn M 0 q targetInput q targetInput :=
        EmptySummaryComputesIn.zero q targetInput
      have hsummary : EmptySummaryComputesIn M 2 p (a :: unread) q targetInput := by
        simpa using
          EmptySummaryComputesIn.read htransitionSingle htopSummary hemptyTail
      simpa [hsource] using hsummary
  · rcases heps with
      ⟨p', r, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' :
        M.transition p none [] r push := by
      simpa [hp, hpopNil] using htransition
    cases hd
    have hsecond : Step M
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [Word.Concat, hrestNil] using hsecond0
    rcases step_sourceStack_empty_or_single_of_step_to_emptyStack
        (M := M) hnorm hsecond with hpushNil | hpushSingle
    · have htransitionEmpty :
          M.transition p none [] r [] := by
        simpa [hpushNil] using htransition'
      have hsecondEmpty : Step M
          { state := r, unread := unread, stack := [] }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushNil] using hsecond
      have hemptyTail :=
        emptySummaryComputesIn_of_step_emptyStack
          (M := M) (p := r) (q := q) hsecondEmpty
      have hpushSummary :
          StackSummaryComputesIn M 0 r ([] : Word stack) unread r unread :=
        StackSummaryComputesIn.nil r unread
      have hsummary : EmptySummaryComputesIn M 2 p unread q targetInput := by
        simpa using
          EmptySummaryComputesIn.epsilon htransitionEmpty hpushSummary hemptyTail
      simpa [hsource] using hsummary
    · rcases hpushSingle with ⟨A, hpushSingle⟩
      have htransitionSingle :
          M.transition p none [] r [A] := by
        simpa [hpushSingle] using htransition'
      have hsecondTop : Step M
          { state := r, unread := unread, stack := A :: ([] : Word stack) }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushSingle] using hsecond
      have htopSummary :=
        stackSummaryComputesIn_of_step_topPop
          (M := M) (p := r) (q := q) (A := A)
          (tail := ([] : Word stack)) hnorm hsecondTop
      have hemptyTail :
          EmptySummaryComputesIn M 0 q targetInput q targetInput :=
        EmptySummaryComputesIn.zero q targetInput
      have hsummary : EmptySummaryComputesIn M 2 p unread q targetInput := by
        simpa using
          EmptySummaryComputesIn.epsilon htransitionSingle htopSummary hemptyTail
      simpa [hsource] using hsummary

theorem emptySummaryComputesIn_of_computesIn_atMostTwo_emptyStack
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hn : n <= 2)
    (hcomp : ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M n p sourceInput q targetInput := by
  cases n with
  | zero =>
      exact emptySummaryComputesIn_of_computesIn_zero_emptyStack hcomp
  | succ n =>
      cases n with
      | zero =>
          exact emptySummaryComputesIn_of_computesIn_one_emptyStack hcomp
      | succ n =>
          cases n with
          | zero =>
              exact emptySummaryComputesIn_of_computesIn_two_emptyStack
                hnorm hcomp
          | succ n =>
              omega

/-!
Once a summary predicate is available, the proof returns to CFG syntax. Stack
summaries become chain derivations, empty summaries become derivations from
{lit}`empty p q`, and accepting empty summaries yield generated words from the
start symbol.
-/

theorem toCFG_betweenDerives_of_singleton_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {A : stack} {w : Word input}
    (h : ToCFGChainDerives M presentation p [A] q w) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord w) := by
  cases h with
  | cons hbetween htail =>
      cases htail with
      | nil _ =>
          simpa [Word.Concat, Word.Empty] using hbetween

theorem toCFGChainDerives_of_stackSummaryComputesIn
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p stackWord sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        ToCFGChainDerives M presentation p stackWord q consumed := by
  induction h with
  | nil q unread =>
      exact ⟨Word.Empty, by simp [Word.Concat, Word.Empty],
        ToCFGChainDerives.nil (M := M) (presentation := presentation) q⟩
  | cons htop hrest ihtop ihrest =>
      rename_i m n p r q A rest sourceInput midInput targetInput
      rcases ihtop with ⟨topWord, htopInput, htopChain⟩
      rcases ihrest with ⟨restWord, hrestInput, hrestChain⟩
      have hbetween :=
        toCFG_betweenDerives_of_singleton_chainDerives htopChain
      refine ⟨Word.Concat topWord restWord, ?_, ?_⟩
      · rw [htopInput, hrestInput]
        simp [Word.Concat, List.append_assoc]
      · exact ToCFGChainDerives.cons hbetween hrestChain
  | popRead htransition hpush ih =>
      rename_i n p r q A a push midInput targetInput
      rcases ih with ⟨chainWord, hchainInput, hchainDerives⟩
      let consumed := Word.Concat (Word.Symbol a) chainWord
      have hbetween : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed] using
          toCFG_popRead_of_chainDerives
            (M := M) (presentation := presentation)
            htransition hchainDerives
      refine ⟨consumed, ?_, ?_⟩
      · rw [hchainInput]
        simp [consumed, Word.Concat, Word.Symbol]
      · simpa [consumed, Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons hbetween
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)
  | popEpsilon htransition hpush ih =>
      rename_i n p r q A push midInput targetInput
      rcases ih with ⟨chainWord, hchainInput, hchainDerives⟩
      have hbetween : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord chainWord) :=
        toCFG_popEpsilon_of_chainDerives
          (M := M) (presentation := presentation)
          htransition hchainDerives
      refine ⟨chainWord, ?_, ?_⟩
      · exact hchainInput
      · simpa [Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons hbetween
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)
  | emptyBeforeTopRead htransition hpush htop ihpush ihtop =>
      rename_i m n p r s q A a push midInput topInput targetInput
      rcases ihpush with ⟨chainWord, hchainInput, hchainDerives⟩
      rcases ihtop with ⟨topWord, htopInput, htopChain⟩
      have htopDerives :=
        toCFG_betweenDerives_of_singleton_chainDerives htopChain
      let consumed :=
        Word.Concat (Word.Symbol a) (Word.Concat chainWord topWord)
      have hbetween : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed] using
          toCFG_emptyBeforeTopRead_of_chainDerives
            (M := M) (presentation := presentation)
            htransition hchainDerives htopDerives
      refine ⟨consumed, ?_, ?_⟩
      · rw [hchainInput, htopInput]
        simp [consumed, Word.Concat, Word.Symbol, List.append_assoc]
      · simpa [consumed, Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons hbetween
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)
  | emptyBeforeTopEpsilon htransition hpush htop ihpush ihtop =>
      rename_i m n p r s q A push midInput topInput targetInput
      rcases ihpush with ⟨chainWord, hchainInput, hchainDerives⟩
      rcases ihtop with ⟨topWord, htopInput, htopChain⟩
      have htopDerives :=
        toCFG_betweenDerives_of_singleton_chainDerives htopChain
      let consumed := Word.Concat chainWord topWord
      have hbetween : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed] using
          toCFG_emptyBeforeTopEpsilon_of_chainDerives
            (M := M) (presentation := presentation)
            htransition hchainDerives htopDerives
      refine ⟨consumed, ?_, ?_⟩
      · rw [hchainInput, htopInput]
        simp [consumed, Word.Concat, List.append_assoc]
      · simpa [consumed, Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons hbetween
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)

theorem toCFGChainDerives_of_stackSummaryComputes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputes M p stackWord sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        ToCFGChainDerives M presentation p stackWord q consumed := by
  rcases h with ⟨n, hn⟩
  exact toCFGChainDerives_of_stackSummaryComputesIn
    (M := M) (presentation := presentation) hn

/-!
Empty-summary derivations are obtained by induction on the summary witness. The
consumed word extracted from the PDA summary becomes the terminal frontier of
the CFG derivation from the corresponding empty-stack nonterminal.
-/

theorem toCFG_emptyDerives_of_emptySummaryComputesIn
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  induction h with
  | zero q unread =>
      refine ⟨Word.Empty, ?_, ?_⟩
      · simp [Word.Concat, Word.Empty]
      · simpa [SententialForm.terminalWord, Word.Empty] using
          toCFG_emptyRefl_derives
            (M := M) (presentation := presentation) (q := q)
  | read htransition hpush hempty ihempty =>
      rename_i m n p r s q a push midInput emptyInput targetInput
      rcases toCFGChainDerives_of_stackSummaryComputesIn
          (M := M) (presentation := presentation) hpush with
        ⟨chainWord, hchainInput, hchainDerives⟩
      rcases ihempty with ⟨emptyWord, hemptyInput, hemptyDerives⟩
      let consumed :=
        Word.Concat (Word.Symbol a) (Word.Concat chainWord emptyWord)
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed] using
          toCFG_emptyRead_of_chainDerives
            (M := M) (presentation := presentation)
            htransition hchainDerives hemptyDerives
      refine ⟨consumed, ?_, hbody⟩
      rw [hchainInput, hemptyInput]
      simp [consumed, Word.Concat, Word.Symbol, List.append_assoc]
  | epsilon htransition hpush hempty ihempty =>
      rename_i m n p r s q push midInput emptyInput targetInput
      rcases toCFGChainDerives_of_stackSummaryComputesIn
          (M := M) (presentation := presentation) hpush with
        ⟨chainWord, hchainInput, hchainDerives⟩
      rcases ihempty with ⟨emptyWord, hemptyInput, hemptyDerives⟩
      let consumed := Word.Concat chainWord emptyWord
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed] using
          toCFG_emptyEpsilon_of_chainDerives
            (M := M) (presentation := presentation)
            htransition hchainDerives hemptyDerives
      refine ⟨consumed, ?_, hbody⟩
      rw [hchainInput, hemptyInput]
      simp [consumed, Word.Concat, List.append_assoc]

theorem toCFG_emptyDerives_of_emptySummaryComputes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputes M p sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  rcases h with ⟨n, hn⟩
  exact toCFG_emptyDerives_of_emptySummaryComputesIn
    (M := M) (presentation := presentation) hn

theorem toCFG_emptyDerives_of_read_stackThenEmptySummary
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p r q : state} {a : input}
    {push : Word stack}
    {midInput targetInput : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hrest : StackThenEmptySummaryComputesIn M n r push midInput
      q targetInput) :
    exists consumed : Word input,
      a :: midInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  toCFG_emptyDerives_of_emptySummaryComputesIn
    (M := M) (presentation := presentation)
    (emptySummaryComputesIn_read_of_stackThenEmptySummary
      htransition hrest)

theorem toCFG_emptyDerives_of_epsilon_stackThenEmptySummary
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p r q : state}
    {push : Word stack}
    {midInput targetInput : Word input}
    (htransition : M.transition p none [] r push)
    (hrest : StackThenEmptySummaryComputesIn M n r push midInput
      q targetInput) :
    exists consumed : Word input,
      midInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  toCFG_emptyDerives_of_emptySummaryComputesIn
    (M := M) (presentation := presentation)
    (emptySummaryComputesIn_epsilon_of_stackThenEmptySummary
      htransition hrest)

theorem toCFG_emptyDerives_of_computesIn_atMostTwo_emptyStack_viaSummary
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hn : n <= 2)
    (hcomp : ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  toCFG_emptyDerives_of_emptySummaryComputesIn
    (emptySummaryComputesIn_of_computesIn_atMostTwo_emptyStack
      hnorm hn hcomp)

theorem toCFG_generates_of_emptySummaryAcceptsIn
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptySummaryComputesIn M n M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_emptySummaryComputesIn
      (M := M) (presentation := presentation) hcomp with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

theorem toCFG_generates_of_emptySummaryAccepts
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptySummaryComputes M M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_emptySummaryComputes
      (M := M) (presentation := presentation) hcomp with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

/-!
The final generated-language wrappers specialize the summary bridge to accepting
computations from the initial configuration. They cover the explicit small
bounds first, then hand off to the summary-completeness assumptions later in the
file.
-/

theorem toCFG_generates_of_acceptsIn_zero
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : ComputesIn M 0 (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_computesIn_zero_emptyStack
      (M := M) (presentation := presentation)
      (p := M.start) (q := qf)
      (sourceInput := w) (targetInput := ([] : Word input))
      (by simpa [initial] using hcomp) with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

theorem toCFG_generates_of_acceptsIn_one
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : ComputesIn M 1 (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_computesIn_one_emptyStack
      (M := M) (presentation := presentation)
      (p := M.start) (q := qf)
      (sourceInput := w) (targetInput := ([] : Word input))
      (by simpa [initial] using hcomp) with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

theorem toCFG_generates_of_acceptsIn_two
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input} {qf : state}
    (hnorm : PopsAtMostOne M)
    (haccept : M.accept qf)
    (hcomp : ComputesIn M 2 (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_computesIn_two_emptyStack
      (M := M) (presentation := presentation)
      (p := M.start) (q := qf)
      (sourceInput := w) (targetInput := ([] : Word input))
      hnorm (by simpa [initial] using hcomp) with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

theorem toCFG_generates_of_acceptsIn_atMostOne
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (hn : n <= 1)
    (haccept : M.accept qf)
    (hcomp : ComputesIn M n (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_computesIn_atMostOne_emptyStack
      (M := M) (presentation := presentation)
      (p := M.start) (q := qf)
      (sourceInput := w) (targetInput := ([] : Word input))
      hn (by simpa [initial] using hcomp) with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

theorem toCFG_generates_of_acceptsIn_atMostTwo
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (hnorm : PopsAtMostOne M)
    (hn : n <= 2)
    (haccept : M.accept qf)
    (hcomp : ComputesIn M n (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  apply toCFG_generates_of_emptySummaryAcceptsIn haccept
  exact emptySummaryComputesIn_of_computesIn_atMostTwo_emptyStack
    hnorm hn (by simpa [initial] using hcomp)

/-!
The final soundness step for generated CFG words goes the other direction:
derivations in the constructed grammar denote real PDA computations, so a word
generated from the start symbol is accepted by the original PDA.
-/

theorem toCFG_yields_sound
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {x y : SententialForm input (ToCFGNonterminal stack state)}
    {w : Word input}
    (h : CFG.Yields (ToCFG M presentation) x y)
    (hw : w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M) y) :
    w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M) x := by
  rcases h with ⟨u, v, A, rhs, hprod, hx, hy⟩
  rw [hy] at hw
  rw [hx]
  exact CFG.formLanguage_replace_sound
    (ToCFGSymbolLanguage M)
    (toCFG_production_sound (toCFG_producesFromList_sound hprod))
    hw

/-!
# Soundness: CFG to PDA

If the constructed grammar derives a terminal word, the original PDA accepts
that word.
-/

theorem toCFG_derives_sound
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {x y : SententialForm input (ToCFGNonterminal stack state)}
    {w : Word input}
    (h : CFG.Derives (ToCFG M presentation) x y)
    (hw : w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M) y) :
    w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M) x := by
  induction h with
  | refl _ =>
      exact hw
  | step hstep _ ih =>
      exact toCFG_yields_sound hstep (ih hw)

theorem toCFG_accepts_of_generates
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input}
    (h : w ∈ CFG.GeneratedLanguage (ToCFG M presentation)) :
    Accepts M w := by
  have hterminal : w ∈ CFG.FormLanguage (ToCFGSymbolLanguage M)
      (SententialForm.terminalWord
        (nt := ToCFGNonterminal stack state) w) :=
    CFG.terminalWord_mem_formLanguage (ToCFGSymbolLanguage M)
      (by intro a; rfl) w
  have hsound := toCFG_derives_sound h hterminal
  rcases hsound with ⟨first, tailWord, hfirst, htail, hwEq⟩
  cases htail
  rw [hwEq, Word.concat_empty_right]
  exact hfirst

/-!
# Summary-completeness assumptions

Completeness of the reverse direction is factored through summary-completeness
predicates. Normalized top-pop PDAs satisfy these predicates.
-/

def EmptySummaryComplete (M : PDA input stack state) : Prop :=
  forall n p q sourceInput targetInput,
    _root_.FoC.Grammars.PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } ->
        EmptySummaryComputesIn M n p sourceInput q targetInput

def EmptySummaryCompleteUpTo (M : PDA input stack state)
    (bound : Nat) : Prop :=
  forall n p q sourceInput targetInput,
    n <= bound ->
      _root_.FoC.Grammars.PDA.ComputesIn M n
        { state := p, unread := sourceInput, stack := [] }
        { state := q, unread := targetInput, stack := [] } ->
          EmptySummaryComputesIn M n p sourceInput q targetInput

def EmptySummaryCompleteForComputes (M : PDA input stack state) : Prop :=
  forall p q sourceInput targetInput,
    _root_.FoC.Grammars.PDA.Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } ->
        EmptySummaryComputes M p sourceInput q targetInput

def StackThenEmptySummaryComplete (M : PDA input stack state) : Prop :=
  forall n p q stackWord sourceInput targetInput,
    _root_.FoC.Grammars.PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := stackWord }
      { state := q, unread := targetInput, stack := [] } ->
        StackThenEmptySummaryComputesIn M n p stackWord sourceInput
          q targetInput

def StackThenEmptySummaryCompleteForComputes
    (M : PDA input stack state) : Prop :=
  forall p q stackWord sourceInput targetInput,
    _root_.FoC.Grammars.PDA.Computes M
      { state := p, unread := sourceInput, stack := stackWord }
      { state := q, unread := targetInput, stack := [] } ->
        StackThenEmptySummaryComputes M p stackWord sourceInput
          q targetInput

def TopPopEmptySummaryComplete (M : PDA input stack state) : Prop :=
  PopsAtMostOne M -> EmptySummaryComplete M

def TopPopStackThenEmptySummaryComplete
    (M : PDA input stack state) : Prop :=
  PopsAtMostOne M -> StackThenEmptySummaryComplete M

theorem emptySummaryCompleteForComputes_of_emptySummaryComplete
    {M : PDA input stack state}
    (hcomplete : EmptySummaryComplete M) :
    EmptySummaryCompleteForComputes M := by
  intro p q sourceInput targetInput hcomp
  rcases computes_exists_length hcomp with ⟨n, hcompIn⟩
  exact ⟨n, hcomplete n p q sourceInput targetInput hcompIn⟩

theorem stackThenEmptySummaryCompleteForComputes_of_complete
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryComplete M) :
    StackThenEmptySummaryCompleteForComputes M := by
  intro p q stackWord sourceInput targetInput hcomp
  rcases computes_exists_length hcomp with ⟨n, hcompIn⟩
  exact ⟨n, hcomplete n p q stackWord sourceInput targetInput hcompIn⟩

theorem emptySummaryComplete_of_stackThenEmptySummaryComplete
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryComplete M) :
    EmptySummaryComplete M := by
  intro n p q sourceInput targetInput hcomp
  exact emptySummaryComputesIn_of_stackThenEmptySummaryComputesIn_nil
    (hcomplete n p q ([] : Word stack) sourceInput targetInput hcomp)

/-!
Completeness is proved by reducing an ordinary empty-stack computation to the
stronger stack-then-empty summary property. The first-step lemma below handles
the nonzero case by asking the completeness hypothesis to summarize the pushed
stack after that first step.
-/

theorem emptySummaryComputesIn_of_step_emptyStack_of_stackThenEmptySummaryComplete
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    {mid : Configuration input stack state}
    (hcomplete : StackThenEmptySummaryComplete M)
    (hstep : Step M
      { state := p, unread := sourceInput, stack := [] } mid)
    (hrest : ComputesIn M n mid
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryComputesIn M (n + 1) p sourceInput q targetInput := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', r, a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' : M.transition p (some a) [] r push := by
      simpa [hp, hpopNil] using htransition
    have hrest' : ComputesIn M n
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [hd, hrestNil, Word.Concat] using hrest
    have hpushed :
        StackThenEmptySummaryComputesIn M n r push unread q targetInput :=
      hcomplete n r q push unread targetInput hrest'
    have hsummary :=
      emptySummaryComputesIn_read_of_stackThenEmptySummary
        htransition' hpushed
    simpa [hsource] using hsummary
  · rcases heps with
      ⟨p', r, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' : M.transition p none [] r push := by
      simpa [hp, hpopNil] using htransition
    have hrest' : ComputesIn M n
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [hd, hrestNil, Word.Concat] using hrest
    have hpushed :
        StackThenEmptySummaryComputesIn M n r push unread q targetInput :=
      hcomplete n r q push unread targetInput hrest'
    have hsummary :=
      emptySummaryComputesIn_epsilon_of_stackThenEmptySummary
        htransition' hpushed
    simpa [hsource] using hsummary

theorem emptySummaryComplete_of_stackThenEmptySummaryComplete_by_first_step
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryComplete M) :
    EmptySummaryComplete M := by
  intro n p q sourceInput targetInput hcomp
  cases n with
  | zero =>
      exact emptySummaryComputesIn_of_computesIn_zero_emptyStack hcomp
  | succ n =>
      rcases computesIn_succ_inv (M := M) (n := n) hcomp with
        ⟨mid, hstep, hrest⟩
      exact
        emptySummaryComputesIn_of_step_emptyStack_of_stackThenEmptySummaryComplete
          hcomplete hstep hrest

theorem emptySummaryCompleteForComputes_of_stackThenEmptySummaryCompleteForComputes
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryCompleteForComputes M) :
    EmptySummaryCompleteForComputes M := by
  intro p q sourceInput targetInput hcomp
  exact emptySummaryComputes_of_stackThenEmptySummaryComputes_nil
    (hcomplete p q ([] : Word stack) sourceInput targetInput hcomp)

theorem stackThenEmptySummaryComplete_of_topPop
    {M : PDA input stack state}
    (hnorm : PopsAtMostOne M) :
    StackThenEmptySummaryComplete M := by
  intro n p q stackWord sourceInput targetInput hcomp
  exact stackThenEmptySummaryComputesIn_of_computesIn_topPop hnorm hcomp

theorem topPopStackThenEmptySummaryComplete
    (M : PDA input stack state) :
    TopPopStackThenEmptySummaryComplete M := by
  intro hnorm
  exact stackThenEmptySummaryComplete_of_topPop hnorm

theorem emptySummaryComplete_of_topPop
    {M : PDA input stack state}
    (hnorm : PopsAtMostOne M) :
    EmptySummaryComplete M :=
  emptySummaryComplete_of_stackThenEmptySummaryComplete
    (stackThenEmptySummaryComplete_of_topPop hnorm)

theorem topPopEmptySummaryComplete
    (M : PDA input stack state) :
    TopPopEmptySummaryComplete M := by
  intro hnorm
  exact emptySummaryComplete_of_topPop hnorm

theorem emptySummaryCompleteUpTo_two_of_topPop
    {M : PDA input stack state}
    (hnorm : PopsAtMostOne M) :
    EmptySummaryCompleteUpTo M 2 := by
  intro n p q sourceInput targetInput hn hcomp
  exact emptySummaryComputesIn_of_computesIn_atMostTwo_emptyStack
    hnorm hn hcomp

/-!
The final exactness statements combine both inclusions: every generated word is
accepted by soundness, and every accepted word is generated once the appropriate
summary-completeness principle is available. Top-pop normalized PDAs satisfy
that principle.
-/

theorem toCFG_generates_of_acceptsIn_of_emptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (hcomplete : EmptySummaryComplete M)
    (haccept : M.accept qf)
    (hcomp : _root_.FoC.Grammars.PDA.ComputesIn M n (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  apply toCFG_generates_of_emptySummaryAcceptsIn haccept
  exact hcomplete n M.start qf w ([] : Word input)
    (by simpa [initial] using hcomp)

theorem toCFG_generates_of_acceptsIn_of_emptySummaryCompleteUpTo
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {bound n : Nat} {w : Word input} {qf : state}
    (hcomplete : EmptySummaryCompleteUpTo M bound)
    (hn : n <= bound)
    (haccept : M.accept qf)
    (hcomp : _root_.FoC.Grammars.PDA.ComputesIn M n (initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  apply toCFG_generates_of_emptySummaryAcceptsIn haccept
  exact hcomplete n M.start qf w ([] : Word input) hn
    (by simpa [initial] using hcomp)

theorem toCFG_generates_of_accepts_of_emptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input}
    (hcomplete : EmptySummaryComplete M)
    (haccepts : Accepts M w) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases haccepts with ⟨qf, haccept, hcomp⟩
  rcases _root_.FoC.Grammars.PDA.computes_exists_length hcomp with
    ⟨n, hcompIn⟩
  exact toCFG_generates_of_acceptsIn_of_emptySummaryComplete
    (M := M) (presentation := presentation)
    hcomplete haccept hcompIn

theorem toCFG_generates_of_accepts_of_emptySummaryCompleteForComputes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {w : Word input}
    (hcomplete : EmptySummaryCompleteForComputes M)
    (haccepts : Accepts M w) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases haccepts with ⟨qf, haccept, hcomp⟩
  exact toCFG_generates_of_emptySummaryAccepts
    (M := M) (presentation := presentation)
    haccept (hcomplete M.start qf w ([] : Word input) hcomp)

theorem toCFG_language_exact_of_emptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : EmptySummaryComplete M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (AcceptedLanguage M) := by
  intro w
  constructor
  · intro h
    exact toCFG_accepts_of_generates h
  · intro h
    exact toCFG_generates_of_accepts_of_emptySummaryComplete
      (M := M) (presentation := presentation) hcomplete h

theorem toCFG_language_exact_of_emptySummaryCompleteForComputes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : EmptySummaryCompleteForComputes M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (AcceptedLanguage M) := by
  intro w
  constructor
  · intro h
    exact toCFG_accepts_of_generates h
  · intro h
    exact toCFG_generates_of_accepts_of_emptySummaryCompleteForComputes
      (M := M) (presentation := presentation) hcomplete h

theorem toCFG_language_exact_of_stackThenEmptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : StackThenEmptySummaryComplete M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (AcceptedLanguage M) :=
  toCFG_language_exact_of_emptySummaryComplete
    (M := M) (presentation := presentation)
    (emptySummaryComplete_of_stackThenEmptySummaryComplete hcomplete)

theorem toCFG_language_exact_of_stackThenEmptySummaryCompleteForComputes
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : StackThenEmptySummaryCompleteForComputes M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (AcceptedLanguage M) :=
  toCFG_language_exact_of_emptySummaryCompleteForComputes
    (M := M) (presentation := presentation)
    (emptySummaryCompleteForComputes_of_stackThenEmptySummaryCompleteForComputes
      hcomplete)

theorem toCFG_language_exact_of_topPop
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hnorm : PopsAtMostOne M) :
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (AcceptedLanguage M) :=
  toCFG_language_exact_of_stackThenEmptySummaryComplete
    (M := M) (presentation := presentation)
    (stackThenEmptySummaryComplete_of_topPop hnorm)

def ToCFGTopPopExact (M : PDA input stack state)
    (presentation : FinitePresentation M) : Prop :=
  PopsAtMostOne M ->
    Language.Equal (CFG.GeneratedLanguage (ToCFG M presentation))
      (PDA.AcceptedLanguage M)

theorem toCFG_topPopExact_of_emptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : TopPopEmptySummaryComplete M) :
    ToCFGTopPopExact M presentation := by
  intro hnorm
  exact toCFG_language_exact_of_emptySummaryComplete
    (M := M) (presentation := presentation) (hcomplete hnorm)

theorem toCFG_topPopExact_of_stackThenEmptySummaryComplete
    {M : PDA input stack state} {presentation : FinitePresentation M}
    (hcomplete : TopPopStackThenEmptySummaryComplete M) :
    ToCFGTopPopExact M presentation := by
  intro hnorm
  exact toCFG_language_exact_of_stackThenEmptySummaryComplete
    (M := M) (presentation := presentation) (hcomplete hnorm)

theorem toCFG_topPopExact
    (M : PDA input stack state) (presentation : FinitePresentation M) :
    ToCFGTopPopExact M presentation := by
  intro hnorm
  exact toCFG_language_exact_of_topPop
    (M := M) (presentation := presentation) hnorm


end PDA

end Grammars
end FoC
