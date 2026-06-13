import FoC.Grammars.PDAToCFG.ReverseDerivations

set_option doc.verso true

/-!
# PDA-to-CFG summary computations
-/

namespace FoC
namespace Grammars

open Languages

namespace PDA

/-!
The summary predicates below are a more scalable replacement for the explicit
zero/one/two-step lemmas. They record just the stack effect that matters to the
CFG construction: empty-stack paths and paths that remove a specified stack word.
-/

inductive EmptyStackComputesIn (M : PDA input stack state) :
    Nat -> state -> Word input -> state -> Word input -> Prop where
  | zero (q : state) (unread : Word input) :
      EmptyStackComputesIn M 0 q unread q unread
  | read {n : Nat} {p r q : state} {a : input}
      {midInput targetInput : Word input} :
      M.transition p (some a) [] r [] ->
        EmptyStackComputesIn M n r midInput q targetInput ->
          EmptyStackComputesIn M (n + 1) p (a :: midInput) q targetInput
  | epsilon {n : Nat} {p r q : state}
      {midInput targetInput : Word input} :
      M.transition p none [] r [] ->
        EmptyStackComputesIn M n r midInput q targetInput ->
          EmptyStackComputesIn M (n + 1) p midInput q targetInput

theorem emptyStackComputesIn_computesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackComputesIn M n p sourceInput q targetInput) :
    ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } := by
  induction h with
  | zero q unread =>
      exact ComputesIn.zero _
  | read htransition htail ih =>
      rename_i p0 r0 q0 a0 midInput0 targetInput0
      have hstep : Step M
          { state := p0, unread := a0 :: midInput0, stack := [] }
          { state := r0, unread := midInput0, stack := [] } := by
        simpa [Word.Concat] using
          Step.read (M := M) (unread := midInput0)
            (restStack := ([] : Word stack)) htransition
      exact ComputesIn.succ hstep ih
  | epsilon htransition htail ih =>
      rename_i p0 r0 q0 midInput0 targetInput0
      have hstep : Step M
          { state := p0, unread := midInput0, stack := [] }
          { state := r0, unread := midInput0, stack := [] } := by
        simpa [Word.Concat] using
          Step.epsilon (M := M) (unread := midInput0)
            (restStack := ([] : Word stack)) htransition
      exact ComputesIn.succ hstep ih

theorem emptyStackComputesIn_computes
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackComputesIn M n p sourceInput q targetInput) :
    Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  computesIn_computes (emptyStackComputesIn_computesIn h)

theorem toCFG_emptyDerives_of_emptyStackComputesIn
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackComputesIn M n p sourceInput q targetInput) :
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
  | read htransition htail ih =>
      rename_i p0 r0 q0 a0 midInput0 targetInput0
      rcases ih with ⟨tailWord, htailInput, htailDerive⟩
      refine ⟨Word.Concat (Word.Symbol a0) tailWord, ?_, ?_⟩
      · rw [htailInput]
        simp [Word.Concat, Word.Symbol]
      · simpa [Word.Concat, Word.Symbol, Word.Empty, List.append_assoc] using
          toCFG_emptyRead_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p0) (r := r0) (s := r0) (q := q0)
            (a := a0) (push := ([] : Word stack))
            (chainWord := (Word.Empty : Word input))
            (emptyWord := tailWord)
            htransition
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) r0)
            htailDerive
  | epsilon htransition htail ih =>
      rename_i p0 r0 q0 midInput0 targetInput0
      rcases ih with ⟨tailWord, htailInput, htailDerive⟩
      refine ⟨tailWord, ?_, ?_⟩
      · exact htailInput
      · simpa [Word.Concat, Word.Empty, List.append_assoc] using
          toCFG_emptyEpsilon_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p0) (r := r0) (s := r0) (q := q0)
            (push := ([] : Word stack))
            (chainWord := (Word.Empty : Word input))
            (emptyWord := tailWord)
            htransition
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) r0)
            htailDerive

theorem toCFG_generates_of_emptyStackAcceptsIn
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptyStackComputesIn M n M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  rcases toCFG_emptyDerives_of_emptyStackComputesIn
      (M := M) (presentation := presentation) hcomp with
    ⟨consumed, hinput, hbody⟩
  have hgen := toCFG_start_derives
    (M := M) (presentation := presentation)
    (q := qf) (w := consumed) haccept hbody
  rw [hinput]
  simpa [Word.Concat, Word.Empty] using hgen

/-!
Stack summaries generalize the empty-stack predicate. They describe the input
consumed while removing an entire pushed stack word, and the combined
stack-then-empty predicate links that removal to the remaining computation to an
accepting empty stack.
-/

inductive StackSummaryComputesIn (M : PDA input stack state) :
    Nat -> state -> Word stack -> Word input -> state -> Word input -> Prop where
  | nil (q : state) (unread : Word input) :
      StackSummaryComputesIn M 0 q [] unread q unread
  | cons {m n : Nat} {p r q : state} {A : stack}
      {rest : Word stack} {sourceInput midInput targetInput : Word input} :
      StackSummaryComputesIn M m p [A] sourceInput r midInput ->
        StackSummaryComputesIn M n r rest midInput q targetInput ->
          StackSummaryComputesIn M (m + n) p (A :: rest)
            sourceInput q targetInput
  | popRead {n : Nat} {p r q : state} {A : stack} {a : input}
      {push : Word stack} {midInput targetInput : Word input} :
      M.transition p (some a) [A] r push ->
        StackSummaryComputesIn M n r push midInput q targetInput ->
          StackSummaryComputesIn M (n + 1) p [A]
            (a :: midInput) q targetInput
  | popEpsilon {n : Nat} {p r q : state} {A : stack}
      {push : Word stack} {midInput targetInput : Word input} :
      M.transition p none [A] r push ->
        StackSummaryComputesIn M n r push midInput q targetInput ->
          StackSummaryComputesIn M (n + 1) p [A]
            midInput q targetInput
  | emptyBeforeTopRead {m n : Nat} {p r s q : state}
      {A : stack} {a : input} {push : Word stack}
      {midInput topInput targetInput : Word input} :
      M.transition p (some a) [] r push ->
        StackSummaryComputesIn M m r push midInput s topInput ->
          StackSummaryComputesIn M n s [A] topInput q targetInput ->
            StackSummaryComputesIn M (m + n + 1) p [A]
              (a :: midInput) q targetInput
  | emptyBeforeTopEpsilon {m n : Nat} {p r s q : state}
      {A : stack} {push : Word stack}
      {midInput topInput targetInput : Word input} :
      M.transition p none [] r push ->
        StackSummaryComputesIn M m r push midInput s topInput ->
          StackSummaryComputesIn M n s [A] topInput q targetInput ->
            StackSummaryComputesIn M (m + n + 1) p [A]
              midInput q targetInput

inductive EmptySummaryComputesIn (M : PDA input stack state) :
    Nat -> state -> Word input -> state -> Word input -> Prop where
  | zero (q : state) (unread : Word input) :
      EmptySummaryComputesIn M 0 q unread q unread
  | read {m n : Nat} {p r s q : state} {a : input}
      {push : Word stack}
      {midInput emptyInput targetInput : Word input} :
      M.transition p (some a) [] r push ->
        StackSummaryComputesIn M m r push midInput s emptyInput ->
          EmptySummaryComputesIn M n s emptyInput q targetInput ->
            EmptySummaryComputesIn M (m + n + 1) p
              (a :: midInput) q targetInput
  | epsilon {m n : Nat} {p r s q : state}
      {push : Word stack}
      {midInput emptyInput targetInput : Word input} :
      M.transition p none [] r push ->
        StackSummaryComputesIn M m r push midInput s emptyInput ->
          EmptySummaryComputesIn M n s emptyInput q targetInput ->
            EmptySummaryComputesIn M (m + n + 1) p
              midInput q targetInput

def StackSummaryComputes (M : PDA input stack state)
    (p : state) (stackWord : Word stack) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  exists n, StackSummaryComputesIn M n p stackWord sourceInput q targetInput

def EmptySummaryComputes (M : PDA input stack state)
    (p : state) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  exists n, EmptySummaryComputesIn M n p sourceInput q targetInput

def StackThenEmptySummaryComputesIn (M : PDA input stack state)
    (n : Nat) (p : state) (stackWord : Word stack)
    (sourceInput : Word input) (q : state)
    (targetInput : Word input) : Prop :=
  exists stackSteps : Nat, exists emptySteps : Nat,
    exists middleState : state, exists middleInput : Word input,
      n = stackSteps + emptySteps ∧
        StackSummaryComputesIn M stackSteps p stackWord sourceInput
          middleState middleInput ∧
        EmptySummaryComputesIn M emptySteps middleState middleInput
          q targetInput

def StackThenEmptySummaryComputes (M : PDA input stack state)
    (p : state) (stackWord : Word stack) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  exists n, StackThenEmptySummaryComputesIn M n p stackWord sourceInput
    q targetInput

/-!
Soundness of the summary predicates says that their inductive structure really
does describe PDA computations. The proofs thread an arbitrary stack tail through
the path, because summaries are meant to compose inside larger stack contexts.
-/

theorem stackSummaryComputesIn_computesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p stackWord sourceInput q targetInput) :
    forall tail : Word stack,
      ComputesIn M n
        { state := p, unread := sourceInput,
          stack := Word.Concat stackWord tail }
        { state := q, unread := targetInput, stack := tail } := by
  induction h with
  | nil q unread =>
      intro tail
      simpa [Word.Concat, Word.Empty] using
        ComputesIn.zero
          ({ state := q, unread := unread, stack := tail } :
            Configuration input stack state)
  | cons htop hrest ihtop ihrest =>
      rename_i m n p r q A rest sourceInput midInput targetInput
      intro tail
      have hfirst := ihtop (Word.Concat rest tail)
      have htail := ihrest tail
      simpa [Word.Concat, List.append_assoc] using
        computesIn_trans hfirst htail
  | popRead htransition htail ih =>
      rename_i n p r q A a push midInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := a :: midInput, stack := A :: tail }
          { state := r, unread := midInput,
            stack := Word.Concat push tail } := by
        simpa [Word.Concat] using
          Step.read (M := M) (unread := midInput)
            (restStack := tail) htransition
      simpa [Word.Concat] using
        ComputesIn.succ hstep (ih tail)
  | popEpsilon htransition htail ih =>
      rename_i n p r q A push midInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := midInput, stack := A :: tail }
          { state := r, unread := midInput,
            stack := Word.Concat push tail } := by
        simpa [Word.Concat] using
          Step.epsilon (M := M) (unread := midInput)
            (restStack := tail) htransition
      simpa [Word.Concat] using
        ComputesIn.succ hstep (ih tail)
  | emptyBeforeTopRead htransition hpush htop ihpush ihtop =>
      rename_i m n p r s q A a push midInput topInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := a :: midInput, stack := A :: tail }
          { state := r, unread := midInput,
            stack := Word.Concat push (A :: tail) } := by
        simpa [Word.Concat] using
          Step.read (M := M) (unread := midInput)
            (restStack := A :: tail) htransition
      have hpushComp := ihpush (A :: tail)
      have htopComp := ihtop tail
      have hrest := computesIn_trans hpushComp htopComp
      simpa [Word.Concat, List.append_assoc] using
        ComputesIn.succ hstep hrest
  | emptyBeforeTopEpsilon htransition hpush htop ihpush ihtop =>
      rename_i m n p r s q A push midInput topInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := midInput, stack := A :: tail }
          { state := r, unread := midInput,
            stack := Word.Concat push (A :: tail) } := by
        simpa [Word.Concat] using
          Step.epsilon (M := M) (unread := midInput)
            (restStack := A :: tail) htransition
      have hpushComp := ihpush (A :: tail)
      have htopComp := ihtop tail
      have hrest := computesIn_trans hpushComp htopComp
      simpa [Word.Concat, List.append_assoc] using
        ComputesIn.succ hstep hrest

theorem stackSummaryComputes_computes
    {M : PDA input stack state}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputes M p stackWord sourceInput q targetInput) :
    forall tail : Word stack,
      Computes M
        { state := p, unread := sourceInput,
          stack := Word.Concat stackWord tail }
        { state := q, unread := targetInput, stack := tail } := by
  rcases h with ⟨n, hn⟩
  intro tail
  exact computesIn_computes (stackSummaryComputesIn_computesIn hn tail)

theorem stackSummaryComputesIn_computes
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p stackWord sourceInput q targetInput) :
    forall tail : Word stack,
      Computes M
        { state := p, unread := sourceInput,
          stack := Word.Concat stackWord tail }
        { state := q, unread := targetInput, stack := tail } := by
  intro tail
  exact computesIn_computes (stackSummaryComputesIn_computesIn h tail)

/-!
Empty summaries are also interpreted in an arbitrary tail context. This tail
version is the workhorse for composing an empty-stack summary after another
summary has exposed the rest of the stack.
-/

theorem emptySummaryComputesIn_computesIn_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    forall tail : Word stack,
      ComputesIn M n
        { state := p, unread := sourceInput, stack := tail }
        { state := q, unread := targetInput, stack := tail } := by
  induction h with
  | zero q unread =>
      intro tail
      exact ComputesIn.zero _
  | read htransition hpush hempty ihempty =>
      rename_i m n p r s q a push midInput emptyInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := a :: midInput, stack := tail }
          { state := r, unread := midInput,
            stack := Word.Concat push tail } := by
        simpa [Word.Concat] using
          Step.read (M := M) (unread := midInput)
            (restStack := tail) htransition
      have hpushComp := stackSummaryComputesIn_computesIn hpush tail
      have hemptyComp := ihempty tail
      have hrest := computesIn_trans hpushComp hemptyComp
      simpa [Word.Concat, List.append_assoc] using
        ComputesIn.succ hstep hrest
  | epsilon htransition hpush hempty ihempty =>
      rename_i m n p r s q push midInput emptyInput targetInput
      intro tail
      have hstep : Step M
          { state := p, unread := midInput, stack := tail }
          { state := r, unread := midInput,
            stack := Word.Concat push tail } := by
        simpa [Word.Concat] using
          Step.epsilon (M := M) (unread := midInput)
            (restStack := tail) htransition
      have hpushComp := stackSummaryComputesIn_computesIn hpush tail
      have hemptyComp := ihempty tail
      have hrest := computesIn_trans hpushComp hemptyComp
      simpa [Word.Concat, List.append_assoc] using
        ComputesIn.succ hstep hrest

theorem emptySummaryComputesIn_computesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  emptySummaryComputesIn_computesIn_tail h ([] : Word stack)

theorem emptySummaryComputesIn_computes
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  computesIn_computes (emptySummaryComputesIn_computesIn h)

theorem emptySummaryComputesIn_computes_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput)
    (tail : Word stack) :
    Computes M
      { state := p, unread := sourceInput, stack := tail }
      { state := q, unread := targetInput, stack := tail } :=
  computesIn_computes (emptySummaryComputesIn_computesIn_tail h tail)

theorem emptySummaryComputes_computes
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputes M p sourceInput q targetInput) :
    Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } := by
  rcases h with ⟨n, hn⟩
  exact emptySummaryComputesIn_computes hn

theorem emptySummaryComputes_computes_tail
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputes M p sourceInput q targetInput)
    (tail : Word stack) :
    Computes M
      { state := p, unread := sourceInput, stack := tail }
      { state := q, unread := targetInput, stack := tail } := by
  rcases h with ⟨n, hn⟩
  exact emptySummaryComputesIn_computes_tail hn tail

theorem stackSummaryComputes_of_stackSummaryComputesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p stackWord sourceInput q targetInput) :
    StackSummaryComputes M p stackWord sourceInput q targetInput :=
  ⟨n, h⟩

theorem emptySummaryComputes_of_emptySummaryComputesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    EmptySummaryComputes M p sourceInput q targetInput :=
  ⟨n, h⟩

/-!
The combined stack-then-empty summary represents the common shape of a
transition that first discharges a pushed stack word and then continues with an
empty-stack computation. These lemmas connect the combined predicate back to
ordinary PDA computations with a tail stack.
-/

theorem stackThenEmptySummaryComputesIn_computesIn_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputesIn M n p stackWord sourceInput
      q targetInput) :
    forall tail : Word stack,
      ComputesIn M n
        { state := p, unread := sourceInput,
          stack := Word.Concat stackWord tail }
        { state := q, unread := targetInput, stack := tail } := by
  rcases h with
    ⟨stackSteps, emptySteps, middleState, middleInput,
      hlen, hstack, hempty⟩
  intro tail
  have hstackComp := stackSummaryComputesIn_computesIn hstack tail
  have hemptyComp := emptySummaryComputesIn_computesIn_tail hempty tail
  have hcomp := computesIn_trans hstackComp hemptyComp
  simpa [hlen] using hcomp

theorem stackThenEmptySummaryComputesIn_computesIn
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputesIn M n p stackWord sourceInput
      q targetInput) :
    ComputesIn M n
      { state := p, unread := sourceInput, stack := stackWord }
      { state := q, unread := targetInput, stack := [] } := by
  simpa [Word.Concat, Word.Empty] using
    stackThenEmptySummaryComputesIn_computesIn_tail h ([] : Word stack)

theorem stackThenEmptySummaryComputesIn_computes_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputesIn M n p stackWord sourceInput
      q targetInput)
    (tail : Word stack) :
    Computes M
      { state := p, unread := sourceInput,
        stack := Word.Concat stackWord tail }
      { state := q, unread := targetInput, stack := tail } :=
  computesIn_computes
    (stackThenEmptySummaryComputesIn_computesIn_tail h tail)

theorem stackThenEmptySummaryComputes_computes_tail
    {M : PDA input stack state}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputes M p stackWord sourceInput
      q targetInput)
    (tail : Word stack) :
    Computes M
      { state := p, unread := sourceInput,
        stack := Word.Concat stackWord tail }
      { state := q, unread := targetInput, stack := tail } := by
  rcases h with ⟨n, hn⟩
  exact stackThenEmptySummaryComputesIn_computes_tail hn tail

theorem stackThenEmptySummaryComputesIn_of_stack_and_empty
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {stackWord : Word stack}
    {sourceInput midInput targetInput : Word input}
    (hstack : StackSummaryComputesIn M m p stackWord sourceInput
      r midInput)
    (hempty : EmptySummaryComputesIn M n r midInput q targetInput) :
    StackThenEmptySummaryComputesIn M (m + n) p stackWord sourceInput
      q targetInput :=
  ⟨m, n, r, midInput, rfl, hstack, hempty⟩

theorem stackThenEmptySummaryComputesIn_of_stack
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (hstack : StackSummaryComputesIn M n p stackWord sourceInput
      q targetInput) :
    StackThenEmptySummaryComputesIn M n p stackWord sourceInput
      q targetInput := by
  refine ⟨n, 0, q, targetInput, ?_, hstack, ?_⟩
  · simp
  · exact EmptySummaryComputesIn.zero q targetInput

theorem stackThenEmptySummaryComputesIn_of_empty
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hempty : EmptySummaryComputesIn M n p sourceInput q targetInput) :
    StackThenEmptySummaryComputesIn M n p ([] : Word stack) sourceInput
      q targetInput := by
  refine ⟨0, n, p, sourceInput, ?_, ?_, hempty⟩
  · simp
  · exact StackSummaryComputesIn.nil p sourceInput

theorem stackThenEmptySummaryComputes_of_stack_and_empty
    {M : PDA input stack state}
    {p r q : state} {stackWord : Word stack}
    {sourceInput midInput targetInput : Word input}
    (hstack : StackSummaryComputes M p stackWord sourceInput r midInput)
    (hempty : EmptySummaryComputes M r midInput q targetInput) :
    StackThenEmptySummaryComputes M p stackWord sourceInput
      q targetInput := by
  rcases hstack with ⟨m, hm⟩
  rcases hempty with ⟨n, hn⟩
  exact ⟨m + n, stackThenEmptySummaryComputesIn_of_stack_and_empty hm hn⟩

theorem stackThenEmptySummaryComputes_of_stack
    {M : PDA input stack state}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (hstack : StackSummaryComputes M p stackWord sourceInput
      q targetInput) :
    StackThenEmptySummaryComputes M p stackWord sourceInput
      q targetInput := by
  rcases hstack with ⟨n, hn⟩
  exact ⟨n, stackThenEmptySummaryComputesIn_of_stack hn⟩

theorem stackThenEmptySummaryComputes_of_empty
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hempty : EmptySummaryComputes M p sourceInput q targetInput) :
    StackThenEmptySummaryComputes M p ([] : Word stack) sourceInput
      q targetInput := by
  rcases hempty with ⟨n, hn⟩
  exact ⟨n, stackThenEmptySummaryComputesIn_of_empty hn⟩

/-!
Transitivity is what makes summaries usable as proof objects rather than just
descriptions of individual steps. Once a computation has been split into
summary-sized pieces, these lemmas put the pieces back together.
-/

theorem emptySummaryComputesIn_trans
    {M : PDA input stack state}
    {m n : Nat} {p r q : state}
    {sourceInput midInput targetInput : Word input}
    (hleft : EmptySummaryComputesIn M m p sourceInput r midInput)
    (hright : EmptySummaryComputesIn M n r midInput q targetInput) :
    EmptySummaryComputesIn M (m + n) p sourceInput q targetInput := by
  induction hleft generalizing q targetInput n with
  | zero r midInput =>
      simpa using hright
  | read htransition hpush hempty ih =>
      rename_i m0 n0 p0 r0 s0 r1 a push mid0 empty0 mid1
      have htail := ih hright
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EmptySummaryComputesIn.read htransition hpush htail
  | epsilon htransition hpush hempty ih =>
      rename_i m0 n0 p0 r0 s0 r1 push mid0 empty0 mid1
      have htail := ih hright
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EmptySummaryComputesIn.epsilon htransition hpush htail

theorem emptySummaryComputes_trans
    {M : PDA input stack state}
    {p r q : state}
    {sourceInput midInput targetInput : Word input}
    (hleft : EmptySummaryComputes M p sourceInput r midInput)
    (hright : EmptySummaryComputes M r midInput q targetInput) :
    EmptySummaryComputes M p sourceInput q targetInput := by
  rcases hleft with ⟨m, hm⟩
  rcases hright with ⟨n, hn⟩
  exact ⟨m + n, emptySummaryComputesIn_trans hm hn⟩

theorem stackSummaryComputesIn_of_emptySummary_prefix_single
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {A : stack}
    {sourceInput midInput targetInput : Word input}
    (hempty : EmptySummaryComputesIn M m p sourceInput r midInput)
    (htop : StackSummaryComputesIn M n r [A] midInput q targetInput) :
    StackSummaryComputesIn M (m + n) p [A] sourceInput q targetInput := by
  induction hempty generalizing q targetInput n A with
  | zero r midInput =>
      simpa using htop
  | read htransition hpush hempty ih =>
      rename_i m0 n0 p0 r0 s0 r1 a push mid0 empty0 mid1
      have htail := ih htop
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StackSummaryComputesIn.emptyBeforeTopRead htransition hpush htail
  | epsilon htransition hpush hempty ih =>
      rename_i m0 n0 p0 r0 s0 r1 push mid0 empty0 mid1
      have htail := ih htop
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StackSummaryComputesIn.emptyBeforeTopEpsilon htransition hpush htail

theorem stackSummaryComputes_of_emptySummary_prefix_single
    {M : PDA input stack state}
    {p r q : state} {A : stack}
    {sourceInput midInput targetInput : Word input}
    (hempty : EmptySummaryComputes M p sourceInput r midInput)
    (htop : StackSummaryComputes M r [A] midInput q targetInput) :
    StackSummaryComputes M p [A] sourceInput q targetInput := by
  rcases hempty with ⟨m, hm⟩
  rcases htop with ⟨n, hn⟩
  exact ⟨m + n, stackSummaryComputesIn_of_emptySummary_prefix_single hm hn⟩

theorem stackSummaryComputesIn_cons_prefix
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {A : stack}
    {rest : Word stack}
    {sourceInput midInput targetInput : Word input}
    (htop : StackSummaryComputesIn M m p [A] sourceInput r midInput)
    (hrest : StackSummaryComputesIn M n r rest midInput q targetInput) :
    StackSummaryComputesIn M (m + n) p (A :: rest)
      sourceInput q targetInput :=
  StackSummaryComputesIn.cons htop hrest

theorem stackSummaryComputes_cons_prefix
    {M : PDA input stack state}
    {p r q : state} {A : stack} {rest : Word stack}
    {sourceInput midInput targetInput : Word input}
    (htop : StackSummaryComputes M p [A] sourceInput r midInput)
    (hrest : StackSummaryComputes M r rest midInput q targetInput) :
    StackSummaryComputes M p (A :: rest) sourceInput q targetInput := by
  rcases htop with ⟨m, hm⟩
  rcases hrest with ⟨n, hn⟩
  exact ⟨m + n, stackSummaryComputesIn_cons_prefix hm hn⟩

/-!
Splitting a stack summary is the main structural lemma for the induction: a run
that removes an appended stack word can be decomposed into the part that removes
the prefix and the part that removes the suffix. This mirrors how the generated
CFG chain is split into adjacent nonterminal summaries.
-/

/-!
Splitting a stack summary at a concatenation boundary is the key algebraic fact
for pushed stack words. The equality-indexed version performs the induction; the
plain append version below specializes it to an explicit prefix and suffix.
-/

theorem stackSummaryComputesIn_split_append_of_eq
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord left right : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p stackWord sourceInput q targetInput)
    (heq : stackWord = Word.Concat left right) :
    exists leftSteps : Nat, exists rightSteps : Nat,
      exists middleState : state, exists middleInput : Word input,
        n = leftSteps + rightSteps ∧
          StackSummaryComputesIn M leftSteps p left sourceInput
            middleState middleInput ∧
          StackSummaryComputesIn M rightSteps middleState right middleInput
            q targetInput := by
  induction h generalizing left right with
  | nil q unread =>
      have hleft : left = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hlen := congrArg List.length heq
        simp [Word.Concat] at hlen
        omega
      have hright : right = [] := by
        simpa [Word.Concat, hleft] using heq.symm
      refine ⟨0, 0, q, unread, ?_, ?_, ?_⟩
      · simp
      · simpa [hleft] using StackSummaryComputesIn.nil (M := M) q unread
      · simpa [hright] using StackSummaryComputesIn.nil (M := M) q unread
  | cons htop hrest ihtop ihrest =>
      rename_i topSteps restSteps p r q A rest sourceInput midInput targetInput
      cases left with
      | nil =>
          have hright : right = A :: rest := by
            simpa [Word.Concat] using heq.symm
          refine ⟨0, topSteps + restSteps, p, sourceInput,
            ?_, ?_, ?_⟩
          · simp
          · exact StackSummaryComputesIn.nil p sourceInput
          · simpa [hright] using StackSummaryComputesIn.cons htop hrest
      | cons B leftTail =>
          have heqCons : A :: rest = B :: Word.Concat leftTail right := heq
          have hA : A = B := (List.cons.inj heqCons).1
          have hrestEq : rest = Word.Concat leftTail right :=
            (List.cons.inj heqCons).2
          rcases ihrest hrestEq with
            ⟨leftSteps, rightSteps, middleState, middleInput,
              hlen, hleft, hright⟩
          refine ⟨topSteps + leftSteps, rightSteps,
            middleState, middleInput, ?_, ?_, hright⟩
          · simp [hlen, Nat.add_comm, Nat.add_left_comm]
          · simpa [hA] using StackSummaryComputesIn.cons htop hleft
  | popRead htransition hpush ih =>
      rename_i tailSteps p r q A a push midInput targetInput
      cases left with
      | nil =>
          have hright : right = [A] := by
            simpa [Word.Concat] using heq.symm
          refine ⟨0, tailSteps + 1, p, (a :: midInput), ?_, ?_, ?_⟩
          · simp
          · exact StackSummaryComputesIn.nil p (a :: midInput)
          · simpa [hright] using
              StackSummaryComputesIn.popRead htransition hpush
      | cons B leftTail =>
          have heqCons : A :: ([] : Word stack) =
              B :: Word.Concat leftTail right := heq
          have hA : A = B := (List.cons.inj heqCons).1
          have hsuffix : Word.Concat leftTail right = [] :=
            (List.cons.inj heqCons).2.symm
          have hleftTail : leftTail = [] := by
            cases leftTail with
            | nil => rfl
            | cons C tail =>
                have hbad := hsuffix
                simp [Word.Concat] at hbad
          have hright : right = [] := by
            simpa [Word.Concat, hleftTail] using hsuffix
          refine ⟨tailSteps + 1, 0, q, targetInput, ?_, ?_, ?_⟩
          · simp
          · simpa [hA, hleftTail] using
              StackSummaryComputesIn.popRead htransition hpush
          · simpa [hright] using
              StackSummaryComputesIn.nil (M := M) q targetInput
  | popEpsilon htransition hpush ih =>
      rename_i tailSteps p r q A push midInput targetInput
      cases left with
      | nil =>
          have hright : right = [A] := by
            simpa [Word.Concat] using heq.symm
          refine ⟨0, tailSteps + 1, p, midInput, ?_, ?_, ?_⟩
          · simp
          · exact StackSummaryComputesIn.nil p midInput
          · simpa [hright] using
              StackSummaryComputesIn.popEpsilon htransition hpush
      | cons B leftTail =>
          have heqCons : A :: ([] : Word stack) =
              B :: Word.Concat leftTail right := heq
          have hA : A = B := (List.cons.inj heqCons).1
          have hsuffix : Word.Concat leftTail right = [] :=
            (List.cons.inj heqCons).2.symm
          have hleftTail : leftTail = [] := by
            cases leftTail with
            | nil => rfl
            | cons C tail =>
                have hbad := hsuffix
                simp [Word.Concat] at hbad
          have hright : right = [] := by
            simpa [Word.Concat, hleftTail] using hsuffix
          refine ⟨tailSteps + 1, 0, q, targetInput, ?_, ?_, ?_⟩
          · simp
          · simpa [hA, hleftTail] using
              StackSummaryComputesIn.popEpsilon htransition hpush
          · simpa [hright] using
              StackSummaryComputesIn.nil (M := M) q targetInput
  | emptyBeforeTopRead htransition hpush htop ihpush ihtop =>
      rename_i pushSteps topSteps p r s q A a push midInput topInput targetInput
      cases left with
      | nil =>
          have hright : right = [A] := by
            simpa [Word.Concat] using heq.symm
          refine ⟨0, pushSteps + topSteps + 1, p, (a :: midInput),
            ?_, ?_, ?_⟩
          · simp
          · exact StackSummaryComputesIn.nil p (a :: midInput)
          · simpa [hright] using
              StackSummaryComputesIn.emptyBeforeTopRead
                htransition hpush htop
      | cons B leftTail =>
          have heqCons : A :: ([] : Word stack) =
              B :: Word.Concat leftTail right := heq
          have hA : A = B := (List.cons.inj heqCons).1
          have hsuffix : Word.Concat leftTail right = [] :=
            (List.cons.inj heqCons).2.symm
          have hleftTail : leftTail = [] := by
            cases leftTail with
            | nil => rfl
            | cons C tail =>
                have hbad := hsuffix
                simp [Word.Concat] at hbad
          have hright : right = [] := by
            simpa [Word.Concat, hleftTail] using hsuffix
          refine ⟨pushSteps + topSteps + 1, 0, q, targetInput,
            ?_, ?_, ?_⟩
          · simp
          · simpa [hA, hleftTail] using
              StackSummaryComputesIn.emptyBeforeTopRead
                htransition hpush htop
          · simpa [hright] using
              StackSummaryComputesIn.nil (M := M) q targetInput
  | emptyBeforeTopEpsilon htransition hpush htop ihpush ihtop =>
      rename_i pushSteps topSteps p r s q A push midInput topInput targetInput
      cases left with
      | nil =>
          have hright : right = [A] := by
            simpa [Word.Concat] using heq.symm
          refine ⟨0, pushSteps + topSteps + 1, p, midInput, ?_, ?_, ?_⟩
          · simp
          · exact StackSummaryComputesIn.nil p midInput
          · simpa [hright] using
              StackSummaryComputesIn.emptyBeforeTopEpsilon
                htransition hpush htop
      | cons B leftTail =>
          have heqCons : A :: ([] : Word stack) =
              B :: Word.Concat leftTail right := heq
          have hA : A = B := (List.cons.inj heqCons).1
          have hsuffix : Word.Concat leftTail right = [] :=
            (List.cons.inj heqCons).2.symm
          have hleftTail : leftTail = [] := by
            cases leftTail with
            | nil => rfl
            | cons C tail =>
                have hbad := hsuffix
                simp [Word.Concat] at hbad
          have hright : right = [] := by
            simpa [Word.Concat, hleftTail] using hsuffix
          refine ⟨pushSteps + topSteps + 1, 0, q, targetInput,
            ?_, ?_, ?_⟩
          · simp
          · simpa [hA, hleftTail] using
              StackSummaryComputesIn.emptyBeforeTopEpsilon
                htransition hpush htop
          · simpa [hright] using
              StackSummaryComputesIn.nil (M := M) q targetInput

/-!
The append-facing split theorem is the version used by callers. It removes the
explicit equality parameter from the induction lemma and exposes the midpoint
input where the prefix summary ends and the suffix summary begins.
-/

theorem stackSummaryComputesIn_split_append
    {M : PDA input stack state}
    {n : Nat} {p q : state} {left right : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputesIn M n p (Word.Concat left right)
      sourceInput q targetInput) :
    exists leftSteps : Nat, exists rightSteps : Nat,
      exists middleState : state, exists middleInput : Word input,
        n = leftSteps + rightSteps ∧
          StackSummaryComputesIn M leftSteps p left sourceInput
            middleState middleInput ∧
          StackSummaryComputesIn M rightSteps middleState right middleInput
            q targetInput :=
  stackSummaryComputesIn_split_append_of_eq h rfl

theorem stackSummaryComputes_split_append
    {M : PDA input stack state}
    {p q : state} {left right : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryComputes M p (Word.Concat left right)
      sourceInput q targetInput) :
    exists middleState : state, exists middleInput : Word input,
      StackSummaryComputes M p left sourceInput middleState middleInput ∧
        StackSummaryComputes M middleState right middleInput
          q targetInput := by
  rcases h with ⟨n, hn⟩
  rcases stackSummaryComputesIn_split_append hn with
    ⟨leftSteps, rightSteps, middleState, middleInput,
      _hlen, hleft, hright⟩
  exact ⟨middleState, middleInput, ⟨leftSteps, hleft⟩,
    ⟨rightSteps, hright⟩⟩

/-!
Stack-then-empty summaries can also be split at a stack prefix. The result keeps
the empty-stack continuation attached to the suffix part, so prefix processing
can be peeled off without losing the final empty-stack goal.
-/

theorem stackThenEmptySummaryComputesIn_split_stack_prefix
    {M : PDA input stack state}
    {n : Nat} {p q : state} {pref suff : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputesIn M n p
      (Word.Concat pref suff) sourceInput q targetInput) :
    exists prefixSteps : Nat, exists suffixSteps : Nat,
      exists middleState : state, exists middleInput : Word input,
        n = prefixSteps + suffixSteps ∧
          StackSummaryComputesIn M prefixSteps p pref sourceInput
            middleState middleInput ∧
          StackThenEmptySummaryComputesIn M suffixSteps middleState suff
            middleInput q targetInput := by
  rcases h with
    ⟨stackSteps, emptySteps, emptyState, emptyInput,
      hlen, hstack, hempty⟩
  rcases stackSummaryComputesIn_split_append hstack with
    ⟨prefixSteps, suffixStackSteps, middleState, middleInput,
      hstackLen, hprefix, hsuffix⟩
  refine ⟨prefixSteps, suffixStackSteps + emptySteps, middleState,
    middleInput, ?_, hprefix, ?_⟩
  · simp [hlen, hstackLen, Nat.add_comm, Nat.add_left_comm]
  · exact stackThenEmptySummaryComputesIn_of_stack_and_empty hsuffix hempty

theorem stackThenEmptySummaryComputes_split_stack_prefix
    {M : PDA input stack state}
    {p q : state} {pref suff : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputes M p
      (Word.Concat pref suff) sourceInput q targetInput) :
    exists middleState : state, exists middleInput : Word input,
      StackSummaryComputes M p pref sourceInput middleState middleInput ∧
        StackThenEmptySummaryComputes M middleState suff
          middleInput q targetInput := by
  rcases h with ⟨n, hn⟩
  rcases stackThenEmptySummaryComputesIn_split_stack_prefix hn with
    ⟨prefixSteps, suffixSteps, middleState, middleInput,
      _hlen, hprefix, hsuffix⟩
  exact ⟨middleState, middleInput, ⟨prefixSteps, hprefix⟩,
    ⟨suffixSteps, hsuffix⟩⟩

/-!
After a split, a stack-then-empty summary can be extended by one leading stack
symbol. This is the composition step used when a PDA transition pushes several
symbols and the CFG chain has to account for them one at a time.
-/

theorem stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {A : stack} {rest : Word stack}
    {sourceInput midInput targetInput : Word input}
    (htop : StackSummaryComputesIn M m p [A] sourceInput r midInput)
    (htail : StackThenEmptySummaryComputesIn M n r rest midInput
      q targetInput) :
    StackThenEmptySummaryComputesIn M (m + n) p (A :: rest)
      sourceInput q targetInput := by
  rcases htail with
    ⟨restSteps, emptySteps, emptyState, emptyInput,
      hlen, hrest, hempty⟩
  refine ⟨m + restSteps, emptySteps, emptyState, emptyInput,
    ?_, ?_, hempty⟩
  · simp [hlen, Nat.add_comm, Nat.add_left_comm]
  · exact StackSummaryComputesIn.cons htop hrest

theorem stackThenEmptySummaryComputes_cons_of_stack_and_stackThenEmpty
    {M : PDA input stack state}
    {p r q : state} {A : stack} {rest : Word stack}
    {sourceInput midInput targetInput : Word input}
    (htop : StackSummaryComputes M p [A] sourceInput r midInput)
    (htail : StackThenEmptySummaryComputes M r rest midInput
      q targetInput) :
    StackThenEmptySummaryComputes M p (A :: rest)
      sourceInput q targetInput := by
  rcases htop with ⟨m, hm⟩
  rcases htail with ⟨n, hn⟩
  exact ⟨m + n,
    stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
      hm hn⟩

/-!
Here the proof consumes the first concrete PDA step and reconstructs the matching
summary predicate. The top-pop normal form keeps the case analysis manageable:
the first step either pops one top symbol or preserves the top symbol while a
pushed prefix is handled first.
-/

/-!
The next reconstruction lemmas turn a real top-pop PDA step into a
stack-then-empty summary. They inspect whether the step consumed input, then
attach the summary for the pushed stack word to the summary for the remaining
empty-stack computation.
-/

theorem stackThenEmptySummaryComputesIn_of_step_of_stackThenEmpty_topPop
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    {mid : Configuration input stack state}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := sourceInput, stack := stackWord } mid)
    (hrest : StackThenEmptySummaryComputesIn M n mid.state mid.stack
      mid.unread q targetInput) :
    StackThenEmptySummaryComputesIn M (n + 1) p stackWord
      sourceInput q targetInput := by
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
    have hstack : stackWord = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hrest' :
        StackThenEmptySummaryComputesIn M n r
          (Word.Concat push restStack) unread q targetInput := by
      simpa [hd] using hrest
    rcases hnorm p' (some a) pop r push htransition with
      hpopNil | hpopSingle
    · have htransition' : M.transition p (some a) [] r push := by
        simpa [hp, hpopNil] using htransition
      have hstackRest : stackWord = restStack := by
        simpa [Word.Concat, hpopNil] using hstack
      cases restStack with
      | nil =>
          have hrestPush :
              StackThenEmptySummaryComputesIn M n r push unread
                q targetInput := by
            simpa [Word.Concat] using hrest'
          rcases hrestPush with
            ⟨pushSteps, emptySteps, emptyState, emptyInput,
              hrestLen, hpush, hemptyTail⟩
          have hempty :
              EmptySummaryComputesIn M (n + 1) p (a :: unread)
                q targetInput := by
            simpa [hrestLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using EmptySummaryComputesIn.read htransition' hpush hemptyTail
          have hsummary :=
            stackThenEmptySummaryComputesIn_of_empty hempty
          simpa [hsource, hstackRest] using hsummary
      | cons A tail =>
          rcases stackThenEmptySummaryComputesIn_split_stack_prefix
              (M := M) (pref := push) (suff := A :: tail)
              hrest' with
            ⟨pushSteps, suffixSteps, afterPush, afterPushInput,
              hrestLen, hpush, hsuffix⟩
          have hsuffix' :
              StackThenEmptySummaryComputesIn M suffixSteps afterPush
                (Word.Concat [A] tail) afterPushInput q targetInput := by
            simpa [Word.Concat] using hsuffix
          rcases stackThenEmptySummaryComputesIn_split_stack_prefix
              (M := M) (pref := [A]) (suff := tail)
              hsuffix' with
            ⟨topSteps, tailSteps, afterTop, afterTopInput,
              hsuffixLen, htop, htail⟩
          have htop' :
              StackSummaryComputesIn M (pushSteps + topSteps + 1)
                p [A] (a :: unread) afterTop afterTopInput :=
            StackSummaryComputesIn.emptyBeforeTopRead
              htransition' hpush htop
          have hsummary :=
            stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
              htop' htail
          simpa [hsource, hstackRest, hrestLen, hsuffixLen,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsummary
    · rcases hpopSingle with ⟨A, hpopSingle⟩
      have htransition' : M.transition p (some a) [A] r push := by
        simpa [hp, hpopSingle] using htransition
      have hstackRest : stackWord = A :: restStack := by
        simpa [Word.Concat, hpopSingle] using hstack
      rcases stackThenEmptySummaryComputesIn_split_stack_prefix
          (M := M) (pref := push) (suff := restStack)
          hrest' with
        ⟨pushSteps, restSteps, afterPush, afterPushInput,
          hrestLen, hpush, htail⟩
      have htop :
          StackSummaryComputesIn M (pushSteps + 1) p [A]
            (a :: unread) afterPush afterPushInput :=
        StackSummaryComputesIn.popRead htransition' hpush
      have hsummary :=
        stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
          htop htail
      simpa [hsource, hstackRest, hrestLen,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsummary
  · rcases heps with
      ⟨p', r, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : stackWord = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hrest' :
        StackThenEmptySummaryComputesIn M n r
          (Word.Concat push restStack) unread q targetInput := by
      simpa [hd] using hrest
    rcases hnorm p' none pop r push htransition with
      hpopNil | hpopSingle
    · have htransition' : M.transition p none [] r push := by
        simpa [hp, hpopNil] using htransition
      have hstackRest : stackWord = restStack := by
        simpa [Word.Concat, hpopNil] using hstack
      cases restStack with
      | nil =>
          have hrestPush :
              StackThenEmptySummaryComputesIn M n r push unread
                q targetInput := by
            simpa [Word.Concat] using hrest'
          rcases hrestPush with
            ⟨pushSteps, emptySteps, emptyState, emptyInput,
              hrestLen, hpush, hemptyTail⟩
          have hempty :
              EmptySummaryComputesIn M (n + 1) p unread
                q targetInput := by
            simpa [hrestLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using EmptySummaryComputesIn.epsilon htransition' hpush hemptyTail
          have hsummary :=
            stackThenEmptySummaryComputesIn_of_empty hempty
          simpa [hsource, hstackRest] using hsummary
      | cons A tail =>
          rcases stackThenEmptySummaryComputesIn_split_stack_prefix
              (M := M) (pref := push) (suff := A :: tail)
              hrest' with
            ⟨pushSteps, suffixSteps, afterPush, afterPushInput,
              hrestLen, hpush, hsuffix⟩
          have hsuffix' :
              StackThenEmptySummaryComputesIn M suffixSteps afterPush
                (Word.Concat [A] tail) afterPushInput q targetInput := by
            simpa [Word.Concat] using hsuffix
          rcases stackThenEmptySummaryComputesIn_split_stack_prefix
              (M := M) (pref := [A]) (suff := tail)
              hsuffix' with
            ⟨topSteps, tailSteps, afterTop, afterTopInput,
              hsuffixLen, htop, htail⟩
          have htop' :
              StackSummaryComputesIn M (pushSteps + topSteps + 1)
                p [A] unread afterTop afterTopInput :=
            StackSummaryComputesIn.emptyBeforeTopEpsilon
              htransition' hpush htop
          have hsummary :=
            stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
              htop' htail
          simpa [hsource, hstackRest, hrestLen, hsuffixLen,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsummary
    · rcases hpopSingle with ⟨A, hpopSingle⟩
      have htransition' : M.transition p none [A] r push := by
        simpa [hp, hpopSingle] using htransition
      have hstackRest : stackWord = A :: restStack := by
        simpa [Word.Concat, hpopSingle] using hstack
      rcases stackThenEmptySummaryComputesIn_split_stack_prefix
          (M := M) (pref := push) (suff := restStack)
          hrest' with
        ⟨pushSteps, restSteps, afterPush, afterPushInput,
          hrestLen, hpush, htail⟩
      have htop :
          StackSummaryComputesIn M (pushSteps + 1) p [A]
            unread afterPush afterPushInput :=
        StackSummaryComputesIn.popEpsilon htransition' hpush
      have hsummary :=
        stackThenEmptySummaryComputesIn_cons_of_stack_and_stackThenEmpty
          htop htail
      simpa [hsource, hstackRest, hrestLen,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsummary

/-!
This theorem is the general first-step reconstruction for top-pop computations.
It finds the first PDA step, turns that step into a stack-then-empty summary, and
uses the remaining computation as the continuation.
-/

theorem stackThenEmptySummaryComputesIn_of_computesIn_topPop
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hcomp : ComputesIn M n
      { state := p, unread := sourceInput, stack := stackWord }
      { state := q, unread := targetInput, stack := [] }) :
    StackThenEmptySummaryComputesIn M n p stackWord sourceInput
      q targetInput := by
  induction n generalizing p q stackWord sourceInput targetInput with
  | zero =>
      have hend := computesIn_zero_eq hcomp
      have hstate : p = q := by
        simpa using congrArg
          (fun c : Configuration input stack state => c.state) hend
      have hinput : sourceInput = targetInput := by
        simpa using congrArg
          (fun c : Configuration input stack state => c.unread) hend
      have hstack : stackWord = [] := by
        simpa using congrArg
          (fun c : Configuration input stack state => c.stack) hend
      have hempty :
          EmptySummaryComputesIn M 0 p sourceInput p sourceInput :=
        EmptySummaryComputesIn.zero p sourceInput
      have hsummary :=
        stackThenEmptySummaryComputesIn_of_empty hempty
      simpa [hstate, hinput, hstack] using hsummary
  | succ n ih =>
      rcases computesIn_succ_inv (M := M) (n := n) hcomp with
        ⟨mid, hstep, hrest⟩
      have htail :
          StackThenEmptySummaryComputesIn M n mid.state mid.stack
            mid.unread q targetInput :=
        ih (p := mid.state) (q := q) (stackWord := mid.stack)
          (sourceInput := mid.unread) (targetInput := targetInput) hrest
      exact stackThenEmptySummaryComputesIn_of_step_of_stackThenEmpty_topPop
        hnorm hstep htail

theorem stackThenEmptySummaryComputesIn_trans_empty
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {stackWord : Word stack}
    {sourceInput midInput targetInput : Word input}
    (hleft : StackThenEmptySummaryComputesIn M m p stackWord
      sourceInput r midInput)
    (hright : EmptySummaryComputesIn M n r midInput q targetInput) :
    StackThenEmptySummaryComputesIn M (m + n) p stackWord
      sourceInput q targetInput := by
  rcases hleft with
    ⟨stackSteps, emptySteps, middleState, middleInput,
      hlen, hstack, hempty⟩
  have hempty' := emptySummaryComputesIn_trans hempty hright
  refine ⟨stackSteps, emptySteps + n, middleState, middleInput,
    ?_, hstack, hempty'⟩
  simp [hlen, Nat.add_comm, Nat.add_left_comm]

theorem stackThenEmptySummaryComputes_trans_empty
    {M : PDA input stack state}
    {p r q : state} {stackWord : Word stack}
    {sourceInput midInput targetInput : Word input}
    (hleft : StackThenEmptySummaryComputes M p stackWord
      sourceInput r midInput)
    (hright : EmptySummaryComputes M r midInput q targetInput) :
    StackThenEmptySummaryComputes M p stackWord
      sourceInput q targetInput := by
  rcases hleft with ⟨m, hm⟩
  rcases hright with ⟨n, hn⟩
  exact ⟨m + n, stackThenEmptySummaryComputesIn_trans_empty hm hn⟩

theorem emptySummaryComputesIn_of_stackThenEmptySummaryComputesIn_nil
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputesIn M n p ([] : Word stack)
      sourceInput q targetInput) :
    EmptySummaryComputesIn M n p sourceInput q targetInput := by
  rcases h with
    ⟨stackSteps, emptySteps, middleState, middleInput,
      hlen, hstack, hempty⟩
  cases hstack with
  | nil p0 unread0 =>
      simpa [hlen] using hempty

theorem emptySummaryComputes_of_stackThenEmptySummaryComputes_nil
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryComputes M p ([] : Word stack)
      sourceInput q targetInput) :
    EmptySummaryComputes M p sourceInput q targetInput := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, emptySummaryComputesIn_of_stackThenEmptySummaryComputesIn_nil hn⟩


end PDA

end Grammars
end FoC
