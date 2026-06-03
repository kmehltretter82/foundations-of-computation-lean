import FoC.Book.Chapter03.Section03
import FoC.Languages.DFA

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter03
namespace Section04

/-!
# Chapter 3, Section 3.4: Finite-State Automata

This section introduces deterministic finite automata. A DFA has a finite
state type, a start state, a transition function, and an accepting predicate;
running the machine folds the transition function over the input word. The
core reusable API is {module}`FoC.Languages.DFA`.

The example machine records only the information needed for its language:
whether no `1` has been seen, exactly one `1` has been seen, or two or more
have been seen. This is the finite-memory intuition behind deterministic
finite automata.
-/

open Foundation
open Languages

inductive TwoOnesState where
  | noneSeen
  | oneSeen
  | twoOrMore
deriving DecidableEq

def TwoOnesStateFinite : FiniteType TwoOnesState where
  elems := [TwoOnesState.noneSeen, TwoOnesState.oneSeen, TwoOnesState.twoOrMore]
  complete := by
    intro q
    cases q <;> simp

def atLeastTwoOnesDFA : DFA Section01.Bit TwoOnesState where
  start := TwoOnesState.noneSeen
  step := fun q input =>
    match q, input with
    | TwoOnesState.noneSeen, Section01.Bit.zero => TwoOnesState.noneSeen
    | TwoOnesState.noneSeen, Section01.Bit.one => TwoOnesState.oneSeen
    | TwoOnesState.oneSeen, Section01.Bit.zero => TwoOnesState.oneSeen
    | TwoOnesState.oneSeen, Section01.Bit.one => TwoOnesState.twoOrMore
    | TwoOnesState.twoOrMore, _ => TwoOnesState.twoOrMore
  accept := fun q =>
    match q with
    | TwoOnesState.twoOrMore => True
    | _ => False
  statesFinite := TwoOnesStateFinite

/-!
## Runs and Acceptance

The first definitions describe the extended transition function and acceptance
predicate. The concrete DFA above recognizes binary words with at least two
ones, matching the section's finite-state-machine examples.

`DFA.RunFrom` starts in an arbitrary state, while `DFA.Run` starts in the
machine's designated start state. Acceptance checks the final state after the
whole input word has been consumed.
-/

theorem dfa_run_empty (M : DFA alpha state) (q : state) :
    DFA.RunFrom M q Word.Empty = q :=
  DFA.runFrom_empty M q

theorem dfa_run_cons (M : DFA alpha state) (q : state) (a : alpha) (w : Word alpha) :
    DFA.RunFrom M q (a :: w) = DFA.RunFrom M (M.step q a) w :=
  DFA.runFrom_cons M q a w

theorem dfa_acceptance_definition (M : DFA alpha state) (w : Word alpha) :
    DFA.Accepts M w <-> M.accept (DFA.Run M w) :=
  Iff.rfl

theorem dfa_language_membership (M : DFA alpha state) (w : Word alpha) :
    w ∈ DFA.Language M <-> DFA.Accepts M w :=
  Iff.rfl

theorem atLeastTwoOnes_run_0011 :
    DFA.Run atLeastTwoOnesDFA
      [Section01.Bit.zero, Section01.Bit.zero, Section01.Bit.one, Section01.Bit.one] =
        TwoOnesState.twoOrMore :=
  rfl

theorem atLeastTwoOnes_accepts_0011 :
    DFA.Accepts atLeastTwoOnesDFA
      [Section01.Bit.zero, Section01.Bit.zero, Section01.Bit.one, Section01.Bit.one] := by
  unfold DFA.Accepts DFA.Run atLeastTwoOnesDFA DFA.RunFrom
  trivial

theorem atLeastTwoOnes_rejects_010 :
    ¬ DFA.Accepts atLeastTwoOnesDFA
      [Section01.Bit.zero, Section01.Bit.one, Section01.Bit.zero] := by
  intro h
  unfold DFA.Accepts DFA.Run atLeastTwoOnesDFA DFA.RunFrom at h
  cases h

/-!
## DFA Constructions

Complement and product constructions give the standard closure operations for
finite-state languages. They are stated as exact acceptance equivalences for
each input word.

The complement construction flips the accepting states. The product
constructions run two machines in parallel so a word can be accepted by both
machines for intersection or by at least one for union.
-/

theorem dfa_complement_acceptance (M : DFA alpha state) (w : Word alpha) :
    DFA.Accepts (DFA.Complement M) w <-> ¬ DFA.Accepts M w :=
  DFA.complement_accepts M w

theorem dfa_intersection_acceptance
    (M : DFA alpha state₁) (N : DFA alpha state₂) (w : Word alpha) :
    DFA.Accepts (DFA.Intersection M N) w <-> DFA.Accepts M w ∧ DFA.Accepts N w :=
  DFA.intersection_accepts M N w

theorem dfa_union_acceptance
    (M : DFA alpha state₁) (N : DFA alpha state₂) (w : Word alpha) :
    DFA.Accepts (DFA.Union M N) w <-> DFA.Accepts M w ∨ DFA.Accepts N w :=
  DFA.union_accepts M N w

end Section04
end Chapter03
end Book
end FoC
