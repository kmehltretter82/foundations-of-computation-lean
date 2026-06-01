import FoC.Book.Chapter03.Section03
import FoC.Languages.DFA

namespace FoC
namespace Book
namespace Chapter03
namespace Section04

/-!
Book: Chapter 3, Section 3.4, Finite-State Automata.
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

-- Book: Chapter 3, Section 3.4, Definition 3.5.
theorem dfa_run_empty (M : DFA alpha state) (q : state) :
    DFA.RunFrom M q Word.Empty = q :=
  DFA.runFrom_empty M q

-- Book: Chapter 3, Section 3.4, recursive extended transition function.
theorem dfa_run_cons (M : DFA alpha state) (q : state) (a : alpha) (w : Word alpha) :
    DFA.RunFrom M q (a :: w) = DFA.RunFrom M (M.step q a) w :=
  DFA.runFrom_cons M q a w

-- Book: Chapter 3, Section 3.4, Definition 3.6.
theorem dfa_acceptance_definition (M : DFA alpha state) (w : Word alpha) :
    DFA.Accepts M w <-> M.accept (DFA.Run M w) :=
  Iff.rfl

-- Book: Chapter 3, Section 3.4, language accepted by a DFA.
theorem dfa_language_membership (M : DFA alpha state) (w : Word alpha) :
    w ∈ DFA.Language M <-> DFA.Accepts M w :=
  Iff.rfl

-- Book: Chapter 3, Section 3.4, Example 3.10 sample run.
theorem atLeastTwoOnes_run_0011 :
    DFA.Run atLeastTwoOnesDFA
      [Section01.Bit.zero, Section01.Bit.zero, Section01.Bit.one, Section01.Bit.one] =
        TwoOnesState.twoOrMore :=
  rfl

-- Book: Chapter 3, Section 3.4, Example 3.10 sample acceptance.
theorem atLeastTwoOnes_accepts_0011 :
    DFA.Accepts atLeastTwoOnesDFA
      [Section01.Bit.zero, Section01.Bit.zero, Section01.Bit.one, Section01.Bit.one] := by
  unfold DFA.Accepts DFA.Run atLeastTwoOnesDFA DFA.RunFrom
  trivial

-- Book: Chapter 3, Section 3.4, sample rejection.
theorem atLeastTwoOnes_rejects_010 :
    ¬ DFA.Accepts atLeastTwoOnesDFA
      [Section01.Bit.zero, Section01.Bit.one, Section01.Bit.zero] := by
  intro h
  unfold DFA.Accepts DFA.Run atLeastTwoOnesDFA DFA.RunFrom at h
  cases h

-- Book: Chapter 3, Section 3.4, complement machine switches final and non-final states.
theorem dfa_complement_acceptance (M : DFA alpha state) (w : Word alpha) :
    DFA.Accepts (DFA.Complement M) w <-> ¬ DFA.Accepts M w :=
  DFA.complement_accepts M w

-- Book: Chapter 3, Section 3.4, product construction for intersection.
theorem dfa_intersection_acceptance
    (M : DFA alpha state₁) (N : DFA alpha state₂) (w : Word alpha) :
    DFA.Accepts (DFA.Intersection M N) w <-> DFA.Accepts M w ∧ DFA.Accepts N w :=
  DFA.intersection_accepts M N w

-- Book: Chapter 3, Section 3.4, product construction for union.
theorem dfa_union_acceptance
    (M : DFA alpha state₁) (N : DFA alpha state₂) (w : Word alpha) :
    DFA.Accepts (DFA.Union M N) w <-> DFA.Accepts M w ∨ DFA.Accepts N w :=
  DFA.union_accepts M N w

end Section04
end Chapter03
end Book
end FoC
