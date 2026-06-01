import FoC.Foundation.Finite
import FoC.Languages.Language

namespace FoC
namespace Grammars

/-!
Pushdown automata.

The stack top is represented by the head of the stack list.  A transition
label `(input, pop, push)` consumes either one input symbol or epsilon, removes
`pop` from the top of the stack, and replaces it with `push`.

Used by:
- Chapter 4, Section 4.4: pushdown automata, configurations, computations,
  and acceptance by final state with empty stack.
-/

open Foundation
open Languages

structure PDA (input : Type u) (stack : Type v) (state : Type w) where
  start : state
  transition : state -> Option input -> Word stack -> state -> Word stack -> Prop
  accept : state -> Prop
  statesFinite : FiniteType state

namespace PDA

structure Configuration (input : Type u) (stack : Type v) (state : Type w) where
  state : state
  unread : Word input
  stack : Word stack

def initial (M : PDA input stack state) (w : Word input) :
    Configuration input stack state where
  state := M.start
  unread := w
  stack := []

inductive Step (M : PDA input stack state) :
    Configuration input stack state -> Configuration input stack state -> Prop where
  | read {q r : state} {a : input} {unread : Word input}
      {pop push restStack : Word stack} :
      M.transition q (some a) pop r push ->
      Step M
        { state := q, unread := a :: unread, stack := Word.Concat pop restStack }
        { state := r, unread := unread, stack := Word.Concat push restStack }
  | epsilon {q r : state} {unread : Word input}
      {pop push restStack : Word stack} :
      M.transition q none pop r push ->
      Step M
        { state := q, unread := unread, stack := Word.Concat pop restStack }
        { state := r, unread := unread, stack := Word.Concat push restStack }

inductive Computes (M : PDA input stack state) :
    Configuration input stack state -> Configuration input stack state -> Prop where
  | refl (c : Configuration input stack state) : Computes M c c
  | step {c d e : Configuration input stack state} :
      Step M c d -> Computes M d e -> Computes M c e

def Accepts (M : PDA input stack state) (w : Word input) : Prop :=
  exists q : state,
    M.accept q ∧
      Computes M (initial M w) { state := q, unread := [], stack := [] }

def AcceptsByFinalState (M : PDA input stack state) (w : Word input) : Prop :=
  exists q : state, exists remainingStack : Word stack,
    M.accept q ∧
      Computes M (initial M w) { state := q, unread := [], stack := remainingStack }

def AcceptsByEmptyStack (M : PDA input stack state) (w : Word input) : Prop :=
  exists q : state,
    Computes M (initial M w) { state := q, unread := [], stack := [] }

def AcceptedLanguage (M : PDA input stack state) : Language input :=
  fun w => Accepts M w

def Recognizable (L : Language input) : Prop :=
  exists stack : Type, exists state : Type, exists M : PDA input stack state,
    Language.Equal (AcceptedLanguage M) L

def Deterministic (M : PDA input stack state) : Prop :=
  forall c d e, Step M c d -> Step M c e -> d = e

theorem computes_trans {M : PDA input stack state}
    {a b c : Configuration input stack state}
    (hab : Computes M a b) (hbc : Computes M b c) : Computes M a c := by
  induction hab with
  | refl _ => exact hbc
  | step hstep _ ih => exact Computes.step hstep (ih hbc)

theorem computes_of_step {M : PDA input stack state}
    {a b : Configuration input stack state} (h : Step M a b) :
    Computes M a b :=
  Computes.step h (Computes.refl b)

theorem accepts_implies_final_state_accepts {M : PDA input stack state}
    {w : Word input} (h : Accepts M w) : AcceptsByFinalState M w := by
  cases h with
  | intro q hq =>
      exact Exists.intro q (Exists.intro ([] : Word stack) hq)

theorem accepts_implies_empty_stack_accepts {M : PDA input stack state}
    {w : Word input} (h : Accepts M w) : AcceptsByEmptyStack M w := by
  cases h with
  | intro q hq =>
      exists q
      exact hq.right

end PDA

end Grammars
end FoC
