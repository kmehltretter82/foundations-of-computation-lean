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

namespace FiniteType

def PairElems : List alpha -> List beta -> List (alpha × beta)
  | [], _ => []
  | x :: xs, ys => (ys.map fun y => (x, y)) ++ PairElems xs ys

theorem pair_mem {xs : List alpha} {ys : List beta}
    {x : alpha} {y : beta} (hx : x ∈ xs) (hy : y ∈ ys) :
    (x, y) ∈ PairElems xs ys := by
  induction xs with
  | nil =>
      cases hx
  | cons z zs ih =>
      cases hx with
      | head =>
          simp [PairElems, hy]
      | tail _ htail =>
          exact List.mem_append.mpr (Or.inr (ih htail))

def product (left : FiniteType alpha) (right : FiniteType beta) :
    FiniteType (alpha × beta) where
  elems := PairElems left.elems right.elems
  complete := by
    intro p
    exact pair_mem (left.complete p.1) (right.complete p.2)

end FiniteType

structure PDA (input : Type u) (stack : Type v) (state : Type w) where
  start : state
  transition : state -> Option input -> Word stack -> state -> Word stack -> Prop
  accept : state -> Prop
  statesFinite : FiniteType state

namespace PDA

structure TransitionRule (input : Type u) (stack : Type v) (state : Type w) where
  source : state
  input? : Option input
  pop : Word stack
  target : state
  push : Word stack

def TransitionRule.Applies
    (rule : TransitionRule input stack state)
    (q : state) (a? : Option input) (pop : Word stack)
    (r : state) (push : Word stack) : Prop :=
  rule.source = q ∧ rule.input? = a? ∧ rule.pop = pop ∧
    rule.target = r ∧ rule.push = push

structure FinitePresentation
    (M : PDA input stack state) where
  stackFinite : FiniteType stack
  transitionRules : List (TransitionRule input stack state)
  transition_complete :
    forall q a? pop r push,
      M.transition q a? pop r push <->
        exists rule, rule ∈ transitionRules ∧
          rule.Applies q a? pop r push
  acceptingStates : List state
  accept_complete :
    forall q, M.accept q <-> q ∈ acceptingStates

def HasFinitePresentation (M : PDA input stack state) : Prop :=
  Nonempty (FinitePresentation M)

def HasFiniteTransitions (M : PDA input stack state) : Prop :=
  exists rules : List (TransitionRule input stack state),
    forall q a? pop r push,
      M.transition q a? pop r push <->
        exists rule, rule ∈ rules ∧ rule.Applies q a? pop r push

def HasFiniteStackAlphabet (_M : PDA input stack state) : Prop :=
  Nonempty (FiniteType stack)

def PopsAtMostOne (M : PDA input stack state) : Prop :=
  forall q a? pop r push,
    M.transition q a? pop r push ->
      pop = [] ∨ exists A : stack, pop = [A]

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

def FinitePresentationRecognizable (L : Language input) : Prop :=
  exists stack : Type, exists state : Type, exists M : PDA input stack state,
    exists _presentation : FinitePresentation M,
      Language.Equal (AcceptedLanguage M) L

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
