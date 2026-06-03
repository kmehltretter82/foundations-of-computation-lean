import FoC.Foundation.Finite
import FoC.Languages.Language

set_option doc.verso true

/-!
# Pushdown automata

The stack top is represented by the head of the stack list.  A transition
label {lit}`(input, pop, push)` consumes either one input symbol or epsilon,
removes {lit}`pop` from the top of the stack, and replaces it with {lit}`push`.

## Book coordinates

Used by:
- Chapter 4, Section 4.4: pushdown automata, configurations, computations,
  and acceptance by final state with empty stack.
-/

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace FiniteType

/-!
# Finite product states

PDA constructions often add control information by taking products of finite
state types. This helper supplies the required finite witness.
-/

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

/-!
# PDA structure

A PDA is given by a start state, a transition relation over optional input and
stack words, an accepting-state predicate, and a finite-state witness.
-/

structure PDA (input : Type u) (stack : Type v) (state : Type w) where
  start : state
  transition : state -> Option input -> Word stack -> state -> Word stack -> Prop
  accept : state -> Prop
  statesFinite : FiniteType state

namespace PDA

/-!
# Finite presentations

The finite-presentation layer turns an arbitrary transition relation into the
book's finite list of transition rules and accepting states.
-/

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

/-!
# Configurations and steps

Configurations record the current state, unread input, and stack. A step either
reads one symbol or takes an epsilon transition while replacing the matched
stack prefix.
-/

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

inductive ComputesIn (M : PDA input stack state) :
    Nat -> Configuration input stack state ->
      Configuration input stack state -> Prop where
  | zero (c : Configuration input stack state) :
      ComputesIn M 0 c c
  | succ {n : Nat} {c d e : Configuration input stack state} :
      Step M c d -> ComputesIn M n d e -> ComputesIn M (n + 1) c e

/-!
# Acceptance modes

The default accepted language uses final state and empty stack. The companion
predicates keep the final-state-only and empty-stack-only variants available for
conversion theorems.
-/

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

/-!
# Computation algebra

The reflexive-transitive computation relation and its length-indexed variant
are interconvertible and compose in the expected way.
-/

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

theorem computesIn_computes {M : PDA input stack state}
    {n : Nat} {a b : Configuration input stack state}
    (h : ComputesIn M n a b) : Computes M a b := by
  induction h with
  | zero c =>
      exact Computes.refl c
  | succ hstep _ ih =>
      exact Computes.step hstep ih

theorem computes_exists_length {M : PDA input stack state}
    {a b : Configuration input stack state}
    (h : Computes M a b) :
    exists n : Nat, ComputesIn M n a b := by
  induction h with
  | refl c =>
      exact ⟨0, ComputesIn.zero c⟩
  | step hstep _ ih =>
      rcases ih with ⟨n, hn⟩
      exact ⟨n + 1, ComputesIn.succ hstep hn⟩

theorem computes_iff_exists_computesIn {M : PDA input stack state}
    {a b : Configuration input stack state} :
    Computes M a b <-> exists n : Nat, ComputesIn M n a b := by
  constructor
  · exact computes_exists_length
  · intro h
    rcases h with ⟨n, hn⟩
    exact computesIn_computes hn

theorem computesIn_of_step {M : PDA input stack state}
    {a b : Configuration input stack state} (h : Step M a b) :
    ComputesIn M 1 a b := by
  simpa using ComputesIn.succ (n := 0) h (ComputesIn.zero b)

theorem computesIn_trans {M : PDA input stack state}
    {m n : Nat} {a b c : Configuration input stack state}
    (hab : ComputesIn M m a b) (hbc : ComputesIn M n b c) :
    ComputesIn M (m + n) a c := by
  induction hab generalizing n c with
  | zero _ =>
      simpa using hbc
  | succ hstep _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ComputesIn.succ hstep (ih hbc)

theorem computesIn_zero_eq {M : PDA input stack state}
    {a b : Configuration input stack state}
    (h : ComputesIn M 0 a b) : a = b := by
  cases h
  rfl

theorem computesIn_succ_inv {M : PDA input stack state}
    {n : Nat} {a c : Configuration input stack state}
    (h : ComputesIn M (n + 1) a c) :
    exists b : Configuration input stack state,
      Step M a b ∧ ComputesIn M n b c := by
  cases h with
  | succ hstep hrest =>
      exact ⟨_, hstep, hrest⟩

theorem computesIn_one_inv {M : PDA input stack state}
    {a c : Configuration input stack state}
    (h : ComputesIn M 1 a c) :
    Step M a c := by
  rcases computesIn_succ_inv (n := 0) h with ⟨b, hstep, hrest⟩
  have hb : b = c := computesIn_zero_eq hrest
  rwa [hb] at hstep

theorem step_cases {M : PDA input stack state}
    {c d : Configuration input stack state}
    (h : Step M c d) :
    (exists q : state, exists r : state, exists a : input,
      exists unread : Word input, exists pop : Word stack,
      exists push : Word stack, exists restStack : Word stack,
        M.transition q (some a) pop r push ∧
          c = { state := q, unread := a :: unread,
                stack := Word.Concat pop restStack } ∧
          d = { state := r, unread := unread,
                stack := Word.Concat push restStack }) ∨
    (exists q : state, exists r : state, exists unread : Word input,
      exists pop : Word stack, exists push : Word stack,
      exists restStack : Word stack,
        M.transition q none pop r push ∧
          c = { state := q, unread := unread,
                stack := Word.Concat pop restStack } ∧
          d = { state := r, unread := unread,
                stack := Word.Concat push restStack }) := by
  cases h with
  | read htransition =>
      left
      repeat first | apply Exists.intro _
      exact ⟨htransition, rfl, rfl⟩
  | epsilon htransition =>
      right
      repeat first | apply Exists.intro _
      exact ⟨htransition, rfl, rfl⟩

theorem step_consumes_empty_or_symbol {M : PDA input stack state}
    {c d : Configuration input stack state}
    (h : Step M c d) :
    (c.unread = d.unread) ∨
      exists a : input, c.unread = a :: d.unread := by
  rcases step_cases h with hread | heps
  · rcases hread with
      ⟨q, r, a, unread, pop, push, restStack,
        _htransition, hc, hd⟩
    right
    refine ⟨a, ?_⟩
    have hsource : c.unread = a :: unread := by
      simpa using congrArg
        (fun config : Configuration input stack state => config.unread) hc
    have htarget : d.unread = unread := by
      simpa using congrArg
        (fun config : Configuration input stack state => config.unread) hd
    simpa [htarget] using hsource
  · rcases heps with
      ⟨q, r, unread, pop, push, restStack,
        _htransition, hc, hd⟩
    left
    have hsource : c.unread = unread := by
      simpa using congrArg
        (fun config : Configuration input stack state => config.unread) hc
    have htarget : d.unread = unread := by
      simpa using congrArg
        (fun config : Configuration input stack state => config.unread) hd
    exact hsource.trans htarget.symm

theorem step_consumes_prefix {M : PDA input stack state}
    {c d : Configuration input stack state}
    (h : Step M c d) :
    exists consumed : Word input,
      c.unread = Word.Concat consumed d.unread := by
  rcases step_consumes_empty_or_symbol h with hinput | hinput
  · exact ⟨Word.Empty, by simpa [Word.Concat, Word.Empty] using hinput⟩
  · rcases hinput with ⟨a, hinput⟩
    exact ⟨Word.Symbol a, by
      simpa [Word.Concat, Word.Symbol] using hinput⟩

theorem computesIn_consumes_prefix {M : PDA input stack state}
    {n : Nat} {c d : Configuration input stack state}
    (h : ComputesIn M n c d) :
    exists consumed : Word input,
      c.unread = Word.Concat consumed d.unread := by
  induction h with
  | zero c =>
      exact ⟨Word.Empty, by simp [Word.Concat, Word.Empty]⟩
  | succ hstep _ ih =>
      rcases step_consumes_prefix hstep with ⟨first, hfirst⟩
      rcases ih with ⟨tail, htail⟩
      exact ⟨Word.Concat first tail, by
        rw [hfirst, htail]
        simp [Word.Concat, List.append_assoc]⟩

theorem computes_consumes_prefix {M : PDA input stack state}
    {c d : Configuration input stack state}
    (h : Computes M c d) :
    exists consumed : Word input,
      c.unread = Word.Concat consumed d.unread := by
  rcases computes_exists_length h with ⟨n, hn⟩
  exact computesIn_consumes_prefix hn

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
