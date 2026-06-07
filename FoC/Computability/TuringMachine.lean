import FoC.Foundation.Finite
import FoC.Languages.Language
import FoC.Computability.Tape

set_option doc.verso true

/-!
# Turing machines

## Configurations and computation

This module formalizes the deterministic one-tape machines used in Chapter 5.
A machine has a start state, a halting state, a partial transition function, and
a finite-state witness.  Configurations pair a state with a tape, and
computation is the reflexive-transitive closure of single-machine steps.

## Book coordinates

Used by:
- Chapter 5, Section 5.1: Turing-machine definition, configurations,
  step-by-step computation, halting, output, and acceptance by halting.
-/

namespace FoC
namespace Computability

open Foundation
open Languages

/-!
# Machine structure

A deterministic one-tape machine has a start state, halting state, partial
transition function, and finite-state witness.
-/

structure TuringMachine (symbol : Type u) (state : Type v) where
  start : state
  halt : state
  transition :
    state -> Option symbol -> Option (Option symbol × Direction × state)
  statesFinite : FiniteType state

namespace TuringMachine

/-!
# Configurations and steps

Configurations pair a control state with a tape. A step reads the current cell,
writes a new cell value, moves the head, and changes state according to the
partial transition function.
-/

structure Configuration (symbol : Type u) (state : Type v) where
  state : state
  tape : Tape symbol
deriving DecidableEq

def initial (M : TuringMachine symbol state) (w : Word symbol) :
    Configuration symbol state where
  state := M.start
  tape := Tape.input w

def applyAction (T : Tape symbol)
    (action : Option symbol × Direction × state) :
    Tape symbol × state :=
  let written := Tape.write action.1 T
  (Tape.move action.2.1 written, action.2.2)

inductive Step (M : TuringMachine symbol state) :
    Configuration symbol state -> Configuration symbol state -> Prop where
  | mk {c : Configuration symbol state} {write : Option symbol}
      {dir : Direction} {nextState : state} :
      M.transition c.state (Tape.read c.tape) = some (write, dir, nextState) ->
      Step M c
        { state := nextState, tape := Tape.move dir (Tape.write write c.tape) }

inductive Computes (M : TuringMachine symbol state) :
    Configuration symbol state -> Configuration symbol state -> Prop where
  | refl (c : Configuration symbol state) : Computes M c c
  | step {c d e : Configuration symbol state} :
      Step M c d -> Computes M d e -> Computes M c e

inductive ComputesIn (M : TuringMachine symbol state) :
    Nat -> Configuration symbol state -> Configuration symbol state -> Prop where
  | zero (c : Configuration symbol state) : ComputesIn M 0 c c
  | succ {n : Nat} {c d e : Configuration symbol state} :
      Step M c d -> ComputesIn M n d e -> ComputesIn M (n + 1) c e

/-!
# Exact tape-window invariants

The exact output relation compares final tapes literally with {name}`Tape.output`.
Moving off either end of the stored window grows the stored context. These
lemmas record the old exact-output obstruction while the public output
predicates below use normalized tape contents.
-/

theorem step_contextLength_mono {M : TuringMachine symbol state}
    {c d : Configuration symbol state} (h : Step M c d) :
    Tape.contextLength c.tape ≤ Tape.contextLength d.tape := by
  cases h with
  | mk =>
      exact Tape.contextLength_move_write_ge _ _ _

theorem computesIn_contextLength_mono {M : TuringMachine symbol state}
    {n : Nat} {c d : Configuration symbol state}
    (h : ComputesIn M n c d) :
    Tape.contextLength c.tape ≤ Tape.contextLength d.tape := by
  induction h with
  | zero c => exact Nat.le_refl _
  | succ hstep _ ih =>
      exact Nat.le_trans (step_contextLength_mono hstep) ih

theorem step_from_empty_contextLength_pos {M : TuringMachine symbol state}
    {d : Configuration symbol state}
    (h : Step M (initial M ([] : Word symbol)) d) :
    0 < Tape.contextLength d.tape := by
  cases h with
  | mk =>
      cases ‹Direction› <;>
        simp [initial, Tape.input_empty, Tape.contextLength, Tape.blank,
          Tape.move, Tape.moveLeft, Tape.moveRight, Tape.write]

theorem computesIn_empty_not_exact_output_single {M : TuringMachine symbol state}
    {n : Nat} {final : Configuration symbol state} (a : symbol)
    (hcomp : ComputesIn M n (initial M ([] : Word symbol)) final)
    (htape : final.tape = Tape.output [a]) :
    False := by
  cases hcomp with
  | zero c =>
      have hhead := congrArg Tape.head htape
      simp [initial, Tape.input_empty, Tape.output, Tape.blank] at hhead
      cases hhead
  | succ hstep hrest =>
      have hfirst := step_from_empty_contextLength_pos hstep
      have hmono := computesIn_contextLength_mono hrest
      have hpos : 0 < Tape.contextLength final.tape :=
        Nat.lt_of_lt_of_le hfirst hmono
      have hzero : Tape.contextLength final.tape = 0 := by
        rw [htape]
        exact Tape.contextLength_output_single a
      omega

/-!
# Halting and accepted languages

Halting predicates are stated from an arbitrary configuration, from an input
word, and with a specified output tape.
-/

def Halted (M : TuringMachine symbol state)
    (c : Configuration symbol state) : Prop :=
  c.state = M.halt

def HaltingTransitionsDisabled (M : TuringMachine symbol state) : Prop :=
  forall cell : Option symbol, M.transition M.halt cell = none

def HaltsFrom (M : TuringMachine symbol state)
    (c : Configuration symbol state) : Prop :=
  exists final, Computes M c final ∧ Halted M final

def HaltsOnInput (M : TuringMachine symbol state) (w : Word symbol) : Prop :=
  HaltsFrom M (initial M w)

def HaltsWithExactOutput (M : TuringMachine symbol state)
    (w out : Word symbol) : Prop :=
  exists final,
    Computes M (initial M w) final ∧
      Halted M final ∧
      final.tape = Tape.output out

def HaltsWithOutput (M : TuringMachine symbol state)
    (w out : Word symbol) : Prop :=
  exists final,
    Computes M (initial M w) final ∧
      Halted M final ∧
      Tape.normalizedOutput final.tape = out

def HaltsFromIn (M : TuringMachine symbol state) (n : Nat)
    (c : Configuration symbol state) : Prop :=
  exists final, ComputesIn M n c final ∧ Halted M final

def HaltsOnInputIn (M : TuringMachine symbol state) (n : Nat)
    (w : Word symbol) : Prop :=
  HaltsFromIn M n (initial M w)

def HaltsWithExactOutputIn (M : TuringMachine symbol state) (n : Nat)
    (w out : Word symbol) : Prop :=
  exists final,
    ComputesIn M n (initial M w) final ∧
      Halted M final ∧
      final.tape = Tape.output out

def HaltsWithOutputIn (M : TuringMachine symbol state) (n : Nat)
    (w out : Word symbol) : Prop :=
  exists final,
    ComputesIn M n (initial M w) final ∧
      Halted M final ∧
      Tape.normalizedOutput final.tape = out

def Accepts (M : TuringMachine symbol state) (w : Word symbol) : Prop :=
  HaltsOnInput M w

def AcceptedLanguage (M : TuringMachine symbol state) : Language symbol :=
  fun w => Accepts M w

def Recognizes (M : TuringMachine symbol state) (L : Language symbol) : Prop :=
  Language.Equal (AcceptedLanguage M) L

/-!
# Computation algebra

The basic facts prove reflexivity, determinism, transitivity, and equivalence
between unbounded computations and length-indexed computations.
-/

theorem computes_refl (M : TuringMachine symbol state)
    (c : Configuration symbol state) :
    Computes M c c :=
  Computes.refl c

theorem computes_of_step {M : TuringMachine symbol state}
    {c d : Configuration symbol state} (h : Step M c d) :
    Computes M c d :=
  Computes.step h (Computes.refl d)

theorem step_deterministic {M : TuringMachine symbol state}
    {c d e : Configuration symbol state}
    (hcd : Step M c d) (hce : Step M c e) :
    d = e := by
  cases hcd with
  | mk hcdAction =>
      cases hce with
      | mk hceAction =>
          have hAction : _ := Eq.trans hcdAction.symm hceAction
          cases hAction
          rfl

theorem no_step_from_halted {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    {c d : Configuration symbol state}
    (hhalt : Halted M c)
    (hstep : Step M c d) :
    False := by
  cases hstep with
  | mk haction =>
      rw [hhalt] at haction
      rw [hstop (Tape.read c.tape)] at haction
      cases haction

theorem computesIn_to_computes {M : TuringMachine symbol state}
    {n : Nat} {c d : Configuration symbol state}
    (h : ComputesIn M n c d) :
    Computes M c d := by
  induction h with
  | zero c => exact Computes.refl c
  | succ hstep _ ih => exact Computes.step hstep ih

theorem computes_to_computesIn {M : TuringMachine symbol state}
    {c d : Configuration symbol state}
    (h : Computes M c d) :
    exists n : Nat, ComputesIn M n c d := by
  induction h with
  | refl c => exact Exists.intro 0 (ComputesIn.zero c)
  | step hstep _ ih =>
      cases ih with
      | intro n hn =>
          exact Exists.intro (n + 1) (ComputesIn.succ hstep hn)

theorem computesIn_zero_eq {M : TuringMachine symbol state}
    {c d : Configuration symbol state}
    (h : ComputesIn M 0 c d) :
    c = d := by
  cases h
  rfl

theorem computesIn_trans_right {M : TuringMachine symbol state}
    {m n : Nat} {a b c : Configuration symbol state}
    (hab : ComputesIn M m a b) (hbc : ComputesIn M n b c) :
    ComputesIn M (n + m) a c := by
  induction hab generalizing n c with
  | zero a =>
      exact hbc
  | succ hstep _ ih =>
      exact ComputesIn.succ hstep (ih hbc)

theorem computesIn_trans {M : TuringMachine symbol state}
    {m n : Nat} {a b c : Configuration symbol state}
    (hab : ComputesIn M m a b) (hbc : ComputesIn M n b c) :
    ComputesIn M (m + n) a c := by
  rw [Nat.add_comm]
  exact computesIn_trans_right hab hbc

theorem computesIn_deterministic {M : TuringMachine symbol state}
    {n : Nat} {c d e : Configuration symbol state}
    (hcd : ComputesIn M n c d) (hce : ComputesIn M n c e) :
    d = e := by
  induction hcd generalizing e with
  | zero c =>
      cases hce
      rfl
  | succ hstep hrest ih =>
      cases hce with
      | succ hstep' hrest' =>
          have hNext := step_deterministic hstep hstep'
          cases hNext
          exact ih hrest'

theorem computes_trans {M : TuringMachine symbol state}
    {a b c : Configuration symbol state}
    (hab : Computes M a b) (hbc : Computes M b c) : Computes M a c := by
  induction hab with
  | refl _ => exact hbc
  | step hstep _ ih => exact Computes.step hstep (ih hbc)

theorem computes_from_halted_eq {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    {c d : Configuration symbol state}
    (hhalt : Halted M c)
    (hcomp : Computes M c d) :
    c = d := by
  induction hcomp with
  | refl _ => rfl
  | step hstep _ _ =>
      exact False.elim (no_step_from_halted hstop hhalt hstep)

theorem computes_to_halted_unique {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    {c d e : Configuration symbol state}
    (hcd : Computes M c d)
    (hd : Halted M d)
    (hce : Computes M c e)
    (he : Halted M e) :
    d = e := by
  induction hcd generalizing e with
  | refl _ =>
      exact computes_from_halted_eq hstop hd hce
  | step hstep _ ih =>
      cases hce with
      | refl _ =>
          exact False.elim (no_step_from_halted hstop he hstep)
      | step hstep' hrest' =>
          have hnext := step_deterministic hstep hstep'
          cases hnext
          exact ih hd hrest' he

theorem halts_with_output_implies_halts {M : TuringMachine symbol state}
    {w out : Word symbol} (h : HaltsWithOutput M w out) :
    HaltsOnInput M w := by
  cases h with
  | intro final hfinal =>
      exact Exists.intro final (And.intro hfinal.left hfinal.right.left)

theorem halts_with_output_in_implies_halts_in {M : TuringMachine symbol state}
    {n : Nat} {w out : Word symbol} (h : HaltsWithOutputIn M n w out) :
    HaltsOnInputIn M n w := by
  cases h with
  | intro final hfinal =>
      exact Exists.intro final (And.intro hfinal.left hfinal.right.left)

theorem halts_from_halted {M : TuringMachine symbol state}
    {c : Configuration symbol state} (h : Halted M c) :
    HaltsFrom M c := by
  exists c
  exact And.intro (Computes.refl c) h

theorem halts_from_of_computes {M : TuringMachine symbol state}
    {c d : Configuration symbol state}
    (hcomp : Computes M c d) (hhalt : Halted M d) :
    HaltsFrom M c :=
  Exists.intro d (And.intro hcomp hhalt)

theorem halts_from_in_to_halts_from {M : TuringMachine symbol state}
    {n : Nat} {c : Configuration symbol state}
    (h : HaltsFromIn M n c) :
    HaltsFrom M c := by
  cases h with
  | intro final hfinal =>
      exact Exists.intro final
        (And.intro (computesIn_to_computes hfinal.left) hfinal.right)

theorem halts_from_to_halts_from_in {M : TuringMachine symbol state}
    {c : Configuration symbol state}
    (h : HaltsFrom M c) :
    exists n : Nat, HaltsFromIn M n c := by
  cases h with
  | intro final hfinal =>
      cases computes_to_computesIn hfinal.left with
      | intro n hn =>
          exists n
          exact Exists.intro final (And.intro hn hfinal.right)

theorem halts_from_iff_exists_halts_from_in {M : TuringMachine symbol state}
    (c : Configuration symbol state) :
    HaltsFrom M c <-> exists n : Nat, HaltsFromIn M n c := by
  constructor
  · exact halts_from_to_halts_from_in
  · intro h
    cases h with
    | intro n hn => exact halts_from_in_to_halts_from hn

theorem halts_from_of_computes_prefix {M : TuringMachine symbol state}
    {c d : Configuration symbol state}
    (hcomp : Computes M c d) (hhalt : HaltsFrom M d) :
    HaltsFrom M c := by
  cases hhalt with
  | intro final hfinal =>
      exists final
      exact And.intro (computes_trans hcomp hfinal.left) hfinal.right

theorem halts_on_input_of_initial_halted {M : TuringMachine symbol state}
    {w : Word symbol} (h : Halted M (initial M w)) :
    HaltsOnInput M w :=
  halts_from_halted h

theorem halts_on_input_in_to_halts_on_input {M : TuringMachine symbol state}
    {n : Nat} {w : Word symbol}
    (h : HaltsOnInputIn M n w) :
    HaltsOnInput M w :=
  halts_from_in_to_halts_from h

theorem halts_on_input_to_halts_on_input_in {M : TuringMachine symbol state}
    {w : Word symbol}
    (h : HaltsOnInput M w) :
    exists n : Nat, HaltsOnInputIn M n w :=
  halts_from_to_halts_from_in h

theorem halts_on_input_iff_exists_halts_on_input_in
    (M : TuringMachine symbol state) (w : Word symbol) :
    HaltsOnInput M w <-> exists n : Nat, HaltsOnInputIn M n w :=
  halts_from_iff_exists_halts_from_in (initial M w)

theorem halts_with_output_in_to_halts_with_output
    {M : TuringMachine symbol state}
    {n : Nat} {w out : Word symbol}
    (h : HaltsWithOutputIn M n w out) :
    HaltsWithOutput M w out := by
  cases h with
  | intro final hfinal =>
      exists final
      exact And.intro (computesIn_to_computes hfinal.left) hfinal.right

theorem halts_with_output_to_halts_with_output_in
    {M : TuringMachine symbol state}
    {w out : Word symbol}
    (h : HaltsWithOutput M w out) :
    exists n : Nat, HaltsWithOutputIn M n w out := by
  cases h with
  | intro final hfinal =>
      cases computes_to_computesIn hfinal.left with
      | intro n hn =>
          exists n
          exact Exists.intro final (And.intro hn hfinal.right)

theorem halts_with_exact_output_in_to_halts_with_output_in
    {M : TuringMachine symbol state}
    {n : Nat} {w out : Word symbol}
    (h : HaltsWithExactOutputIn M n w out) :
    HaltsWithOutputIn M n w out := by
  cases h with
  | intro final hfinal =>
      exists final
      constructor
      · exact hfinal.left
      · constructor
        · exact hfinal.right.left
        · exact Tape.normalizedOutput_of_eq_output hfinal.right.right

theorem halts_with_exact_output_to_halts_with_output
    {M : TuringMachine symbol state}
    {w out : Word symbol}
    (h : HaltsWithExactOutput M w out) :
    HaltsWithOutput M w out := by
  cases h with
  | intro final hfinal =>
      exists final
      constructor
      · exact hfinal.left
      · constructor
        · exact hfinal.right.left
        · exact Tape.normalizedOutput_of_eq_output hfinal.right.right

theorem not_haltsWithExactOutput_empty_single (M : TuringMachine symbol state)
    (a : symbol) :
    ¬ HaltsWithExactOutput M ([] : Word symbol) [a] := by
  intro h
  cases h with
  | intro final hfinal =>
      cases computes_to_computesIn hfinal.left with
      | intro n hn =>
          exact computesIn_empty_not_exact_output_single a hn hfinal.right.right

theorem halts_with_output_iff_exists_halts_with_output_in
    (M : TuringMachine symbol state) (w out : Word symbol) :
    HaltsWithOutput M w out <->
      exists n : Nat, HaltsWithOutputIn M n w out := by
  constructor
  · exact halts_with_output_to_halts_with_output_in
  · intro h
    cases h with
    | intro n hn => exact halts_with_output_in_to_halts_with_output hn

theorem halts_with_output_in_output_unique
    {M : TuringMachine symbol state}
    {n : Nat} {w out1 out2 : Word symbol}
    (h1 : HaltsWithOutputIn M n w out1)
    (h2 : HaltsWithOutputIn M n w out2) :
    out1 = out2 := by
  cases h1 with
  | intro final1 hfinal1 =>
      cases h2 with
      | intro final2 hfinal2 =>
          have hfinal :
              final1 = final2 :=
            computesIn_deterministic hfinal1.left hfinal2.left
          apply Tape.output_injective
          rw [← hfinal1.right.right, ← hfinal2.right.right, hfinal]

theorem halts_with_output_unique
    {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    {w out1 out2 : Word symbol}
    (h1 : HaltsWithOutput M w out1)
    (h2 : HaltsWithOutput M w out2) :
    out1 = out2 := by
  cases h1 with
  | intro final1 hfinal1 =>
      cases h2 with
      | intro final2 hfinal2 =>
          have hfinal :
              final1 = final2 :=
            computes_to_halted_unique hstop
              hfinal1.left hfinal1.right.left
              hfinal2.left hfinal2.right.left
          apply Tape.output_injective
          rw [← hfinal1.right.right, ← hfinal2.right.right, hfinal]

theorem accepted_language_mem (M : TuringMachine symbol state) (w : Word symbol) :
    w ∈ AcceptedLanguage M <-> HaltsOnInput M w :=
  Iff.rfl

theorem recognizes_acceptedLanguage (M : TuringMachine symbol state) :
    Recognizes M (AcceptedLanguage M) :=
  Language.equal_refl (AcceptedLanguage M)

theorem recognizes_accepts_iff {M : TuringMachine symbol state}
    {L : Language symbol} (h : Recognizes M L) (w : Word symbol) :
    Accepts M w <-> w ∈ L :=
  h w

end TuringMachine

end Computability
end FoC
