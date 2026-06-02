import FoC.Foundation.Finite
import FoC.Languages.Language
import FoC.Computability.Tape

namespace FoC
namespace Computability

/-!
Deterministic one-tape Turing machines.

Used by:
- Chapter 5, Section 5.1: Turing-machine definition, configurations,
  step-by-step computation, halting, output, and acceptance by halting.
-/

open Foundation
open Languages

structure TuringMachine (symbol : Type u) (state : Type v) where
  start : state
  halt : state
  transition :
    state -> Option symbol -> Option (Option symbol × Direction × state)
  statesFinite : FiniteType state

namespace TuringMachine

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

def Halted (M : TuringMachine symbol state)
    (c : Configuration symbol state) : Prop :=
  c.state = M.halt

def HaltsFrom (M : TuringMachine symbol state)
    (c : Configuration symbol state) : Prop :=
  exists final, Computes M c final ∧ Halted M final

def HaltsOnInput (M : TuringMachine symbol state) (w : Word symbol) : Prop :=
  HaltsFrom M (initial M w)

def HaltsWithOutput (M : TuringMachine symbol state)
    (w out : Word symbol) : Prop :=
  exists final,
    Computes M (initial M w) final ∧
      Halted M final ∧
      final.tape = Tape.output out

def HaltsFromIn (M : TuringMachine symbol state) (n : Nat)
    (c : Configuration symbol state) : Prop :=
  exists final, ComputesIn M n c final ∧ Halted M final

def HaltsOnInputIn (M : TuringMachine symbol state) (n : Nat)
    (w : Word symbol) : Prop :=
  HaltsFromIn M n (initial M w)

def HaltsWithOutputIn (M : TuringMachine symbol state) (n : Nat)
    (w out : Word symbol) : Prop :=
  exists final,
    ComputesIn M n (initial M w) final ∧
      Halted M final ∧
      final.tape = Tape.output out

def Accepts (M : TuringMachine symbol state) (w : Word symbol) : Prop :=
  HaltsOnInput M w

def AcceptedLanguage (M : TuringMachine symbol state) : Language symbol :=
  fun w => Accepts M w

def Recognizes (M : TuringMachine symbol state) (L : Language symbol) : Prop :=
  Language.Equal (AcceptedLanguage M) L

theorem computes_refl (M : TuringMachine symbol state)
    (c : Configuration symbol state) :
    Computes M c c :=
  Computes.refl c

theorem computes_of_step {M : TuringMachine symbol state}
    {c d : Configuration symbol state} (h : Step M c d) :
    Computes M c d :=
  Computes.step h (Computes.refl d)

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

theorem computes_trans {M : TuringMachine symbol state}
    {a b c : Configuration symbol state}
    (hab : Computes M a b) (hbc : Computes M b c) : Computes M a c := by
  induction hab with
  | refl _ => exact hbc
  | step hstep _ ih => exact Computes.step hstep (ih hbc)

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

theorem halts_with_output_iff_exists_halts_with_output_in
    (M : TuringMachine symbol state) (w out : Word symbol) :
    HaltsWithOutput M w out <->
      exists n : Nat, HaltsWithOutputIn M n w out := by
  constructor
  · exact halts_with_output_to_halts_with_output_in
  · intro h
    cases h with
    | intro n hn => exact halts_with_output_in_to_halts_with_output hn

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
