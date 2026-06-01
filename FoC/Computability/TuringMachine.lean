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
