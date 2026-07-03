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

inductive Step (M : TuringMachine symbol state) :
    Configuration symbol state -> Configuration symbol state -> Prop where
  | mk {c : Configuration symbol state} {write : Option symbol}
      {dir : Direction} {nextState : state} :
      M.transition c.state (Tape.read c.tape) = some (write, dir, nextState) ->
      Step M c
        { state := nextState, tape := Tape.move dir (Tape.write write c.tape) }

def stepConfig (M : TuringMachine symbol state)
    (c : Configuration symbol state) : Option (Configuration symbol state) :=
  match M.transition c.state (Tape.read c.tape) with
  | none => none
  | some (write, dir, nextState) =>
      some
        { state := nextState,
          tape := Tape.move dir (Tape.write write c.tape) }

def runConfig? (M : TuringMachine symbol state) :
    Nat -> Configuration symbol state -> Option (Configuration symbol state)
  | 0, c => some c
  | n + 1, c =>
      match M.stepConfig c with
      | none => none
      | some next => runConfig? M n next

theorem step_iff_transition_eq_some
    {M : TuringMachine symbol state}
    {c d : Configuration symbol state} :
    Step M c d <->
      exists write : Option symbol,
      exists dir : Direction,
      exists nextState : state,
        M.transition c.state (Tape.read c.tape) =
            some (write, dir, nextState) ∧
          d =
            { state := nextState,
              tape := Tape.move dir (Tape.write write c.tape) } := by
  constructor
  · intro hstep
    cases hstep with
    | mk haction =>
        exact ⟨_, _, _, haction, rfl⟩
  · intro h
    rcases h with ⟨write, dir, nextState, haction, rfl⟩
    exact Step.mk haction

theorem stepConfig_eq_some_iff_step
    {M : TuringMachine symbol state}
    {c d : Configuration symbol state} :
    M.stepConfig c = some d <-> Step M c d := by
  constructor
  · intro hstep
    unfold stepConfig at hstep
    cases haction : M.transition c.state (Tape.read c.tape) with
    | none =>
        simp [haction] at hstep
    | some action =>
        rcases action with ⟨write, dir, nextState⟩
        simp [haction] at hstep
        cases hstep
        exact Step.mk haction
  · intro hstep
    cases hstep with
    | mk haction =>
        simp [stepConfig, haction]

/-!
# Finite-state reindexing

The construction layers sometimes receive a machine whose state type lives in
an arbitrary universe.  Since every machine carries a finite-state witness, it
can be reindexed to a concrete {name}`Fin` state space without changing its
halting behavior.
-/

noncomputable def indexed (M : TuringMachine symbol state) :
    TuringMachine symbol (Fin M.statesFinite.elems.length) where
  start := Foundation.FiniteType.indexOf M.statesFinite M.start
  halt := Foundation.FiniteType.indexOf M.statesFinite M.halt
  transition := fun index cell =>
    match M.transition
        (Foundation.FiniteType.valueOf M.statesFinite index) cell with
    | none => none
    | some (write, dir, nextState) =>
        some (write, dir,
          Foundation.FiniteType.indexOf M.statesFinite nextState)
  statesFinite := Foundation.FiniteType.fin M.statesFinite.elems.length

def indexedDecidable [DecidableEq state] (M : TuringMachine symbol state) :
    TuringMachine symbol (Fin M.statesFinite.elems.length) where
  start := Foundation.FiniteType.indexOfDecidable M.statesFinite M.start
  halt := Foundation.FiniteType.indexOfDecidable M.statesFinite M.halt
  transition := fun index cell =>
    match M.transition
        (Foundation.FiniteType.valueOf M.statesFinite index) cell with
    | none => none
    | some (write, dir, nextState) =>
        some (write, dir,
          Foundation.FiniteType.indexOfDecidable
            M.statesFinite nextState)
  statesFinite := Foundation.FiniteType.fin M.statesFinite.elems.length

theorem indexed_step_of_step
    {M : TuringMachine symbol state}
    {c d : Configuration symbol state}
    (hstep : Step M c d) :
    Step (indexed M)
      { state := Foundation.FiniteType.indexOf M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.indexOf M.statesFinite d.state,
        tape := d.tape } := by
  cases hstep with
  | mk haction =>
      exact Step.mk (by
        simp [indexed, Foundation.FiniteType.valueOf_indexOf, haction])

theorem indexedDecidable_step_of_step [DecidableEq state]
    {M : TuringMachine symbol state}
    {c d : Configuration symbol state}
    (hstep : Step M c d) :
    Step (indexedDecidable M)
      { state := Foundation.FiniteType.indexOfDecidable M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.indexOfDecidable M.statesFinite d.state,
        tape := d.tape } := by
  cases hstep with
  | mk haction =>
      exact Step.mk (by
        simp [indexedDecidable, Foundation.FiniteType.valueOf_indexOfDecidable,
          haction])

theorem step_of_indexed_step
    {M : TuringMachine symbol state}
    {c d : Configuration symbol (Fin M.statesFinite.elems.length)}
    (hstep : Step (indexed M) c d) :
    Step M
      { state := Foundation.FiniteType.valueOf M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.valueOf M.statesFinite d.state,
        tape := d.tape } := by
  cases hstep with
  | mk haction =>
      cases hM :
          M.transition
            (Foundation.FiniteType.valueOf M.statesFinite c.state)
            (Tape.read c.tape) with
      | none =>
          simp [indexed, hM] at haction
      | some action =>
          rcases action with ⟨write, dir, nextState⟩
          simp [indexed, hM] at haction
          rcases haction with ⟨hwrite, hdir, hstate⟩
          subst hwrite
          subst hdir
          cases hstate
          simpa [Foundation.FiniteType.valueOf_indexOf] using
            Step.mk hM

theorem step_of_indexedDecidable_step [DecidableEq state]
    {M : TuringMachine symbol state}
    {c d : Configuration symbol (Fin M.statesFinite.elems.length)}
    (hstep : Step (indexedDecidable M) c d) :
    Step M
      { state := Foundation.FiniteType.valueOf M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.valueOf M.statesFinite d.state,
        tape := d.tape } := by
  cases hstep with
  | mk haction =>
      cases hM :
          M.transition
            (Foundation.FiniteType.valueOf M.statesFinite c.state)
            (Tape.read c.tape) with
      | none =>
          simp [indexedDecidable, hM] at haction
      | some action =>
          rcases action with ⟨write, dir, nextState⟩
          simp [indexedDecidable, hM] at haction
          rcases haction with ⟨hwrite, hdir, hstate⟩
          subst hwrite
          subst hdir
          cases hstate
          simpa [Foundation.FiniteType.valueOf_indexOfDecidable] using
            Step.mk hM

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

theorem indexed_computes_of_computes
    {M : TuringMachine symbol state}
    {c d : Configuration symbol state}
    (hcomp : Computes M c d) :
    Computes (indexed M)
      { state := Foundation.FiniteType.indexOf M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.indexOf M.statesFinite d.state,
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact Computes.refl _
  | step hstep _ ih =>
      exact Computes.step (indexed_step_of_step hstep) ih

theorem computes_of_indexed_computes
    {M : TuringMachine symbol state}
    {c d : Configuration symbol (Fin M.statesFinite.elems.length)}
    (hcomp : Computes (indexed M) c d) :
    Computes M
      { state := Foundation.FiniteType.valueOf M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.valueOf M.statesFinite d.state,
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact Computes.refl _
  | step hstep _ ih =>
      exact Computes.step (step_of_indexed_step hstep) ih

theorem indexed_computesIn_of_computesIn
    {M : TuringMachine symbol state}
    {n : Nat} {c d : Configuration symbol state}
    (hcomp : ComputesIn M n c d) :
    ComputesIn (indexed M) n
      { state := Foundation.FiniteType.indexOf M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.indexOf M.statesFinite d.state,
        tape := d.tape } := by
  induction hcomp with
  | zero c =>
      exact ComputesIn.zero _
  | succ hstep _ ih =>
      exact ComputesIn.succ (indexed_step_of_step hstep) ih

theorem computesIn_of_indexed_computesIn
    {M : TuringMachine symbol state}
    {n : Nat}
    {c d : Configuration symbol (Fin M.statesFinite.elems.length)}
    (hcomp : ComputesIn (indexed M) n c d) :
    ComputesIn M n
      { state := Foundation.FiniteType.valueOf M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.valueOf M.statesFinite d.state,
        tape := d.tape } := by
  induction hcomp with
  | zero c =>
      exact ComputesIn.zero _
  | succ hstep _ ih =>
      exact ComputesIn.succ (step_of_indexed_step hstep) ih

theorem indexedDecidable_computes_of_computes [DecidableEq state]
    {M : TuringMachine symbol state}
    {c d : Configuration symbol state}
    (hcomp : Computes M c d) :
    Computes (indexedDecidable M)
      { state := Foundation.FiniteType.indexOfDecidable M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.indexOfDecidable M.statesFinite d.state,
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact Computes.refl _
  | step hstep _ ih =>
      exact Computes.step (indexedDecidable_step_of_step hstep) ih

theorem computes_of_indexedDecidable_computes [DecidableEq state]
    {M : TuringMachine symbol state}
    {c d : Configuration symbol (Fin M.statesFinite.elems.length)}
    (hcomp : Computes (indexedDecidable M) c d) :
    Computes M
      { state := Foundation.FiniteType.valueOf M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.valueOf M.statesFinite d.state,
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact Computes.refl _
  | step hstep _ ih =>
      exact Computes.step (step_of_indexedDecidable_step hstep) ih

theorem indexedDecidable_computesIn_of_computesIn [DecidableEq state]
    {M : TuringMachine symbol state}
    {n : Nat} {c d : Configuration symbol state}
    (hcomp : ComputesIn M n c d) :
    ComputesIn (indexedDecidable M) n
      { state := Foundation.FiniteType.indexOfDecidable M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.indexOfDecidable M.statesFinite d.state,
        tape := d.tape } := by
  induction hcomp with
  | zero c =>
      exact ComputesIn.zero _
  | succ hstep _ ih =>
      exact ComputesIn.succ (indexedDecidable_step_of_step hstep) ih

theorem computesIn_of_indexedDecidable_computesIn [DecidableEq state]
    {M : TuringMachine symbol state}
    {n : Nat}
    {c d : Configuration symbol (Fin M.statesFinite.elems.length)}
    (hcomp : ComputesIn (indexedDecidable M) n c d) :
    ComputesIn M n
      { state := Foundation.FiniteType.valueOf M.statesFinite c.state,
        tape := c.tape }
      { state := Foundation.FiniteType.valueOf M.statesFinite d.state,
        tape := d.tape } := by
  induction hcomp with
  | zero c =>
      exact ComputesIn.zero _
  | succ hstep _ ih =>
      exact ComputesIn.succ (step_of_indexedDecidable_step hstep) ih

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
      lia

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

theorem indexed_haltsFrom_iff
    (M : TuringMachine symbol state)
    (c : Configuration symbol state) :
    HaltsFrom (indexed M)
        { state := Foundation.FiniteType.indexOf M.statesFinite c.state,
          tape := c.tape } <->
      HaltsFrom M c := by
  constructor
  · intro hhalt
    rcases hhalt with ⟨final, hcomp, hfinal⟩
    have hcompOriginal :=
      computes_of_indexed_computes (M := M) hcomp
    have hstate :
        Foundation.FiniteType.valueOf M.statesFinite final.state =
          M.halt := by
      have hindex :
          final.state =
            Foundation.FiniteType.indexOf M.statesFinite M.halt := by
        simpa [Halted, indexed] using hfinal
      rw [hindex, Foundation.FiniteType.valueOf_indexOf]
    exact
      ⟨{ state :=
            Foundation.FiniteType.valueOf M.statesFinite final.state,
          tape := final.tape },
        by
          simpa [Foundation.FiniteType.valueOf_indexOf] using
            hcompOriginal,
        by
          simp [Halted, hstate]⟩
  · intro hhalt
    rcases hhalt with ⟨final, hcomp, hfinal⟩
    have hcompIndexed :=
      indexed_computes_of_computes (M := M) hcomp
    exact
      ⟨{ state := Foundation.FiniteType.indexOf M.statesFinite final.state,
          tape := final.tape },
        hcompIndexed,
        by
          have hstate : final.state = M.halt := by
            simpa [Halted] using hfinal
          simp [Halted, indexed, hstate]⟩

theorem indexed_haltsOnInput_iff
    (M : TuringMachine symbol state) (w : Word symbol) :
    HaltsOnInput (indexed M) w <-> HaltsOnInput M w := by
  simpa [HaltsOnInput, initial, indexed] using
    indexed_haltsFrom_iff (M := M) (c := initial M w)

theorem indexed_haltsFromIn_iff
    (M : TuringMachine symbol state) (n : Nat)
    (c : Configuration symbol state) :
    HaltsFromIn (indexed M) n
        { state := Foundation.FiniteType.indexOf M.statesFinite c.state,
          tape := c.tape } <->
      HaltsFromIn M n c := by
  constructor
  · intro hhalt
    rcases hhalt with ⟨final, hcomp, hfinal⟩
    have hcompOriginal :=
      computesIn_of_indexed_computesIn (M := M) hcomp
    have hstate :
        Foundation.FiniteType.valueOf M.statesFinite final.state =
          M.halt := by
      have hindex :
          final.state =
            Foundation.FiniteType.indexOf M.statesFinite M.halt := by
        simpa [Halted, indexed] using hfinal
      rw [hindex, Foundation.FiniteType.valueOf_indexOf]
    exact
      ⟨{ state :=
            Foundation.FiniteType.valueOf M.statesFinite final.state,
          tape := final.tape },
        by
          simpa [Foundation.FiniteType.valueOf_indexOf] using
            hcompOriginal,
        by
          simp [Halted, hstate]⟩
  · intro hhalt
    rcases hhalt with ⟨final, hcomp, hfinal⟩
    have hcompIndexed :=
      indexed_computesIn_of_computesIn (M := M) hcomp
    exact
      ⟨{ state := Foundation.FiniteType.indexOf M.statesFinite final.state,
          tape := final.tape },
        hcompIndexed,
        by
          have hstate : final.state = M.halt := by
            simpa [Halted] using hfinal
          simp [Halted, indexed, hstate]⟩

theorem indexed_haltsOnInputIn_iff
    (M : TuringMachine symbol state) (n : Nat) (w : Word symbol) :
    HaltsOnInputIn (indexed M) n w <-> HaltsOnInputIn M n w := by
  simpa [HaltsOnInputIn, initial, indexed] using
    indexed_haltsFromIn_iff (M := M) (n := n) (c := initial M w)

theorem indexedDecidable_haltsFromIn_iff [DecidableEq state]
    (M : TuringMachine symbol state) (n : Nat)
    (c : Configuration symbol state) :
    HaltsFromIn (indexedDecidable M) n
        { state :=
            Foundation.FiniteType.indexOfDecidable M.statesFinite c.state,
          tape := c.tape } <->
      HaltsFromIn M n c := by
  constructor
  · intro hhalt
    rcases hhalt with ⟨final, hcomp, hfinal⟩
    have hcompOriginal :=
      computesIn_of_indexedDecidable_computesIn (M := M) hcomp
    have hstate :
        Foundation.FiniteType.valueOf M.statesFinite final.state =
          M.halt := by
      have hindex :
          final.state =
            Foundation.FiniteType.indexOfDecidable
              M.statesFinite M.halt := by
        simpa [Halted, indexedDecidable] using hfinal
      rw [hindex, Foundation.FiniteType.valueOf_indexOfDecidable]
    exact
      ⟨{ state :=
            Foundation.FiniteType.valueOf M.statesFinite final.state,
          tape := final.tape },
        by
          simpa [Foundation.FiniteType.valueOf_indexOfDecidable] using
            hcompOriginal,
        by
          simp [Halted, hstate]⟩
  · intro hhalt
    rcases hhalt with ⟨final, hcomp, hfinal⟩
    have hcompIndexed :=
      indexedDecidable_computesIn_of_computesIn (M := M) hcomp
    exact
      ⟨{ state :=
            Foundation.FiniteType.indexOfDecidable
              M.statesFinite final.state,
          tape := final.tape },
        hcompIndexed,
        by
          have hstate : final.state = M.halt := by
            simpa [Halted] using hfinal
          simp [Halted, indexedDecidable, hstate]⟩

theorem indexedDecidable_haltsOnInputIn_iff [DecidableEq state]
    (M : TuringMachine symbol state) (n : Nat) (w : Word symbol) :
    HaltsOnInputIn (indexedDecidable M) n w <-> HaltsOnInputIn M n w := by
  simpa [HaltsOnInputIn, initial, indexedDecidable] using
    indexedDecidable_haltsFromIn_iff (M := M) (n := n)
      (c := initial M w)

theorem computesIn_succ_iff {M : TuringMachine symbol state}
    {n : Nat} {c e : Configuration symbol state} :
    ComputesIn M (n + 1) c e <->
      exists d : Configuration symbol state,
        Step M c d ∧ ComputesIn M n d e := by
  constructor
  · intro h
    cases h with
    | succ hstep hrest =>
        exact ⟨_, hstep, hrest⟩
  · intro h
    rcases h with ⟨d, hstep, hrest⟩
    exact ComputesIn.succ hstep hrest

theorem runConfig?_eq_some_iff_computesIn
    {M : TuringMachine symbol state}
    {n : Nat} {c d : Configuration symbol state} :
    M.runConfig? n c = some d <-> ComputesIn M n c d := by
  induction n generalizing c with
  | zero =>
      constructor
      · intro hrun
        simp [runConfig?] at hrun
        cases hrun
        exact ComputesIn.zero _
      · intro hcomp
        cases hcomp
        simp [runConfig?]
  | succ n ih =>
      constructor
      · intro hrun
        simp [runConfig?] at hrun
        cases hstep : M.stepConfig c with
        | none =>
            simp [hstep] at hrun
        | some next =>
            simp [hstep] at hrun
            exact
              ComputesIn.succ
                (stepConfig_eq_some_iff_step.mp hstep)
                (ih.mp hrun)
      · intro hcomp
        rcases computesIn_succ_iff.mp hcomp with
          ⟨next, hstep, htail⟩
        have hstepConfig : M.stepConfig c = some next :=
          stepConfig_eq_some_iff_step.mpr hstep
        simp [runConfig?, hstepConfig]
        exact ih.mpr htail

theorem haltsFromIn_iff_runConfig?
    {M : TuringMachine symbol state}
    {n : Nat} {c : Configuration symbol state} :
    HaltsFromIn M n c <->
      exists final : Configuration symbol state,
        M.runConfig? n c = some final ∧ Halted M final := by
  constructor
  · intro hhalt
    rcases hhalt with ⟨final, hcomp, hfinal⟩
    exact
      ⟨final, runConfig?_eq_some_iff_computesIn.mpr hcomp, hfinal⟩
  · intro hhalt
    rcases hhalt with ⟨final, hrun, hfinal⟩
    exact
      ⟨final, runConfig?_eq_some_iff_computesIn.mp hrun, hfinal⟩

instance [DecidableEq state] (M : TuringMachine symbol state)
    (n : Nat) (c : Configuration symbol state) :
    Decidable (HaltsFromIn M n c) := by
  cases hrun : M.runConfig? n c with
  | none =>
      exact isFalse (by
        intro hhalt
        rcases haltsFromIn_iff_runConfig?.mp hhalt with
          ⟨final, hfinal, _hhalted⟩
        rw [hrun] at hfinal
        cases hfinal)
  | some final =>
      by_cases hhalted : final.state = M.halt
      · exact isTrue (haltsFromIn_iff_runConfig?.mpr
          ⟨final, hrun, by simpa [Halted] using hhalted⟩)
      · exact isFalse (by
          intro hhalt
          rcases haltsFromIn_iff_runConfig?.mp hhalt with
            ⟨final', hfinal', hhalted'⟩
          rw [hrun] at hfinal'
          cases hfinal'
          exact hhalted (by simpa [Halted] using hhalted'))

instance [DecidableEq state] (M : TuringMachine symbol state)
    (n : Nat) (w : Word symbol) :
    Decidable (HaltsOnInputIn M n w) := by
  unfold HaltsOnInputIn
  infer_instance

theorem haltsFromIn_zero_iff {M : TuringMachine symbol state}
    {c : Configuration symbol state} :
    HaltsFromIn M 0 c <-> Halted M c := by
  constructor
  · intro h
    rcases h with ⟨final, hcomp, hhalt⟩
    cases hcomp
    exact hhalt
  · intro h
    exact ⟨c, ComputesIn.zero c, h⟩

theorem haltsOnInputIn_zero_iff {M : TuringMachine symbol state}
    {w : Word symbol} :
    HaltsOnInputIn M 0 w <-> Halted M (initial M w) := by
  exact haltsFromIn_zero_iff

theorem haltsFromIn_succ_iff {M : TuringMachine symbol state}
    {n : Nat} {c : Configuration symbol state} :
    HaltsFromIn M (n + 1) c <->
      exists d : Configuration symbol state,
        Step M c d ∧ HaltsFromIn M n d := by
  constructor
  · intro h
    rcases h with ⟨final, hcomp, hhalt⟩
    rcases computesIn_succ_iff.mp hcomp with
      ⟨d, hstep, hrest⟩
    exact ⟨d, hstep, final, hrest, hhalt⟩
  · intro h
    rcases h with ⟨d, hstep, final, hrest, hhalt⟩
    exact ⟨final, ComputesIn.succ hstep hrest, hhalt⟩

theorem haltsOnInputIn_succ_iff {M : TuringMachine symbol state}
    {n : Nat} {w : Word symbol} :
    HaltsOnInputIn M (n + 1) w <->
      exists d : Configuration symbol state,
        Step M (initial M w) d ∧ HaltsFromIn M n d := by
  exact haltsFromIn_succ_iff

theorem not_step_of_transition_eq_none
    {M : TuringMachine symbol state}
    {c d : Configuration symbol state}
    (htransition :
      M.transition c.state (Tape.read c.tape) = none) :
    ¬ Step M c d := by
  intro hstep
  cases hstep with
  | mk haction =>
      rw [htransition] at haction
      cases haction

theorem not_haltsFromIn_succ_of_transition_eq_none
    {M : TuringMachine symbol state}
    {n : Nat} {c : Configuration symbol state}
    (htransition :
      M.transition c.state (Tape.read c.tape) = none) :
    ¬ HaltsFromIn M (n + 1) c := by
  intro hhalt
  rcases haltsFromIn_succ_iff.mp hhalt with
    ⟨d, hstep, _htail⟩
  exact not_step_of_transition_eq_none htransition hstep

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

theorem computesIn_succ_iff_of_transition_eq_some
    {M : TuringMachine symbol state}
    {n : Nat} {c e : Configuration symbol state}
    {write : Option symbol} {dir : Direction} {nextState : state}
    (htransition :
      M.transition c.state (Tape.read c.tape) =
        some (write, dir, nextState)) :
    ComputesIn M (n + 1) c e <->
      ComputesIn M n
        { state := nextState,
          tape := Tape.move dir (Tape.write write c.tape) } e := by
  constructor
  · intro hcomp
    rcases computesIn_succ_iff.mp hcomp with
      ⟨d, hstep, htail⟩
    have hd :
        d =
          { state := nextState,
            tape := Tape.move dir (Tape.write write c.tape) } := by
      exact step_deterministic hstep (Step.mk htransition)
    cases hd
    exact htail
  · intro htail
    exact ComputesIn.succ (Step.mk htransition) htail

theorem computesIn_succ_iff_false_of_transition_eq_none
    {M : TuringMachine symbol state}
    {n : Nat} {c e : Configuration symbol state}
    (htransition :
      M.transition c.state (Tape.read c.tape) = none) :
    ComputesIn M (n + 1) c e <-> False := by
  constructor
  · intro hcomp
    rcases computesIn_succ_iff.mp hcomp with
      ⟨d, hstep, _htail⟩
    exact not_step_of_transition_eq_none htransition hstep
  · intro hfalse
    cases hfalse

theorem haltsFromIn_succ_of_step {M : TuringMachine symbol state}
    {n : Nat} {c d : Configuration symbol state}
    (hstep : Step M c d) (htail : HaltsFromIn M n d) :
    HaltsFromIn M (n + 1) c := by
  exact haltsFromIn_succ_iff.mpr ⟨d, hstep, htail⟩

theorem haltsFromIn_tail_of_step {M : TuringMachine symbol state}
    {n : Nat} {c d : Configuration symbol state}
    (hstep : Step M c d) (hhalt : HaltsFromIn M (n + 1) c) :
    HaltsFromIn M n d := by
  rcases haltsFromIn_succ_iff.mp hhalt with
    ⟨next, hstepNext, htail⟩
  have hnext : d = next := step_deterministic hstep hstepNext
  cases hnext
  exact htail

theorem haltsFromIn_succ_iff_of_step {M : TuringMachine symbol state}
    {n : Nat} {c d : Configuration symbol state}
    (hstep : Step M c d) :
    HaltsFromIn M (n + 1) c <-> HaltsFromIn M n d := by
  constructor
  · exact haltsFromIn_tail_of_step hstep
  · exact haltsFromIn_succ_of_step hstep

theorem haltsFromIn_succ_transition_iff
    {M : TuringMachine symbol state}
    {n : Nat} {c : Configuration symbol state} :
    HaltsFromIn M (n + 1) c <->
      exists write : Option symbol,
      exists dir : Direction,
      exists nextState : state,
        M.transition c.state (Tape.read c.tape) =
          some (write, dir, nextState) ∧
          HaltsFromIn M n
            { state := nextState,
              tape := Tape.move dir (Tape.write write c.tape) } := by
  constructor
  · intro hhalt
    rcases haltsFromIn_succ_iff.mp hhalt with
      ⟨d, hstep, htail⟩
    cases hstep with
    | mk haction =>
        exact ⟨_, _, _, haction, htail⟩
  · intro h
    rcases h with ⟨write, dir, nextState, haction, htail⟩
    exact
      haltsFromIn_succ_of_step
        (Step.mk haction)
        htail

theorem haltsFromIn_succ_iff_of_transition_eq_some
    {M : TuringMachine symbol state}
    {n : Nat} {c : Configuration symbol state}
    {write : Option symbol} {dir : Direction} {nextState : state}
    (htransition :
      M.transition c.state (Tape.read c.tape) =
        some (write, dir, nextState)) :
    HaltsFromIn M (n + 1) c <->
      HaltsFromIn M n
        { state := nextState,
          tape := Tape.move dir (Tape.write write c.tape) } := by
  exact haltsFromIn_succ_iff_of_step (Step.mk htransition)

theorem haltsFromIn_succ_iff_false_of_transition_eq_none
    {M : TuringMachine symbol state}
    {n : Nat} {c : Configuration symbol state}
    (htransition :
      M.transition c.state (Tape.read c.tape) = none) :
    HaltsFromIn M (n + 1) c <-> False := by
  constructor
  · intro hhalt
    exact not_haltsFromIn_succ_of_transition_eq_none htransition hhalt
  · intro hfalse
    cases hfalse

theorem haltsOnInputIn_succ_iff_of_step
    {M : TuringMachine symbol state}
    {n : Nat} {w : Word symbol}
    {d : Configuration symbol state}
    (hstep : Step M (initial M w) d) :
    HaltsOnInputIn M (n + 1) w <-> HaltsFromIn M n d := by
  exact haltsFromIn_succ_iff_of_step hstep

theorem haltsOnInputIn_succ_transition_iff
    {M : TuringMachine symbol state}
    {n : Nat} {w : Word symbol} :
    HaltsOnInputIn M (n + 1) w <->
      exists write : Option symbol,
      exists dir : Direction,
      exists nextState : state,
        M.transition M.start (Tape.read (Tape.input w)) =
          some (write, dir, nextState) ∧
          HaltsFromIn M n
            { state := nextState,
              tape :=
                Tape.move dir
                  (Tape.write write (Tape.input w)) } := by
  simpa [HaltsOnInputIn, initial] using
    (haltsFromIn_succ_transition_iff
      (M := M) (n := n) (c := initial M w))

theorem haltsOnInputIn_succ_iff_of_transition_eq_some
    {M : TuringMachine symbol state}
    {n : Nat} {w : Word symbol}
    {write : Option symbol} {dir : Direction} {nextState : state}
    (htransition :
      M.transition M.start (Tape.read (Tape.input w)) =
        some (write, dir, nextState)) :
    HaltsOnInputIn M (n + 1) w <->
      HaltsFromIn M n
        { state := nextState,
          tape := Tape.move dir (Tape.write write (Tape.input w)) } := by
  simpa [HaltsOnInputIn, initial] using
    (haltsFromIn_succ_iff_of_transition_eq_some
      (M := M) (n := n) (c := initial M w) htransition)

theorem haltsOnInputIn_succ_iff_false_of_transition_eq_none
    {M : TuringMachine symbol state}
    {n : Nat} {w : Word symbol}
    (htransition :
      M.transition M.start (Tape.read (Tape.input w)) = none) :
    HaltsOnInputIn M (n + 1) w <-> False := by
  simpa [HaltsOnInputIn, initial] using
    (haltsFromIn_succ_iff_false_of_transition_eq_none
      (M := M) (n := n) (c := initial M w) htransition)

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
