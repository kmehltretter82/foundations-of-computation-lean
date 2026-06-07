import FoC.Computability.Recognizable

set_option doc.verso true

/-!
# Machine transformations

## Decider to acceptor

This module collects reusable transformations between concrete Turing machines.
The first construction turns a stopped yes/no decider into a halting-only
acceptor: it simulates the decider, checks the halted output cell, and enters
its own halt state exactly on the accepting output.

## Book coordinates

Used by:
- Chapter 5, Section 5.1: decidability implies acceptability for stopped
  yes/no deciders.
-/

namespace FoC
namespace Computability

open Foundation
open Languages
open Classical

/-!
# Decider-to-acceptor state space

The transformed machine runs the original machine in a tagged state, enters
{lit}`accept` when the simulated halted configuration shows the accepting symbol,
and otherwise moves to a nonhalting loop.
-/

inductive DeciderToAcceptorState (state : Type u) where
  | run : state -> DeciderToAcceptorState state
  | accept : DeciderToAcceptorState state
  | loop : DeciderToAcceptorState state

namespace DeciderToAcceptorState

def finite (h : FiniteType state) : FiniteType (DeciderToAcceptorState state) where
  elems := h.elems.map DeciderToAcceptorState.run ++
    [DeciderToAcceptorState.accept, DeciderToAcceptorState.loop]
  complete := by
    intro q
    cases q with
    | run s =>
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨s, h.complete s, rfl⟩
    | accept =>
        apply List.mem_append_right
        simp
    | loop =>
        apply List.mem_append_right
        simp

end DeciderToAcceptorState

/-!
# Normalized-output decider-to-acceptor state space

For a general normalized-output decider, the halted head may not sit on the
accepting or rejecting symbol.  The scanner below uses the rejecting symbol as
a temporary marker.  It never writes the accepting symbol; after the decider
halts, it expands a visited interval alternately to the right and to the left
until it encounters the accepting symbol.
-/

inductive NormalizedDeciderToAcceptorState (state : Type u) where
  | run : state -> NormalizedDeciderToAcceptorState state
  | sweepRight : NormalizedDeciderToAcceptorState state
  | sweepLeft : NormalizedDeciderToAcceptorState state
  | accept : NormalizedDeciderToAcceptorState state

namespace NormalizedDeciderToAcceptorState

def finite (h : FiniteType state) :
    FiniteType (NormalizedDeciderToAcceptorState state) where
  elems := h.elems.map NormalizedDeciderToAcceptorState.run ++
    [NormalizedDeciderToAcceptorState.sweepRight,
      NormalizedDeciderToAcceptorState.sweepLeft,
      NormalizedDeciderToAcceptorState.accept]
  complete := by
    intro q
    cases q with
    | run s =>
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨s, h.complete s, rfl⟩
    | sweepRight =>
        apply List.mem_append_right
        simp
    | sweepLeft =>
        apply List.mem_append_right
        simp
    | accept =>
        apply List.mem_append_right
        simp

end NormalizedDeciderToAcceptorState

namespace TuringMachine

theorem tape_read_mem_cells {T : Tape symbol} {a : symbol}
    (hread : Tape.read T = some a) :
    some a ∈ Tape.cells T := by
  cases T with
  | mk left head right =>
      simp [Tape.read, Tape.cells] at hread ⊢
      exact Or.inr (Or.inl hread.symm)

theorem tape_mem_cells_move_of_mem
    (dir : Direction) {T : Tape symbol} {a : symbol}
    (hmem : some a ∈ Tape.cells T) :
    some a ∈ Tape.cells (Tape.move dir T) := by
  cases T with
  | mk left head right =>
      cases dir with
      | left =>
          cases left with
          | nil =>
              simp [Tape.move, Tape.moveLeft, Tape.cells] at hmem ⊢
              exact hmem
          | cons leftHead leftTail =>
              simp [Tape.move, Tape.moveLeft, Tape.cells, List.reverse_cons,
                List.append_assoc] at hmem ⊢
              exact hmem
      | right =>
          cases right with
          | nil =>
              simp [Tape.move, Tape.moveRight, Tape.cells, List.reverse_cons,
                List.append_assoc] at hmem ⊢
              exact hmem
          | cons rightHead rightTail =>
              simp [Tape.move, Tape.moveRight, Tape.cells, List.reverse_cons,
                List.append_assoc] at hmem ⊢
              exact hmem

theorem tape_mem_cells_of_move_mem
    (dir : Direction) {T : Tape symbol} {a : symbol}
    (hmem : some a ∈ Tape.cells (Tape.move dir T)) :
    some a ∈ Tape.cells T := by
  cases T with
  | mk left head right =>
      cases dir with
      | left =>
          cases left with
          | nil =>
              simp [Tape.move, Tape.moveLeft, Tape.cells] at hmem ⊢
              exact hmem
          | cons leftHead leftTail =>
              simp [Tape.move, Tape.moveLeft, Tape.cells, List.reverse_cons,
                List.append_assoc] at hmem ⊢
              exact hmem
      | right =>
          cases right with
          | nil =>
              simp [Tape.move, Tape.moveRight, Tape.cells, List.reverse_cons,
                List.append_assoc] at hmem ⊢
              exact hmem
          | cons rightHead rightTail =>
              simp [Tape.move, Tape.moveRight, Tape.cells, List.reverse_cons,
                List.append_assoc] at hmem ⊢
              exact hmem

theorem tape_mem_cells_of_write_marker_move_mem
    {zero one : symbol} (hzeroOne : zero ≠ one)
    (dir : Direction) {T : Tape symbol}
    (hmem :
      some one ∈ Tape.cells
        (Tape.move dir (Tape.write (some zero) T))) :
    some one ∈ Tape.cells T := by
  have hwrite :
      some one ∈ Tape.cells (Tape.write (some zero) T) :=
    tape_mem_cells_of_move_mem dir hmem
  cases T with
  | mk left head right =>
      simp [Tape.write, Tape.cells] at hwrite ⊢
      rcases hwrite with hleft | hhead | hright
      · exact Or.inl hleft
      · exact False.elim (hzeroOne (by simpa using hhead.symm))
      · exact Or.inr (Or.inr hright)

theorem tape_write_read_eq (T : Tape symbol) :
    Tape.write (Tape.read T) T = T := by
  cases T
  rfl

theorem not_mem_some_of_filterMap_singleton_ne
    {cells : List (Option symbol)} {zero one : symbol}
    (hzeroOne : zero ≠ one)
    (h : cells.filterMap (fun cell => cell) = [zero]) :
    some one ∉ cells := by
  induction cells with
  | nil =>
      intro hmem
      cases hmem
  | cons cell rest ih =>
      intro hmem
      cases cell with
      | none =>
          simp at hmem h
          exact ih h hmem
      | some a =>
          simp at h
          have haZero : a = zero := h.left
          cases hmem with
          | head =>
              exact hzeroOne (by rw [← haZero])
          | tail _ htail =>
              have hnone := h.right (some one) htail
              cases hnone

theorem tape_no_one_of_normalized_zero
    {T : Tape symbol} {zero one : symbol}
    (hzeroOne : zero ≠ one)
    (hout : Tape.normalizedOutput T = [zero]) :
    some one ∉ Tape.cells T :=
  not_mem_some_of_filterMap_singleton_ne hzeroOne hout

def normalizedRunConfig (c : Configuration symbol state) :
    Configuration symbol (NormalizedDeciderToAcceptorState state) where
  state := NormalizedDeciderToAcceptorState.run c.state
  tape := c.tape

noncomputable def normalizedDeciderToAcceptorTransition
    (M : TuringMachine symbol state) (zero one : symbol) :
    NormalizedDeciderToAcceptorState state -> Option symbol ->
      Option (Option symbol × Direction ×
        NormalizedDeciderToAcceptorState state)
  | NormalizedDeciderToAcceptorState.run s, cell =>
      if s = M.halt then
        if cell = some one then
          some (cell, Direction.right,
            NormalizedDeciderToAcceptorState.accept)
        else
          some (some zero, Direction.right,
            NormalizedDeciderToAcceptorState.sweepRight)
      else
        match M.transition s cell with
        | some (write, dir, nextState) =>
            some (write, dir,
              NormalizedDeciderToAcceptorState.run nextState)
        | none => none
  | NormalizedDeciderToAcceptorState.sweepRight, cell =>
      if cell = some one then
        some (cell, Direction.right,
          NormalizedDeciderToAcceptorState.accept)
      else
        match cell with
        | none =>
            some (some zero, Direction.left,
              NormalizedDeciderToAcceptorState.sweepLeft)
        | some a =>
            some (some a, Direction.right,
              NormalizedDeciderToAcceptorState.sweepRight)
  | NormalizedDeciderToAcceptorState.sweepLeft, cell =>
      if cell = some one then
        some (cell, Direction.right,
          NormalizedDeciderToAcceptorState.accept)
      else
        match cell with
        | none =>
            some (some zero, Direction.right,
              NormalizedDeciderToAcceptorState.sweepRight)
        | some a =>
            some (some a, Direction.left,
              NormalizedDeciderToAcceptorState.sweepLeft)
  | NormalizedDeciderToAcceptorState.accept, _ => none

noncomputable def normalizedDeciderToAcceptor
    (M : TuringMachine symbol state) (zero one : symbol) :
    TuringMachine symbol (NormalizedDeciderToAcceptorState state) where
  start := NormalizedDeciderToAcceptorState.run M.start
  halt := NormalizedDeciderToAcceptorState.accept
  transition := normalizedDeciderToAcceptorTransition M zero one
  statesFinite := NormalizedDeciderToAcceptorState.finite M.statesFinite

@[simp] theorem normalizedDeciderToAcceptor_initial
    (M : TuringMachine symbol state) (zero one : symbol) (w : Word symbol) :
    (normalizedDeciderToAcceptor M zero one).initial w =
      normalizedRunConfig (M.initial w) :=
  rfl

theorem normalizedDeciderToAcceptor_step_run
    {M : TuringMachine symbol state} {zero one : symbol}
    {c d : Configuration symbol state}
    (hnot : c.state ≠ M.halt)
    (hstep : Step M c d) :
    Step (normalizedDeciderToAcceptor M zero one)
      (normalizedRunConfig c) (normalizedRunConfig d) := by
  cases hstep with
  | mk haction =>
      exact Step.mk (by
        simp [normalizedRunConfig, normalizedDeciderToAcceptor,
          normalizedDeciderToAcceptorTransition, hnot, haction])

theorem normalizedDeciderToAcceptor_step_run_of_stopped
    {M : TuringMachine symbol state} {zero one : symbol}
    (hstop : HaltingTransitionsDisabled M)
    {c d : Configuration symbol state}
    (hstep : Step M c d) :
    Step (normalizedDeciderToAcceptor M zero one)
      (normalizedRunConfig c) (normalizedRunConfig d) := by
  have hnot : c.state ≠ M.halt := by
    intro hhalt
    exact False.elim (no_step_from_halted hstop hhalt hstep)
  exact normalizedDeciderToAcceptor_step_run hnot hstep

theorem normalizedDeciderToAcceptor_simulates_computes
    {M : TuringMachine symbol state} {zero one : symbol}
    (hstop : HaltingTransitionsDisabled M)
    {c d : Configuration symbol state}
    (hcomp : Computes M c d) :
    Computes (normalizedDeciderToAcceptor M zero one)
      (normalizedRunConfig c) (normalizedRunConfig d) := by
  induction hcomp with
  | refl c =>
      exact Computes.refl (normalizedRunConfig c)
  | step hstep _ ih =>
      exact Computes.step
        (normalizedDeciderToAcceptor_step_run_of_stopped hstop hstep) ih

def OneCellPreserved (one : symbol) (original current : Tape symbol) : Prop :=
  some one ∈ Tape.cells current -> some one ∈ Tape.cells original

def NormalizedDeciderToAcceptorInvariant
    (M : TuringMachine symbol state) (one : symbol) (input : Word symbol)
    (c : Configuration symbol (NormalizedDeciderToAcceptorState state)) : Prop :=
  match c.state with
  | NormalizedDeciderToAcceptorState.run s =>
      Computes M (M.initial input) { state := s, tape := c.tape }
  | NormalizedDeciderToAcceptorState.sweepRight =>
      exists halted : Configuration symbol state,
        Computes M (M.initial input) halted ∧
          Halted M halted ∧
          OneCellPreserved one halted.tape c.tape
  | NormalizedDeciderToAcceptorState.sweepLeft =>
      exists halted : Configuration symbol state,
        Computes M (M.initial input) halted ∧
          Halted M halted ∧
          OneCellPreserved one halted.tape c.tape
  | NormalizedDeciderToAcceptorState.accept =>
      exists halted : Configuration symbol state,
        Computes M (M.initial input) halted ∧
          Halted M halted ∧
          some one ∈ Tape.cells halted.tape

theorem normalizedDeciderToAcceptor_invariant_step
    {M : TuringMachine symbol state} {zero one : symbol} {input : Word symbol}
    (hzeroOne : zero ≠ one)
    {c d : Configuration symbol (NormalizedDeciderToAcceptorState state)}
    (hinv : NormalizedDeciderToAcceptorInvariant M one input c)
    (hstep : Step (normalizedDeciderToAcceptor M zero one) c d) :
    NormalizedDeciderToAcceptorInvariant M one input d := by
  cases hstep with
  | mk haction =>
      cases hcstate : c.state with
      | run s =>
          simp [NormalizedDeciderToAcceptorInvariant, hcstate] at hinv
          by_cases hhalt : s = M.halt
          · by_cases hone : Tape.read c.tape = some one
            · simp [normalizedDeciderToAcceptor,
                normalizedDeciderToAcceptorTransition, hcstate, hhalt,
                hone] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              cases hwrite
              cases hdir
              cases hnext
              simp [NormalizedDeciderToAcceptorInvariant]
              exact ⟨{ state := s, tape := c.tape }, hinv, hhalt,
                tape_read_mem_cells hone⟩
            · simp [normalizedDeciderToAcceptor,
                normalizedDeciderToAcceptorTransition, hcstate, hhalt,
                hone] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              cases hwrite
              cases hdir
              cases hnext
              simp [NormalizedDeciderToAcceptorInvariant]
              exists { state := s, tape := c.tape }
              constructor
              · exact hinv
              constructor
              · exact hhalt
              · intro hmem
                exact tape_mem_cells_of_write_marker_move_mem
                  hzeroOne Direction.right hmem
          · cases hM : M.transition s (Tape.read c.tape) with
            | none =>
                simp [normalizedDeciderToAcceptor,
                  normalizedDeciderToAcceptorTransition, hcstate, hhalt,
                  hM] at haction
            | some action =>
                rcases action with ⟨write, dir, nextState⟩
                simp [normalizedDeciderToAcceptor,
                  normalizedDeciderToAcceptorTransition, hcstate, hhalt,
                  hM] at haction
                rcases haction with ⟨hwrite, hdir, hnext⟩
                cases hwrite
                cases hdir
                cases hnext
                simp [NormalizedDeciderToAcceptorInvariant]
                exact computes_trans hinv
                  (Computes.step (Step.mk hM) (Computes.refl _))
      | sweepRight =>
          simp [NormalizedDeciderToAcceptorInvariant, hcstate] at hinv
          rcases hinv with ⟨halted, hcomp, hhalted, hpreserve⟩
          by_cases hone : Tape.read c.tape = some one
          · simp [normalizedDeciderToAcceptor,
              normalizedDeciderToAcceptorTransition, hcstate, hone] at haction
            rcases haction with ⟨hwrite, hdir, hnext⟩
            cases hwrite
            cases hdir
            cases hnext
            simp [NormalizedDeciderToAcceptorInvariant]
            exact ⟨halted, hcomp, hhalted,
              hpreserve (tape_read_mem_cells hone)⟩
          · cases hcell : Tape.read c.tape with
            | none =>
                simp [normalizedDeciderToAcceptor,
                  normalizedDeciderToAcceptorTransition, hcstate,
                  hcell] at haction
                rcases haction with ⟨hwrite, hdir, hnext⟩
                cases hwrite
                cases hdir
                cases hnext
                simp [NormalizedDeciderToAcceptorInvariant]
                exists halted
                constructor
                · exact hcomp
                constructor
                · exact hhalted
                · intro hmem
                  exact hpreserve
                    (tape_mem_cells_of_write_marker_move_mem
                      hzeroOne Direction.left hmem)
            | some a =>
                have hane : a ≠ one := by
                  intro ha
                  exact hone (by rw [hcell, ha])
                simp [normalizedDeciderToAcceptor,
                  normalizedDeciderToAcceptorTransition, hcstate,
                  hcell, hane] at haction
                rcases haction with ⟨hwrite, hdir, hnext⟩
                cases hwrite
                cases hdir
                cases hnext
                simp [NormalizedDeciderToAcceptorInvariant]
                exists halted
                constructor
                · exact hcomp
                constructor
                · exact hhalted
                · intro hmem
                  have hwriteRead :
                      Tape.write (some a) c.tape = c.tape := by
                    rw [← hcell]
                    exact tape_write_read_eq c.tape
                  have hbefore :=
                    tape_mem_cells_of_move_mem Direction.right hmem
                  rw [hwriteRead] at hbefore
                  exact hpreserve hbefore
      | sweepLeft =>
          simp [NormalizedDeciderToAcceptorInvariant, hcstate] at hinv
          rcases hinv with ⟨halted, hcomp, hhalted, hpreserve⟩
          by_cases hone : Tape.read c.tape = some one
          · simp [normalizedDeciderToAcceptor,
              normalizedDeciderToAcceptorTransition, hcstate, hone] at haction
            rcases haction with ⟨hwrite, hdir, hnext⟩
            cases hwrite
            cases hdir
            cases hnext
            simp [NormalizedDeciderToAcceptorInvariant]
            exact ⟨halted, hcomp, hhalted,
              hpreserve (tape_read_mem_cells hone)⟩
          · cases hcell : Tape.read c.tape with
            | none =>
                simp [normalizedDeciderToAcceptor,
                  normalizedDeciderToAcceptorTransition, hcstate,
                  hcell] at haction
                rcases haction with ⟨hwrite, hdir, hnext⟩
                cases hwrite
                cases hdir
                cases hnext
                simp [NormalizedDeciderToAcceptorInvariant]
                exists halted
                constructor
                · exact hcomp
                constructor
                · exact hhalted
                · intro hmem
                  exact hpreserve
                    (tape_mem_cells_of_write_marker_move_mem
                      hzeroOne Direction.right hmem)
            | some a =>
                have hane : a ≠ one := by
                  intro ha
                  exact hone (by rw [hcell, ha])
                simp [normalizedDeciderToAcceptor,
                  normalizedDeciderToAcceptorTransition, hcstate,
                  hcell, hane] at haction
                rcases haction with ⟨hwrite, hdir, hnext⟩
                cases hwrite
                cases hdir
                cases hnext
                simp [NormalizedDeciderToAcceptorInvariant]
                exists halted
                constructor
                · exact hcomp
                constructor
                · exact hhalted
                · intro hmem
                  have hwriteRead :
                      Tape.write (some a) c.tape = c.tape := by
                    rw [← hcell]
                    exact tape_write_read_eq c.tape
                  have hbefore :=
                    tape_mem_cells_of_move_mem Direction.left hmem
                  rw [hwriteRead] at hbefore
                  exact hpreserve hbefore
      | accept =>
          simp [normalizedDeciderToAcceptor,
            normalizedDeciderToAcceptorTransition, hcstate] at haction

theorem normalizedDeciderToAcceptor_invariant_of_computesIn
    {M : TuringMachine symbol state} {zero one : symbol} {input : Word symbol}
    (hzeroOne : zero ≠ one)
    {n : Nat}
    {c d : Configuration symbol (NormalizedDeciderToAcceptorState state)}
    (hcomp : ComputesIn (normalizedDeciderToAcceptor M zero one) n c d)
    (hinv : NormalizedDeciderToAcceptorInvariant M one input c) :
    NormalizedDeciderToAcceptorInvariant M one input d := by
  induction hcomp with
  | zero c =>
      exact hinv
  | succ hstep _ ih =>
      exact ih (normalizedDeciderToAcceptor_invariant_step
        hzeroOne hinv hstep)

theorem normalizedDeciderToAcceptor_initial_invariant
    (M : TuringMachine symbol state) (zero one : symbol) (input : Word symbol) :
    NormalizedDeciderToAcceptorInvariant M one input
      ((normalizedDeciderToAcceptor M zero one).initial input) := by
  simp [normalizedDeciderToAcceptor_initial,
    NormalizedDeciderToAcceptorInvariant, normalizedRunConfig]
  exact Computes.refl (M.initial input)

theorem normalizedDeciderToAcceptor_halts_sound_of_stopped_decider
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (hdec : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hhalt :
      HaltsOnInput (normalizedDeciderToAcceptor M zero one)
        (EncodeWord encodeInput w)) :
    w ∈ L := by
  rcases hhalt with ⟨final, hcomp, hfinal⟩
  rcases computes_to_computesIn hcomp with ⟨n, hcompIn⟩
  have hinv :=
    normalizedDeciderToAcceptor_invariant_of_computesIn
      (M := M) (zero := zero) (one := one)
      (input := EncodeWord encodeInput w)
      hzeroOne hcompIn
      (normalizedDeciderToAcceptor_initial_invariant
        M zero one (EncodeWord encodeInput w))
  cases hstate : final.state with
  | run s =>
      simp [Halted, normalizedDeciderToAcceptor, hstate] at hfinal
  | sweepRight =>
      simp [Halted, normalizedDeciderToAcceptor, hstate] at hfinal
  | sweepLeft =>
      simp [Halted, normalizedDeciderToAcceptor, hstate] at hfinal
  | accept =>
      simp [NormalizedDeciderToAcceptorInvariant, hstate] at hinv
      rcases hinv with ⟨halted, hcompM, hhalted, honeMem⟩
      apply Classical.byContradiction
      intro hnot
      rcases (hdec w).right hnot with ⟨rejectFinal, hcompReject,
        hhaltReject, hrejectOutput⟩
      have hEq :=
        computes_to_halted_unique hstop hcompM hhalted
          hcompReject hhaltReject
      have honeReject : some one ∈ Tape.cells rejectFinal.tape := by
        rw [← hEq]
        exact honeMem
      exact tape_no_one_of_normalized_zero hzeroOne hrejectOutput honeReject

theorem normalizedDeciderToAcceptor_sweepRight_accept_step
    (M : TuringMachine symbol state) (zero one : symbol)
    {T : Tape symbol}
    (hread : Tape.read T = some one) :
    Step (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepRight, tape := T }
      { state := NormalizedDeciderToAcceptorState.accept,
        tape := Tape.move Direction.right (Tape.write (some one) T) } := by
  exact Step.mk (by
    simp [normalizedDeciderToAcceptor,
      normalizedDeciderToAcceptorTransition, hread])

theorem normalizedDeciderToAcceptor_sweepLeft_accept_step
    (M : TuringMachine symbol state) (zero one : symbol)
    {T : Tape symbol}
    (hread : Tape.read T = some one) :
    Step (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepLeft, tape := T }
      { state := NormalizedDeciderToAcceptorState.accept,
        tape := Tape.move Direction.right (Tape.write (some one) T) } := by
  exact Step.mk (by
    simp [normalizedDeciderToAcceptor,
      normalizedDeciderToAcceptorTransition, hread])

theorem normalizedDeciderToAcceptor_sweepRight_blank_step
    (M : TuringMachine symbol state) (zero one : symbol)
    {T : Tape symbol}
    (hread : Tape.read T = none) :
    Step (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepRight, tape := T }
      { state := NormalizedDeciderToAcceptorState.sweepLeft,
        tape := Tape.move Direction.left (Tape.write (some zero) T) } := by
  have hnot : Tape.read T ≠ some one := by
    rw [hread]
    intro hbad
    cases hbad
  exact Step.mk (by
    simp [normalizedDeciderToAcceptor,
      normalizedDeciderToAcceptorTransition, hread])

theorem normalizedDeciderToAcceptor_sweepLeft_blank_step
    (M : TuringMachine symbol state) (zero one : symbol)
    {T : Tape symbol}
    (hread : Tape.read T = none) :
    Step (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepLeft, tape := T }
      { state := NormalizedDeciderToAcceptorState.sweepRight,
        tape := Tape.move Direction.right (Tape.write (some zero) T) } := by
  have hnot : Tape.read T ≠ some one := by
    rw [hread]
    intro hbad
    cases hbad
  exact Step.mk (by
    simp [normalizedDeciderToAcceptor,
      normalizedDeciderToAcceptorTransition, hread])

theorem normalizedDeciderToAcceptor_sweepRight_symbol_step
    (M : TuringMachine symbol state) (zero one a : symbol)
    {T : Tape symbol}
    (hread : Tape.read T = some a) (ha : a ≠ one) :
    Step (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepRight, tape := T }
      { state := NormalizedDeciderToAcceptorState.sweepRight,
        tape := Tape.move Direction.right (Tape.write (some a) T) } := by
  have hnot : Tape.read T ≠ some one := by
    intro hbad
    rw [hread] at hbad
    exact ha (by simpa using hbad)
  exact Step.mk (by
    simp [normalizedDeciderToAcceptor,
      normalizedDeciderToAcceptorTransition, hread, ha])

theorem normalizedDeciderToAcceptor_sweepLeft_symbol_step
    (M : TuringMachine symbol state) (zero one a : symbol)
    {T : Tape symbol}
    (hread : Tape.read T = some a) (ha : a ≠ one) :
    Step (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepLeft, tape := T }
      { state := NormalizedDeciderToAcceptorState.sweepLeft,
        tape := Tape.move Direction.left (Tape.write (some a) T) } := by
  have hnot : Tape.read T ≠ some one := by
    intro hbad
    rw [hread] at hbad
    exact ha (by simpa using hbad)
  exact Step.mk (by
    simp [normalizedDeciderToAcceptor,
      normalizedDeciderToAcceptorTransition, hread, ha])

def NormalizedOutputScannerComplete
    (M : TuringMachine symbol state) (zero one : symbol) : Prop :=
  forall final : Configuration symbol state,
    Halted M final ->
      Tape.normalizedOutput final.tape = [one] ->
        HaltsFrom (normalizedDeciderToAcceptor M zero one)
          (normalizedRunConfig final)

theorem normalizedDeciderToAcceptor_halts_of_mem
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : HaltingTransitionsDisabled M)
    (hscanner : NormalizedOutputScannerComplete M zero one)
    (hdec : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hw : w ∈ L) :
    HaltsOnInput (normalizedDeciderToAcceptor M zero one)
      (EncodeWord encodeInput w) := by
  rcases (hdec w).left hw with ⟨final, hcomp, hhalt, hout⟩
  have hsim := normalizedDeciderToAcceptor_simulates_computes
    (M := M) (zero := zero) (one := one) hstop hcomp
  exact halts_from_of_computes_prefix hsim (hscanner final hhalt hout)

theorem normalizedDeciderToAcceptor_acceptsLanguage_of_stopped_decider
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hscanner : NormalizedOutputScannerComplete M zero one)
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    AcceptsLanguage (normalizedDeciderToAcceptor M zero one) encodeInput L := by
  intro w
  constructor
  · exact normalizedDeciderToAcceptor_halts_sound_of_stopped_decider
      h.left h.right.left h.right.right
  · exact normalizedDeciderToAcceptor_halts_of_mem
      h.left hscanner h.right.right

def runConfig (c : Configuration symbol state) :
    Configuration symbol (DeciderToAcceptorState state) where
  state := DeciderToAcceptorState.run c.state
  tape := c.tape

noncomputable def deciderToAcceptorTransition
    (M : TuringMachine symbol state) (one : symbol) :
    DeciderToAcceptorState state -> Option symbol ->
      Option (Option symbol × Direction × DeciderToAcceptorState state)
  | DeciderToAcceptorState.run s, cell =>
      if s = M.halt then
        if cell = some one then
          some (cell, Direction.right, DeciderToAcceptorState.accept)
        else
          some (cell, Direction.right, DeciderToAcceptorState.loop)
      else
        match M.transition s cell with
        | some (write, dir, nextState) =>
            some (write, dir, DeciderToAcceptorState.run nextState)
        | none => none
  | DeciderToAcceptorState.accept, _ => none
  | DeciderToAcceptorState.loop, cell =>
      some (cell, Direction.right, DeciderToAcceptorState.loop)

noncomputable def deciderToAcceptor
    (M : TuringMachine symbol state) (one : symbol) :
    TuringMachine symbol (DeciderToAcceptorState state) where
  start := DeciderToAcceptorState.run M.start
  halt := DeciderToAcceptorState.accept
  transition := deciderToAcceptorTransition M one
  statesFinite := DeciderToAcceptorState.finite M.statesFinite

@[simp] theorem deciderToAcceptor_initial
    (M : TuringMachine symbol state) (one : symbol) (w : Word symbol) :
    (deciderToAcceptor M one).initial w =
      runConfig (M.initial w) :=
  rfl

theorem deciderToAcceptor_step_run
    {M : TuringMachine symbol state} {one : symbol}
    {c d : Configuration symbol state}
    (hnot : c.state ≠ M.halt)
    (hstep : Step M c d) :
    Step (deciderToAcceptor M one) (runConfig c) (runConfig d) := by
  cases hstep with
  | mk haction =>
      exact Step.mk (by
        simp [runConfig, deciderToAcceptor, deciderToAcceptorTransition,
          hnot, haction])

theorem deciderToAcceptor_step_run_of_stopped
    {M : TuringMachine symbol state} {one : symbol}
    (hstop : HaltingTransitionsDisabled M)
    {c d : Configuration symbol state}
    (hstep : Step M c d) :
    Step (deciderToAcceptor M one) (runConfig c) (runConfig d) := by
  have hnot : c.state ≠ M.halt := by
    intro hhalt
    exact False.elim (no_step_from_halted hstop hhalt hstep)
  exact deciderToAcceptor_step_run hnot hstep

theorem deciderToAcceptor_simulates_computes
    {M : TuringMachine symbol state} {one : symbol}
    (hstop : HaltingTransitionsDisabled M)
    {c d : Configuration symbol state}
    (hcomp : Computes M c d) :
    Computes (deciderToAcceptor M one) (runConfig c) (runConfig d) := by
  induction hcomp with
  | refl c =>
      exact Computes.refl (runConfig c)
  | step hstep _ ih =>
      exact Computes.step (deciderToAcceptor_step_run_of_stopped hstop hstep) ih

def DeciderToAcceptorInvariant
    (M : TuringMachine symbol state) (one : symbol) (input : Word symbol)
    (c : Configuration symbol (DeciderToAcceptorState state)) : Prop :=
  match c.state with
  | DeciderToAcceptorState.run s =>
      Computes M (M.initial input) { state := s, tape := c.tape }
  | DeciderToAcceptorState.accept =>
      exists halted : Configuration symbol state,
        Computes M (M.initial input) halted ∧
          Halted M halted ∧ Tape.read halted.tape = some one
  | DeciderToAcceptorState.loop => True

theorem deciderToAcceptor_invariant_step
    {M : TuringMachine symbol state} {one : symbol} {input : Word symbol}
    {c d : Configuration symbol (DeciderToAcceptorState state)}
    (hinv : DeciderToAcceptorInvariant M one input c)
    (hstep : Step (deciderToAcceptor M one) c d) :
    DeciderToAcceptorInvariant M one input d := by
  cases hstep with
  | mk haction =>
      cases hcstate : c.state with
      | run s =>
          simp [DeciderToAcceptorInvariant, hcstate] at hinv
          by_cases hhalt : s = M.halt
          · by_cases hone : Tape.read c.tape = some one
            · simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate,
                hhalt, hone] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              cases hwrite
              cases hdir
              cases hnext
              simp [DeciderToAcceptorInvariant]
              exact ⟨{ state := s, tape := c.tape }, hinv, hhalt, hone⟩
            · simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate,
                hhalt, hone] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              cases hwrite
              cases hdir
              cases hnext
              simp [DeciderToAcceptorInvariant]
          · cases hM : M.transition s (Tape.read c.tape) with
            | none =>
                simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate,
                  hhalt, hM] at haction
            | some action =>
                rcases action with ⟨write, dir, nextState⟩
                simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate,
                  hhalt, hM] at haction
                rcases haction with ⟨hwrite, hdir, hnext⟩
                cases hwrite
                cases hdir
                cases hnext
                simp [DeciderToAcceptorInvariant]
                exact computes_trans hinv
                  (Computes.step (Step.mk hM) (Computes.refl _))
      | accept =>
          simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate] at haction
      | loop =>
          simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate] at haction
          rcases haction with ⟨hwrite, hdir, hnext⟩
          cases hwrite
          cases hdir
          cases hnext
          simp [DeciderToAcceptorInvariant]

theorem deciderToAcceptor_invariant_of_computesIn
    {M : TuringMachine symbol state} {one : symbol} {input : Word symbol}
    {n : Nat}
    {c d : Configuration symbol (DeciderToAcceptorState state)}
    (hcomp : ComputesIn (deciderToAcceptor M one) n c d)
    (hinv : DeciderToAcceptorInvariant M one input c) :
    DeciderToAcceptorInvariant M one input d := by
  induction hcomp with
  | zero c =>
      exact hinv
  | succ hstep _ ih =>
      exact ih (deciderToAcceptor_invariant_step hinv hstep)

theorem deciderToAcceptor_initial_invariant
    (M : TuringMachine symbol state) (one : symbol) (input : Word symbol) :
    DeciderToAcceptorInvariant M one input
      ((deciderToAcceptor M one).initial input) := by
  simp [deciderToAcceptor_initial, DeciderToAcceptorInvariant, runConfig]
  exact Computes.refl (M.initial input)

theorem deciderToAcceptor_halts_of_mem
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : HaltingTransitionsDisabled M)
    (hdec : DecidesLanguageByHeadOutput M encodeInput zero one L)
    {w : Word input}
    (hw : w ∈ L) :
    HaltsOnInput (deciderToAcceptor M one) (EncodeWord encodeInput w) := by
  rcases (hdec w).left hw with ⟨final, hcomp, hhalt, hread⟩
  have hsim := deciderToAcceptor_simulates_computes
    (M := M) (one := one) hstop hcomp
  have hhaltState : final.state = M.halt := hhalt
  let acceptConfig :
      Configuration symbol (DeciderToAcceptorState state) :=
    { state := DeciderToAcceptorState.accept,
      tape := Tape.move Direction.right (Tape.write (some one) final.tape) }
  have hstep :
      Step (deciderToAcceptor M one) (runConfig final) acceptConfig := by
    exact Step.mk (by
      simp [runConfig, deciderToAcceptor,
        deciderToAcceptorTransition, hhaltState, hread])
  exact ⟨acceptConfig,
    computes_trans hsim (Computes.step hstep (Computes.refl acceptConfig)),
    rfl⟩

theorem deciderToAcceptor_halts_sound_of_stopped_decider
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (hdec : DecidesLanguageByHeadOutput M encodeInput zero one L)
    {w : Word input}
    (hhalt :
      HaltsOnInput (deciderToAcceptor M one) (EncodeWord encodeInput w)) :
    w ∈ L := by
  rcases hhalt with ⟨final, hcomp, hfinal⟩
  rcases computes_to_computesIn hcomp with ⟨n, hcompIn⟩
  have hinv :=
    deciderToAcceptor_invariant_of_computesIn
      (M := M) (one := one) (input := EncodeWord encodeInput w)
      hcompIn
      (deciderToAcceptor_initial_invariant
        M one (EncodeWord encodeInput w))
  cases hstate : final.state with
  | run s =>
      simp [Halted, deciderToAcceptor, hstate] at hfinal
  | accept =>
      simp [DeciderToAcceptorInvariant, hstate] at hinv
      rcases hinv with ⟨halted, hcompM, hhalted, hreadOne⟩
      apply Classical.byContradiction
      intro hnot
      rcases (hdec w).right hnot with ⟨rejectFinal, hcompReject,
        hhaltReject, hreadReject⟩
      have hEq :=
        computes_to_halted_unique hstop hcompM hhalted
          hcompReject hhaltReject
      have hreadZero : Tape.read halted.tape = some zero := by
        rw [hEq]
        exact hreadReject
      rw [hreadOne] at hreadZero
      have honeZero : one = zero := by
        simpa using hreadZero
      exact hzeroOne honeZero.symm
  | loop =>
      simp [Halted, deciderToAcceptor, hstate] at hfinal

theorem deciderToAcceptor_acceptsLanguage_of_stopped_decider
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (hdec : DecidesLanguageByHeadOutput M encodeInput zero one L) :
    AcceptsLanguage (deciderToAcceptor M one) encodeInput L := by
  intro w
  constructor
  · exact deciderToAcceptor_halts_sound_of_stopped_decider
      hstop hzeroOne hdec
  · exact deciderToAcceptor_halts_of_mem hstop hdec

theorem stoppedDecidesLanguageByHeadOutput_to_turingAcceptable
    {symbol state input : Type}
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguageByHeadOutput M encodeInput zero one L) :
    TuringAcceptable L := by
  exists symbol
  exists DeciderToAcceptorState state
  exists deciderToAcceptor M one
  exists encodeInput
  exact deciderToAcceptor_acceptsLanguage_of_stopped_decider
    h.left h.right.left h.right.right

theorem stoppedTuringDecidableByHeadOutput_to_turingAcceptable
    {input : Type} {L : Language input}
    (h : StoppedTuringDecidableByHeadOutput L) :
    TuringAcceptable L := by
  rcases h with ⟨symbol, state, M, encodeInput, zero, one, hdec⟩
  exists symbol
  exists DeciderToAcceptorState state
  exists deciderToAcceptor M one
  exists encodeInput
  exact deciderToAcceptor_acceptsLanguage_of_stopped_decider
    hdec.left hdec.right.left hdec.right.right

end TuringMachine

end Computability
end FoC
