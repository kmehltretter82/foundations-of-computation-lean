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

/-!
**Scanner tape shapes.**  The scanner proof uses explicit finite tape windows:
blocks of marker cells, blocks of blanks, and a distinguished accepting cell.
The right-target and left-target shapes describe the moment when the scanner is
looking at the next unvisited cell on the corresponding side.
-/

def scannerZeroBlock (zero : symbol) (n : Nat) : List (Option symbol) :=
  List.replicate n (some zero)

def scannerBlankBlock (n : Nat) : List (Option symbol) :=
  List.replicate n none

theorem list_replicate_append_self
    (a : α) (n : Nat) (rest : List α) :
    List.replicate n a ++ a :: rest =
      List.replicate (n + 1) a ++ rest := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        a :: (List.replicate n a ++ a :: rest) =
          a :: (List.replicate (n + 1) a ++ rest)
      rw [ih]

theorem scannerZeroBlock_append_marker
    (zero : symbol) (n : Nat) (rest : List (Option symbol)) :
    scannerZeroBlock zero n ++ some zero :: rest =
      scannerZeroBlock zero (n + 1) ++ rest := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        some zero :: (scannerZeroBlock zero n ++ some zero :: rest) =
          some zero :: (scannerZeroBlock zero (n + 1) ++ rest)
      rw [ih]

def scannerRightTargetTape
    (zero one : symbol) (markedLeft blanksLeft blanksRight : Nat)
    (tail : List (Option symbol)) : Tape symbol :=
  match blanksRight with
  | 0 =>
      { left := scannerZeroBlock zero markedLeft ++
          scannerBlankBlock blanksLeft,
        head := some one,
        right := tail }
  | n + 1 =>
      { left := scannerZeroBlock zero markedLeft ++
          scannerBlankBlock blanksLeft,
        head := none,
        right := scannerBlankBlock n ++ some one :: tail }

def scannerLeftTargetTape
    (zero one : symbol) (markedRight blanksRight blanksLeft : Nat)
    (tail : List (Option symbol)) : Tape symbol :=
  match blanksLeft with
  | 0 =>
      { left := tail,
        head := some one,
        right := scannerZeroBlock zero markedRight ++
          scannerBlankBlock blanksRight }
  | n + 1 =>
      { left := scannerBlankBlock n ++ some one :: tail,
        head := none,
        right := scannerZeroBlock zero markedRight ++
          scannerBlankBlock blanksRight }

def scannerRightCrossTape
    (zero : symbol) (crossed : Nat) (left rest : List (Option symbol)) :
    Tape symbol :=
  match rest with
  | [] =>
      { left := scannerZeroBlock zero crossed ++ left,
        head := none,
        right := [] }
  | cell :: cells =>
      { left := scannerZeroBlock zero crossed ++ left,
        head := cell,
        right := cells }

def scannerLeftCrossTape
    (zero : symbol) (crossed : Nat) (right rest : List (Option symbol)) :
    Tape symbol :=
  match rest with
  | [] =>
      { left := [],
        head := none,
        right := scannerZeroBlock zero crossed ++ right }
  | cell :: cells =>
      { left := cells,
        head := cell,
        right := scannerZeroBlock zero crossed ++ right }

/-!
**Crossing marker blocks.**  Once a boundary blank has been marked, the scanner
travels back across a finite block of markers. These two lemmas package those
straight-line runs so the expansion cycles below can talk about whole sweeps
instead of individual marker steps.
-/

theorem normalizedDeciderToAcceptor_sweepRight_cross_zeroBlock
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one) (zeros crossed : Nat)
    (left rest : List (Option symbol)) :
    Computes (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepRight,
        tape := scannerRightCrossTape zero crossed left
          (scannerZeroBlock zero zeros ++ rest) }
      { state := NormalizedDeciderToAcceptorState.sweepRight,
        tape := scannerRightCrossTape zero (crossed + zeros) left rest } := by
  induction zeros generalizing crossed with
  | zero =>
      exact Computes.refl _
  | succ zeros ih =>
      have hstep :
          Step (normalizedDeciderToAcceptor M zero one)
            { state := NormalizedDeciderToAcceptorState.sweepRight,
              tape := scannerRightCrossTape zero crossed left
                (scannerZeroBlock zero (Nat.succ zeros) ++ rest) }
            { state := NormalizedDeciderToAcceptorState.sweepRight,
              tape := scannerRightCrossTape zero (crossed + 1) left
                (scannerZeroBlock zero zeros ++ rest) } := by
        exact normalizedDeciderToAcceptor_sweepRight_symbol_step
          M zero one zero
          (by simp [scannerZeroBlock, scannerRightCrossTape,
            Tape.read, List.replicate_succ])
          hzeroOne
      have hrest := ih (crossed + 1)
      exact Computes.step hstep (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hrest)

theorem normalizedDeciderToAcceptor_sweepLeft_cross_zeroBlock
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one) (zeros crossed : Nat)
    (right rest : List (Option symbol)) :
    Computes (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepLeft,
        tape := scannerLeftCrossTape zero crossed right
          (scannerZeroBlock zero zeros ++ rest) }
      { state := NormalizedDeciderToAcceptorState.sweepLeft,
        tape := scannerLeftCrossTape zero (crossed + zeros) right rest } := by
  induction zeros generalizing crossed with
  | zero =>
      exact Computes.refl _
  | succ zeros ih =>
      have hstep :
          Step (normalizedDeciderToAcceptor M zero one)
            { state := NormalizedDeciderToAcceptorState.sweepLeft,
              tape := scannerLeftCrossTape zero crossed right
                (scannerZeroBlock zero (Nat.succ zeros) ++ rest) }
            { state := NormalizedDeciderToAcceptorState.sweepLeft,
              tape := scannerLeftCrossTape zero (crossed + 1) right
                (scannerZeroBlock zero zeros ++ rest) } := by
        exact normalizedDeciderToAcceptor_sweepLeft_symbol_step
          M zero one zero
          (by simp [scannerZeroBlock, scannerLeftCrossTape,
            Tape.read, List.replicate_succ])
          hzeroOne
      have hrest := ih (crossed + 1)
      exact Computes.step hstep (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hrest)

/-!
**Expansion cycles.**  If the scanner reaches a blank before seeing the
accepting symbol, it marks that blank, sweeps to the opposite boundary, marks
one blank there, and returns to the next unvisited cell. Each cycle strictly
reduces the number of blanks between the frontier and the accepting cell.
-/

theorem normalizedDeciderToAcceptor_sweepRight_target_blank_cycle
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one)
    (markedLeft blanksLeft blanksRight : Nat)
    (tail : List (Option symbol)) :
    Computes (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepRight,
        tape := scannerRightTargetTape zero one markedLeft blanksLeft
          (blanksRight + 1) tail }
      { state := NormalizedDeciderToAcceptorState.sweepRight,
        tape := scannerRightTargetTape zero one (markedLeft + 2)
          blanksLeft.pred blanksRight tail } := by
  let rightCtx :=
    some zero :: scannerBlankBlock blanksRight ++ some one :: tail
  let leftRest := scannerZeroBlock zero markedLeft ++
    scannerBlankBlock blanksLeft
  let afterRightMark : Tape symbol :=
    scannerLeftCrossTape zero 0 rightCtx leftRest
  have hstepRight :
      Step (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepRight,
          tape := scannerRightTargetTape zero one markedLeft blanksLeft
            (blanksRight + 1) tail }
        { state := NormalizedDeciderToAcceptorState.sweepLeft,
          tape := afterRightMark } := by
    simpa [afterRightMark, rightCtx, leftRest, scannerRightTargetTape,
      scannerLeftCrossTape, Tape.read, Tape.move, Tape.moveLeft,
      Tape.write, scannerBlankBlock, scannerZeroBlock,
      List.replicate_succ, List.append_assoc]
      using
        normalizedDeciderToAcceptor_sweepRight_blank_step
          M zero one
          (T := scannerRightTargetTape zero one markedLeft blanksLeft
            (blanksRight + 1) tail)
          (by simp [scannerRightTargetTape, Tape.read])
  let leftBoundary : Tape symbol :=
    scannerLeftCrossTape zero (0 + markedLeft) rightCtx
      (scannerBlankBlock blanksLeft)
  have hcrossLeft :
      Computes (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepLeft,
          tape := afterRightMark }
        { state := NormalizedDeciderToAcceptorState.sweepLeft,
          tape := leftBoundary } := by
    simpa [afterRightMark, leftBoundary, leftRest, rightCtx]
      using
        normalizedDeciderToAcceptor_sweepLeft_cross_zeroBlock
          M hzeroOne markedLeft 0 rightCtx
          (scannerBlankBlock blanksLeft)
  let afterLeftMark : Tape symbol :=
    scannerRightCrossTape zero 1 (scannerBlankBlock blanksLeft.pred)
      (scannerZeroBlock zero (markedLeft + 1) ++
        scannerBlankBlock blanksRight ++ some one :: tail)
  have hstepLeft :
      Step (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepLeft,
          tape := leftBoundary }
        { state := NormalizedDeciderToAcceptorState.sweepRight,
          tape := afterLeftMark } := by
    cases blanksLeft with
    | zero =>
        simpa [leftBoundary, afterLeftMark, rightCtx, scannerLeftCrossTape,
          scannerRightCrossTape, scannerBlankBlock, scannerZeroBlock,
          scannerZeroBlock_append_marker, list_replicate_append_self,
          Tape.read, Tape.move, Tape.moveRight, Tape.write,
          List.append_assoc]
          using
            normalizedDeciderToAcceptor_sweepLeft_blank_step
              M zero one
              (T := leftBoundary)
              (by simp [leftBoundary, scannerLeftCrossTape, Tape.read,
                scannerBlankBlock])
    | succ blanksLeft =>
        simpa [leftBoundary, afterLeftMark, rightCtx, scannerLeftCrossTape,
          scannerRightCrossTape, scannerBlankBlock, scannerZeroBlock,
          scannerZeroBlock_append_marker, list_replicate_append_self,
          Tape.read, Tape.move, Tape.moveRight, Tape.write,
          List.replicate_succ, List.append_assoc]
          using
            normalizedDeciderToAcceptor_sweepLeft_blank_step
              M zero one
              (T := leftBoundary)
              (by simp [leftBoundary, scannerLeftCrossTape, Tape.read,
                scannerBlankBlock, List.replicate_succ])
  have hcrossRight :
      Computes (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepRight,
          tape := afterLeftMark }
        { state := NormalizedDeciderToAcceptorState.sweepRight,
          tape := scannerRightTargetTape zero one (markedLeft + 2)
            blanksLeft.pred blanksRight tail } := by
    have h :=
      normalizedDeciderToAcceptor_sweepRight_cross_zeroBlock
        M hzeroOne (markedLeft + 1) 1
        (scannerBlankBlock blanksLeft.pred)
        (scannerBlankBlock blanksRight ++ some one :: tail)
    cases blanksRight with
    | zero =>
        simpa [afterLeftMark, rightCtx, scannerRightTargetTape,
          scannerRightCrossTape, scannerBlankBlock, scannerZeroBlock,
          List.replicate_succ, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using h
    | succ blanksRight =>
        simpa [afterLeftMark, rightCtx, scannerRightTargetTape,
          scannerRightCrossTape, scannerBlankBlock, scannerZeroBlock,
          List.replicate_succ, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using h
  exact Computes.step hstepRight
    (computes_trans hcrossLeft
      (Computes.step hstepLeft hcrossRight))

theorem normalizedDeciderToAcceptor_sweepLeft_target_blank_cycle
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one)
    (markedRight blanksRight blanksLeft : Nat)
    (tail : List (Option symbol)) :
    Computes (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepLeft,
        tape := scannerLeftTargetTape zero one markedRight blanksRight
          (blanksLeft + 1) tail }
      { state := NormalizedDeciderToAcceptorState.sweepLeft,
        tape := scannerLeftTargetTape zero one (markedRight + 2)
          blanksRight.pred blanksLeft tail } := by
  let leftCtx :=
    some zero :: scannerBlankBlock blanksLeft ++ some one :: tail
  let rightRest := scannerZeroBlock zero markedRight ++
    scannerBlankBlock blanksRight
  let afterLeftMark : Tape symbol :=
    scannerRightCrossTape zero 0 leftCtx rightRest
  have hstepLeft :
      Step (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepLeft,
          tape := scannerLeftTargetTape zero one markedRight blanksRight
            (blanksLeft + 1) tail }
        { state := NormalizedDeciderToAcceptorState.sweepRight,
          tape := afterLeftMark } := by
    simpa [afterLeftMark, leftCtx, rightRest, scannerLeftTargetTape,
      scannerRightCrossTape, Tape.read, Tape.move, Tape.moveRight,
      Tape.write, scannerBlankBlock, scannerZeroBlock,
      List.replicate_succ, List.append_assoc]
      using
        normalizedDeciderToAcceptor_sweepLeft_blank_step
          M zero one
          (T := scannerLeftTargetTape zero one markedRight blanksRight
            (blanksLeft + 1) tail)
          (by simp [scannerLeftTargetTape, Tape.read])
  let rightBoundary : Tape symbol :=
    scannerRightCrossTape zero (0 + markedRight) leftCtx
      (scannerBlankBlock blanksRight)
  have hcrossRight :
      Computes (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepRight,
          tape := afterLeftMark }
        { state := NormalizedDeciderToAcceptorState.sweepRight,
          tape := rightBoundary } := by
    simpa [afterLeftMark, rightBoundary, rightRest, leftCtx]
      using
        normalizedDeciderToAcceptor_sweepRight_cross_zeroBlock
          M hzeroOne markedRight 0 leftCtx
          (scannerBlankBlock blanksRight)
  let afterRightMark : Tape symbol :=
    scannerLeftCrossTape zero 1 (scannerBlankBlock blanksRight.pred)
      (scannerZeroBlock zero (markedRight + 1) ++
        scannerBlankBlock blanksLeft ++ some one :: tail)
  have hstepRight :
      Step (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepRight,
          tape := rightBoundary }
        { state := NormalizedDeciderToAcceptorState.sweepLeft,
          tape := afterRightMark } := by
    cases blanksRight with
    | zero =>
        simpa [rightBoundary, afterRightMark, leftCtx,
          scannerRightCrossTape, scannerLeftCrossTape, scannerBlankBlock,
          scannerZeroBlock, scannerZeroBlock_append_marker,
          list_replicate_append_self,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write,
          List.append_assoc]
          using
            normalizedDeciderToAcceptor_sweepRight_blank_step
              M zero one
              (T := rightBoundary)
              (by simp [rightBoundary, scannerRightCrossTape, Tape.read,
                scannerBlankBlock])
    | succ blanksRight =>
        simpa [rightBoundary, afterRightMark, leftCtx,
          scannerRightCrossTape, scannerLeftCrossTape, scannerBlankBlock,
          scannerZeroBlock, scannerZeroBlock_append_marker,
          list_replicate_append_self,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write,
          List.replicate_succ, List.append_assoc]
          using
            normalizedDeciderToAcceptor_sweepRight_blank_step
              M zero one
              (T := rightBoundary)
              (by simp [rightBoundary, scannerRightCrossTape, Tape.read,
                scannerBlankBlock, List.replicate_succ])
  have hcrossLeft :
      Computes (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepLeft,
          tape := afterRightMark }
        { state := NormalizedDeciderToAcceptorState.sweepLeft,
          tape := scannerLeftTargetTape zero one (markedRight + 2)
            blanksRight.pred blanksLeft tail } := by
    have h :=
      normalizedDeciderToAcceptor_sweepLeft_cross_zeroBlock
        M hzeroOne (markedRight + 1) 1
        (scannerBlankBlock blanksRight.pred)
        (scannerBlankBlock blanksLeft ++ some one :: tail)
    cases blanksLeft with
    | zero =>
        simpa [afterRightMark, leftCtx, scannerLeftTargetTape,
          scannerLeftCrossTape, scannerBlankBlock, scannerZeroBlock,
          List.replicate_succ, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using h
    | succ blanksLeft =>
        simpa [afterRightMark, leftCtx, scannerLeftTargetTape,
          scannerLeftCrossTape, scannerBlankBlock, scannerZeroBlock,
          List.replicate_succ, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using h
  exact Computes.step hstepLeft
    (computes_trans hcrossRight
      (Computes.step hstepRight hcrossLeft))

/-!
**Finite scanner termination.**  The target-side proofs are ordinary induction
on the number of blanks between the current frontier and the accepting cell.
At distance zero the next step accepts; otherwise one expansion cycle decreases
the distance.
-/

theorem normalizedDeciderToAcceptor_sweepRight_target_zero_halts
    (M : TuringMachine symbol state) (zero one : symbol)
    (markedLeft blanksLeft : Nat) (tail : List (Option symbol)) :
    HaltsFrom (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepRight,
        tape := scannerRightTargetTape zero one markedLeft blanksLeft 0 tail } := by
  let acceptConfig :
      Configuration symbol (NormalizedDeciderToAcceptorState state) :=
    { state := NormalizedDeciderToAcceptorState.accept,
      tape := Tape.move Direction.right
        (Tape.write (some one)
          (scannerRightTargetTape zero one markedLeft blanksLeft 0 tail)) }
  have hstep :
      Step (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepRight,
          tape := scannerRightTargetTape zero one markedLeft blanksLeft 0 tail }
        acceptConfig := by
    exact normalizedDeciderToAcceptor_sweepRight_accept_step
      M zero one (by simp [scannerRightTargetTape, Tape.read])
  exact ⟨acceptConfig,
    Computes.step hstep (Computes.refl acceptConfig), rfl⟩

theorem normalizedDeciderToAcceptor_sweepLeft_target_zero_halts
    (M : TuringMachine symbol state) (zero one : symbol)
    (markedRight blanksRight : Nat) (tail : List (Option symbol)) :
    HaltsFrom (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepLeft,
        tape := scannerLeftTargetTape zero one markedRight blanksRight 0 tail } := by
  let acceptConfig :
      Configuration symbol (NormalizedDeciderToAcceptorState state) :=
    { state := NormalizedDeciderToAcceptorState.accept,
      tape := Tape.move Direction.right
        (Tape.write (some one)
          (scannerLeftTargetTape zero one markedRight blanksRight 0 tail)) }
  have hstep :
      Step (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepLeft,
          tape := scannerLeftTargetTape zero one markedRight blanksRight 0 tail }
        acceptConfig := by
    exact normalizedDeciderToAcceptor_sweepLeft_accept_step
      M zero one (by simp [scannerLeftTargetTape, Tape.read])
  exact ⟨acceptConfig,
    Computes.step hstep (Computes.refl acceptConfig), rfl⟩

theorem normalizedDeciderToAcceptor_sweepRight_target_halts
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one)
    (blanksRight markedLeft blanksLeft : Nat)
    (tail : List (Option symbol)) :
    HaltsFrom (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepRight,
        tape := scannerRightTargetTape zero one markedLeft blanksLeft
          blanksRight tail } := by
  induction blanksRight generalizing markedLeft blanksLeft with
  | zero =>
      exact normalizedDeciderToAcceptor_sweepRight_target_zero_halts
        M zero one markedLeft blanksLeft tail
  | succ blanksRight ih =>
      exact halts_from_of_computes_prefix
        (normalizedDeciderToAcceptor_sweepRight_target_blank_cycle
          M hzeroOne markedLeft blanksLeft blanksRight tail)
        (ih (markedLeft + 2) blanksLeft.pred)

theorem normalizedDeciderToAcceptor_sweepLeft_target_halts
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one)
    (blanksLeft markedRight blanksRight : Nat)
    (tail : List (Option symbol)) :
    HaltsFrom (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepLeft,
        tape := scannerLeftTargetTape zero one markedRight blanksRight
          blanksLeft tail } := by
  induction blanksLeft generalizing markedRight blanksRight with
  | zero =>
      exact normalizedDeciderToAcceptor_sweepLeft_target_zero_halts
        M zero one markedRight blanksRight tail
  | succ blanksLeft ih =>
      exact halts_from_of_computes_prefix
        (normalizedDeciderToAcceptor_sweepLeft_target_blank_cycle
          M hzeroOne markedRight blanksRight blanksLeft tail)
        (ih (markedRight + 2) blanksRight.pred)

/-!
**Normalized output to scanner starts.**  A halted tape with normalized output
{lit}`[one]` has exactly one nonblank contribution to the output list. The
following list lemmas split such a tape into the head, right-side, and left-side
scanner-start cases used by {lit}`normalizedOutputScannerComplete`.
-/

theorem filterMap_singleton_decompose
    {cells : List (Option symbol)} {one : symbol}
    (h : cells.filterMap (fun cell => cell) = [one]) :
    exists blanks : Nat, exists tail : List (Option symbol),
      cells = scannerBlankBlock blanks ++ some one :: tail := by
  induction cells with
  | nil =>
      simp at h
  | cons cell rest ih =>
      cases cell with
      | none =>
          simp at h
          rcases ih h with ⟨blanks, tail, htail⟩
          exists blanks + 1
          exists tail
          simp [scannerBlankBlock, List.replicate_succ, htail]
      | some a =>
          simp at h
          exists 0
          exists rest
          simp [scannerBlankBlock, h.left]

theorem filterMap_nil_eq_blankBlock
    {cells : List (Option symbol)}
    (h : cells.filterMap (fun cell => cell) = ([] : List symbol)) :
    cells = scannerBlankBlock cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          have hrest :
              rest.filterMap (fun cell => cell) = ([] : List symbol) := by
            simpa using h
          rw [ih hrest]
          simp [scannerBlankBlock, List.replicate_succ]
      | some a =>
          simp at h

theorem filterMap_nil_decompose
    {cells : List (Option symbol)}
    (h : cells.filterMap (fun cell => cell) = ([] : List symbol)) :
    exists blanks : Nat, cells = scannerBlankBlock blanks := by
  exact ⟨cells.length, filterMap_nil_eq_blankBlock h⟩

theorem filterMap_of_reverse_nil
    {cells : List (Option symbol)}
    (h : cells.reverse.filterMap (fun cell => cell) = ([] : List symbol)) :
    cells.filterMap (fun cell => cell) = ([] : List symbol) := by
  have hrev :
      (cells.filterMap (fun cell => cell)).reverse = ([] : List symbol) := by
    simpa [List.filterMap_reverse] using h
  simpa using congrArg List.reverse hrev

theorem filterMap_of_reverse_singleton
    {cells : List (Option symbol)} {one : symbol}
    (h : cells.reverse.filterMap (fun cell => cell) = [one]) :
    cells.filterMap (fun cell => cell) = [one] := by
  have hrev :
      (cells.filterMap (fun cell => cell)).reverse = [one] := by
    simpa [List.filterMap_reverse] using h
  simpa using congrArg List.reverse hrev

def NormalizedOutputScannerComplete
    (M : TuringMachine symbol state) (zero one : symbol) : Prop :=
  forall final : Configuration symbol state,
    Halted M final ->
      Tape.normalizedOutput final.tape = [one] ->
        HaltsFrom (normalizedDeciderToAcceptor M zero one)
          (normalizedRunConfig final)

theorem normalizedOutputScannerComplete
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one) :
    NormalizedOutputScannerComplete M zero one := by
  intro final hhalt hout
  rcases final with ⟨finalState, tape⟩
  cases tape with
  | mk left head right =>
      simp [Halted] at hhalt
      cases head with
      | none =>
          have hsplit :
              (left.reverse.filterMap (fun cell => cell) = ([] : List symbol) ∧
                  right.filterMap (fun cell => cell) = [one]) ∨
                (left.reverse.filterMap (fun cell => cell) = [one] ∧
                  right.filterMap (fun cell => cell) = ([] : List symbol)) := by
            have hfull :
                left.reverse.filterMap (fun cell => cell) ++
                    right.filterMap (fun cell => cell) = [one] := by
              simpa [Tape.normalizedOutput, Tape.cells,
                List.filterMap_append] using hout
            exact List.append_eq_singleton_iff.mp hfull
          cases hsplit with
          | inl hright =>
              rcases hright with ⟨hleftOut, hrightOut⟩
              rcases filterMap_nil_decompose
                  (filterMap_of_reverse_nil hleftOut) with
                ⟨blanksLeftCtx, hleftBlank⟩
              rcases filterMap_singleton_decompose hrightOut with
                ⟨blanksRight, tail, hrightShape⟩
              let startConfig :
                  Configuration symbol
                    (NormalizedDeciderToAcceptorState state) :=
                normalizedRunConfig
                  { state := finalState,
                    tape := { left := left, head := none, right := right } }
              let targetConfig :
                  Configuration symbol
                    (NormalizedDeciderToAcceptorState state) :=
                { state := NormalizedDeciderToAcceptorState.sweepRight,
                  tape := scannerRightTargetTape zero one 1 blanksLeftCtx
                    blanksRight tail }
              have hstep :
                  Step (normalizedDeciderToAcceptor M zero one)
                    startConfig targetConfig := by
                cases blanksRight with
                | zero =>
                    simpa [startConfig, targetConfig, normalizedRunConfig,
                      normalizedDeciderToAcceptor,
                      normalizedDeciderToAcceptorTransition, hhalt,
                      hleftBlank, hrightShape, scannerRightTargetTape,
                      scannerBlankBlock, scannerZeroBlock, Tape.read,
                      Tape.move, Tape.moveRight, Tape.write]
                      using
                        (Step.mk
                          (M := normalizedDeciderToAcceptor M zero one)
                          (c := startConfig)
                          (write := some zero)
                          (dir := Direction.right)
                          (nextState :=
                            NormalizedDeciderToAcceptorState.sweepRight)
                          (by
                            simp [startConfig, normalizedRunConfig,
                              normalizedDeciderToAcceptor,
                              normalizedDeciderToAcceptorTransition, hhalt,
                              Tape.read]))
                | succ blanksRight =>
                    simpa [startConfig, targetConfig, normalizedRunConfig,
                      normalizedDeciderToAcceptor,
                      normalizedDeciderToAcceptorTransition, hhalt,
                      hleftBlank, hrightShape, scannerRightTargetTape,
                      scannerBlankBlock, scannerZeroBlock, Tape.read,
                      Tape.move, Tape.moveRight, Tape.write,
                      List.replicate_succ]
                      using
                        (Step.mk
                          (M := normalizedDeciderToAcceptor M zero one)
                          (c := startConfig)
                          (write := some zero)
                          (dir := Direction.right)
                          (nextState :=
                            NormalizedDeciderToAcceptorState.sweepRight)
                          (by
                            simp [startConfig, normalizedRunConfig,
                              normalizedDeciderToAcceptor,
                              normalizedDeciderToAcceptorTransition, hhalt,
                              Tape.read]))
              exact halts_from_of_computes_prefix
                (computes_of_step hstep)
                (normalizedDeciderToAcceptor_sweepRight_target_halts
                  M hzeroOne blanksRight 1 blanksLeftCtx tail)
          | inr hleft =>
              rcases hleft with ⟨hleftOut, hrightOut⟩
              rcases filterMap_nil_decompose hrightOut with
                ⟨rightBlanks, hrightBlank⟩
              have hleftForward :
                  left.filterMap (fun cell => cell) = [one] :=
                filterMap_of_reverse_singleton hleftOut
              rcases filterMap_singleton_decompose hleftForward with
                ⟨blanksLeft, tail, hleftShape⟩
              let startConfig :
                  Configuration symbol
                    (NormalizedDeciderToAcceptorState state) :=
                normalizedRunConfig
                  { state := finalState,
                    tape := { left := left, head := none, right := right } }
              let afterRunConfig :
                  Configuration symbol
                    (NormalizedDeciderToAcceptorState state) :=
                { state := NormalizedDeciderToAcceptorState.sweepRight,
                  tape :=
                    scannerRightCrossTape zero 1
                      (scannerBlankBlock blanksLeft ++ some one :: tail)
                      (scannerBlankBlock rightBlanks) }
              have hstepRun :
                  Step (normalizedDeciderToAcceptor M zero one)
                    startConfig afterRunConfig := by
                cases rightBlanks with
                | zero =>
                    simpa [startConfig, afterRunConfig, normalizedRunConfig,
                      normalizedDeciderToAcceptor,
                      normalizedDeciderToAcceptorTransition, hhalt,
                      hleftShape, hrightBlank, scannerRightCrossTape,
                      scannerBlankBlock, scannerZeroBlock, Tape.read,
                      Tape.move, Tape.moveRight, Tape.write]
                      using
                        (Step.mk
                          (M := normalizedDeciderToAcceptor M zero one)
                          (c := startConfig)
                          (write := some zero)
                          (dir := Direction.right)
                          (nextState :=
                            NormalizedDeciderToAcceptorState.sweepRight)
                          (by
                            simp [startConfig, normalizedRunConfig,
                              normalizedDeciderToAcceptor,
                              normalizedDeciderToAcceptorTransition, hhalt,
                              Tape.read]))
                | succ rightPred =>
                    simpa [startConfig, afterRunConfig, normalizedRunConfig,
                      normalizedDeciderToAcceptor,
                      normalizedDeciderToAcceptorTransition, hhalt,
                      hleftShape, hrightBlank, scannerRightCrossTape,
                      scannerBlankBlock, scannerZeroBlock, Tape.read,
                      Tape.move, Tape.moveRight, Tape.write,
                      List.replicate_succ]
                      using
                        (Step.mk
                          (M := normalizedDeciderToAcceptor M zero one)
                          (c := startConfig)
                          (write := some zero)
                          (dir := Direction.right)
                          (nextState :=
                            NormalizedDeciderToAcceptorState.sweepRight)
                          (by
                            simp [startConfig, normalizedRunConfig,
                              normalizedDeciderToAcceptor,
                              normalizedDeciderToAcceptorTransition, hhalt,
                              Tape.read]))
              let rightCtx :=
                some zero :: scannerBlankBlock rightBlanks.pred
              let leftRest :=
                scannerZeroBlock zero 1 ++
                  scannerBlankBlock blanksLeft ++ some one :: tail
              let afterRightMark : Tape symbol :=
                scannerLeftCrossTape zero 0 rightCtx leftRest
              have hstepRight :
                  Step (normalizedDeciderToAcceptor M zero one)
                    afterRunConfig
                    { state := NormalizedDeciderToAcceptorState.sweepLeft,
                      tape := afterRightMark } := by
                cases rightBlanks with
                | zero =>
                    simpa [afterRunConfig, afterRightMark, rightCtx,
                      leftRest, scannerRightCrossTape,
                      scannerLeftCrossTape, scannerBlankBlock,
                      scannerZeroBlock, Tape.read, Tape.move,
                      Tape.moveLeft, Tape.write]
                      using
                        normalizedDeciderToAcceptor_sweepRight_blank_step
                          M zero one
                          (T := afterRunConfig.tape)
                          (by
                            simp [afterRunConfig, scannerRightCrossTape,
                              Tape.read, scannerBlankBlock])
                | succ rightPred =>
                    simpa [afterRunConfig, afterRightMark, rightCtx,
                      leftRest, scannerRightCrossTape,
                      scannerLeftCrossTape, scannerBlankBlock,
                      scannerZeroBlock, Tape.read, Tape.move,
                      Tape.moveLeft, Tape.write, List.replicate_succ]
                      using
                        normalizedDeciderToAcceptor_sweepRight_blank_step
                          M zero one
                          (T := afterRunConfig.tape)
                          (by
                            simp [afterRunConfig, scannerRightCrossTape,
                              Tape.read, scannerBlankBlock,
                              List.replicate_succ])
              have hcrossLeft :
                  Computes (normalizedDeciderToAcceptor M zero one)
                    { state := NormalizedDeciderToAcceptorState.sweepLeft,
                      tape := afterRightMark }
                    { state := NormalizedDeciderToAcceptorState.sweepLeft,
                      tape := scannerLeftTargetTape zero one 2
                        rightBlanks.pred blanksLeft tail } := by
                have h :=
                  normalizedDeciderToAcceptor_sweepLeft_cross_zeroBlock
                    M hzeroOne 1 0 rightCtx
                    (scannerBlankBlock blanksLeft ++ some one :: tail)
                cases blanksLeft with
                | zero =>
                    simpa [afterRightMark, rightCtx, leftRest,
                      scannerLeftTargetTape, scannerLeftCrossTape,
                      scannerBlankBlock, scannerZeroBlock,
                      List.replicate_succ, List.append_assoc]
                      using h
                | succ blanksLeft =>
                    simpa [afterRightMark, rightCtx, leftRest,
                      scannerLeftTargetTape, scannerLeftCrossTape,
                      scannerBlankBlock, scannerZeroBlock,
                      List.replicate_succ, List.append_assoc]
                      using h
              exact halts_from_of_computes_prefix
                (Computes.step hstepRun
                  (Computes.step hstepRight hcrossLeft))
                (normalizedDeciderToAcceptor_sweepLeft_target_halts
                  M hzeroOne blanksLeft 2 rightBlanks.pred tail)
      | some a =>
          by_cases ha : a = one
          · subst a
            let startConfig :
                Configuration symbol
                  (NormalizedDeciderToAcceptorState state) :=
              normalizedRunConfig
                { state := finalState,
                  tape := { left := left, head := some one, right := right } }
            let acceptConfig :
                Configuration symbol
                  (NormalizedDeciderToAcceptorState state) :=
              { state := NormalizedDeciderToAcceptorState.accept,
                tape := Tape.move Direction.right
                  (Tape.write (some one)
                    { left := left, head := some one, right := right }) }
            have hstep :
                Step (normalizedDeciderToAcceptor M zero one)
                  startConfig acceptConfig := by
              simpa [startConfig, acceptConfig, normalizedRunConfig,
                normalizedDeciderToAcceptor,
                normalizedDeciderToAcceptorTransition, hhalt, Tape.read]
                using
                  (Step.mk
                    (M := normalizedDeciderToAcceptor M zero one)
                    (c := startConfig)
                    (write := some one)
                    (dir := Direction.right)
                    (nextState := NormalizedDeciderToAcceptorState.accept)
                    (by
                      simp [startConfig, normalizedRunConfig,
                        normalizedDeciderToAcceptor,
                        normalizedDeciderToAcceptorTransition, hhalt,
                        Tape.read]))
            exact ⟨acceptConfig,
              Computes.step hstep (Computes.refl acceptConfig), rfl⟩
          · have haMem :
                a ∈ (left.reverse ++ some a :: right).filterMap
                    (fun cell => cell) := by
              simp
            have houtCells :
                (left.reverse ++ some a :: right).filterMap
                    (fun cell => cell) = [one] := by
              simpa [Tape.normalizedOutput, Tape.cells] using hout
            rw [houtCells] at haMem
            simp at haMem
            exact False.elim (ha haMem)

theorem normalizedDeciderToAcceptor_halts_of_mem
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (hdec : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hw : w ∈ L) :
    HaltsOnInput (normalizedDeciderToAcceptor M zero one)
      (EncodeWord encodeInput w) := by
  rcases (hdec w).left hw with ⟨final, hcomp, hhalt, hout⟩
  have hsim := normalizedDeciderToAcceptor_simulates_computes
    (M := M) (zero := zero) (one := one) hstop hcomp
  exact halts_from_of_computes_prefix hsim
    (normalizedOutputScannerComplete M hzeroOne final hhalt hout)

theorem normalizedDeciderToAcceptor_acceptsLanguage_of_stopped_decider
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    AcceptsLanguage (normalizedDeciderToAcceptor M zero one) encodeInput L := by
  intro w
  constructor
  · exact normalizedDeciderToAcceptor_halts_sound_of_stopped_decider
      h.left h.right.left h.right.right
  · exact normalizedDeciderToAcceptor_halts_of_mem
      h.left h.right.left h.right.right

theorem stoppedDecidesLanguage_to_turingAcceptable
    {symbol state input : Type}
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    TuringAcceptable L := by
  exists symbol
  exists NormalizedDeciderToAcceptorState state
  exists normalizedDeciderToAcceptor M zero one
  exists encodeInput
  exact normalizedDeciderToAcceptor_acceptsLanguage_of_stopped_decider h

theorem stoppedTuringDecidable_to_turingAcceptable
    {input : Type} {L : Language input}
    (h : StoppedTuringDecidable L) :
    TuringAcceptable L := by
  rcases h with ⟨symbol, state, M, encodeInput, zero, one, hdec⟩
  exists symbol
  exists NormalizedDeciderToAcceptorState state
  exists normalizedDeciderToAcceptor M zero one
  exists encodeInput
  exact normalizedDeciderToAcceptor_acceptsLanguage_of_stopped_decider hdec

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
