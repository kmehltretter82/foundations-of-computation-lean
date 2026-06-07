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

namespace TuringMachine

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
