import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StatefulOptionAppend

set_option doc.verso true

/-!
# Generated two-state optional-output compiler

This module provides a generated transition table for the generic stateful
optional-output append invariant when the scanner has exactly two finite-control
states.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def boolState (b : Bool) : Nat :=
  if b then 1 else 0

def twoStateOptionNext
    (next0 next1 : Bool -> Bool) (state : Nat) (bit : Bool) : Nat :=
  if state = 0 then boolState (next0 bit) else boolState (next1 bit)

def twoStateOptionEmit
    (emit0 emit1 : Bool -> Option Bool) (state : Nat) (bit : Bool) :
    Option Bool :=
  if state = 0 then emit0 bit else emit1 bit

theorem boolState_lt_two (b : Bool) : boolState b < 2 := by
  cases b <;> simp [boolState]

theorem twoStateOptionNext_lt_two
    (next0 next1 : Bool -> Bool) :
    forall state bit, state < 2 ->
      twoStateOptionNext next0 next1 state bit < 2 := by
  intro state bit _hstate
  by_cases hzero : state = 0 <;>
    simp [twoStateOptionNext, hzero, boolState_lt_two]

namespace FiniteTransducer

def twoStateOptionAppendWriterStart : Nat := 2

def twoStateOptionAppendHalt (final : Word Bool) : Nat :=
  twoStateOptionAppendWriterStart + final.length

def twoStateOptionAppendPrefixTransitions
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (_final : Word Bool) :
    List TransitionDescription :=
  [ { source := 0
      read := none
      write := none
      move := Direction.right
      target := twoStateOptionAppendWriterStart }
  , { source := 1
      read := none
      write := none
      move := Direction.right
      target := twoStateOptionAppendWriterStart }
  , { source := 0
      read := some false
      write := emit0 false
      move := Direction.right
      target := boolState (next0 false) }
  , { source := 0
      read := some true
      write := emit0 true
      move := Direction.right
      target := boolState (next0 true) }
  , { source := 1
      read := some false
      write := emit1 false
      move := Direction.right
      target := boolState (next1 false) }
  , { source := 1
      read := some true
      write := emit1 true
      move := Direction.right
      target := boolState (next1 true) } ]

def twoStateOptionAppendTransitions
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (final : Word Bool) :
    List TransitionDescription :=
  List.append
    (twoStateOptionAppendPrefixTransitions next0 next1 emit0 emit1 final)
    (copyAppendWordWriteTransitionsFrom
      twoStateOptionAppendWriterStart
      (twoStateOptionAppendHalt final) final)

theorem twoStateOptionAppendPrefix_source_lt_writerStart
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    forall t : TransitionDescription,
      t ∈ twoStateOptionAppendPrefixTransitions
          next0 next1 emit0 emit1 final ->
        t.source < twoStateOptionAppendWriterStart := by
  intro t ht
  simp [twoStateOptionAppendPrefixTransitions,
    twoStateOptionAppendWriterStart] at ht
  rcases ht with ht | ht | ht | ht | ht | ht <;> subst t <;>
    simp [twoStateOptionAppendWriterStart]

theorem twoStateOptionAppendPrefix_deterministic
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    forall t u : TransitionDescription,
      t ∈ twoStateOptionAppendPrefixTransitions
          next0 next1 emit0 emit1 final ->
      u ∈ twoStateOptionAppendPrefixTransitions
          next0 next1 emit0 emit1 final ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u := by
  intro t u ht hu hkey
  simp [twoStateOptionAppendPrefixTransitions] at ht hu
  rcases ht with ht | ht | ht | ht | ht | ht <;>
    rcases hu with hu | hu | hu | hu | hu | hu <;>
    subst t <;> subst u <;>
    simp [TransitionDescription.SameKey,
      TransitionDescription.SameAction] at hkey ⊢

end FiniteTransducer

def generatedTwoStateOptionAppendDescription
    (start : Bool)
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (final : Word Bool) : MachineDescription where
  stateCount := FiniteTransducer.twoStateOptionAppendHalt final + 1
  start := boolState start
  halt := FiniteTransducer.twoStateOptionAppendHalt final
  transitions :=
    FiniteTransducer.twoStateOptionAppendTransitions
      next0 next1 emit0 emit1 final

theorem generatedTwoStateOptionAppendDescription_step_bit
    (start : Bool)
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (final : Word Bool)
    (state bit : Bool) (left right : List (Option Bool)) :
    (generatedTwoStateOptionAppendDescription
      start next0 next1 emit0 emit1 final).runConfig 1
        { state := boolState state
          tape := tapeAtCells left (some bit :: right) } =
      { state :=
          match state with
          | false => boolState (next0 bit)
          | true => boolState (next1 bit)
        tape :=
          tapeAtCells
            ((match state with
              | false => emit0 bit
              | true => emit1 bit) :: left)
            right } := by
  cases state <;> cases bit <;> cases right <;>
    simp [generatedTwoStateOptionAppendDescription,
      FiniteTransducer.twoStateOptionAppendTransitions,
      FiniteTransducer.twoStateOptionAppendPrefixTransitions,
      FiniteTransducer.twoStateOptionAppendWriterStart,
      boolState, tapeAtCells, runConfig, stepConfig,
      lookupTransition, Matches, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem generatedTwoStateOptionAppendDescription_step_blank
    (start : Bool)
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (final : Word Bool)
    (state : Bool) (left : List (Option Bool)) :
    (generatedTwoStateOptionAppendDescription
      start next0 next1 emit0 emit1 final).runConfig 1
        { state := boolState state
          tape := tapeAtCells left [none] } =
      { state := FiniteTransducer.twoStateOptionAppendWriterStart
        tape := tapeAtCells (none :: left) [none] } := by
  cases state <;>
    simp [generatedTwoStateOptionAppendDescription,
      FiniteTransducer.twoStateOptionAppendTransitions,
      FiniteTransducer.twoStateOptionAppendPrefixTransitions,
      FiniteTransducer.twoStateOptionAppendWriterStart,
      boolState, tapeAtCells, runConfig, stepConfig,
      lookupTransition, Matches, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem generatedTwoStateOptionAppendDescription_writerRuns
    (start : Bool)
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (final : Word Bool)
    (left : List (Option Bool)) :
    (generatedTwoStateOptionAppendDescription
      start next0 next1 emit0 emit1 final).runConfig
        final.length
        { state := FiniteTransducer.twoStateOptionAppendWriterStart
          tape := tapeAtCells left [none] } =
      { state :=
          (generatedTwoStateOptionAppendDescription
            start next0 next1 emit0 emit1 final).halt
        tape := statefulOptionAppendWriteTargetTapeAtBlank left final } := by
  have hpre :
      forall t : TransitionDescription,
        t ∈ FiniteTransducer.twoStateOptionAppendPrefixTransitions
            next0 next1 emit0 emit1 final ->
          t.source < FiniteTransducer.twoStateOptionAppendWriterStart :=
    FiniteTransducer.twoStateOptionAppendPrefix_source_lt_writerStart
      next0 next1 emit0 emit1 final
  have hrun :=
    copyAppendWordWriteTransitionsFrom_run_with_pre
      (FiniteTransducer.twoStateOptionAppendPrefixTransitions
        next0 next1 emit0 emit1 final)
      FiniteTransducer.twoStateOptionAppendWriterStart
      (boolState start) final left hpre
  simpa [generatedTwoStateOptionAppendDescription,
    FiniteTransducer.twoStateOptionAppendTransitions,
    FiniteTransducer.twoStateOptionAppendHalt,
    statefulOptionAppendWriteTargetTapeAtBlank] using hrun

theorem generatedTwoStateOptionAppendDescription_wellFormed
    (start : Bool)
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (final : Word Bool) :
    (generatedTwoStateOptionAppendDescription
      start next0 next1 emit0 emit1 final).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [generatedTwoStateOptionAppendDescription,
      FiniteTransducer.twoStateOptionAppendHalt,
      FiniteTransducer.twoStateOptionAppendWriterStart]
  · have hstart := boolState_lt_two start
    simp [generatedTwoStateOptionAppendDescription,
      FiniteTransducer.twoStateOptionAppendHalt,
      FiniteTransducer.twoStateOptionAppendWriterStart]
    omega
  · simp [generatedTwoStateOptionAppendDescription]
  · intro t ht
    simp [generatedTwoStateOptionAppendDescription,
      FiniteTransducer.twoStateOptionAppendTransitions] at ht
    rcases ht with ht | ht
    · simp [FiniteTransducer.twoStateOptionAppendPrefixTransitions,
        TransitionDescription.WellFormed,
        FiniteTransducer.twoStateOptionAppendHalt,
        FiniteTransducer.twoStateOptionAppendWriterStart,
        generatedTwoStateOptionAppendDescription,
        boolState] at ht ⊢
      rcases ht with ht | ht | ht | ht | ht | ht <;> subst t <;>
        constructor <;>
        cases next0 false <;> cases next0 true <;>
        cases next1 false <;> cases next1 true <;>
        simp <;> omega
    · have htwf :=
        FiniteTransducer.copyAppendWordWriteTransitionsFrom_wellFormed
          FiniteTransducer.twoStateOptionAppendWriterStart final t ht
      simpa [generatedTwoStateOptionAppendDescription,
        FiniteTransducer.twoStateOptionAppendHalt,
        FiniteTransducer.twoStateOptionAppendWriterStart,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htwf
  · intro t u ht hu hkey
    simp [generatedTwoStateOptionAppendDescription,
      FiniteTransducer.twoStateOptionAppendTransitions] at ht hu
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact
        FiniteTransducer.twoStateOptionAppendPrefix_deterministic
          next0 next1 emit0 emit1 final t u ht hu hkey
    · have hubounds :=
        FiniteTransducer.copyAppendWordWriteTransitionsFrom_source_bounds
          FiniteTransducer.twoStateOptionAppendWriterStart
          (FiniteTransducer.twoStateOptionAppendHalt final) final u hu
      have htsource :=
        FiniteTransducer.twoStateOptionAppendPrefix_source_lt_writerStart
          next0 next1 emit0 emit1 final t ht
      have husource : u.source = t.source := hkey.left.symm
      omega
    · have htbounds :=
        FiniteTransducer.copyAppendWordWriteTransitionsFrom_source_bounds
          FiniteTransducer.twoStateOptionAppendWriterStart
          (FiniteTransducer.twoStateOptionAppendHalt final) final t ht
      have husource :=
        FiniteTransducer.twoStateOptionAppendPrefix_source_lt_writerStart
          next0 next1 emit0 emit1 final u hu
      have htsource : t.source = u.source := hkey.left
      omega
    · exact
        FiniteTransducer.copyAppendWordWriteTransitionsFrom_deterministic
          FiniteTransducer.twoStateOptionAppendWriterStart final
          t u
          (by
            simpa [FiniteTransducer.twoStateOptionAppendHalt,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht)
          (by
            simpa [FiniteTransducer.twoStateOptionAppendHalt,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu)
          hkey

theorem generatedTwoStateOptionAppendDescription_haltTransitionFree
    (start : Bool)
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (final : Word Bool) :
    (generatedTwoStateOptionAppendDescription
      start next0 next1 emit0 emit1 final).HaltTransitionFree := by
  intro t ht hsource
  simp [generatedTwoStateOptionAppendDescription,
    FiniteTransducer.twoStateOptionAppendTransitions] at ht
  rcases ht with ht | ht
  · have hlt :=
      FiniteTransducer.twoStateOptionAppendPrefix_source_lt_writerStart
        next0 next1 emit0 emit1 final t ht
    simp [FiniteTransducer.twoStateOptionAppendWriterStart] at hlt
    simp [generatedTwoStateOptionAppendDescription,
      FiniteTransducer.twoStateOptionAppendHalt,
      FiniteTransducer.twoStateOptionAppendWriterStart] at hsource
    omega
  · have hbounds :=
      FiniteTransducer.copyAppendWordWriteTransitionsFrom_source_bounds
        FiniteTransducer.twoStateOptionAppendWriterStart
        (FiniteTransducer.twoStateOptionAppendHalt final) final t ht
    simp [FiniteTransducer.twoStateOptionAppendWriterStart] at hbounds
    simp [generatedTwoStateOptionAppendDescription,
      FiniteTransducer.twoStateOptionAppendHalt,
      FiniteTransducer.twoStateOptionAppendWriterStart] at hsource
    omega

theorem generatedTwoStateOptionAppendDescription_subroutineReady
    (start : Bool)
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (final : Word Bool) :
    (generatedTwoStateOptionAppendDescription
      start next0 next1 emit0 emit1 final).SubroutineReady :=
  ⟨generatedTwoStateOptionAppendDescription_wellFormed
      start next0 next1 emit0 emit1 final,
    generatedTwoStateOptionAppendDescription_haltTransitionFree
      start next0 next1 emit0 emit1 final⟩

theorem generatedTwoStateOptionAppendDescription_statefulContract
    (start : Bool)
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (final : Word Bool) :
    StatefulOptionAppendMachineContract
      (generatedTwoStateOptionAppendDescription
        start next0 next1 emit0 emit1 final)
      2
      (twoStateOptionNext next0 next1)
      (twoStateOptionEmit emit0 emit1)
      final := by
  constructor
  · intro state bit left right hstate
    cases state with
    | zero =>
        simpa [twoStateOptionNext, twoStateOptionEmit,
          boolState] using
          generatedTwoStateOptionAppendDescription_step_bit
            start next0 next1 emit0 emit1 final false bit left right
    | succ state =>
        cases state with
        | zero =>
            simpa [twoStateOptionNext, twoStateOptionEmit,
              boolState] using
              generatedTwoStateOptionAppendDescription_step_bit
                start next0 next1 emit0 emit1 final true bit left right
        | succ state =>
            omega
  · intro state left hstate
    cases state with
    | zero =>
        simpa [twoStateOptionNext, twoStateOptionEmit,
          boolState] using
          generatedTwoStateOptionAppendDescription_step_blank
            start next0 next1 emit0 emit1 final false left
    | succ state =>
        cases state with
        | zero =>
            simpa [twoStateOptionNext, twoStateOptionEmit,
              boolState] using
              generatedTwoStateOptionAppendDescription_step_blank
                start next0 next1 emit0 emit1 final true left
        | succ state =>
            omega
  · intro left
    exact generatedTwoStateOptionAppendDescription_writerRuns
      start next0 next1 emit0 emit1 final left

theorem twoStateOptionAppendTransducer_compiledByGeneratedDescription
    (start : Bool)
    (next0 next1 : Bool -> Bool)
    (emit0 emit1 : Bool -> Option Bool)
    (final : Word Bool) :
    ExactCompiledByDescription
      (statefulOptionAppendTransducer
        2 (boolState start)
        (twoStateOptionNext next0 next1)
        (twoStateOptionEmit emit0 emit1)
        final)
      (generatedTwoStateOptionAppendDescription
        start next0 next1 emit0 emit1 final)
      (fun input _output leftScratch =>
        FSTStatefulOptionAppendTargetTape
          (twoStateOptionNext next0 next1)
          (twoStateOptionEmit emit0 emit1)
          (boolState start) input final leftScratch) := by
  exact
    statefulOptionAppendTransducer_compiledByMachineContract
      (generatedTwoStateOptionAppendDescription
        start next0 next1 emit0 emit1 final)
      2 (boolState start)
      (twoStateOptionNext next0 next1)
      (twoStateOptionEmit emit0 emit1)
      final
      (generatedTwoStateOptionAppendDescription_subroutineReady
        start next0 next1 emit0 emit1 final)
      (generatedTwoStateOptionAppendDescription_statefulContract
        start next0 next1 emit0 emit1 final)
      (boolState_lt_two start)
      rfl
      (twoStateOptionNext_lt_two next0 next1)

end FiniteTransducers
end CommonGround

end Computability
end FoC
