import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StatefulOptionAppend

set_option doc.verso true

/-!
# Two-state optional-output finite-control compiler

This module is the first finite-control compiler slice with more than one scan
state.  The generated machine alternates between two scan states, applies the
corresponding optional-output rewrite to each input bit, then writes an
arbitrary final word from a generated writer block.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def alternatingEmit
    (emit0 emit1 : Bool -> Option Bool) (phase bit : Bool) :
    Option Bool :=
  if phase then emit1 bit else emit0 bit

def alternatingScanState (phase : Bool) : Nat :=
  if phase then 1 else 0

def alternatingPhaseAfter : Bool -> Word Bool -> Bool
  | phase, [] => phase
  | phase, _bit :: rest => alternatingPhaseAfter (!phase) rest

def alternatingOptionCellsFrom
    (emit0 emit1 : Bool -> Option Bool) :
    Bool -> Word Bool -> List (Option Bool)
  | _phase, [] => []
  | phase, bit :: rest =>
      alternatingEmit emit0 emit1 phase bit ::
        alternatingOptionCellsFrom emit0 emit1 (!phase) rest

def alternatingOptionOutputFrom
    (emit0 emit1 : Bool -> Option Bool) :
    Bool -> Word Bool -> Word Bool
  | _phase, [] => []
  | phase, bit :: rest =>
      List.append
        (optionEmitWord (alternatingEmit emit0 emit1 phase) bit)
        (alternatingOptionOutputFrom emit0 emit1 (!phase) rest)

theorem alternatingOptionOutputFrom_eq_filterMap_cells
    (emit0 emit1 : Bool -> Option Bool) (phase : Bool)
    (input : Word Bool) :
    alternatingOptionOutputFrom emit0 emit1 phase input =
      (alternatingOptionCellsFrom emit0 emit1 phase input).filterMap
        (fun cell => cell) := by
  induction input generalizing phase with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases hbit : alternatingEmit emit0 emit1 phase bit with
      | none =>
          simp [alternatingOptionOutputFrom, alternatingOptionCellsFrom,
            optionEmitWord, hbit, ih]
      | some out =>
          simp [alternatingOptionOutputFrom, alternatingOptionCellsFrom,
            optionEmitWord, hbit, ih]

def alternatingOptionAppendTransducer
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    FiniteTransducer where
  stateCount := 3
  start := 0
  halt := 2
  step := fun state read =>
    match state, read with
    | 0, some bit => some (1, optionEmitWord emit0 bit)
    | 1, some bit => some (0, optionEmitWord emit1 bit)
    | 0, none => some (2, final)
    | 1, none => some (2, final)
    | _, _ => none

theorem alternatingOptionAppendTransducer_wellFormed
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    (alternatingOptionAppendTransducer emit0 emit1 final).WellFormed := by
  refine
    ⟨by simp [alternatingOptionAppendTransducer],
      by simp [alternatingOptionAppendTransducer],
      by simp [alternatingOptionAppendTransducer], ?_⟩
  intro state read next out hstep
  cases state with
  | zero =>
      cases read with
      | none =>
          simp [alternatingOptionAppendTransducer] at hstep
          rcases hstep with ⟨hnext, _hout⟩
          rw [← hnext]
          simp [alternatingOptionAppendTransducer]
      | some bit =>
          cases bit <;>
            simp [alternatingOptionAppendTransducer] at hstep <;>
            rcases hstep with ⟨hnext, _hout⟩ <;>
            rw [← hnext] <;>
            simp [alternatingOptionAppendTransducer]
  | succ state =>
      cases state with
      | zero =>
          cases read with
          | none =>
              simp [alternatingOptionAppendTransducer] at hstep
              rcases hstep with ⟨hnext, _hout⟩
              rw [← hnext]
              simp [alternatingOptionAppendTransducer]
          | some bit =>
              cases bit <;>
                simp [alternatingOptionAppendTransducer] at hstep <;>
                rcases hstep with ⟨hnext, _hout⟩ <;>
                rw [← hnext] <;>
                simp [alternatingOptionAppendTransducer]
      | succ state =>
          cases read with
          | none =>
              simp [alternatingOptionAppendTransducer] at hstep
          | some bit =>
              cases bit <;>
                simp [alternatingOptionAppendTransducer] at hstep

theorem alternatingOptionAppendTransducer_run_state
    (emit0 emit1 : Bool -> Option Bool) (final input : Word Bool)
    (phase : Bool) :
    (alternatingOptionAppendTransducer emit0 emit1 final).run
        (input.length + 1) (alternatingScanState phase) input =
      some ((alternatingOptionAppendTransducer emit0 emit1 final).halt,
        List.append
          (alternatingOptionOutputFrom emit0 emit1 phase input)
          final) := by
  induction input generalizing phase with
  | nil =>
      cases phase <;>
        simp [FiniteTransducer.run, alternatingOptionAppendTransducer,
          alternatingScanState, alternatingOptionOutputFrom] <;> rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = (rest.length + 1) + 1 by
        simp]
      cases phase <;> cases bit
      · rw [FiniteTransducer.run]
        simp [alternatingOptionAppendTransducer,
          alternatingScanState, alternatingOptionOutputFrom,
          alternatingEmit, optionEmitWord]
        have hih := ih true
        simp [alternatingOptionAppendTransducer,
          alternatingScanState, optionEmitWord] at hih
        rw [hih]
        rfl
      · rw [FiniteTransducer.run]
        simp [alternatingOptionAppendTransducer,
          alternatingScanState, alternatingOptionOutputFrom,
          alternatingEmit, optionEmitWord]
        have hih := ih true
        simp [alternatingOptionAppendTransducer,
          alternatingScanState, optionEmitWord] at hih
        rw [hih]
        rfl
      · rw [FiniteTransducer.run]
        simp [alternatingOptionAppendTransducer,
          alternatingScanState, alternatingOptionOutputFrom,
          alternatingEmit, optionEmitWord]
        have hih := ih false
        simp [alternatingOptionAppendTransducer,
          alternatingScanState, optionEmitWord] at hih
        rw [hih]
        rfl
      · rw [FiniteTransducer.run]
        simp [alternatingOptionAppendTransducer,
          alternatingScanState, alternatingOptionOutputFrom,
          alternatingEmit, optionEmitWord]
        have hih := ih false
        simp [alternatingOptionAppendTransducer,
          alternatingScanState, optionEmitWord] at hih
        rw [hih]
        rfl

theorem alternatingOptionAppendTransducer_run
    (emit0 emit1 : Bool -> Option Bool) (final input : Word Bool) :
    (alternatingOptionAppendTransducer emit0 emit1 final).runFromStart
        (input.length + 1) input =
      some ((alternatingOptionAppendTransducer emit0 emit1 final).halt,
        List.append
          (alternatingOptionOutputFrom emit0 emit1 false input)
          final) := by
  exact alternatingOptionAppendTransducer_run_state
    emit0 emit1 final input false

theorem alternatingOptionAppendTransducer_runsToOutput
    (emit0 emit1 : Bool -> Option Bool) (final input : Word Bool) :
    (alternatingOptionAppendTransducer emit0 emit1 final).RunsToOutput
      input
      (List.append
        (alternatingOptionOutputFrom emit0 emit1 false input)
        final) := by
  exact alternatingOptionAppendTransducer_run emit0 emit1 final input

def alternatingNatNext (state : Nat) (_bit : Bool) : Nat :=
  if state = 0 then 1 else 0

def alternatingNatEmit
    (emit0 emit1 : Bool -> Option Bool) (state : Nat) (bit : Bool) :
    Option Bool :=
  if state = 0 then emit0 bit else emit1 bit

theorem alternatingNatNext_lt_two :
    forall state bit, state < 2 ->
      alternatingNatNext state bit < 2 := by
  intro state bit hstate
  by_cases hzero : state = 0 <;>
    simp [alternatingNatNext, hzero]

namespace FiniteTransducer

def alternatingOptionAppendWriterStart : Nat := 2

def alternatingOptionAppendHalt (final : Word Bool) : Nat :=
  alternatingOptionAppendWriterStart + final.length

def alternatingOptionAppendPrefixTransitions
    (emit0 emit1 : Bool -> Option Bool) (_final : Word Bool) :
    List TransitionDescription :=
  [ { source := 0
      read := none
      write := none
      move := Direction.right
      target := alternatingOptionAppendWriterStart }
  , { source := 1
      read := none
      write := none
      move := Direction.right
      target := alternatingOptionAppendWriterStart }
  , { source := 0
      read := some false
      write := emit0 false
      move := Direction.right
      target := 1 }
  , { source := 0
      read := some true
      write := emit0 true
      move := Direction.right
      target := 1 }
  , { source := 1
      read := some false
      write := emit1 false
      move := Direction.right
      target := 0 }
  , { source := 1
      read := some true
      write := emit1 true
      move := Direction.right
      target := 0 } ]

def alternatingOptionAppendTransitions
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    List TransitionDescription :=
  List.append
    (alternatingOptionAppendPrefixTransitions emit0 emit1 final)
    (copyAppendWordWriteTransitionsFrom
      alternatingOptionAppendWriterStart
      (alternatingOptionAppendHalt final) final)

theorem alternatingOptionAppendPrefix_source_lt_writerStart
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    forall t : TransitionDescription,
      t ∈ alternatingOptionAppendPrefixTransitions emit0 emit1 final ->
        t.source < alternatingOptionAppendWriterStart := by
  intro t ht
  simp [alternatingOptionAppendPrefixTransitions,
    alternatingOptionAppendWriterStart] at ht
  rcases ht with ht | ht | ht | ht | ht | ht <;> subst t <;>
    simp [alternatingOptionAppendWriterStart]

theorem alternatingOptionAppendPrefix_deterministic
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    forall t u : TransitionDescription,
      t ∈ alternatingOptionAppendPrefixTransitions emit0 emit1 final ->
      u ∈ alternatingOptionAppendPrefixTransitions emit0 emit1 final ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u := by
  intro t u ht hu hkey
  simp [alternatingOptionAppendPrefixTransitions] at ht hu
  rcases ht with ht | ht | ht | ht | ht | ht <;>
    rcases hu with hu | hu | hu | hu | hu | hu <;>
    subst t <;> subst u <;>
    simp [TransitionDescription.SameKey,
      TransitionDescription.SameAction] at hkey ⊢

end FiniteTransducer

def generatedAlternatingOptionAppendDescription
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    MachineDescription where
  stateCount := FiniteTransducer.alternatingOptionAppendHalt final + 1
  start := 0
  halt := FiniteTransducer.alternatingOptionAppendHalt final
  transitions :=
    FiniteTransducer.alternatingOptionAppendTransitions emit0 emit1 final

def appendWordWriteTargetTapeAtBlank
    (left : List (Option Bool)) (final : Word Bool) : Tape Bool :=
  tapeAtCells (List.append (final.reverse.map some) left) []

def FSTAlternatingOptionAppendTargetTape
    (emit0 emit1 : Bool -> Option Bool) (input final : Word Bool)
    (leftScratch : Nat) : Tape Bool :=
  appendWordWriteTargetTapeAtBlank
    (none ::
      List.append
        (alternatingOptionCellsFrom emit0 emit1 false input).reverse
        (List.replicate leftScratch (none : Option Bool)))
    final

theorem generatedAlternatingOptionAppendDescription_step_bit
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool)
    (phase bit : Bool) (left right : List (Option Bool)) :
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).runConfig 1
        { state := alternatingScanState phase
          tape := tapeAtCells left (some bit :: right) } =
      { state := alternatingScanState (!phase)
        tape :=
          tapeAtCells
            (alternatingEmit emit0 emit1 phase bit :: left)
            right } := by
  cases phase <;> cases bit <;> cases right <;>
    simp [generatedAlternatingOptionAppendDescription,
      FiniteTransducer.alternatingOptionAppendTransitions,
      FiniteTransducer.alternatingOptionAppendPrefixTransitions,
      FiniteTransducer.alternatingOptionAppendWriterStart,
      alternatingScanState, alternatingEmit,
      tapeAtCells, runConfig, stepConfig, lookupTransition,
      Matches, Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem generatedAlternatingOptionAppendDescription_step_blank
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool)
    (phase : Bool) (left : List (Option Bool)) :
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).runConfig 1
        { state := alternatingScanState phase
          tape := tapeAtCells left [none] } =
      { state := FiniteTransducer.alternatingOptionAppendWriterStart
        tape := tapeAtCells (none :: left) [none] } := by
  cases phase <;>
    simp [generatedAlternatingOptionAppendDescription,
      FiniteTransducer.alternatingOptionAppendTransitions,
      FiniteTransducer.alternatingOptionAppendPrefixTransitions,
      FiniteTransducer.alternatingOptionAppendWriterStart,
      alternatingScanState, tapeAtCells, runConfig, stepConfig,
      lookupTransition, Matches, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem generatedAlternatingOptionAppendDescription_run_scan
    (emit0 emit1 : Bool -> Option Bool) (final input : Word Bool)
    (phase : Bool) (left : List (Option Bool)) :
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).runConfig
        input.length
        { state := alternatingScanState phase
          tape := tapeAtCells left
            (List.append (input.map some) [none]) } =
      { state := alternatingScanState (alternatingPhaseAfter phase input)
        tape :=
          tapeAtCells
            (List.append
              (alternatingOptionCellsFrom emit0 emit1 phase input).reverse
              left)
            [none] } := by
  induction input generalizing phase left with
  | nil =>
      simp [runConfig, alternatingPhaseAfter, alternatingOptionCellsFrom]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        (generatedAlternatingOptionAppendDescription emit0 emit1 final).runConfig
            rest.length
            ((generatedAlternatingOptionAppendDescription emit0 emit1 final).runConfig 1
              { state := alternatingScanState phase
                tape :=
                  tapeAtCells left
                    (some bit :: List.append (rest.map some) [none]) }) =
          { state :=
              alternatingScanState
                (alternatingPhaseAfter phase (bit :: rest))
            tape :=
              tapeAtCells
                (List.append
                  (alternatingOptionCellsFrom emit0 emit1 phase
                    (bit :: rest)).reverse left)
                [none] }
      rw [generatedAlternatingOptionAppendDescription_step_bit]
      simpa [alternatingPhaseAfter, alternatingOptionCellsFrom,
        List.reverse_cons, List.append_assoc] using
        ih (!phase) (alternatingEmit emit0 emit1 phase bit :: left)

theorem generatedAlternatingOptionAppendDescription_run_to_writer_start
    (emit0 emit1 : Bool -> Option Bool) (final input : Word Bool)
    (leftScratch : Nat) :
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).runConfig
        (input.length + 1)
        { state := (generatedAlternatingOptionAppendDescription
            emit0 emit1 final).start
          tape := FSTSourceTape input leftScratch } =
      { state := FiniteTransducer.alternatingOptionAppendWriterStart
        tape :=
          tapeAtCells
            (none ::
              List.append
                (alternatingOptionCellsFrom emit0 emit1 false input).reverse
                (List.replicate leftScratch (none : Option Bool)))
            [none] } := by
  rw [runConfig_add]
  change
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).runConfig 1
      ((generatedAlternatingOptionAppendDescription emit0 emit1 final).runConfig
        input.length
        { state := alternatingScanState false
          tape :=
            tapeAtCells (List.replicate leftScratch (none : Option Bool))
              (List.append (input.map some) [none]) }) =
      { state := FiniteTransducer.alternatingOptionAppendWriterStart
        tape :=
          tapeAtCells
            (none ::
              List.append
                (alternatingOptionCellsFrom emit0 emit1 false input).reverse
                (List.replicate leftScratch (none : Option Bool)))
            [none] }
  rw [generatedAlternatingOptionAppendDescription_run_scan]
  rw [generatedAlternatingOptionAppendDescription_step_blank]

theorem generatedAlternatingOptionAppendDescription_writerRuns
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool)
    (left : List (Option Bool)) :
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).runConfig
        final.length
        { state := FiniteTransducer.alternatingOptionAppendWriterStart
          tape := tapeAtCells left [none] } =
      { state := (generatedAlternatingOptionAppendDescription
            emit0 emit1 final).halt
        tape := appendWordWriteTargetTapeAtBlank left final } := by
  have hpre :
      forall t : TransitionDescription,
        t ∈ FiniteTransducer.alternatingOptionAppendPrefixTransitions
            emit0 emit1 final ->
          t.source < FiniteTransducer.alternatingOptionAppendWriterStart :=
    FiniteTransducer.alternatingOptionAppendPrefix_source_lt_writerStart
      emit0 emit1 final
  have hrun :=
    copyAppendWordWriteTransitionsFrom_run_with_pre
      (FiniteTransducer.alternatingOptionAppendPrefixTransitions
        emit0 emit1 final)
      FiniteTransducer.alternatingOptionAppendWriterStart
      0 final left hpre
  simpa [generatedAlternatingOptionAppendDescription,
    FiniteTransducer.alternatingOptionAppendTransitions,
    FiniteTransducer.alternatingOptionAppendHalt,
    appendWordWriteTargetTapeAtBlank] using hrun

theorem generatedAlternatingOptionAppendDescription_run_to_target
    (emit0 emit1 : Bool -> Option Bool) (final input : Word Bool)
    (leftScratch : Nat) :
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).runConfig
        (input.length + 1 + final.length)
        { state := (generatedAlternatingOptionAppendDescription
            emit0 emit1 final).start
          tape := FSTSourceTape input leftScratch } =
      { state :=
          (generatedAlternatingOptionAppendDescription emit0 emit1 final).halt
        tape :=
          FSTAlternatingOptionAppendTargetTape
            emit0 emit1 input final leftScratch } := by
  rw [show input.length + 1 + final.length =
      (input.length + 1) + final.length by omega]
  rw [runConfig_add]
  rw [generatedAlternatingOptionAppendDescription_run_to_writer_start]
  rw [generatedAlternatingOptionAppendDescription_writerRuns]
  simp [FSTAlternatingOptionAppendTargetTape]

theorem generatedAlternatingOptionAppendDescription_wellFormed
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [generatedAlternatingOptionAppendDescription,
      FiniteTransducer.alternatingOptionAppendHalt,
      FiniteTransducer.alternatingOptionAppendWriterStart]
  · simp [generatedAlternatingOptionAppendDescription,
      FiniteTransducer.alternatingOptionAppendHalt,
      FiniteTransducer.alternatingOptionAppendWriterStart]
  · simp [generatedAlternatingOptionAppendDescription]
  · intro t ht
    simp [generatedAlternatingOptionAppendDescription,
      FiniteTransducer.alternatingOptionAppendTransitions] at ht
    rcases ht with ht | ht
    · simp [FiniteTransducer.alternatingOptionAppendPrefixTransitions,
        TransitionDescription.WellFormed,
        FiniteTransducer.alternatingOptionAppendHalt,
        FiniteTransducer.alternatingOptionAppendWriterStart,
        generatedAlternatingOptionAppendDescription] at ht ⊢
      rcases ht with ht | ht | ht | ht | ht | ht <;> subst t <;>
        constructor <;>
        simp <;> omega
    · have htwf :=
        FiniteTransducer.copyAppendWordWriteTransitionsFrom_wellFormed
          FiniteTransducer.alternatingOptionAppendWriterStart final t ht
      simpa [generatedAlternatingOptionAppendDescription,
        FiniteTransducer.alternatingOptionAppendHalt,
        FiniteTransducer.alternatingOptionAppendWriterStart,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htwf
  · intro t u ht hu hkey
    simp [generatedAlternatingOptionAppendDescription,
      FiniteTransducer.alternatingOptionAppendTransitions] at ht hu
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact
        FiniteTransducer.alternatingOptionAppendPrefix_deterministic
          emit0 emit1 final t u ht hu hkey
    · have hubounds :=
        FiniteTransducer.copyAppendWordWriteTransitionsFrom_source_bounds
          FiniteTransducer.alternatingOptionAppendWriterStart
          (FiniteTransducer.alternatingOptionAppendHalt final) final u hu
      have htsource :=
        FiniteTransducer.alternatingOptionAppendPrefix_source_lt_writerStart
          emit0 emit1 final t ht
      have husource : u.source = t.source := hkey.left.symm
      omega
    · have htbounds :=
        FiniteTransducer.copyAppendWordWriteTransitionsFrom_source_bounds
          FiniteTransducer.alternatingOptionAppendWriterStart
          (FiniteTransducer.alternatingOptionAppendHalt final) final t ht
      have husource :=
        FiniteTransducer.alternatingOptionAppendPrefix_source_lt_writerStart
          emit0 emit1 final u hu
      have htsource : t.source = u.source := hkey.left
      omega
    · exact
        FiniteTransducer.copyAppendWordWriteTransitionsFrom_deterministic
          FiniteTransducer.alternatingOptionAppendWriterStart final
          t u
          (by
            simpa [FiniteTransducer.alternatingOptionAppendHalt,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht)
          (by
            simpa [FiniteTransducer.alternatingOptionAppendHalt,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu)
          hkey

theorem generatedAlternatingOptionAppendDescription_haltTransitionFree
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).HaltTransitionFree := by
  intro t ht hsource
  simp [generatedAlternatingOptionAppendDescription,
    FiniteTransducer.alternatingOptionAppendTransitions] at ht
  rcases ht with ht | ht
  · have hlt :=
      FiniteTransducer.alternatingOptionAppendPrefix_source_lt_writerStart
        emit0 emit1 final t ht
    simp [FiniteTransducer.alternatingOptionAppendWriterStart] at hlt
    simp [generatedAlternatingOptionAppendDescription,
      FiniteTransducer.alternatingOptionAppendHalt,
      FiniteTransducer.alternatingOptionAppendWriterStart] at hsource
    omega
  · have hbounds :=
      FiniteTransducer.copyAppendWordWriteTransitionsFrom_source_bounds
        FiniteTransducer.alternatingOptionAppendWriterStart
        (FiniteTransducer.alternatingOptionAppendHalt final) final t ht
    simp [FiniteTransducer.alternatingOptionAppendWriterStart] at hbounds
    simp [generatedAlternatingOptionAppendDescription,
      FiniteTransducer.alternatingOptionAppendHalt,
      FiniteTransducer.alternatingOptionAppendWriterStart] at hsource
    omega

theorem generatedAlternatingOptionAppendDescription_subroutineReady
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).SubroutineReady :=
  ⟨generatedAlternatingOptionAppendDescription_wellFormed emit0 emit1 final,
    generatedAlternatingOptionAppendDescription_haltTransitionFree
      emit0 emit1 final⟩

theorem generatedAlternatingOptionAppendDescription_statefulContract
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    StatefulOptionAppendMachineContract
      (generatedAlternatingOptionAppendDescription emit0 emit1 final)
      2
      alternatingNatNext
      (alternatingNatEmit emit0 emit1)
      final := by
  constructor
  · intro state bit left right hstate
    cases state with
    | zero =>
        simpa [alternatingNatNext, alternatingNatEmit,
          alternatingScanState, alternatingEmit] using
          generatedAlternatingOptionAppendDescription_step_bit
            emit0 emit1 final false bit left right
    | succ state =>
        cases state with
        | zero =>
            simpa [alternatingNatNext, alternatingNatEmit,
              alternatingScanState, alternatingEmit] using
              generatedAlternatingOptionAppendDescription_step_bit
                emit0 emit1 final true bit left right
        | succ state =>
            omega
  · intro state left hstate
    cases state with
    | zero =>
        simpa [alternatingNatNext, alternatingNatEmit,
          alternatingScanState, alternatingEmit] using
          generatedAlternatingOptionAppendDescription_step_blank
            emit0 emit1 final false left
    | succ state =>
        cases state with
        | zero =>
            simpa [alternatingNatNext, alternatingNatEmit,
              alternatingScanState, alternatingEmit] using
              generatedAlternatingOptionAppendDescription_step_blank
                emit0 emit1 final true left
        | succ state =>
            omega
  · intro left
    exact generatedAlternatingOptionAppendDescription_writerRuns
      emit0 emit1 final left

theorem statefulAlternatingOptionAppendTransducer_compiledByGeneratedDescription
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    ExactCompiledByDescription
      (statefulOptionAppendTransducer
        2 0 alternatingNatNext (alternatingNatEmit emit0 emit1) final)
      (generatedAlternatingOptionAppendDescription emit0 emit1 final)
      (fun input _output leftScratch =>
        FSTStatefulOptionAppendTargetTape
          alternatingNatNext (alternatingNatEmit emit0 emit1)
          0 input final leftScratch) := by
  exact
    statefulOptionAppendTransducer_compiledByMachineContract
      (generatedAlternatingOptionAppendDescription emit0 emit1 final)
      2 0 alternatingNatNext (alternatingNatEmit emit0 emit1) final
      (generatedAlternatingOptionAppendDescription_subroutineReady
        emit0 emit1 final)
      (generatedAlternatingOptionAppendDescription_statefulContract
        emit0 emit1 final)
      (by decide)
      rfl
      alternatingNatNext_lt_two

theorem generatedAlternatingOptionAppendDescription_haltsFrom_FSTSourceTape
    (emit0 emit1 : Bool -> Option Bool) (final input : Word Bool)
    (leftScratch : Nat) :
    (generatedAlternatingOptionAppendDescription emit0 emit1 final).HaltsFromTape
      (FSTSourceTape input leftScratch)
      (FSTAlternatingOptionAppendTargetTape
        emit0 emit1 input final leftScratch) := by
  refine ⟨input.length + 1 + final.length, ?_⟩
  have hrun :=
    generatedAlternatingOptionAppendDescription_run_to_target
      emit0 emit1 final input leftScratch
  constructor
  · simpa using congrArg MachineDescription.Configuration.state hrun
  · simpa using congrArg MachineDescription.Configuration.tape hrun

theorem alternatingOptionAppendTransducer_compiledByGeneratedDescription
    (emit0 emit1 : Bool -> Option Bool) (final : Word Bool) :
    ExactCompiledByDescription
      (alternatingOptionAppendTransducer emit0 emit1 final)
      (generatedAlternatingOptionAppendDescription emit0 emit1 final)
      (fun input _output leftScratch =>
        FSTAlternatingOptionAppendTargetTape
          emit0 emit1 input final leftScratch) := by
  constructor
  · exact generatedAlternatingOptionAppendDescription_subroutineReady
      emit0 emit1 final
  · intro input output leftScratch hrun
    have hout := alternatingOptionAppendTransducer_run emit0 emit1 final input
    change
      (alternatingOptionAppendTransducer emit0 emit1 final).runFromStart
          (input.length + 1) input =
        some ((alternatingOptionAppendTransducer emit0 emit1 final).halt,
          output) at hrun
    rw [hout] at hrun
    cases hrun
    exact generatedAlternatingOptionAppendDescription_haltsFrom_FSTSourceTape
      emit0 emit1 final input leftScratch

end FiniteTransducers
end CommonGround

end Computability
end FoC
