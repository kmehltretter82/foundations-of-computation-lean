import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OptionAppend

set_option doc.verso true

/-!
# Stateful optional-output append contract

This module factors out the generic run invariant for finite-control scanners
whose input transitions emit zero or one physical output cell and whose blank
transition hands off to a generated append-word writer.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def statefulOptionAfter
    (next : Nat -> Bool -> Nat) :
    Nat -> Word Bool -> Nat
  | state, [] => state
  | state, bit :: rest => statefulOptionAfter next (next state bit) rest

def statefulOptionCellsFrom
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool) :
    Nat -> Word Bool -> List (Option Bool)
  | _state, [] => []
  | state, bit :: rest =>
      emit state bit ::
        statefulOptionCellsFrom next emit (next state bit) rest

def statefulOptionOutputFrom
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool) :
    Nat -> Word Bool -> Word Bool
  | _state, [] => []
  | state, bit :: rest =>
      List.append
        (optionEmitWord (emit state) bit)
        (statefulOptionOutputFrom next emit (next state bit) rest)

theorem statefulOptionAfter_append
    (next : Nat -> Bool -> Nat)
    (state : Nat) (xs ys : Word Bool) :
    statefulOptionAfter next state (List.append xs ys) =
      statefulOptionAfter next
        (statefulOptionAfter next state xs) ys := by
  induction xs generalizing state with
  | nil =>
      rfl
  | cons bit rest ih =>
      simpa [statefulOptionAfter] using
        ih (next state bit)

theorem statefulOptionCellsFrom_append
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (state : Nat) (xs ys : Word Bool) :
    statefulOptionCellsFrom next emit state (List.append xs ys) =
      List.append
        (statefulOptionCellsFrom next emit state xs)
        (statefulOptionCellsFrom next emit
          (statefulOptionAfter next state xs) ys) := by
  induction xs generalizing state with
  | nil =>
      rfl
  | cons bit rest ih =>
      simpa [statefulOptionAfter, statefulOptionCellsFrom,
        List.append_assoc] using
        ih (next state bit)

theorem statefulOptionOutputFrom_append
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (state : Nat) (xs ys : Word Bool) :
    statefulOptionOutputFrom next emit state (List.append xs ys) =
      List.append
        (statefulOptionOutputFrom next emit state xs)
        (statefulOptionOutputFrom next emit
          (statefulOptionAfter next state xs) ys) := by
  induction xs generalizing state with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases hbit : emit state bit with
      | none =>
          simp [statefulOptionOutputFrom, statefulOptionAfter,
            optionEmitWord, hbit]
          exact ih (next state bit)
      | some out =>
          simp [statefulOptionOutputFrom, statefulOptionAfter,
            optionEmitWord, hbit]
          exact congrArg (fun tail => out :: tail)
            (ih (next state bit))

theorem statefulOptionOutputFrom_eq_filterMap_cells
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (state : Nat) (input : Word Bool) :
    statefulOptionOutputFrom next emit state input =
      (statefulOptionCellsFrom next emit state input).filterMap
        (fun cell => cell) := by
  induction input generalizing state with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases hbit : emit state bit with
      | none =>
          simp [statefulOptionOutputFrom, statefulOptionCellsFrom,
            optionEmitWord, hbit, ih]
      | some out =>
          simp [statefulOptionOutputFrom, statefulOptionCellsFrom,
            optionEmitWord, hbit, ih]

def statefulOptionAppendTransducer
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool) : FiniteTransducer where
  stateCount := scanStateCount + 1
  start := start
  halt := scanStateCount
  step := fun state read =>
    if state < scanStateCount then
      match read with
      | none => some (scanStateCount, final)
      | some bit => some (next state bit, optionEmitWord (emit state) bit)
    else
      none

theorem statefulOptionAppendTransducer_wellFormed
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (hstart : start < scanStateCount)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    (statefulOptionAppendTransducer
      scanStateCount start next emit final).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [statefulOptionAppendTransducer]
  · simp [statefulOptionAppendTransducer]
    omega
  · simp [statefulOptionAppendTransducer]
  intro state read target out hstep
  by_cases hstate : state < scanStateCount
  · cases read with
    | none =>
        simp [statefulOptionAppendTransducer, hstate] at hstep
        rcases hstep with ⟨htarget, _hout⟩
        rw [← htarget]
        simp [statefulOptionAppendTransducer]
    | some bit =>
        simp [statefulOptionAppendTransducer, hstate] at hstep
        rcases hstep with ⟨htarget, _hout⟩
        rw [← htarget]
        have hlt := hnext state bit hstate
        simp [statefulOptionAppendTransducer]
        omega
  · simp [statefulOptionAppendTransducer, hstate] at hstep

theorem statefulOptionAfter_lt
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    forall state input,
      state < scanStateCount ->
        statefulOptionAfter next state input < scanStateCount := by
  intro state input hstate
  induction input generalizing state with
  | nil =>
      simpa [statefulOptionAfter] using hstate
  | cons bit rest ih =>
      exact ih (next state bit) (hnext state bit hstate)

theorem statefulOptionAppendTransducer_run_state
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final input : Word Bool)
    (state : Nat)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount)
    (hstate : state < scanStateCount) :
    (statefulOptionAppendTransducer
      scanStateCount start next emit final).run
        (input.length + 1) state input =
      some (scanStateCount,
        List.append
          (statefulOptionOutputFrom next emit state input)
          final) := by
  induction input generalizing state with
  | nil =>
      have hnot : state ≠ scanStateCount := by omega
      simp [FiniteTransducer.run, statefulOptionAppendTransducer,
        hstate, hnot, statefulOptionOutputFrom]
      rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = (rest.length + 1) + 1 by
        simp]
      rw [FiniteTransducer.run]
      have hnextState : next state bit < scanStateCount :=
        hnext state bit hstate
      have hnot : state ≠ scanStateCount := by omega
      have hnextNot : next state bit ≠ scanStateCount := by omega
      simp [statefulOptionAppendTransducer, hstate,
        hnot, hnextNot,
        statefulOptionOutputFrom, optionEmitWord]
      have hih := ih (next state bit) hnextState
      simp [statefulOptionAppendTransducer, optionEmitWord] at hih
      rw [hih]
      rfl

theorem statefulOptionAppendTransducer_run
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final input : Word Bool)
    (hstart : start < scanStateCount)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    (statefulOptionAppendTransducer
      scanStateCount start next emit final).runFromStart
        (input.length + 1) input =
      some (scanStateCount,
        List.append
          (statefulOptionOutputFrom next emit start input)
          final) := by
  exact statefulOptionAppendTransducer_run_state
    scanStateCount start next emit final input start hnext hstart

theorem statefulOptionAppendTransducer_runsToOutput
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final input : Word Bool)
    (hstart : start < scanStateCount)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    (statefulOptionAppendTransducer
      scanStateCount start next emit final).RunsToOutput
        input
        (List.append
          (statefulOptionOutputFrom next emit start input)
          final) := by
  exact statefulOptionAppendTransducer_run
    scanStateCount start next emit final input hstart hnext

def statefulOptionAppendWriteTargetTapeAtBlank
    (left : List (Option Bool)) (final : Word Bool) : Tape Bool :=
  tapeAtCells (List.append (final.reverse.map some) left) []

def FSTStatefulOptionAppendTargetTape
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input final : Word Bool)
    (leftScratch : Nat) : Tape Bool :=
  statefulOptionAppendWriteTargetTapeAtBlank
    (none ::
      List.append
        (statefulOptionCellsFrom next emit start input).reverse
        (List.replicate leftScratch (none : Option Bool)))
    final

def FSTStatefulOptionAppendSourceTapeWithPadding
    (input : Word Bool) (leftScratch : Nat)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells (List.replicate leftScratch (none : Option Bool))
    (List.append (input.map some) (none :: padding))

def FSTStatefulOptionAppendTargetTapeWithPadding
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input : Word Bool)
    (leftScratch : Nat) (padding : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        (statefulOptionCellsFrom next emit start input).reverse
        (List.replicate leftScratch (none : Option Bool)))
    padding

def FSTStatefulOptionAppendTargetTapeFromLeft
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input final : Word Bool)
    (left : List (Option Bool)) : Tape Bool :=
  statefulOptionAppendWriteTargetTapeAtBlank
    (none ::
      List.append
        (statefulOptionCellsFrom next emit start input).reverse
        left)
    final

def FSTStatefulOptionAppendTargetTapeFromLeftWithPadding
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input : Word Bool)
    (left padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (none ::
      List.append
        (statefulOptionCellsFrom next emit start input).reverse
        left)
    padding

def FSTStatefulOptionAppendPrefixedSourceTape
    (pref input : Word Bool) (leftScratch : Nat) : Tape Bool :=
  tapeAtCells
    (List.append (pref.reverse.map some)
      (List.replicate leftScratch (none : Option Bool)))
    (List.append (input.map some) [none])

def FSTStatefulOptionAppendPrefixedTargetTape
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (pref input final : Word Bool)
    (leftScratch : Nat) : Tape Bool :=
  FSTStatefulOptionAppendTargetTapeFromLeft
    next emit start input final
    (List.append (pref.reverse.map some)
      (List.replicate leftScratch (none : Option Bool)))

theorem statefulOptionAppendWriteTargetTapeAtBlank_cells
    (left : List (Option Bool)) (final : Word Bool) :
    Tape.cells
        (statefulOptionAppendWriteTargetTapeAtBlank left final) =
      List.append left.reverse
        (List.append (final.map some) [none]) := by
  simp [statefulOptionAppendWriteTargetTapeAtBlank, tapeAtCells,
    Tape.cells, List.reverse_append, List.map_reverse,
    List.append_assoc]

theorem FSTStatefulOptionAppendTargetTape_cells
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input final : Word Bool)
    (leftScratch : Nat) :
    Tape.cells
        (FSTStatefulOptionAppendTargetTape
          next emit start input final leftScratch) =
      List.append
        (List.replicate leftScratch (none : Option Bool))
        (List.append
          (statefulOptionCellsFrom next emit start input)
          (List.append [none] (List.append (final.map some) [none]))) := by
  rw [FSTStatefulOptionAppendTargetTape,
    statefulOptionAppendWriteTargetTapeAtBlank_cells]
  simp [List.reverse_append, List.append_assoc]

theorem FSTStatefulOptionAppendTargetTapeWithPadding_cells_cons
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input : Word Bool)
    (leftScratch : Nat) (paddingHead : Option Bool)
    (paddingTail : List (Option Bool)) :
    Tape.cells
        (FSTStatefulOptionAppendTargetTapeWithPadding
          next emit start input leftScratch
          (paddingHead :: paddingTail)) =
      List.append
        (List.replicate leftScratch (none : Option Bool))
        (List.append
          (statefulOptionCellsFrom next emit start input)
          (none :: paddingHead :: paddingTail)) := by
  simp [FSTStatefulOptionAppendTargetTapeWithPadding,
    tapeAtCells, Tape.cells, List.reverse_append,
    List.append_assoc]

theorem FSTStatefulOptionAppendTargetTapeFromLeft_cells
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input final : Word Bool)
    (left : List (Option Bool)) :
    Tape.cells
        (FSTStatefulOptionAppendTargetTapeFromLeft
          next emit start input final left) =
      List.append left.reverse
        (List.append
          (statefulOptionCellsFrom next emit start input)
          (List.append [none] (List.append (final.map some) [none]))) := by
  rw [FSTStatefulOptionAppendTargetTapeFromLeft,
    statefulOptionAppendWriteTargetTapeAtBlank_cells]
  simp [List.reverse_append, List.append_assoc]

theorem FSTStatefulOptionAppendPrefixedTargetTape_cells
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (pref input final : Word Bool)
    (leftScratch : Nat) :
    Tape.cells
        (FSTStatefulOptionAppendPrefixedTargetTape
          next emit start pref input final leftScratch) =
      List.append
        (List.replicate leftScratch (none : Option Bool))
        (List.append
          (pref.map some)
          (List.append
            (statefulOptionCellsFrom next emit start input)
            (List.append [none] (List.append (final.map some) [none])))) := by
  rw [FSTStatefulOptionAppendPrefixedTargetTape,
    FSTStatefulOptionAppendTargetTapeFromLeft_cells]
  simp [List.reverse_append, List.map_reverse, List.append_assoc]

theorem FSTStatefulOptionAppendTargetTape_normalizedOutput
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input final : Word Bool)
    (leftScratch : Nat) :
    Tape.normalizedOutput
        (FSTStatefulOptionAppendTargetTape
          next emit start input final leftScratch) =
      List.append
        (statefulOptionOutputFrom next emit start input)
        final := by
  rw [FSTStatefulOptionAppendTargetTape,
    statefulOptionAppendWriteTargetTapeAtBlank,
    tapeAtCells_normalizedOutput]
  rw [statefulOptionOutputFrom_eq_filterMap_cells]
  simp [Function.comp_def, List.filterMap_append,
    List.reverse_append, List.map_reverse]

theorem FSTStatefulOptionAppendTargetTapeFromLeft_normalizedOutput
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (input final : Word Bool)
    (left : List (Option Bool)) :
    Tape.normalizedOutput
        (FSTStatefulOptionAppendTargetTapeFromLeft
          next emit start input final left) =
      List.append
        (left.reverse.filterMap (fun cell => cell))
        (List.append
          (statefulOptionOutputFrom next emit start input)
          final) := by
  rw [FSTStatefulOptionAppendTargetTapeFromLeft,
    statefulOptionAppendWriteTargetTapeAtBlank,
    tapeAtCells_normalizedOutput]
  rw [statefulOptionOutputFrom_eq_filterMap_cells]
  simp [Function.comp_def, List.filterMap_append,
    List.reverse_append, List.map_reverse, List.append_assoc]

theorem FSTStatefulOptionAppendPrefixedTargetTape_normalizedOutput
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (start : Nat) (pref input final : Word Bool)
    (leftScratch : Nat) :
    Tape.normalizedOutput
        (FSTStatefulOptionAppendPrefixedTargetTape
          next emit start pref input final leftScratch) =
      List.append pref
        (List.append
          (statefulOptionOutputFrom next emit start input)
          final) := by
  rw [FSTStatefulOptionAppendPrefixedTargetTape,
    FSTStatefulOptionAppendTargetTapeFromLeft_normalizedOutput]
  simp [Function.comp_def, List.filterMap_append]

structure StatefulOptionAppendMachineContract
    (D : MachineDescription)
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool) : Prop where
  step_bit :
    forall state bit left right,
      state < scanStateCount ->
        D.runConfig 1
          { state := state
            tape := tapeAtCells left (some bit :: right) } =
        { state := next state bit
          tape := tapeAtCells (emit state bit :: left) right }
  step_blank :
    forall state left,
      state < scanStateCount ->
        D.runConfig 1
          { state := state
            tape := tapeAtCells left [none] } =
        { state := scanStateCount
          tape := tapeAtCells (none :: left) [none] }
  writer_runs :
    forall left,
      D.runConfig final.length
        { state := scanStateCount
          tape := tapeAtCells left [none] } =
        { state := D.halt
          tape := statefulOptionAppendWriteTargetTapeAtBlank left final }

theorem StatefulOptionAppendMachineContract.run_scan
    {D : MachineDescription}
    {scanStateCount : Nat}
    {next : Nat -> Bool -> Nat}
    {emit : Nat -> Bool -> Option Bool}
    {final : Word Bool}
    (h : StatefulOptionAppendMachineContract
      D scanStateCount next emit final)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    forall (input : Word Bool) (state : Nat)
      (left : List (Option Bool)),
      state < scanStateCount ->
        D.runConfig input.length
          { state := state
            tape := tapeAtCells left
              (List.append (input.map some) [none]) } =
        { state := statefulOptionAfter next state input
          tape :=
            tapeAtCells
              (List.append
                (statefulOptionCellsFrom next emit state input).reverse
                left)
              [none] } := by
  intro input
  induction input with
  | nil =>
      intro state left hstate
      simp [runConfig, statefulOptionAfter, statefulOptionCellsFrom]
  | cons bit rest ih =>
      intro state left hstate
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        D.runConfig rest.length
            (D.runConfig 1
              { state := state
                tape :=
                  tapeAtCells left
                    (some bit :: List.append (rest.map some) [none]) }) =
          { state := statefulOptionAfter next state (bit :: rest)
            tape :=
              tapeAtCells
                (List.append
                  (statefulOptionCellsFrom next emit state
                    (bit :: rest)).reverse left)
                [none] }
      rw [h.step_bit state bit left
        (List.append (rest.map some) [none]) hstate]
      simpa [statefulOptionAfter, statefulOptionCellsFrom,
        List.reverse_cons, List.append_assoc] using
        ih (next state bit) (emit state bit :: left)
          (hnext state bit hstate)

theorem StatefulOptionAppendMachineContract.run_scan_withPadding
    {D : MachineDescription}
    {scanStateCount : Nat}
    {next : Nat -> Bool -> Nat}
    {emit : Nat -> Bool -> Option Bool}
    {final : Word Bool}
    (h : StatefulOptionAppendMachineContract
      D scanStateCount next emit final)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    forall (input : Word Bool) (state : Nat)
      (left padding : List (Option Bool)),
      state < scanStateCount ->
        D.runConfig input.length
          { state := state
            tape := tapeAtCells left
              (List.append (input.map some) (none :: padding)) } =
        { state := statefulOptionAfter next state input
          tape :=
            tapeAtCells
              (List.append
                (statefulOptionCellsFrom next emit state input).reverse
                left)
              (none :: padding) } := by
  intro input
  induction input with
  | nil =>
      intro state left padding hstate
      simp [runConfig, statefulOptionAfter, statefulOptionCellsFrom]
  | cons bit rest ih =>
      intro state left padding hstate
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        D.runConfig rest.length
            (D.runConfig 1
              { state := state
                tape :=
                  tapeAtCells left
                    (some bit ::
                      List.append (rest.map some)
                        (none :: padding)) }) =
          { state := statefulOptionAfter next state (bit :: rest)
            tape :=
              tapeAtCells
                (List.append
                  (statefulOptionCellsFrom next emit state
                    (bit :: rest)).reverse left)
                (none :: padding) }
      rw [h.step_bit state bit left
        (List.append (rest.map some) (none :: padding)) hstate]
      simpa [statefulOptionAfter, statefulOptionCellsFrom,
        List.reverse_cons, List.append_assoc] using
        ih (next state bit) (emit state bit :: left) padding
          (hnext state bit hstate)

theorem StatefulOptionAppendMachineContract.run_to_writer_start
    {D : MachineDescription}
    {scanStateCount : Nat}
    {next : Nat -> Bool -> Nat}
    {emit : Nat -> Bool -> Option Bool}
    {final : Word Bool}
    (h : StatefulOptionAppendMachineContract
      D scanStateCount next emit final)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount)
    (start : Nat) (input : Word Bool) (leftScratch : Nat)
    (hstart : start < scanStateCount) :
    D.runConfig (input.length + 1)
        { state := start
          tape := FSTSourceTape input leftScratch } =
      { state := scanStateCount
        tape :=
          tapeAtCells
            (none ::
              List.append
                (statefulOptionCellsFrom next emit start input).reverse
                (List.replicate leftScratch (none : Option Bool)))
            [none] } := by
  rw [runConfig_add]
  change
    D.runConfig 1
      (D.runConfig input.length
        { state := start
          tape :=
            tapeAtCells (List.replicate leftScratch (none : Option Bool))
              (List.append (input.map some) [none]) }) =
      { state := scanStateCount
        tape :=
          tapeAtCells
            (none ::
              List.append
                (statefulOptionCellsFrom next emit start input).reverse
                (List.replicate leftScratch (none : Option Bool)))
            [none] }
  rw [h.run_scan hnext input start
    (List.replicate leftScratch (none : Option Bool)) hstart]
  exact h.step_blank
    (statefulOptionAfter next start input)
    (List.append
      (statefulOptionCellsFrom next emit start input).reverse
      (List.replicate leftScratch (none : Option Bool)))
    (statefulOptionAfter_lt scanStateCount next hnext start input hstart)

theorem StatefulOptionAppendMachineContract.run_to_target
    {D : MachineDescription}
    {scanStateCount : Nat}
    {next : Nat -> Bool -> Nat}
    {emit : Nat -> Bool -> Option Bool}
    {final : Word Bool}
    (h : StatefulOptionAppendMachineContract
      D scanStateCount next emit final)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount)
    (start : Nat) (input : Word Bool) (leftScratch : Nat)
    (hstart : start < scanStateCount) :
    D.runConfig (input.length + 1 + final.length)
        { state := start
          tape := FSTSourceTape input leftScratch } =
      { state := D.halt
        tape :=
          FSTStatefulOptionAppendTargetTape
            next emit start input final leftScratch } := by
  rw [show input.length + 1 + final.length =
      (input.length + 1) + final.length by omega]
  rw [runConfig_add]
  rw [h.run_to_writer_start hnext start input leftScratch hstart]
  rw [h.writer_runs]
  simp [FSTStatefulOptionAppendTargetTape]

theorem StatefulOptionAppendMachineContract.run_to_target_from_tapeAtCells
    {D : MachineDescription}
    {scanStateCount : Nat}
    {next : Nat -> Bool -> Nat}
    {emit : Nat -> Bool -> Option Bool}
    {final : Word Bool}
    (h : StatefulOptionAppendMachineContract
      D scanStateCount next emit final)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount)
    (start : Nat) (input : Word Bool)
    (left : List (Option Bool))
    (hstart : start < scanStateCount) :
    D.runConfig (input.length + 1 + final.length)
        { state := start
          tape := tapeAtCells left
            (List.append (input.map some) [none]) } =
      { state := D.halt
        tape :=
          FSTStatefulOptionAppendTargetTapeFromLeft
            next emit start input final left } := by
  rw [show input.length + 1 + final.length =
      (input.length + 1) + final.length by omega]
  rw [runConfig_add]
  rw [runConfig_add D input.length 1
    { state := start
      tape := tapeAtCells left
        (List.append (input.map some) [none]) }]
  rw [h.run_scan hnext input start left hstart]
  rw [h.step_blank
    (statefulOptionAfter next start input)
    (List.append
      (statefulOptionCellsFrom next emit start input).reverse left)
    (statefulOptionAfter_lt scanStateCount next hnext start input hstart)]
  rw [h.writer_runs]
  simp [FSTStatefulOptionAppendTargetTapeFromLeft]

theorem StatefulOptionAppendMachineContract.haltsFrom_FSTSourceTape
    {D : MachineDescription}
    {scanStateCount : Nat}
    {next : Nat -> Bool -> Nat}
    {emit : Nat -> Bool -> Option Bool}
    {final : Word Bool}
    (h : StatefulOptionAppendMachineContract
      D scanStateCount next emit final)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount)
    (start : Nat) (input : Word Bool) (leftScratch : Nat)
    (hstart : start < scanStateCount)
    (hDstart : D.start = start) :
    D.HaltsFromTape
      (FSTSourceTape input leftScratch)
      (FSTStatefulOptionAppendTargetTape
        next emit start input final leftScratch) := by
  refine ⟨input.length + 1 + final.length, ?_⟩
  have hrun :=
    h.run_to_target hnext start input leftScratch hstart
  constructor
  · simpa [hDstart] using
      congrArg MachineDescription.Configuration.state hrun
  · simpa [hDstart] using
      congrArg MachineDescription.Configuration.tape hrun

theorem StatefulOptionAppendMachineContract.haltsFrom_tapeAtCells
    {D : MachineDescription}
    {scanStateCount : Nat}
    {next : Nat -> Bool -> Nat}
    {emit : Nat -> Bool -> Option Bool}
    {final : Word Bool}
    (h : StatefulOptionAppendMachineContract
      D scanStateCount next emit final)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount)
    (start : Nat) (input : Word Bool)
    (left : List (Option Bool))
    (hstart : start < scanStateCount)
    (hDstart : D.start = start) :
    D.HaltsFromTape
      (tapeAtCells left (List.append (input.map some) [none]))
      (FSTStatefulOptionAppendTargetTapeFromLeft
        next emit start input final left) := by
  refine ⟨input.length + 1 + final.length, ?_⟩
  have hrun :=
    h.run_to_target_from_tapeAtCells
      hnext start input left hstart
  constructor
  · simpa [hDstart] using
      congrArg MachineDescription.Configuration.state hrun
  · simpa [hDstart] using
      congrArg MachineDescription.Configuration.tape hrun

theorem StatefulOptionAppendMachineContract.haltsFrom_prefixedSourceTape
    {D : MachineDescription}
    {scanStateCount : Nat}
    {next : Nat -> Bool -> Nat}
    {emit : Nat -> Bool -> Option Bool}
    {final : Word Bool}
    (h : StatefulOptionAppendMachineContract
      D scanStateCount next emit final)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount)
    (start : Nat) (pref input : Word Bool)
    (leftScratch : Nat)
    (hstart : start < scanStateCount)
    (hDstart : D.start = start) :
    D.HaltsFromTape
      (FSTStatefulOptionAppendPrefixedSourceTape
        pref input leftScratch)
      (FSTStatefulOptionAppendPrefixedTargetTape
        next emit start pref input final leftScratch) := by
  simpa [FSTStatefulOptionAppendPrefixedSourceTape,
    FSTStatefulOptionAppendPrefixedTargetTape] using
    h.haltsFrom_tapeAtCells hnext start input
      (List.append (pref.reverse.map some)
        (List.replicate leftScratch (none : Option Bool)))
      hstart hDstart

theorem statefulOptionAppendTransducer_compiledByMachineContract
    (D : MachineDescription)
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (hready : D.SubroutineReady)
    (hcontract :
      StatefulOptionAppendMachineContract
        D scanStateCount next emit final)
    (hstart : start < scanStateCount)
    (hDstart : D.start = start)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    ExactCompiledByDescription
      (statefulOptionAppendTransducer
        scanStateCount start next emit final)
      D
      (fun input _output leftScratch =>
        FSTStatefulOptionAppendTargetTape
          next emit start input final leftScratch) := by
  constructor
  · exact hready
  · intro input output leftScratch hrun
    have hout :=
      statefulOptionAppendTransducer_run
        scanStateCount start next emit final input hstart hnext
    change
      (statefulOptionAppendTransducer
        scanStateCount start next emit final).runFromStart
          (input.length + 1) input =
        some
          ((statefulOptionAppendTransducer
            scanStateCount start next emit final).halt, output) at hrun
    rw [hout] at hrun
    cases hrun
    exact hcontract.haltsFrom_FSTSourceTape
      hnext start input leftScratch hstart hDstart

end FiniteTransducers
end CommonGround

end Computability
end FoC
