import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.AppendWord

set_option doc.verso true

/-!
# Optional-output finite transducer compiler

This module proves a keep/delete compiler slice.  Each input bit is rewritten to
an optional output cell, so {lit}`none` deletes the bit in the normalized output
and {lit}`some b` keeps or rewrites it.  The exact tape theorem preserves the
physical blank cells left by deleted bits.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def optionEmitWord (emit : Bool -> Option Bool) (bit : Bool) :
    Word Bool :=
  match emit bit with
  | none => []
  | some out => [out]

def optionAppendFinalTransducer
    (emit : Bool -> Option Bool) (final : Word Bool) :
    FiniteTransducer :=
  bitwiseOutputTransducer (optionEmitWord emit) final

theorem bitwiseOutput_optionEmitWord
    (emit : Bool -> Option Bool) (input : Word Bool) :
    bitwiseOutput (optionEmitWord emit) input =
      input.filterMap emit := by
  induction input with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases hbit : emit bit with
      | none =>
          simp [bitwiseOutput, optionEmitWord, hbit, ih]
      | some out =>
          simp [bitwiseOutput, optionEmitWord, hbit, ih]

theorem optionAppendFinalTransducer_wellFormed
    (emit : Bool -> Option Bool) (final : Word Bool) :
    (optionAppendFinalTransducer emit final).WellFormed := by
  exact bitwiseOutputTransducer_wellFormed (optionEmitWord emit) final

theorem optionAppendFinalTransducer_run
    (emit : Bool -> Option Bool) (final input : Word Bool) :
    (optionAppendFinalTransducer emit final).runFromStart
        (input.length + 1) input =
      some ((optionAppendFinalTransducer emit final).halt,
        List.append (input.filterMap emit) final) := by
  rw [optionAppendFinalTransducer, bitwiseOutputTransducer_run,
    bitwiseOutput_optionEmitWord]

theorem optionAppendFinalTransducer_runsToOutput
    (emit : Bool -> Option Bool) (final input : Word Bool) :
    (optionAppendFinalTransducer emit final).RunsToOutput
      input (List.append (input.filterMap emit) final) := by
  exact optionAppendFinalTransducer_run emit final input

namespace FiniteTransducer

def optionAppendWordScanFalseTransition
    (emit : Bool -> Option Bool) : TransitionDescription :=
  { source := 0
    read := some false
    write := emit false
    move := Direction.right
    target := 0 }

def optionAppendWordScanTrueTransition
    (emit : Bool -> Option Bool) : TransitionDescription :=
  { source := 0
    read := some true
    write := emit true
    move := Direction.right
    target := 0 }

def optionAppendWordTransitions
    (emit : Bool -> Option Bool) (final : Word Bool) :
    List TransitionDescription :=
  match copyAppendWordWriteTransitionsFrom 0 (copyAppendWordHalt final) final with
  | [] =>
      [ { source := 0
          read := none
          write := none
          move := Direction.right
          target := copyAppendWordHalt final }
      , optionAppendWordScanFalseTransition emit
      , optionAppendWordScanTrueTransition emit ]
  | first :: rest =>
      first :: optionAppendWordScanFalseTransition emit ::
        optionAppendWordScanTrueTransition emit :: rest

theorem optionAppendWordPrefix_deterministic
    (emit : Bool -> Option Bool) (first t u : TransitionDescription)
    (hfirstSource : first.source = 0)
    (hfirstRead : first.read = none)
    (ht :
      t ∈ [first, optionAppendWordScanFalseTransition emit,
        optionAppendWordScanTrueTransition emit])
    (hu :
      u ∈ [first, optionAppendWordScanFalseTransition emit,
        optionAppendWordScanTrueTransition emit])
    (hkey : TransitionDescription.SameKey t u) :
    TransitionDescription.SameAction t u := by
  simp [optionAppendWordScanFalseTransition,
    optionAppendWordScanTrueTransition] at ht hu
  rcases ht with ht | ht | ht <;>
    rcases hu with hu | hu | hu <;>
    subst t <;> subst u <;>
    simp [TransitionDescription.SameKey,
      TransitionDescription.SameAction, hfirstSource, hfirstRead] at hkey ⊢

end FiniteTransducer

def generatedOptionAppendWordDescription
    (emit : Bool -> Option Bool) (final : Word Bool) :
    MachineDescription where
  stateCount := FiniteTransducer.copyAppendWordHalt final + 1
  start := 0
  halt := FiniteTransducer.copyAppendWordHalt final
  transitions := FiniteTransducer.optionAppendWordTransitions emit final

def FSTOptionAppendFinalWordTargetTape
    (emit : Bool -> Option Bool) (input final : Word Bool)
    (leftScratch : Nat) : Tape Bool :=
  appendFinalWordWriteTargetTape
    (List.append (input.reverse.map emit)
      (List.replicate leftScratch (none : Option Bool)))
    final

theorem filterMap_option_reverse_map
    (emit : Bool -> Option Bool) (input : Word Bool) :
    List.filterMap (fun cell : Option Bool => cell)
        ((input.reverse.map emit).reverse) =
      input.filterMap emit := by
  induction input with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases hbit : emit bit with
      | none =>
          simp [List.reverse_cons, List.map_append, hbit,
            Function.comp_def]
      | some out =>
          simp [List.reverse_cons, List.map_append, hbit,
            Function.comp_def]

theorem FSTOptionAppendFinalWordTargetTape_normalizedOutput
    (emit : Bool -> Option Bool) (input final : Word Bool)
    (leftScratch : Nat) :
    Tape.normalizedOutput
        (FSTOptionAppendFinalWordTargetTape emit input final leftScratch) =
      List.append (input.filterMap emit) final := by
  cases final with
  | nil =>
      rw [FSTOptionAppendFinalWordTargetTape,
        appendFinalWordWriteTargetTape, tapeAtCells_normalizedOutput]
      simp [Function.comp_def, List.filterMap_append]
  | cons bit rest =>
      rw [FSTOptionAppendFinalWordTargetTape,
        appendFinalWordWriteTargetTape, tapeAtCells_normalizedOutput]
      simp [Function.comp_def, List.filterMap_append,
        List.reverse_append, List.map_append]

theorem generatedOptionAppendWordDescription_step_bit
    (emit : Bool -> Option Bool) (final : Word Bool) (bit : Bool)
    (left right : List (Option Bool)) :
    (generatedOptionAppendWordDescription emit final).runConfig 1
        { state := (generatedOptionAppendWordDescription emit final).start
          tape := tapeAtCells left (some bit :: right) } =
      { state := (generatedOptionAppendWordDescription emit final).start
        tape := tapeAtCells (emit bit :: left) right } := by
  cases final with
  | nil =>
      cases bit <;> cases right <;>
        simp [generatedOptionAppendWordDescription,
          FiniteTransducer.optionAppendWordTransitions,
          FiniteTransducer.copyAppendWordWriteTransitionsFrom,
          FiniteTransducer.optionAppendWordScanFalseTransition,
          FiniteTransducer.optionAppendWordScanTrueTransition,
          FiniteTransducer.copyAppendWordHalt,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]
  | cons first rest =>
      cases bit <;> cases right <;>
        simp [generatedOptionAppendWordDescription,
          FiniteTransducer.optionAppendWordTransitions,
          FiniteTransducer.copyAppendWordWriteTransitionsFrom,
          FiniteTransducer.optionAppendWordScanFalseTransition,
          FiniteTransducer.optionAppendWordScanTrueTransition,
          FiniteTransducer.copyAppendWordHalt,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]

theorem generatedOptionAppendWordDescription_step_blank
    (emit : Bool -> Option Bool) (bit : Bool) (rest : Word Bool)
    (left : List (Option Bool)) :
    (generatedOptionAppendWordDescription emit (bit :: rest)).runConfig 1
        { state :=
            (generatedOptionAppendWordDescription emit (bit :: rest)).start
          tape := tapeAtCells left [none] } =
      { state :=
          match rest with
          | [] =>
              (generatedOptionAppendWordDescription emit (bit :: rest)).halt
          | _ :: _ => 1
        tape := tapeAtCells (some bit :: left) [] } := by
  cases rest <;>
    simp [generatedOptionAppendWordDescription,
      FiniteTransducer.optionAppendWordTransitions,
      FiniteTransducer.copyAppendWordWriteTransitionsFrom,
      FiniteTransducer.copyAppendWordHalt,
      FiniteTransducer.optionAppendWordScanFalseTransition,
      FiniteTransducer.optionAppendWordScanTrueTransition,
      runConfig, stepConfig, lookupTransition, Matches, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem generatedOptionAppendWordDescription_run_scan
    (emit : Bool -> Option Bool) (final input : Word Bool)
    (left : List (Option Bool)) :
    (generatedOptionAppendWordDescription emit final).runConfig input.length
        { state := (generatedOptionAppendWordDescription emit final).start
          tape := tapeAtCells left
            (List.append (input.map some) [none]) } =
      { state := (generatedOptionAppendWordDescription emit final).start
        tape :=
          tapeAtCells
            (List.append (input.reverse.map emit) left)
            [none] } := by
  induction input generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        (generatedOptionAppendWordDescription emit final).runConfig rest.length
            ((generatedOptionAppendWordDescription emit final).runConfig 1
              { state :=
                  (generatedOptionAppendWordDescription emit final).start
                tape :=
                  tapeAtCells left
                    (some bit :: List.append (rest.map some) [none]) }) =
          { state := (generatedOptionAppendWordDescription emit final).start
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map emit) left)
                [none] }
      rw [generatedOptionAppendWordDescription_step_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (emit bit :: left)

theorem generatedOptionAppendWordDescription_run_to_write_boundary
    (emit : Bool -> Option Bool) (final input : Word Bool)
    (leftScratch : Nat) :
    (generatedOptionAppendWordDescription emit final).runConfig
        input.length
        { state := (generatedOptionAppendWordDescription emit final).start
          tape := FSTSourceTape input leftScratch } =
      { state := (generatedOptionAppendWordDescription emit final).start
        tape :=
          tapeAtCells
            (List.append (input.reverse.map emit)
              (List.replicate leftScratch (none : Option Bool)))
            [none] } := by
  simpa [FSTSourceTape, List.append_assoc] using
    generatedOptionAppendWordDescription_run_scan emit final input
      (List.replicate leftScratch (none : Option Bool))

theorem generatedOptionAppendWordDescription_writerRuns
    (emit : Bool -> Option Bool) (final : Word Bool) :
    AppendFinalWordWriterRuns
      (generatedOptionAppendWordDescription emit final) final := by
  intro left
  cases final with
  | nil =>
      simp [generatedOptionAppendWordDescription,
        FiniteTransducer.optionAppendWordTransitions,
        FiniteTransducer.copyAppendWordWriteTransitionsFrom,
        FiniteTransducer.optionAppendWordScanFalseTransition,
        FiniteTransducer.optionAppendWordScanTrueTransition,
        FiniteTransducer.copyAppendWordHalt,
        appendFinalWordWriteTargetTape,
        runConfig, stepConfig, lookupTransition, Matches, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons bit rest =>
      cases rest with
      | nil =>
          simp [generatedOptionAppendWordDescription,
            FiniteTransducer.optionAppendWordTransitions,
            FiniteTransducer.copyAppendWordWriteTransitionsFrom,
            FiniteTransducer.optionAppendWordScanFalseTransition,
            FiniteTransducer.optionAppendWordScanTrueTransition,
            FiniteTransducer.copyAppendWordHalt,
            appendFinalWordWriteTargetTape,
            runConfig, stepConfig, lookupTransition, Matches, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveRight]
      | cons next more =>
          rw [show
              FiniteTransducer.copyAppendWordHalt (bit :: next :: more) =
                1 + (next :: more).length by
            simp [FiniteTransducer.copyAppendWordHalt]
            omega]
          rw [runConfig_add]
          rw [generatedOptionAppendWordDescription_step_blank]
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.optionAppendWordScanFalseTransition emit
          let scanTrue : TransitionDescription :=
            FiniteTransducer.optionAppendWordScanTrueTransition emit
          have hpre :
              forall t : TransitionDescription,
                t ∈ [first, scanFalse, scanTrue] -> t.source < 1 := by
            intro t ht
            simp [first, scanFalse, scanTrue,
              FiniteTransducer.optionAppendWordScanFalseTransition,
              FiniteTransducer.optionAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;> simp
          have htail :=
            copyAppendWordWriteTransitionsFrom_run_with_pre
              [first, scanFalse, scanTrue]
              1 0 (next :: more) (some bit :: left) hpre
          simpa [generatedOptionAppendWordDescription,
            FiniteTransducer.optionAppendWordTransitions,
            FiniteTransducer.copyAppendWordWriteTransitionsFrom,
            FiniteTransducer.copyAppendWordHalt,
            FiniteTransducer.optionAppendWordScanFalseTransition,
            FiniteTransducer.optionAppendWordScanTrueTransition,
            first, scanFalse, scanTrue, appendFinalWordWriteTargetTape,
            tapeAtCells, List.reverse_cons, List.map_append,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using htail

theorem generatedOptionAppendWordDescription_wellFormed
    (emit : Bool -> Option Bool) (final : Word Bool) :
    (generatedOptionAppendWordDescription emit final).WellFormed := by
  cases final with
  | nil =>
      let first : TransitionDescription :=
        { source := 0
          read := none
          write := none
          move := Direction.right
          target := 1 }
      have htrans :
          (generatedOptionAppendWordDescription emit []).transitions =
            [first,
              FiniteTransducer.optionAppendWordScanFalseTransition emit,
              FiniteTransducer.optionAppendWordScanTrueTransition emit] := by
        rfl
      refine
        ⟨by simp [generatedOptionAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt],
          by simp [generatedOptionAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt],
          by simp [generatedOptionAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt], ?_, ?_⟩
      · intro t ht
        rw [htrans] at ht
        simp [first, FiniteTransducer.optionAppendWordScanFalseTransition,
          FiniteTransducer.optionAppendWordScanTrueTransition] at ht
        rcases ht with ht | ht | ht <;> subst t <;>
          simp [TransitionDescription.WellFormed,
            generatedOptionAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt]
      · intro t u ht hu hkey
        rw [htrans] at ht hu
        exact
          FiniteTransducer.optionAppendWordPrefix_deterministic
            emit first t u rfl rfl ht hu hkey
  | cons bit rest =>
      cases rest with
      | nil =>
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          have htrans :
              (generatedOptionAppendWordDescription emit [bit]).transitions =
                [first,
                  FiniteTransducer.optionAppendWordScanFalseTransition emit,
                  FiniteTransducer.optionAppendWordScanTrueTransition emit] := by
            rfl
          refine
            ⟨by simp [generatedOptionAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt],
              by simp [generatedOptionAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt],
              by simp [generatedOptionAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt], ?_, ?_⟩
          · intro t ht
            rw [htrans] at ht
            simp [first, FiniteTransducer.optionAppendWordScanFalseTransition,
              FiniteTransducer.optionAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;>
              simp [TransitionDescription.WellFormed,
                generatedOptionAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt]
          · intro t u ht hu hkey
            rw [htrans] at ht hu
            exact
              FiniteTransducer.optionAppendWordPrefix_deterministic
                emit first t u rfl rfl ht hu hkey
      | cons next more =>
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.optionAppendWordScanFalseTransition emit
          let scanTrue : TransitionDescription :=
            FiniteTransducer.optionAppendWordScanTrueTransition emit
          have htrans :
              (generatedOptionAppendWordDescription emit
                  (bit :: next :: more)).transitions =
                List.append [first, scanFalse, scanTrue]
                  (FiniteTransducer.copyAppendWordWriteTransitionsFrom
                    1
                    (FiniteTransducer.copyAppendWordHalt
                      (bit :: next :: more))
                    (next :: more)) := by
            rfl
          have hhalt :
              FiniteTransducer.copyAppendWordHalt (bit :: next :: more) =
                1 + (next :: more).length := by
            simp [FiniteTransducer.copyAppendWordHalt]
            omega
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · simp [generatedOptionAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · simp [generatedOptionAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · simp [generatedOptionAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · intro t ht
            rw [htrans] at ht
            rcases List.mem_append.mp ht with ht | ht
            · simp [first, scanFalse, scanTrue,
                FiniteTransducer.optionAppendWordScanFalseTransition,
                FiniteTransducer.optionAppendWordScanTrueTransition] at ht
              rcases ht with ht | ht | ht <;> subst t <;>
                constructor <;> simp [generatedOptionAppendWordDescription,
                  FiniteTransducer.copyAppendWordHalt]
            · have ht' :
                t ∈ FiniteTransducer.copyAppendWordWriteTransitionsFrom
                  1 (1 + (next :: more).length) (next :: more) := by
                simpa [hhalt] using ht
              have htwf :=
                FiniteTransducer.copyAppendWordWriteTransitionsFrom_wellFormed
                  1 (next :: more) t ht'
              simpa [generatedOptionAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htwf
          · intro t u ht hu hkey
            rw [htrans] at ht hu
            rcases List.mem_append.mp ht with ht | ht <;>
              rcases List.mem_append.mp hu with hu | hu
            · exact
                FiniteTransducer.optionAppendWordPrefix_deterministic
                  emit first t u rfl rfl ht hu hkey
            · simp [first, scanFalse, scanTrue,
                FiniteTransducer.optionAppendWordScanFalseTransition,
                FiniteTransducer.optionAppendWordScanTrueTransition] at ht
              rcases ht with ht | ht | ht <;> subst t
              all_goals
                have hu' :
                  u ∈ FiniteTransducer.copyAppendWordWriteTransitionsFrom
                    1 (1 + (next :: more).length) (next :: more) := by
                  simpa [hhalt] using hu
                have hubounds :=
                  FiniteTransducer.copyAppendWordWriteTransitionsFrom_source_bounds
                    1 (1 + (next :: more).length) (next :: more) u hu'
                have husource : u.source = 0 := hkey.left.symm
                omega
            · simp [first, scanFalse, scanTrue,
                FiniteTransducer.optionAppendWordScanFalseTransition,
                FiniteTransducer.optionAppendWordScanTrueTransition] at hu
              rcases hu with hu | hu | hu <;> subst u
              all_goals
                have ht' :
                  t ∈ FiniteTransducer.copyAppendWordWriteTransitionsFrom
                    1 (1 + (next :: more).length) (next :: more) := by
                  simpa [hhalt] using ht
                have htbounds :=
                  FiniteTransducer.copyAppendWordWriteTransitionsFrom_source_bounds
                    1 (1 + (next :: more).length) (next :: more) t ht'
                have htsource : t.source = 0 := hkey.left
                omega
            · have ht' :
                t ∈ FiniteTransducer.copyAppendWordWriteTransitionsFrom
                  1 (1 + (next :: more).length) (next :: more) := by
                simpa [hhalt] using ht
              have hu' :
                u ∈ FiniteTransducer.copyAppendWordWriteTransitionsFrom
                  1 (1 + (next :: more).length) (next :: more) := by
                simpa [hhalt] using hu
              exact
                FiniteTransducer.copyAppendWordWriteTransitionsFrom_deterministic
                  1 (next :: more) t u ht' hu' hkey

theorem generatedOptionAppendWordDescription_haltTransitionFree
    (emit : Bool -> Option Bool) (final : Word Bool) :
    (generatedOptionAppendWordDescription emit final).HaltTransitionFree := by
  cases final with
  | nil =>
      let first : TransitionDescription :=
        { source := 0
          read := none
          write := none
          move := Direction.right
          target := 1 }
      have htrans :
          (generatedOptionAppendWordDescription emit []).transitions =
            [first,
              FiniteTransducer.optionAppendWordScanFalseTransition emit,
              FiniteTransducer.optionAppendWordScanTrueTransition emit] := by
        rfl
      intro t ht
      rw [htrans] at ht
      simp [first, FiniteTransducer.optionAppendWordScanFalseTransition,
        FiniteTransducer.optionAppendWordScanTrueTransition] at ht
      rcases ht with ht | ht | ht <;> subst t <;>
        simp [generatedOptionAppendWordDescription,
          FiniteTransducer.copyAppendWordHalt]
  | cons bit rest =>
      cases rest with
      | nil =>
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          have htrans :
              (generatedOptionAppendWordDescription emit [bit]).transitions =
                [first,
                  FiniteTransducer.optionAppendWordScanFalseTransition emit,
                  FiniteTransducer.optionAppendWordScanTrueTransition emit] := by
            rfl
          intro t ht
          rw [htrans] at ht
          simp [first, FiniteTransducer.optionAppendWordScanFalseTransition,
            FiniteTransducer.optionAppendWordScanTrueTransition] at ht
          rcases ht with ht | ht | ht <;> subst t <;>
            simp [generatedOptionAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
      | cons next more =>
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.optionAppendWordScanFalseTransition emit
          let scanTrue : TransitionDescription :=
            FiniteTransducer.optionAppendWordScanTrueTransition emit
          have htrans :
              (generatedOptionAppendWordDescription emit
                  (bit :: next :: more)).transitions =
                List.append [first, scanFalse, scanTrue]
                  (FiniteTransducer.copyAppendWordWriteTransitionsFrom
                    1
                    (FiniteTransducer.copyAppendWordHalt
                      (bit :: next :: more))
                    (next :: more)) := by
            rfl
          have hhalt :
              FiniteTransducer.copyAppendWordHalt (bit :: next :: more) =
                1 + (next :: more).length := by
            simp [FiniteTransducer.copyAppendWordHalt]
            omega
          intro t ht
          rw [htrans] at ht
          rcases List.mem_append.mp ht with ht | ht
          · simp [first, scanFalse, scanTrue,
              FiniteTransducer.optionAppendWordScanFalseTransition,
              FiniteTransducer.optionAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;>
              simp [generatedOptionAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt]
          · intro hsource
            have ht' :
                t ∈ FiniteTransducer.copyAppendWordWriteTransitionsFrom
                  1 (1 + (next :: more).length) (next :: more) := by
              simpa [hhalt] using ht
            have hbounds :=
              FiniteTransducer.copyAppendWordWriteTransitionsFrom_source_bounds
                1 (1 + (next :: more).length) (next :: more) t ht'
            have hsourceEq :
                t.source = 1 + (next :: more).length := by
              simpa [generatedOptionAppendWordDescription, hhalt] using hsource
            omega

theorem generatedOptionAppendWordDescription_subroutineReady
    (emit : Bool -> Option Bool) (final : Word Bool) :
    (generatedOptionAppendWordDescription emit final).SubroutineReady :=
  ⟨generatedOptionAppendWordDescription_wellFormed emit final,
    generatedOptionAppendWordDescription_haltTransitionFree emit final⟩

theorem generatedOptionAppendWordDescription_haltsFrom_FSTSourceTape
    (emit : Bool -> Option Bool) (final input : Word Bool)
    (leftScratch : Nat) :
    (generatedOptionAppendWordDescription emit final).HaltsFromTape
      (FSTSourceTape input leftScratch)
      (FSTOptionAppendFinalWordTargetTape emit input final leftScratch) := by
  refine ⟨input.length + FiniteTransducer.copyAppendWordHalt final, ?_⟩
  change
    ((generatedOptionAppendWordDescription emit final).runConfig
        (input.length + FiniteTransducer.copyAppendWordHalt final)
        { state := (generatedOptionAppendWordDescription emit final).start
          tape := FSTSourceTape input leftScratch }).state =
      (generatedOptionAppendWordDescription emit final).halt ∧
    ((generatedOptionAppendWordDescription emit final).runConfig
        (input.length + FiniteTransducer.copyAppendWordHalt final)
        { state := (generatedOptionAppendWordDescription emit final).start
          tape := FSTSourceTape input leftScratch }).tape =
      FSTOptionAppendFinalWordTargetTape emit input final leftScratch
  rw [runConfig_add]
  rw [generatedOptionAppendWordDescription_run_to_write_boundary]
  have hwrite :=
    generatedOptionAppendWordDescription_writerRuns emit final
      (List.append (input.reverse.map emit)
        (List.replicate leftScratch (none : Option Bool)))
  constructor
  · simpa [FSTOptionAppendFinalWordTargetTape] using
      congrArg MachineDescription.Configuration.state hwrite
  · simpa [FSTOptionAppendFinalWordTargetTape] using
      congrArg MachineDescription.Configuration.tape hwrite

theorem optionAppendFinalTransducer_compiledByGeneratedDescription
    (emit : Bool -> Option Bool) (final : Word Bool) :
    ExactCompiledByDescription
      (optionAppendFinalTransducer emit final)
      (generatedOptionAppendWordDescription emit final)
      (fun input _output leftScratch =>
        FSTOptionAppendFinalWordTargetTape emit input final leftScratch) := by
  constructor
  · exact generatedOptionAppendWordDescription_subroutineReady emit final
  · intro input output leftScratch hrun
    have hout := optionAppendFinalTransducer_run emit final input
    change
      (optionAppendFinalTransducer emit final).runFromStart
          (input.length + 1) input =
        some ((optionAppendFinalTransducer emit final).halt, output) at hrun
    rw [hout] at hrun
    cases hrun
    exact generatedOptionAppendWordDescription_haltsFrom_FSTSourceTape
      emit final input leftScratch

end FiniteTransducers
end CommonGround

end Computability
end FoC
