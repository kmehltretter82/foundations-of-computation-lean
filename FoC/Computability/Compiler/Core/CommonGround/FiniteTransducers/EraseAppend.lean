import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.AppendWord

set_option doc.verso true

/-!
# Erase-and-append finite transducer compiler

This module proves a deletion-oriented compiler slice: each consumed input bit
is erased, then an arbitrary generated final word is written at the trailing
blank boundary.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def eraseAppendFinalTransducer
    (final : Word Bool) : FiniteTransducer :=
  bitwiseOutputTransducer (fun _bit => []) final

theorem bitwiseOutput_empty
    (input : Word Bool) :
    bitwiseOutput (fun _bit => []) input = [] := by
  induction input with
  | nil =>
      rfl
  | cons _bit rest ih =>
      simp [bitwiseOutput, ih]

theorem eraseAppendFinalTransducer_wellFormed
    (final : Word Bool) :
    (eraseAppendFinalTransducer final).WellFormed := by
  exact bitwiseOutputTransducer_wellFormed (fun _bit => []) final

theorem eraseAppendFinalTransducer_run
    (final input : Word Bool) :
    (eraseAppendFinalTransducer final).runFromStart
        (input.length + 1) input =
      some ((eraseAppendFinalTransducer final).halt, final) := by
  rw [eraseAppendFinalTransducer, bitwiseOutputTransducer_run,
    bitwiseOutput_empty]
  rfl

theorem eraseAppendFinalTransducer_runsToOutput
    (final input : Word Bool) :
    (eraseAppendFinalTransducer final).RunsToOutput input final := by
  exact eraseAppendFinalTransducer_run final input

namespace FiniteTransducer

def eraseAppendWordScanFalseTransition : TransitionDescription :=
  { source := 0
    read := some false
    write := none
    move := Direction.right
    target := 0 }

def eraseAppendWordScanTrueTransition : TransitionDescription :=
  { source := 0
    read := some true
    write := none
    move := Direction.right
    target := 0 }

def eraseAppendWordTransitions
    (final : Word Bool) : List TransitionDescription :=
  match copyAppendWordWriteTransitionsFrom 0 (copyAppendWordHalt final) final with
  | [] =>
      [ { source := 0
          read := none
          write := none
          move := Direction.right
          target := copyAppendWordHalt final }
      , eraseAppendWordScanFalseTransition
      , eraseAppendWordScanTrueTransition ]
  | first :: rest =>
      first :: eraseAppendWordScanFalseTransition ::
        eraseAppendWordScanTrueTransition :: rest

theorem eraseAppendWordPrefix_deterministic
    (first t u : TransitionDescription)
    (hfirstSource : first.source = 0)
    (hfirstRead : first.read = none)
    (ht :
      t ∈ [first, eraseAppendWordScanFalseTransition,
        eraseAppendWordScanTrueTransition])
    (hu :
      u ∈ [first, eraseAppendWordScanFalseTransition,
        eraseAppendWordScanTrueTransition])
    (hkey : TransitionDescription.SameKey t u) :
    TransitionDescription.SameAction t u := by
  simp [eraseAppendWordScanFalseTransition,
    eraseAppendWordScanTrueTransition] at ht hu
  rcases ht with ht | ht | ht <;>
    rcases hu with hu | hu | hu <;>
    subst t <;> subst u <;>
    simp [TransitionDescription.SameKey,
      TransitionDescription.SameAction, hfirstSource, hfirstRead] at hkey ⊢

end FiniteTransducer

def generatedEraseAppendWordDescription
    (final : Word Bool) : MachineDescription where
  stateCount := FiniteTransducer.copyAppendWordHalt final + 1
  start := 0
  halt := FiniteTransducer.copyAppendWordHalt final
  transitions := FiniteTransducer.eraseAppendWordTransitions final

def FSTEraseAppendFinalWordTargetTape
    (input final : Word Bool) (leftScratch : Nat) : Tape Bool :=
  appendFinalWordWriteTargetTape
    (List.append
      (input.reverse.map (fun _bit => (none : Option Bool)))
      (List.replicate leftScratch (none : Option Bool)))
    final

theorem filterMap_bool_none
    (input : Word Bool) :
    List.filterMap (fun _bit : Bool => (none : Option Bool)) input =
      [] := by
  induction input with
  | nil =>
      rfl
  | cons _bit rest ih =>
      simp [ih]

theorem FSTEraseAppendFinalWordTargetTape_normalizedOutput
    (input final : Word Bool) (leftScratch : Nat) :
    Tape.normalizedOutput
        (FSTEraseAppendFinalWordTargetTape input final leftScratch) =
      final := by
  cases final with
  | nil =>
      rw [FSTEraseAppendFinalWordTargetTape,
        appendFinalWordWriteTargetTape, tapeAtCells_normalizedOutput]
      simp [Function.comp_def, List.filterMap_append,
        filterMap_bool_none]
  | cons bit rest =>
      rw [FSTEraseAppendFinalWordTargetTape,
        appendFinalWordWriteTargetTape, tapeAtCells_normalizedOutput]
      simp [Function.comp_def, List.filterMap_append,
        List.reverse_append, List.map_append, List.append_assoc,
        filterMap_bool_none]

theorem generatedEraseAppendWordDescription_step_bit
    (final : Word Bool) (bit : Bool)
    (left right : List (Option Bool)) :
    (generatedEraseAppendWordDescription final).runConfig 1
        { state := (generatedEraseAppendWordDescription final).start
          tape := tapeAtCells left (some bit :: right) } =
      { state := (generatedEraseAppendWordDescription final).start
        tape := tapeAtCells (none :: left) right } := by
  cases final with
  | nil =>
      cases bit <;> cases right <;>
        simp [generatedEraseAppendWordDescription,
          FiniteTransducer.eraseAppendWordTransitions,
          FiniteTransducer.copyAppendWordWriteTransitionsFrom,
          FiniteTransducer.eraseAppendWordScanFalseTransition,
          FiniteTransducer.eraseAppendWordScanTrueTransition,
          FiniteTransducer.copyAppendWordHalt,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]
  | cons first rest =>
      cases bit <;> cases right <;>
        simp [generatedEraseAppendWordDescription,
          FiniteTransducer.eraseAppendWordTransitions,
          FiniteTransducer.copyAppendWordWriteTransitionsFrom,
          FiniteTransducer.eraseAppendWordScanFalseTransition,
          FiniteTransducer.eraseAppendWordScanTrueTransition,
          FiniteTransducer.copyAppendWordHalt,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]

theorem generatedEraseAppendWordDescription_step_blank
    (bit : Bool) (rest : Word Bool) (left : List (Option Bool)) :
    (generatedEraseAppendWordDescription (bit :: rest)).runConfig 1
        { state := (generatedEraseAppendWordDescription (bit :: rest)).start
          tape := tapeAtCells left [none] } =
      { state :=
          match rest with
          | [] => (generatedEraseAppendWordDescription (bit :: rest)).halt
          | _ :: _ => 1
        tape := tapeAtCells (some bit :: left) [] } := by
  cases rest <;>
    simp [generatedEraseAppendWordDescription,
      FiniteTransducer.eraseAppendWordTransitions,
      FiniteTransducer.copyAppendWordWriteTransitionsFrom,
      FiniteTransducer.copyAppendWordHalt,
      FiniteTransducer.eraseAppendWordScanFalseTransition,
      FiniteTransducer.eraseAppendWordScanTrueTransition,
      runConfig, stepConfig, lookupTransition, Matches, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem generatedEraseAppendWordDescription_run_scan
    (final input : Word Bool) (left : List (Option Bool)) :
    (generatedEraseAppendWordDescription final).runConfig input.length
        { state := (generatedEraseAppendWordDescription final).start
          tape := tapeAtCells left
            (List.append (input.map some) [none]) } =
      { state := (generatedEraseAppendWordDescription final).start
        tape :=
          tapeAtCells
            (List.append
              (input.reverse.map (fun _bit => (none : Option Bool))) left)
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
        (generatedEraseAppendWordDescription final).runConfig rest.length
            ((generatedEraseAppendWordDescription final).runConfig 1
              { state := (generatedEraseAppendWordDescription final).start
                tape :=
                  tapeAtCells left
                    (some bit :: List.append (rest.map some) [none]) }) =
          { state := (generatedEraseAppendWordDescription final).start
            tape :=
              tapeAtCells
                (List.append
                  ((bit :: rest).reverse.map
                    (fun _bit => (none : Option Bool))) left)
                [none] }
      rw [generatedEraseAppendWordDescription_step_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (none :: left)

theorem generatedEraseAppendWordDescription_run_to_write_boundary
    (final input : Word Bool) (leftScratch : Nat) :
    (generatedEraseAppendWordDescription final).runConfig
        input.length
        { state := (generatedEraseAppendWordDescription final).start
          tape := FSTSourceTape input leftScratch } =
      { state := (generatedEraseAppendWordDescription final).start
        tape :=
          tapeAtCells
            (List.append
              (input.reverse.map (fun _bit => (none : Option Bool)))
              (List.replicate leftScratch (none : Option Bool)))
            [none] } := by
  simpa [FSTSourceTape, List.append_assoc] using
    generatedEraseAppendWordDescription_run_scan final input
      (List.replicate leftScratch (none : Option Bool))

theorem generatedEraseAppendWordDescription_writerRuns
    (final : Word Bool) :
    AppendFinalWordWriterRuns
      (generatedEraseAppendWordDescription final) final := by
  intro left
  cases final with
  | nil =>
      simp [generatedEraseAppendWordDescription,
        FiniteTransducer.eraseAppendWordTransitions,
        FiniteTransducer.copyAppendWordWriteTransitionsFrom,
        FiniteTransducer.eraseAppendWordScanFalseTransition,
        FiniteTransducer.eraseAppendWordScanTrueTransition,
        FiniteTransducer.copyAppendWordHalt,
        appendFinalWordWriteTargetTape,
        runConfig, stepConfig, lookupTransition, Matches, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons bit rest =>
      cases rest with
      | nil =>
          simp [generatedEraseAppendWordDescription,
            FiniteTransducer.eraseAppendWordTransitions,
            FiniteTransducer.copyAppendWordWriteTransitionsFrom,
            FiniteTransducer.eraseAppendWordScanFalseTransition,
            FiniteTransducer.eraseAppendWordScanTrueTransition,
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
          rw [generatedEraseAppendWordDescription_step_blank]
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.eraseAppendWordScanFalseTransition
          let scanTrue : TransitionDescription :=
            FiniteTransducer.eraseAppendWordScanTrueTransition
          have hpre :
              forall t : TransitionDescription,
                t ∈ [first, scanFalse, scanTrue] -> t.source < 1 := by
            intro t ht
            simp [first, scanFalse, scanTrue,
              FiniteTransducer.eraseAppendWordScanFalseTransition,
              FiniteTransducer.eraseAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;> simp
          have htail :=
            copyAppendWordWriteTransitionsFrom_run_with_pre
              [first, scanFalse, scanTrue]
              1 0 (next :: more) (some bit :: left) hpre
          simpa [generatedEraseAppendWordDescription,
            FiniteTransducer.eraseAppendWordTransitions,
            FiniteTransducer.copyAppendWordWriteTransitionsFrom,
            FiniteTransducer.copyAppendWordHalt,
            FiniteTransducer.eraseAppendWordScanFalseTransition,
            FiniteTransducer.eraseAppendWordScanTrueTransition,
            first, scanFalse, scanTrue, appendFinalWordWriteTargetTape,
            tapeAtCells, List.reverse_cons, List.map_append,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using htail

theorem generatedEraseAppendWordDescription_wellFormed
    (final : Word Bool) :
    (generatedEraseAppendWordDescription final).WellFormed := by
  cases final with
  | nil =>
      let first : TransitionDescription :=
        { source := 0
          read := none
          write := none
          move := Direction.right
          target := 1 }
      have htrans :
          (generatedEraseAppendWordDescription []).transitions =
            [first,
              FiniteTransducer.eraseAppendWordScanFalseTransition,
              FiniteTransducer.eraseAppendWordScanTrueTransition] := by
        rfl
      refine
        ⟨by simp [generatedEraseAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt],
          by simp [generatedEraseAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt],
          by simp [generatedEraseAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt], ?_, ?_⟩
      · intro t ht
        rw [htrans] at ht
        simp [first, FiniteTransducer.eraseAppendWordScanFalseTransition,
          FiniteTransducer.eraseAppendWordScanTrueTransition] at ht
        rcases ht with ht | ht | ht <;> subst t <;>
          simp [TransitionDescription.WellFormed,
            generatedEraseAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt]
      · intro t u ht hu hkey
        rw [htrans] at ht hu
        exact
          FiniteTransducer.eraseAppendWordPrefix_deterministic
            first t u rfl rfl ht hu hkey
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
              (generatedEraseAppendWordDescription [bit]).transitions =
                [first,
                  FiniteTransducer.eraseAppendWordScanFalseTransition,
                  FiniteTransducer.eraseAppendWordScanTrueTransition] := by
            rfl
          refine
            ⟨by simp [generatedEraseAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt],
              by simp [generatedEraseAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt],
              by simp [generatedEraseAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt], ?_, ?_⟩
          · intro t ht
            rw [htrans] at ht
            simp [first, FiniteTransducer.eraseAppendWordScanFalseTransition,
              FiniteTransducer.eraseAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;>
              simp [TransitionDescription.WellFormed,
                generatedEraseAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt]
          · intro t u ht hu hkey
            rw [htrans] at ht hu
            exact
              FiniteTransducer.eraseAppendWordPrefix_deterministic
                first t u rfl rfl ht hu hkey
      | cons next more =>
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.eraseAppendWordScanFalseTransition
          let scanTrue : TransitionDescription :=
            FiniteTransducer.eraseAppendWordScanTrueTransition
          have htrans :
              (generatedEraseAppendWordDescription
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
          · simp [generatedEraseAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · simp [generatedEraseAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · simp [generatedEraseAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · intro t ht
            rw [htrans] at ht
            rcases List.mem_append.mp ht with ht | ht
            · simp [first, scanFalse, scanTrue,
                FiniteTransducer.eraseAppendWordScanFalseTransition,
                FiniteTransducer.eraseAppendWordScanTrueTransition] at ht
              rcases ht with ht | ht | ht <;> subst t <;>
                constructor <;> simp [generatedEraseAppendWordDescription,
                  FiniteTransducer.copyAppendWordHalt]
            · have ht' :
                t ∈ FiniteTransducer.copyAppendWordWriteTransitionsFrom
                  1 (1 + (next :: more).length) (next :: more) := by
                simpa [hhalt] using ht
              have htwf :=
                FiniteTransducer.copyAppendWordWriteTransitionsFrom_wellFormed
                  1 (next :: more) t ht'
              simpa [generatedEraseAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htwf
          · intro t u ht hu hkey
            rw [htrans] at ht hu
            rcases List.mem_append.mp ht with ht | ht <;>
              rcases List.mem_append.mp hu with hu | hu
            · exact
                FiniteTransducer.eraseAppendWordPrefix_deterministic
                  first t u rfl rfl ht hu hkey
            · simp [first, scanFalse, scanTrue,
                FiniteTransducer.eraseAppendWordScanFalseTransition,
                FiniteTransducer.eraseAppendWordScanTrueTransition] at ht
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
                FiniteTransducer.eraseAppendWordScanFalseTransition,
                FiniteTransducer.eraseAppendWordScanTrueTransition] at hu
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

theorem generatedEraseAppendWordDescription_haltTransitionFree
    (final : Word Bool) :
    (generatedEraseAppendWordDescription final).HaltTransitionFree := by
  cases final with
  | nil =>
      exact transition_notFrom_of_all
        (l := (generatedEraseAppendWordDescription []).transitions)
        (state := (generatedEraseAppendWordDescription []).halt)
        (by native_decide)
  | cons bit rest =>
      cases rest with
      | nil =>
          cases bit
          · exact transition_notFrom_of_all
              (l := (generatedEraseAppendWordDescription [false]).transitions)
              (state := (generatedEraseAppendWordDescription [false]).halt)
              (by native_decide)
          · exact transition_notFrom_of_all
              (l := (generatedEraseAppendWordDescription [true]).transitions)
              (state := (generatedEraseAppendWordDescription [true]).halt)
              (by native_decide)
      | cons next more =>
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.eraseAppendWordScanFalseTransition
          let scanTrue : TransitionDescription :=
            FiniteTransducer.eraseAppendWordScanTrueTransition
          have htrans :
              (generatedEraseAppendWordDescription
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
              FiniteTransducer.eraseAppendWordScanFalseTransition,
              FiniteTransducer.eraseAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;>
              simp [generatedEraseAppendWordDescription,
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
              simpa [generatedEraseAppendWordDescription, hhalt] using hsource
            omega

theorem generatedEraseAppendWordDescription_subroutineReady
    (final : Word Bool) :
    (generatedEraseAppendWordDescription final).SubroutineReady :=
  ⟨generatedEraseAppendWordDescription_wellFormed final,
    generatedEraseAppendWordDescription_haltTransitionFree final⟩

theorem generatedEraseAppendWordDescription_haltsFrom_FSTSourceTape
    (final input : Word Bool) (leftScratch : Nat) :
    (generatedEraseAppendWordDescription final).HaltsFromTape
      (FSTSourceTape input leftScratch)
      (FSTEraseAppendFinalWordTargetTape input final leftScratch) := by
  refine ⟨input.length + FiniteTransducer.copyAppendWordHalt final, ?_⟩
  change
    ((generatedEraseAppendWordDescription final).runConfig
        (input.length + FiniteTransducer.copyAppendWordHalt final)
        { state := (generatedEraseAppendWordDescription final).start
          tape := FSTSourceTape input leftScratch }).state =
      (generatedEraseAppendWordDescription final).halt ∧
    ((generatedEraseAppendWordDescription final).runConfig
        (input.length + FiniteTransducer.copyAppendWordHalt final)
        { state := (generatedEraseAppendWordDescription final).start
          tape := FSTSourceTape input leftScratch }).tape =
      FSTEraseAppendFinalWordTargetTape input final leftScratch
  rw [runConfig_add]
  rw [generatedEraseAppendWordDescription_run_to_write_boundary]
  have hwrite :=
    generatedEraseAppendWordDescription_writerRuns final
      (List.append
        (input.reverse.map (fun _bit => (none : Option Bool)))
        (List.replicate leftScratch (none : Option Bool)))
  constructor
  · simpa [FSTEraseAppendFinalWordTargetTape] using
      congrArg MachineDescription.Configuration.state hwrite
  · simpa [FSTEraseAppendFinalWordTargetTape] using
      congrArg MachineDescription.Configuration.tape hwrite

theorem eraseAppendFinalTransducer_compiledByGeneratedDescription
    (final : Word Bool) :
    ExactCompiledByDescription
      (eraseAppendFinalTransducer final)
      (generatedEraseAppendWordDescription final)
      (fun input _output leftScratch =>
        FSTEraseAppendFinalWordTargetTape input final leftScratch) := by
  constructor
  · exact generatedEraseAppendWordDescription_subroutineReady final
  · intro input output leftScratch hrun
    have hout := eraseAppendFinalTransducer_run final input
    change
      (eraseAppendFinalTransducer final).runFromStart
          (input.length + 1) input =
        some ((eraseAppendFinalTransducer final).halt, output) at hrun
    rw [hout] at hrun
    cases hrun
    exact generatedEraseAppendWordDescription_haltsFrom_FSTSourceTape
      final input leftScratch

end FiniteTransducers
end CommonGround

end Computability
end FoC
