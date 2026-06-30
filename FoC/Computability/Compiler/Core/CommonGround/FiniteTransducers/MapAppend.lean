import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.AppendWord

set_option doc.verso true

/-!
# Length-preserving bit-map FST compiler

This module extends the append-word compiler slice from copying input bits to
rewriting each input bit through a Boolean map before appending a generated
final word.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def bitMapAppendFinalTransducer
    (emit : Bool -> Bool) (final : Word Bool) :
    FiniteTransducer :=
  bitwiseOutputTransducer (fun bit => [emit bit]) final

theorem bitwiseOutput_singleton_map
    (emit : Bool -> Bool) (input : Word Bool) :
    bitwiseOutput (fun bit => [emit bit]) input = input.map emit := by
  induction input with
  | nil =>
      rfl
  | cons bit rest ih =>
      simp [bitwiseOutput, ih]

theorem bitMapAppendFinalTransducer_wellFormed
    (emit : Bool -> Bool) (final : Word Bool) :
    (bitMapAppendFinalTransducer emit final).WellFormed := by
  exact bitwiseOutputTransducer_wellFormed (fun bit => [emit bit]) final

theorem bitMapAppendFinalTransducer_run
    (emit : Bool -> Bool) (final input : Word Bool) :
    (bitMapAppendFinalTransducer emit final).runFromStart
        (input.length + 1) input =
      some ((bitMapAppendFinalTransducer emit final).halt,
        List.append (input.map emit) final) := by
  rw [bitMapAppendFinalTransducer, bitwiseOutputTransducer_run,
    bitwiseOutput_singleton_map]

theorem bitMapAppendFinalTransducer_runsToOutput
    (emit : Bool -> Bool) (final input : Word Bool) :
    (bitMapAppendFinalTransducer emit final).RunsToOutput
      input (List.append (input.map emit) final) := by
  exact bitMapAppendFinalTransducer_run emit final input

namespace FiniteTransducer

def mapAppendWordScanFalseTransition
    (emit : Bool -> Bool) : TransitionDescription :=
  { source := 0
    read := some false
    write := some (emit false)
    move := Direction.right
    target := 0 }

def mapAppendWordScanTrueTransition
    (emit : Bool -> Bool) : TransitionDescription :=
  { source := 0
    read := some true
    write := some (emit true)
    move := Direction.right
    target := 0 }

def mapAppendWordTransitions
    (emit : Bool -> Bool) (final : Word Bool) :
    List TransitionDescription :=
  match copyAppendWordWriteTransitionsFrom 0 (copyAppendWordHalt final) final with
  | [] =>
      [ { source := 0
          read := none
          write := none
          move := Direction.right
          target := copyAppendWordHalt final }
      , mapAppendWordScanFalseTransition emit
      , mapAppendWordScanTrueTransition emit ]
  | first :: rest =>
      first :: mapAppendWordScanFalseTransition emit ::
        mapAppendWordScanTrueTransition emit :: rest

theorem mapAppendWordPrefix_deterministic
    (emit : Bool -> Bool) (first t u : TransitionDescription)
    (hfirstSource : first.source = 0)
    (hfirstRead : first.read = none)
    (ht :
      t ∈ [first, mapAppendWordScanFalseTransition emit,
        mapAppendWordScanTrueTransition emit])
    (hu :
      u ∈ [first, mapAppendWordScanFalseTransition emit,
        mapAppendWordScanTrueTransition emit])
    (hkey : TransitionDescription.SameKey t u) :
    TransitionDescription.SameAction t u := by
  simp [mapAppendWordScanFalseTransition,
    mapAppendWordScanTrueTransition] at ht hu
  rcases ht with ht | ht | ht <;>
    rcases hu with hu | hu | hu <;>
    subst t <;> subst u <;>
    simp [TransitionDescription.SameKey,
      TransitionDescription.SameAction, hfirstSource, hfirstRead] at hkey ⊢

end FiniteTransducer

def generatedMapAppendWordDescription
    (emit : Bool -> Bool) (final : Word Bool) :
    MachineDescription where
  stateCount := FiniteTransducer.copyAppendWordHalt final + 1
  start := 0
  halt := FiniteTransducer.copyAppendWordHalt final
  transitions := FiniteTransducer.mapAppendWordTransitions emit final

theorem generatedMapAppendWordDescription_id_eq_appendWord
    (final : Word Bool) :
    generatedMapAppendWordDescription (fun bit => bit) final =
      generatedAppendWordDescription final := by
  cases h : FiniteTransducer.copyAppendWordWriteTransitionsFrom 0
      (FiniteTransducer.copyAppendWordHalt final) final with
  | nil =>
      simp [generatedMapAppendWordDescription, generatedAppendWordDescription,
        FiniteTransducer.mapAppendWordTransitions,
        FiniteTransducer.copyAppendWordTransitions,
        FiniteTransducer.mapAppendWordScanFalseTransition,
        FiniteTransducer.mapAppendWordScanTrueTransition,
        FiniteTransducer.copyAppendWordScanFalseTransition,
        FiniteTransducer.copyAppendWordScanTrueTransition, h]
  | cons _first _rest =>
      simp [generatedMapAppendWordDescription, generatedAppendWordDescription,
        FiniteTransducer.mapAppendWordTransitions,
        FiniteTransducer.copyAppendWordTransitions,
        FiniteTransducer.mapAppendWordScanFalseTransition,
        FiniteTransducer.mapAppendWordScanTrueTransition,
        FiniteTransducer.copyAppendWordScanFalseTransition,
        FiniteTransducer.copyAppendWordScanTrueTransition, h]

def FSTMapAppendFinalWordTargetTape
    (emit : Bool -> Bool) (input final : Word Bool)
    (leftScratch : Nat) : Tape Bool :=
  appendFinalWordWriteTargetTape
    (List.append ((input.map emit).reverse.map some)
      (List.replicate leftScratch (none : Option Bool)))
    final

theorem FSTMapAppendFinalWordTargetTape_normalizedOutput
    (emit : Bool -> Bool) (input final : Word Bool)
    (leftScratch : Nat) :
    Tape.normalizedOutput
        (FSTMapAppendFinalWordTargetTape emit input final leftScratch) =
      List.append (input.map emit) final := by
  cases final with
  | nil =>
      rw [FSTMapAppendFinalWordTargetTape,
        appendFinalWordWriteTargetTape, tapeAtCells_normalizedOutput]
      simp [Function.comp_def, List.filterMap_append]
  | cons bit rest =>
      rw [FSTMapAppendFinalWordTargetTape,
        appendFinalWordWriteTargetTape, tapeAtCells_normalizedOutput]
      simp [Function.comp_def, List.filterMap_append,
        List.reverse_append, List.map_append, List.append_assoc]

theorem generatedMapAppendWordDescription_step_bit
    (emit : Bool -> Bool) (final : Word Bool) (bit : Bool)
    (left right : List (Option Bool)) :
    (generatedMapAppendWordDescription emit final).runConfig 1
        { state := (generatedMapAppendWordDescription emit final).start
          tape := tapeAtCells left (some bit :: right) } =
      { state := (generatedMapAppendWordDescription emit final).start
        tape := tapeAtCells (some (emit bit) :: left) right } := by
  cases final with
  | nil =>
      cases bit <;> cases right <;>
        simp [generatedMapAppendWordDescription,
          FiniteTransducer.mapAppendWordTransitions,
          FiniteTransducer.copyAppendWordWriteTransitionsFrom,
          FiniteTransducer.mapAppendWordScanFalseTransition,
          FiniteTransducer.mapAppendWordScanTrueTransition,
          FiniteTransducer.copyAppendWordHalt,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]
  | cons first rest =>
      cases bit <;> cases right <;>
        simp [generatedMapAppendWordDescription,
          FiniteTransducer.mapAppendWordTransitions,
          FiniteTransducer.copyAppendWordWriteTransitionsFrom,
          FiniteTransducer.mapAppendWordScanFalseTransition,
          FiniteTransducer.mapAppendWordScanTrueTransition,
          FiniteTransducer.copyAppendWordHalt,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]

theorem generatedMapAppendWordDescription_step_blank
    (emit : Bool -> Bool) (bit : Bool) (rest : Word Bool)
    (left : List (Option Bool)) :
    (generatedMapAppendWordDescription emit (bit :: rest)).runConfig 1
        { state := (generatedMapAppendWordDescription emit (bit :: rest)).start
          tape := tapeAtCells left [none] } =
      { state :=
          match rest with
          | [] => (generatedMapAppendWordDescription emit (bit :: rest)).halt
          | _ :: _ => 1
        tape := tapeAtCells (some bit :: left) [] } := by
  cases rest <;>
    simp [generatedMapAppendWordDescription,
      FiniteTransducer.mapAppendWordTransitions,
      FiniteTransducer.copyAppendWordWriteTransitionsFrom,
      FiniteTransducer.copyAppendWordHalt,
      FiniteTransducer.mapAppendWordScanFalseTransition,
      FiniteTransducer.mapAppendWordScanTrueTransition,
      runConfig, stepConfig, lookupTransition, Matches, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem generatedMapAppendWordDescription_run_scan
    (emit : Bool -> Bool) (final input : Word Bool)
    (left : List (Option Bool)) :
    (generatedMapAppendWordDescription emit final).runConfig input.length
        { state := (generatedMapAppendWordDescription emit final).start
          tape := tapeAtCells left
            (List.append (input.map some) [none]) } =
      { state := (generatedMapAppendWordDescription emit final).start
        tape :=
          tapeAtCells
            (List.append ((input.map emit).reverse.map some) left)
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
        (generatedMapAppendWordDescription emit final).runConfig rest.length
            ((generatedMapAppendWordDescription emit final).runConfig 1
              { state := (generatedMapAppendWordDescription emit final).start
                tape :=
                  tapeAtCells left
                    (some bit :: List.append (rest.map some) [none]) }) =
          { state := (generatedMapAppendWordDescription emit final).start
            tape :=
              tapeAtCells
                (List.append (((bit :: rest).map emit).reverse.map some)
                  left)
                [none] }
      rw [generatedMapAppendWordDescription_step_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some (emit bit) :: left)

theorem generatedMapAppendWordDescription_run_to_write_boundary
    (emit : Bool -> Bool) (final input : Word Bool) (leftScratch : Nat) :
    (generatedMapAppendWordDescription emit final).runConfig
        input.length
        { state := (generatedMapAppendWordDescription emit final).start
          tape := FSTSourceTape input leftScratch } =
      { state := (generatedMapAppendWordDescription emit final).start
        tape :=
          tapeAtCells
            (List.append ((input.map emit).reverse.map some)
              (List.replicate leftScratch (none : Option Bool)))
            [none] } := by
  simpa [FSTSourceTape, List.append_assoc] using
    generatedMapAppendWordDescription_run_scan emit final input
      (List.replicate leftScratch (none : Option Bool))

def MapAppendFinalWordWriterRuns
    (D : MachineDescription) (final : Word Bool) : Prop :=
  forall left : List (Option Bool),
    D.runConfig (FiniteTransducer.copyAppendWordHalt final)
      { state := D.start
        tape := tapeAtCells left [none] } =
    { state := D.halt
      tape := appendFinalWordWriteTargetTape left final }

theorem generatedMapAppendWordDescription_writerRuns
    (emit : Bool -> Bool) (final : Word Bool) :
    MapAppendFinalWordWriterRuns
      (generatedMapAppendWordDescription emit final) final := by
  intro left
  cases final with
  | nil =>
      simp [generatedMapAppendWordDescription,
        FiniteTransducer.mapAppendWordTransitions,
        FiniteTransducer.copyAppendWordWriteTransitionsFrom,
        FiniteTransducer.mapAppendWordScanFalseTransition,
        FiniteTransducer.mapAppendWordScanTrueTransition,
        FiniteTransducer.copyAppendWordHalt,
        appendFinalWordWriteTargetTape,
        runConfig, stepConfig, lookupTransition, Matches, tapeAtCells,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | cons bit rest =>
      cases rest with
      | nil =>
          simp [generatedMapAppendWordDescription,
            FiniteTransducer.mapAppendWordTransitions,
            FiniteTransducer.copyAppendWordWriteTransitionsFrom,
            FiniteTransducer.mapAppendWordScanFalseTransition,
            FiniteTransducer.mapAppendWordScanTrueTransition,
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
          rw [generatedMapAppendWordDescription_step_blank]
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.mapAppendWordScanFalseTransition emit
          let scanTrue : TransitionDescription :=
            FiniteTransducer.mapAppendWordScanTrueTransition emit
          have hpre :
              forall t : TransitionDescription,
                t ∈ [first, scanFalse, scanTrue] -> t.source < 1 := by
            intro t ht
            simp [first, scanFalse, scanTrue,
              FiniteTransducer.mapAppendWordScanFalseTransition,
              FiniteTransducer.mapAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;> simp
          have htail :=
            copyAppendWordWriteTransitionsFrom_run_with_pre
              [first, scanFalse, scanTrue]
              1 0 (next :: more) (some bit :: left) hpre
          simpa [generatedMapAppendWordDescription,
            FiniteTransducer.mapAppendWordTransitions,
            FiniteTransducer.copyAppendWordWriteTransitionsFrom,
            FiniteTransducer.copyAppendWordHalt,
            FiniteTransducer.mapAppendWordScanFalseTransition,
            FiniteTransducer.mapAppendWordScanTrueTransition,
            first, scanFalse, scanTrue, appendFinalWordWriteTargetTape,
            tapeAtCells, List.reverse_cons, List.map_append,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using htail

theorem generatedMapAppendWordDescription_wellFormed
    (emit : Bool -> Bool) (final : Word Bool) :
    (generatedMapAppendWordDescription emit final).WellFormed := by
  cases final with
  | nil =>
      let first : TransitionDescription :=
        { source := 0
          read := none
          write := none
          move := Direction.right
          target := 1 }
      have htrans :
          (generatedMapAppendWordDescription emit []).transitions =
            [first,
              FiniteTransducer.mapAppendWordScanFalseTransition emit,
              FiniteTransducer.mapAppendWordScanTrueTransition emit] := by
        rfl
      refine
        ⟨by simp [generatedMapAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt],
          by simp [generatedMapAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt],
          by simp [generatedMapAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt], ?_, ?_⟩
      · intro t ht
        rw [htrans] at ht
        simp [first, FiniteTransducer.mapAppendWordScanFalseTransition,
          FiniteTransducer.mapAppendWordScanTrueTransition] at ht
        rcases ht with ht | ht | ht <;> subst t <;>
          simp [TransitionDescription.WellFormed,
            generatedMapAppendWordDescription,
            FiniteTransducer.copyAppendWordHalt]
      · intro t u ht hu hkey
        rw [htrans] at ht hu
        exact
          FiniteTransducer.mapAppendWordPrefix_deterministic
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
              (generatedMapAppendWordDescription emit [bit]).transitions =
                [first,
                  FiniteTransducer.mapAppendWordScanFalseTransition emit,
                  FiniteTransducer.mapAppendWordScanTrueTransition emit] := by
            rfl
          refine
            ⟨by simp [generatedMapAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt],
              by simp [generatedMapAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt],
              by simp [generatedMapAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt], ?_, ?_⟩
          · intro t ht
            rw [htrans] at ht
            simp [first, FiniteTransducer.mapAppendWordScanFalseTransition,
              FiniteTransducer.mapAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;>
              simp [TransitionDescription.WellFormed,
                generatedMapAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt]
          · intro t u ht hu hkey
            rw [htrans] at ht hu
            exact
              FiniteTransducer.mapAppendWordPrefix_deterministic
                emit first t u rfl rfl ht hu hkey
      | cons next more =>
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.mapAppendWordScanFalseTransition emit
          let scanTrue : TransitionDescription :=
            FiniteTransducer.mapAppendWordScanTrueTransition emit
          have htrans :
              (generatedMapAppendWordDescription emit
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
          · simp [generatedMapAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · simp [generatedMapAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · simp [generatedMapAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · intro t ht
            rw [htrans] at ht
            rcases List.mem_append.mp ht with ht | ht
            · simp [first, scanFalse, scanTrue,
                FiniteTransducer.mapAppendWordScanFalseTransition,
                FiniteTransducer.mapAppendWordScanTrueTransition] at ht
              rcases ht with ht | ht | ht <;> subst t <;>
                constructor <;> simp [generatedMapAppendWordDescription,
                  FiniteTransducer.copyAppendWordHalt]
            · have ht' :
                t ∈ FiniteTransducer.copyAppendWordWriteTransitionsFrom
                  1 (1 + (next :: more).length) (next :: more) := by
                simpa [hhalt] using ht
              have htwf :=
                FiniteTransducer.copyAppendWordWriteTransitionsFrom_wellFormed
                  1 (next :: more) t ht'
              simpa [generatedMapAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htwf
          · intro t u ht hu hkey
            rw [htrans] at ht hu
            rcases List.mem_append.mp ht with ht | ht <;>
              rcases List.mem_append.mp hu with hu | hu
            · exact
                FiniteTransducer.mapAppendWordPrefix_deterministic
                  emit first t u rfl rfl ht hu hkey
            · simp [first, scanFalse, scanTrue,
                FiniteTransducer.mapAppendWordScanFalseTransition,
                FiniteTransducer.mapAppendWordScanTrueTransition] at ht
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
                FiniteTransducer.mapAppendWordScanFalseTransition,
                FiniteTransducer.mapAppendWordScanTrueTransition] at hu
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

theorem generatedMapAppendWordDescription_haltTransitionFree
    (emit : Bool -> Bool) (final : Word Bool) :
    (generatedMapAppendWordDescription emit final).HaltTransitionFree := by
  cases final with
  | nil =>
      let first : TransitionDescription :=
        { source := 0
          read := none
          write := none
          move := Direction.right
          target := 1 }
      have htrans :
          (generatedMapAppendWordDescription emit []).transitions =
            [first,
              FiniteTransducer.mapAppendWordScanFalseTransition emit,
              FiniteTransducer.mapAppendWordScanTrueTransition emit] := by
        rfl
      intro t ht
      rw [htrans] at ht
      simp [first, FiniteTransducer.mapAppendWordScanFalseTransition,
        FiniteTransducer.mapAppendWordScanTrueTransition] at ht
      rcases ht with ht | ht | ht <;> subst t <;>
        simp [generatedMapAppendWordDescription,
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
              (generatedMapAppendWordDescription emit [bit]).transitions =
                [first,
                  FiniteTransducer.mapAppendWordScanFalseTransition emit,
                  FiniteTransducer.mapAppendWordScanTrueTransition emit] := by
            rfl
          intro t ht
          rw [htrans] at ht
          simp [first, FiniteTransducer.mapAppendWordScanFalseTransition,
            FiniteTransducer.mapAppendWordScanTrueTransition] at ht
          rcases ht with ht | ht | ht <;> subst t <;>
            simp [generatedMapAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
      | cons next more =>
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.mapAppendWordScanFalseTransition emit
          let scanTrue : TransitionDescription :=
            FiniteTransducer.mapAppendWordScanTrueTransition emit
          have htrans :
              (generatedMapAppendWordDescription emit
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
              FiniteTransducer.mapAppendWordScanFalseTransition,
              FiniteTransducer.mapAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;>
              simp [generatedMapAppendWordDescription,
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
              simpa [generatedMapAppendWordDescription, hhalt] using hsource
            omega

theorem generatedMapAppendWordDescription_subroutineReady
    (emit : Bool -> Bool) (final : Word Bool) :
    (generatedMapAppendWordDescription emit final).SubroutineReady :=
  ⟨generatedMapAppendWordDescription_wellFormed emit final,
    generatedMapAppendWordDescription_haltTransitionFree emit final⟩

theorem generatedMapAppendWordDescription_haltsFrom_FSTSourceTape
    (emit : Bool -> Bool) (final input : Word Bool)
    (leftScratch : Nat) :
    (generatedMapAppendWordDescription emit final).HaltsFromTape
      (FSTSourceTape input leftScratch)
      (FSTMapAppendFinalWordTargetTape emit input final leftScratch) := by
  refine ⟨input.length + FiniteTransducer.copyAppendWordHalt final, ?_⟩
  change
    ((generatedMapAppendWordDescription emit final).runConfig
        (input.length + FiniteTransducer.copyAppendWordHalt final)
        { state := (generatedMapAppendWordDescription emit final).start
          tape := FSTSourceTape input leftScratch }).state =
      (generatedMapAppendWordDescription emit final).halt ∧
    ((generatedMapAppendWordDescription emit final).runConfig
        (input.length + FiniteTransducer.copyAppendWordHalt final)
        { state := (generatedMapAppendWordDescription emit final).start
          tape := FSTSourceTape input leftScratch }).tape =
      FSTMapAppendFinalWordTargetTape emit input final leftScratch
  rw [runConfig_add]
  rw [generatedMapAppendWordDescription_run_to_write_boundary]
  have hwrite :=
    generatedMapAppendWordDescription_writerRuns emit final
      (List.append ((input.map emit).reverse.map some)
        (List.replicate leftScratch (none : Option Bool)))
  constructor
  · simpa [FSTMapAppendFinalWordTargetTape] using
      congrArg MachineDescription.Configuration.state hwrite
  · simpa [FSTMapAppendFinalWordTargetTape] using
      congrArg MachineDescription.Configuration.tape hwrite

theorem bitMapAppendFinalTransducer_compiledByGeneratedDescription
    (emit : Bool -> Bool) (final : Word Bool) :
    ExactCompiledByDescription
      (bitMapAppendFinalTransducer emit final)
      (generatedMapAppendWordDescription emit final)
      (fun input _output leftScratch =>
        FSTMapAppendFinalWordTargetTape emit input final leftScratch) := by
  constructor
  · exact generatedMapAppendWordDescription_subroutineReady emit final
  · intro input output leftScratch hrun
    have hout := bitMapAppendFinalTransducer_run emit final input
    change
      (bitMapAppendFinalTransducer emit final).runFromStart
          (input.length + 1) input =
        some ((bitMapAppendFinalTransducer emit final).halt, output) at hrun
    rw [hout] at hrun
    cases hrun
    exact generatedMapAppendWordDescription_haltsFrom_FSTSourceTape
      emit final input leftScratch

end FiniteTransducers
end CommonGround

end Computability
end FoC
