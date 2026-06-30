import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic

set_option doc.verso true

/-!
# Certified append-word finite transducer compiler
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

def generatedAppendWordDescription
    (final : Word Bool) : MachineDescription where
  stateCount := FiniteTransducer.copyAppendWordHalt final + 1
  start := 0
  halt := FiniteTransducer.copyAppendWordHalt final
  transitions := FiniteTransducer.copyAppendWordTransitions final

def appendFinalWordWriteTargetTape
    (left : List (Option Bool)) (final : Word Bool) : Tape Bool :=
  match final with
  | [] => tapeAtCells (none :: left) []
  | _ :: _ =>
      tapeAtCells (List.append (final.reverse.map some) left) []

def FSTAppendFinalWordTargetTape
    (input final : Word Bool) (leftScratch : Nat) : Tape Bool :=
  appendFinalWordWriteTargetTape
    (List.append (input.reverse.map some)
      (List.replicate leftScratch (none : Option Bool)))
    final

theorem find?_matches_none_of_sources_lt
    {l : List TransitionDescription} {state : Nat} {read : Option Bool}
    (hsource : forall t : TransitionDescription, t ∈ l -> t.source < state) :
    l.find? (Matches state read) = none := by
  rw [List.find?_eq_none]
  intro t ht hmatch
  have htstate : t.source = state := by
    unfold Matches at hmatch
    simp at hmatch
    exact hmatch.left
  have hlt := hsource t ht
  omega

theorem copyAppendWordWriteTransitionsFrom_step_with_pre
    (pre : List TransitionDescription) (source startState halt : Nat)
    (bit : Bool) (rest : Word Bool) (left : List (Option Bool))
    (hpre : forall t : TransitionDescription, t ∈ pre -> t.source < source) :
    let D : MachineDescription :=
      { stateCount := halt + 1
        start := startState
        halt := halt
        transitions :=
          List.append pre
            (FiniteTransducer.copyAppendWordWriteTransitionsFrom
              source halt (bit :: rest)) }
    D.runConfig 1
        { state := source
          tape := tapeAtCells left [none] } =
      { state :=
          match rest with
          | [] => halt
          | _ :: _ => source + 1
        tape := tapeAtCells (some bit :: left) [] } := by
  intro D
  have hpreFind :
      pre.find? (Matches source none) = none :=
    find?_matches_none_of_sources_lt hpre
  cases rest <;>
    simp [D, FiniteTransducer.copyAppendWordWriteTransitionsFrom,
      runConfig, stepConfig, lookupTransition, List.find?_append,
      hpreFind, Matches, tapeAtCells, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem copyAppendWordWriteTransitionsFrom_run_with_pre
    (pre : List TransitionDescription) (source startState : Nat)
    (final : Word Bool) (left : List (Option Bool))
    (hpre : forall t : TransitionDescription, t ∈ pre -> t.source < source) :
    let halt := source + final.length
    let D : MachineDescription :=
      { stateCount := halt + 1
        start := startState
        halt := halt
        transitions :=
          List.append pre
            (FiniteTransducer.copyAppendWordWriteTransitionsFrom
              source halt final) }
    D.runConfig final.length
        { state := source
          tape := tapeAtCells left [none] } =
      { state := halt
        tape :=
          tapeAtCells
            (List.append (final.reverse.map some) left)
            [] } := by
  induction final generalizing pre source startState left with
  | nil =>
      intro halt _D
      simp [halt, tapeAtCells, runConfig]
  | cons bit rest ih =>
      intro halt D
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      have hstep :=
        copyAppendWordWriteTransitionsFrom_step_with_pre
          pre source startState halt bit rest left hpre
      change
        D.runConfig rest.length
            (D.runConfig 1
              { state := source
                tape := tapeAtCells left [none] }) =
          { state := halt
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                [] }
      rw [hstep]
      cases rest with
      | nil =>
          simp [halt, tapeAtCells, runConfig]
      | cons _next _more =>
          let first : TransitionDescription :=
            { source := source
              read := none
              write := some bit
              move := Direction.right
              target := source + 1 }
          have hpre' :
              forall t : TransitionDescription,
                t ∈ List.append pre [first] -> t.source < source + 1 := by
            intro t ht
            simp at ht
            rcases ht with ht | ht
            · have hlt := hpre t ht
              omega
            · subst t
              simp [first]
          have htail :=
            ih (List.append pre [first]) (source + 1) startState
              (some bit :: left) hpre'
          simpa [D, halt, first, tapeAtCells,
            FiniteTransducer.copyAppendWordWriteTransitionsFrom,
            List.append_assoc, List.reverse_cons, List.map_append,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem generatedAppendWordDescription_step_bit
    (final : Word Bool) (bit : Bool)
    (left right : List (Option Bool)) :
    (generatedAppendWordDescription final).runConfig 1
        { state := (generatedAppendWordDescription final).start
          tape := tapeAtCells left (some bit :: right) } =
      { state := (generatedAppendWordDescription final).start
        tape := tapeAtCells (some bit :: left) right } := by
  cases final with
  | nil =>
      cases bit <;> cases right <;>
        simp [generatedAppendWordDescription,
          FiniteTransducer.copyAppendWordTransitions,
          FiniteTransducer.copyAppendWordWriteTransitionsFrom,
          FiniteTransducer.copyAppendWordScanFalseTransition,
          FiniteTransducer.copyAppendWordScanTrueTransition,
          FiniteTransducer.copyAppendWordHalt,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]
  | cons first rest =>
      cases bit <;> cases right <;>
        simp [generatedAppendWordDescription,
          FiniteTransducer.copyAppendWordTransitions,
          FiniteTransducer.copyAppendWordWriteTransitionsFrom,
          FiniteTransducer.copyAppendWordScanFalseTransition,
          FiniteTransducer.copyAppendWordScanTrueTransition,
          FiniteTransducer.copyAppendWordHalt,
          tapeAtCells, runConfig, stepConfig, lookupTransition,
          Matches, Tape.read, Tape.write,
          Tape.move, Tape.moveRight]

theorem generatedAppendWordDescription_step_blank
    (bit : Bool) (rest : Word Bool) (left : List (Option Bool)) :
    (generatedAppendWordDescription (bit :: rest)).runConfig 1
        { state := (generatedAppendWordDescription (bit :: rest)).start
          tape := tapeAtCells left [none] } =
      { state :=
          match rest with
          | [] => (generatedAppendWordDescription (bit :: rest)).halt
          | _ :: _ => 1
        tape := tapeAtCells (some bit :: left) [] } := by
  cases rest <;>
    simp [generatedAppendWordDescription,
      FiniteTransducer.copyAppendWordTransitions,
      FiniteTransducer.copyAppendWordWriteTransitionsFrom,
      FiniteTransducer.copyAppendWordHalt,
      FiniteTransducer.copyAppendWordScanFalseTransition,
      FiniteTransducer.copyAppendWordScanTrueTransition,
      runConfig, stepConfig, lookupTransition, Matches, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem generatedAppendWordDescription_run_scan
    (final input : Word Bool) (left : List (Option Bool)) :
    (generatedAppendWordDescription final).runConfig input.length
        { state := (generatedAppendWordDescription final).start
          tape := tapeAtCells left (List.append (input.map some) [none]) } =
      { state := (generatedAppendWordDescription final).start
        tape :=
          tapeAtCells
            (List.append (input.reverse.map some) left)
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
        (generatedAppendWordDescription final).runConfig rest.length
            ((generatedAppendWordDescription final).runConfig 1
              { state := (generatedAppendWordDescription final).start
                tape :=
                  tapeAtCells left
                    (some bit :: List.append (rest.map some) [none]) }) =
          { state := (generatedAppendWordDescription final).start
            tape :=
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                [none] }
      rw [generatedAppendWordDescription_step_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

def AppendFinalWordWriterRuns
    (D : MachineDescription) (final : Word Bool) : Prop :=
  forall left : List (Option Bool),
    D.runConfig (FiniteTransducer.copyAppendWordHalt final)
      { state := D.start
        tape := tapeAtCells left [none] } =
    { state := D.halt
      tape := appendFinalWordWriteTargetTape left final }

theorem generatedAppendWordDescription_run_to_write_boundary
    (final input : Word Bool) (leftScratch : Nat) :
    (generatedAppendWordDescription final).runConfig
        input.length
        { state := (generatedAppendWordDescription final).start
          tape := FSTSourceTape input leftScratch } =
      { state := (generatedAppendWordDescription final).start
        tape :=
          tapeAtCells
            (List.append (input.reverse.map some)
              (List.replicate leftScratch (none : Option Bool)))
            [none] } := by
  simpa [FSTSourceTape, List.append_assoc] using
    generatedAppendWordDescription_run_scan final input
      (List.replicate leftScratch (none : Option Bool))

theorem generatedAppendWordDescription_haltsFrom_FSTSourceTape_of_writer
    (final input : Word Bool) (leftScratch : Nat)
    (hwriter :
      AppendFinalWordWriterRuns
        (generatedAppendWordDescription final) final) :
    (generatedAppendWordDescription final).HaltsFromTape
      (FSTSourceTape input leftScratch)
      (FSTAppendFinalWordTargetTape input final leftScratch) := by
  refine ⟨input.length + FiniteTransducer.copyAppendWordHalt final, ?_⟩
  change
    ((generatedAppendWordDescription final).runConfig
        (input.length + FiniteTransducer.copyAppendWordHalt final)
        { state := (generatedAppendWordDescription final).start
          tape := FSTSourceTape input leftScratch }).state =
      (generatedAppendWordDescription final).halt ∧
    ((generatedAppendWordDescription final).runConfig
        (input.length + FiniteTransducer.copyAppendWordHalt final)
        { state := (generatedAppendWordDescription final).start
          tape := FSTSourceTape input leftScratch }).tape =
      FSTAppendFinalWordTargetTape input final leftScratch
  rw [runConfig_add]
  rw [generatedAppendWordDescription_run_to_write_boundary]
  have hwrite :=
    hwriter
      (List.append (input.reverse.map some)
        (List.replicate leftScratch (none : Option Bool)))
  constructor
  · simpa [FSTAppendFinalWordTargetTape] using
      congrArg MachineDescription.Configuration.state hwrite
  · simpa [FSTAppendFinalWordTargetTape] using
      congrArg MachineDescription.Configuration.tape hwrite

theorem appendFinalWordTransducer_compiledByGeneratedDescription_of_writer
    (final : Word Bool)
    (hready :
      (generatedAppendWordDescription final).SubroutineReady)
    (hwriter :
      AppendFinalWordWriterRuns
        (generatedAppendWordDescription final) final) :
    ExactCompiledByDescription
      (appendFinalWordTransducer final)
      (generatedAppendWordDescription final)
      (fun input _output leftScratch =>
        FSTAppendFinalWordTargetTape input final leftScratch) := by
  constructor
  · exact hready
  · intro input output leftScratch hrun
    have hout := appendFinalWordTransducer_run final input
    change
      (appendFinalWordTransducer final).runFromStart
          (input.length + 1) input =
        some ((appendFinalWordTransducer final).halt, output) at hrun
    rw [hout] at hrun
    cases hrun
    exact generatedAppendWordDescription_haltsFrom_FSTSourceTape_of_writer
      final input leftScratch hwriter

theorem generatedAppendWordDescription_empty_wellFormed :
    (generatedAppendWordDescription []).WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := (generatedAppendWordDescription []).transitions)
      (stateCount := (generatedAppendWordDescription []).stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := (generatedAppendWordDescription []).transitions)
      (by native_decide)

theorem generatedAppendWordDescription_empty_haltTransitionFree :
    (generatedAppendWordDescription []).HaltTransitionFree :=
  transition_notFrom_of_all
    (l := (generatedAppendWordDescription []).transitions)
    (state := (generatedAppendWordDescription []).halt)
    (by native_decide)

theorem generatedAppendWordDescription_empty_subroutineReady :
    (generatedAppendWordDescription []).SubroutineReady :=
  ⟨generatedAppendWordDescription_empty_wellFormed,
    generatedAppendWordDescription_empty_haltTransitionFree⟩

theorem generatedAppendWordDescription_empty_writerRuns :
    AppendFinalWordWriterRuns
      (generatedAppendWordDescription []) [] := by
  intro left
  simp [generatedAppendWordDescription,
    FiniteTransducer.copyAppendWordTransitions,
    FiniteTransducer.copyAppendWordWriteTransitionsFrom,
    FiniteTransducer.copyAppendWordScanFalseTransition,
    FiniteTransducer.copyAppendWordScanTrueTransition,
    FiniteTransducer.copyAppendWordHalt,
    appendFinalWordWriteTargetTape,
    tapeAtCells, runConfig, stepConfig, lookupTransition,
    Matches, Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem appendFinalWordTransducer_empty_compiledByGeneratedDescription :
    ExactCompiledByDescription
      (appendFinalWordTransducer [])
      (generatedAppendWordDescription [])
      (fun input _output leftScratch =>
        FSTAppendFinalWordTargetTape input [] leftScratch) :=
  appendFinalWordTransducer_compiledByGeneratedDescription_of_writer
    [] generatedAppendWordDescription_empty_subroutineReady
    generatedAppendWordDescription_empty_writerRuns

theorem generatedAppendWordDescription_singleton_wellFormed
    (bit : Bool) :
    (generatedAppendWordDescription [bit]).WellFormed := by
  cases bit <;>
    refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := (generatedAppendWordDescription [false]).transitions)
      (stateCount := (generatedAppendWordDescription [false]).stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := (generatedAppendWordDescription [false]).transitions)
      (by native_decide)
  · exact transition_wellFormed_of_all
      (l := (generatedAppendWordDescription [true]).transitions)
      (stateCount := (generatedAppendWordDescription [true]).stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := (generatedAppendWordDescription [true]).transitions)
      (by native_decide)

theorem generatedAppendWordDescription_singleton_haltTransitionFree
    (bit : Bool) :
    (generatedAppendWordDescription [bit]).HaltTransitionFree := by
  cases bit
  · exact transition_notFrom_of_all
      (l := (generatedAppendWordDescription [false]).transitions)
      (state := (generatedAppendWordDescription [false]).halt)
      (by native_decide)
  · exact transition_notFrom_of_all
      (l := (generatedAppendWordDescription [true]).transitions)
      (state := (generatedAppendWordDescription [true]).halt)
      (by native_decide)

theorem generatedAppendWordDescription_singleton_subroutineReady
    (bit : Bool) :
    (generatedAppendWordDescription [bit]).SubroutineReady :=
  ⟨generatedAppendWordDescription_singleton_wellFormed bit,
    generatedAppendWordDescription_singleton_haltTransitionFree bit⟩

theorem generatedAppendWordDescription_singleton_writerRuns
    (bit : Bool) :
    AppendFinalWordWriterRuns
      (generatedAppendWordDescription [bit]) [bit] := by
  intro left
  cases bit <;>
    simp [generatedAppendWordDescription,
      FiniteTransducer.copyAppendWordTransitions,
      FiniteTransducer.copyAppendWordWriteTransitionsFrom,
      FiniteTransducer.copyAppendWordScanFalseTransition,
      FiniteTransducer.copyAppendWordScanTrueTransition,
      FiniteTransducer.copyAppendWordHalt,
      appendFinalWordWriteTargetTape,
      tapeAtCells, runConfig, stepConfig, lookupTransition,
      Matches, Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem appendFinalWordTransducer_singleton_compiledByGeneratedDescription
    (bit : Bool) :
    ExactCompiledByDescription
      (appendFinalWordTransducer [bit])
      (generatedAppendWordDescription [bit])
      (fun input _output leftScratch =>
        FSTAppendFinalWordTargetTape input [bit] leftScratch) :=
  appendFinalWordTransducer_compiledByGeneratedDescription_of_writer
    [bit] (generatedAppendWordDescription_singleton_subroutineReady bit)
    (generatedAppendWordDescription_singleton_writerRuns bit)

theorem generatedAppendWordDescription_wellFormed
    (final : Word Bool) :
    (generatedAppendWordDescription final).WellFormed := by
  cases final with
  | nil =>
      exact generatedAppendWordDescription_empty_wellFormed
  | cons bit rest =>
      cases rest with
      | nil =>
          exact generatedAppendWordDescription_singleton_wellFormed bit
      | cons next more =>
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.copyAppendWordScanFalseTransition
          let scanTrue : TransitionDescription :=
            FiniteTransducer.copyAppendWordScanTrueTransition
          have htrans :
              (generatedAppendWordDescription (bit :: next :: more)).transitions =
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
          · simp [generatedAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · simp [generatedAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · simp [generatedAppendWordDescription,
              FiniteTransducer.copyAppendWordHalt]
          · intro t ht
            rw [htrans] at ht
            rcases List.mem_append.mp ht with ht | ht
            · simp [first, scanFalse, scanTrue,
                FiniteTransducer.copyAppendWordScanFalseTransition,
                FiniteTransducer.copyAppendWordScanTrueTransition] at ht
              rcases ht with ht | ht | ht <;> subst t <;>
                constructor <;> simp [generatedAppendWordDescription,
                  FiniteTransducer.copyAppendWordHalt]
            · have ht' :
                t ∈ FiniteTransducer.copyAppendWordWriteTransitionsFrom
                  1 (1 + (next :: more).length) (next :: more) := by
                simpa [hhalt] using ht
              have htwf :=
                FiniteTransducer.copyAppendWordWriteTransitionsFrom_wellFormed
                  1 (next :: more) t ht'
              simpa [generatedAppendWordDescription,
                FiniteTransducer.copyAppendWordHalt,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htwf
          · intro t u ht hu hkey
            rw [htrans] at ht hu
            rcases List.mem_append.mp ht with ht | ht <;>
              rcases List.mem_append.mp hu with hu | hu
            · have hprefixDet :=
                transition_deterministic_of_all
                  (l := [first, scanFalse, scanTrue])
                  (by cases bit <;> native_decide)
              exact hprefixDet t u ht hu hkey
            · simp [first, scanFalse, scanTrue,
                FiniteTransducer.copyAppendWordScanFalseTransition,
                FiniteTransducer.copyAppendWordScanTrueTransition] at ht
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
                FiniteTransducer.copyAppendWordScanFalseTransition,
                FiniteTransducer.copyAppendWordScanTrueTransition] at hu
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

theorem generatedAppendWordDescription_haltTransitionFree
    (final : Word Bool) :
    (generatedAppendWordDescription final).HaltTransitionFree := by
  cases final with
  | nil =>
      exact generatedAppendWordDescription_empty_haltTransitionFree
  | cons bit rest =>
      cases rest with
      | nil =>
          exact generatedAppendWordDescription_singleton_haltTransitionFree bit
      | cons next more =>
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.copyAppendWordScanFalseTransition
          let scanTrue : TransitionDescription :=
            FiniteTransducer.copyAppendWordScanTrueTransition
          have htrans :
              (generatedAppendWordDescription (bit :: next :: more)).transitions =
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
              FiniteTransducer.copyAppendWordScanFalseTransition,
              FiniteTransducer.copyAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;>
              simp [generatedAppendWordDescription,
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
              simpa [generatedAppendWordDescription, hhalt] using hsource
            omega

theorem generatedAppendWordDescription_subroutineReady
    (final : Word Bool) :
    (generatedAppendWordDescription final).SubroutineReady :=
  ⟨generatedAppendWordDescription_wellFormed final,
    generatedAppendWordDescription_haltTransitionFree final⟩

theorem generatedAppendWordDescription_writerRuns
    (final : Word Bool) :
    AppendFinalWordWriterRuns
      (generatedAppendWordDescription final) final := by
  intro left
  cases final with
  | nil =>
      exact generatedAppendWordDescription_empty_writerRuns left
  | cons bit rest =>
      cases rest with
      | nil =>
          exact generatedAppendWordDescription_singleton_writerRuns bit left
      | cons next more =>
          rw [show
              FiniteTransducer.copyAppendWordHalt (bit :: next :: more) =
                1 + (next :: more).length by
            simp [FiniteTransducer.copyAppendWordHalt]
            omega]
          rw [runConfig_add]
          rw [generatedAppendWordDescription_step_blank]
          let first : TransitionDescription :=
            { source := 0
              read := none
              write := some bit
              move := Direction.right
              target := 1 }
          let scanFalse : TransitionDescription :=
            FiniteTransducer.copyAppendWordScanFalseTransition
          let scanTrue : TransitionDescription :=
            FiniteTransducer.copyAppendWordScanTrueTransition
          have hpre :
              forall t : TransitionDescription,
                t ∈ [first, scanFalse, scanTrue] -> t.source < 1 := by
            intro t ht
            simp [first, scanFalse, scanTrue,
              FiniteTransducer.copyAppendWordScanFalseTransition,
              FiniteTransducer.copyAppendWordScanTrueTransition] at ht
            rcases ht with ht | ht | ht <;> subst t <;> simp
          have htail :=
            copyAppendWordWriteTransitionsFrom_run_with_pre
              [first, scanFalse, scanTrue]
              1 0 (next :: more) (some bit :: left) hpre
          simpa [generatedAppendWordDescription,
            FiniteTransducer.copyAppendWordTransitions,
            FiniteTransducer.copyAppendWordWriteTransitionsFrom,
            FiniteTransducer.copyAppendWordHalt,
            FiniteTransducer.copyAppendWordScanFalseTransition,
            FiniteTransducer.copyAppendWordScanTrueTransition,
            first, scanFalse, scanTrue, appendFinalWordWriteTargetTape,
            tapeAtCells, List.reverse_cons, List.map_append,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using htail

theorem appendFinalWordTransducer_compiledByGeneratedDescription
    (final : Word Bool) :
    ExactCompiledByDescription
      (appendFinalWordTransducer final)
      (generatedAppendWordDescription final)
      (fun input _output leftScratch =>
        FSTAppendFinalWordTargetTape input final leftScratch) :=
  appendFinalWordTransducer_compiledByGeneratedDescription_of_writer
    final (generatedAppendWordDescription_subroutineReady final)
    (generatedAppendWordDescription_writerRuns final)

/--
Generated fixed-four append machine.  The source FST has two states; the
compiler expands its trailing-blank emission row into three internal writer
states and one final halt state.
-/
def generatedAppendFixedFourBitsDescription
    (b0 b1 b2 b3 : Bool) : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    (appendFixedFourBitsTransducer b0 b1 b2 b3).copyAppendFourTransitions

theorem generatedAppendFixedFourBitsDescription_eq_appendFixedFour
    (b0 b1 b2 b3 : Bool) :
    generatedAppendFixedFourBitsDescription b0 b1 b2 b3 =
      AppendFixedFourBitsRightDescription b0 b1 b2 b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    native_decide

theorem generatedAppendWordDescription_fixedFour_eq_generated
    (b0 b1 b2 b3 : Bool) :
    generatedAppendWordDescription [b0, b1, b2, b3] =
      generatedAppendFixedFourBitsDescription b0 b1 b2 b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    native_decide

theorem generatedAppendWordDescription_fixedFour_eq_appendFixedFour
    (b0 b1 b2 b3 : Bool) :
    generatedAppendWordDescription [b0, b1, b2, b3] =
      AppendFixedFourBitsRightDescription b0 b1 b2 b3 := by
  rw [generatedAppendWordDescription_fixedFour_eq_generated,
    generatedAppendFixedFourBitsDescription_eq_appendFixedFour]

theorem generatedAppendWordDescription_fixedFour_subroutineReady
    (b0 b1 b2 b3 : Bool) :
    (generatedAppendWordDescription [b0, b1, b2, b3]).SubroutineReady := by
  rw [generatedAppendWordDescription_fixedFour_eq_appendFixedFour]
  exact appendFixedFourBitsRightDescription_subroutineReady b0 b1 b2 b3

theorem generatedAppendWordDescription_fixedFour_writerRuns
    (b0 b1 b2 b3 : Bool) :
    AppendFinalWordWriterRuns
      (generatedAppendWordDescription [b0, b1, b2, b3])
      [b0, b1, b2, b3] := by
  intro left
  rw [generatedAppendWordDescription_fixedFour_eq_appendFixedFour]
  simpa [AppendFinalWordWriterRuns,
    FiniteTransducer.copyAppendWordHalt,
    appendFinalWordWriteTargetTape] using
    appendFixedFourBitsRightDescription_run_write_tapeAtCells
      b0 b1 b2 b3 left

theorem appendFixedFourBitsTransducer_compiledByGeneratedWordDescription_via_writer
    (b0 b1 b2 b3 : Bool) :
    ExactCompiledByDescription
      (appendFixedFourBitsTransducer b0 b1 b2 b3)
      (generatedAppendWordDescription [b0, b1, b2, b3])
      (fun input _output leftScratch =>
        FSTAppendFinalWordTargetTape input [b0, b1, b2, b3] leftScratch) := by
  exact appendFinalWordTransducer_compiledByGeneratedDescription_of_writer
    [b0, b1, b2, b3]
    (generatedAppendWordDescription_fixedFour_subroutineReady b0 b1 b2 b3)
    (generatedAppendWordDescription_fixedFour_writerRuns b0 b1 b2 b3)

theorem generatedAppendFixedFourBitsDescription_wellFormed
    (b0 b1 b2 b3 : Bool) :
    (generatedAppendFixedFourBitsDescription b0 b1 b2 b3).WellFormed := by
  rw [generatedAppendFixedFourBitsDescription_eq_appendFixedFour]
  exact appendFixedFourBitsRightDescription_wellFormed b0 b1 b2 b3

theorem generatedAppendFixedFourBitsDescription_haltTransitionFree
    (b0 b1 b2 b3 : Bool) :
    (generatedAppendFixedFourBitsDescription b0 b1 b2 b3).HaltTransitionFree := by
  rw [generatedAppendFixedFourBitsDescription_eq_appendFixedFour]
  exact appendFixedFourBitsRightDescription_haltTransitionFree b0 b1 b2 b3

theorem generatedAppendFixedFourBitsDescription_subroutineReady
    (b0 b1 b2 b3 : Bool) :
    (generatedAppendFixedFourBitsDescription b0 b1 b2 b3).SubroutineReady :=
  ⟨generatedAppendFixedFourBitsDescription_wellFormed b0 b1 b2 b3,
    generatedAppendFixedFourBitsDescription_haltTransitionFree b0 b1 b2 b3⟩

theorem generatedAppendFixedFourBitsDescription_haltsFrom_FSTSourceTape
    (b0 b1 b2 b3 : Bool) (input : Word Bool) (leftScratch : Nat) :
    (generatedAppendFixedFourBitsDescription b0 b1 b2 b3).HaltsFromTape
      (FSTSourceTape input leftScratch)
      (FSTRightAppendedTargetTape
        (List.append input [b0, b1, b2, b3]) leftScratch) := by
  rw [generatedAppendFixedFourBitsDescription_eq_appendFixedFour]
  exact appendFixedFourBitsRightDescription_haltsFrom_FSTSourceTape
    b0 b1 b2 b3 input leftScratch

theorem appendFixedFourBitsTransducer_compiledByDescription
    (b0 b1 b2 b3 : Bool) :
    ExactCompiledByDescription
      (appendFixedFourBitsTransducer b0 b1 b2 b3)
      (AppendFixedFourBitsRightDescription b0 b1 b2 b3)
      (fun _input output leftScratch =>
        FSTRightAppendedTargetTape output leftScratch) := by
  constructor
  · exact appendFixedFourBitsRightDescription_subroutineReady b0 b1 b2 b3
  · intro input output leftScratch hrun
    have hout := appendFixedFourBitsTransducer_run b0 b1 b2 b3 input
    change
      (appendFixedFourBitsTransducer b0 b1 b2 b3).runFromStart
          (input.length + 1) input =
        some ((appendFixedFourBitsTransducer b0 b1 b2 b3).halt, output)
      at hrun
    rw [hout] at hrun
    cases hrun
    exact appendFixedFourBitsRightDescription_haltsFrom_FSTSourceTape
      b0 b1 b2 b3 input leftScratch

theorem appendFixedFourBitsTransducer_compiledByGeneratedDescription
    (b0 b1 b2 b3 : Bool) :
    ExactCompiledByDescription
      (appendFixedFourBitsTransducer b0 b1 b2 b3)
      (generatedAppendFixedFourBitsDescription b0 b1 b2 b3)
      (fun _input output leftScratch =>
        FSTRightAppendedTargetTape output leftScratch) := by
  constructor
  · exact generatedAppendFixedFourBitsDescription_subroutineReady
      b0 b1 b2 b3
  · intro input output leftScratch hrun
    have hout := appendFixedFourBitsTransducer_run b0 b1 b2 b3 input
    change
      (appendFixedFourBitsTransducer b0 b1 b2 b3).runFromStart
          (input.length + 1) input =
        some ((appendFixedFourBitsTransducer b0 b1 b2 b3).halt, output)
      at hrun
    rw [hout] at hrun
    cases hrun
    exact generatedAppendFixedFourBitsDescription_haltsFrom_FSTSourceTape
      b0 b1 b2 b3 input leftScratch

theorem appendFixedFourBitsTransducer_compiledByGeneratedWordDescription
    (b0 b1 b2 b3 : Bool) :
    ExactCompiledByDescription
      (appendFixedFourBitsTransducer b0 b1 b2 b3)
      (generatedAppendWordDescription [b0, b1, b2, b3])
      (fun _input output leftScratch =>
        FSTRightAppendedTargetTape output leftScratch) := by
  rw [generatedAppendWordDescription_fixedFour_eq_generated]
  exact appendFixedFourBitsTransducer_compiledByGeneratedDescription
    b0 b1 b2 b3


end FiniteTransducers
end CommonGround

end Computability
end FoC
