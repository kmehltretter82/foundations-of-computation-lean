import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.Basic
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.GeneratedCallSearch

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

inductive BoundedSimulatorCanonicalInputParserState
    (pairState : Type uStage) where
  | scan : BoundedSimulatorCanonicalInputParserState pairState
  | rewindFirst : BoundedSimulatorCanonicalInputParserState pairState
  | rewindPrefix : BoundedSimulatorCanonicalInputParserState pairState
  | run : pairState ->
      BoundedSimulatorCanonicalInputParserState pairState

namespace BoundedSimulatorCanonicalInputParserState

def finite (hpair : Foundation.FiniteType pairState) :
    Foundation.FiniteType
      (BoundedSimulatorCanonicalInputParserState pairState) where
  elems := [scan, rewindFirst, rewindPrefix] ++ hpair.elems.map run
  complete := by
    intro state
    cases state with
    | scan =>
        simp
    | rewindFirst =>
        simp
    | rewindPrefix =>
        simp
    | run state =>
        simp
        exact hpair.complete state

end BoundedSimulatorCanonicalInputParserState

private abbrev BSCIPS :=
  BoundedSimulatorCanonicalInputParserState

def boundedSimulatorCanonicalInputParserMachine
    (pairRunner : TuringMachine MachineCodeSymbol pairState) :
    TuringMachine MachineCodeSymbol
      (BSCIPS pairState) where
  start := BoundedSimulatorCanonicalInputParserState.scan
  halt := BoundedSimulatorCanonicalInputParserState.run pairRunner.halt
  transition := fun state cell =>
    match state with
    | BoundedSimulatorCanonicalInputParserState.scan =>
        match cell with
        | some MachineCodeSymbol.tick =>
            some (some MachineCodeSymbol.tick, Direction.right,
              BoundedSimulatorCanonicalInputParserState.scan)
        | some MachineCodeSymbol.done =>
            some (some MachineCodeSymbol.done, Direction.right,
              BoundedSimulatorCanonicalInputParserState.rewindFirst)
        | _ => none
    | BoundedSimulatorCanonicalInputParserState.rewindFirst =>
        some (cell, Direction.left,
          BoundedSimulatorCanonicalInputParserState.rewindPrefix)
    | BoundedSimulatorCanonicalInputParserState.rewindPrefix =>
        match cell with
        | some MachineCodeSymbol.tick =>
            some (some MachineCodeSymbol.tick, Direction.left,
              BoundedSimulatorCanonicalInputParserState.rewindPrefix)
        | some MachineCodeSymbol.done =>
            some (some MachineCodeSymbol.done, Direction.left,
              BoundedSimulatorCanonicalInputParserState.rewindPrefix)
        | none =>
            some (none, Direction.right,
              BoundedSimulatorCanonicalInputParserState.run pairRunner.start)
        | _ => none
    | BoundedSimulatorCanonicalInputParserState.run state =>
        match pairRunner.transition state cell with
        | none => none
        | some (write, dir, nextState) =>
            some (write, dir,
              BoundedSimulatorCanonicalInputParserState.run nextState)
  statesFinite :=
    BoundedSimulatorCanonicalInputParserState.finite
      pairRunner.statesFinite

private abbrev BSCIPM
    {pairState : Type uStage}
    (pairRunner : TuringMachine MachineCodeSymbol pairState) :=
  boundedSimulatorCanonicalInputParserMachine pairRunner

def boundedSimulatorCanonicalInputParserScannedLeftRev :
    Nat -> Word MachineCodeSymbol -> Word MachineCodeSymbol
  | 0, leftRev => MachineCodeSymbol.done :: leftRev
  | stage + 1, leftRev =>
      boundedSimulatorCanonicalInputParserScannedLeftRev
        stage (MachineCodeSymbol.tick :: leftRev)

def boundedSimulatorCanonicalInputParserEncodedRight :
    Word MachineCodeSymbol -> List (Option MachineCodeSymbol)
  | [] => [none]
  | symbol :: suffix => (symbol :: suffix).map some

def boundedSimulatorCanonicalInputParserNoneBeforePrefixTape
    (stage : Nat) (encoded : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol where
  left := []
  head := none
  right :=
    List.append
      (List.replicate stage
        (some MachineCodeSymbol.tick : Option MachineCodeSymbol))
      (some MachineCodeSymbol.done ::
        boundedSimulatorCanonicalInputParserEncodedRight encoded)

def boundedSimulatorCanonicalInputParserNoneBeforeRightTape
    (right : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol where
  left := []
  head := none
  right := right

def boundedSimulatorCanonicalInputParserRewindTargetTape
    (stage : Nat) (head : MachineCodeSymbol)
    (right : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol where
  left := []
  head := none
  right :=
    List.append
      (List.replicate stage
        (some MachineCodeSymbol.tick : Option MachineCodeSymbol))
      (some head :: right)

theorem replicate_append_self_cons
    (n : Nat) (a : α) (xs : List α) :
    List.append (List.replicate n a) (a :: xs) =
      a :: List.append (List.replicate n a) xs := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate]
      exact ih

theorem boundedSimulatorCanonicalInputParserRewindTargetTape_succ
    (stage : Nat) (head : MachineCodeSymbol)
    (right : List (Option MachineCodeSymbol)) :
    boundedSimulatorCanonicalInputParserRewindTargetTape
        (stage + 1) head right =
      boundedSimulatorCanonicalInputParserRewindTargetTape
        stage MachineCodeSymbol.tick (some head :: right) := by
  simp [boundedSimulatorCanonicalInputParserRewindTargetTape,
    List.replicate]
  exact
    (replicate_append_self_cons stage
      (some MachineCodeSymbol.tick : Option MachineCodeSymbol)
      (some head :: right)).symm

theorem boundedSimulatorCanonicalInputParserScannedLeftRev_eq
    (stage : Nat) (leftRev : Word MachineCodeSymbol) :
    boundedSimulatorCanonicalInputParserScannedLeftRev stage leftRev =
      MachineCodeSymbol.done ::
        List.append
          (List.replicate stage MachineCodeSymbol.tick) leftRev := by
  induction stage generalizing leftRev with
  | zero =>
      rfl
  | succ stage ih =>
      rw [boundedSimulatorCanonicalInputParserScannedLeftRev, ih]
      rw [replicate_append_self_cons]
      simp [List.replicate]

theorem boundedSimulator_dropTrailingNone_replicate_tick_done_none
    (stage : Nat) :
    Tape.dropTrailingNone
        (List.append
          (List.replicate stage
            (some MachineCodeSymbol.tick : Option MachineCodeSymbol))
          [some MachineCodeSymbol.done, none]) =
      Tape.dropTrailingNone
        (List.append
          (List.replicate stage
            (some MachineCodeSymbol.tick : Option MachineCodeSymbol))
          [some MachineCodeSymbol.done]) := by
  induction stage with
  | zero =>
      rfl
  | succ stage ih =>
      simpa [List.replicate, Tape.dropTrailingNone] using ih

theorem boundedSimulatorCanonicalInputParser_handoffTape_equiv_input
    (stage : Nat) (encoded : Word MachineCodeSymbol) :
    Tape.Equiv
      (Tape.move Direction.right
        (boundedSimulatorCanonicalInputParserNoneBeforePrefixTape
          stage encoded))
      (Tape.input (CodePrefixRecognizerStageCode encoded stage)) := by
  induction stage with
  | zero =>
      cases encoded <;>
        simp [CodePrefixRecognizerStageCode,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          boundedSimulatorCanonicalInputParserNoneBeforePrefixTape,
          boundedSimulatorCanonicalInputParserEncodedRight,
          Tape.Equiv, Tape.move, Tape.moveRight,
          Tape.input, List.replicate,
          Tape.dropTrailingNone]
  | succ stage ih =>
      cases encoded with
      | nil =>
          simp [CodePrefixRecognizerStageCode,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat,
            codePrefixParserNormalizer_encodeNat_eq_replicate_tick_done,
            boundedSimulatorCanonicalInputParserNoneBeforePrefixTape,
            boundedSimulatorCanonicalInputParserEncodedRight,
            Tape.Equiv, Tape.move, Tape.moveRight,
            Tape.input, List.replicate,
            Tape.dropTrailingNone]
          exact
            boundedSimulator_dropTrailingNone_replicate_tick_done_none
              stage
      | cons head tail =>
          simp [CodePrefixRecognizerStageCode,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat,
            codePrefixParserNormalizer_encodeNat_eq_replicate_tick_done,
            boundedSimulatorCanonicalInputParserNoneBeforePrefixTape,
            boundedSimulatorCanonicalInputParserEncodedRight,
            Tape.Equiv, Tape.move, Tape.moveRight,
            Tape.input, List.replicate,
            Tape.dropTrailingNone]

theorem boundedSimulatorCanonicalInputParserMachine_step_scan_tick
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (BSCIPM pairRunner)
      { state := BoundedSimulatorCanonicalInputParserState.scan
        tape :=
          stageCodeDecoderTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := BoundedSimulatorCanonicalInputParserState.scan
        tape :=
          stageCodeDecoderTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← stageCodeDecoderTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [boundedSimulatorCanonicalInputParserMachine,
      stageCodeDecoderTape, Tape.read])

theorem boundedSimulatorCanonicalInputParserMachine_step_scan_done
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (BSCIPM pairRunner)
      { state := BoundedSimulatorCanonicalInputParserState.scan
        tape :=
          stageCodeDecoderTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := BoundedSimulatorCanonicalInputParserState.rewindFirst
        tape :=
          stageCodeDecoderTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← stageCodeDecoderTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [boundedSimulatorCanonicalInputParserMachine,
      stageCodeDecoderTape, Tape.read])

theorem boundedSimulatorCanonicalInputParserMachine_step_rewindFirst
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (BSCIPM pairRunner)
      { state := BoundedSimulatorCanonicalInputParserState.rewindFirst
        tape :=
          stageCodeDecoderTape
            (MachineCodeSymbol.done :: leftRev) suffix }
      { state := BoundedSimulatorCanonicalInputParserState.rewindPrefix
        tape :=
          Tape.move Direction.left
            (stageCodeDecoderTape
              (MachineCodeSymbol.done :: leftRev) suffix) } := by
  exact TuringMachine.Step.mk (by
    cases suffix <;>
      simp [boundedSimulatorCanonicalInputParserMachine,
        stageCodeDecoderTape, Tape.read])

theorem boundedSimulatorCanonicalInputParserMachine_step_rewindPrefix_done
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (BSCIPM pairRunner)
      { state := BoundedSimulatorCanonicalInputParserState.rewindPrefix
        tape :=
          stageCodeDecoderTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := BoundedSimulatorCanonicalInputParserState.rewindPrefix
        tape :=
          Tape.move Direction.left
            (stageCodeDecoderTape leftRev
              (MachineCodeSymbol.done :: suffix)) } := by
  exact TuringMachine.Step.mk (by
    simp [boundedSimulatorCanonicalInputParserMachine,
      stageCodeDecoderTape, Tape.read])

theorem boundedSimulatorCanonicalInputParserMachine_step_rewindPrefix_tick
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (BSCIPM pairRunner)
      { state := BoundedSimulatorCanonicalInputParserState.rewindPrefix
        tape :=
          stageCodeDecoderTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := BoundedSimulatorCanonicalInputParserState.rewindPrefix
        tape :=
          Tape.move Direction.left
            (stageCodeDecoderTape leftRev
              (MachineCodeSymbol.tick :: suffix)) } := by
  exact TuringMachine.Step.mk (by
    simp [boundedSimulatorCanonicalInputParserMachine,
      stageCodeDecoderTape, Tape.read])

theorem boundedSimulatorCanonicalInputParserMachine_step_rewindPrefix_none
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    (right : List (Option MachineCodeSymbol)) :
    TuringMachine.Step
      (BSCIPM pairRunner)
      { state := BoundedSimulatorCanonicalInputParserState.rewindPrefix
        tape :=
          boundedSimulatorCanonicalInputParserNoneBeforeRightTape
            right }
      { state := BoundedSimulatorCanonicalInputParserState.run
          pairRunner.start
        tape :=
          Tape.move Direction.right
            (boundedSimulatorCanonicalInputParserNoneBeforeRightTape
              right) } := by
  exact TuringMachine.Step.mk (by
    simp [boundedSimulatorCanonicalInputParserMachine,
      boundedSimulatorCanonicalInputParserNoneBeforeRightTape,
      Tape.read])

theorem boundedSimulatorCanonicalInputParserMachine_step_run
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    {state nextState : pairState}
    {tape : Tape MachineCodeSymbol} {write : Option MachineCodeSymbol}
    {dir : Direction}
    (haction :
      pairRunner.transition state (Tape.read tape) =
        some (write, dir, nextState)) :
    TuringMachine.Step
      (BSCIPM pairRunner)
      { state := BoundedSimulatorCanonicalInputParserState.run state
        tape := tape }
      { state := BoundedSimulatorCanonicalInputParserState.run nextState
        tape := Tape.move dir (Tape.write write tape) } := by
  exact TuringMachine.Step.mk (by
    simp [boundedSimulatorCanonicalInputParserMachine, haction])

theorem boundedSimulatorCanonicalInputParserMachine_computes_run
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    {c d : TuringMachine.Configuration MachineCodeSymbol pairState}
    (hcomp : TuringMachine.Computes pairRunner c d) :
    TuringMachine.Computes
      (BSCIPM pairRunner)
      { state := BoundedSimulatorCanonicalInputParserState.run c.state
        tape := c.tape }
      { state := BoundedSimulatorCanonicalInputParserState.run d.state
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      cases hstep with
      | mk haction =>
          exact TuringMachine.Computes.step
            (boundedSimulatorCanonicalInputParserMachine_step_run
              pairRunner haction)
            ih

theorem boundedSimulatorCanonicalInputParserMachine_computes_scan
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    (leftRev : Word MachineCodeSymbol)
    (stage : Nat) (encoded : Word MachineCodeSymbol) :
    TuringMachine.Computes
      (BSCIPM pairRunner)
      { state := BoundedSimulatorCanonicalInputParserState.scan
        tape :=
          stageCodeDecoderTape leftRev
            (CodePrefixRecognizerStageCode encoded stage) }
      { state :=
          BoundedSimulatorCanonicalInputParserState.rewindFirst
        tape :=
          stageCodeDecoderTape
            (boundedSimulatorCanonicalInputParserScannedLeftRev
              stage leftRev)
            encoded } := by
  induction stage generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.step
        (by
          simpa [CodePrefixRecognizerStageCode,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            boundedSimulatorCanonicalInputParserMachine_step_scan_done
              pairRunner leftRev encoded)
        (TuringMachine.Computes.refl _)
  | succ stage ih =>
      exact TuringMachine.Computes.step
        (by
          simpa [CodePrefixRecognizerStageCode,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            boundedSimulatorCanonicalInputParserMachine_step_scan_tick
              pairRunner leftRev
              (CodePrefixRecognizerStageCode encoded stage))
        (by
          simpa [boundedSimulatorCanonicalInputParserScannedLeftRev] using
            ih (MachineCodeSymbol.tick :: leftRev))

theorem boundedSimulatorCanonicalInputParserMachine_computes_rewindPrefix_to_none
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    (head : MachineCodeSymbol)
    (stage : Nat) (right : List (Option MachineCodeSymbol))
    (hhead :
      head = MachineCodeSymbol.tick ∨
        head = MachineCodeSymbol.done) :
    TuringMachine.Computes
      (BSCIPM pairRunner)
      { state :=
          BoundedSimulatorCanonicalInputParserState.rewindPrefix
        tape :=
          { left :=
              (List.replicate stage
                (some MachineCodeSymbol.tick :
                  Option MachineCodeSymbol))
            head := some head
            right := right } }
      { state :=
          BoundedSimulatorCanonicalInputParserState.rewindPrefix
        tape :=
          { left := []
            head := none
            right :=
              List.append
                (List.replicate stage
                  (some MachineCodeSymbol.tick :
                    Option MachineCodeSymbol))
                (some head :: right) } } := by
  induction stage generalizing head right with
  | zero =>
      have hstep :
          TuringMachine.Step
            (BSCIPM pairRunner)
            { state :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix
              tape :=
                { left := []
                  head := some head
                  right := right } }
            { state :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix
              tape :=
                { left := []
                  head := none
                  right := some head :: right } } := by
        rcases hhead with rfl | rfl
        · exact
            TuringMachine.Step.mk
              (M := BSCIPM pairRunner)
              (c :=
                { state :=
                    BoundedSimulatorCanonicalInputParserState.rewindPrefix
                  tape :=
                    { left := []
                      head := some MachineCodeSymbol.tick
                      right := right } })
              (write := some MachineCodeSymbol.tick)
              (dir := Direction.left)
              (nextState :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix)
              (by
                simp [BSCIPM,
                  boundedSimulatorCanonicalInputParserMachine,
                  Tape.read])
        · exact
            TuringMachine.Step.mk
              (M := BSCIPM pairRunner)
              (c :=
                { state :=
                    BoundedSimulatorCanonicalInputParserState.rewindPrefix
                  tape :=
                    { left := []
                      head := some MachineCodeSymbol.done
                      right := right } })
              (write := some MachineCodeSymbol.done)
              (dir := Direction.left)
              (nextState :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix)
              (by
                simp [BSCIPM,
                  boundedSimulatorCanonicalInputParserMachine,
                  Tape.read])
      exact TuringMachine.Computes.step hstep
        (TuringMachine.Computes.refl _)
  | succ stage ih =>
      have hstep :
          TuringMachine.Step
            (BSCIPM pairRunner)
            { state :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix
              tape :=
                { left :=
                    some MachineCodeSymbol.tick ::
                      List.replicate stage
                        (some MachineCodeSymbol.tick :
                          Option MachineCodeSymbol)
                  head := some head
                  right := right } }
            { state :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix
              tape :=
                { left :=
                    List.replicate stage
                      (some MachineCodeSymbol.tick :
                        Option MachineCodeSymbol)
                  head := some MachineCodeSymbol.tick
                  right := some head :: right } } := by
        rcases hhead with rfl | rfl
        · exact
            TuringMachine.Step.mk
              (M := BSCIPM pairRunner)
              (c :=
                { state :=
                    BoundedSimulatorCanonicalInputParserState.rewindPrefix
                  tape :=
                    { left :=
                        some MachineCodeSymbol.tick ::
                          List.replicate stage
                            (some MachineCodeSymbol.tick :
                              Option MachineCodeSymbol)
                      head := some MachineCodeSymbol.tick
                      right := right } })
              (write := some MachineCodeSymbol.tick)
              (dir := Direction.left)
              (nextState :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix)
              (by
                simp [BSCIPM,
                  boundedSimulatorCanonicalInputParserMachine,
                  Tape.read])
        · exact
            TuringMachine.Step.mk
              (M := BSCIPM pairRunner)
              (c :=
                { state :=
                    BoundedSimulatorCanonicalInputParserState.rewindPrefix
                  tape :=
                    { left :=
                        some MachineCodeSymbol.tick ::
                          List.replicate stage
                            (some MachineCodeSymbol.tick :
                              Option MachineCodeSymbol)
                      head := some MachineCodeSymbol.done
                      right := right } })
              (write := some MachineCodeSymbol.done)
              (dir := Direction.left)
              (nextState :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix)
              (by
                simp [BSCIPM,
                  boundedSimulatorCanonicalInputParserMachine,
                  Tape.read])
      exact TuringMachine.Computes.step hstep
        (by
          have htail :=
            ih MachineCodeSymbol.tick (some head :: right)
              (Or.inl rfl)
          have hright :
              List.append
                  (List.replicate stage
                    (some MachineCodeSymbol.tick :
                      Option MachineCodeSymbol))
                  (some MachineCodeSymbol.tick :: some head :: right) =
                some MachineCodeSymbol.tick ::
                  List.append
                    (List.replicate stage
                      (some MachineCodeSymbol.tick :
                        Option MachineCodeSymbol))
                    (some head :: right) :=
            replicate_append_self_cons stage
              (some MachineCodeSymbol.tick : Option MachineCodeSymbol)
              (some head :: right)
          rw [hright] at htail
          simpa [List.replicate] using htail)

theorem boundedSimulatorCanonicalInputParserMachine_computes_rewindFirst
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    (stage : Nat) (encoded : Word MachineCodeSymbol) :
    exists tape : Tape MachineCodeSymbol,
      TuringMachine.Computes
        (BSCIPM pairRunner)
        { state :=
            BoundedSimulatorCanonicalInputParserState.rewindFirst
          tape :=
            stageCodeDecoderTape
              (boundedSimulatorCanonicalInputParserScannedLeftRev
                stage [])
              encoded }
        { state :=
            BoundedSimulatorCanonicalInputParserState.run
              pairRunner.start
          tape := tape } ∧
        Tape.Equiv tape
          (Tape.input (CodePrefixRecognizerStageCode encoded stage)) := by
  let right :=
    List.append
      (List.replicate stage
        (some MachineCodeSymbol.tick : Option MachineCodeSymbol))
      (some MachineCodeSymbol.done ::
        boundedSimulatorCanonicalInputParserEncodedRight encoded)
  refine
    Exists.intro
      (Tape.move Direction.right
        (boundedSimulatorCanonicalInputParserNoneBeforePrefixTape
          stage encoded)) ?_
  constructor
  · have hfirst :
        TuringMachine.Step
          (BSCIPM pairRunner)
          { state :=
              BoundedSimulatorCanonicalInputParserState.rewindFirst
            tape :=
              stageCodeDecoderTape
                (boundedSimulatorCanonicalInputParserScannedLeftRev
                  stage [])
                encoded }
          { state :=
              BoundedSimulatorCanonicalInputParserState.rewindPrefix
            tape :=
              Tape.move Direction.left
                (stageCodeDecoderTape
                  (MachineCodeSymbol.done ::
                    List.replicate stage MachineCodeSymbol.tick)
                  encoded) } := by
        simpa [boundedSimulatorCanonicalInputParserScannedLeftRev_eq]
          using
            (boundedSimulatorCanonicalInputParserMachine_step_rewindFirst
              pairRunner
              (List.replicate stage MachineCodeSymbol.tick)
              encoded)
    have hrewind :
          TuringMachine.Computes
            (BSCIPM pairRunner)
            { state :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix
              tape :=
                Tape.move Direction.left
                  (stageCodeDecoderTape
                    (MachineCodeSymbol.done ::
                      List.replicate stage MachineCodeSymbol.tick)
                    encoded) }
            { state :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix
              tape :=
                boundedSimulatorCanonicalInputParserNoneBeforePrefixTape
                  stage encoded } := by
        cases encoded with
        | nil =>
            simpa [stageCodeDecoderTape, Tape.move, Tape.moveLeft,
              boundedSimulatorCanonicalInputParserNoneBeforePrefixTape,
              boundedSimulatorCanonicalInputParserEncodedRight, right] using
              (boundedSimulatorCanonicalInputParserMachine_computes_rewindPrefix_to_none
                pairRunner MachineCodeSymbol.done stage [none]
                (Or.inr rfl))
        | cons head tail =>
            simpa [stageCodeDecoderTape, Tape.move, Tape.moveLeft,
              boundedSimulatorCanonicalInputParserNoneBeforePrefixTape,
              boundedSimulatorCanonicalInputParserEncodedRight, right] using
              (boundedSimulatorCanonicalInputParserMachine_computes_rewindPrefix_to_none
                pairRunner MachineCodeSymbol.done stage
                ((head :: tail).map some) (Or.inr rfl))
    have hnone :
          TuringMachine.Step
            (BSCIPM pairRunner)
            { state :=
                BoundedSimulatorCanonicalInputParserState.rewindPrefix
              tape :=
                boundedSimulatorCanonicalInputParserNoneBeforePrefixTape
                  stage encoded }
            { state :=
                BoundedSimulatorCanonicalInputParserState.run
                  pairRunner.start
              tape :=
                Tape.move Direction.right
                  (boundedSimulatorCanonicalInputParserNoneBeforePrefixTape
                    stage encoded) } := by
        simpa [boundedSimulatorCanonicalInputParserNoneBeforePrefixTape,
          right] using
          (boundedSimulatorCanonicalInputParserMachine_step_rewindPrefix_none
            pairRunner right)
    exact
        TuringMachine.Computes.step hfirst
          (TuringMachine.computes_trans hrewind
            (TuringMachine.Computes.step hnone
              (TuringMachine.Computes.refl _)))
  · exact
      boundedSimulatorCanonicalInputParser_handoffTape_equiv_input
        stage encoded

theorem boundedSimulatorCanonicalInputParserMachine_halts_of_pairRunner
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    (stage : Nat) (encoded : Word MachineCodeSymbol)
    (hpair :
      TuringMachine.HaltsOnInput pairRunner
        (CodePrefixRecognizerStageCode encoded stage)) :
    TuringMachine.HaltsOnInput (BSCIPM pairRunner)
      (CodePrefixRecognizerStageCode encoded stage) := by
  rcases
      boundedSimulatorCanonicalInputParserMachine_computes_rewindFirst
        pairRunner stage encoded with
    ⟨handoffTape, hrewind, hequiv⟩
  have hpairFrom :
      TuringMachine.HaltsFrom pairRunner
        { state := pairRunner.start
          tape := handoffTape } := by
    have hinput :
        TuringMachine.HaltsFrom pairRunner
          { state := pairRunner.start
            tape :=
              Tape.input
                (CodePrefixRecognizerStageCode encoded stage) } := by
      simpa [TuringMachine.HaltsOnInput, TuringMachine.initial]
        using hpair
    exact
      (turingMachine_haltsFrom_tape_equiv_iff
        pairRunner pairRunner.start (Tape.Equiv.symm hequiv)).mp
        hinput
  rcases hpairFrom with ⟨pairFinal, hpairComp, hpairHalt⟩
  have hscan :=
    boundedSimulatorCanonicalInputParserMachine_computes_scan
      pairRunner ([] : Word MachineCodeSymbol) stage encoded
  have hrun :
      TuringMachine.Computes
        (BSCIPM pairRunner)
        { state :=
            BoundedSimulatorCanonicalInputParserState.run
              pairRunner.start
          tape := handoffTape }
        { state :=
            BoundedSimulatorCanonicalInputParserState.run
              pairFinal.state
          tape := pairFinal.tape } :=
    boundedSimulatorCanonicalInputParserMachine_computes_run
      pairRunner hpairComp
  have hhalt :
      TuringMachine.Halted
        (BSCIPM pairRunner)
        { state :=
            BoundedSimulatorCanonicalInputParserState.run
              pairFinal.state
          tape := pairFinal.tape } := by
    have hstate : pairFinal.state = pairRunner.halt := by
      simpa [TuringMachine.Halted] using hpairHalt
    simp [TuringMachine.Halted,
      boundedSimulatorCanonicalInputParserMachine, hstate]
  have hcomp :
      TuringMachine.Computes
        (BSCIPM pairRunner)
        (TuringMachine.initial
          (BSCIPM pairRunner)
          (CodePrefixRecognizerStageCode encoded stage))
        { state :=
            BoundedSimulatorCanonicalInputParserState.run
              pairFinal.state
          tape := pairFinal.tape } := by
    simpa [TuringMachine.initial,
      boundedSimulatorCanonicalInputParserMachine,
      stageCodeDecoderTape_nil_eq_input] using
      TuringMachine.computes_trans hscan
        (TuringMachine.computes_trans hrewind hrun)
  exact ⟨_, hcomp, hhalt⟩

theorem boundedSimulatorCanonicalInputParserMachine_halts_run_only
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    {steps : Nat} {state : pairState}
    {tape : Tape MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (BSCIPM pairRunner)
        steps
        { state :=
            BoundedSimulatorCanonicalInputParserState.run state
          tape := tape }) :
    TuringMachine.HaltsFrom pairRunner
      { state := state
        tape := tape } := by
  induction steps generalizing state tape with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp
      simp [TuringMachine.Halted,
        boundedSimulatorCanonicalInputParserMachine] at hfinal
      subst state
      exact TuringMachine.halts_from_halted rfl
  | succ steps ih =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | succ hstep hrest =>
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              cases hpair :
                  pairRunner.transition state (Tape.read tape) with
              | none =>
                  simp [boundedSimulatorCanonicalInputParserMachine,
                    hpair] at haction
              | some action =>
                  rcases action with ⟨write', dir', nextState'⟩
                  simp [boundedSimulatorCanonicalInputParserMachine,
                    hpair] at haction
                  rcases haction with ⟨hwrite, hdir, hnext⟩
                  subst write
                  subst dir
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        (BSCIPM pairRunner)
                        steps
                        { state :=
                            BoundedSimulatorCanonicalInputParserState.run
                              nextState'
                          tape :=
                            Tape.move dir'
                              (Tape.write write' tape) } :=
                    ⟨final, hrest, hfinal⟩
                  rcases ih htail with
                    ⟨pairFinal, hpairComp, hpairHalt⟩
                  exact
                    ⟨pairFinal,
                      TuringMachine.Computes.step
                        (TuringMachine.Step.mk hpair) hpairComp,
                      hpairHalt⟩

theorem boundedSimulatorCanonicalInputParserMachine_halts_noneBeforePrefix_generic_only
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    {steps : Nat} {right : List (Option MachineCodeSymbol)}
    (hhalt :
      TuringMachine.HaltsFromIn
        (BSCIPM pairRunner)
        steps
        { state :=
            BoundedSimulatorCanonicalInputParserState.rewindPrefix
          tape :=
            boundedSimulatorCanonicalInputParserNoneBeforeRightTape
              right }) :
    TuringMachine.HaltsFrom pairRunner
      { state := pairRunner.start
        tape :=
          Tape.move Direction.right
            (boundedSimulatorCanonicalInputParserNoneBeforeRightTape
              right) } := by
  cases steps with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp
      simp [TuringMachine.Halted,
        boundedSimulatorCanonicalInputParserMachine] at hfinal
  | succ steps =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | succ hstep hrest =>
          cases hstep with
          | mk haction =>
              simp [boundedSimulatorCanonicalInputParserMachine,
                boundedSimulatorCanonicalInputParserNoneBeforeRightTape,
                Tape.read] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              subst hwrite
              subst hdir
              cases hnext
              exact
                boundedSimulatorCanonicalInputParserMachine_halts_run_only
                  pairRunner
                  (steps := steps)
                  (state := pairRunner.start)
                  (tape :=
                    Tape.move Direction.right
                      (boundedSimulatorCanonicalInputParserNoneBeforeRightTape
                        right))
                  ⟨final, hrest, hfinal⟩

theorem boundedSimulatorCanonicalInputParserMachine_halts_rewindPrefix_generic_only
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    {steps stage : Nat} {head : MachineCodeSymbol}
    {right : List (Option MachineCodeSymbol)}
    (hhead :
      head = MachineCodeSymbol.tick ∨
        head = MachineCodeSymbol.done)
    (hhalt :
      TuringMachine.HaltsFromIn
        (BSCIPM pairRunner)
        steps
        { state :=
            BoundedSimulatorCanonicalInputParserState.rewindPrefix
          tape :=
            { left :=
                List.replicate stage
                  (some MachineCodeSymbol.tick :
                    Option MachineCodeSymbol)
              head := some head
              right := right } }) :
    TuringMachine.HaltsFrom pairRunner
      { state := pairRunner.start
        tape :=
          Tape.move Direction.right
            (boundedSimulatorCanonicalInputParserRewindTargetTape
              stage head right) } := by
  induction stage generalizing steps head right with
  | zero =>
      cases steps with
      | zero =>
          rcases hhalt with ⟨final, hcomp, hfinal⟩
          cases hcomp
          simp [TuringMachine.Halted,
            boundedSimulatorCanonicalInputParserMachine] at hfinal
      | succ steps =>
          rcases hhalt with ⟨final, hcomp, hfinal⟩
          cases hcomp with
          | succ hstep hrest =>
              cases hstep with
              | mk haction =>
                  rcases hhead with rfl | rfl
                  · simp [boundedSimulatorCanonicalInputParserMachine,
                      Tape.read] at haction
                    rcases haction with ⟨hwrite, hdir, hnext⟩
                    subst hwrite
                    subst hdir
                    cases hnext
                    simpa [List.replicate] using
                      boundedSimulatorCanonicalInputParserMachine_halts_noneBeforePrefix_generic_only
                        pairRunner
                        (steps := steps)
                        (right := some MachineCodeSymbol.tick :: right)
                        ⟨final, hrest, hfinal⟩
                  · simp [boundedSimulatorCanonicalInputParserMachine,
                      Tape.read] at haction
                    rcases haction with ⟨hwrite, hdir, hnext⟩
                    subst hwrite
                    subst hdir
                    cases hnext
                    simpa [List.replicate] using
                      boundedSimulatorCanonicalInputParserMachine_halts_noneBeforePrefix_generic_only
                        pairRunner
                        (steps := steps)
                        (right := some MachineCodeSymbol.done :: right)
                        ⟨final, hrest, hfinal⟩
  | succ stage ih =>
      cases steps with
      | zero =>
          rcases hhalt with ⟨final, hcomp, hfinal⟩
          cases hcomp
          simp [TuringMachine.Halted,
            boundedSimulatorCanonicalInputParserMachine] at hfinal
      | succ steps =>
          rcases hhalt with ⟨final, hcomp, hfinal⟩
          cases hcomp with
          | succ hstep hrest =>
              cases hstep with
              | mk haction =>
                  rcases hhead with rfl | rfl
                  · simp [boundedSimulatorCanonicalInputParserMachine,
                      Tape.read] at haction
                    rcases haction with ⟨hwrite, hdir, hnext⟩
                    subst hwrite
                    subst hdir
                    cases hnext
                    have htail :=
                      ih
                        (steps := steps)
                        (head := MachineCodeSymbol.tick)
                        (right :=
                          some MachineCodeSymbol.tick :: right)
                        (Or.inl rfl)
                        ⟨final, hrest, hfinal⟩
                    simpa
                      [boundedSimulatorCanonicalInputParserRewindTargetTape_succ]
                      using htail
                  · simp [boundedSimulatorCanonicalInputParserMachine,
                      Tape.read] at haction
                    rcases haction with ⟨hwrite, hdir, hnext⟩
                    subst hwrite
                    subst hdir
                    cases hnext
                    have htail :=
                      ih
                        (steps := steps)
                        (head := MachineCodeSymbol.tick)
                        (right :=
                          some MachineCodeSymbol.done :: right)
                        (Or.inl rfl)
                        ⟨final, hrest, hfinal⟩
                    simpa
                      [boundedSimulatorCanonicalInputParserRewindTargetTape_succ]
                      using htail

theorem boundedSimulatorCanonicalInputParserMachine_halts_noneBeforePrefix_only
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    {steps stage : Nat} {encoded : Word MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (BSCIPM pairRunner)
        steps
        { state :=
            BoundedSimulatorCanonicalInputParserState.rewindPrefix
          tape :=
            boundedSimulatorCanonicalInputParserNoneBeforePrefixTape
              stage encoded }) :
    TuringMachine.HaltsFrom pairRunner
      { state := pairRunner.start
        tape :=
          Tape.move Direction.right
            (boundedSimulatorCanonicalInputParserNoneBeforePrefixTape
              stage encoded) } := by
  cases steps with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp
      simp [TuringMachine.Halted,
        boundedSimulatorCanonicalInputParserMachine] at hfinal
  | succ steps =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | succ hstep hrest =>
          cases hstep with
          | mk haction =>
              simp [boundedSimulatorCanonicalInputParserMachine,
                boundedSimulatorCanonicalInputParserNoneBeforePrefixTape,
                Tape.read] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              subst hwrite
              subst hdir
              cases hnext
              exact
                boundedSimulatorCanonicalInputParserMachine_halts_run_only
                  pairRunner
                  (steps := steps)
                  (state := pairRunner.start)
                  (tape :=
                    Tape.move Direction.right
                      (boundedSimulatorCanonicalInputParserNoneBeforePrefixTape
                        stage encoded))
                  ⟨final, hrest, hfinal⟩

theorem boundedSimulatorCanonicalInputParserMachine_halts_rewindFirst_only
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    {steps stage : Nat} {encoded : Word MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (BSCIPM pairRunner)
        steps
        { state :=
            BoundedSimulatorCanonicalInputParserState.rewindFirst
          tape :=
            stageCodeDecoderTape
              (boundedSimulatorCanonicalInputParserScannedLeftRev
                stage [])
              encoded }) :
    TuringMachine.HaltsOnInput pairRunner
      (CodePrefixRecognizerStageCode encoded stage) := by
  have hpairFrom :
      TuringMachine.HaltsFrom pairRunner
        { state := pairRunner.start
          tape :=
            Tape.move Direction.right
              (boundedSimulatorCanonicalInputParserRewindTargetTape
                stage MachineCodeSymbol.done
                (boundedSimulatorCanonicalInputParserEncodedRight
                  encoded)) } := by
    cases steps with
    | zero =>
        rcases hhalt with ⟨final, hcomp, hfinal⟩
        cases hcomp
        simp [TuringMachine.Halted,
          boundedSimulatorCanonicalInputParserMachine] at hfinal
    | succ steps =>
        rcases hhalt with ⟨final, hcomp, hfinal⟩
        cases hcomp with
        | succ hstep hrest =>
            cases hstep with
            | mk haction =>
                cases encoded with
                | nil =>
                    simp [boundedSimulatorCanonicalInputParserMachine,
                      boundedSimulatorCanonicalInputParserScannedLeftRev_eq,
                      stageCodeDecoderTape, Tape.read] at haction
                    rcases haction with ⟨hwrite, hdir, hnext⟩
                    subst hwrite
                    subst hdir
                    cases hnext
                    have hrewind :
                        TuringMachine.HaltsFromIn
                          (BSCIPM pairRunner)
                          steps
                          { state :=
                              BoundedSimulatorCanonicalInputParserState.rewindPrefix
                            tape :=
                              { left :=
                                  List.replicate stage
                                    (some MachineCodeSymbol.tick :
                                      Option MachineCodeSymbol)
                                head := some MachineCodeSymbol.done
                                right :=
                                  boundedSimulatorCanonicalInputParserEncodedRight
                                    ([] : Word MachineCodeSymbol) } } := by
                      refine ⟨final, ?_, hfinal⟩
                      simpa [
                        boundedSimulatorCanonicalInputParserScannedLeftRev_eq,
                        stageCodeDecoderTape, Tape.write, Tape.move,
                        Tape.moveLeft,
                        boundedSimulatorCanonicalInputParserEncodedRight]
                        using hrest
                    exact
                      boundedSimulatorCanonicalInputParserMachine_halts_rewindPrefix_generic_only
                        pairRunner
                        (steps := steps)
                        (stage := stage)
                        (head := MachineCodeSymbol.done)
                        (right :=
                          boundedSimulatorCanonicalInputParserEncodedRight
                            ([] : Word MachineCodeSymbol))
                        (Or.inr rfl)
                        hrewind
                | cons head tail =>
                    simp [boundedSimulatorCanonicalInputParserMachine,
                      boundedSimulatorCanonicalInputParserScannedLeftRev_eq,
                      stageCodeDecoderTape, Tape.read] at haction
                    rcases haction with ⟨hwrite, hdir, hnext⟩
                    subst hwrite
                    subst hdir
                    cases hnext
                    have hrewind :
                        TuringMachine.HaltsFromIn
                          (BSCIPM pairRunner)
                          steps
                          { state :=
                              BoundedSimulatorCanonicalInputParserState.rewindPrefix
                            tape :=
                              { left :=
                                  List.replicate stage
                                    (some MachineCodeSymbol.tick :
                                      Option MachineCodeSymbol)
                                head := some MachineCodeSymbol.done
                                right :=
                                  boundedSimulatorCanonicalInputParserEncodedRight
                                    (head :: tail) } } := by
                      refine ⟨final, ?_, hfinal⟩
                      simpa [
                        boundedSimulatorCanonicalInputParserScannedLeftRev_eq,
                        stageCodeDecoderTape, Tape.write, Tape.move,
                        Tape.moveLeft,
                        boundedSimulatorCanonicalInputParserEncodedRight]
                        using hrest
                    exact
                      boundedSimulatorCanonicalInputParserMachine_halts_rewindPrefix_generic_only
                        pairRunner
                        (steps := steps)
                        (stage := stage)
                        (head := MachineCodeSymbol.done)
                        (right :=
                          boundedSimulatorCanonicalInputParserEncodedRight
                            (head :: tail))
                        (Or.inr rfl)
                        hrewind
  have hequiv :
      Tape.Equiv
        (Tape.move Direction.right
          (boundedSimulatorCanonicalInputParserRewindTargetTape
            stage MachineCodeSymbol.done
            (boundedSimulatorCanonicalInputParserEncodedRight encoded)))
        (Tape.input (CodePrefixRecognizerStageCode encoded stage)) := by
    simpa [boundedSimulatorCanonicalInputParserRewindTargetTape,
      boundedSimulatorCanonicalInputParserNoneBeforePrefixTape] using
      boundedSimulatorCanonicalInputParser_handoffTape_equiv_input
        stage encoded
  have hinput :
      TuringMachine.HaltsFrom pairRunner
        { state := pairRunner.start
          tape :=
            Tape.input (CodePrefixRecognizerStageCode encoded stage) } :=
    (turingMachine_haltsFrom_tape_equiv_iff
      pairRunner pairRunner.start hequiv).mp hpairFrom
  simpa [TuringMachine.HaltsOnInput, TuringMachine.initial] using hinput

theorem boundedSimulatorCanonicalInputParserMachine_halts_scan_only_acc
    (pairRunner : TuringMachine MachineCodeSymbol pairState)
    {steps scanned : Nat} {rest : Word MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (BSCIPM pairRunner)
        steps
        { state := BoundedSimulatorCanonicalInputParserState.scan
          tape :=
            stageCodeDecoderTape
              (List.replicate scanned MachineCodeSymbol.tick)
              rest }) :
    exists stage : Nat,
    exists encoded : Word MachineCodeSymbol,
      rest = CodePrefixRecognizerStageCode encoded stage ∧
        TuringMachine.HaltsOnInput pairRunner
          (CodePrefixRecognizerStageCode encoded (scanned + stage)) := by
  induction steps generalizing scanned rest with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp
      simp [TuringMachine.Halted,
        boundedSimulatorCanonicalInputParserMachine] at hfinal
  | succ steps ih =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [boundedSimulatorCanonicalInputParserMachine,
                    stageCodeDecoderTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [boundedSimulatorCanonicalInputParserMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [boundedSimulatorCanonicalInputParserMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      simp [boundedSimulatorCanonicalInputParserMachine,
                        stageCodeDecoderTape, Tape.read] at haction
                      rcases haction with ⟨hwrite, hdir, hnext⟩
                      subst hwrite
                      subst hdir
                      cases hnext
                      have htail :
                          TuringMachine.HaltsFromIn
                            (BSCIPM pairRunner)
                            steps
                            { state :=
                                BoundedSimulatorCanonicalInputParserState.scan
                              tape :=
                                stageCodeDecoderTape
                                  (List.replicate (Nat.succ scanned)
                                    MachineCodeSymbol.tick)
                                  suffix } := by
                        refine ⟨final, ?_, hfinal⟩
                        cases suffix <;>
                          simpa [stageCodeDecoderTape,
                            stageCodeDecoderTape_move_right,
                            Tape.write, Tape.move, Tape.moveRight,
                            List.replicate] using hrest
                      rcases ih htail with
                        ⟨stage, encoded, hsuffix, hpair⟩
                      refine ⟨stage + 1, encoded, ?_, ?_⟩
                      · simp [CodePrefixRecognizerStageCode,
                          MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]
                      · have hbudget :
                            Nat.succ scanned + stage =
                              scanned + (stage + 1) := by
                          omega
                        simpa [hbudget] using hpair
              | done =>
                  cases hstep with
                  | mk haction =>
                      simp [boundedSimulatorCanonicalInputParserMachine,
                        stageCodeDecoderTape, Tape.read] at haction
                      rcases haction with ⟨hwrite, hdir, hnext⟩
                      subst hwrite
                      subst hdir
                      cases hnext
                      have hrewind :
                          TuringMachine.HaltsFromIn
                            (BSCIPM pairRunner)
                            steps
                            { state :=
                                BoundedSimulatorCanonicalInputParserState.rewindFirst
                              tape :=
                                stageCodeDecoderTape
                                  (boundedSimulatorCanonicalInputParserScannedLeftRev
                                    scanned [])
                                  suffix } := by
                        refine ⟨final, ?_, hfinal⟩
                        cases suffix <;>
                          simpa [
                            boundedSimulatorCanonicalInputParserScannedLeftRev_eq,
                            stageCodeDecoderTape,
                            stageCodeDecoderTape_move_right,
                            Tape.write, Tape.move, Tape.moveRight]
                            using hrest
                      have hpair :=
                        boundedSimulatorCanonicalInputParserMachine_halts_rewindFirst_only
                          pairRunner
                          (steps := steps)
                          (stage := scanned)
                          (encoded := suffix)
                          hrewind
                      exact ⟨0, suffix, by
                        simp [CodePrefixRecognizerStageCode,
                          MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat],
                        by simpa using hpair⟩
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [boundedSimulatorCanonicalInputParserMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [boundedSimulatorCanonicalInputParserMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [boundedSimulatorCanonicalInputParserMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [boundedSimulatorCanonicalInputParserMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [boundedSimulatorCanonicalInputParserMachine,
                        stageCodeDecoderTape, Tape.read] at haction

/--
Canonical-input wrapper obligation for the bounded simulator loop.  The
machine parses a {name}`CodePrefixRecognizerStageCode` input and dispatches
the preserved canonical input to the supplied pair runner.
-/
def CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalInputParserObligation
    {pairState : Type uStage}
    (pairRunner : TuringMachine MachineCodeSymbol pairState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens <->
        exists budget : Nat,
        exists encoded : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode encoded budget ∧
            TuringMachine.HaltsOnInput pairRunner
              (CodePrefixRecognizerStageCode encoded budget)

/--
Bounded pair-loop obligation for the canonical bounded simulator loop.  The
machine enumerates bounded {lit}`(checkedStage, fuel)` pairs, rebuilds each
checked stage-code input, and runs the supplied simulator for the selected
fuel.
-/
def CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorPairLoopObligation
    {simulatorState : Type uSimulator}
    (simulator : TuringMachine MachineCodeSymbol simulatorState) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    forall encoded : Word MachineCodeSymbol,
    forall budget : Nat,
      TuringMachine.HaltsOnInput runner
          (CodePrefixRecognizerStageCode encoded budget) <->
        exists checkedStage : Nat,
        exists fuel : Nat,
          checkedStage ≤ budget ∧
            fuel ≤ budget ∧
            TuringMachine.HaltsOnInputIn simulator fuel
              (CodePrefixRecognizerStageCode encoded checkedStage)

/--
Finite-machine leaf for parsing canonical stage-code input before invoking a
bounded pair runner.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalInputParserFiniteLeaf
    {pairState : Type}
    (pairRunner : TuringMachine MachineCodeSymbol pairState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalInputParserObligation
      pairRunner := by
  refine ⟨BSCIPS pairState, BSCIPM pairRunner, ?_⟩
  intro tokens
  constructor
  · intro hhalt
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hhalt with
      ⟨steps, hsteps⟩
    have hfrom :
        TuringMachine.HaltsFromIn
          (BSCIPM pairRunner)
          steps
          { state := BoundedSimulatorCanonicalInputParserState.scan
            tape :=
              stageCodeDecoderTape
                (List.replicate 0 MachineCodeSymbol.tick)
                tokens } := by
      simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
        boundedSimulatorCanonicalInputParserMachine,
        stageCodeDecoderTape_nil_eq_input, List.replicate] using
        hsteps
    rcases
        boundedSimulatorCanonicalInputParserMachine_halts_scan_only_acc
          pairRunner
          (steps := steps)
          (scanned := 0)
          (rest := tokens)
          hfrom with
      ⟨budget, encoded, htokens, hpair⟩
    exact ⟨budget, encoded, htokens, by simpa using hpair⟩
  · intro htarget
    rcases htarget with ⟨budget, encoded, rfl, hpair⟩
    exact
      boundedSimulatorCanonicalInputParserMachine_halts_of_pairRunner
        pairRunner budget encoded hpair

/--
Finite-machine leaf for the bounded pair loop.  This is the transition-table
work that enumerates bounded pairs, rebuilds checked stage-code inputs, and
runs the supplied simulator for the selected fuel.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorPairLoopFiniteLeaf
    {simulatorState : Type uSimulator}
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorPairLoopObligation
      simulator := by
  sorry

/--
Adapter from the parser wrapper and pair-loop construction to the canonical
raw-loop contract.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopFiniteLeaf
    {simulatorState : Type uSimulator}
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopObligation
      simulator := by
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorPairLoopFiniteLeaf
        simulator with
    ⟨pairState, pairRunner, hpairRunner⟩
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalInputParserFiniteLeaf
        pairRunner with
    ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro tokens
  constructor
  · intro hhalt
    rcases (hrunner tokens).mp hhalt with
      ⟨budget, encoded, htokens, hpair⟩
    rcases (hpairRunner encoded budget).mp hpair with
      ⟨checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩
    exact
      ⟨budget, encoded, checkedStage, fuel, htokens,
        hcheckedStage, hfuel, hsimulator⟩
  · intro htarget
    rcases htarget with
      ⟨budget, encoded, checkedStage, fuel, htokens,
        hcheckedStage, hfuel, hsimulator⟩
    exact (hrunner tokens).mpr
      ⟨budget, encoded, htokens,
        (hpairRunner encoded budget).mpr
          ⟨checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩⟩

/--
Adapter from the canonical bounded simulator loop to the
{name}`MachineDescription.decodeNat` contract.  The transition-table work lives
in {name}`codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopFiniteLeaf`;
this theorem only exposes the parsed budget and payload.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorDecodeNatFiniteLeaf
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopDecodeNatObligation
      simulator := by
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopFiniteLeaf
        simulator with
    ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro tokens
  constructor
  · intro hhalt
    rcases (hrunner tokens).mp hhalt with
      ⟨budget, encoded, checkedStage, fuel, htokens,
        hcheckedStage, hfuel, hsimulator⟩
    exact
      ⟨budget, encoded, checkedStage, fuel,
        by
          rw [htokens]
          exact codePrefixRecognizerStageCode_decodeNat encoded budget,
        hcheckedStage, hfuel, hsimulator⟩
  · intro htarget
    rcases htarget with
      ⟨budget, encoded, checkedStage, fuel, hdecode,
        hcheckedStage, hfuel, hsimulator⟩
    exact (hrunner tokens).mpr
      ⟨budget, encoded, checkedStage, fuel,
        codePrefixRecognizerStageCode_eq_of_decodeNat hdecode,
        hcheckedStage, hfuel, hsimulator⟩

/-- Canonical bounded-loop construction, exposed under the core name. -/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopObligation_core
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopObligation
      simulator := by
  exact
    codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorCanonicalRawLoopFiniteLeaf
      simulator

/--
Concrete transition-table obligation for the bounded simulator loop after the
outer stage-code parser has been exposed as a
{name}`MachineDescription.decodeNat` contract.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopDecodeNatObligation_core
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopDecodeNatObligation
      simulator := by
  exact
    codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorDecodeNatFiniteLeaf
      simulator

/--
Concrete transition-table obligation for the bounded simulator loop.  It must
parse the outer budget code, enumerate bounded {lit}`(checkedStage, fuel)`
pairs, rebuild the checked stage-code input, and run the fixed simulator for
the selected fuel.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopObligation_core
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopObligation
      simulator := by
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopDecodeNatObligation_core
        simulator with
    ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro tokens
  constructor
  · intro hhalt
    rcases (hrunner tokens).mp hhalt with
      ⟨budget, encoded, checkedStage, fuel, hdecode,
        hcheckedStage, hfuel, hsimulator⟩
    exact
      ⟨budget, encoded, checkedStage, fuel,
        codePrefixRecognizerStageCode_eq_of_decodeNat hdecode,
        hcheckedStage, hfuel, hsimulator⟩
  · intro htarget
    rcases htarget with
      ⟨budget, encoded, checkedStage, fuel, htokens,
        hcheckedStage, hfuel, hsimulator⟩
    exact (hrunner tokens).mpr
      ⟨budget, encoded, checkedStage, fuel,
        by
          rw [htokens]
          exact codePrefixRecognizerStageCode_decodeNat encoded budget,
        hcheckedStage, hfuel, hsimulator⟩

end Computability
end FoC
