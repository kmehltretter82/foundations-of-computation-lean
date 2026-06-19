import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser

set_option doc.verso true

/-!
# Description-prefix identity normalizer

The normalizer validates one complete machine-description prefix while
restoring every temporary marker before halting.  Its accepting runs therefore
preserve the normalized input word exactly.
-/

namespace FoC
namespace Computability

open Languages

theorem tape_normalizedOutput_move_left
    (T : Tape MachineCodeSymbol) :
    Tape.normalizedOutput (Tape.move Direction.left T) =
      Tape.normalizedOutput T := by
  cases T with
  | mk left head right =>
      cases left with
      | nil =>
          simp [Tape.move, Tape.moveLeft, Tape.normalizedOutput,
            Tape.cells]
      | cons leftHead leftTail =>
          simp [Tape.move, Tape.moveLeft, Tape.normalizedOutput,
            Tape.cells, List.reverse_cons, List.append_assoc]

theorem tape_normalizedOutput_move_right
    (T : Tape MachineCodeSymbol) :
    Tape.normalizedOutput (Tape.move Direction.right T) =
      Tape.normalizedOutput T := by
  cases T with
  | mk left head right =>
      cases right with
      | nil =>
          cases head <;>
            simp [Tape.move, Tape.moveRight, Tape.normalizedOutput,
              Tape.cells, List.reverse_cons, List.append_assoc]
      | cons rightHead rightTail =>
          simp [Tape.move, Tape.moveRight, Tape.normalizedOutput,
            Tape.cells, List.reverse_cons, List.append_assoc]

theorem tape_normalizedOutput_move
    (dir : Direction) (T : Tape MachineCodeSymbol) :
    Tape.normalizedOutput (Tape.move dir T) =
      Tape.normalizedOutput T := by
  cases dir with
  | left =>
      exact tape_normalizedOutput_move_left T
  | right =>
      exact tape_normalizedOutput_move_right T

theorem tape_normalizedOutput_move_write_read
    (dir : Direction) (T : Tape MachineCodeSymbol) :
    Tape.normalizedOutput
        (Tape.move dir (Tape.write (Tape.read T) T)) =
      Tape.normalizedOutput T := by
  cases T with
  | mk left head right =>
      exact
        tape_normalizedOutput_move dir
          { left := left, head := head, right := right }

inductive CodePrefixParserNormalizerState where
  | needHeader : CodePrefixParserNormalizerState
  | stateCount : CodePrefixParserNormalizerState
  | startField : CodePrefixParserNormalizerState
  | haltField : CodePrefixParserNormalizerState
  | findCount :
      TransitionListParserMarker -> CodePrefixParserNormalizerState
  | seekCountDone :
      TransitionListParserMarker -> CodePrefixParserNormalizerState
  | seekMarker :
      Option MachineCodeSymbol -> CodePrefixParserNormalizerState
  | enterMarkedPosition : CodePrefixParserNormalizerState
  | needTransition : CodePrefixParserNormalizerState
  | sourceNat : CodePrefixParserNormalizerState
  | readCell : CodePrefixParserNormalizerState
  | writeCell : CodePrefixParserNormalizerState
  | moveField : CodePrefixParserNormalizerState
  | targetNat : CodePrefixParserNormalizerState
  | markPosition : CodePrefixParserNormalizerState
  | returnLeft :
      Option MachineCodeSymbol -> CodePrefixParserNormalizerState
  | restoreSeekMarker :
      Option MachineCodeSymbol -> CodePrefixParserNormalizerState
  | restoreReturnLeft : CodePrefixParserNormalizerState
  | restoreLeft : CodePrefixParserNormalizerState
  | restoreForward : CodePrefixParserNormalizerState
  | halt : CodePrefixParserNormalizerState

namespace CodePrefixParserNormalizerState

def elems : List CodePrefixParserNormalizerState :=
  [needHeader, stateCount, startField, haltField] ++
  (TransitionListParserState.markers.map
    CodePrefixParserNormalizerState.findCount) ++
  (TransitionListParserState.markers.map
    CodePrefixParserNormalizerState.seekCountDone) ++
  (TransitionListParserState.optionCells.map
    CodePrefixParserNormalizerState.seekMarker) ++
  [enterMarkedPosition,
    needTransition,
    sourceNat,
    readCell,
    writeCell,
    moveField,
    targetNat,
    markPosition] ++
  (TransitionListParserState.optionCells.map
    CodePrefixParserNormalizerState.returnLeft) ++
  (TransitionListParserState.optionCells.map
    CodePrefixParserNormalizerState.restoreSeekMarker) ++
  [restoreReturnLeft, restoreLeft, restoreForward, halt]

def finite : Foundation.FiniteType CodePrefixParserNormalizerState where
  elems := elems
  complete := by
    intro state
    cases state with
    | needHeader =>
        simp [elems]
    | stateCount =>
        simp [elems]
    | startField =>
        simp [elems]
    | haltField =>
        simp [elems]
    | findCount marker =>
        simp [elems, TransitionListParserState.markers_complete marker]
    | seekCountDone marker =>
        simp [elems, TransitionListParserState.markers_complete marker]
    | seekMarker cell =>
        simp [elems, TransitionListParserState.optionCells_complete cell]
    | enterMarkedPosition =>
        simp [elems]
    | needTransition =>
        simp [elems]
    | sourceNat =>
        simp [elems]
    | readCell =>
        simp [elems]
    | writeCell =>
        simp [elems]
    | moveField =>
        simp [elems]
    | targetNat =>
        simp [elems]
    | markPosition =>
        simp [elems]
    | returnLeft cell =>
        simp [elems, TransitionListParserState.optionCells_complete cell]
    | restoreSeekMarker cell =>
        simp [elems, TransitionListParserState.optionCells_complete cell]
    | restoreReturnLeft =>
        simp [elems]
    | restoreLeft =>
        simp [elems]
    | restoreForward =>
        simp [elems]
    | halt =>
        simp [elems]

end CodePrefixParserNormalizerState

def codePrefixParserNormalizerKeep
    (cell : Option MachineCodeSymbol)
    (dir : Direction)
    (next : CodePrefixParserNormalizerState) :
    Option (Option MachineCodeSymbol × Direction ×
      CodePrefixParserNormalizerState) :=
  some (cell, dir, next)

def codePrefixParserNormalizerMachine :
    TuringMachine MachineCodeSymbol CodePrefixParserNormalizerState where
  start := CodePrefixParserNormalizerState.needHeader
  halt := CodePrefixParserNormalizerState.halt
  transition := fun state cell =>
    match state, cell with
    | CodePrefixParserNormalizerState.needHeader,
        some MachineCodeSymbol.header =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.stateCount

    | CodePrefixParserNormalizerState.stateCount,
        some MachineCodeSymbol.tick =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.stateCount
    | CodePrefixParserNormalizerState.stateCount,
        some MachineCodeSymbol.done =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.startField

    | CodePrefixParserNormalizerState.startField,
        some MachineCodeSymbol.tick =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.startField
    | CodePrefixParserNormalizerState.startField,
        some MachineCodeSymbol.done =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.haltField

    | CodePrefixParserNormalizerState.haltField,
        some MachineCodeSymbol.tick =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.haltField
    | CodePrefixParserNormalizerState.haltField,
        some MachineCodeSymbol.done =>
        codePrefixParserNormalizerKeep cell Direction.right
          (CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial)

    | CodePrefixParserNormalizerState.findCount marker,
        some MachineCodeSymbol.blank =>
        codePrefixParserNormalizerKeep cell Direction.right
          (CodePrefixParserNormalizerState.findCount marker)
    | CodePrefixParserNormalizerState.findCount marker,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.blank, Direction.right,
            CodePrefixParserNormalizerState.seekCountDone marker)
    | CodePrefixParserNormalizerState.findCount
        TransitionListParserMarker.initial,
        some MachineCodeSymbol.done =>
        codePrefixParserNormalizerKeep cell Direction.left
          CodePrefixParserNormalizerState.restoreLeft
    | CodePrefixParserNormalizerState.findCount
        (TransitionListParserMarker.saved saved),
        some MachineCodeSymbol.done =>
        codePrefixParserNormalizerKeep cell Direction.right
          (CodePrefixParserNormalizerState.restoreSeekMarker saved)

    | CodePrefixParserNormalizerState.seekCountDone marker,
        some MachineCodeSymbol.done =>
        match marker with
        | TransitionListParserMarker.initial =>
            codePrefixParserNormalizerKeep cell Direction.right
              CodePrefixParserNormalizerState.needTransition
        | TransitionListParserMarker.saved saved =>
            codePrefixParserNormalizerKeep cell Direction.right
              (CodePrefixParserNormalizerState.seekMarker saved)
    | CodePrefixParserNormalizerState.seekCountDone marker, some _ =>
        codePrefixParserNormalizerKeep cell Direction.right
          (CodePrefixParserNormalizerState.seekCountDone marker)

    | CodePrefixParserNormalizerState.seekMarker saved,
        some MachineCodeSymbol.header =>
        some
          (saved, Direction.left,
            CodePrefixParserNormalizerState.enterMarkedPosition)
    | CodePrefixParserNormalizerState.seekMarker saved, some _ =>
        codePrefixParserNormalizerKeep cell Direction.right
          (CodePrefixParserNormalizerState.seekMarker saved)

    | CodePrefixParserNormalizerState.enterMarkedPosition, some _ =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.needTransition
    | CodePrefixParserNormalizerState.enterMarkedPosition, none =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.needTransition

    | CodePrefixParserNormalizerState.needTransition,
        some MachineCodeSymbol.transition =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.sourceNat
    | CodePrefixParserNormalizerState.sourceNat,
        some MachineCodeSymbol.tick =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.sourceNat
    | CodePrefixParserNormalizerState.sourceNat,
        some MachineCodeSymbol.done =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.readCell
    | CodePrefixParserNormalizerState.readCell,
        some MachineCodeSymbol.blank =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.writeCell
    | CodePrefixParserNormalizerState.readCell,
        some MachineCodeSymbol.zero =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.writeCell
    | CodePrefixParserNormalizerState.readCell,
        some MachineCodeSymbol.one =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.writeCell
    | CodePrefixParserNormalizerState.writeCell,
        some MachineCodeSymbol.blank =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.moveField
    | CodePrefixParserNormalizerState.writeCell,
        some MachineCodeSymbol.zero =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.moveField
    | CodePrefixParserNormalizerState.writeCell,
        some MachineCodeSymbol.one =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.moveField
    | CodePrefixParserNormalizerState.moveField,
        some MachineCodeSymbol.moveLeft =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.targetNat
    | CodePrefixParserNormalizerState.moveField,
        some MachineCodeSymbol.moveRight =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.targetNat
    | CodePrefixParserNormalizerState.targetNat,
        some MachineCodeSymbol.tick =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.targetNat
    | CodePrefixParserNormalizerState.targetNat,
        some MachineCodeSymbol.done =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.markPosition

    | CodePrefixParserNormalizerState.markPosition, cell =>
        some
          (some MachineCodeSymbol.header, Direction.left,
            CodePrefixParserNormalizerState.returnLeft cell)
    | CodePrefixParserNormalizerState.returnLeft saved, none =>
        codePrefixParserNormalizerKeep cell Direction.right
          (CodePrefixParserNormalizerState.findCount
            (TransitionListParserMarker.saved saved))
    | CodePrefixParserNormalizerState.returnLeft saved, some _ =>
        codePrefixParserNormalizerKeep cell Direction.left
          (CodePrefixParserNormalizerState.returnLeft saved)

    | CodePrefixParserNormalizerState.restoreSeekMarker saved,
        some MachineCodeSymbol.header =>
        some
          (saved, Direction.left,
            CodePrefixParserNormalizerState.restoreReturnLeft)
    | CodePrefixParserNormalizerState.restoreSeekMarker saved, some _ =>
        codePrefixParserNormalizerKeep cell Direction.right
          (CodePrefixParserNormalizerState.restoreSeekMarker saved)
    | CodePrefixParserNormalizerState.restoreReturnLeft, none =>
        codePrefixParserNormalizerKeep cell Direction.right
          (CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial)
    | CodePrefixParserNormalizerState.restoreReturnLeft, some _ =>
        codePrefixParserNormalizerKeep cell Direction.left
          CodePrefixParserNormalizerState.restoreReturnLeft

    | CodePrefixParserNormalizerState.restoreLeft,
        some MachineCodeSymbol.blank =>
        some
          (some MachineCodeSymbol.tick, Direction.left,
            CodePrefixParserNormalizerState.restoreLeft)
    | CodePrefixParserNormalizerState.restoreLeft, _ =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.restoreForward
    | CodePrefixParserNormalizerState.restoreForward,
        some MachineCodeSymbol.tick =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.restoreForward
    | CodePrefixParserNormalizerState.restoreForward,
        some MachineCodeSymbol.done =>
        codePrefixParserNormalizerKeep cell Direction.right
          CodePrefixParserNormalizerState.halt
    | _, _ => none
  statesFinite := CodePrefixParserNormalizerState.finite

def codePrefixParserNormalizerTape :=
  transitionListParserTape

theorem codePrefixParserNormalizerTape_nil_eq_input
    (tokens : Word MachineCodeSymbol) :
    codePrefixParserNormalizerTape [] tokens =
      Tape.input tokens :=
  transitionListParserTape_nil_eq_input tokens

theorem codePrefixParserNormalizer_step_header
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.needHeader
        tape :=
          codePrefixParserNormalizerTape leftRev
            (MachineCodeSymbol.header :: suffix) }
      { state := CodePrefixParserNormalizerState.stateCount
        tape :=
          codePrefixParserNormalizerTape
            (MachineCodeSymbol.header :: leftRev) suffix } := by
  unfold codePrefixParserNormalizerTape
  rw [← transitionListParserTape_move_right leftRev
    MachineCodeSymbol.header suffix]
  exact TuringMachine.Step.mk (by
    simp [codePrefixParserNormalizerMachine,
      transitionListParserTape, codePrefixParserNormalizerKeep, Tape.read])

theorem codePrefixParserNormalizer_step_tick_stateCount
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.stateCount
        tape :=
          codePrefixParserNormalizerTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := CodePrefixParserNormalizerState.stateCount
        tape :=
          codePrefixParserNormalizerTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  unfold codePrefixParserNormalizerTape
  rw [← transitionListParserTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [codePrefixParserNormalizerMachine,
      transitionListParserTape, codePrefixParserNormalizerKeep, Tape.read])

theorem codePrefixParserNormalizer_step_done_stateCount
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.stateCount
        tape :=
          codePrefixParserNormalizerTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.startField
        tape :=
          codePrefixParserNormalizerTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  unfold codePrefixParserNormalizerTape
  rw [← transitionListParserTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [codePrefixParserNormalizerMachine,
      transitionListParserTape, codePrefixParserNormalizerKeep, Tape.read])

theorem codePrefixParserNormalizer_step_tick_startField
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.startField
        tape :=
          codePrefixParserNormalizerTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := CodePrefixParserNormalizerState.startField
        tape :=
          codePrefixParserNormalizerTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  unfold codePrefixParserNormalizerTape
  rw [← transitionListParserTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [codePrefixParserNormalizerMachine,
      transitionListParserTape, codePrefixParserNormalizerKeep, Tape.read])

theorem codePrefixParserNormalizer_step_done_startField
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.startField
        tape :=
          codePrefixParserNormalizerTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.haltField
        tape :=
          codePrefixParserNormalizerTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  unfold codePrefixParserNormalizerTape
  rw [← transitionListParserTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [codePrefixParserNormalizerMachine,
      transitionListParserTape, codePrefixParserNormalizerKeep, Tape.read])

theorem codePrefixParserNormalizer_step_tick_haltField
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.haltField
        tape :=
          codePrefixParserNormalizerTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := CodePrefixParserNormalizerState.haltField
        tape :=
          codePrefixParserNormalizerTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  unfold codePrefixParserNormalizerTape
  rw [← transitionListParserTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [codePrefixParserNormalizerMachine,
      transitionListParserTape, codePrefixParserNormalizerKeep, Tape.read])

theorem codePrefixParserNormalizer_step_done_haltField
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.haltField
        tape :=
          codePrefixParserNormalizerTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial
        tape :=
          codePrefixParserNormalizerTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  unfold codePrefixParserNormalizerTape
  rw [← transitionListParserTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [codePrefixParserNormalizerMachine,
      transitionListParserTape, codePrefixParserNormalizerKeep, Tape.read])

theorem codePrefixParserNormalizer_computes_nat
    (current next : CodePrefixParserNormalizerState)
    (htick :
      forall leftRev suffix : Word MachineCodeSymbol,
        TuringMachine.Step codePrefixParserNormalizerMachine
          { state := current
            tape :=
              codePrefixParserNormalizerTape leftRev
                (MachineCodeSymbol.tick :: suffix) }
          { state := current
            tape :=
              codePrefixParserNormalizerTape
                (MachineCodeSymbol.tick :: leftRev) suffix })
    (hdone :
      forall leftRev suffix : Word MachineCodeSymbol,
        TuringMachine.Step codePrefixParserNormalizerMachine
          { state := current
            tape :=
              codePrefixParserNormalizerTape leftRev
                (MachineCodeSymbol.done :: suffix) }
          { state := next
            tape :=
              codePrefixParserNormalizerTape
                (MachineCodeSymbol.done :: leftRev) suffix })
    (leftRev : Word MachineCodeSymbol) (n : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.ComputesIn codePrefixParserNormalizerMachine
      (n + 1)
      { state := current
        tape :=
          codePrefixParserNormalizerTape leftRev
            (MachineDescription.encodeNatAppend n suffix) }
      { state := next
        tape :=
          codePrefixParserNormalizerTape
            (List.append (MachineDescription.encodeNat n).reverse leftRev)
            suffix } := by
  induction n generalizing leftRev with
  | zero =>
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat] using
        TuringMachine.ComputesIn.succ
          (hdone leftRev suffix)
          (TuringMachine.ComputesIn.zero _)
  | succ n ih =>
      have htail := ih (MachineCodeSymbol.tick :: leftRev)
      have hcomp :
          TuringMachine.ComputesIn
            codePrefixParserNormalizerMachine
            (n + 1 + 1)
            { state := current
              tape :=
                codePrefixParserNormalizerTape leftRev
                  (MachineCodeSymbol.tick ::
                    MachineDescription.encodeNatAppend n suffix) }
            { state := next
              tape :=
                codePrefixParserNormalizerTape
                  (List.append (MachineDescription.encodeNat n).reverse
                    (MachineCodeSymbol.tick :: leftRev))
                  suffix } :=
        TuringMachine.ComputesIn.succ
          (htick leftRev (MachineDescription.encodeNatAppend n suffix))
          htail
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, List.append_assoc] using hcomp

end Computability
end FoC
