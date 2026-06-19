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
        some
          (none, Direction.right,
          (CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial))

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

    | CodePrefixParserNormalizerState.restoreLeft, none =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            CodePrefixParserNormalizerState.restoreForward)
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
          transitionListParserOptionTape
            (none :: leftRev.map some) (suffix.map some) } := by
  rw [← show
      Tape.move Direction.right
          (Tape.write none
            (codePrefixParserNormalizerTape leftRev
              (MachineCodeSymbol.done :: suffix))) =
        transitionListParserOptionTape
          (none :: leftRev.map some) (suffix.map some) by
    cases suffix <;>
      simp [codePrefixParserNormalizerTape,
        transitionListParserTape, Tape.move,
        Tape.moveRight, Tape.write,
        transitionListParserOptionTape]]
  exact TuringMachine.Step.mk (by
    simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerTape, transitionListParserTape,
      Tape.read])

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

theorem codePrefixParserNormalizer_computes_nat'
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
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := current
        tape :=
          codePrefixParserNormalizerTape leftRev
            (MachineDescription.encodeNatAppend n suffix) }
      { state := next
        tape :=
          codePrefixParserNormalizerTape
            (List.append (MachineDescription.encodeNat n).reverse leftRev)
            suffix } :=
  TuringMachine.computesIn_to_computes
    (codePrefixParserNormalizer_computes_nat
      current next htick hdone leftRev n suffix)

def codePrefixParserNormalizerMarkedNatReverse :
    Nat -> List (Option MachineCodeSymbol)
  | 0 => [none]
  | n + 1 =>
      List.append
        (codePrefixParserNormalizerMarkedNatReverse n)
        [some MachineCodeSymbol.tick]

theorem codePrefixParserNormalizerMachine_computes_haltField_marked
    (leftRev : Word MachineCodeSymbol) (n : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.haltField
        tape :=
          codePrefixParserNormalizerTape leftRev
            (MachineDescription.encodeNatAppend n suffix) }
      { state :=
          CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape
            (List.append
              (codePrefixParserNormalizerMarkedNatReverse n)
              (leftRev.map some))
            (suffix.map some) } := by
  induction n generalizing leftRev with
  | zero =>
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        codePrefixParserNormalizerMarkedNatReverse] using
        TuringMachine.computes_of_step
          (codePrefixParserNormalizer_step_done_haltField
            leftRev suffix)
  | succ n ih =>
      have htail := ih (MachineCodeSymbol.tick :: leftRev)
      have hcomp :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.haltField
              tape :=
                codePrefixParserNormalizerTape leftRev
                  (MachineCodeSymbol.tick ::
                    MachineDescription.encodeNatAppend n suffix) }
            { state :=
                CodePrefixParserNormalizerState.findCount
                  TransitionListParserMarker.initial
              tape :=
                transitionListParserOptionTape
                  (List.append
                    (codePrefixParserNormalizerMarkedNatReverse n)
                    ((MachineCodeSymbol.tick :: leftRev).map some))
                  (suffix.map some) } :=
        TuringMachine.Computes.step
          (codePrefixParserNormalizer_step_tick_haltField
            leftRev (MachineDescription.encodeNatAppend n suffix))
          htail
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        codePrefixParserNormalizerMarkedNatReverse,
        List.append_assoc] using hcomp

def codePrefixParserNormalizerMarkedHeaderLeft
    (D : MachineDescription) : List (Option MachineCodeSymbol) :=
  List.append
    (codePrefixParserNormalizerMarkedNatReverse D.halt)
    (List.append
      ((MachineDescription.encodeNat D.start).reverse.map some)
      (List.append
        ((MachineDescription.encodeNat D.stateCount).reverse.map some)
        [some MachineCodeSymbol.header]))

theorem codePrefixParserNormalizerMachine_computes_headerFields_marked
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.needHeader
        tape :=
          codePrefixParserNormalizerTape []
            (MachineDescription.encodeDescriptionAppend D input) }
      { state :=
          CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedHeaderLeft D)
            ((MachineDescription.encodeNatAppend D.transitions.length
              (MachineDescription.encodeTransitionsAppend
                D.transitions input)).map some) } := by
  cases D with
  | mk stateCount start halt transitions =>
      let afterHeader : Word MachineCodeSymbol :=
        [MachineCodeSymbol.header]
      let afterState : Word MachineCodeSymbol :=
        List.append (MachineDescription.encodeNat stateCount).reverse
          afterHeader
      let afterStart : Word MachineCodeSymbol :=
        List.append (MachineDescription.encodeNat start).reverse
          afterState
      have hheader :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.needHeader
              tape :=
                codePrefixParserNormalizerTape []
                  (MachineCodeSymbol.header ::
                    MachineDescription.encodeNatAppend stateCount
                      (MachineDescription.encodeNatAppend start
                        (MachineDescription.encodeNatAppend halt
                          (MachineDescription.encodeNatAppend
                            transitions.length
                            (MachineDescription.encodeTransitionsAppend
                              transitions input))))) }
            { state := CodePrefixParserNormalizerState.stateCount
              tape :=
                codePrefixParserNormalizerTape afterHeader
                  (MachineDescription.encodeNatAppend stateCount
                    (MachineDescription.encodeNatAppend start
                      (MachineDescription.encodeNatAppend halt
                        (MachineDescription.encodeNatAppend
                          transitions.length
                          (MachineDescription.encodeTransitionsAppend
                            transitions input))))) } :=
        TuringMachine.computes_of_step
          (by
            simpa [afterHeader] using
              codePrefixParserNormalizer_step_header []
                (MachineDescription.encodeNatAppend stateCount
                  (MachineDescription.encodeNatAppend start
                    (MachineDescription.encodeNatAppend halt
                      (MachineDescription.encodeNatAppend
                        transitions.length
                        (MachineDescription.encodeTransitionsAppend
                          transitions input)))))
          )
      have hstate :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.stateCount
              tape :=
                codePrefixParserNormalizerTape afterHeader
                  (MachineDescription.encodeNatAppend stateCount
                    (MachineDescription.encodeNatAppend start
                      (MachineDescription.encodeNatAppend halt
                        (MachineDescription.encodeNatAppend
                          transitions.length
                          (MachineDescription.encodeTransitionsAppend
                            transitions input))))) }
            { state := CodePrefixParserNormalizerState.startField
              tape :=
                codePrefixParserNormalizerTape afterState
                  (MachineDescription.encodeNatAppend start
                    (MachineDescription.encodeNatAppend halt
                      (MachineDescription.encodeNatAppend
                        transitions.length
                        (MachineDescription.encodeTransitionsAppend
                          transitions input)))) } := by
        simpa [afterState] using
          codePrefixParserNormalizer_computes_nat'
            CodePrefixParserNormalizerState.stateCount
            CodePrefixParserNormalizerState.startField
            codePrefixParserNormalizer_step_tick_stateCount
            codePrefixParserNormalizer_step_done_stateCount
            afterHeader stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt
                (MachineDescription.encodeNatAppend transitions.length
                  (MachineDescription.encodeTransitionsAppend
                    transitions input))))
      have hstart :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.startField
              tape :=
                codePrefixParserNormalizerTape afterState
                  (MachineDescription.encodeNatAppend start
                    (MachineDescription.encodeNatAppend halt
                      (MachineDescription.encodeNatAppend
                        transitions.length
                        (MachineDescription.encodeTransitionsAppend
                          transitions input)))) }
            { state := CodePrefixParserNormalizerState.haltField
              tape :=
                codePrefixParserNormalizerTape afterStart
                  (MachineDescription.encodeNatAppend halt
                    (MachineDescription.encodeNatAppend
                      transitions.length
                      (MachineDescription.encodeTransitionsAppend
                        transitions input))) } := by
        simpa [afterStart] using
          codePrefixParserNormalizer_computes_nat'
            CodePrefixParserNormalizerState.startField
            CodePrefixParserNormalizerState.haltField
            codePrefixParserNormalizer_step_tick_startField
            codePrefixParserNormalizer_step_done_startField
            afterState start
            (MachineDescription.encodeNatAppend halt
              (MachineDescription.encodeNatAppend transitions.length
                (MachineDescription.encodeTransitionsAppend
                  transitions input)))
      have hhalt :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.haltField
              tape :=
                codePrefixParserNormalizerTape afterStart
                  (MachineDescription.encodeNatAppend halt
                    (MachineDescription.encodeNatAppend
                      transitions.length
                      (MachineDescription.encodeTransitionsAppend
                        transitions input))) }
            { state :=
                CodePrefixParserNormalizerState.findCount
                  TransitionListParserMarker.initial
              tape :=
                transitionListParserOptionTape
                  (codePrefixParserNormalizerMarkedHeaderLeft
                    { stateCount := stateCount
                      start := start
                      halt := halt
                      transitions := transitions })
                  ((MachineDescription.encodeNatAppend transitions.length
                    (MachineDescription.encodeTransitionsAppend
                      transitions input)).map some) } := by
        simpa [afterStart, afterState, afterHeader,
          codePrefixParserNormalizerMarkedHeaderLeft,
          List.map_append, List.append_assoc] using
          codePrefixParserNormalizerMachine_computes_haltField_marked
            afterStart halt
            (MachineDescription.encodeNatAppend transitions.length
              (MachineDescription.encodeTransitionsAppend
                transitions input))
      exact
        TuringMachine.computes_trans hheader
          (TuringMachine.computes_trans hstate
            (TuringMachine.computes_trans hstart
              (by
                simpa [MachineDescription.encodeDescriptionAppend,
                  afterHeader, afterState, afterStart,
                  codePrefixParserNormalizerMarkedHeaderLeft,
                  List.map_append, List.append_assoc] using hhalt)))

theorem codePrefixParserNormalizerMachine_step_keep_right
    {state next : CodePrefixParserNormalizerState}
    {leftRev suffix : List (Option MachineCodeSymbol)}
    {cell : Option MachineCodeSymbol}
    (htransition :
      codePrefixParserNormalizerMachine.transition state cell =
        some (cell, Direction.right, next)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := state
        tape :=
          transitionListParserOptionTape leftRev
            (cell :: suffix) }
      { state := next
        tape :=
          transitionListParserOptionTape
            (cell :: leftRev) suffix } := by
  rw [← transitionListParserOptionTape_move_right
    leftRev suffix cell cell]
  exact TuringMachine.Step.mk (by
    simpa [transitionListParserOptionTape, Tape.read] using htransition)

theorem codePrefixParserNormalizerMachine_step_write_right
    {state next : CodePrefixParserNormalizerState}
    {leftRev suffix : List (Option MachineCodeSymbol)}
    {cell write : Option MachineCodeSymbol}
    (htransition :
      codePrefixParserNormalizerMachine.transition state cell =
        some (write, Direction.right, next)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := state
        tape :=
          transitionListParserOptionTape leftRev
            (cell :: suffix) }
      { state := next
        tape :=
          transitionListParserOptionTape
            (write :: leftRev) suffix } := by
  rw [← transitionListParserOptionTape_move_right
    leftRev suffix cell write]
  exact TuringMachine.Step.mk (by
    simpa [transitionListParserOptionTape, Tape.read] using htransition)

theorem codePrefixParserNormalizerMachine_step_keep_left_nonempty
    {state next : CodePrefixParserNormalizerState}
    {leftTail suffix : List (Option MachineCodeSymbol)}
    {leftHead cell : Option MachineCodeSymbol}
    (htransition :
      codePrefixParserNormalizerMachine.transition state cell =
        some (cell, Direction.left, next)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := state
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail) (cell :: suffix) }
      { state := next
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: cell :: suffix) } := by
  rw [← transitionListParserOptionTape_move_left
    leftTail suffix leftHead cell cell]
  exact TuringMachine.Step.mk (by
    simpa [transitionListParserOptionTape, Tape.read] using htransition)

theorem codePrefixParserNormalizerMachine_step_keep_left_boundary
    {state next : CodePrefixParserNormalizerState}
    {suffix : List (Option MachineCodeSymbol)}
    {cell : Option MachineCodeSymbol}
    (htransition :
      codePrefixParserNormalizerMachine.transition state cell =
        some (cell, Direction.left, next)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := state
        tape :=
          transitionListParserOptionTape [] (cell :: suffix) }
      { state := next
        tape :=
          transitionListParserOptionTape []
            (none :: cell :: suffix) } := by
  rw [← transitionListParserOptionTape_move_left_boundary
    suffix cell cell]
  exact TuringMachine.Step.mk (by
    simpa [transitionListParserOptionTape, Tape.read] using htransition)

theorem codePrefixParserNormalizerMachine_step_write_left_nonempty
    {state next : CodePrefixParserNormalizerState}
    {leftTail suffix : List (Option MachineCodeSymbol)}
    {leftHead cell write : Option MachineCodeSymbol}
    (htransition :
      codePrefixParserNormalizerMachine.transition state cell =
        some (write, Direction.left, next)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := state
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail) (cell :: suffix) }
      { state := next
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: write :: suffix) } := by
  rw [← transitionListParserOptionTape_move_left
    leftTail suffix leftHead cell write]
  exact TuringMachine.Step.mk (by
    simpa [transitionListParserOptionTape, Tape.read] using htransition)

theorem codePrefixParserNormalizerMachine_step_write_left_boundary
    {state next : CodePrefixParserNormalizerState}
    {suffix : List (Option MachineCodeSymbol)}
    {cell write : Option MachineCodeSymbol}
    (htransition :
      codePrefixParserNormalizerMachine.transition state cell =
        some (write, Direction.left, next)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := state
        tape :=
          transitionListParserOptionTape [] (cell :: suffix) }
      { state := next
        tape :=
          transitionListParserOptionTape []
            (none :: write :: suffix) } := by
  rw [← transitionListParserOptionTape_move_left_boundary
    suffix cell write]
  exact TuringMachine.Step.mk (by
    simpa [transitionListParserOptionTape, Tape.read] using htransition)

theorem codePrefixParserNormalizerMachine_step_write_left_empty
    {state next : CodePrefixParserNormalizerState}
    {leftRev : List (Option MachineCodeSymbol)}
    {write : Option MachineCodeSymbol}
    (htransition :
      codePrefixParserNormalizerMachine.transition state none =
        some (write, Direction.left, next)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := state
        tape := transitionListParserOptionTape leftRev [] }
      { state := next
        tape :=
          match leftRev with
          | [] => transitionListParserOptionTape [] [none, write]
          | leftHead :: leftTail =>
              transitionListParserOptionTape leftTail [leftHead, write] } := by
  cases leftRev with
  | nil =>
      simp
      rw [← transitionListParserOptionTape_move_left_boundary_empty write]
      exact TuringMachine.Step.mk (by
        simpa [transitionListParserOptionTape, Tape.read] using htransition)
  | cons leftHead leftTail =>
      simp
      rw [← transitionListParserOptionTape_move_left_empty
        leftTail leftHead write]
      exact TuringMachine.Step.mk (by
        simpa [transitionListParserOptionTape, Tape.read] using htransition)

theorem codePrefixParserNormalizerMachine_computes_nat_option
    {current next : CodePrefixParserNormalizerState}
    (htick :
      forall leftRev suffix : List (Option MachineCodeSymbol),
        TuringMachine.Step codePrefixParserNormalizerMachine
          { state := current
            tape :=
              transitionListParserOptionTape leftRev
                (some MachineCodeSymbol.tick :: suffix) }
          { state := current
            tape :=
              transitionListParserOptionTape
                (some MachineCodeSymbol.tick :: leftRev) suffix })
    (hdone :
      forall leftRev suffix : List (Option MachineCodeSymbol),
        TuringMachine.Step codePrefixParserNormalizerMachine
          { state := current
            tape :=
              transitionListParserOptionTape leftRev
                (some MachineCodeSymbol.done :: suffix) }
          { state := next
            tape :=
              transitionListParserOptionTape
                (some MachineCodeSymbol.done :: leftRev) suffix })
    (leftRev : List (Option MachineCodeSymbol)) (n : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := current
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeNatAppend n suffix).map some) }
      { state := next
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeNat n).reverse.map some)
              leftRev)
            (suffix.map some) } := by
  induction n generalizing leftRev with
  | zero =>
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat] using
        TuringMachine.Computes.step
          (hdone leftRev (suffix.map some))
          (TuringMachine.Computes.refl _)
  | succ n ih =>
      have htail := ih (some MachineCodeSymbol.tick :: leftRev)
      have hcomp :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := current
              tape :=
                transitionListParserOptionTape leftRev
                  (some MachineCodeSymbol.tick ::
                    (MachineDescription.encodeNatAppend n suffix).map some) }
            { state := next
              tape :=
                transitionListParserOptionTape
                  (List.append
                    ((MachineDescription.encodeNat n).reverse.map some)
                    (some MachineCodeSymbol.tick :: leftRev))
                  (suffix.map some) } :=
        TuringMachine.Computes.step
          (htick leftRev
            ((MachineDescription.encodeNatAppend n suffix).map some))
          htail
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, List.append_assoc] using hcomp

theorem codePrefixParserNormalizerMachine_computes_needTransition
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineCodeSymbol.transition :: suffix).map some) }
      { state := CodePrefixParserNormalizerState.sourceNat
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.transition :: leftRev)
            (suffix.map some) } :=
  TuringMachine.computes_of_step
    (codePrefixParserNormalizerMachine_step_keep_right
      (by simp [codePrefixParserNormalizerMachine,
        codePrefixParserNormalizerKeep]))

theorem codePrefixParserNormalizerMachine_step_sourceNat_tick
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.sourceNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state := CodePrefixParserNormalizerState.sourceNat
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.tick :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_sourceNat_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.sourceNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.readCell
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_computes_readCell
    (cell : Option Bool)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.readCell
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeCellAppend cell suffix).map some) }
      { state := CodePrefixParserNormalizerState.writeCell
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeCell cell).reverse.map some)
              leftRev)
            (suffix.map some) } := by
  cases cell with
  | none =>
      simpa [MachineDescription.encodeCellAppend,
        MachineDescription.encodeCell] using
        TuringMachine.computes_of_step
          (codePrefixParserNormalizerMachine_step_keep_right
            (by simp [codePrefixParserNormalizerMachine,
              codePrefixParserNormalizerKeep]))
  | some b =>
      cases b <;>
        simpa [MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell] using
          TuringMachine.computes_of_step
            (codePrefixParserNormalizerMachine_step_keep_right
              (by simp [codePrefixParserNormalizerMachine,
                codePrefixParserNormalizerKeep]))

theorem codePrefixParserNormalizerMachine_computes_writeCell
    (cell : Option Bool)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.writeCell
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeCellAppend cell suffix).map some) }
      { state := CodePrefixParserNormalizerState.moveField
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeCell cell).reverse.map some)
              leftRev)
            (suffix.map some) } := by
  cases cell with
  | none =>
      simpa [MachineDescription.encodeCellAppend,
        MachineDescription.encodeCell] using
        TuringMachine.computes_of_step
          (codePrefixParserNormalizerMachine_step_keep_right
            (by simp [codePrefixParserNormalizerMachine,
              codePrefixParserNormalizerKeep]))
  | some b =>
      cases b <;>
        simpa [MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell] using
          TuringMachine.computes_of_step
            (codePrefixParserNormalizerMachine_step_keep_right
              (by simp [codePrefixParserNormalizerMachine,
                codePrefixParserNormalizerKeep]))

theorem codePrefixParserNormalizerMachine_computes_moveField
    (dir : Direction)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.moveField
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeDirectionAppend dir suffix).map some) }
      { state := CodePrefixParserNormalizerState.targetNat
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeDirection dir).reverse.map some)
              leftRev)
            (suffix.map some) } := by
  cases dir <;>
    simpa [MachineDescription.encodeDirectionAppend,
      MachineDescription.encodeDirection] using
      TuringMachine.computes_of_step
        (codePrefixParserNormalizerMachine_step_keep_right
          (by simp [codePrefixParserNormalizerMachine,
            codePrefixParserNormalizerKeep]))

theorem codePrefixParserNormalizerMachine_step_targetNat_tick
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.targetNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state := CodePrefixParserNormalizerState.targetNat
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.tick :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_targetNat_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.targetNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_computes_transition
    (t : TransitionDescription)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeTransitionAppend t suffix).map some) }
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeNat t.target).reverse.map some)
              (List.append
                ((MachineDescription.encodeDirection t.move).reverse.map some)
                (List.append
                  ((MachineDescription.encodeCell t.write).reverse.map some)
                  (List.append
                    ((MachineDescription.encodeCell t.read).reverse.map some)
                    (List.append
                      ((MachineDescription.encodeNat t.source).reverse.map some)
                      (some MachineCodeSymbol.transition :: leftRev))))))
            (suffix.map some) } := by
  let afterTransition : List (Option MachineCodeSymbol) :=
    some MachineCodeSymbol.transition :: leftRev
  let afterSource : List (Option MachineCodeSymbol) :=
    List.append
      ((MachineDescription.encodeNat t.source).reverse.map some)
      afterTransition
  let afterRead : List (Option MachineCodeSymbol) :=
    List.append
      ((MachineDescription.encodeCell t.read).reverse.map some)
      afterSource
  let afterWrite : List (Option MachineCodeSymbol) :=
    List.append
      ((MachineDescription.encodeCell t.write).reverse.map some)
      afterRead
  let afterMove : List (Option MachineCodeSymbol) :=
    List.append
      ((MachineDescription.encodeDirection t.move).reverse.map some)
      afterWrite
  have htransition :=
    codePrefixParserNormalizerMachine_computes_needTransition
      leftRev
      (MachineDescription.encodeNatAppend t.source
        (MachineDescription.encodeCellAppend t.read
          (MachineDescription.encodeCellAppend t.write
            (MachineDescription.encodeDirectionAppend t.move
              (MachineDescription.encodeNatAppend t.target suffix)))))
  have hsource :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.sourceNat
          tape :=
            transitionListParserOptionTape afterTransition
              ((MachineDescription.encodeNatAppend t.source
                (MachineDescription.encodeCellAppend t.read
                  (MachineDescription.encodeCellAppend t.write
                    (MachineDescription.encodeDirectionAppend t.move
                      (MachineDescription.encodeNatAppend t.target
                        suffix))))).map some) }
        { state := CodePrefixParserNormalizerState.readCell
          tape :=
            transitionListParserOptionTape afterSource
              ((MachineDescription.encodeCellAppend t.read
                (MachineDescription.encodeCellAppend t.write
                  (MachineDescription.encodeDirectionAppend t.move
                    (MachineDescription.encodeNatAppend t.target
                      suffix)))).map some) } := by
    simpa [afterSource] using
      codePrefixParserNormalizerMachine_computes_nat_option
        codePrefixParserNormalizerMachine_step_sourceNat_tick
        codePrefixParserNormalizerMachine_step_sourceNat_done
        afterTransition t.source
        (MachineDescription.encodeCellAppend t.read
          (MachineDescription.encodeCellAppend t.write
            (MachineDescription.encodeDirectionAppend t.move
              (MachineDescription.encodeNatAppend t.target suffix))))
  have hread :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.readCell
          tape :=
            transitionListParserOptionTape afterSource
              ((MachineDescription.encodeCellAppend t.read
                (MachineDescription.encodeCellAppend t.write
                  (MachineDescription.encodeDirectionAppend t.move
                    (MachineDescription.encodeNatAppend t.target
                      suffix)))).map some) }
        { state := CodePrefixParserNormalizerState.writeCell
          tape :=
            transitionListParserOptionTape afterRead
              ((MachineDescription.encodeCellAppend t.write
                (MachineDescription.encodeDirectionAppend t.move
                  (MachineDescription.encodeNatAppend t.target
                    suffix))).map some) } := by
    simpa [afterRead] using
      codePrefixParserNormalizerMachine_computes_readCell
        t.read afterSource
        (MachineDescription.encodeCellAppend t.write
          (MachineDescription.encodeDirectionAppend t.move
            (MachineDescription.encodeNatAppend t.target suffix)))
  have hwrite :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.writeCell
          tape :=
            transitionListParserOptionTape afterRead
              ((MachineDescription.encodeCellAppend t.write
                (MachineDescription.encodeDirectionAppend t.move
                  (MachineDescription.encodeNatAppend t.target
                    suffix))).map some) }
        { state := CodePrefixParserNormalizerState.moveField
          tape :=
            transitionListParserOptionTape afterWrite
              ((MachineDescription.encodeDirectionAppend t.move
                (MachineDescription.encodeNatAppend t.target
                  suffix)).map some) } := by
    simpa [afterWrite] using
      codePrefixParserNormalizerMachine_computes_writeCell
        t.write afterRead
        (MachineDescription.encodeDirectionAppend t.move
          (MachineDescription.encodeNatAppend t.target suffix))
  have hmove :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.moveField
          tape :=
            transitionListParserOptionTape afterWrite
              ((MachineDescription.encodeDirectionAppend t.move
                (MachineDescription.encodeNatAppend t.target
                  suffix)).map some) }
        { state := CodePrefixParserNormalizerState.targetNat
          tape :=
            transitionListParserOptionTape afterMove
              ((MachineDescription.encodeNatAppend t.target
                suffix).map some) } := by
    simpa [afterMove] using
      codePrefixParserNormalizerMachine_computes_moveField
        t.move afterWrite
        (MachineDescription.encodeNatAppend t.target suffix)
  have htarget :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.targetNat
          tape :=
            transitionListParserOptionTape afterMove
              ((MachineDescription.encodeNatAppend t.target
                suffix).map some) }
        { state := CodePrefixParserNormalizerState.markPosition
          tape :=
            transitionListParserOptionTape
              (List.append
                ((MachineDescription.encodeNat t.target).reverse.map some)
                afterMove)
              (suffix.map some) } := by
    exact
      codePrefixParserNormalizerMachine_computes_nat_option
        codePrefixParserNormalizerMachine_step_targetNat_tick
        codePrefixParserNormalizerMachine_step_targetNat_done
        afterMove t.target suffix
  exact
    TuringMachine.computes_trans
      (by
        simpa [MachineDescription.encodeTransitionAppend] using
          htransition)
      (TuringMachine.computes_trans hsource
        (TuringMachine.computes_trans hread
          (TuringMachine.computes_trans hwrite
            (TuringMachine.computes_trans hmove
              (by
                simpa [afterMove, afterWrite, afterRead,
                  afterSource, afterTransition] using htarget)))))

theorem codePrefixParserNormalizerMachine_step_returnLeft_some_nonempty
    (saved : Option MachineCodeSymbol)
    (leftTail suffix : List (Option MachineCodeSymbol))
    (leftHead : Option MachineCodeSymbol)
    (symbol : MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.returnLeft saved
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail)
            (some symbol :: suffix) }
      { state := CodePrefixParserNormalizerState.returnLeft saved
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: some symbol :: suffix) } :=
  codePrefixParserNormalizerMachine_step_keep_left_nonempty
    (by cases symbol <;>
      simp [codePrefixParserNormalizerMachine,
        codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_returnLeft_none
    (saved : Option MachineCodeSymbol)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.returnLeft saved
        tape :=
          transitionListParserOptionTape leftRev
            (none :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape
            (none :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_returnLeft_toBoundary
    (saved : Option MachineCodeSymbol)
    (leftSymbols : Word MachineCodeSymbol)
    (prefixLeft suffix : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.returnLeft saved
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft))
            (some current :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape
            (none :: prefixLeft)
            (List.append (leftSymbols.reverse.map some)
              (some current :: suffix)) } := by
  induction leftSymbols generalizing current suffix with
  | nil =>
      exact
        TuringMachine.Computes.step
          (codePrefixParserNormalizerMachine_step_returnLeft_some_nonempty
            saved prefixLeft suffix none current)
          (by
            simpa using
              TuringMachine.Computes.step
                (codePrefixParserNormalizerMachine_step_returnLeft_none
                  saved prefixLeft (some current :: suffix))
                (TuringMachine.Computes.refl _))
  | cons leftHead leftTail ih =>
      have htail := ih (some current :: suffix) leftHead
      exact
        TuringMachine.Computes.step
          (codePrefixParserNormalizerMachine_step_returnLeft_some_nonempty
            saved
            (List.append (leftTail.map some) (none :: prefixLeft))
            suffix
            (some leftHead)
            current)
          (by
            simpa [List.append_assoc] using htail)

theorem codePrefixParserNormalizerMachine_step_restoreReturnLeft_some_nonempty
    (leftTail suffix : List (Option MachineCodeSymbol))
    (leftHead : Option MachineCodeSymbol)
    (symbol : MachineCodeSymbol) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreReturnLeft
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail)
            (some symbol :: suffix) }
      { state := CodePrefixParserNormalizerState.restoreReturnLeft
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: some symbol :: suffix) } :=
  codePrefixParserNormalizerMachine_step_keep_left_nonempty
    (by cases symbol <;>
      simp [codePrefixParserNormalizerMachine,
        codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_restoreReturnLeft_none
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreReturnLeft
        tape :=
          transitionListParserOptionTape leftRev
            (none :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape
            (none :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_restoreReturnLeft_toBoundary
    (leftSymbols : Word MachineCodeSymbol)
    (prefixLeft suffix : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreReturnLeft
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft))
            (some current :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape
            (none :: prefixLeft)
            (List.append (leftSymbols.reverse.map some)
              (some current :: suffix)) } := by
  induction leftSymbols generalizing current suffix with
  | nil =>
      exact
        TuringMachine.Computes.step
          (codePrefixParserNormalizerMachine_step_restoreReturnLeft_some_nonempty
            prefixLeft suffix none current)
          (by
            simpa using
              TuringMachine.Computes.step
                (codePrefixParserNormalizerMachine_step_restoreReturnLeft_none
                  prefixLeft (some current :: suffix))
                (TuringMachine.Computes.refl _))
  | cons leftHead leftTail ih =>
      have htail := ih (some current :: suffix) leftHead
      exact
        TuringMachine.Computes.step
          (codePrefixParserNormalizerMachine_step_restoreReturnLeft_some_nonempty
            (List.append (leftTail.map some) (none :: prefixLeft))
            suffix
            (some leftHead)
            current)
          (by
            simpa [List.append_assoc] using htail)

theorem codePrefixParserNormalizerMachine_haltsFromIn_needHeader_head
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.needHeader
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists suffix : Word MachineCodeSymbol,
      rest = MachineCodeSymbol.header :: suffix := by
  cases steps with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  exact ⟨suffix, rfl⟩
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | done =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_stateCount_nat
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.stateCount
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend n suffix := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_stateCount
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.stateCount
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨n, parsedSuffix, hsuffix⟩
                  exact
                    ⟨n + 1, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact
                    ⟨0, suffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_startField_nat
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.startField
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend n suffix := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_startField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.startField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨n, parsedSuffix, hsuffix⟩
                  exact
                    ⟨n + 1, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact
                    ⟨0, suffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_haltField_nat
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.haltField
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend n suffix := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_haltField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.haltField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨n, parsedSuffix, hsuffix⟩
                  exact
                    ⟨n + 1, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact
                    ⟨0, suffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_startField_fields
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.startField
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineDescription.encodeNatAppend start
          (MachineDescription.encodeNatAppend halt suffix) := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_startField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.startField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨start + 1, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_done_startField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.haltField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.done :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases
                    codePrefixParserNormalizerMachine_haltsFromIn_haltField_nat
                      htail with
                    ⟨halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨0, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_stateCount_fields
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.stateCount
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineDescription.encodeNatAppend stateCount
          (MachineDescription.encodeNatAppend start
            (MachineDescription.encodeNatAppend halt suffix)) := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_stateCount
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.stateCount
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨stateCount, start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨stateCount + 1, start, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_done_stateCount
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.startField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.done :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases
                    codePrefixParserNormalizerMachine_haltsFromIn_startField_fields
                      htail with
                    ⟨start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨0, start, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_needHeader_fields
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.needHeader
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt suffix)) := by
  cases steps with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_header
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.stateCount
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.header :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases
                    codePrefixParserNormalizerMachine_haltsFromIn_stateCount_fields
                      htail with
                    ⟨stateCount, start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨stateCount, start, halt, parsedSuffix,
                      by simp [hsuffix]⟩
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | done =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

/-!
**Normalizer code-spec frontier.**  The concrete
{name}`codePrefixParserNormalizerMachine` is the finite-state witness used by
the first universal-prefix scaffold.  Its remaining correctness proof is split
into soundness and completeness directions; the packaged spec below keeps
downstream construction code independent of that split.
-/

theorem codePrefixParserNormalizerMachine_haltsWithOutputIn_needHeader_fields
    {steps : Nat} {tokens out : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsWithOutputIn
        codePrefixParserNormalizerMachine steps tokens out) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt suffix)) := by
  have hhalts :
      TuringMachine.HaltsOnInputIn
        codePrefixParserNormalizerMachine steps tokens :=
    TuringMachine.halts_with_output_in_implies_halts_in h
  exact
    codePrefixParserNormalizerMachine_haltsFromIn_needHeader_fields
      (steps := steps) (leftRev := []) (rest := tokens)
      (by
        simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
          codePrefixParserNormalizerMachine,
          codePrefixParserNormalizerTape_nil_eq_input] using hhalts)

theorem codePrefixParserNormalizerMachine_haltsWithOutput_needHeader_fields
    {tokens out : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt suffix)) := by
  rcases
      TuringMachine.halts_with_output_to_halts_with_output_in h with
    ⟨steps, hsteps⟩
  exact
    codePrefixParserNormalizerMachine_haltsWithOutputIn_needHeader_fields
      hsteps

theorem decodeDescriptionPrefix_of_header_and_decodeTransitions
    {tokens rest : Word MachineCodeSymbol}
    {stateCount start halt transitionCount : Nat}
    {transitions : List TransitionDescription}
    {input : Word MachineCodeSymbol}
    (htokens :
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt
                (MachineDescription.encodeNatAppend transitionCount rest))))
    (htrans :
      MachineDescription.decodeTransitions transitionCount rest =
        some (transitions, input)) :
    MachineDescription.decodeDescriptionPrefix tokens =
      some
        (({ stateCount := stateCount
            start := start
            halt := halt
            transitions := transitions } : MachineDescription),
          input) := by
  subst tokens
  simp [MachineDescription.decodeDescriptionPrefix,
    MachineDescription.decodeNat_encodeNatAppend, htrans]

theorem codePrefixParserNormalizerMachine_haltsWithOutput_decodeTransitions
    {tokens out transitionBlock : Word MachineCodeSymbol}
    {stateCount start halt : Nat}
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out)
    (htokens :
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt transitionBlock))) :
    exists transitionCount : Nat,
    exists rest : Word MachineCodeSymbol,
    exists transitions : List TransitionDescription,
    exists input : Word MachineCodeSymbol,
      transitionBlock =
          MachineDescription.encodeNatAppend transitionCount rest ∧
        MachineDescription.decodeTransitions transitionCount rest =
          some (transitions, input) := by
  sorry

theorem codePrefixParserNormalizerMachine_haltsWithOutput_decodePrefix
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    exists D : MachineDescription,
    exists input : Word MachineCodeSymbol,
      MachineDescription.decodeDescriptionPrefix tokens =
        some (D, input) := by
  rcases
      codePrefixParserNormalizerMachine_haltsWithOutput_needHeader_fields
        h with
    ⟨stateCount, start, halt, transitionBlock, htokens⟩
  rcases
      codePrefixParserNormalizerMachine_haltsWithOutput_decodeTransitions
        h htokens with
    ⟨transitionCount, rest, transitions, input, hblock, htrans⟩
  refine
    ⟨{ stateCount := stateCount
       start := start
       halt := halt
       transitions := transitions }, input, ?_⟩
  exact
    decodeDescriptionPrefix_of_header_and_decodeTransitions
      (stateCount := stateCount) (start := start) (halt := halt)
      (transitionCount := transitionCount) (rest := rest)
      (transitions := transitions) (input := input)
      (by simpa [hblock] using htokens)
      htrans

theorem codePrefixParserNormalizerMachine_haltsWithOutput_output_eq_input
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    out = tokens := by
  sorry

theorem codePrefixParserNormalizerMachine_haltsWithOutput_only_decode
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    out = tokens ∧
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix tokens =
          some (D, input) := by
  exact
    ⟨codePrefixParserNormalizerMachine_haltsWithOutput_output_eq_input
        tokens out h,
      codePrefixParserNormalizerMachine_haltsWithOutput_decodePrefix
        tokens out h⟩

theorem codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescriptionAppend
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput
      codePrefixParserNormalizerMachine
      (MachineDescription.encodeDescriptionAppend D input)
      (MachineDescription.encodeDescriptionAppend D input) := by
  sorry

theorem codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescription_append
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput
      codePrefixParserNormalizerMachine
      (List.append (MachineDescription.encodeDescription D) input)
      (List.append (MachineDescription.encodeDescription D) input) := by
  rw [← MachineDescription.encodeDescriptionAppend_eq_encodeDescription_append
    D input]
  exact
    codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescriptionAppend
      D input

theorem codePrefixParserNormalizerMachine_code_sound
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    CodePrefixParserNormalizerCode.transform tokens = some out := by
  rcases
      codePrefixParserNormalizerMachine_haltsWithOutput_only_decode
        tokens out h with
    ⟨hout, D, input, hdecode⟩
  exact
    (codePrefixParserNormalizerCode_transform_eq_some_iff
      tokens out).mpr
      ⟨D, input, hdecode,
        by
          rw [hout]
          exact
            MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
              hdecode⟩

theorem codePrefixParserNormalizerMachine_code_complete
    (tokens out : Word MachineCodeSymbol)
    (h : CodePrefixParserNormalizerCode.transform tokens = some out) :
    TuringMachine.HaltsWithOutput
      codePrefixParserNormalizerMachine tokens out := by
  rcases
      (codePrefixParserNormalizerCode_transform_eq_some_iff
        tokens out).mp h with
    ⟨D, input, hdecode, hout⟩
  have htokens :
      tokens = List.append (MachineDescription.encodeDescription D) input :=
    MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
      hdecode
  rw [htokens, hout]
  exact
    codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescription_append
      D input

theorem codePrefixParserNormalizerMachine_code_spec :
    CodePrefixParserNormalizerCodeMachineSpec
      codePrefixParserNormalizerMachine := by
  intro tokens out
  constructor
  · exact codePrefixParserNormalizerMachine_code_sound tokens out
  · exact codePrefixParserNormalizerMachine_code_complete tokens out

end Computability
end FoC
