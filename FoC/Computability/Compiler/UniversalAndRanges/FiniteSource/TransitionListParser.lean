import FoC.Computability.Compiler.UniversalAndRanges.HeaderParser

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

/-!
**Transition-list parser.**  The description-prefix parser has to validate a
unary transition count and then parse exactly that many transition records.  The
machine below uses the count itself as the work tape: each consumed count tick is
overwritten by {name}`MachineCodeSymbol.blank`.  After every parsed record it
marks the exact next parsing position with {name}`MachineCodeSymbol.header`,
returns to the count prefix, and consumes the next tick.  The saved marker cell
is carried in the finite control state.
-/

def TransitionListParserConstruction : Prop :=
  exists state : Type,
  exists parser : TuringMachine MachineCodeSymbol state,
    forall count : Nat,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput parser
          (MachineDescription.encodeNatAppend count tokens) <->
        exists transitions : List TransitionDescription,
        exists suffix : Word MachineCodeSymbol,
          MachineDescription.decodeTransitions count tokens =
            some (transitions, suffix)

inductive TransitionListParserMarker where
  | initial : TransitionListParserMarker
  | saved : Option MachineCodeSymbol -> TransitionListParserMarker

inductive TransitionListParserState where
  | findCount : TransitionListParserMarker -> TransitionListParserState
  | seekCountDone : TransitionListParserMarker -> TransitionListParserState
  | seekMarker : Option MachineCodeSymbol -> TransitionListParserState
  | enterMarkedPosition : TransitionListParserState
  | needTransition : TransitionListParserState
  | sourceNat : TransitionListParserState
  | readCell : TransitionListParserState
  | writeCell : TransitionListParserState
  | moveField : TransitionListParserState
  | targetNat : TransitionListParserState
  | markPosition : TransitionListParserState
  | returnLeft : Option MachineCodeSymbol -> TransitionListParserState
  | halt : TransitionListParserState

namespace TransitionListParserState

def optionCells : List (Option MachineCodeSymbol) :=
  [none,
    some MachineCodeSymbol.header,
    some MachineCodeSymbol.transition,
    some MachineCodeSymbol.tick,
    some MachineCodeSymbol.done,
    some MachineCodeSymbol.blank,
    some MachineCodeSymbol.zero,
    some MachineCodeSymbol.one,
    some MachineCodeSymbol.moveLeft,
    some MachineCodeSymbol.moveRight]

theorem optionCells_complete (cell : Option MachineCodeSymbol) :
    cell ∈ optionCells := by
  cases cell with
  | none =>
      simp [optionCells]
  | some symbol =>
      cases symbol <;> simp [optionCells]

def markers : List TransitionListParserMarker :=
  TransitionListParserMarker.initial ::
    optionCells.map TransitionListParserMarker.saved

theorem markers_complete (marker : TransitionListParserMarker) :
    marker ∈ markers := by
  cases marker with
  | initial =>
      simp [markers]
  | saved cell =>
      simp [markers, optionCells_complete cell]

def elems : List TransitionListParserState :=
  (markers.map TransitionListParserState.findCount) ++
  (markers.map TransitionListParserState.seekCountDone) ++
  (optionCells.map TransitionListParserState.seekMarker) ++
  [enterMarkedPosition,
    needTransition,
    sourceNat,
    readCell,
    writeCell,
    moveField,
    targetNat,
    markPosition] ++
  (optionCells.map TransitionListParserState.returnLeft) ++
  [halt]

def finite : Foundation.FiniteType TransitionListParserState where
  elems := elems
  complete := by
    intro state
    cases state with
    | findCount marker =>
        simp [elems, markers_complete marker]
    | seekCountDone marker =>
        simp [elems, markers_complete marker]
    | seekMarker cell =>
        simp [elems, optionCells_complete cell]
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
        simp [elems, optionCells_complete]
    | returnLeft cell =>
        simp [elems, optionCells_complete cell]
    | halt =>
        simp [elems]

end TransitionListParserState

def transitionListParserKeep
    (cell : Option MachineCodeSymbol)
    (dir : Direction)
    (next : TransitionListParserState) :
    Option (Option MachineCodeSymbol × Direction × TransitionListParserState) :=
  some (cell, dir, next)

def transitionListParserMachine :
    TuringMachine MachineCodeSymbol TransitionListParserState where
  start := TransitionListParserState.findCount
    TransitionListParserMarker.initial
  halt := TransitionListParserState.halt
  transition := fun state cell =>
    match state, cell with
    | TransitionListParserState.findCount marker,
        some MachineCodeSymbol.blank =>
        transitionListParserKeep cell Direction.right
          (TransitionListParserState.findCount marker)
    | TransitionListParserState.findCount marker,
        some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.blank, Direction.right,
            TransitionListParserState.seekCountDone marker)
    | TransitionListParserState.findCount _,
        some MachineCodeSymbol.done =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.halt

    | TransitionListParserState.seekCountDone marker,
        some MachineCodeSymbol.done =>
        match marker with
        | TransitionListParserMarker.initial =>
            transitionListParserKeep cell Direction.right
              TransitionListParserState.needTransition
        | TransitionListParserMarker.saved saved =>
            transitionListParserKeep cell Direction.right
              (TransitionListParserState.seekMarker saved)
    | TransitionListParserState.seekCountDone marker, some _ =>
        transitionListParserKeep cell Direction.right
          (TransitionListParserState.seekCountDone marker)

    | TransitionListParserState.seekMarker saved,
        some MachineCodeSymbol.header =>
        some
          (saved, Direction.left,
            TransitionListParserState.enterMarkedPosition)
    | TransitionListParserState.seekMarker saved, some _ =>
        transitionListParserKeep cell Direction.right
          (TransitionListParserState.seekMarker saved)

    | TransitionListParserState.enterMarkedPosition, some _ =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.needTransition
    | TransitionListParserState.enterMarkedPosition, none =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.needTransition

    | TransitionListParserState.needTransition,
        some MachineCodeSymbol.transition =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.sourceNat
    | TransitionListParserState.sourceNat,
        some MachineCodeSymbol.tick =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.sourceNat
    | TransitionListParserState.sourceNat,
        some MachineCodeSymbol.done =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.readCell
    | TransitionListParserState.readCell,
        some MachineCodeSymbol.blank =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.writeCell
    | TransitionListParserState.readCell,
        some MachineCodeSymbol.zero =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.writeCell
    | TransitionListParserState.readCell,
        some MachineCodeSymbol.one =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.writeCell
    | TransitionListParserState.writeCell,
        some MachineCodeSymbol.blank =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.moveField
    | TransitionListParserState.writeCell,
        some MachineCodeSymbol.zero =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.moveField
    | TransitionListParserState.writeCell,
        some MachineCodeSymbol.one =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.moveField
    | TransitionListParserState.moveField,
        some MachineCodeSymbol.moveLeft =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.targetNat
    | TransitionListParserState.moveField,
        some MachineCodeSymbol.moveRight =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.targetNat
    | TransitionListParserState.targetNat,
        some MachineCodeSymbol.tick =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.targetNat
    | TransitionListParserState.targetNat,
        some MachineCodeSymbol.done =>
        transitionListParserKeep cell Direction.right
          TransitionListParserState.markPosition

    | TransitionListParserState.markPosition, cell =>
        some
          (some MachineCodeSymbol.header, Direction.left,
            TransitionListParserState.returnLeft cell)
    | TransitionListParserState.returnLeft saved, none =>
        transitionListParserKeep cell Direction.right
          (TransitionListParserState.findCount
            (TransitionListParserMarker.saved saved))
    | TransitionListParserState.returnLeft saved, some _ =>
        transitionListParserKeep cell Direction.left
          (TransitionListParserState.returnLeft saved)
    | _, _ => none
  statesFinite := TransitionListParserState.finite

def transitionListParserTape
    (leftRev rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := leftRev.map some
        head := none
        right := [] }
  | symbol :: suffix =>
      { left := leftRev.map some
        head := some symbol
        right := suffix.map some }

theorem transitionListParserTape_move_right
    (leftRev : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write (some symbol)
          (transitionListParserTape leftRev
            (symbol :: suffix))) =
      transitionListParserTape
        (symbol :: leftRev) suffix := by
  cases suffix <;>
    simp [transitionListParserTape, Tape.move,
      Tape.moveRight, Tape.write]

theorem transitionListParserTape_nil_eq_input
    (tokens : Word MachineCodeSymbol) :
    transitionListParserTape [] tokens =
      Tape.input tokens := by
  cases tokens <;> rfl

def transitionListParserOptionTape
    (leftRev rest : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := leftRev
        head := none
        right := [] }
  | cell :: suffix =>
      { left := leftRev
        head := cell
        right := suffix }

theorem transitionListParserOptionTape_move_right
    (leftRev suffix : List (Option MachineCodeSymbol))
    (old write : Option MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write write
          (transitionListParserOptionTape leftRev
            (old :: suffix))) =
      transitionListParserOptionTape
        (write :: leftRev) suffix := by
  cases suffix <;>
    simp [transitionListParserOptionTape, Tape.move,
      Tape.moveRight, Tape.write]

theorem transitionListParserOptionTape_move_right_empty
    (leftRev : List (Option MachineCodeSymbol))
    (write : Option MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write write
          (transitionListParserOptionTape leftRev [])) =
      transitionListParserOptionTape
        (write :: leftRev) [] := by
  simp [transitionListParserOptionTape, Tape.move,
    Tape.moveRight, Tape.write]

theorem transitionListParserOptionTape_move_left
    (leftTail suffix : List (Option MachineCodeSymbol))
    (leftHead old write : Option MachineCodeSymbol) :
    Tape.move Direction.left
        (Tape.write write
          (transitionListParserOptionTape
            (leftHead :: leftTail) (old :: suffix))) =
      transitionListParserOptionTape leftTail
        (leftHead :: write :: suffix) := by
  cases suffix <;>
    simp [transitionListParserOptionTape, Tape.move,
      Tape.moveLeft, Tape.write]

theorem transitionListParserOptionTape_move_left_empty
    (leftTail : List (Option MachineCodeSymbol))
    (leftHead write : Option MachineCodeSymbol) :
    Tape.move Direction.left
        (Tape.write write
          (transitionListParserOptionTape
            (leftHead :: leftTail) [])) =
      transitionListParserOptionTape leftTail
        (leftHead :: write :: []) := by
  simp [transitionListParserOptionTape, Tape.move,
    Tape.moveLeft, Tape.write]

theorem transitionListParserOptionTape_move_left_boundary
    (suffix : List (Option MachineCodeSymbol))
    (old write : Option MachineCodeSymbol) :
    Tape.move Direction.left
        (Tape.write write
          (transitionListParserOptionTape [] (old :: suffix))) =
      transitionListParserOptionTape []
        (none :: write :: suffix) := by
  cases suffix <;>
    simp [transitionListParserOptionTape, Tape.move,
      Tape.moveLeft, Tape.write]

theorem transitionListParserOptionTape_move_left_boundary_empty
    (write : Option MachineCodeSymbol) :
    Tape.move Direction.left
        (Tape.write write
          (transitionListParserOptionTape [] [])) =
      transitionListParserOptionTape []
        (none :: write :: []) := by
  simp [transitionListParserOptionTape, Tape.move,
    Tape.moveLeft, Tape.write]

theorem transitionListParserOptionTape_nil_eq_input
    (tokens : Word MachineCodeSymbol) :
    transitionListParserOptionTape [] (tokens.map some) =
      Tape.input tokens := by
  cases tokens <;> rfl

theorem transitionListParserMachine_step_keep_right
    {state next : TransitionListParserState}
    {leftRev suffix : List (Option MachineCodeSymbol)}
    {cell : Option MachineCodeSymbol}
    (htransition :
      transitionListParserMachine.transition state cell =
        some (cell, Direction.right, next)) :
    TuringMachine.Step transitionListParserMachine
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

theorem transitionListParserMachine_step_write_right
    {state next : TransitionListParserState}
    {leftRev suffix : List (Option MachineCodeSymbol)}
    {cell write : Option MachineCodeSymbol}
    (htransition :
      transitionListParserMachine.transition state cell =
        some (write, Direction.right, next)) :
    TuringMachine.Step transitionListParserMachine
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

theorem transitionListParserMachine_step_keep_left_nonempty
    {state next : TransitionListParserState}
    {leftTail suffix : List (Option MachineCodeSymbol)}
    {leftHead cell : Option MachineCodeSymbol}
    (htransition :
      transitionListParserMachine.transition state cell =
        some (cell, Direction.left, next)) :
    TuringMachine.Step transitionListParserMachine
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

theorem transitionListParserMachine_step_keep_left_boundary
    {state next : TransitionListParserState}
    {suffix : List (Option MachineCodeSymbol)}
    {cell : Option MachineCodeSymbol}
    (htransition :
      transitionListParserMachine.transition state cell =
        some (cell, Direction.left, next)) :
    TuringMachine.Step transitionListParserMachine
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

theorem transitionListParserMachine_step_returnLeft_some_nonempty
    (saved : Option MachineCodeSymbol)
    (leftTail suffix : List (Option MachineCodeSymbol))
    (leftHead : Option MachineCodeSymbol)
    (symbol : MachineCodeSymbol) :
    TuringMachine.Step transitionListParserMachine
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail)
            (some symbol :: suffix) }
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: some symbol :: suffix) } := by
  exact transitionListParserMachine_step_keep_left_nonempty
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_returnLeft_some_boundary
    (saved : Option MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol))
    (symbol : MachineCodeSymbol) :
    TuringMachine.Step transitionListParserMachine
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape []
            (some symbol :: suffix) }
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape []
            (none :: some symbol :: suffix) } := by
  exact transitionListParserMachine_step_keep_left_boundary
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_returnLeft_none_boundary
    (saved : Option MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step transitionListParserMachine
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape []
            (none :: suffix) }
      { state :=
          TransitionListParserState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape [none] suffix } := by
  exact transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_findCount_done
    (marker : TransitionListParserMarker)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step transitionListParserMachine
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := TransitionListParserState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } := by
  exact transitionListParserMachine_step_keep_right
    (by
      cases marker <;>
        simp [transitionListParserMachine,
          transitionListParserKeep])

theorem transitionListParserMachine_step_findCount_blank
    (marker : TransitionListParserMarker)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step transitionListParserMachine
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.blank :: suffix) }
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.blank :: leftRev) suffix } := by
  exact transitionListParserMachine_step_keep_right
    (by
      cases marker <;>
        simp [transitionListParserMachine,
          transitionListParserKeep])

theorem transitionListParserMachine_step_findCount_tick
    (marker : TransitionListParserMarker)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step transitionListParserMachine
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state := TransitionListParserState.seekCountDone marker
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.blank :: leftRev) suffix } := by
  exact transitionListParserMachine_step_write_right
    (by
      cases marker <;>
        simp [transitionListParserMachine,
          transitionListParserKeep])

theorem transitionListParserMachine_step_sourceNat_tick
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step transitionListParserMachine
      { state := TransitionListParserState.sourceNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state := TransitionListParserState.sourceNat
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.tick :: leftRev) suffix } := by
  exact transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_sourceNat_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step transitionListParserMachine
      { state := TransitionListParserState.sourceNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := TransitionListParserState.readCell
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } := by
  exact transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_targetNat_tick
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step transitionListParserMachine
      { state := TransitionListParserState.targetNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state := TransitionListParserState.targetNat
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.tick :: leftRev) suffix } := by
  exact transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_targetNat_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step transitionListParserMachine
      { state := TransitionListParserState.targetNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } := by
  exact transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_computes_nat
    {current next : TransitionListParserState}
    (htick :
      forall leftRev suffix : List (Option MachineCodeSymbol),
        TuringMachine.Step transitionListParserMachine
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
        TuringMachine.Step transitionListParserMachine
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
    TuringMachine.Computes transitionListParserMachine
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
          TuringMachine.Computes transitionListParserMachine
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

theorem transitionListParserMachine_computes_needTransition
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineCodeSymbol.transition :: suffix).map some) }
      { state := TransitionListParserState.sourceNat
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.transition :: leftRev)
            (suffix.map some) } :=
  TuringMachine.computes_of_step
    (transitionListParserMachine_step_keep_right
      (by simp [transitionListParserMachine,
        transitionListParserKeep]))

theorem transitionListParserMachine_computes_readCell
    (cell : Option Bool)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.readCell
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeCellAppend cell suffix).map some) }
      { state := TransitionListParserState.writeCell
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
          (transitionListParserMachine_step_keep_right
            (by simp [transitionListParserMachine,
              transitionListParserKeep]))
  | some b =>
      cases b <;>
        simpa [MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell] using
          TuringMachine.computes_of_step
            (transitionListParserMachine_step_keep_right
              (by simp [transitionListParserMachine,
                transitionListParserKeep]))

theorem transitionListParserMachine_computes_writeCell
    (cell : Option Bool)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.writeCell
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeCellAppend cell suffix).map some) }
      { state := TransitionListParserState.moveField
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
          (transitionListParserMachine_step_keep_right
            (by simp [transitionListParserMachine,
              transitionListParserKeep]))
  | some b =>
      cases b <;>
        simpa [MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell] using
          TuringMachine.computes_of_step
            (transitionListParserMachine_step_keep_right
              (by simp [transitionListParserMachine,
                transitionListParserKeep]))

theorem transitionListParserMachine_computes_moveField
    (dir : Direction)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.moveField
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeDirectionAppend dir suffix).map some) }
      { state := TransitionListParserState.targetNat
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
        (transitionListParserMachine_step_keep_right
          (by simp [transitionListParserMachine,
            transitionListParserKeep]))

theorem transitionListParserMachine_computes_transition
    (t : TransitionDescription)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeTransitionAppend t suffix).map some) }
      { state := TransitionListParserState.markPosition
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
    transitionListParserMachine_computes_needTransition
      leftRev
      (MachineDescription.encodeNatAppend t.source
        (MachineDescription.encodeCellAppend t.read
          (MachineDescription.encodeCellAppend t.write
            (MachineDescription.encodeDirectionAppend t.move
              (MachineDescription.encodeNatAppend t.target suffix)))))
  have hsource :
      TuringMachine.Computes transitionListParserMachine
        { state := TransitionListParserState.sourceNat
          tape :=
            transitionListParserOptionTape afterTransition
              ((MachineDescription.encodeNatAppend t.source
                (MachineDescription.encodeCellAppend t.read
                  (MachineDescription.encodeCellAppend t.write
                    (MachineDescription.encodeDirectionAppend t.move
                      (MachineDescription.encodeNatAppend t.target
                        suffix))))).map some) }
        { state := TransitionListParserState.readCell
          tape :=
            transitionListParserOptionTape afterSource
              ((MachineDescription.encodeCellAppend t.read
                (MachineDescription.encodeCellAppend t.write
                  (MachineDescription.encodeDirectionAppend t.move
                    (MachineDescription.encodeNatAppend t.target
                      suffix)))).map some) } := by
    simpa [afterSource] using
      transitionListParserMachine_computes_nat
        transitionListParserMachine_step_sourceNat_tick
        transitionListParserMachine_step_sourceNat_done
        afterTransition t.source
        (MachineDescription.encodeCellAppend t.read
          (MachineDescription.encodeCellAppend t.write
            (MachineDescription.encodeDirectionAppend t.move
              (MachineDescription.encodeNatAppend t.target suffix))))
  have hread :
      TuringMachine.Computes transitionListParserMachine
        { state := TransitionListParserState.readCell
          tape :=
            transitionListParserOptionTape afterSource
              ((MachineDescription.encodeCellAppend t.read
                (MachineDescription.encodeCellAppend t.write
                  (MachineDescription.encodeDirectionAppend t.move
                    (MachineDescription.encodeNatAppend t.target
                      suffix)))).map some) }
        { state := TransitionListParserState.writeCell
          tape :=
            transitionListParserOptionTape afterRead
              ((MachineDescription.encodeCellAppend t.write
                (MachineDescription.encodeDirectionAppend t.move
                  (MachineDescription.encodeNatAppend t.target
                    suffix))).map some) } := by
    simpa [afterRead] using
      transitionListParserMachine_computes_readCell
        t.read afterSource
        (MachineDescription.encodeCellAppend t.write
          (MachineDescription.encodeDirectionAppend t.move
            (MachineDescription.encodeNatAppend t.target suffix)))
  have hwrite :
      TuringMachine.Computes transitionListParserMachine
        { state := TransitionListParserState.writeCell
          tape :=
            transitionListParserOptionTape afterRead
              ((MachineDescription.encodeCellAppend t.write
                (MachineDescription.encodeDirectionAppend t.move
                  (MachineDescription.encodeNatAppend t.target
                    suffix))).map some) }
        { state := TransitionListParserState.moveField
          tape :=
            transitionListParserOptionTape afterWrite
              ((MachineDescription.encodeDirectionAppend t.move
                (MachineDescription.encodeNatAppend t.target
                  suffix)).map some) } := by
    simpa [afterWrite] using
      transitionListParserMachine_computes_writeCell
        t.write afterRead
        (MachineDescription.encodeDirectionAppend t.move
          (MachineDescription.encodeNatAppend t.target suffix))
  have hmove :
      TuringMachine.Computes transitionListParserMachine
        { state := TransitionListParserState.moveField
          tape :=
            transitionListParserOptionTape afterWrite
              ((MachineDescription.encodeDirectionAppend t.move
                (MachineDescription.encodeNatAppend t.target
                  suffix)).map some) }
        { state := TransitionListParserState.targetNat
          tape :=
            transitionListParserOptionTape afterMove
              ((MachineDescription.encodeNatAppend t.target
                suffix).map some) } := by
    simpa [afterMove] using
      transitionListParserMachine_computes_moveField
        t.move afterWrite
        (MachineDescription.encodeNatAppend t.target suffix)
  have htarget :
      TuringMachine.Computes transitionListParserMachine
        { state := TransitionListParserState.targetNat
          tape :=
            transitionListParserOptionTape afterMove
              ((MachineDescription.encodeNatAppend t.target
                suffix).map some) }
        { state := TransitionListParserState.markPosition
          tape :=
            transitionListParserOptionTape
              (List.append
                ((MachineDescription.encodeNat t.target).reverse.map some)
                afterMove)
              (suffix.map some) } := by
    exact
      transitionListParserMachine_computes_nat
        transitionListParserMachine_step_targetNat_tick
        transitionListParserMachine_step_targetNat_done
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

theorem transitionListParserMachine_returnLeft_noBoundary
    (saved : Option MachineCodeSymbol)
    (leftSymbols : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape
            (leftSymbols.map some)
            (some current :: suffix) }
      { state :=
          TransitionListParserState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape [none]
            (List.append (leftSymbols.reverse.map some)
              (some current :: suffix)) } := by
  induction leftSymbols generalizing current suffix with
  | nil =>
      exact
        TuringMachine.Computes.step
          (transitionListParserMachine_step_returnLeft_some_boundary
            saved suffix current)
          (by
            simpa using
              TuringMachine.Computes.step
                (transitionListParserMachine_step_returnLeft_none_boundary
                  saved (some current :: suffix))
                (TuringMachine.Computes.refl _))
  | cons leftHead leftTail ih =>
      have htail :=
        ih leftHead (some current :: suffix)
      exact
        TuringMachine.Computes.step
          (transitionListParserMachine_step_returnLeft_some_nonempty
            saved (leftTail.map some) suffix
            (some leftHead) current)
          (by
            simpa [List.append_assoc] using htail)

theorem transitionListParserMachine_returnLeft_withBoundary
    (saved : Option MachineCodeSymbol)
    (leftSymbols : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some) [none])
            (some current :: suffix) }
      { state :=
          TransitionListParserState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape [none]
            (List.append (leftSymbols.reverse.map some)
              (some current :: suffix)) } := by
  induction leftSymbols generalizing current suffix with
  | nil =>
      exact
        TuringMachine.Computes.step
          (transitionListParserMachine_step_returnLeft_some_nonempty
            saved [] suffix none current)
          (by
            simpa using
              TuringMachine.Computes.step
                (transitionListParserMachine_step_returnLeft_none_boundary
                  saved (some current :: suffix))
                (TuringMachine.Computes.refl _))
  | cons leftHead leftTail ih =>
      have htail :=
        ih leftHead (some current :: suffix)
      exact
        TuringMachine.Computes.step
          (transitionListParserMachine_step_returnLeft_some_nonempty
            saved
            (List.append (leftTail.map some) [none])
            suffix (some leftHead) current)
          (by
            simpa [List.append_assoc] using htail)

theorem transitionListParserMachine_halts_count_zero
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput transitionListParserMachine
      (MachineDescription.encodeNatAppend 0 tokens) := by
  have hstep :
      TuringMachine.Step transitionListParserMachine
        { state := TransitionListParserState.findCount
            TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape []
              ((MachineDescription.encodeNatAppend 0 tokens).map some) }
        { state := TransitionListParserState.halt
          tape :=
            transitionListParserOptionTape
              [some MachineCodeSymbol.done]
              (tokens.map some) } := by
    simpa [MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat] using
      transitionListParserMachine_step_findCount_done
        TransitionListParserMarker.initial [] (tokens.map some)
  have hcomp :
      TuringMachine.Computes transitionListParserMachine
        { state := TransitionListParserState.findCount
            TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape []
              ((MachineDescription.encodeNatAppend 0 tokens).map some) }
        { state := TransitionListParserState.halt
          tape :=
            transitionListParserOptionTape
              [some MachineCodeSymbol.done]
              (tokens.map some) } :=
    TuringMachine.Computes.step hstep
      (TuringMachine.Computes.refl _)
  have hhalts :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.findCount
            TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape []
              ((MachineDescription.encodeNatAppend 0 tokens).map some) } :=
    TuringMachine.halts_from_of_computes hcomp rfl
  simpa [TuringMachine.HaltsOnInput, TuringMachine.initial,
    transitionListParserMachine,
    transitionListParserOptionTape_nil_eq_input] using hhalts

theorem transitionListParserMachine_count_zero_spec
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput transitionListParserMachine
        (MachineDescription.encodeNatAppend 0 tokens) ∧
      (exists transitions : List TransitionDescription,
       exists suffix : Word MachineCodeSymbol,
        MachineDescription.decodeTransitions 0 tokens =
          some (transitions, suffix)) := by
  exact
    ⟨transitionListParserMachine_halts_count_zero tokens,
      ⟨[], tokens, rfl⟩⟩

end Computability
end FoC
