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
    cases state <;> simp [elems, markers_complete, optionCells_complete]

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

private abbrev TLPM := transitionListParserMachine

theorem transitionListParserMachine_haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled
      TLPM := by
  intro cell
  cases cell <;>
    simp [transitionListParserMachine]

theorem transitionListParserMachine_halts_from_of_computes_suffix
    {c d : TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState}
    (hprefix :
      TuringMachine.Computes TLPM c d)
    (hhalt :
      TuringMachine.HaltsFrom TLPM c) :
    TuringMachine.HaltsFrom TLPM d := by
  rcases hhalt with ⟨final, hfinalComp, hfinalHalt⟩
  induction hprefix generalizing final with
  | refl c =>
      exact ⟨final, hfinalComp, hfinalHalt⟩
  | step hstep hrest ih =>
      cases hfinalComp with
      | refl =>
          exact
            False.elim
              (TuringMachine.no_step_from_halted
                transitionListParserMachine_haltingTransitionsDisabled
                hfinalHalt hstep)
      | step hstep' hfinalTail =>
          have hnext :=
            TuringMachine.step_deterministic hstep hstep'
          cases hnext
          exact ih final hfinalTail hfinalHalt

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

theorem transitionListParserMachine_not_haltsFrom_of_stuck
    {c : TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState}
    (hnotHalt :
      ¬ TuringMachine.Halted TLPM c)
    (hnostep :
      forall d : TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState,
        ¬ TuringMachine.Step TLPM c d) :
    ¬ TuringMachine.HaltsFrom TLPM c := by
  intro h
  rcases h with ⟨final, hcomp, hhalt⟩
  cases hcomp with
  | refl =>
      exact hnotHalt hhalt
  | step hstep _ =>
      exact hnostep _ hstep

theorem transitionListParserMachine_not_haltsFrom_needTransition_empty
    (leftRev : List (Option MachineCodeSymbol)) :
    ¬ TuringMachine.HaltsFrom TLPM
      { state := TransitionListParserState.needTransition
        tape := transitionListParserOptionTape leftRev [] } := by
  refine
    transitionListParserMachine_not_haltsFrom_of_stuck
      ?_ ?_
  · simp [TuringMachine.Halted, transitionListParserMachine]
  · intro d hstep
    cases hstep with
    | mk htransition =>
        simp [transitionListParserMachine,
          transitionListParserOptionTape, Tape.read] at htransition

theorem transitionListParserMachine_not_haltsFrom_needTransition_nonTransition
    {symbol : MachineCodeSymbol}
    (hsymbol : symbol ≠ MachineCodeSymbol.transition)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : List (Option MachineCodeSymbol)) :
    ¬ TuringMachine.HaltsFrom TLPM
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape leftRev
            (some symbol :: suffix) } := by
  refine
    transitionListParserMachine_not_haltsFrom_of_stuck
      ?_ ?_
  · simp [TuringMachine.Halted, transitionListParserMachine]
  · intro d hstep
    cases hstep with
    | mk htransition =>
        cases symbol <;>
          simp [transitionListParserMachine,
          transitionListParserOptionTape, Tape.read] at hsymbol htransition

theorem transitionListParserMachine_not_haltsFrom_needTransition_none
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    ¬ TuringMachine.HaltsFrom TLPM
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape leftRev
            (none :: suffix) } := by
  refine
    transitionListParserMachine_not_haltsFrom_of_stuck
      ?_ ?_
  · simp [TuringMachine.Halted, transitionListParserMachine]
  · intro d hstep
    cases hstep with
    | mk htransition =>
        simp [transitionListParserMachine,
          transitionListParserOptionTape, Tape.read] at htransition

def transitionListParserNoHeader
    (symbols : List MachineCodeSymbol) : Prop :=
  forall symbol : MachineCodeSymbol,
    symbol ∈ symbols -> symbol ≠ MachineCodeSymbol.header

theorem transitionListParserNoHeader_append
    {left right : List MachineCodeSymbol}
    (hleft : transitionListParserNoHeader left)
    (hright : transitionListParserNoHeader right) :
    transitionListParserNoHeader (List.append left right) := by
  intro symbol hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft symbol hmem
  · exact hright symbol hmem

theorem transitionListParserNoHeader_cons
    {head : MachineCodeSymbol} {tail : List MachineCodeSymbol}
    (hhead : head ≠ MachineCodeSymbol.header)
    (htail : transitionListParserNoHeader tail) :
    transitionListParserNoHeader (head :: tail) := by
  intro symbol hmem
  rcases List.mem_cons.mp hmem with h | hmem
  · rw [h]
    exact hhead
  · exact htail symbol hmem

theorem transitionListParser_encodeNat_noHeader
    (n : Nat) :
    transitionListParserNoHeader (MachineDescription.encodeNat n) := by
  induction n with
  | zero =>
      intro symbol hmem
      simp [MachineDescription.encodeNat] at hmem
      subst symbol
      simp
  | succ n ih =>
      exact
        transitionListParserNoHeader_cons
          (by simp) ih

theorem transitionListParser_encodeCell_noHeader
    (cell : Option Bool) :
    transitionListParserNoHeader
      (MachineDescription.encodeCell cell) := by
  cases cell with
  | none =>
      intro symbol hmem
      simp [MachineDescription.encodeCell] at hmem
      subst symbol
      simp
  | some b =>
      cases b <;>
        intro symbol hmem <;>
        simp [MachineDescription.encodeCell] at hmem <;>
        subst symbol <;>
        simp

theorem transitionListParser_encodeDirection_noHeader
    (dir : Direction) :
    transitionListParserNoHeader
      (MachineDescription.encodeDirection dir) := by
  cases dir <;>
    intro symbol hmem <;>
    simp [MachineDescription.encodeDirection] at hmem <;>
    subst symbol <;>
    simp

theorem transitionListParser_encodeNatAppend_noHeader
    (n : Nat) {suffix : List MachineCodeSymbol}
    (hsuffix : transitionListParserNoHeader suffix) :
    transitionListParserNoHeader
      (MachineDescription.encodeNatAppend n suffix) := by
  simpa [MachineDescription.encodeNatAppend] using
    transitionListParserNoHeader_append
      (transitionListParser_encodeNat_noHeader n) hsuffix

theorem transitionListParser_encodeCellAppend_noHeader
    (cell : Option Bool) {suffix : List MachineCodeSymbol}
    (hsuffix : transitionListParserNoHeader suffix) :
    transitionListParserNoHeader
      (MachineDescription.encodeCellAppend cell suffix) := by
  simpa [MachineDescription.encodeCellAppend] using
    transitionListParserNoHeader_append
      (transitionListParser_encodeCell_noHeader cell) hsuffix

theorem transitionListParser_encodeDirectionAppend_noHeader
    (dir : Direction) {suffix : List MachineCodeSymbol}
    (hsuffix : transitionListParserNoHeader suffix) :
    transitionListParserNoHeader
      (MachineDescription.encodeDirectionAppend dir suffix) := by
  simpa [MachineDescription.encodeDirectionAppend] using
    transitionListParserNoHeader_append
      (transitionListParser_encodeDirection_noHeader dir) hsuffix

theorem transitionListParser_encodeTransitionAppend_noHeader
    (t : TransitionDescription) {suffix : List MachineCodeSymbol}
    (hsuffix : transitionListParserNoHeader suffix) :
    transitionListParserNoHeader
      (MachineDescription.encodeTransitionAppend t suffix) := by
  unfold MachineDescription.encodeTransitionAppend
  exact
    transitionListParserNoHeader_cons
      (by simp)
      (transitionListParser_encodeNatAppend_noHeader t.source
        (transitionListParser_encodeCellAppend_noHeader t.read
          (transitionListParser_encodeCellAppend_noHeader t.write
            (transitionListParser_encodeDirectionAppend_noHeader t.move
              (transitionListParser_encodeNatAppend_noHeader t.target
                hsuffix)))))

theorem transitionListParser_encodeTransition_noHeader
    (t : TransitionDescription) :
    transitionListParserNoHeader
      (MachineDescription.encodeTransition t) := by
  simpa [MachineDescription.encodeTransition] using
    transitionListParser_encodeTransitionAppend_noHeader
      t (suffix := []) (by
        intro symbol hmem
        simp at hmem)

theorem transitionListParser_encodeTransitionsAppend_noHeader
    (transitions : List TransitionDescription)
    {suffix : List MachineCodeSymbol}
    (hsuffix : transitionListParserNoHeader suffix) :
    transitionListParserNoHeader
      (MachineDescription.encodeTransitionsAppend transitions suffix) := by
  induction transitions with
  | nil =>
      exact hsuffix
  | cons t rest ih =>
      exact transitionListParser_encodeTransitionAppend_noHeader t ih

theorem transitionListParserMachine_step_keep_right
    {state next : TransitionListParserState}
    {leftRev suffix : List (Option MachineCodeSymbol)}
    {cell : Option MachineCodeSymbol}
    (htransition :
      TLPM.transition state cell =
        some (cell, Direction.right, next)) :
    TuringMachine.Step TLPM
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
      TLPM.transition state cell =
        some (write, Direction.right, next)) :
    TuringMachine.Step TLPM
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
      TLPM.transition state cell =
        some (cell, Direction.left, next)) :
    TuringMachine.Step TLPM
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

theorem transitionListParserMachine_step_write_left_nonempty
    {state next : TransitionListParserState}
    {leftTail suffix : List (Option MachineCodeSymbol)}
    {leftHead cell write : Option MachineCodeSymbol}
    (htransition :
      TLPM.transition state cell =
        some (write, Direction.left, next)) :
    TuringMachine.Step TLPM
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

theorem transitionListParserMachine_step_write_left_empty
    {state next : TransitionListParserState}
    {leftTail : List (Option MachineCodeSymbol)}
    {leftHead write : Option MachineCodeSymbol}
    (htransition :
      TLPM.transition state none =
        some (write, Direction.left, next)) :
    TuringMachine.Step TLPM
      { state := state
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail) [] }
      { state := next
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: write :: []) } := by
  rw [← transitionListParserOptionTape_move_left_empty
    leftTail leftHead write]
  exact TuringMachine.Step.mk (by
    simpa [transitionListParserOptionTape, Tape.read] using htransition)

theorem transitionListParserMachine_step_keep_left_boundary
    {state next : TransitionListParserState}
    {suffix : List (Option MachineCodeSymbol)}
    {cell : Option MachineCodeSymbol}
    (htransition :
      TLPM.transition state cell =
        some (cell, Direction.left, next)) :
    TuringMachine.Step TLPM
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
    TuringMachine.Step TLPM
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail)
            (some symbol :: suffix) }
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: some symbol :: suffix) } :=
  transitionListParserMachine_step_keep_left_nonempty
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_returnLeft_some_boundary
    (saved : Option MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol))
    (symbol : MachineCodeSymbol) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape []
            (some symbol :: suffix) }
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape []
            (none :: some symbol :: suffix) } :=
  transitionListParserMachine_step_keep_left_boundary
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_returnLeft_none_boundary
    (saved : Option MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape []
            (none :: suffix) }
      { state :=
          TransitionListParserState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape [none] suffix } :=
  transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_returnLeft_none
    (saved : Option MachineCodeSymbol)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape leftRev
            (none :: suffix) }
      { state :=
          TransitionListParserState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape
            (none :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_findCount_done
    (marker : TransitionListParserMarker)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := TransitionListParserState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by
      cases marker <;>
        simp [transitionListParserMachine,
          transitionListParserKeep])

theorem transitionListParserMachine_step_findCount_blank
    (marker : TransitionListParserMarker)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.blank :: suffix) }
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.blank :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by
      cases marker <;>
        simp [transitionListParserMachine,
          transitionListParserKeep])

theorem transitionListParserMachine_step_findCount_tick
    (marker : TransitionListParserMarker)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state := TransitionListParserState.seekCountDone marker
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.blank :: leftRev) suffix } :=
  transitionListParserMachine_step_write_right
    (by
      cases marker <;>
        simp [transitionListParserMachine,
          transitionListParserKeep])

theorem transitionListParserMachine_step_seekCountDone_tick
    (marker : TransitionListParserMarker)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.seekCountDone marker
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state := TransitionListParserState.seekCountDone marker
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.tick :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by
      cases marker <;>
        simp [transitionListParserMachine,
          transitionListParserKeep])

theorem transitionListParserMachine_step_seekCountDone_done_initial
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state :=
          TransitionListParserState.seekCountDone
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_seekCountDone_done_saved
    (saved : Option MachineCodeSymbol)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state :=
          TransitionListParserState.seekCountDone
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := TransitionListParserState.seekMarker saved
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_seekMarker_nonHeader
    (saved : Option MachineCodeSymbol)
    {symbol : MachineCodeSymbol}
    (hsymbol : symbol ≠ MachineCodeSymbol.header)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.seekMarker saved
        tape :=
          transitionListParserOptionTape leftRev
            (some symbol :: suffix) }
      { state := TransitionListParserState.seekMarker saved
        tape :=
          transitionListParserOptionTape
            (some symbol :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by
      cases symbol <;>
        simp [transitionListParserMachine,
          transitionListParserKeep] at hsymbol ⊢)

theorem transitionListParserMachine_step_seekMarker_header
    (saved : Option MachineCodeSymbol)
    (leftTail suffix : List (Option MachineCodeSymbol))
    (leftHead : Option MachineCodeSymbol) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.seekMarker saved
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail)
            (some MachineCodeSymbol.header :: suffix) }
      { state := TransitionListParserState.enterMarkedPosition
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: saved :: suffix) } :=
  transitionListParserMachine_step_write_left_nonempty
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_enterMarkedPosition
    (leftRev suffix : List (Option MachineCodeSymbol))
    (cell : Option MachineCodeSymbol) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.enterMarkedPosition
        tape :=
          transitionListParserOptionTape leftRev
            (cell :: suffix) }
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape
            (cell :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by
      cases cell <;>
        simp [transitionListParserMachine,
          transitionListParserKeep])

theorem transitionListParserMachine_step_enterMarkedPosition_empty
    (leftRev : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.enterMarkedPosition
        tape :=
          transitionListParserOptionTape leftRev [] }
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape
            (none :: leftRev) [] } := by
  rw [← transitionListParserOptionTape_move_right_empty leftRev none]
  exact TuringMachine.Step.mk (by
    simp [transitionListParserMachine,
          transitionListParserOptionTape, Tape.read,
      transitionListParserKeep])

theorem transitionListParserMachine_step_markPosition
    (saved : Option MachineCodeSymbol)
    (leftTail suffix : List (Option MachineCodeSymbol))
    (leftHead : Option MachineCodeSymbol) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail) (saved :: suffix) }
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: some MachineCodeSymbol.header :: suffix) } :=
  transitionListParserMachine_step_write_left_nonempty
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_markPosition_empty
    (leftTail : List (Option MachineCodeSymbol))
    (leftHead : Option MachineCodeSymbol) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail) [] }
      { state := TransitionListParserState.returnLeft none
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: some MachineCodeSymbol.header :: []) } :=
  transitionListParserMachine_step_write_left_empty
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_sourceNat_tick
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.sourceNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state := TransitionListParserState.sourceNat
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.tick :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_sourceNat_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.sourceNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := TransitionListParserState.readCell
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_targetNat_tick
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.targetNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state := TransitionListParserState.targetNat
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.tick :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_step_targetNat_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step TLPM
      { state := TransitionListParserState.targetNat
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  transitionListParserMachine_step_keep_right
    (by simp [transitionListParserMachine,
      transitionListParserKeep])

theorem transitionListParserMachine_computes_nat
    {current next : TransitionListParserState}
    (htick :
      forall leftRev suffix : List (Option MachineCodeSymbol),
        TuringMachine.Step TLPM
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
        TuringMachine.Step TLPM
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
    TuringMachine.Computes TLPM
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
          TuringMachine.Computes TLPM
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

theorem transitionListParserMachine_computes_seekCountDone_initial
    (leftRev : List (Option MachineCodeSymbol)) (count : Nat)
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.Computes TLPM
      { state :=
          TransitionListParserState.seekCountDone
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeNatAppend count tokens).map some) }
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeNat count).reverse.map some)
              leftRev)
            (tokens.map some) } :=
  transitionListParserMachine_computes_nat
    (transitionListParserMachine_step_seekCountDone_tick
      TransitionListParserMarker.initial)
    transitionListParserMachine_step_seekCountDone_done_initial
    leftRev count tokens

theorem transitionListParserMachine_computes_seekCountDone_saved
    (saved : Option MachineCodeSymbol)
    (leftRev : List (Option MachineCodeSymbol)) (count : Nat)
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.Computes TLPM
      { state :=
          TransitionListParserState.seekCountDone
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeNatAppend count tokens).map some) }
      { state := TransitionListParserState.seekMarker saved
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeNat count).reverse.map some)
              leftRev)
            (tokens.map some) } :=
  transitionListParserMachine_computes_nat
    (transitionListParserMachine_step_seekCountDone_tick
      (TransitionListParserMarker.saved saved))
    (transitionListParserMachine_step_seekCountDone_done_saved saved)
    leftRev count tokens

theorem transitionListParserMachine_computes_needTransition
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes TLPM
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
    TuringMachine.Computes TLPM
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
    TuringMachine.Computes TLPM
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
    TuringMachine.Computes TLPM
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
    TuringMachine.Computes TLPM
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
      TuringMachine.Computes TLPM
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
      TuringMachine.Computes TLPM
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
      TuringMachine.Computes TLPM
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
      TuringMachine.Computes TLPM
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
      TuringMachine.Computes TLPM
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

theorem transitionListParserMachine_computes_succCount_to_needTransition
    (count : Nat) (tokens : Word MachineCodeSymbol) :
    TuringMachine.Computes TLPM
      { state :=
          TransitionListParserState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape []
            ((MachineDescription.encodeNatAppend (count + 1)
              tokens).map some) }
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape
            ((MachineCodeSymbol.blank ::
              MachineDescription.encodeNat count).reverse.map some)
            (tokens.map some) } := by
  have htick :
      TuringMachine.Step TLPM
        { state :=
            TransitionListParserState.findCount
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape []
              ((MachineDescription.encodeNatAppend (count + 1)
                tokens).map some) }
        { state :=
            TransitionListParserState.seekCountDone
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape
              [some MachineCodeSymbol.blank]
              ((MachineDescription.encodeNatAppend count tokens).map
                some) } := by
    simpa [MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat] using
      transitionListParserMachine_step_findCount_tick
        TransitionListParserMarker.initial []
        ((MachineDescription.encodeNatAppend count tokens).map some)
  have hseek :=
    transitionListParserMachine_computes_seekCountDone_initial
      [some MachineCodeSymbol.blank] count tokens
  exact
    TuringMachine.Computes.step htick
      (by
        simpa [MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat, List.map_append,
          List.reverse_cons, List.append_assoc] using hseek)

theorem transitionListParserMachine_computes_nextTransition_to_markPosition
    (count : Nat) (t : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes TLPM
      { state :=
          TransitionListParserState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape []
            ((MachineDescription.encodeNatAppend (count + 1)
              (MachineDescription.encodeTransitionAppend t suffix)).map
              some) }
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            ((List.append
              (MachineCodeSymbol.blank ::
                MachineDescription.encodeNat count)
              (MachineDescription.encodeTransition t)).reverse.map some)
            (suffix.map some) } := by
  have htick :
      TuringMachine.Step TLPM
        { state :=
            TransitionListParserState.findCount
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape []
              ((MachineDescription.encodeNatAppend (count + 1)
                (MachineDescription.encodeTransitionAppend t suffix)).map
                some) }
        { state :=
            TransitionListParserState.seekCountDone
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape
              [some MachineCodeSymbol.blank]
              ((MachineDescription.encodeNatAppend count
                (MachineDescription.encodeTransitionAppend t suffix)).map
                some) } := by
    simpa [MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat] using
      transitionListParserMachine_step_findCount_tick
        TransitionListParserMarker.initial []
        ((MachineDescription.encodeNatAppend count
          (MachineDescription.encodeTransitionAppend t suffix)).map some)
  have hseek :=
    transitionListParserMachine_computes_seekCountDone_initial
      [some MachineCodeSymbol.blank] count
      (MachineDescription.encodeTransitionAppend t suffix)
  have hparse :=
    transitionListParserMachine_computes_transition t
      (List.append
        ((MachineDescription.encodeNat count).reverse.map some)
        [some MachineCodeSymbol.blank])
      suffix
  exact
    TuringMachine.Computes.step htick
      (TuringMachine.computes_trans
        (by
          simpa [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using hseek)
        (by
          simpa [MachineDescription.encodeTransition,
            MachineDescription.encodeTransitionAppend,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeCellAppend,
            MachineDescription.encodeDirectionAppend,
            List.reverse_append, List.map_append,
            List.append_assoc] using hparse))

theorem transitionListParserMachine_returnLeft_noBoundary
    (saved : Option MachineCodeSymbol)
    (leftSymbols : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes TLPM
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
    TuringMachine.Computes TLPM
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

theorem transitionListParserMachine_returnLeft_toBoundary
    (saved : Option MachineCodeSymbol)
    (leftSymbols : Word MachineCodeSymbol)
    (prefixLeft suffix : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) :
    TuringMachine.Computes TLPM
      { state := TransitionListParserState.returnLeft saved
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft))
            (some current :: suffix) }
      { state :=
          TransitionListParserState.findCount
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
          (transitionListParserMachine_step_returnLeft_some_nonempty
            saved prefixLeft suffix none current)
          (by
            simpa using
              TuringMachine.Computes.step
                (transitionListParserMachine_step_returnLeft_none
                  saved prefixLeft (some current :: suffix))
                (TuringMachine.Computes.refl _))
  | cons leftHead leftTail ih =>
      have htail := ih (some current :: suffix) leftHead
      exact
        TuringMachine.Computes.step
          (transitionListParserMachine_step_returnLeft_some_nonempty
            saved
            (List.append (leftTail.map some) (none :: prefixLeft))
            suffix
            (some leftHead)
            current)
          (by
            simpa [List.append_assoc] using htail)

theorem transitionListParserMachine_markPosition_returnLeft_noBoundary
    (saved : Option MachineCodeSymbol)
    (leftSymbols : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes TLPM
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (some current :: leftSymbols.map some)
            (saved :: suffix) }
      { state :=
          TransitionListParserState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape [none]
            (List.append (leftSymbols.reverse.map some)
              (some current ::
                some MachineCodeSymbol.header :: suffix)) } := by
  exact
    TuringMachine.Computes.step
      (transitionListParserMachine_step_markPosition
        saved (leftSymbols.map some) suffix (some current))
      (transitionListParserMachine_returnLeft_noBoundary
        saved leftSymbols current
        (some MachineCodeSymbol.header :: suffix))

theorem transitionListParserMachine_markPosition_returnLeft_toBoundary
    (saved : Option MachineCodeSymbol)
    (leftSymbols : Word MachineCodeSymbol)
    (prefixLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes TLPM
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (some current ::
              List.append (leftSymbols.map some) (none :: prefixLeft))
            (saved :: suffix) }
      { state :=
          TransitionListParserState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape (none :: prefixLeft)
            (List.append (leftSymbols.reverse.map some)
              (some current ::
                some MachineCodeSymbol.header :: suffix)) } := by
  exact
    TuringMachine.Computes.step
      (transitionListParserMachine_step_markPosition
        saved
        (List.append (leftSymbols.map some) (none :: prefixLeft))
        suffix (some current))
      (transitionListParserMachine_returnLeft_toBoundary
        saved leftSymbols prefixLeft
        (some MachineCodeSymbol.header :: suffix)
        current)

theorem transitionListParserMachine_markPosition_empty_returnLeft_noBoundary
    (leftSymbols : Word MachineCodeSymbol)
    (current : MachineCodeSymbol) :
    TuringMachine.Computes TLPM
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (some current :: leftSymbols.map some) [] }
      { state :=
          TransitionListParserState.findCount
            (TransitionListParserMarker.saved none)
        tape :=
          transitionListParserOptionTape [none]
            (List.append (leftSymbols.reverse.map some)
              (some current ::
                some MachineCodeSymbol.header :: [])) } := by
  exact
    TuringMachine.Computes.step
      (transitionListParserMachine_step_markPosition_empty
        (leftSymbols.map some) (some current))
      (transitionListParserMachine_returnLeft_noBoundary
        none leftSymbols current
        [some MachineCodeSymbol.header])

theorem transitionListParserMachine_markPosition_empty_returnLeft_toBoundary
    (leftSymbols : Word MachineCodeSymbol)
    (prefixLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) :
    TuringMachine.Computes TLPM
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (some current ::
              List.append (leftSymbols.map some) (none :: prefixLeft))
            [] }
      { state :=
          TransitionListParserState.findCount
            (TransitionListParserMarker.saved none)
        tape :=
          transitionListParserOptionTape (none :: prefixLeft)
            (List.append (leftSymbols.reverse.map some)
              (some current ::
                some MachineCodeSymbol.header :: [])) } := by
  exact
    TuringMachine.Computes.step
      (transitionListParserMachine_step_markPosition_empty
        (List.append (leftSymbols.map some) (none :: prefixLeft))
        (some current))
      (transitionListParserMachine_returnLeft_toBoundary
        none leftSymbols prefixLeft
        (some MachineCodeSymbol.header :: [])
        current)

theorem transitionListParserMachine_haltsFrom_findCount_blank_done
    (marker : TransitionListParserMarker)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.HaltsFrom TLPM
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.blank ::
              some MachineCodeSymbol.done :: suffix) } := by
  have hblank :=
    transitionListParserMachine_step_findCount_blank
      marker leftRev (some MachineCodeSymbol.done :: suffix)
  have hdone :=
    transitionListParserMachine_step_findCount_done
      marker (some MachineCodeSymbol.blank :: leftRev) suffix
  have hcomp :
      TuringMachine.Computes TLPM
        { state := TransitionListParserState.findCount marker
          tape :=
            transitionListParserOptionTape leftRev
              (some MachineCodeSymbol.blank ::
                some MachineCodeSymbol.done :: suffix) }
        { state := TransitionListParserState.halt
          tape :=
            transitionListParserOptionTape
              (some MachineCodeSymbol.done ::
                some MachineCodeSymbol.blank :: leftRev)
              suffix } :=
    TuringMachine.Computes.step hblank
      (TuringMachine.Computes.step hdone
        (TuringMachine.Computes.refl _))
  exact TuringMachine.halts_from_of_computes hcomp rfl

theorem transitionListParserMachine_haltsFrom_findCount_blanks_done
    (marker : TransitionListParserMarker)
    (blanks : Nat) (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.HaltsFrom TLPM
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              (some MachineCodeSymbol.done :: suffix)) } := by
  induction blanks generalizing leftRev with
  | zero =>
      have hstep :=
        transitionListParserMachine_step_findCount_done
          marker leftRev suffix
      exact
        TuringMachine.halts_from_of_computes
          (TuringMachine.Computes.step hstep
            (TuringMachine.Computes.refl _))
          rfl
  | succ blanks ih =>
      have hstep :=
        transitionListParserMachine_step_findCount_blank
          marker leftRev
          (List.append
            (List.replicate blanks (some MachineCodeSymbol.blank))
            (some MachineCodeSymbol.done :: suffix))
      exact
        TuringMachine.halts_from_of_computes_prefix
          (TuringMachine.Computes.step hstep
            (TuringMachine.Computes.refl _))
          (ih (some MachineCodeSymbol.blank :: leftRev))

theorem transitionListParser_replicate_blank_append_cons
    (blanks : Nat) (leftRev : List (Option MachineCodeSymbol)) :
    List.append
        (List.replicate blanks (some MachineCodeSymbol.blank))
        (some MachineCodeSymbol.blank :: leftRev) =
      List.append
        (List.replicate (blanks + 1) (some MachineCodeSymbol.blank))
        leftRev := by
  induction blanks with
  | zero =>
      rfl
  | succ blanks ih =>
      simpa [List.replicate] using ih

theorem transitionListParser_blank_cons_replicate_append_none
    (blanks : Nat) :
    some MachineCodeSymbol.blank ::
        List.append
          (List.replicate blanks (some MachineCodeSymbol.blank))
          [none] =
      List.append
        (List.replicate blanks (some MachineCodeSymbol.blank))
        [some MachineCodeSymbol.blank, none] := by
  induction blanks with
  | zero =>
      rfl
  | succ blanks ih =>
      simpa [List.replicate, List.append_assoc] using
        congrArg (fun xs => some MachineCodeSymbol.blank :: xs) ih

theorem transitionListParserMachine_computes_findCount_blanks
    (marker : TransitionListParserMarker)
    (blanks : Nat) (leftRev rest : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes TLPM
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              rest) }
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape
            (List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              leftRev)
            rest } := by
  induction blanks generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.refl _
  | succ blanks ih =>
      have hstep :=
        transitionListParserMachine_step_findCount_blank
          marker leftRev
          (List.append
            (List.replicate blanks (some MachineCodeSymbol.blank))
            rest)
      exact
        TuringMachine.Computes.step hstep
          (by
            have hrep :=
              transitionListParser_replicate_blank_append_cons
                blanks leftRev
            have hcomp := ih (some MachineCodeSymbol.blank :: leftRev)
            rw [hrep] at hcomp
            simpa [List.append_assoc] using hcomp)


end Computability
end FoC
