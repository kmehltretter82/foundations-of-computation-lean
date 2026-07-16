import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.Runs

set_option doc.verso true

/-!
# Transition-list suffix-marker restoration

A finite gate restores the suffix cell saved by the transition-list parser and
returns to the first parsed transition token.
-/

namespace FoC
namespace Computability

open Languages

inductive MarkerRestoreState where
  | seek (saved : Option MachineCodeSymbol) : MarkerRestoreState
  | rewind : MarkerRestoreState
  | enterBlank : MarkerRestoreState
  | enterDone : MarkerRestoreState
  | halt : MarkerRestoreState
deriving DecidableEq

namespace MarkerRestoreState

def elems : List MarkerRestoreState :=
  TransitionListParserState.optionCells.map MarkerRestoreState.seek ++
    [rewind, enterBlank, enterDone, halt]

def finite : Foundation.FiniteType MarkerRestoreState where
  elems := elems
  complete := by
    intro state
    cases state with
    | seek saved =>
        simp [elems,
          TransitionListParserState.optionCells_complete saved]
    | rewind => simp [elems]
    | enterBlank => simp [elems]
    | enterDone => simp [elems]
    | halt => simp [elems]

end MarkerRestoreState

def markerRestoreMachine :
    TuringMachine MachineCodeSymbol MarkerRestoreState where
  start := MarkerRestoreState.seek none
  halt := MarkerRestoreState.halt
  transition := fun state cell =>
    match state, cell with
    | MarkerRestoreState.seek saved,
        some MachineCodeSymbol.header =>
        some (saved, Direction.left, MarkerRestoreState.rewind)
    | MarkerRestoreState.seek saved, some symbol =>
        some
          (some symbol, Direction.right,
            MarkerRestoreState.seek saved)
    | MarkerRestoreState.rewind, some symbol =>
        some
          (some symbol, Direction.left,
            MarkerRestoreState.rewind)
    | MarkerRestoreState.rewind, none =>
        some (none, Direction.right, MarkerRestoreState.enterBlank)
    | MarkerRestoreState.enterBlank,
        some MachineCodeSymbol.blank =>
        some
          (some MachineCodeSymbol.blank, Direction.right,
            MarkerRestoreState.enterDone)
    | MarkerRestoreState.enterDone,
        some MachineCodeSymbol.blank =>
        some
          (some MachineCodeSymbol.blank, Direction.right,
            MarkerRestoreState.enterDone)
    | MarkerRestoreState.enterDone,
        some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            MarkerRestoreState.halt)
    | _, _ => none
  statesFinite := MarkerRestoreState.finite

theorem markerRestoreMachine_step_seek_nonHeader
    (saved : Option MachineCodeSymbol)
    {symbol : MachineCodeSymbol}
    (hsymbol : symbol ≠ MachineCodeSymbol.header)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step markerRestoreMachine
      { state := MarkerRestoreState.seek saved
        tape :=
          transitionListParserOptionTape leftRev
            (some symbol :: suffix) }
      { state := MarkerRestoreState.seek saved
        tape :=
          transitionListParserOptionTape
            (some symbol :: leftRev) suffix } := by
  rw [← transitionListParserOptionTape_move_right
    leftRev suffix (some symbol) (some symbol)]
  exact TuringMachine.Step.mk (by
    cases symbol <;>
      simp [markerRestoreMachine, transitionListParserOptionTape,
        Tape.read] at hsymbol ⊢)

theorem markerRestoreMachine_computes_seek_prefix
    (saved : Option MachineCodeSymbol)
    (symbols : Word MachineCodeSymbol)
    (hsymbols : transitionListParserNoHeader symbols)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes markerRestoreMachine
      { state := MarkerRestoreState.seek saved
        tape :=
          transitionListParserOptionTape leftRev
            (List.append (symbols.map some)
              (some MachineCodeSymbol.header :: suffix)) }
      { state := MarkerRestoreState.seek saved
        tape :=
          transitionListParserOptionTape
            (List.append (symbols.reverse.map some) leftRev)
            (some MachineCodeSymbol.header :: suffix) } := by
  induction symbols generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.refl _
  | cons symbol tail ih =>
      have hhead : symbol ≠ MachineCodeSymbol.header :=
        hsymbols symbol (by simp)
      have htail : transitionListParserNoHeader tail := by
        intro candidate hmem
        exact hsymbols candidate (by simp [hmem])
      have hstep :=
        markerRestoreMachine_step_seek_nonHeader saved hhead leftRev
          (List.append (tail.map some)
            (some MachineCodeSymbol.header :: suffix))
      have hrest := ih htail (some symbol :: leftRev)
      exact
        TuringMachine.Computes.step
          (by simpa using hstep)
          (by
            simpa [List.map_reverse, List.append_assoc]
              using hrest)

theorem markerRestoreMachine_step_restore_marker
    (saved : Option MachineCodeSymbol)
    (leftTail suffix : List (Option MachineCodeSymbol))
    (leftHead : Option MachineCodeSymbol) :
    TuringMachine.Step markerRestoreMachine
      { state := MarkerRestoreState.seek saved
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail)
            (some MachineCodeSymbol.header :: suffix) }
      { state := MarkerRestoreState.rewind
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: saved :: suffix) } := by
  rw [← transitionListParserOptionTape_move_left
    leftTail suffix leftHead (some MachineCodeSymbol.header) saved]
  exact TuringMachine.Step.mk (by
    simp [markerRestoreMachine, transitionListParserOptionTape,
      Tape.read])

theorem markerRestoreMachine_step_rewind_symbol
    (leftTail suffix : List (Option MachineCodeSymbol))
    (leftHead : Option MachineCodeSymbol)
    (current : MachineCodeSymbol) :
    TuringMachine.Step markerRestoreMachine
      { state := MarkerRestoreState.rewind
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail)
            (some current :: suffix) }
      { state := MarkerRestoreState.rewind
        tape :=
          transitionListParserOptionTape leftTail
            (leftHead :: some current :: suffix) } := by
  rw [← transitionListParserOptionTape_move_left
    leftTail suffix leftHead (some current) (some current)]
  exact TuringMachine.Step.mk (by
    simp [markerRestoreMachine, transitionListParserOptionTape,
      Tape.read])

theorem markerRestoreMachine_computes_rewind_to_boundary
    (leftSymbols : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes markerRestoreMachine
      { state := MarkerRestoreState.rewind
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some) [none])
            (some current :: suffix) }
      { state := MarkerRestoreState.rewind
        tape :=
          transitionListParserOptionTape []
            (none ::
              List.append (leftSymbols.reverse.map some)
                (some current :: suffix)) } := by
  induction leftSymbols generalizing current suffix with
  | nil =>
      exact
        TuringMachine.Computes.step
          (by
            simpa using
              markerRestoreMachine_step_rewind_symbol
                [] suffix none current)
          (TuringMachine.Computes.refl _)
  | cons leftHead leftTail ih =>
      have hstep :=
        markerRestoreMachine_step_rewind_symbol
          (List.append (leftTail.map some) [none]) suffix
          (some leftHead) current
      have hrest := ih leftHead (some current :: suffix)
      exact
        TuringMachine.Computes.step
          (by simpa using hstep)
          (by
            simpa [List.map_reverse, List.append_assoc]
              using hrest)

theorem markerRestoreMachine_step_rewind_boundary
    (suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step markerRestoreMachine
      { state := MarkerRestoreState.rewind
        tape :=
          transitionListParserOptionTape [] (none :: suffix) }
      { state := MarkerRestoreState.enterBlank
        tape :=
          transitionListParserOptionTape [none] suffix } := by
  rw [← transitionListParserOptionTape_move_right
    [] suffix none none]
  exact TuringMachine.Step.mk (by
    simp [markerRestoreMachine, transitionListParserOptionTape,
      Tape.read])

theorem markerRestoreMachine_step_enter_blank
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step markerRestoreMachine
      { state := MarkerRestoreState.enterBlank
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.blank :: suffix) }
      { state := MarkerRestoreState.enterDone
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.blank :: leftRev) suffix } := by
  rw [← transitionListParserOptionTape_move_right
    leftRev suffix (some MachineCodeSymbol.blank)
      (some MachineCodeSymbol.blank)]
  exact TuringMachine.Step.mk (by
    simp [markerRestoreMachine, transitionListParserOptionTape,
      Tape.read])

theorem markerRestoreMachine_step_enter_more_blank
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step markerRestoreMachine
      { state := MarkerRestoreState.enterDone
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.blank :: suffix) }
      { state := MarkerRestoreState.enterDone
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.blank :: leftRev) suffix } := by
  rw [← transitionListParserOptionTape_move_right
    leftRev suffix (some MachineCodeSymbol.blank)
      (some MachineCodeSymbol.blank)]
  exact TuringMachine.Step.mk (by
    simp [markerRestoreMachine, transitionListParserOptionTape,
      Tape.read])

theorem markerRestoreMachine_step_enter_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step markerRestoreMachine
      { state := MarkerRestoreState.enterDone
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := MarkerRestoreState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← transitionListParserOptionTape_move_right
    leftRev suffix (some MachineCodeSymbol.done)
      (some MachineCodeSymbol.done)]
  exact TuringMachine.Step.mk (by
    simp [markerRestoreMachine, transitionListParserOptionTape,
      Tape.read])

theorem markerRestoreMachine_computes_enterDone_blanks
    (blanks : Nat)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes markerRestoreMachine
      { state := MarkerRestoreState.enterDone
        tape :=
          transitionListParserOptionTape leftRev
            (List.append
              (List.replicate blanks
                (some MachineCodeSymbol.blank))
              (some MachineCodeSymbol.done :: suffix)) }
      { state := MarkerRestoreState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                leftRev)
            suffix } := by
  induction blanks generalizing leftRev with
  | zero =>
      exact
        TuringMachine.Computes.step
          (by
            simpa using
              markerRestoreMachine_step_enter_done leftRev suffix)
          (TuringMachine.Computes.refl _)
  | succ blanks ih =>
      have hstep :=
        markerRestoreMachine_step_enter_more_blank leftRev
          (List.append
            (List.replicate blanks
              (some MachineCodeSymbol.blank))
            (some MachineCodeSymbol.done :: suffix))
      have hrest :=
        ih (some MachineCodeSymbol.blank :: leftRev)
      have hrep :=
        list_replicate_append_cons_eq_cons_append
          (some MachineCodeSymbol.blank) blanks leftRev
      have htarget :=
        congrArg (List.cons (some MachineCodeSymbol.done)) hrep
      exact
        TuringMachine.Computes.step
          (by
            simpa [List.replicate_succ]
              using hstep)
          (by
            simpa [List.replicate_succ, hrep, htarget,
              List.append_assoc]
              using hrest)

end Computability
end FoC
