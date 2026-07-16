import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.Runs
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

namespace FoC
namespace Computability

open Languages

namespace Section53TransitionParserHandoff

/-!
# Exact transition-parser handoff

The public transition-list parser theorem exposes ordinary halting. The
interpreter composes that parser with a runtime table scan, so this module
records the parser's exact physical endpoint for the smallest nonempty table.
-/

/-- The suffix cells left by the parser's final position marker. -/
def markedSuffixCells
    (suffix : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  match suffix with
  | [] => [some MachineCodeSymbol.header]
  | _ :: rest => some MachineCodeSymbol.header :: rest.map some

theorem markedSuffixCells_cons_ne_original
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (hfirst : first ≠ MachineCodeSymbol.header) :
    markedSuffixCells (first :: rest) ≠
      (first :: rest).map some := by
  intro heq
  cases first <;> simp [markedSuffixCells] at hfirst heq

/-- Exact halt configuration after parsing one transition row. -/
def oneTransitionHaltConfig
    (t : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state := TransitionListParserState.halt
    tape :=
      transitionListParserOptionTape
        [some MachineCodeSymbol.done,
          some MachineCodeSymbol.blank,
          none]
        (List.append
          (List.map some (MachineDescription.encodeTransition t))
          (markedSuffixCells suffix)) }

theorem transitionListParserMachine_computes_findCount_blank_done_exact
    (marker : TransitionListParserMarker)
    (tail : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape [none]
            (some MachineCodeSymbol.blank ::
              some MachineCodeSymbol.done :: tail) }
      { state := TransitionListParserState.halt
        tape :=
          transitionListParserOptionTape
            [some MachineCodeSymbol.done,
              some MachineCodeSymbol.blank,
              none]
            tail } := by
  have hblank :=
    transitionListParserMachine_computes_findCount_blanks
      marker 1 [none]
      (some MachineCodeSymbol.done :: tail)
  have hdone :=
    transitionListParserMachine_step_findCount_done marker
      [some MachineCodeSymbol.blank, none] tail
  exact
    TuringMachine.computes_trans
      (by simpa using hblank)
      (TuringMachine.Computes.step hdone
        (TuringMachine.Computes.refl _))

theorem transitionListParserMachine_computes_findCount_blanks_done_exact
    (marker : TransitionListParserMarker)
    (blanks : Nat)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (List.append
              (List.replicate blanks
                (some MachineCodeSymbol.blank))
              (some MachineCodeSymbol.done :: suffix)) }
      { state := TransitionListParserState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                leftRev)
            suffix } := by
  have hblanks :=
    transitionListParserMachine_computes_findCount_blanks
      marker blanks leftRev
      (some MachineCodeSymbol.done :: suffix)
  have hdone :=
    transitionListParserMachine_step_findCount_done marker
      (List.append
        (List.replicate blanks (some MachineCodeSymbol.blank))
        leftRev)
      suffix
  exact
    TuringMachine.computes_trans
      hblanks
      (TuringMachine.Computes.step hdone
        (TuringMachine.Computes.refl _))

theorem transitionListParserMachine_computes_markPosition_after_oneCount_exact
    (t : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            ((List.append
              [MachineCodeSymbol.blank, MachineCodeSymbol.done]
              (MachineDescription.encodeTransition t)).reverse.map some)
            (suffix.map some) }
      (oneTransitionHaltConfig t suffix) := by
  let leftNormal : Word MachineCodeSymbol :=
    List.append
      [MachineCodeSymbol.blank, MachineCodeSymbol.done]
      (MachineDescription.encodeTransition t)
  have hrevNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal]
  cases hrev : leftNormal.reverse with
  | nil =>
      exact False.elim (hrevNonempty hrev)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa using! h
      cases suffix with
      | nil =>
          have hreturn :=
            transitionListParserMachine_markPosition_empty_returnLeft_noBoundary
              leftSymbols current
          have hmap :
              leftNormal.map some =
                List.append (leftSymbols.reverse.map some)
                  [some current] := by
            simpa [List.map_append] using
              congrArg (List.map some) hleft
          have hrest :
              List.append (leftSymbols.reverse.map some)
                  [some current, some MachineCodeSymbol.header] =
                some MachineCodeSymbol.blank ::
                  some MachineCodeSymbol.done ::
                    List.append
                      (List.map some
                        (MachineDescription.encodeTransition t))
                      [some MachineCodeSymbol.header] := by
            calc
              List.append (leftSymbols.reverse.map some)
                  [some current, some MachineCodeSymbol.header] =
                List.append
                  (List.append (leftSymbols.reverse.map some)
                    [some current])
                  [some MachineCodeSymbol.header] := by
                    simp [List.append_assoc]
              _ = List.append (leftNormal.map some)
                    [some MachineCodeSymbol.header] := by
                    rw [hmap]
              _ = some MachineCodeSymbol.blank ::
                    some MachineCodeSymbol.done ::
                      List.append
                        (List.map some
                          (MachineDescription.encodeTransition t))
                        [some MachineCodeSymbol.header] := by
                    simp [leftNormal]
          rw [hrest] at hreturn
          have hfinish :=
            transitionListParserMachine_computes_findCount_blank_done_exact
              (TransitionListParserMarker.saved none)
              (List.append
                (List.map some
                  (MachineDescription.encodeTransition t))
                [some MachineCodeSymbol.header])
          exact
            TuringMachine.computes_trans
              (by simpa using hreturn)
              (by
                simpa [oneTransitionHaltConfig, markedSuffixCells]
                  using hfinish)
      | cons first rest =>
          have hreturn :=
            transitionListParserMachine_markPosition_returnLeft_noBoundary
              (some first) leftSymbols current (rest.map some)
          have hmap :
              leftNormal.map some =
                List.append (leftSymbols.reverse.map some)
                  [some current] := by
            simpa [List.map_append] using
              congrArg (List.map some) hleft
          have hrest :
              List.append (leftSymbols.reverse.map some)
                  (some current ::
                    some MachineCodeSymbol.header :: rest.map some) =
                some MachineCodeSymbol.blank ::
                  some MachineCodeSymbol.done ::
                    List.append
                      (List.map some
                        (MachineDescription.encodeTransition t))
                      (some MachineCodeSymbol.header :: rest.map some) := by
            calc
              List.append (leftSymbols.reverse.map some)
                  (some current ::
                    some MachineCodeSymbol.header :: rest.map some) =
                List.append
                  (List.append (leftSymbols.reverse.map some)
                    [some current])
                  (some MachineCodeSymbol.header :: rest.map some) := by
                    simp [List.append_assoc]
              _ = List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header :: rest.map some) := by
                    rw [hmap]
              _ = some MachineCodeSymbol.blank ::
                    some MachineCodeSymbol.done ::
                      List.append
                        (List.map some
                          (MachineDescription.encodeTransition t))
                        (some MachineCodeSymbol.header ::
                          rest.map some) := by
                    simp [leftNormal]
          rw [hrest] at hreturn
          have hfinish :=
            transitionListParserMachine_computes_findCount_blank_done_exact
              (TransitionListParserMarker.saved (some first))
              (List.append
                (List.map some
                  (MachineDescription.encodeTransition t))
                (some MachineCodeSymbol.header :: rest.map some))
          exact
            TuringMachine.computes_trans
              (by simpa using hreturn)
              (by
                simpa [oneTransitionHaltConfig, markedSuffixCells]
                  using hfinish)

theorem transitionListParserMachine_computes_oneTransition_exact
    (t : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      (TuringMachine.initial transitionListParserMachine
        (MachineDescription.encodeNatAppend 1
          (MachineDescription.encodeTransitionAppend t suffix)))
      (oneTransitionHaltConfig t suffix) := by
  have hprefix :=
    transitionListParserMachine_computes_nextTransition_to_markPosition
      0 t suffix
  have htail :=
    transitionListParserMachine_computes_markPosition_after_oneCount_exact
      t suffix
  exact
    TuringMachine.computes_trans
      (by
        simpa [TuringMachine.initial, transitionListParserMachine,
          transitionListParserOptionTape_nil_eq_input]
          using hprefix)
      (by
        simpa [MachineDescription.encodeNat]
          using htail)

/-- Exact parser endpoint when the encoded transition count is zero. -/
def zeroTransitionHaltConfig
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state := TransitionListParserState.halt
    tape :=
      transitionListParserOptionTape
        [some MachineCodeSymbol.done]
        (tokens.map some) }

theorem transitionListParserMachine_computes_count_zero_exact
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      (TuringMachine.initial transitionListParserMachine
        (MachineDescription.encodeNatAppend 0 tokens))
      (zeroTransitionHaltConfig tokens) := by
  have hstep :=
    transitionListParserMachine_step_findCount_done
      TransitionListParserMarker.initial [] (tokens.map some)
  change
    TuringMachine.Computes transitionListParserMachine
      { state :=
          TransitionListParserState.findCount
            TransitionListParserMarker.initial
        tape :=
          Tape.input
            (MachineDescription.encodeNatAppend 0 tokens) }
      (zeroTransitionHaltConfig tokens)
  rw [← transitionListParserOptionTape_nil_eq_input
    (MachineDescription.encodeNatAppend 0 tokens)]
  exact
    TuringMachine.Computes.step
      (by
        simpa [MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat]
          using hstep)
      (by
        simpa [zeroTransitionHaltConfig]
          using TuringMachine.Computes.refl
            (zeroTransitionHaltConfig tokens))

/-!
## Saved-marker restoration gate

The parser still carries the overwritten suffix head in
`TransitionListParserMarker.saved` immediately before its final `done` row.
The following finite gate is entered after that row moves onto the first
transition token.  It scans to the marker, restores the saved cell, rewinds to
the true left tape boundary, and halts again on the first transition token.
-/

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

def savedSuffixHead
    (suffix : Word MachineCodeSymbol) : Option MachineCodeSymbol :=
  match suffix with
  | [] => none
  | first :: _ => some first

/-- Exact suffix cells after restoration; the empty case retains one visited blank. -/
def restoredSuffixCells
    (suffix : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  match suffix with
  | [] => [none]
  | _ => suffix.map some

def markerRestoreSourceConfig
    (t : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState :=
  { state := MarkerRestoreState.seek (savedSuffixHead suffix)
    tape := (oneTransitionHaltConfig t suffix).tape }

def markerRestoreTargetConfig
    (t : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState :=
  { state := MarkerRestoreState.halt
    tape :=
      transitionListParserOptionTape
        [some MachineCodeSymbol.done,
          some MachineCodeSymbol.blank,
          none]
        (List.append
          (List.map some (MachineDescription.encodeTransition t))
          (restoredSuffixCells suffix)) }

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

/-- Physical counter cells left of the first parsed transition row. -/
def parsedTableLeftRev (rowCount : Nat) :
    List (Option MachineCodeSymbol) :=
  some MachineCodeSymbol.done ::
    List.append
      (List.replicate rowCount (some MachineCodeSymbol.blank))
      [none]

theorem transitionListParserOptionTape_append_none_equiv
    (leftRev rest : List (Option MachineCodeSymbol)) :
    Tape.Equiv
      (transitionListParserOptionTape leftRev rest)
      (transitionListParserOptionTape
        (List.append leftRev [none]) rest) := by
  cases rest with
  | nil =>
      exact
        ⟨(dropTrailingNone_append_none leftRev).symm,
          rfl, rfl⟩
  | cons cell suffix =>
      exact
        ⟨(dropTrailingNone_append_none leftRev).symm,
          rfl, rfl⟩

/-- Final mark-position configuration after the last row has been decoded. -/
def finalTransitionMarkConfig
    (rowCount : Nat)
    (symbols suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state := TransitionListParserState.markPosition
    tape :=
      transitionListParserOptionTape
        (List.append
          ((List.append
            (List.replicate rowCount MachineCodeSymbol.blank)
            (MachineCodeSymbol.done :: symbols)).reverse.map some)
          [none])
        (suffix.map some) }

/-- Exact marked parser endpoint for a nonempty decoded table. -/
def parsedTransitionHaltConfig
    (rowCount : Nat)
    (symbols suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state := TransitionListParserState.halt
    tape :=
      transitionListParserOptionTape
        (parsedTableLeftRev rowCount)
        (List.append (symbols.map some)
          (markedSuffixCells suffix)) }

theorem transitionListParserMachine_computes_final_mark_exact
    (rowCount : Nat)
    (symbols suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      (finalTransitionMarkConfig rowCount symbols suffix)
      (parsedTransitionHaltConfig rowCount symbols suffix) := by
  let leftNormal : Word MachineCodeSymbol :=
    List.append
      (List.replicate rowCount MachineCodeSymbol.blank)
      (MachineCodeSymbol.done :: symbols)
  have hreverseNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal]
  cases hreverse : leftNormal.reverse with
  | nil =>
      exact False.elim (hreverseNonempty hreverse)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hreverse
        simpa using! h
      cases suffix with
      | nil =>
          have hreturn :=
            transitionListParserMachine_markPosition_empty_returnLeft_toBoundary
              leftSymbols [] current
          have hprefix :
              List.append (leftSymbols.map some).reverse [some current] =
                leftNormal.map some := by
            have hmap := congrArg (List.map some) hleft
            simpa [List.map_append, List.map_reverse,
              List.append_assoc]
              using hmap.symm
          have htargetRest :
              List.append (leftSymbols.map some).reverse
                  [some current, some MachineCodeSymbol.header] =
                List.append
                  (List.replicate rowCount
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.done ::
                    List.append (symbols.map some)
                      [some MachineCodeSymbol.header]) := by
            calc
              List.append (leftSymbols.map some).reverse
                  [some current, some MachineCodeSymbol.header] =
                List.append
                  (List.append (leftSymbols.map some).reverse
                    [some current])
                  [some MachineCodeSymbol.header] := by
                  simp [List.append_assoc]
              _ = List.append (leftNormal.map some)
                    [some MachineCodeSymbol.header] := by
                  rw [hprefix]
              _ = List.append
                    (List.replicate rowCount
                      (some MachineCodeSymbol.blank))
                    (some MachineCodeSymbol.done ::
                      List.append (symbols.map some)
                        [some MachineCodeSymbol.header]) := by
                  simp [leftNormal, List.map_append,
                    List.map_replicate, List.append_assoc]
          have hfinish :=
            transitionListParserMachine_computes_findCount_blanks_done_exact
              (TransitionListParserMarker.saved none)
              rowCount [none]
              (List.append (symbols.map some)
                [some MachineCodeSymbol.header])
          have htargetRest' :
              List.append (leftSymbols.reverse.map some)
                  [some current, some MachineCodeSymbol.header] =
                List.append
                  (List.replicate rowCount
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.done ::
                    List.append (symbols.map some)
                      [some MachineCodeSymbol.header]) := by
            simpa [List.map_reverse] using htargetRest
          rw [htargetRest'] at hreturn
          have hsourceLeft :
              List.append
                  ((List.append
                    (List.replicate rowCount
                      MachineCodeSymbol.blank)
                    (MachineCodeSymbol.done :: symbols)).reverse.map
                    some)
                  [none] =
                some current ::
                  List.append (leftSymbols.map some) [none] := by
            change
              List.append (leftNormal.reverse.map some) [none] = _
            rw [hreverse]
            rfl
          exact
            TuringMachine.computes_trans
              (by
                simpa only [finalTransitionMarkConfig, hsourceLeft,
                  List.map]
                  using hreturn)
              (by
                simpa [parsedTransitionHaltConfig,
                  parsedTableLeftRev, markedSuffixCells]
                  using hfinish)

      | cons first rest =>
          have hreturn :=
            transitionListParserMachine_markPosition_returnLeft_toBoundary
              (some first) leftSymbols [] current (rest.map some)
          have hprefix :
              List.append (leftSymbols.map some).reverse [some current] =
                leftNormal.map some := by
            have hmap := congrArg (List.map some) hleft
            simpa [List.map_append, List.map_reverse,
              List.append_assoc]
              using hmap.symm
          have htargetRest :
              List.append (leftSymbols.map some).reverse
                  (some current ::
                    some MachineCodeSymbol.header :: rest.map some) =
                List.append
                  (List.replicate rowCount
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.done ::
                    List.append (symbols.map some)
                      (some MachineCodeSymbol.header ::
                        rest.map some)) := by
            calc
              List.append (leftSymbols.map some).reverse
                  (some current ::
                    some MachineCodeSymbol.header :: rest.map some) =
                List.append
                  (List.append (leftSymbols.map some).reverse
                    [some current])
                  (some MachineCodeSymbol.header ::
                    rest.map some) := by
                  simp [List.append_assoc]
              _ = List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header ::
                      rest.map some) := by
                  rw [hprefix]
              _ = List.append
                    (List.replicate rowCount
                      (some MachineCodeSymbol.blank))
                    (some MachineCodeSymbol.done ::
                      List.append (symbols.map some)
                        (some MachineCodeSymbol.header ::
                          rest.map some)) := by
                  simp [leftNormal, List.map_append,
                    List.map_replicate, List.append_assoc]
          have hfinish :=
            transitionListParserMachine_computes_findCount_blanks_done_exact
              (TransitionListParserMarker.saved (some first))
              rowCount [none]
              (List.append (symbols.map some)
                (some MachineCodeSymbol.header :: rest.map some))
          have htargetRest' :
              List.append (leftSymbols.reverse.map some)
                  (some current ::
                    some MachineCodeSymbol.header :: rest.map some) =
                List.append
                  (List.replicate rowCount
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.done ::
                    List.append (symbols.map some)
                      (some MachineCodeSymbol.header ::
                        rest.map some)) := by
            simpa [List.map_reverse] using htargetRest
          rw [htargetRest'] at hreturn
          have hsourceLeft :
              List.append
                  ((List.append
                    (List.replicate rowCount
                      MachineCodeSymbol.blank)
                    (MachineCodeSymbol.done :: symbols)).reverse.map
                    some)
                  [none] =
                some current ::
                  List.append (leftSymbols.map some) [none] := by
            change
              List.append (leftNormal.reverse.map some) [none] = _
            rw [hreverse]
            rfl
          exact
            TuringMachine.computes_trans
              (by
                simpa only [finalTransitionMarkConfig, hsourceLeft,
                  List.map]
                  using hreturn)
              (by
                simpa [parsedTransitionHaltConfig,
                  parsedTableLeftRev, markedSuffixCells]
                  using hfinish)

end Section53TransitionParserHandoff

end Computability
end FoC
