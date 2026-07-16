import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.Runs
import FoC.Computability.TapeLemmas

set_option doc.verso true

/-!
# Exact transition-list parser endpoints

Exact zero-table and completed-table configurations used to compose the parser
with later finite-machine phases.
-/

namespace FoC
namespace Computability

open Languages

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
          (transitionListParserMarkedTail suffix)) }

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
                  parsedTableLeftRev, transitionListParserMarkedTail]
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
                  parsedTableLeftRev, transitionListParserMarkedTail]
                  using hfinish)

end Computability
end FoC
