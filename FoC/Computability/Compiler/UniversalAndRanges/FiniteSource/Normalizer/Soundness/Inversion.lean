import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Soundness.Basic

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

theorem codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck
    {c : TuringMachine.Configuration MachineCodeSymbol
      CodePrefixParserNormalizerState}
    (hnotHalt :
      ¬ TuringMachine.Halted codePrefixParserNormalizerMachine c)
    (hnostep :
      forall d : TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserNormalizerState,
        ¬ TuringMachine.Step codePrefixParserNormalizerMachine c d) :
    ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine c := by
  intro h
  rcases h with ⟨final, hcomp, hhalt⟩
  cases hcomp with
  | refl =>
      exact hnotHalt hhalt
  | step hstep _ =>
      exact hnostep _ hstep

theorem codePrefixParserNormalizerMachine_not_haltsFrom_needTransition_empty
    (leftRev : List (Option MachineCodeSymbol)) :
    ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.needTransition
        tape := transitionListParserOptionTape leftRev [] } := by
  refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
  · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
  · intro d hstep
    cases hstep with
    | mk htransition =>
        simp [codePrefixParserNormalizerMachine,
          transitionListParserOptionTape, Tape.read] at htransition

theorem codePrefixParserNormalizerMachine_not_haltsFrom_needTransition_nonTransition
    {symbol : MachineCodeSymbol}
    (hsymbol : symbol ≠ MachineCodeSymbol.transition)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : List (Option MachineCodeSymbol)) :
    ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape leftRev
            (some symbol :: suffix) } := by
  refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
  · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
  · intro d hstep
    cases hstep with
    | mk htransition =>
        cases symbol <;>
          simp [codePrefixParserNormalizerMachine,
            transitionListParserOptionTape, Tape.read] at hsymbol htransition

theorem codePrefixParserNormalizerMachine_not_haltsFrom_needTransition_none
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape leftRev
            (none :: suffix) } := by
  refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
  · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
  · intro d hstep
    cases hstep with
    | mk htransition =>
        simp [codePrefixParserNormalizerMachine,
          transitionListParserOptionTape, Tape.read] at htransition

theorem codePrefixParserNormalizerMachine_haltsFrom_sourceNat_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.sourceNat
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeNatAppend n suffix ∧
        TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
          { state := CodePrefixParserNormalizerState.readCell
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeNat n).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  induction tokens generalizing leftRev with
  | nil =>
      exact
        False.elim
          ((codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck
              (by simp [TuringMachine.Halted,
                codePrefixParserNormalizerMachine])
              (by
                intro d hstep
                cases hstep with
                | mk htransition =>
                    simp [codePrefixParserNormalizerMachine,
                      transitionListParserOptionTape, Tape.read] at htransition))
            h)
  | cons symbol rest ih =>
      have hstuck
          (hsymbol :
            symbol ≠ MachineCodeSymbol.tick ∧
              symbol ≠ MachineCodeSymbol.done) :
          ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.sourceNat
              tape :=
                transitionListParserOptionTape leftRev
                  ((symbol :: rest).map some) } := by
        refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
        · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
        · intro d hstep
          cases hstep with
          | mk htransition =>
              cases symbol <;>
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read] at hsymbol htransition
      cases symbol with
      | tick =>
        have htail :
            TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
              { state := CodePrefixParserNormalizerState.sourceNat
                tape :=
                  transitionListParserOptionTape
                    (some MachineCodeSymbol.tick :: leftRev)
                    (rest.map some) } :=
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_sourceNat_tick
                leftRev (rest.map some)))
            h
        rcases ih htail with ⟨n, suffix, htokens, hread⟩
        refine ⟨n + 1, suffix, ?_, ?_⟩
        · simp [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat, htokens]
        · simpa [MachineDescription.encodeNat,
            List.append_assoc] using hread
      | done =>
        refine ⟨0, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeNat] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_sourceNat_done
                leftRev (rest.map some)))
            h
      | header =>
        exact False.elim (hstuck (by simp) h)
      | transition =>
        exact False.elim (hstuck (by simp) h)
      | blank =>
        exact False.elim (hstuck (by simp) h)
      | zero =>
        exact False.elim (hstuck (by simp) h)
      | one =>
        exact False.elim (hstuck (by simp) h)
      | moveLeft =>
        exact False.elim (hstuck (by simp) h)
      | moveRight =>
        exact False.elim (hstuck (by simp) h)

theorem codePrefixParserNormalizerMachine_haltsFrom_readCell_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.readCell
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists cell : Option Bool,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeCellAppend cell suffix ∧
        TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
          { state := CodePrefixParserNormalizerState.writeCell
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeCell cell).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  cases tokens with
  | nil =>
      exact False.elim
        ((codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck
            (by simp [TuringMachine.Halted,
              codePrefixParserNormalizerMachine])
            (by
              intro d hstep
              cases hstep with
              | mk htransition =>
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read] at htransition))
          h)
  | cons symbol rest =>
      have hstuck
          (hsymbol :
            symbol ≠ MachineCodeSymbol.blank ∧
              symbol ≠ MachineCodeSymbol.zero ∧
              symbol ≠ MachineCodeSymbol.one) :
          ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.readCell
              tape :=
                transitionListParserOptionTape leftRev
                  ((symbol :: rest).map some) } := by
        refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
        · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
        · intro d hstep
          cases hstep with
          | mk htransition =>
              cases symbol <;>
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read] at hsymbol htransition
      cases symbol with
      | blank =>
        refine ⟨none, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeCell] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_keep_right
                (by simp [codePrefixParserNormalizerMachine,
                  codePrefixParserNormalizerKeep])))
            h
      | zero =>
        refine ⟨some false, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeCell] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_keep_right
                (by simp [codePrefixParserNormalizerMachine,
                  codePrefixParserNormalizerKeep])))
            h
      | one =>
        refine ⟨some true, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeCell] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_keep_right
                (by simp [codePrefixParserNormalizerMachine,
                  codePrefixParserNormalizerKeep])))
            h
      | header =>
        exact False.elim (hstuck (by simp) h)
      | transition =>
        exact False.elim (hstuck (by simp) h)
      | tick =>
        exact False.elim (hstuck (by simp) h)
      | done =>
        exact False.elim (hstuck (by simp) h)
      | moveLeft =>
        exact False.elim (hstuck (by simp) h)
      | moveRight =>
        exact False.elim (hstuck (by simp) h)

theorem codePrefixParserNormalizerMachine_haltsFrom_writeCell_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.writeCell
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists cell : Option Bool,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeCellAppend cell suffix ∧
        TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
          { state := CodePrefixParserNormalizerState.moveField
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeCell cell).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  cases tokens with
  | nil =>
      exact False.elim
        ((codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck
            (by simp [TuringMachine.Halted,
              codePrefixParserNormalizerMachine])
            (by
              intro d hstep
              cases hstep with
              | mk htransition =>
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read] at htransition))
          h)
  | cons symbol rest =>
      have hstuck
          (hsymbol :
            symbol ≠ MachineCodeSymbol.blank ∧
              symbol ≠ MachineCodeSymbol.zero ∧
              symbol ≠ MachineCodeSymbol.one) :
          ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.writeCell
              tape :=
                transitionListParserOptionTape leftRev
                  ((symbol :: rest).map some) } := by
        refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
        · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
        · intro d hstep
          cases hstep with
          | mk htransition =>
              cases symbol <;>
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read] at hsymbol htransition
      cases symbol with
      | blank =>
        refine ⟨none, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeCell] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_keep_right
                (by simp [codePrefixParserNormalizerMachine,
                  codePrefixParserNormalizerKeep])))
            h
      | zero =>
        refine ⟨some false, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeCell] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_keep_right
                (by simp [codePrefixParserNormalizerMachine,
                  codePrefixParserNormalizerKeep])))
            h
      | one =>
        refine ⟨some true, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeCell] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_keep_right
                (by simp [codePrefixParserNormalizerMachine,
                  codePrefixParserNormalizerKeep])))
            h
      | header =>
        exact False.elim (hstuck (by simp) h)
      | transition =>
        exact False.elim (hstuck (by simp) h)
      | tick =>
        exact False.elim (hstuck (by simp) h)
      | done =>
        exact False.elim (hstuck (by simp) h)
      | moveLeft =>
        exact False.elim (hstuck (by simp) h)
      | moveRight =>
        exact False.elim (hstuck (by simp) h)

theorem codePrefixParserNormalizerMachine_haltsFrom_moveField_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.moveField
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists dir : Direction,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeDirectionAppend dir suffix ∧
        TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
          { state := CodePrefixParserNormalizerState.targetNat
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeDirection dir).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  cases tokens with
  | nil =>
      exact False.elim
        ((codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck
            (by simp [TuringMachine.Halted,
              codePrefixParserNormalizerMachine])
            (by
              intro d hstep
              cases hstep with
              | mk htransition =>
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read] at htransition))
          h)
  | cons symbol rest =>
      have hstuck
          (hsymbol :
            symbol ≠ MachineCodeSymbol.moveLeft ∧
              symbol ≠ MachineCodeSymbol.moveRight) :
          ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.moveField
              tape :=
                transitionListParserOptionTape leftRev
                  ((symbol :: rest).map some) } := by
        refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
        · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
        · intro d hstep
          cases hstep with
          | mk htransition =>
              cases symbol <;>
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read] at hsymbol htransition
      cases symbol with
      | moveLeft =>
        refine ⟨Direction.left, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeDirection] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_keep_right
                (by simp [codePrefixParserNormalizerMachine,
                  codePrefixParserNormalizerKeep])))
            h
      | moveRight =>
        refine ⟨Direction.right, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeDirection] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_keep_right
                (by simp [codePrefixParserNormalizerMachine,
                  codePrefixParserNormalizerKeep])))
            h
      | header =>
        exact False.elim (hstuck (by simp) h)
      | transition =>
        exact False.elim (hstuck (by simp) h)
      | tick =>
        exact False.elim (hstuck (by simp) h)
      | done =>
        exact False.elim (hstuck (by simp) h)
      | blank =>
        exact False.elim (hstuck (by simp) h)
      | zero =>
        exact False.elim (hstuck (by simp) h)
      | one =>
        exact False.elim (hstuck (by simp) h)

theorem codePrefixParserNormalizerMachine_haltsFrom_targetNat_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.targetNat
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeNatAppend n suffix ∧
        TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
          { state := CodePrefixParserNormalizerState.markPosition
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeNat n).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  induction tokens generalizing leftRev with
  | nil =>
      exact
        False.elim
          ((codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck
              (by simp [TuringMachine.Halted,
                codePrefixParserNormalizerMachine])
              (by
                intro d hstep
                cases hstep with
                | mk htransition =>
                    simp [codePrefixParserNormalizerMachine,
                      transitionListParserOptionTape, Tape.read] at htransition))
            h)
  | cons symbol rest ih =>
      have hstuck
          (hsymbol :
            symbol ≠ MachineCodeSymbol.tick ∧
              symbol ≠ MachineCodeSymbol.done) :
          ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.targetNat
              tape :=
                transitionListParserOptionTape leftRev
                  ((symbol :: rest).map some) } := by
        refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
        · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
        · intro d hstep
          cases hstep with
          | mk htransition =>
              cases symbol <;>
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read] at hsymbol htransition
      cases symbol with
      | tick =>
        have htail :
            TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
              { state := CodePrefixParserNormalizerState.targetNat
                tape :=
                  transitionListParserOptionTape
                    (some MachineCodeSymbol.tick :: leftRev)
                    (rest.map some) } :=
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_targetNat_tick
                leftRev (rest.map some)))
            h
        rcases ih htail with ⟨n, suffix, htokens, hmark⟩
        refine ⟨n + 1, suffix, ?_, ?_⟩
        · simp [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat, htokens]
        · simpa [MachineDescription.encodeNat,
            List.append_assoc] using hmark
      | done =>
        refine ⟨0, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeNat] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_targetNat_done
                leftRev (rest.map some)))
            h
      | header =>
        exact False.elim (hstuck (by simp) h)
      | transition =>
        exact False.elim (hstuck (by simp) h)
      | blank =>
        exact False.elim (hstuck (by simp) h)
      | zero =>
        exact False.elim (hstuck (by simp) h)
      | one =>
        exact False.elim (hstuck (by simp) h)
      | moveLeft =>
        exact False.elim (hstuck (by simp) h)
      | moveRight =>
        exact False.elim (hstuck (by simp) h)

theorem codePrefixParserNormalizerMachine_haltsFrom_seekCountDone_initial_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state :=
            CodePrefixParserNormalizerState.seekCountDone
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists count : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeNatAppend count suffix ∧
        TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
          { state := CodePrefixParserNormalizerState.needTransition
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeNat count).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  induction tokens generalizing leftRev with
  | nil =>
      exact
        False.elim
          ((codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck
              (by simp [TuringMachine.Halted,
                codePrefixParserNormalizerMachine])
              (by
                intro d hstep
                cases hstep with
                | mk htransition =>
                    simp [codePrefixParserNormalizerMachine,
                      transitionListParserOptionTape, Tape.read] at htransition))
            h)
  | cons symbol rest ih =>
      have hstuck
          (hsymbol :
            symbol ≠ MachineCodeSymbol.tick ∧
              symbol ≠ MachineCodeSymbol.done) :
          ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
            { state :=
                CodePrefixParserNormalizerState.seekCountDone
                  TransitionListParserMarker.initial
              tape :=
                transitionListParserOptionTape leftRev
                  ((symbol :: rest).map some) } := by
        refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
        · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
        · intro d hstep
          cases hstep with
          | mk htransition =>
              cases symbol <;>
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read] at hsymbol htransition
      cases symbol with
      | tick =>
        have htail :
            TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
              { state :=
                  CodePrefixParserNormalizerState.seekCountDone
                    TransitionListParserMarker.initial
                tape :=
                  transitionListParserOptionTape
                    (some MachineCodeSymbol.tick :: leftRev)
                    (rest.map some) } :=
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_seekCountDone_initial_tick
                leftRev (rest.map some)))
            h
        rcases ih htail with ⟨count, suffix, htokens, hneed⟩
        refine ⟨count + 1, suffix, ?_, ?_⟩
        · simp [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat, htokens]
        · simpa [MachineDescription.encodeNat,
            List.append_assoc] using hneed
      | done =>
        refine ⟨0, rest, rfl, ?_⟩
        simpa [MachineDescription.encodeNat] using
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (TuringMachine.computes_of_step
              (codePrefixParserNormalizerMachine_step_seekCountDone_initial_done
                leftRev (rest.map some)))
            h
      | header =>
        exact False.elim (hstuck (by simp) h)
      | transition =>
        exact False.elim (hstuck (by simp) h)
      | blank =>
        exact False.elim (hstuck (by simp) h)
      | zero =>
        exact False.elim (hstuck (by simp) h)
      | one =>
        exact False.elim (hstuck (by simp) h)
      | moveLeft =>
        exact False.elim (hstuck (by simp) h)
      | moveRight =>
        exact False.elim (hstuck (by simp) h)

theorem codePrefixParserNormalizerMachine_haltsFrom_needTransition_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.needTransition
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists t : TransitionDescription,
    exists restTokens : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeTransitionAppend t restTokens ∧
        TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
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
                (restTokens.map some) } := by
  cases tokens with
  | nil =>
      exact False.elim
        ((codePrefixParserNormalizerMachine_not_haltsFrom_needTransition_empty
            leftRev)
          h)
  | cons symbol rest =>
      by_cases hsymbol : symbol = MachineCodeSymbol.transition
      · subst symbol
        have hsourceFrom :
            TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
              { state := CodePrefixParserNormalizerState.sourceNat
                tape :=
                  transitionListParserOptionTape
                    (some MachineCodeSymbol.transition :: leftRev)
                    (rest.map some) } :=
          codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
            (codePrefixParserNormalizerMachine_computes_needTransition
              leftRev rest)
            h
        rcases
            codePrefixParserNormalizerMachine_haltsFrom_sourceNat_inv
              hsourceFrom with
          ⟨source, afterSource, hsourceTokens, hreadFrom⟩
        rcases
            codePrefixParserNormalizerMachine_haltsFrom_readCell_inv
              hreadFrom with
          ⟨read, afterRead, hreadTokens, hwriteFrom⟩
        rcases
            codePrefixParserNormalizerMachine_haltsFrom_writeCell_inv
              hwriteFrom with
          ⟨write, afterWrite, hwriteTokens, hmoveFrom⟩
        rcases
            codePrefixParserNormalizerMachine_haltsFrom_moveField_inv
              hmoveFrom with
          ⟨move, afterMove, hmoveTokens, htargetFrom⟩
        rcases
            codePrefixParserNormalizerMachine_haltsFrom_targetNat_inv
              htargetFrom with
          ⟨target, restTokens, htargetTokens, hmarkFrom⟩
        let t : TransitionDescription :=
          { source := source
            read := read
            write := write
            move := move
            target := target }
        refine ⟨t, restTokens, ?_, ?_⟩
        · simp [t, MachineDescription.encodeTransitionAppend,
            hsourceTokens, hreadTokens, hwriteTokens,
            hmoveTokens, htargetTokens]
        · simpa [t, MachineDescription.encodeTransition,
            MachineDescription.encodeTransitionAppend,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeCellAppend,
            MachineDescription.encodeDirectionAppend,
            List.append_assoc] using hmarkFrom
      · exact False.elim
          ((codePrefixParserNormalizerMachine_not_haltsFrom_needTransition_nonTransition
              hsymbol leftRev (rest.map some))
            h)

end Computability
end FoC
