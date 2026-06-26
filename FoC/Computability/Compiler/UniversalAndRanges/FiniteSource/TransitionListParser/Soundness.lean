import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.Runs
set_option doc.verso true

/-!
# Transition List Parser Soundness

Soundness proofs showing that accepting parser runs decode exactly the encoded
transition table on the tape.
-/

namespace FoC
namespace Computability

open Languages

theorem transitionListParserMachine_haltsFromIn_sourceNat_inv
    {steps : Nat} {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn transitionListParserMachine steps
        { state := TransitionListParserState.sourceNat
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeNatAppend n suffix ∧
        TuringMachine.HaltsFrom transitionListParserMachine
          { state := TransitionListParserState.readCell
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeNat n).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  induction steps generalizing leftRev tokens with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted, transitionListParserMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases tokens with
          | nil =>
              cases hstep with
              | mk htransition =>
                  simp [transitionListParserMachine,
                    transitionListParserOptionTape, Tape.read] at htransition
          | cons symbol rest =>
              cases symbol <;> try
                (cases hstep with
                | mk htransition =>
                    simp [transitionListParserMachine,
                      transitionListParserOptionTape, Tape.read] at htransition)
              · have hnext :=
                  TuringMachine.step_deterministic
                    (transitionListParserMachine_step_sourceNat_tick
                      leftRev (rest.map some)) hstep
                cases hnext
                have htail :
                    TuringMachine.HaltsFromIn
                      transitionListParserMachine steps
                      { state := TransitionListParserState.sourceNat
                        tape :=
                          transitionListParserOptionTape
                            (some MachineCodeSymbol.tick :: leftRev)
                            (rest.map some) } :=
                  ⟨final, hrest, hhalt⟩
                rcases ih htail with
                  ⟨n, suffix, htokens, hread⟩
                refine ⟨n + 1, suffix, ?_, ?_⟩
                · simp [MachineDescription.encodeNatAppend,
                    MachineDescription.encodeNat, htokens]
                · simpa [MachineDescription.encodeNat,
                    List.append_assoc] using hread
              · have hnext :=
                  TuringMachine.step_deterministic
                    (transitionListParserMachine_step_sourceNat_done
                      leftRev (rest.map some)) hstep
                cases hnext
                refine ⟨0, rest, ?_, ?_⟩
                · rfl
                · simpa [MachineDescription.encodeNat] using
                    (TuringMachine.halts_from_in_to_halts_from
                      (M := transitionListParserMachine)
                      ⟨final, hrest, hhalt⟩)

theorem transitionListParserMachine_haltsFrom_sourceNat_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.sourceNat
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeNatAppend n suffix ∧
        TuringMachine.HaltsFrom transitionListParserMachine
          { state := TransitionListParserState.readCell
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeNat n).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  rcases TuringMachine.halts_from_to_halts_from_in h with
    ⟨steps, hsteps⟩
  exact transitionListParserMachine_haltsFromIn_sourceNat_inv hsteps

theorem transitionListParserMachine_haltsFromIn_readCell_inv
    {steps : Nat} {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn transitionListParserMachine steps
        { state := TransitionListParserState.readCell
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists cell : Option Bool,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeCellAppend cell suffix ∧
        TuringMachine.HaltsFrom transitionListParserMachine
          { state := TransitionListParserState.writeCell
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeCell cell).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  cases steps with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted, transitionListParserMachine] at hhalt
  | succ steps =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases tokens with
          | nil =>
              cases hstep with
              | mk htransition =>
                  simp [transitionListParserMachine,
                    transitionListParserOptionTape, Tape.read] at htransition
          | cons symbol rest =>
              cases symbol with
              | blank =>
                  have hknown :
                      TuringMachine.Step transitionListParserMachine
                        { state := TransitionListParserState.readCell
                          tape :=
                            transitionListParserOptionTape leftRev
                              (some MachineCodeSymbol.blank ::
                                rest.map some) }
                        { state := TransitionListParserState.writeCell
                          tape :=
                            transitionListParserOptionTape
                              (some MachineCodeSymbol.blank :: leftRev)
                              (rest.map some) } :=
                    transitionListParserMachine_step_keep_right
                      (by simp [transitionListParserMachine,
                        transitionListParserKeep])
                  have hnext :=
                    TuringMachine.step_deterministic hknown hstep
                  cases hnext
                  refine ⟨none, rest, rfl, ?_⟩
                  simpa [MachineDescription.encodeCell] using
                    (TuringMachine.halts_from_in_to_halts_from
                      (M := transitionListParserMachine)
                      ⟨final, hrest, hhalt⟩)
              | zero =>
                  have hknown :
                      TuringMachine.Step transitionListParserMachine
                        { state := TransitionListParserState.readCell
                          tape :=
                            transitionListParserOptionTape leftRev
                              (some MachineCodeSymbol.zero ::
                                rest.map some) }
                        { state := TransitionListParserState.writeCell
                          tape :=
                            transitionListParserOptionTape
                              (some MachineCodeSymbol.zero :: leftRev)
                              (rest.map some) } :=
                    transitionListParserMachine_step_keep_right
                      (by simp [transitionListParserMachine,
                        transitionListParserKeep])
                  have hnext :=
                    TuringMachine.step_deterministic hknown hstep
                  cases hnext
                  refine ⟨some false, rest, rfl, ?_⟩
                  simpa [MachineDescription.encodeCell] using
                    (TuringMachine.halts_from_in_to_halts_from
                      (M := transitionListParserMachine)
                      ⟨final, hrest, hhalt⟩)
              | one =>
                  have hknown :
                      TuringMachine.Step transitionListParserMachine
                        { state := TransitionListParserState.readCell
                          tape :=
                            transitionListParserOptionTape leftRev
                              (some MachineCodeSymbol.one ::
                                rest.map some) }
                        { state := TransitionListParserState.writeCell
                          tape :=
                            transitionListParserOptionTape
                              (some MachineCodeSymbol.one :: leftRev)
                              (rest.map some) } :=
                    transitionListParserMachine_step_keep_right
                      (by simp [transitionListParserMachine,
                        transitionListParserKeep])
                  have hnext :=
                    TuringMachine.step_deterministic hknown hstep
                  cases hnext
                  refine ⟨some true, rest, rfl, ?_⟩
                  simpa [MachineDescription.encodeCell] using
                    (TuringMachine.halts_from_in_to_halts_from
                      (M := transitionListParserMachine)
                      ⟨final, hrest, hhalt⟩)
              | header =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | transition =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | tick =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | done =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | moveLeft =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | moveRight =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition

theorem transitionListParserMachine_haltsFrom_readCell_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.readCell
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists cell : Option Bool,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeCellAppend cell suffix ∧
        TuringMachine.HaltsFrom transitionListParserMachine
          { state := TransitionListParserState.writeCell
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeCell cell).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  rcases TuringMachine.halts_from_to_halts_from_in h with
    ⟨steps, hsteps⟩
  exact transitionListParserMachine_haltsFromIn_readCell_inv hsteps

theorem transitionListParserMachine_haltsFromIn_writeCell_inv
    {steps : Nat} {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn transitionListParserMachine steps
        { state := TransitionListParserState.writeCell
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists cell : Option Bool,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeCellAppend cell suffix ∧
        TuringMachine.HaltsFrom transitionListParserMachine
          { state := TransitionListParserState.moveField
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeCell cell).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  cases steps with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted, transitionListParserMachine] at hhalt
  | succ steps =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases tokens with
          | nil =>
              cases hstep with
              | mk htransition =>
                  simp [transitionListParserMachine,
                    transitionListParserOptionTape, Tape.read] at htransition
          | cons symbol rest =>
              cases symbol with
              | blank =>
                  have hknown :
                      TuringMachine.Step transitionListParserMachine
                        { state := TransitionListParserState.writeCell
                          tape :=
                            transitionListParserOptionTape leftRev
                              (some MachineCodeSymbol.blank ::
                                rest.map some) }
                        { state := TransitionListParserState.moveField
                          tape :=
                            transitionListParserOptionTape
                              (some MachineCodeSymbol.blank :: leftRev)
                              (rest.map some) } :=
                    transitionListParserMachine_step_keep_right
                      (by simp [transitionListParserMachine,
                        transitionListParserKeep])
                  have hnext :=
                    TuringMachine.step_deterministic hknown hstep
                  cases hnext
                  refine ⟨none, rest, rfl, ?_⟩
                  simpa [MachineDescription.encodeCell] using
                    (TuringMachine.halts_from_in_to_halts_from
                      (M := transitionListParserMachine)
                      ⟨final, hrest, hhalt⟩)
              | zero =>
                  have hknown :
                      TuringMachine.Step transitionListParserMachine
                        { state := TransitionListParserState.writeCell
                          tape :=
                            transitionListParserOptionTape leftRev
                              (some MachineCodeSymbol.zero ::
                                rest.map some) }
                        { state := TransitionListParserState.moveField
                          tape :=
                            transitionListParserOptionTape
                              (some MachineCodeSymbol.zero :: leftRev)
                              (rest.map some) } :=
                    transitionListParserMachine_step_keep_right
                      (by simp [transitionListParserMachine,
                        transitionListParserKeep])
                  have hnext :=
                    TuringMachine.step_deterministic hknown hstep
                  cases hnext
                  refine ⟨some false, rest, rfl, ?_⟩
                  simpa [MachineDescription.encodeCell] using
                    (TuringMachine.halts_from_in_to_halts_from
                      (M := transitionListParserMachine)
                      ⟨final, hrest, hhalt⟩)
              | one =>
                  have hknown :
                      TuringMachine.Step transitionListParserMachine
                        { state := TransitionListParserState.writeCell
                          tape :=
                            transitionListParserOptionTape leftRev
                              (some MachineCodeSymbol.one ::
                                rest.map some) }
                        { state := TransitionListParserState.moveField
                          tape :=
                            transitionListParserOptionTape
                              (some MachineCodeSymbol.one :: leftRev)
                              (rest.map some) } :=
                    transitionListParserMachine_step_keep_right
                      (by simp [transitionListParserMachine,
                        transitionListParserKeep])
                  have hnext :=
                    TuringMachine.step_deterministic hknown hstep
                  cases hnext
                  refine ⟨some true, rest, rfl, ?_⟩
                  simpa [MachineDescription.encodeCell] using
                    (TuringMachine.halts_from_in_to_halts_from
                      (M := transitionListParserMachine)
                      ⟨final, hrest, hhalt⟩)
              | header =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | transition =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | tick =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | done =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | moveLeft =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | moveRight =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition

theorem transitionListParserMachine_haltsFrom_writeCell_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.writeCell
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists cell : Option Bool,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeCellAppend cell suffix ∧
        TuringMachine.HaltsFrom transitionListParserMachine
          { state := TransitionListParserState.moveField
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeCell cell).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  rcases TuringMachine.halts_from_to_halts_from_in h with
    ⟨steps, hsteps⟩
  exact transitionListParserMachine_haltsFromIn_writeCell_inv hsteps

theorem transitionListParserMachine_haltsFromIn_moveField_inv
    {steps : Nat} {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn transitionListParserMachine steps
        { state := TransitionListParserState.moveField
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists dir : Direction,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeDirectionAppend dir suffix ∧
        TuringMachine.HaltsFrom transitionListParserMachine
          { state := TransitionListParserState.targetNat
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeDirection dir).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  cases steps with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted, transitionListParserMachine] at hhalt
  | succ steps =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases tokens with
          | nil =>
              cases hstep with
              | mk htransition =>
                  simp [transitionListParserMachine,
                    transitionListParserOptionTape, Tape.read] at htransition
          | cons symbol rest =>
              cases symbol with
              | moveLeft =>
                  have hknown :
                      TuringMachine.Step transitionListParserMachine
                        { state := TransitionListParserState.moveField
                          tape :=
                            transitionListParserOptionTape leftRev
                              (some MachineCodeSymbol.moveLeft ::
                                rest.map some) }
                        { state := TransitionListParserState.targetNat
                          tape :=
                            transitionListParserOptionTape
                              (some MachineCodeSymbol.moveLeft :: leftRev)
                              (rest.map some) } :=
                    transitionListParserMachine_step_keep_right
                      (by simp [transitionListParserMachine,
                        transitionListParserKeep])
                  have hnext :=
                    TuringMachine.step_deterministic hknown hstep
                  cases hnext
                  refine ⟨Direction.left, rest, rfl, ?_⟩
                  simpa [MachineDescription.encodeDirection] using
                    (TuringMachine.halts_from_in_to_halts_from
                      (M := transitionListParserMachine)
                      ⟨final, hrest, hhalt⟩)
              | moveRight =>
                  have hknown :
                      TuringMachine.Step transitionListParserMachine
                        { state := TransitionListParserState.moveField
                          tape :=
                            transitionListParserOptionTape leftRev
                              (some MachineCodeSymbol.moveRight ::
                                rest.map some) }
                        { state := TransitionListParserState.targetNat
                          tape :=
                            transitionListParserOptionTape
                              (some MachineCodeSymbol.moveRight :: leftRev)
                              (rest.map some) } :=
                    transitionListParserMachine_step_keep_right
                      (by simp [transitionListParserMachine,
                        transitionListParserKeep])
                  have hnext :=
                    TuringMachine.step_deterministic hknown hstep
                  cases hnext
                  refine ⟨Direction.right, rest, rfl, ?_⟩
                  simpa [MachineDescription.encodeDirection] using
                    (TuringMachine.halts_from_in_to_halts_from
                      (M := transitionListParserMachine)
                      ⟨final, hrest, hhalt⟩)
              | header =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | transition =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | tick =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | done =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | blank =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | zero =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition
              | one =>
                  cases hstep with
                  | mk htransition =>
                      simp [transitionListParserMachine,
                        transitionListParserOptionTape, Tape.read] at htransition

theorem transitionListParserMachine_haltsFrom_moveField_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.moveField
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists dir : Direction,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeDirectionAppend dir suffix ∧
        TuringMachine.HaltsFrom transitionListParserMachine
          { state := TransitionListParserState.targetNat
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeDirection dir).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  rcases TuringMachine.halts_from_to_halts_from_in h with
    ⟨steps, hsteps⟩
  exact transitionListParserMachine_haltsFromIn_moveField_inv hsteps

theorem transitionListParserMachine_haltsFromIn_targetNat_inv
    {steps : Nat} {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn transitionListParserMachine steps
        { state := TransitionListParserState.targetNat
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeNatAppend n suffix ∧
        TuringMachine.HaltsFrom transitionListParserMachine
          { state := TransitionListParserState.markPosition
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeNat n).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  induction steps generalizing leftRev tokens with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted, transitionListParserMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases tokens with
          | nil =>
              cases hstep with
              | mk htransition =>
                  simp [transitionListParserMachine,
                    transitionListParserOptionTape, Tape.read] at htransition
          | cons symbol rest =>
              cases symbol <;> try
                (cases hstep with
                | mk htransition =>
                    simp [transitionListParserMachine,
                      transitionListParserOptionTape, Tape.read] at htransition)
              · have hnext :=
                  TuringMachine.step_deterministic
                    (transitionListParserMachine_step_targetNat_tick
                      leftRev (rest.map some)) hstep
                cases hnext
                have htail :
                    TuringMachine.HaltsFromIn
                      transitionListParserMachine steps
                      { state := TransitionListParserState.targetNat
                        tape :=
                          transitionListParserOptionTape
                            (some MachineCodeSymbol.tick :: leftRev)
                            (rest.map some) } :=
                  ⟨final, hrest, hhalt⟩
                rcases ih htail with
                  ⟨n, suffix, htokens, hmark⟩
                refine ⟨n + 1, suffix, ?_, ?_⟩
                · simp [MachineDescription.encodeNatAppend,
                    MachineDescription.encodeNat, htokens]
                · simpa [MachineDescription.encodeNat,
                    List.append_assoc] using hmark
              · have hnext :=
                  TuringMachine.step_deterministic
                    (transitionListParserMachine_step_targetNat_done
                      leftRev (rest.map some)) hstep
                cases hnext
                refine ⟨0, rest, ?_, ?_⟩
                · rfl
                · simpa [MachineDescription.encodeNat] using
                    (TuringMachine.halts_from_in_to_halts_from
                      (M := transitionListParserMachine)
                      ⟨final, hrest, hhalt⟩)

theorem transitionListParserMachine_haltsFrom_targetNat_inv
    {leftRev : List (Option MachineCodeSymbol)}
    {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.targetNat
          tape :=
            transitionListParserOptionTape leftRev
              (tokens.map some) }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeNatAppend n suffix ∧
        TuringMachine.HaltsFrom transitionListParserMachine
          { state := TransitionListParserState.markPosition
            tape :=
              transitionListParserOptionTape
                (List.append
                  ((MachineDescription.encodeNat n).reverse.map some)
                  leftRev)
                (suffix.map some) } := by
  rcases TuringMachine.halts_from_to_halts_from_in h with
    ⟨steps, hsteps⟩
  exact transitionListParserMachine_haltsFromIn_targetNat_inv hsteps

def transitionListParserMarkedContextLeft
    (boundary : Bool) (blanks count : Nat)
    (pre : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  List.append
    ((List.append
      (List.append
        (List.replicate blanks MachineCodeSymbol.blank)
        (MachineDescription.encodeNat count))
      pre).reverse.map some)
    (if boundary then [none] else [])

theorem transitionListParserMachine_computes_markPosition_context_to_needTransition
    (boundary : Bool) (blanks count : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (symbol : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (transitionListParserMarkedContextLeft
              boundary blanks (count + 1) pre)
            ((symbol :: suffix).map some) }
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape
            (transitionListParserMarkedContextLeft
              true (blanks + 1) count pre)
            ((symbol :: suffix).map some) } := by
  let leftNormal : Word MachineCodeSymbol :=
    List.append
      (List.append
        (List.replicate blanks MachineCodeSymbol.blank)
        (MachineDescription.encodeNat (count + 1)))
      pre
  let countLeft : List (Option MachineCodeSymbol) :=
    List.append
      ((MachineDescription.encodeNat count).reverse.map some)
      (List.append
        (List.replicate (blanks + 1) (some MachineCodeSymbol.blank))
        [none])
  have hrevNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal, MachineDescription.encodeNat]
  cases hrev : leftNormal.reverse with
  | nil =>
      exact False.elim (hrevNonempty hrev)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa using h
      have hprefix :
          List.append (List.map some leftSymbols).reverse
              [some current] =
            leftNormal.map some := by
        have hmap :=
          congrArg (fun xs : List MachineCodeSymbol => xs.map some)
            hleft
        simpa [List.map_append, List.map_reverse,
          List.append_assoc] using hmap.symm
      have hleftStartNoBoundary :
          transitionListParserMarkedContextLeft
            false blanks (count + 1) pre =
            some current :: leftSymbols.map some := by
        have hmapRev :
            leftNormal.reverse.map some =
              some current :: leftSymbols.map some := by
          simp [hrev]
        simpa [transitionListParserMarkedContextLeft,
          leftNormal, List.reverse_append, List.map_append,
          List.map_reverse, List.map_replicate, List.append_assoc] using
          hmapRev
      have hleftStartBoundary :
          transitionListParserMarkedContextLeft
            true blanks (count + 1) pre =
            some current ::
              List.append (leftSymbols.map some) [none] := by
        have hmapRev :
            List.append (leftNormal.reverse.map some) [none] =
              some current :: List.append (leftSymbols.map some) [none] := by
          simp [hrev]
        simpa [transitionListParserMarkedContextLeft,
          leftNormal, List.reverse_append, List.map_append,
          List.map_reverse, List.map_replicate, List.append_assoc] using
          hmapRev
      have hreturn :
          TuringMachine.Computes transitionListParserMachine
            { state := TransitionListParserState.markPosition
              tape :=
                transitionListParserOptionTape
                  (transitionListParserMarkedContextLeft
                    boundary blanks (count + 1) pre)
                  (some symbol :: suffix.map some) }
            { state :=
                TransitionListParserState.findCount
                  (TransitionListParserMarker.saved (some symbol))
              tape :=
                transitionListParserOptionTape [none]
                  (List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header ::
                      suffix.map some)) } := by
        cases boundary
        · have hreturnNoBoundary :=
            transitionListParserMachine_markPosition_returnLeft_noBoundary
              (some symbol) leftSymbols current (suffix.map some)
          have htargetRest :
              List.append (List.map some leftSymbols).reverse
                  (some current ::
                    some MachineCodeSymbol.header ::
                      suffix.map some) =
                List.append (leftNormal.map some)
                  (some MachineCodeSymbol.header ::
                    suffix.map some) := by
            calc
              List.append (List.map some leftSymbols).reverse
                  (some current ::
                    some MachineCodeSymbol.header ::
                      suffix.map some)
                  =
                List.append
                  (List.append (List.map some leftSymbols).reverse
                    [some current])
                  (some MachineCodeSymbol.header ::
                    suffix.map some) := by
                    simp [List.append_assoc]
              _ =
                List.append (leftNormal.map some)
                  (some MachineCodeSymbol.header ::
                    suffix.map some) := by
                    rw [hprefix]
          exact
            by
              rw [← htargetRest]
              rw [hleftStartNoBoundary]
              simpa [List.map_reverse] using hreturnNoBoundary
        · have hreturnBoundary :=
            transitionListParserMachine_markPosition_returnLeft_toBoundary
              (some symbol) leftSymbols [] current (suffix.map some)
          have htargetRest :
              List.append (List.map some leftSymbols).reverse
                  (some current ::
                    some MachineCodeSymbol.header ::
                      suffix.map some) =
                List.append (leftNormal.map some)
                  (some MachineCodeSymbol.header ::
                    suffix.map some) := by
            calc
              List.append (List.map some leftSymbols).reverse
                  (some current ::
                    some MachineCodeSymbol.header ::
                      suffix.map some)
                  =
                List.append
                  (List.append (List.map some leftSymbols).reverse
                    [some current])
                  (some MachineCodeSymbol.header ::
                    suffix.map some) := by
                    simp [List.append_assoc]
              _ =
                List.append (leftNormal.map some)
                  (some MachineCodeSymbol.header ::
                    suffix.map some) := by
                    rw [hprefix]
          exact
            by
              rw [← htargetRest]
              rw [hleftStartBoundary]
              simpa [List.map_reverse] using hreturnBoundary
      have hfind :=
        transitionListParserMachine_computes_findCount_blanks
          (TransitionListParserMarker.saved (some symbol))
          blanks [none]
          (some MachineCodeSymbol.tick ::
            List.append
              ((MachineDescription.encodeNat count).map some)
              (List.append (pre.map some)
                (some MachineCodeSymbol.header :: suffix.map some)))
      have htick :
          TuringMachine.Step transitionListParserMachine
            { state :=
                TransitionListParserState.findCount
                  (TransitionListParserMarker.saved (some symbol))
              tape :=
                transitionListParserOptionTape
                  (List.append
                    (List.replicate blanks
                      (some MachineCodeSymbol.blank))
                    [none])
                  (some MachineCodeSymbol.tick ::
                    List.append
                      ((MachineDescription.encodeNat count).map some)
                      (List.append (pre.map some)
                        (some MachineCodeSymbol.header ::
                          suffix.map some))) }
            { state :=
                TransitionListParserState.seekCountDone
                  (TransitionListParserMarker.saved (some symbol))
              tape :=
                transitionListParserOptionTape
                  (some MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      [none])
                  (List.append
                    ((MachineDescription.encodeNat count).map some)
                    (List.append (pre.map some)
                      (some MachineCodeSymbol.header ::
                        suffix.map some))) } :=
        transitionListParserMachine_step_findCount_tick
          (TransitionListParserMarker.saved (some symbol))
          (List.append
            (List.replicate blanks (some MachineCodeSymbol.blank))
            [none])
          (List.append
            ((MachineDescription.encodeNat count).map some)
            (List.append (pre.map some)
              (some MachineCodeSymbol.header :: suffix.map some)))
      have hseek :=
        transitionListParserMachine_computes_seekCountDone_saved
          (some symbol)
          (some MachineCodeSymbol.blank ::
            List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              [none])
          count
          (List.append pre
            (MachineCodeSymbol.header :: suffix))
      have hmarker :=
        transitionListParserMachine_computes_seekMarker_prefix
          (some symbol) pre
          (MachineCodeSymbol.header :: suffix)
          hpre
          countLeft
      let scanLeft : List (Option MachineCodeSymbol) :=
        List.append (pre.reverse.map some) countLeft
      have hscanNonempty : scanLeft ≠ [] := by
        simp [scanLeft, countLeft]
      cases hscan : scanLeft with
      | nil =>
          exact False.elim (hscanNonempty hscan)
      | cons leftHead leftTail =>
          have hheader :
              TuringMachine.Step transitionListParserMachine
                { state :=
                    TransitionListParserState.seekMarker
                      (some symbol)
                  tape :=
                    transitionListParserOptionTape scanLeft
                      (some MachineCodeSymbol.header ::
                        suffix.map some) }
                { state := TransitionListParserState.enterMarkedPosition
                  tape :=
                    transitionListParserOptionTape leftTail
                      (leftHead :: some symbol ::
                        suffix.map some) } := by
            simpa [hscan] using
              transitionListParserMachine_step_seekMarker_header
                (some symbol) leftTail (suffix.map some) leftHead
          have henter :
              TuringMachine.Step transitionListParserMachine
                { state := TransitionListParserState.enterMarkedPosition
                  tape :=
                    transitionListParserOptionTape leftTail
                      (leftHead :: some symbol ::
                        suffix.map some) }
                { state := TransitionListParserState.needTransition
                  tape :=
                    transitionListParserOptionTape scanLeft
                      (some symbol :: suffix.map some) } := by
            simpa [hscan] using
              transitionListParserMachine_step_enterMarkedPosition
                leftTail (some symbol :: suffix.map some) leftHead
          have hleftDone :
              scanLeft =
                transitionListParserMarkedContextLeft
                  true (blanks + 1) count pre := by
            have hblank :=
              transitionListParser_blank_cons_replicate_append_none
                blanks
            simp [scanLeft, countLeft,
              transitionListParserMarkedContextLeft,
              List.map_append, List.map_reverse,
              List.map_replicate, List.reverse_append,
              List.replicate_succ, List.append_assoc]
            exact hblank
          have hreturnRest :
              List.append (leftNormal.map some)
                  (some MachineCodeSymbol.header ::
                    suffix.map some) =
                List.append
                  (List.replicate blanks
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.tick ::
                    List.append
                      ((MachineDescription.encodeNat count).map some)
                      (List.append (pre.map some)
                        (some MachineCodeSymbol.header ::
                          suffix.map some))) := by
            simp [leftNormal, MachineDescription.encodeNat,
              List.map_append, List.map_replicate,
              List.append_assoc]
          exact
            TuringMachine.computes_trans hreturn
              (TuringMachine.computes_trans
                (by
                  change
                    TuringMachine.Computes transitionListParserMachine
                      { state :=
                          TransitionListParserState.findCount
                            (TransitionListParserMarker.saved
                              (some symbol))
                        tape :=
                          transitionListParserOptionTape [none]
                            (List.append (leftNormal.map some)
                              (some MachineCodeSymbol.header ::
                                suffix.map some)) }
                      { state :=
                          TransitionListParserState.findCount
                            (TransitionListParserMarker.saved
                              (some symbol))
                        tape :=
                          transitionListParserOptionTape
                            (List.append
                              (List.replicate blanks
                                (some MachineCodeSymbol.blank))
                              [none])
                            (some MachineCodeSymbol.tick ::
                              List.append
                                ((MachineDescription.encodeNat count).map
                                  some)
                                (List.append (pre.map some)
                                  (some MachineCodeSymbol.header ::
                                    suffix.map some))) }
                  rw [hreturnRest]
                  exact hfind)
                (TuringMachine.Computes.step htick
                  (TuringMachine.computes_trans
                    (by
                      simpa [MachineDescription.encodeNatAppend,
                        List.map_append, List.append_assoc] using hseek)
                    (TuringMachine.computes_trans
                      (by
                        simpa [scanLeft, countLeft, List.map_append,
                          List.map_reverse, List.append_assoc] using
                          hmarker)
                      (TuringMachine.Computes.step hheader
                        (TuringMachine.Computes.step henter
                          (by
                            rw [hleftDone]
                            exact TuringMachine.Computes.refl _)))))))

theorem transitionListParserMachine_computes_markPosition_context_empty_to_needTransition
    (boundary : Bool) (blanks count : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre) :
    TuringMachine.Computes transitionListParserMachine
      { state := TransitionListParserState.markPosition
        tape :=
          transitionListParserOptionTape
            (transitionListParserMarkedContextLeft
              boundary blanks (count + 1) pre)
            [] }
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape
            (transitionListParserMarkedContextLeft
              true (blanks + 1) count pre)
            [none] } := by
  let leftNormal : Word MachineCodeSymbol :=
    List.append
      (List.append
        (List.replicate blanks MachineCodeSymbol.blank)
        (MachineDescription.encodeNat (count + 1)))
      pre
  let countLeft : List (Option MachineCodeSymbol) :=
    List.append
      ((MachineDescription.encodeNat count).reverse.map some)
      (List.append
        (List.replicate (blanks + 1) (some MachineCodeSymbol.blank))
        [none])
  have hrevNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal, MachineDescription.encodeNat]
  cases hrev : leftNormal.reverse with
  | nil =>
      exact False.elim (hrevNonempty hrev)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa using h
      have hprefix :
          List.append (List.map some leftSymbols).reverse
              [some current] =
            leftNormal.map some := by
        have hmap :=
          congrArg (fun xs : List MachineCodeSymbol => xs.map some)
            hleft
        simpa [List.map_append, List.map_reverse,
          List.append_assoc] using hmap.symm
      have hleftStartNoBoundary :
          transitionListParserMarkedContextLeft
            false blanks (count + 1) pre =
            some current :: leftSymbols.map some := by
        have hmapRev :
            leftNormal.reverse.map some =
              some current :: leftSymbols.map some := by
          simp [hrev]
        simpa [transitionListParserMarkedContextLeft,
          leftNormal, List.reverse_append, List.map_append,
          List.map_reverse, List.map_replicate, List.append_assoc] using
          hmapRev
      have hleftStartBoundary :
          transitionListParserMarkedContextLeft
            true blanks (count + 1) pre =
            some current ::
              List.append (leftSymbols.map some) [none] := by
        have hmapRev :
            List.append (leftNormal.reverse.map some) [none] =
              some current :: List.append (leftSymbols.map some) [none] := by
          simp [hrev]
        simpa [transitionListParserMarkedContextLeft,
          leftNormal, List.reverse_append, List.map_append,
          List.map_reverse, List.map_replicate, List.append_assoc] using
          hmapRev
      have hreturn :
          TuringMachine.Computes transitionListParserMachine
            { state := TransitionListParserState.markPosition
              tape :=
                transitionListParserOptionTape
                  (transitionListParserMarkedContextLeft
                    boundary blanks (count + 1) pre)
                  [] }
            { state :=
                TransitionListParserState.findCount
                  (TransitionListParserMarker.saved none)
              tape :=
                transitionListParserOptionTape [none]
                  (List.append (leftNormal.map some)
                    [some MachineCodeSymbol.header]) } := by
        cases boundary
        · have hreturnNoBoundary :=
            transitionListParserMachine_markPosition_empty_returnLeft_noBoundary
              leftSymbols current
          have htargetRest :
              List.append (List.map some leftSymbols).reverse
                  [some current, some MachineCodeSymbol.header] =
                List.append (leftNormal.map some)
                  [some MachineCodeSymbol.header] := by
            calc
              List.append (List.map some leftSymbols).reverse
                  [some current, some MachineCodeSymbol.header]
                  =
                List.append
                  (List.append (List.map some leftSymbols).reverse
                    [some current])
                  [some MachineCodeSymbol.header] := by
                    simp [List.append_assoc]
              _ =
                List.append (leftNormal.map some)
                  [some MachineCodeSymbol.header] := by
                    rw [hprefix]
          exact
            by
              rw [← htargetRest]
              rw [hleftStartNoBoundary]
              simpa [List.map_reverse] using hreturnNoBoundary
        · have hreturnBoundary :=
            transitionListParserMachine_markPosition_empty_returnLeft_toBoundary
              leftSymbols [] current
          have htargetRest :
              List.append (List.map some leftSymbols).reverse
                  [some current, some MachineCodeSymbol.header] =
                List.append (leftNormal.map some)
                  [some MachineCodeSymbol.header] := by
            calc
              List.append (List.map some leftSymbols).reverse
                  [some current, some MachineCodeSymbol.header]
                  =
                List.append
                  (List.append (List.map some leftSymbols).reverse
                    [some current])
                  [some MachineCodeSymbol.header] := by
                    simp [List.append_assoc]
              _ =
                List.append (leftNormal.map some)
                  [some MachineCodeSymbol.header] := by
                    rw [hprefix]
          exact
            by
              rw [← htargetRest]
              rw [hleftStartBoundary]
              simpa [List.map_reverse] using hreturnBoundary
      have hfind :=
        transitionListParserMachine_computes_findCount_blanks
          (TransitionListParserMarker.saved none)
          blanks [none]
          (some MachineCodeSymbol.tick ::
            List.append
              ((MachineDescription.encodeNat count).map some)
              (List.append (pre.map some)
                [some MachineCodeSymbol.header]))
      have htick :
          TuringMachine.Step transitionListParserMachine
            { state :=
                TransitionListParserState.findCount
                  (TransitionListParserMarker.saved none)
              tape :=
                transitionListParserOptionTape
                  (List.append
                    (List.replicate blanks
                      (some MachineCodeSymbol.blank))
                    [none])
                  (some MachineCodeSymbol.tick ::
                    List.append
                      ((MachineDescription.encodeNat count).map some)
                      (List.append (pre.map some)
                        [some MachineCodeSymbol.header])) }
            { state :=
                TransitionListParserState.seekCountDone
                  (TransitionListParserMarker.saved none)
              tape :=
                transitionListParserOptionTape
                  (some MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      [none])
                  (List.append
                    ((MachineDescription.encodeNat count).map some)
                    (List.append (pre.map some)
                      [some MachineCodeSymbol.header])) } :=
        transitionListParserMachine_step_findCount_tick
          (TransitionListParserMarker.saved none)
          (List.append
            (List.replicate blanks (some MachineCodeSymbol.blank))
            [none])
          (List.append
            ((MachineDescription.encodeNat count).map some)
            (List.append (pre.map some)
              [some MachineCodeSymbol.header]))
      have hseek :=
        transitionListParserMachine_computes_seekCountDone_saved
          none
          (some MachineCodeSymbol.blank ::
            List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              [none])
          count
          (List.append pre [MachineCodeSymbol.header])
      have hmarker :=
        transitionListParserMachine_computes_seekMarker_prefix
          none pre [MachineCodeSymbol.header] hpre countLeft
      let scanLeft : List (Option MachineCodeSymbol) :=
        List.append (pre.reverse.map some) countLeft
      have hscanNonempty : scanLeft ≠ [] := by
        simp [scanLeft, countLeft]
      cases hscan : scanLeft with
      | nil =>
          exact False.elim (hscanNonempty hscan)
      | cons leftHead leftTail =>
          have hheader :
              TuringMachine.Step transitionListParserMachine
                { state := TransitionListParserState.seekMarker none
                  tape :=
                    transitionListParserOptionTape scanLeft
                      [some MachineCodeSymbol.header] }
                { state := TransitionListParserState.enterMarkedPosition
                  tape :=
                    transitionListParserOptionTape leftTail
                      [leftHead, none] } := by
            simpa [hscan] using
              transitionListParserMachine_step_seekMarker_header
                none leftTail [] leftHead
          have henter :
              TuringMachine.Step transitionListParserMachine
                { state := TransitionListParserState.enterMarkedPosition
                  tape :=
                    transitionListParserOptionTape leftTail
                      [leftHead, none] }
                { state := TransitionListParserState.needTransition
                  tape :=
                    transitionListParserOptionTape scanLeft [none] } := by
            simpa [hscan] using
              transitionListParserMachine_step_enterMarkedPosition
                leftTail [none] leftHead
          have hleftDone :
              scanLeft =
                transitionListParserMarkedContextLeft
                  true (blanks + 1) count pre := by
            have hblank :=
              transitionListParser_blank_cons_replicate_append_none
                blanks
            simp [scanLeft, countLeft,
              transitionListParserMarkedContextLeft,
              List.map_append, List.map_reverse,
              List.map_replicate, List.reverse_append,
              List.replicate_succ, List.append_assoc]
            exact hblank
          have hreturnRest :
              List.append (leftNormal.map some)
                  [some MachineCodeSymbol.header] =
                List.append
                  (List.replicate blanks
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.tick ::
                    List.append
                      ((MachineDescription.encodeNat count).map some)
                      (List.append (pre.map some)
                        [some MachineCodeSymbol.header])) := by
            simp [leftNormal, MachineDescription.encodeNat,
              List.map_append, List.map_replicate,
              List.append_assoc]
          exact
            TuringMachine.computes_trans hreturn
              (TuringMachine.computes_trans
                (by
                  change
                    TuringMachine.Computes transitionListParserMachine
                      { state :=
                          TransitionListParserState.findCount
                            (TransitionListParserMarker.saved none)
                        tape :=
                          transitionListParserOptionTape [none]
                            (List.append (leftNormal.map some)
                              [some MachineCodeSymbol.header]) }
                      { state :=
                          TransitionListParserState.findCount
                            (TransitionListParserMarker.saved none)
                        tape :=
                          transitionListParserOptionTape
                            (List.append
                              (List.replicate blanks
                                (some MachineCodeSymbol.blank))
                              [none])
                            (some MachineCodeSymbol.tick ::
                              List.append
                                ((MachineDescription.encodeNat count).map
                                  some)
                                (List.append (pre.map some)
                                  [some MachineCodeSymbol.header])) }
                  rw [hreturnRest]
                  exact hfind)
                (TuringMachine.Computes.step htick
                  (TuringMachine.computes_trans
                    (by
                      simpa [MachineDescription.encodeNatAppend,
                        List.map_append, List.append_assoc] using hseek)
                    (TuringMachine.computes_trans
                      (by
                        simpa [scanLeft, countLeft, List.map_append,
                          List.map_reverse, List.append_assoc] using
                          hmarker)
                      (TuringMachine.Computes.step hheader
                        (TuringMachine.Computes.step henter
                          (by
                            rw [hleftDone]
                            exact TuringMachine.Computes.refl _)))))))

theorem transitionListParserMachine_haltsFrom_markPosition_context_inv
    (count : Nat) :
    forall (boundary : Bool) (blanks : Nat)
      (pre tokens : Word MachineCodeSymbol),
      transitionListParserNoHeader pre ->
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.markPosition
          tape :=
            transitionListParserOptionTape
              (transitionListParserMarkedContextLeft
                boundary blanks count pre)
              (tokens.map some) } ->
      exists transitions : List TransitionDescription,
      exists suffix : Word MachineCodeSymbol,
        count = transitions.length ∧
          tokens =
            MachineDescription.encodeTransitionsAppend
              transitions suffix := by
  induction count with
  | zero =>
      intro boundary blanks pre tokens hpre h
      exact ⟨[], tokens, rfl, rfl⟩
  | succ count ih =>
      intro boundary blanks pre tokens hpre h
      cases tokens with
      | nil =>
          have hneed :
              TuringMachine.HaltsFrom transitionListParserMachine
                { state := TransitionListParserState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (transitionListParserMarkedContextLeft
                        true (blanks + 1) count pre)
                      [none] } := by
            exact
              transitionListParserMachine_halts_from_of_computes_suffix
                (transitionListParserMachine_computes_markPosition_context_empty_to_needTransition
                  boundary blanks count pre hpre)
                h
          exact
            False.elim
              ((transitionListParserMachine_not_haltsFrom_needTransition_none
                  (transitionListParserMarkedContextLeft
                    true (blanks + 1) count pre)
                  [])
                hneed)
      | cons symbol rest =>
          have hneed :
              TuringMachine.HaltsFrom transitionListParserMachine
                { state := TransitionListParserState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (transitionListParserMarkedContextLeft
                        true (blanks + 1) count pre)
                      ((symbol :: rest).map some) } := by
            exact
              transitionListParserMachine_halts_from_of_computes_suffix
                (transitionListParserMachine_computes_markPosition_context_to_needTransition
                  boundary blanks count pre hpre symbol rest)
                h
          by_cases hsymbol : symbol = MachineCodeSymbol.transition
          · subst symbol
            have hsourceFrom :
                TuringMachine.HaltsFrom transitionListParserMachine
                  { state := TransitionListParserState.sourceNat
                    tape :=
                      transitionListParserOptionTape
                        (some MachineCodeSymbol.transition ::
                          transitionListParserMarkedContextLeft
                            true (blanks + 1) count pre)
                        (rest.map some) } := by
              exact
                transitionListParserMachine_halts_from_of_computes_suffix
                  (transitionListParserMachine_computes_needTransition
                    (transitionListParserMarkedContextLeft
                      true (blanks + 1) count pre)
                    rest)
                  hneed
            rcases
                transitionListParserMachine_haltsFrom_sourceNat_inv
                  hsourceFrom with
              ⟨source, afterSource, hsourceTokens, hreadFrom⟩
            rcases
                transitionListParserMachine_haltsFrom_readCell_inv
                  hreadFrom with
              ⟨read, afterRead, hreadTokens, hwriteFrom⟩
            rcases
                transitionListParserMachine_haltsFrom_writeCell_inv
                  hwriteFrom with
              ⟨write, afterWrite, hwriteTokens, hmoveFrom⟩
            rcases
                transitionListParserMachine_haltsFrom_moveField_inv
                  hmoveFrom with
              ⟨move, afterMove, hmoveTokens, htargetFrom⟩
            rcases
                transitionListParserMachine_haltsFrom_targetNat_inv
                  htargetFrom with
              ⟨target, restTokens, htargetTokens, hmarkFrom⟩
            let t : TransitionDescription :=
              { source := source
                read := read
                write := write
                move := move
                target := target }
            have hpre' :
                transitionListParserNoHeader
                  (List.append pre
                    (MachineDescription.encodeTransition t)) :=
              transitionListParserNoHeader_append hpre
                (transitionListParser_encodeTransition_noHeader t)
            have hmarkContext :
                TuringMachine.HaltsFrom transitionListParserMachine
                  { state := TransitionListParserState.markPosition
                    tape :=
                      transitionListParserOptionTape
                        (transitionListParserMarkedContextLeft
                          true (blanks + 1) count
                          (List.append pre
                            (MachineDescription.encodeTransition t)))
                        (restTokens.map some) } := by
              simpa [transitionListParserMarkedContextLeft, t,
                MachineDescription.encodeTransition,
                MachineDescription.encodeTransitionAppend,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeCellAppend,
                MachineDescription.encodeDirectionAppend,
                List.reverse_append, List.map_append,
                List.map_reverse, List.append_assoc] using hmarkFrom
            rcases ih true (blanks + 1)
                (List.append pre (MachineDescription.encodeTransition t))
                restTokens hpre' hmarkContext with
              ⟨transitions, suffix, hcount, hrestTokens⟩
            refine ⟨t :: transitions, suffix, ?_, ?_⟩
            · simp [hcount]
            · simp [MachineDescription.encodeTransitionsAppend,
                MachineDescription.encodeTransitionAppend,
                hsourceTokens, hreadTokens, hwriteTokens,
                hmoveTokens, htargetTokens, hrestTokens, t]
          · exact
              False.elim
                ((transitionListParserMachine_not_haltsFrom_needTransition_nonTransition
                    hsymbol
                    (transitionListParserMarkedContextLeft
                      true (blanks + 1) count pre)
                    (rest.map some))
                  hneed)

theorem transitionListParserMachine_haltsFrom_needTransition_transition_inv
    {count : Nat} {rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.needTransition
          tape :=
            transitionListParserOptionTape
              ((MachineCodeSymbol.blank ::
                MachineDescription.encodeNat count).reverse.map some)
              ((MachineCodeSymbol.transition :: rest).map some) }) :
    exists t : TransitionDescription,
    exists restTokens : Word MachineCodeSymbol,
      MachineCodeSymbol.transition :: rest =
          MachineDescription.encodeTransitionAppend t restTokens ∧
        TuringMachine.HaltsOnInput transitionListParserMachine
          (MachineDescription.encodeNatAppend count restTokens) := by
  have hsourceFrom :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.sourceNat
          tape :=
            transitionListParserOptionTape
              (some MachineCodeSymbol.transition ::
                ((MachineCodeSymbol.blank ::
                  MachineDescription.encodeNat count).reverse.map some))
              (rest.map some) } := by
    exact
      transitionListParserMachine_halts_from_of_computes_suffix
        (transitionListParserMachine_computes_needTransition
          ((MachineCodeSymbol.blank ::
            MachineDescription.encodeNat count).reverse.map some)
          rest)
        h
  rcases
      transitionListParserMachine_haltsFrom_sourceNat_inv
        hsourceFrom with
    ⟨source, afterSource, hsourceTokens, hreadFrom⟩
  rcases
      transitionListParserMachine_haltsFrom_readCell_inv
        hreadFrom with
    ⟨read, afterRead, hreadTokens, hwriteFrom⟩
  rcases
      transitionListParserMachine_haltsFrom_writeCell_inv
        hwriteFrom with
    ⟨write, afterWrite, hwriteTokens, hmoveFrom⟩
  rcases
      transitionListParserMachine_haltsFrom_moveField_inv
        hmoveFrom with
    ⟨move, afterMove, hmoveTokens, htargetFrom⟩
  rcases
      transitionListParserMachine_haltsFrom_targetNat_inv
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
      hsourceTokens, hreadTokens, hwriteTokens, hmoveTokens,
      htargetTokens]
  · cases count with
    | zero =>
        exact transitionListParserMachine_halts_count_zero restTokens
    | succ count =>
        have hpre :
            transitionListParserNoHeader
              (MachineDescription.encodeTransition t) :=
          transitionListParser_encodeTransition_noHeader t
        have hmarkContext :
            TuringMachine.HaltsFrom transitionListParserMachine
              { state := TransitionListParserState.markPosition
                tape :=
                  transitionListParserOptionTape
                    (transitionListParserMarkedContextLeft
                      false 1 (count + 1)
                      (MachineDescription.encodeTransition t))
                    (restTokens.map some) } := by
          simpa [transitionListParserMarkedContextLeft, t,
            MachineDescription.encodeTransition,
            MachineDescription.encodeTransitionAppend,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeCellAppend,
            MachineDescription.encodeDirectionAppend,
            MachineDescription.encodeNat,
            List.reverse_append, List.map_append,
            List.map_reverse, List.append_assoc] using hmarkFrom
        rcases
            transitionListParserMachine_haltsFrom_markPosition_context_inv
              (count + 1) false 1
              (MachineDescription.encodeTransition t)
              restTokens hpre hmarkContext with
          ⟨transitions, suffix, hcount, hrestTokens⟩
        have hhalts :=
          transitionListParserMachine_halts_encodeTransitionsAppend
            transitions suffix
        rw [hcount, hrestTokens]
        exact hhalts

theorem transitionListParserMachine_haltsFrom_needTransition_inv
    {count : Nat} {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state := TransitionListParserState.needTransition
          tape :=
            transitionListParserOptionTape
              ((MachineCodeSymbol.blank ::
                MachineDescription.encodeNat count).reverse.map some)
              (tokens.map some) }) :
    exists t : TransitionDescription,
    exists restTokens : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeTransitionAppend t restTokens ∧
        TuringMachine.HaltsOnInput transitionListParserMachine
          (MachineDescription.encodeNatAppend count restTokens) := by
  cases tokens with
  | nil =>
      exact
        False.elim
          ((transitionListParserMachine_not_haltsFrom_needTransition_empty
              ((MachineCodeSymbol.blank ::
                MachineDescription.encodeNat count).reverse.map some))
            h)
  | cons symbol rest =>
      by_cases hsymbol : symbol = MachineCodeSymbol.transition
      · subst symbol
        exact
          transitionListParserMachine_haltsFrom_needTransition_transition_inv
            h
      · exact
          False.elim
            ((transitionListParserMachine_not_haltsFrom_needTransition_nonTransition
                hsymbol
                ((MachineCodeSymbol.blank ::
                  MachineDescription.encodeNat count).reverse.map some)
                (rest.map some))
              h)

theorem transitionListParserMachine_halts_succ_inv
    {count : Nat} {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsOnInput transitionListParserMachine
        (MachineDescription.encodeNatAppend (count + 1) tokens)) :
    exists t : TransitionDescription,
    exists restTokens : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeTransitionAppend t restTokens ∧
        TuringMachine.HaltsOnInput transitionListParserMachine
          (MachineDescription.encodeNatAppend count restTokens) := by
  have hprefix :=
    transitionListParserMachine_computes_succCount_to_needTransition
      count tokens
  have hfrom :
      TuringMachine.HaltsFrom transitionListParserMachine
        { state :=
            TransitionListParserState.findCount
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape []
              ((MachineDescription.encodeNatAppend (count + 1)
                tokens).map some) } := by
    simpa [TuringMachine.HaltsOnInput, TuringMachine.initial,
      transitionListParserMachine,
      transitionListParserOptionTape_nil_eq_input] using h
  have hneed :=
    transitionListParserMachine_halts_from_of_computes_suffix
      hprefix hfrom
  exact transitionListParserMachine_haltsFrom_needTransition_inv hneed

theorem transitionListParserMachine_halts_encodeNatAppend_only_encodeTransitionsAppend
    {count : Nat} {tokens : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsOnInput transitionListParserMachine
        (MachineDescription.encodeNatAppend count tokens)) :
    exists transitions : List TransitionDescription,
    exists suffix : Word MachineCodeSymbol,
      count = transitions.length ∧
        tokens =
          MachineDescription.encodeTransitionsAppend transitions suffix := by
  cases count with
  | zero =>
      exact ⟨[], tokens, rfl, rfl⟩
  | succ count =>
      rcases transitionListParserMachine_halts_succ_inv h with
        ⟨t, restTokens, htokens, hrest⟩
      rcases
          transitionListParserMachine_halts_encodeNatAppend_only_encodeTransitionsAppend
            hrest with
        ⟨transitions, suffix, hcount, hrestTokens⟩
      refine ⟨t :: transitions, suffix, ?_, ?_⟩
      · simp [hcount]
      · rw [htokens, hrestTokens]
        rfl


end Computability
end FoC
