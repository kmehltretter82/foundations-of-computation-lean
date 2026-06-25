import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.BranchEmitters.Base

set_option doc.verso true

/-!
# Branch emitter failure cleanup

Continuation of the split finite-source branch emitter development.
-/

namespace FoC
namespace Computability

open Languages

theorem codePrefixParserBranch_failure_boundary
    (rightBlanks : Nat) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.failureEraseLeft
        tape :=
          transitionListParserOptionTape []
            (none :: List.replicate rightBlanks none) }
      codePrefixParserBranchFalseOutput := by
  let afterZero :
      TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserBranchState :=
    { state := CodePrefixParserBranchState.failureWriteDone
      tape :=
        transitionListParserOptionTape []
          (none :: some MachineCodeSymbol.zero ::
            List.replicate rightBlanks none) }
  let afterDone :
      TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserBranchState :=
    { state := CodePrefixParserBranchState.failureWriteTick
      tape :=
        transitionListParserOptionTape []
          (none :: some MachineCodeSymbol.done ::
            some MachineCodeSymbol.zero ::
              List.replicate rightBlanks none) }
  let final :
      TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserBranchState :=
    { state := CodePrefixParserBranchState.halt
      tape :=
        transitionListParserOptionTape [some MachineCodeSymbol.tick]
          (some MachineCodeSymbol.done ::
            some MachineCodeSymbol.zero ::
              List.replicate rightBlanks none) }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact
      TuringMachine.Computes.step
        (TuringMachine.Step.mk
          (write := some MachineCodeSymbol.zero)
          (dir := Direction.left)
          (nextState := CodePrefixParserBranchState.failureWriteDone)
          (by
            simp [codePrefixParserBranchMachine,
              transitionListParserOptionTape, Tape.read]))
        (TuringMachine.Computes.step
          (TuringMachine.Step.mk
            (write := some MachineCodeSymbol.done)
            (dir := Direction.left)
            (nextState := CodePrefixParserBranchState.failureWriteTick)
            (by
              simp [codePrefixParserBranchMachine,
                transitionListParserOptionTape, Tape.read]))
          (TuringMachine.Computes.step
            (TuringMachine.Step.mk
              (write := some MachineCodeSymbol.tick)
              (dir := Direction.right)
              (nextState := CodePrefixParserBranchState.halt)
              (by
                simp [codePrefixParserBranchMachine,
                  transitionListParserOptionTape, Tape.read, Tape.move,
                  Tape.write]))
            (TuringMachine.Computes.refl _)))
  · simp [TuringMachine.Halted, codePrefixParserBranchMachine, final]
  · simp [final, codePrefixParserBranchFalseOutput,
      transitionListParserOptionTape_normalizedOutput]

theorem codePrefixParserBranch_failure_eraseLeft_symbol
    (leftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (rightBlanks : Nat) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.failureEraseLeft
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (some current :: List.replicate rightBlanks none) }
      codePrefixParserBranchFalseOutput := by
  induction leftRev generalizing current rightBlanks with
  | nil =>
      have hstep :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.failureEraseLeft
              tape :=
                transitionListParserOptionTape
                  ([] : List (Option MachineCodeSymbol))
                  (some current :: List.replicate rightBlanks none) }
            { state := CodePrefixParserBranchState.failureEraseLeft
              tape :=
                transitionListParserOptionTape []
                  (none :: none ::
                    List.replicate rightBlanks none) } :=
        TuringMachine.Step.mk
          (write := none)
          (dir := Direction.left)
          (nextState := CodePrefixParserBranchState.failureEraseLeft)
          (by
            simp [codePrefixParserBranchMachine,
              transitionListParserOptionTape, Tape.read])
      rcases
          codePrefixParserBranch_failure_boundary
            (rightBlanks + 1) with
        ⟨final, hcomp, hhalt, hout⟩
      refine ⟨final, ?_, hhalt, hout⟩
      simpa [List.replicate_succ, List.replicate_succ,
        Nat.add_comm] using TuringMachine.Computes.step hstep hcomp
  | cons leftHead leftTail ih =>
      have hstep :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.failureEraseLeft
              tape :=
                transitionListParserOptionTape
                  ((leftHead :: leftTail).map some)
                  (some current :: List.replicate rightBlanks none) }
            { state := CodePrefixParserBranchState.failureEraseLeft
              tape :=
                transitionListParserOptionTape (leftTail.map some)
                  (some leftHead :: none ::
                    List.replicate rightBlanks none) } :=
        TuringMachine.Step.mk
          (write := none)
          (dir := Direction.left)
          (nextState := CodePrefixParserBranchState.failureEraseLeft)
          (by
            simp [codePrefixParserBranchMachine,
              transitionListParserOptionTape, Tape.read])
      rcases ih leftHead (rightBlanks + 1) with
        ⟨final, hcomp, hhalt, hout⟩
      refine ⟨final, ?_, hhalt, hout⟩
      simpa [List.replicate_succ, Nat.add_comm] using
        TuringMachine.Computes.step hstep hcomp

theorem codePrefixParserBranch_failure_eraseRight
    (leftRev rest : Word MachineCodeSymbol) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.failureEraseRight
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (rest.map some) }
      codePrefixParserBranchFalseOutput := by
  induction rest generalizing leftRev with
  | nil =>
      have hstep_empty_left :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.failureEraseRight
              tape :=
                transitionListParserOptionTape
                  ([] : List (Option MachineCodeSymbol)) [] }
            { state := CodePrefixParserBranchState.failureEraseLeft
              tape := transitionListParserOptionTape [] [none, none] } :=
        TuringMachine.Step.mk
          (write := none)
          (dir := Direction.left)
          (nextState := CodePrefixParserBranchState.failureEraseLeft)
          (by
            simp [codePrefixParserBranchMachine,
              transitionListParserOptionTape, Tape.read])
      cases leftRev with
      | nil =>
          rcases codePrefixParserBranch_failure_boundary 1 with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, hout⟩
          simpa using TuringMachine.Computes.step hstep_empty_left hcomp
      | cons leftHead leftTail =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.failureEraseRight
                  tape :=
                    transitionListParserOptionTape
                      ((leftHead :: leftTail).map some) [] }
                { state := CodePrefixParserBranchState.failureEraseLeft
                  tape :=
                    transitionListParserOptionTape (leftTail.map some)
                      [some leftHead, none] } :=
            TuringMachine.Step.mk
              (write := none)
              (dir := Direction.left)
              (nextState := CodePrefixParserBranchState.failureEraseLeft)
              (by
                simp [codePrefixParserBranchMachine,
                  transitionListParserOptionTape, Tape.read])
          rcases
              codePrefixParserBranch_failure_eraseLeft_symbol
                leftTail leftHead 1 with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, hout⟩
          simpa using TuringMachine.Computes.step hstep hcomp
  | cons symbol rest ih =>
      have hstep :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.failureEraseRight
              tape :=
                transitionListParserOptionTape (leftRev.map some)
                  ((symbol :: rest).map some) }
            { state := CodePrefixParserBranchState.failureEraseRight
              tape :=
                transitionListParserOptionTape
                  ((MachineCodeSymbol.blank :: leftRev).map some)
                  (rest.map some) } :=
        by
          change
            TuringMachine.Step codePrefixParserBranchMachine
              { state := CodePrefixParserBranchState.failureEraseRight
                tape :=
                  transitionListParserOptionTape (leftRev.map some)
                    ((symbol :: rest).map some) }
              { state := CodePrefixParserBranchState.failureEraseRight
                tape :=
                  transitionListParserOptionTape
                    (some MachineCodeSymbol.blank :: leftRev.map some)
                    (rest.map some) }
          rw [← transitionListParserOptionTape_move_right
            (leftRev.map some) (rest.map some) (some symbol)
            (some MachineCodeSymbol.blank)]
          exact
            TuringMachine.Step.mk
              (write := some MachineCodeSymbol.blank)
              (dir := Direction.right)
              (nextState := CodePrefixParserBranchState.failureEraseRight)
              (by
                simp [codePrefixParserBranchMachine,
                  transitionListParserOptionTape, Tape.read])
      rcases ih (MachineCodeSymbol.blank :: leftRev) with
        ⟨final, hcomp, hhalt, hout⟩
      exact ⟨final, TuringMachine.Computes.step hstep hcomp, hhalt, hout⟩

theorem codePrefixParserBranch_failure_eraseRight_blanks
    (leftRev rest : Word MachineCodeSymbol) (rightBlanks : Nat) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.failureEraseRight
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (List.append (rest.map some)
              (List.replicate rightBlanks none)) }
      codePrefixParserBranchFalseOutput := by
  induction rest generalizing leftRev with
  | nil =>
      cases rightBlanks with
      | zero =>
          cases leftRev with
          | nil =>
              have hstep :
                  TuringMachine.Step codePrefixParserBranchMachine
                    { state :=
                        CodePrefixParserBranchState.failureEraseRight
                      tape :=
                        transitionListParserOptionTape
                          ([] : List (Option MachineCodeSymbol)) [] }
                    { state :=
                        CodePrefixParserBranchState.failureEraseLeft
                      tape := transitionListParserOptionTape [] [none, none] } := by
                rw [← transitionListParserOptionTape_move_left_boundary_empty
                  none]
                exact
                  TuringMachine.Step.mk
                    (write := none)
                    (dir := Direction.left)
                    (nextState :=
                      CodePrefixParserBranchState.failureEraseLeft)
                    (by
                      simp [codePrefixParserBranchMachine,
                        transitionListParserOptionTape, Tape.read])
              rcases codePrefixParserBranch_failure_boundary 1 with
                ⟨final, hcomp, hhalt, hout⟩
              exact
                ⟨final, TuringMachine.Computes.step hstep hcomp,
                  hhalt, hout⟩
          | cons leftHead leftTail =>
              have hstep :
                  TuringMachine.Step codePrefixParserBranchMachine
                    { state :=
                        CodePrefixParserBranchState.failureEraseRight
                      tape :=
                        transitionListParserOptionTape
                          ((leftHead :: leftTail).map some) [] }
                    { state :=
                        CodePrefixParserBranchState.failureEraseLeft
                      tape :=
                        transitionListParserOptionTape
                          (leftTail.map some) [some leftHead, none] } := by
                rw [← transitionListParserOptionTape_move_left_empty
                  (leftTail.map some) (some leftHead) none]
                exact
                  TuringMachine.Step.mk
                    (write := none)
                    (dir := Direction.left)
                    (nextState :=
                      CodePrefixParserBranchState.failureEraseLeft)
                    (by
                      simp [codePrefixParserBranchMachine,
                        transitionListParserOptionTape, Tape.read])
              rcases
                  codePrefixParserBranch_failure_eraseLeft_symbol
                    leftTail leftHead 1 with
                ⟨final, hcomp, hhalt, hout⟩
              exact
                ⟨final, TuringMachine.Computes.step hstep hcomp,
                  hhalt, hout⟩
      | succ rightBlanks =>
          cases leftRev with
          | nil =>
              have hstep :
                  TuringMachine.Step codePrefixParserBranchMachine
                    { state :=
                        CodePrefixParserBranchState.failureEraseRight
                      tape :=
                        transitionListParserOptionTape
                          ([] : List (Option MachineCodeSymbol))
                          (none :: List.replicate rightBlanks none) }
                    { state :=
                        CodePrefixParserBranchState.failureEraseLeft
                      tape :=
                        transitionListParserOptionTape []
                          (none :: none ::
                            List.replicate rightBlanks none) } := by
                rw [← transitionListParserOptionTape_move_left_boundary
                  (List.replicate rightBlanks none) none none]
                exact
                  TuringMachine.Step.mk
                    (write := none)
                    (dir := Direction.left)
                    (nextState :=
                      CodePrefixParserBranchState.failureEraseLeft)
                    (by
                      simp [codePrefixParserBranchMachine,
                        transitionListParserOptionTape, Tape.read])
              rcases
                  codePrefixParserBranch_failure_boundary
                    (rightBlanks + 1) with
                ⟨final, hcomp, hhalt, hout⟩
              refine ⟨final, ?_, hhalt, hout⟩
              simpa [List.replicate_succ, Nat.add_comm] using
                TuringMachine.Computes.step hstep hcomp
          | cons leftHead leftTail =>
              have hstep :
                  TuringMachine.Step codePrefixParserBranchMachine
                    { state :=
                        CodePrefixParserBranchState.failureEraseRight
                      tape :=
                        transitionListParserOptionTape
                          ((leftHead :: leftTail).map some)
                          (none :: List.replicate rightBlanks none) }
                    { state :=
                        CodePrefixParserBranchState.failureEraseLeft
                      tape :=
                        transitionListParserOptionTape
                          (leftTail.map some)
                          (some leftHead :: none ::
                            List.replicate rightBlanks none) } := by
                rw [← transitionListParserOptionTape_move_left
                  (leftTail.map some)
                  (List.replicate rightBlanks none)
                  (some leftHead) none none]
                exact
                  TuringMachine.Step.mk
                    (write := none)
                    (dir := Direction.left)
                    (nextState :=
                      CodePrefixParserBranchState.failureEraseLeft)
                    (by
                      simp [codePrefixParserBranchMachine,
                        transitionListParserOptionTape, Tape.read])
              rcases
                  codePrefixParserBranch_failure_eraseLeft_symbol
                    leftTail leftHead (rightBlanks + 1) with
                ⟨final, hcomp, hhalt, hout⟩
              refine ⟨final, ?_, hhalt, hout⟩
              simpa [List.replicate_succ, Nat.add_comm] using
                TuringMachine.Computes.step hstep hcomp
  | cons symbol rest ih =>
      have hstep :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.failureEraseRight
              tape :=
                transitionListParserOptionTape (leftRev.map some)
                  (List.append ((symbol :: rest).map some)
                    (List.replicate rightBlanks none)) }
            { state := CodePrefixParserBranchState.failureEraseRight
              tape :=
                transitionListParserOptionTape
                  ((MachineCodeSymbol.blank :: leftRev).map some)
                  (List.append (rest.map some)
                    (List.replicate rightBlanks none)) } :=
        by
          change
            TuringMachine.Step codePrefixParserBranchMachine
              { state := CodePrefixParserBranchState.failureEraseRight
                tape :=
                  transitionListParserOptionTape (leftRev.map some)
                    (some symbol ::
                      List.append (rest.map some)
                        (List.replicate rightBlanks none)) }
              { state := CodePrefixParserBranchState.failureEraseRight
                tape :=
                  transitionListParserOptionTape
                    (some MachineCodeSymbol.blank :: leftRev.map some)
                    (List.append (rest.map some)
                      (List.replicate rightBlanks none)) }
          rw [← transitionListParserOptionTape_move_right
            (leftRev.map some)
            (List.append (rest.map some)
              (List.replicate rightBlanks none))
            (some symbol) (some MachineCodeSymbol.blank)]
          exact
            TuringMachine.Step.mk
              (write := some MachineCodeSymbol.blank)
              (dir := Direction.right)
              (nextState := CodePrefixParserBranchState.failureEraseRight)
              (by
                simp [codePrefixParserBranchMachine,
                  transitionListParserOptionTape, Tape.read])
      rcases ih (MachineCodeSymbol.blank :: leftRev) with
        ⟨final, hcomp, hhalt, hout⟩
      exact ⟨final, TuringMachine.Computes.step hstep hcomp, hhalt, hout⟩

theorem codePrefixParserBranch_failure_seekBoundary_marker
    (prefixLeft right : Word MachineCodeSymbol) (rightBlanks : Nat) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.failureSeekBoundary
        tape :=
          transitionListParserOptionTape (prefixLeft.map some)
            (none :: List.append (right.map some)
              (List.replicate rightBlanks none)) }
      codePrefixParserBranchFalseOutput := by
  have hstep :
      TuringMachine.Step codePrefixParserBranchMachine
        { state := CodePrefixParserBranchState.failureSeekBoundary
          tape :=
            transitionListParserOptionTape (prefixLeft.map some)
              (none :: List.append (right.map some)
                (List.replicate rightBlanks none)) }
        { state := CodePrefixParserBranchState.failureEraseRight
          tape :=
            transitionListParserOptionTape
              ((MachineCodeSymbol.done :: prefixLeft).map some)
              (List.append (right.map some)
                (List.replicate rightBlanks none)) } := by
    change
      TuringMachine.Step codePrefixParserBranchMachine
        { state := CodePrefixParserBranchState.failureSeekBoundary
          tape :=
            transitionListParserOptionTape (prefixLeft.map some)
              (none :: List.append (right.map some)
                (List.replicate rightBlanks none)) }
        { state := CodePrefixParserBranchState.failureEraseRight
          tape :=
            transitionListParserOptionTape
              (some MachineCodeSymbol.done :: prefixLeft.map some)
              (List.append (right.map some)
                (List.replicate rightBlanks none)) }
    rw [← transitionListParserOptionTape_move_right
      (prefixLeft.map some)
      (List.append (right.map some)
        (List.replicate rightBlanks none))
      none (some MachineCodeSymbol.done)]
    exact
      TuringMachine.Step.mk
        (write := some MachineCodeSymbol.done)
        (dir := Direction.right)
        (nextState := CodePrefixParserBranchState.failureEraseRight)
        (by
          simp [codePrefixParserBranchMachine,
            transitionListParserOptionTape, Tape.read])
  rcases
      codePrefixParserBranch_failure_eraseRight_blanks
        (MachineCodeSymbol.done :: prefixLeft) right rightBlanks with
    ⟨final, hcomp, hhalt, hout⟩
  exact ⟨final, TuringMachine.Computes.step hstep hcomp, hhalt, hout⟩

theorem codePrefixParserBranch_failure_seekBoundary_symbol
    (leftSymbols prefixLeft right : Word MachineCodeSymbol)
    (current : MachineCodeSymbol) (rightBlanks : Nat) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.failureSeekBoundary
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (some current :: List.append (right.map some)
              (List.replicate rightBlanks none)) }
      codePrefixParserBranchFalseOutput := by
  induction leftSymbols generalizing current right with
  | nil =>
      have hstep :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.failureSeekBoundary
              tape :=
                transitionListParserOptionTape
                  (none :: prefixLeft.map some)
                  (some current :: List.append (right.map some)
                    (List.replicate rightBlanks none)) }
            { state := CodePrefixParserBranchState.failureSeekBoundary
              tape :=
                transitionListParserOptionTape (prefixLeft.map some)
                  (none :: some current ::
                    List.append (right.map some)
                      (List.replicate rightBlanks none)) } :=
        TuringMachine.Step.mk
          (write := some current)
          (dir := Direction.left)
          (nextState := CodePrefixParserBranchState.failureSeekBoundary)
          (by
            simp [codePrefixParserBranchMachine,
              transitionListParserOptionTape, Tape.read])
      rcases
          codePrefixParserBranch_failure_seekBoundary_marker
            prefixLeft (current :: right) rightBlanks with
        ⟨final, hcomp, hhalt, hout⟩
      refine ⟨final, ?_, hhalt, hout⟩
      simpa [List.append_assoc] using
        TuringMachine.Computes.step hstep hcomp
  | cons leftHead leftTail ih =>
      have hstep :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.failureSeekBoundary
              tape :=
                transitionListParserOptionTape
                  (List.append ((leftHead :: leftTail).map some)
                    (none :: prefixLeft.map some))
                  (some current :: List.append (right.map some)
                    (List.replicate rightBlanks none)) }
            { state := CodePrefixParserBranchState.failureSeekBoundary
              tape :=
                transitionListParserOptionTape
                  (List.append (leftTail.map some)
                    (none :: prefixLeft.map some))
                  (some leftHead :: some current ::
                    List.append (right.map some)
                      (List.replicate rightBlanks none)) } :=
        TuringMachine.Step.mk
          (write := some current)
          (dir := Direction.left)
          (nextState := CodePrefixParserBranchState.failureSeekBoundary)
          (by
            simp [codePrefixParserBranchMachine,
              transitionListParserOptionTape, Tape.read])
      rcases ih (current := leftHead) (right := current :: right) with
        ⟨final, hcomp, hhalt, hout⟩
      refine ⟨final, ?_, hhalt, hout⟩
      simpa [List.append_assoc] using
        TuringMachine.Computes.step hstep hcomp

theorem codePrefixParserBranch_failure_from_stuck_boundary
    (q : CodePrefixParserNormalizerState)
    (hboundary :
      codePrefixParserBranchFailureNeedsBoundary q = true)
    (leftSymbols prefixLeft rest : Word MachineCodeSymbol)
    (hstuck :
      codePrefixParserNormalizerMachine.transition q
          (Tape.read
            (transitionListParserOptionTape
              (List.append (leftSymbols.map some)
                (none :: prefixLeft.map some))
              (rest.map some))) =
        none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer q
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (rest.map some) }
      codePrefixParserBranchFalseOutput := by
  cases rest with
  | nil =>
      have htransition :
          codePrefixParserBranchMachine.transition
              (CodePrefixParserBranchState.normalizer q)
              (Tape.read
                (transitionListParserOptionTape
                  (List.append (leftSymbols.map some)
                    (none :: prefixLeft.map some)) [])) =
            some (none, Direction.left,
              CodePrefixParserBranchState.failureSeekBoundary) := by
        cases q <;>
          simp [codePrefixParserBranchMachine,
            codePrefixParserBranchFailureNeedsBoundary,
            transitionListParserOptionTape, Tape.read] at hboundary hstuck ⊢
        all_goals rw [hstuck]
      cases leftSymbols with
      | nil =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.normalizer q
                  tape :=
                    transitionListParserOptionTape
                      (none :: prefixLeft.map some) [] }
                { state := CodePrefixParserBranchState.failureSeekBoundary
                  tape :=
                    transitionListParserOptionTape (prefixLeft.map some)
                      [none, none] } := by
            rw [← transitionListParserOptionTape_move_left_empty
              (prefixLeft.map some) none none]
            exact TuringMachine.Step.mk htransition
          rcases
              codePrefixParserBranch_failure_seekBoundary_marker
                prefixLeft [] 1 with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, hout⟩
          simpa using TuringMachine.Computes.step hstep hcomp
      | cons leftHead leftTail =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.normalizer q
                  tape :=
                    transitionListParserOptionTape
                      (List.append ((leftHead :: leftTail).map some)
                        (none :: prefixLeft.map some)) [] }
                { state := CodePrefixParserBranchState.failureSeekBoundary
                  tape :=
                    transitionListParserOptionTape
                      (List.append (leftTail.map some)
                        (none :: prefixLeft.map some))
                      [some leftHead, none] } := by
            change
              TuringMachine.Step codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.normalizer q
                  tape :=
                    transitionListParserOptionTape
                      (some leftHead ::
                        List.append (leftTail.map some)
                          (none :: prefixLeft.map some)) [] }
                { state := CodePrefixParserBranchState.failureSeekBoundary
                  tape :=
                    transitionListParserOptionTape
                      (List.append (leftTail.map some)
                        (none :: prefixLeft.map some))
                      [some leftHead, none] }
            rw [← transitionListParserOptionTape_move_left_empty
              (List.append (leftTail.map some)
                (none :: prefixLeft.map some))
              (some leftHead) none]
            exact TuringMachine.Step.mk htransition
          rcases
              codePrefixParserBranch_failure_seekBoundary_symbol
                leftTail prefixLeft [] leftHead 1 with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, hout⟩
          simpa using TuringMachine.Computes.step hstep hcomp
  | cons symbol suffix =>
      have htransition :
          codePrefixParserBranchMachine.transition
              (CodePrefixParserBranchState.normalizer q)
              (Tape.read
                (transitionListParserOptionTape
                  (List.append (leftSymbols.map some)
                    (none :: prefixLeft.map some))
                  ((symbol :: suffix).map some))) =
            some (some symbol, Direction.left,
              CodePrefixParserBranchState.failureSeekBoundary) := by
        cases q <;>
          simp [codePrefixParserBranchMachine,
            codePrefixParserBranchFailureNeedsBoundary,
            transitionListParserOptionTape, Tape.read] at hboundary hstuck ⊢
        all_goals rw [hstuck]
      cases leftSymbols with
      | nil =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.normalizer q
                  tape :=
                    transitionListParserOptionTape
                      (none :: prefixLeft.map some)
                      ((symbol :: suffix).map some) }
                { state := CodePrefixParserBranchState.failureSeekBoundary
                  tape :=
                    transitionListParserOptionTape (prefixLeft.map some)
                      (none :: some symbol :: suffix.map some) } := by
            rw [← transitionListParserOptionTape_move_left
              (prefixLeft.map some) (suffix.map some)
              none (some symbol) (some symbol)]
            exact TuringMachine.Step.mk htransition
          rcases
              codePrefixParserBranch_failure_seekBoundary_marker
                prefixLeft (symbol :: suffix) 0 with
            ⟨final, hcomp, hhalt, hout⟩
          have hcomp' :
              TuringMachine.Computes codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.failureSeekBoundary
                  tape :=
                    transitionListParserOptionTape (prefixLeft.map some)
                      (none :: some symbol :: suffix.map some) }
                final := by
            simpa using hcomp
          refine ⟨final, ?_, hhalt, hout⟩
          exact TuringMachine.Computes.step hstep hcomp'
      | cons leftHead leftTail =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.normalizer q
                  tape :=
                    transitionListParserOptionTape
                      (List.append ((leftHead :: leftTail).map some)
                        (none :: prefixLeft.map some))
                      ((symbol :: suffix).map some) }
                { state := CodePrefixParserBranchState.failureSeekBoundary
                  tape :=
                    transitionListParserOptionTape
                      (List.append (leftTail.map some)
                        (none :: prefixLeft.map some))
                      (some leftHead :: some symbol :: suffix.map some) } := by
            change
              TuringMachine.Step codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.normalizer q
                  tape :=
                    transitionListParserOptionTape
                      (some leftHead ::
                        List.append (leftTail.map some)
                          (none :: prefixLeft.map some))
                      (some symbol :: suffix.map some) }
                { state := CodePrefixParserBranchState.failureSeekBoundary
                  tape :=
                    transitionListParserOptionTape
                      (List.append (leftTail.map some)
                        (none :: prefixLeft.map some))
                      (some leftHead :: some symbol :: suffix.map some) }
            rw [← transitionListParserOptionTape_move_left
              (List.append (leftTail.map some)
                (none :: prefixLeft.map some))
              (suffix.map some)
              (some leftHead) (some symbol) (some symbol)]
            exact TuringMachine.Step.mk htransition
          rcases
              codePrefixParserBranch_failure_seekBoundary_symbol
                leftTail prefixLeft (symbol :: suffix) leftHead 0 with
            ⟨final, hcomp, hhalt, hout⟩
          have hcomp' :
              TuringMachine.Computes codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.failureSeekBoundary
                  tape :=
                    transitionListParserOptionTape
                      (List.append (leftTail.map some)
                        (none :: prefixLeft.map some))
                      (some leftHead :: some symbol :: suffix.map some) }
                final := by
            simpa using hcomp
          refine ⟨final, ?_, hhalt, hout⟩
          exact TuringMachine.Computes.step hstep hcomp'

theorem codePrefixParserBranch_failure_from_clean_stuck_noBoundary
    (q : CodePrefixParserNormalizerState)
    (hnotHalt : q ≠ CodePrefixParserNormalizerState.halt)
    (hboundary :
      codePrefixParserBranchFailureNeedsBoundary q = false)
    (leftRev rest : Word MachineCodeSymbol)
    (hstuck :
      codePrefixParserNormalizerMachine.transition q
          (Tape.read
            (transitionListParserOptionTape (leftRev.map some)
              (rest.map some))) =
        none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer q
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (rest.map some) }
      codePrefixParserBranchFalseOutput := by
  cases rest with
  | nil =>
      have htransition :
          codePrefixParserBranchMachine.transition
              (CodePrefixParserBranchState.normalizer q)
              (Tape.read
                (transitionListParserOptionTape (leftRev.map some) [])) =
            some (some MachineCodeSymbol.blank, Direction.right,
              CodePrefixParserBranchState.failureEraseRight) := by
        cases q <;>
          simp [codePrefixParserBranchMachine,
            codePrefixParserBranchFailureNeedsBoundary,
            transitionListParserOptionTape, Tape.read] at hnotHalt hboundary hstuck ⊢
        all_goals rw [hstuck]
      have hstep :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.normalizer q
              tape :=
                transitionListParserOptionTape (leftRev.map some) [] }
            { state := CodePrefixParserBranchState.failureEraseRight
              tape :=
                transitionListParserOptionTape
                  ((MachineCodeSymbol.blank :: leftRev).map some) [] } := by
        change
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.normalizer q
              tape :=
                transitionListParserOptionTape (leftRev.map some) [] }
            { state := CodePrefixParserBranchState.failureEraseRight
              tape :=
                transitionListParserOptionTape
                  (some MachineCodeSymbol.blank :: leftRev.map some) [] }
        rw [← transitionListParserOptionTape_move_right_empty
          (leftRev.map some) (some MachineCodeSymbol.blank)]
        exact TuringMachine.Step.mk htransition
      rcases
          codePrefixParserBranch_failure_eraseRight
            (MachineCodeSymbol.blank :: leftRev) [] with
        ⟨final, hcomp, hhalt, hout⟩
      exact ⟨final, TuringMachine.Computes.step hstep hcomp, hhalt, hout⟩
  | cons symbol suffix =>
      have htransition :
          codePrefixParserBranchMachine.transition
              (CodePrefixParserBranchState.normalizer q)
              (Tape.read
                (transitionListParserOptionTape (leftRev.map some)
                  ((symbol :: suffix).map some))) =
            some (some MachineCodeSymbol.blank, Direction.right,
              CodePrefixParserBranchState.failureEraseRight) := by
        cases q <;>
          simp [codePrefixParserBranchMachine,
            codePrefixParserBranchFailureNeedsBoundary,
            transitionListParserOptionTape, Tape.read] at hnotHalt hboundary hstuck ⊢
        all_goals rw [hstuck]
      have hstep :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.normalizer q
              tape :=
                transitionListParserOptionTape (leftRev.map some)
                  ((symbol :: suffix).map some) }
            { state := CodePrefixParserBranchState.failureEraseRight
              tape :=
                transitionListParserOptionTape
                  ((MachineCodeSymbol.blank :: leftRev).map some)
                  (suffix.map some) } := by
        change
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.normalizer q
              tape :=
                transitionListParserOptionTape (leftRev.map some)
                  ((symbol :: suffix).map some) }
            { state := CodePrefixParserBranchState.failureEraseRight
              tape :=
                transitionListParserOptionTape
                  (some MachineCodeSymbol.blank :: leftRev.map some)
                  (suffix.map some) }
        rw [← transitionListParserOptionTape_move_right
          (leftRev.map some) (suffix.map some) (some symbol)
          (some MachineCodeSymbol.blank)]
        exact TuringMachine.Step.mk htransition
      rcases
          codePrefixParserBranch_failure_eraseRight
            (MachineCodeSymbol.blank :: leftRev) suffix with
        ⟨final, hcomp, hhalt, hout⟩
      exact ⟨final, TuringMachine.Computes.step hstep hcomp, hhalt, hout⟩

end Computability
end FoC
