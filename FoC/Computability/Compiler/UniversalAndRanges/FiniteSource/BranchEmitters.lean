import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer
set_option doc.verso true

/-!
# Finite Source Branch Emitters

This module implements the compiler components responsible for emitting branch instructions in finite source programs.
-/


set_option doc.verso true

namespace FoC
namespace Computability

open Languages

def codePrefixParserBranchTruePrefix : Word MachineCodeSymbol :=
  [MachineCodeSymbol.tick, MachineCodeSymbol.done, MachineCodeSymbol.one]

def codePrefixParserBranchFalseOutput : Word MachineCodeSymbol :=
  [MachineCodeSymbol.tick, MachineCodeSymbol.done, MachineCodeSymbol.zero]

theorem codePrefixParserBranchTruePrefix_append
    (tokens : Word MachineCodeSymbol) :
    List.append codePrefixParserBranchTruePrefix tokens =
      MachineDescription.encodeBoolWordAppend [true] tokens := by
  rfl

theorem codePrefixParserBranchFalseOutput_eq :
    codePrefixParserBranchFalseOutput =
      MachineDescription.encodeBoolWord [false] := by
  rfl

theorem transitionListParserTape_eq_optionTape_map
    (leftRev rest : Word MachineCodeSymbol) :
    transitionListParserTape leftRev rest =
      transitionListParserOptionTape (leftRev.map some) (rest.map some) := by
  cases rest <;> rfl

inductive CodePrefixParserBranchState where
  | normalizer :
      CodePrefixParserNormalizerState -> CodePrefixParserBranchState
  | successSeekLeft : CodePrefixParserBranchState
  | successWriteDone : CodePrefixParserBranchState
  | successWriteTick : CodePrefixParserBranchState
  | failureSeekBoundary : CodePrefixParserBranchState
  | failureEraseRight : CodePrefixParserBranchState
  | failureEraseLeft : CodePrefixParserBranchState
  | failureWriteDone : CodePrefixParserBranchState
  | failureWriteTick : CodePrefixParserBranchState
  | halt : CodePrefixParserBranchState

namespace CodePrefixParserBranchState

def elems : List CodePrefixParserBranchState :=
  (CodePrefixParserNormalizerState.elems.map
    CodePrefixParserBranchState.normalizer) ++
  [successSeekLeft,
    successWriteDone,
    successWriteTick,
    failureSeekBoundary,
    failureEraseRight,
    failureEraseLeft,
    failureWriteDone,
    failureWriteTick,
    halt]

def finite : Foundation.FiniteType CodePrefixParserBranchState where
  elems := elems
  complete := by
    intro state
    cases state with
    | normalizer q =>
        have hq : q ∈ CodePrefixParserNormalizerState.elems :=
          CodePrefixParserNormalizerState.finite.complete q
        simp [elems, hq]
    | successSeekLeft =>
        simp [elems]
    | successWriteDone =>
        simp [elems]
    | successWriteTick =>
        simp [elems]
    | failureSeekBoundary =>
        simp [elems]
    | failureEraseRight =>
        simp [elems]
    | failureEraseLeft =>
        simp [elems]
    | failureWriteDone =>
        simp [elems]
    | failureWriteTick =>
        simp [elems]
    | halt =>
        simp [elems]

end CodePrefixParserBranchState

def codePrefixParserBranchFailureNeedsBoundary :
    CodePrefixParserNormalizerState -> Bool
  | CodePrefixParserNormalizerState.needHeader => false
  | CodePrefixParserNormalizerState.stateCount => false
  | CodePrefixParserNormalizerState.startField => false
  | CodePrefixParserNormalizerState.haltField => false
  | CodePrefixParserNormalizerState.halt => false
  | _ => true

def codePrefixParserBranchMachine :
    TuringMachine MachineCodeSymbol CodePrefixParserBranchState where
  start :=
    CodePrefixParserBranchState.normalizer
      CodePrefixParserNormalizerState.needHeader
  halt := CodePrefixParserBranchState.halt
  transition := fun state cell =>
    match state with
    | CodePrefixParserBranchState.normalizer
        CodePrefixParserNormalizerState.halt =>
        some (cell, Direction.left,
          CodePrefixParserBranchState.successSeekLeft)
    | CodePrefixParserBranchState.normalizer q =>
        match codePrefixParserNormalizerMachine.transition q cell with
        | some (write, dir, next) =>
            some (write, dir,
              CodePrefixParserBranchState.normalizer next)
        | none =>
            if codePrefixParserBranchFailureNeedsBoundary q then
              some (cell, Direction.left,
                CodePrefixParserBranchState.failureSeekBoundary)
            else
              some (some MachineCodeSymbol.blank, Direction.right,
                CodePrefixParserBranchState.failureEraseRight)
    | CodePrefixParserBranchState.successSeekLeft =>
        match cell with
        | some _ =>
            some (cell, Direction.left,
              CodePrefixParserBranchState.successSeekLeft)
        | none =>
            some (some MachineCodeSymbol.one, Direction.left,
              CodePrefixParserBranchState.successWriteDone)
    | CodePrefixParserBranchState.successWriteDone =>
        some (some MachineCodeSymbol.done, Direction.left,
          CodePrefixParserBranchState.successWriteTick)
    | CodePrefixParserBranchState.successWriteTick =>
        some (some MachineCodeSymbol.tick, Direction.right,
          CodePrefixParserBranchState.halt)
    | CodePrefixParserBranchState.failureSeekBoundary =>
        match cell with
        | some _ =>
            some (cell, Direction.left,
              CodePrefixParserBranchState.failureSeekBoundary)
        | none =>
            some (some MachineCodeSymbol.done, Direction.right,
              CodePrefixParserBranchState.failureEraseRight)
    | CodePrefixParserBranchState.failureEraseRight =>
        match cell with
        | some _ =>
            some (some MachineCodeSymbol.blank, Direction.right,
              CodePrefixParserBranchState.failureEraseRight)
        | none =>
            some (none, Direction.left,
              CodePrefixParserBranchState.failureEraseLeft)
    | CodePrefixParserBranchState.failureEraseLeft =>
        match cell with
        | some _ =>
            some (none, Direction.left,
              CodePrefixParserBranchState.failureEraseLeft)
        | none =>
            some (some MachineCodeSymbol.zero, Direction.left,
              CodePrefixParserBranchState.failureWriteDone)
    | CodePrefixParserBranchState.failureWriteDone =>
        some (some MachineCodeSymbol.done, Direction.left,
          CodePrefixParserBranchState.failureWriteTick)
    | CodePrefixParserBranchState.failureWriteTick =>
        some (some MachineCodeSymbol.tick, Direction.right,
          CodePrefixParserBranchState.halt)
    | CodePrefixParserBranchState.halt =>
        none
  statesFinite := CodePrefixParserBranchState.finite

theorem codePrefixParserBranchMachine_haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled
      codePrefixParserBranchMachine := by
  intro cell
  simp [codePrefixParserBranchMachine]

def codePrefixParserBranchLiftConfig
    (c :
      TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserNormalizerState) :
    TuringMachine.Configuration MachineCodeSymbol
      CodePrefixParserBranchState :=
  { state := CodePrefixParserBranchState.normalizer c.state
    tape := c.tape }

theorem codePrefixParserBranchMachine_step_of_normalizer_step
    {c d :
      TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserNormalizerState}
    (hstep : TuringMachine.Step codePrefixParserNormalizerMachine c d) :
    TuringMachine.Step codePrefixParserBranchMachine
      (codePrefixParserBranchLiftConfig c)
      (codePrefixParserBranchLiftConfig d) := by
  rcases c with ⟨q, tape⟩
  cases hstep with
  | mk htransition =>
      cases q
      case halt =>
        simp [codePrefixParserNormalizerMachine] at htransition
      all_goals
        exact TuringMachine.Step.mk (by
          simp [codePrefixParserBranchLiftConfig,
            codePrefixParserBranchMachine]
          rw [htransition])

theorem codePrefixParserBranchMachine_computes_of_normalizer_computes
    {c d :
      TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserNormalizerState}
    (hcomp : TuringMachine.Computes codePrefixParserNormalizerMachine c d) :
    TuringMachine.Computes codePrefixParserBranchMachine
      (codePrefixParserBranchLiftConfig c)
      (codePrefixParserBranchLiftConfig d) := by
  induction hcomp with
  | refl c =>
      exact TuringMachine.Computes.refl _
  | step hstep _ ih =>
      exact TuringMachine.Computes.step
        (codePrefixParserBranchMachine_step_of_normalizer_step hstep)
        ih

def codePrefixParserBranchHaltsFromWithOutput
    (c :
      TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserBranchState)
    (out : Word MachineCodeSymbol) : Prop :=
  exists final :
    TuringMachine.Configuration MachineCodeSymbol
      CodePrefixParserBranchState,
    TuringMachine.Computes codePrefixParserBranchMachine c final ∧
      TuringMachine.Halted codePrefixParserBranchMachine final ∧
        Tape.normalizedOutput final.tape = out

theorem codePrefixParserBranch_success_boundary
    (right : List (Option MachineCodeSymbol)) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.successSeekLeft
        tape := transitionListParserOptionTape [] (none :: right) }
      (List.append codePrefixParserBranchTruePrefix
        (right.filterMap (fun cell => cell))) := by
  let afterOne :
      TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserBranchState :=
    { state := CodePrefixParserBranchState.successWriteDone
      tape :=
        transitionListParserOptionTape []
          (none :: some MachineCodeSymbol.one :: right) }
  let afterDone :
      TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserBranchState :=
    { state := CodePrefixParserBranchState.successWriteTick
      tape :=
        transitionListParserOptionTape []
          (none :: some MachineCodeSymbol.done ::
            some MachineCodeSymbol.one :: right) }
  let final :
      TuringMachine.Configuration MachineCodeSymbol
        CodePrefixParserBranchState :=
    { state := CodePrefixParserBranchState.halt
      tape :=
        transitionListParserOptionTape [some MachineCodeSymbol.tick]
          (some MachineCodeSymbol.done ::
            some MachineCodeSymbol.one :: right) }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact
      TuringMachine.Computes.step
        (TuringMachine.Step.mk
          (write := some MachineCodeSymbol.one)
          (dir := Direction.left)
          (nextState := CodePrefixParserBranchState.successWriteDone)
          (by
          simp [codePrefixParserBranchMachine,
            transitionListParserOptionTape, Tape.read]))
        (TuringMachine.Computes.step
          (TuringMachine.Step.mk
            (write := some MachineCodeSymbol.done)
            (dir := Direction.left)
            (nextState := CodePrefixParserBranchState.successWriteTick)
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
  · simp [final, codePrefixParserBranchTruePrefix,
      transitionListParserOptionTape_normalizedOutput]

theorem codePrefixParserBranch_success_seek_symbol
    (leftRev : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (right : List (Option MachineCodeSymbol)) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.successSeekLeft
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (some current :: right) }
      (List.append codePrefixParserBranchTruePrefix
        (List.append leftRev.reverse
          (current :: right.filterMap (fun cell => cell)))) := by
  induction leftRev generalizing current right with
  | nil =>
      have hstep :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.successSeekLeft
              tape :=
                transitionListParserOptionTape ([] : List (Option MachineCodeSymbol))
                  (some current :: right) }
            { state := CodePrefixParserBranchState.successSeekLeft
              tape :=
                transitionListParserOptionTape []
                  (none :: some current :: right) } :=
        TuringMachine.Step.mk
          (write := some current)
          (dir := Direction.left)
          (nextState := CodePrefixParserBranchState.successSeekLeft)
          (by
          simp [codePrefixParserBranchMachine,
            transitionListParserOptionTape, Tape.read])
      rcases
          codePrefixParserBranch_success_boundary
            (some current :: right) with
        ⟨final, hcomp, hhalt, hout⟩
      refine ⟨final, ?_, hhalt, ?_⟩
      · exact TuringMachine.Computes.step hstep hcomp
      · simpa [codePrefixParserBranchTruePrefix] using hout
  | cons leftHead leftTail ih =>
      have hstep :
          TuringMachine.Step codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.successSeekLeft
              tape :=
                transitionListParserOptionTape
                  ((leftHead :: leftTail).map some)
                  (some current :: right) }
            { state := CodePrefixParserBranchState.successSeekLeft
              tape :=
                transitionListParserOptionTape (leftTail.map some)
                  (some leftHead :: some current :: right) } :=
        TuringMachine.Step.mk
          (write := some current)
          (dir := Direction.left)
          (nextState := CodePrefixParserBranchState.successSeekLeft)
          (by
          simp [codePrefixParserBranchMachine,
            transitionListParserOptionTape, Tape.read])
      rcases ih leftHead (some current :: right) with
        ⟨final, hcomp, hhalt, hout⟩
      refine ⟨final, ?_, hhalt, ?_⟩
      · exact TuringMachine.Computes.step hstep hcomp
      · simpa [List.append_assoc] using hout

theorem codePrefixParserBranch_success_from_clean_halt
    (leftRev rest : Word MachineCodeSymbol) :
    codePrefixParserBranchHaltsFromWithOutput
      { state :=
          CodePrefixParserBranchState.normalizer
            CodePrefixParserNormalizerState.halt
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (rest.map some) }
      (List.append codePrefixParserBranchTruePrefix
        (List.append leftRev.reverse rest)) := by
  cases leftRev with
  | nil =>
      cases rest with
      | nil =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state :=
                    CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ([] : List (Option MachineCodeSymbol)) [] }
                { state := CodePrefixParserBranchState.successSeekLeft
                  tape := transitionListParserOptionTape [] [none, none] } :=
            TuringMachine.Step.mk
              (write := none)
              (dir := Direction.left)
              (nextState :=
                CodePrefixParserBranchState.successSeekLeft)
              (by
                simp [codePrefixParserBranchMachine,
                  transitionListParserOptionTape, Tape.read])
          rcases codePrefixParserBranch_success_boundary [none] with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, ?_⟩
          · exact TuringMachine.Computes.step hstep hcomp
          · simpa using hout
      | cons head tail =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state :=
                    CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ([] : List (Option MachineCodeSymbol))
                      ((head :: tail).map some) }
                { state := CodePrefixParserBranchState.successSeekLeft
                  tape :=
                    transitionListParserOptionTape []
                      (none :: some head :: tail.map some) } :=
            TuringMachine.Step.mk
              (write := some head)
              (dir := Direction.left)
              (nextState :=
                CodePrefixParserBranchState.successSeekLeft)
              (by
                simp [codePrefixParserBranchMachine,
                  transitionListParserOptionTape, Tape.read])
          rcases
              codePrefixParserBranch_success_boundary
                (some head :: tail.map some) with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, ?_⟩
          · exact TuringMachine.Computes.step hstep hcomp
          · simpa [codePrefixParserNormalizer_filterMap_comp_some]
              using hout
  | cons leftHead leftTail =>
      cases rest with
      | nil =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state :=
                    CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ((leftHead :: leftTail).map some) [] }
                { state := CodePrefixParserBranchState.successSeekLeft
                  tape :=
                    transitionListParserOptionTape (leftTail.map some)
                      [some leftHead, none] } :=
            TuringMachine.Step.mk
              (write := none)
              (dir := Direction.left)
              (nextState :=
                CodePrefixParserBranchState.successSeekLeft)
              (by
                simp [codePrefixParserBranchMachine,
                  transitionListParserOptionTape, Tape.read])
          rcases
              codePrefixParserBranch_success_seek_symbol
                leftTail leftHead [none] with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, ?_⟩
          · exact TuringMachine.Computes.step hstep hcomp
          · simpa [List.append_assoc] using hout
      | cons head tail =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state :=
                    CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ((leftHead :: leftTail).map some)
                      ((head :: tail).map some) }
                { state := CodePrefixParserBranchState.successSeekLeft
                  tape :=
                    transitionListParserOptionTape (leftTail.map some)
                      (some leftHead :: some head :: tail.map some) } :=
            TuringMachine.Step.mk
              (write := some head)
              (dir := Direction.left)
              (nextState :=
                CodePrefixParserBranchState.successSeekLeft)
              (by
                simp [codePrefixParserBranchMachine,
                  transitionListParserOptionTape, Tape.read])
          rcases
              codePrefixParserBranch_success_seek_symbol
                leftTail leftHead (some head :: tail.map some) with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, ?_⟩
          · exact TuringMachine.Computes.step hstep hcomp
          · simpa [List.append_assoc,
              codePrefixParserNormalizer_filterMap_comp_some] using hout

theorem codePrefixParserBranch_success_from_clean_halt_options
    (leftRev : Word MachineCodeSymbol)
    (right : List (Option MachineCodeSymbol)) :
    codePrefixParserBranchHaltsFromWithOutput
      { state :=
          CodePrefixParserBranchState.normalizer
            CodePrefixParserNormalizerState.halt
        tape :=
          transitionListParserOptionTape (leftRev.map some) right }
      (List.append codePrefixParserBranchTruePrefix
        (List.append leftRev.reverse
          (right.filterMap (fun cell => cell)))) := by
  cases leftRev with
  | nil =>
      cases right with
      | nil =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state :=
                    CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ([] : List (Option MachineCodeSymbol)) [] }
                { state := CodePrefixParserBranchState.successSeekLeft
                  tape := transitionListParserOptionTape [] [none, none] } :=
            TuringMachine.Step.mk
              (write := none)
              (dir := Direction.left)
              (nextState :=
                CodePrefixParserBranchState.successSeekLeft)
              (by
                simp [codePrefixParserBranchMachine,
                  transitionListParserOptionTape, Tape.read])
          rcases codePrefixParserBranch_success_boundary [none] with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, ?_⟩
          · exact TuringMachine.Computes.step hstep hcomp
          · simpa using hout
      | cons cell suffix =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state :=
                    CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ([] : List (Option MachineCodeSymbol))
                      (cell :: suffix) }
                { state := CodePrefixParserBranchState.successSeekLeft
                  tape :=
                    transitionListParserOptionTape []
                      (none :: cell :: suffix) } :=
            TuringMachine.Step.mk
              (write := cell)
              (dir := Direction.left)
              (nextState :=
                CodePrefixParserBranchState.successSeekLeft)
              (by
                cases cell <;>
                  simp [codePrefixParserBranchMachine,
                    transitionListParserOptionTape, Tape.read])
          rcases
              codePrefixParserBranch_success_boundary
                (cell :: suffix) with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, ?_⟩
          · exact TuringMachine.Computes.step hstep hcomp
          · simpa using hout
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state :=
                    CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ((leftHead :: leftTail).map some) [] }
                { state := CodePrefixParserBranchState.successSeekLeft
                  tape :=
                    transitionListParserOptionTape (leftTail.map some)
                      [some leftHead, none] } :=
            TuringMachine.Step.mk
              (write := none)
              (dir := Direction.left)
              (nextState :=
                CodePrefixParserBranchState.successSeekLeft)
              (by
                simp [codePrefixParserBranchMachine,
                  transitionListParserOptionTape, Tape.read])
          rcases
              codePrefixParserBranch_success_seek_symbol
                leftTail leftHead [none] with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, ?_⟩
          · exact TuringMachine.Computes.step hstep hcomp
          · simpa [List.append_assoc] using hout
      | cons cell suffix =>
          have hstep :
              TuringMachine.Step codePrefixParserBranchMachine
                { state :=
                    CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      ((leftHead :: leftTail).map some)
                      (cell :: suffix) }
                { state := CodePrefixParserBranchState.successSeekLeft
                  tape :=
                    transitionListParserOptionTape (leftTail.map some)
                      (some leftHead :: cell :: suffix) } :=
            TuringMachine.Step.mk
              (write := cell)
              (dir := Direction.left)
              (nextState :=
                CodePrefixParserBranchState.successSeekLeft)
              (by
                cases cell <;>
                  simp [codePrefixParserBranchMachine,
                    transitionListParserOptionTape, Tape.read])
          rcases
              codePrefixParserBranch_success_seek_symbol
                leftTail leftHead (cell :: suffix) with
            ⟨final, hcomp, hhalt, hout⟩
          refine ⟨final, ?_, hhalt, ?_⟩
          · exact TuringMachine.Computes.step hstep hcomp
          · simpa [List.append_assoc] using hout

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

theorem codePrefixParserBranch_failure_nat_noBoundary
    {current : CodePrefixParserNormalizerState}
    (hnotHalt : current ≠ CodePrefixParserNormalizerState.halt)
    (hboundary :
      codePrefixParserBranchFailureNeedsBoundary current = false)
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
    (hstuck_empty :
      codePrefixParserNormalizerMachine.transition current none = none)
    (hstuck_bad :
      forall symbol : MachineCodeSymbol,
        symbol ≠ MachineCodeSymbol.tick ->
        symbol ≠ MachineCodeSymbol.done ->
          codePrefixParserNormalizerMachine.transition current
            (some symbol) = none)
    (leftRev tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  induction tokens generalizing leftRev with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_clean_stuck_noBoundary
          current hnotHalt hboundary leftRev [] (by
            simpa [transitionListParserOptionTape, Tape.read] using
              hstuck_empty)
  | cons symbol rest ih =>
      cases symbol with
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases htail : MachineDescription.decodeNat rest with
          | none =>
              have hstep :
                  TuringMachine.Step codePrefixParserBranchMachine
                    { state := CodePrefixParserBranchState.normalizer current
                      tape :=
                        transitionListParserOptionTape (leftRev.map some)
                          ((MachineCodeSymbol.tick :: rest).map some) }
                    { state := CodePrefixParserBranchState.normalizer current
                      tape :=
                        transitionListParserOptionTape
                          ((MachineCodeSymbol.tick :: leftRev).map some)
                          (rest.map some) } := by
                simpa using
                  codePrefixParserBranchMachine_step_of_normalizer_step
                    (htick (leftRev.map some) (rest.map some))
              rcases ih (MachineCodeSymbol.tick :: leftRev) htail with
                ⟨final, hcomp, hhalt, hout⟩
              exact
                ⟨final, TuringMachine.Computes.step hstep hcomp,
                  hhalt, hout⟩
          | some parsed =>
              simp [htail] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.header :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.header (by simp) (by simp))
      | transition =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.transition :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.transition (by simp) (by simp))
      | blank =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.blank :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.blank (by simp) (by simp))
      | zero =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.zero :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.zero (by simp) (by simp))
      | one =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.one :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.one (by simp) (by simp))
      | moveLeft =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.moveLeft :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveLeft (by simp) (by simp))
      | moveRight =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.moveRight :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveRight (by simp) (by simp))

theorem codePrefixParserBranch_failure_stateCount_noBoundary
    (leftRev tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.stateCount
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_noBoundary
    (by intro h; cases h)
    (by rfl)
    (by
      intro leftRev suffix
      exact
        codePrefixParserNormalizerMachine_step_keep_right
          (by simp [codePrefixParserNormalizerMachine,
            codePrefixParserNormalizerKeep]))
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol htick hdone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
    leftRev tokens hdecode

theorem codePrefixParserBranch_failure_startField_noBoundary
    (leftRev tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.startField
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_noBoundary
    (by intro h; cases h)
    (by rfl)
    (by
      intro leftRev suffix
      exact
        codePrefixParserNormalizerMachine_step_keep_right
          (by simp [codePrefixParserNormalizerMachine,
            codePrefixParserNormalizerKeep]))
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol htick hdone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
    leftRev tokens hdecode

theorem codePrefixParserBranch_failure_haltField_noBoundary
    (leftRev tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.haltField
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_noBoundary
    (by intro h; cases h)
    (by rfl)
    (by
      intro leftRev suffix
      exact
        codePrefixParserNormalizerMachine_step_keep_right
          (by simp [codePrefixParserNormalizerMachine,
            codePrefixParserNormalizerKeep]))
    (by simp [codePrefixParserNormalizerMachine])
      (by
        intro symbol htick hdone
        cases symbol <;>
          simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
    leftRev tokens hdecode

theorem codePrefixParserBranch_computes_nat_noBoundary
    {current next : CodePrefixParserNormalizerState}
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
    (leftRev tokens suffix : Word MachineCodeSymbol)
    (n : Nat)
    (hdecode : MachineDescription.decodeNat tokens = some (n, suffix)) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (tokens.map some) }
      { state := CodePrefixParserBranchState.normalizer next
        tape :=
          transitionListParserOptionTape
            ((List.append (MachineDescription.encodeNat n).reverse
              leftRev).map some)
            (suffix.map some) } := by
  have htokens :
      tokens = MachineDescription.encodeNatAppend n suffix :=
    MachineDescription.decodeNat_eq_some_encodeNatAppend hdecode
  have hnorm :=
    codePrefixParserNormalizer_computes_nat'
      current next htick hdone leftRev n suffix
  have hbranch :=
    codePrefixParserBranchMachine_computes_of_normalizer_computes hnorm
  simpa [htokens, codePrefixParserBranchLiftConfig,
    codePrefixParserNormalizerTape,
    transitionListParserTape_eq_optionTape_map,
    List.map_append, List.map_reverse] using hbranch

theorem codePrefixParserBranch_failure_nat_boundary
    {current : CodePrefixParserNormalizerState}
    (hboundary :
      codePrefixParserBranchFailureNeedsBoundary current = true)
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
    (hstuck_empty :
      codePrefixParserNormalizerMachine.transition current none = none)
    (hstuck_bad :
      forall symbol : MachineCodeSymbol,
        symbol ≠ MachineCodeSymbol.tick ->
        symbol ≠ MachineCodeSymbol.done ->
          codePrefixParserNormalizerMachine.transition current
            (some symbol) = none)
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  induction tokens generalizing leftSymbols with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_stuck_boundary
          current hboundary leftSymbols prefixLeft [] (by
            simpa [transitionListParserOptionTape, Tape.read] using
              hstuck_empty)
  | cons symbol rest ih =>
      cases symbol with
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases htail : MachineDescription.decodeNat rest with
          | none =>
              have hstep :
                  TuringMachine.Step codePrefixParserBranchMachine
                    { state := CodePrefixParserBranchState.normalizer current
                      tape :=
                        transitionListParserOptionTape
                          (List.append (leftSymbols.map some)
                            (none :: prefixLeft.map some))
                          ((MachineCodeSymbol.tick :: rest).map some) }
                    { state := CodePrefixParserBranchState.normalizer current
                      tape :=
                        transitionListParserOptionTape
                          (List.append
                            ((MachineCodeSymbol.tick :: leftSymbols).map
                              some)
                            (none :: prefixLeft.map some))
                          (rest.map some) } := by
                simpa [List.append_assoc] using
                  codePrefixParserBranchMachine_step_of_normalizer_step
                    (htick
                      (List.append (leftSymbols.map some)
                        (none :: prefixLeft.map some))
                      (rest.map some))
              rcases ih (MachineCodeSymbol.tick :: leftSymbols) htail with
                ⟨final, hcomp, hhalt, hout⟩
              exact
                ⟨final, TuringMachine.Computes.step hstep hcomp,
                  hhalt, hout⟩
          | some parsed =>
              simp [htail] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.header :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.header (by simp) (by simp))
      | transition =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.transition :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.transition (by simp) (by simp))
      | blank =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.blank :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.blank (by simp) (by simp))
      | zero =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.zero :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.zero (by simp) (by simp))
      | one =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.one :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.one (by simp) (by simp))
      | moveLeft =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.moveLeft :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveLeft (by simp) (by simp))
      | moveRight =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.moveRight :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveRight (by simp) (by simp))

theorem codePrefixParserBranch_failure_cell_boundary
    {current : CodePrefixParserNormalizerState}
    (hboundary :
      codePrefixParserBranchFailureNeedsBoundary current = true)
    (hstuck_empty :
      codePrefixParserNormalizerMachine.transition current none = none)
    (hstuck_bad :
      forall symbol : MachineCodeSymbol,
        symbol ≠ MachineCodeSymbol.blank ->
        symbol ≠ MachineCodeSymbol.zero ->
        symbol ≠ MachineCodeSymbol.one ->
          codePrefixParserNormalizerMachine.transition current
            (some symbol) = none)
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeCell tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  cases tokens with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_stuck_boundary
          current hboundary leftSymbols prefixLeft [] (by
            simpa [transitionListParserOptionTape, Tape.read] using
              hstuck_empty)
  | cons symbol rest =>
      cases symbol with
      | blank =>
          simp [MachineDescription.decodeCell] at hdecode
      | zero =>
          simp [MachineDescription.decodeCell] at hdecode
      | one =>
          simp [MachineDescription.decodeCell] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.header :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.header
                    (by simp) (by simp) (by simp))
      | transition =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.transition :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.transition
                    (by simp) (by simp) (by simp))
      | tick =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.tick :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.tick
                    (by simp) (by simp) (by simp))
      | done =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.done :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.done
                    (by simp) (by simp) (by simp))
      | moveLeft =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.moveLeft :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveLeft
                    (by simp) (by simp) (by simp))
      | moveRight =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.moveRight :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveRight
                    (by simp) (by simp) (by simp))

theorem codePrefixParserBranch_failure_direction_boundary
    {current : CodePrefixParserNormalizerState}
    (hboundary :
      codePrefixParserBranchFailureNeedsBoundary current = true)
    (hstuck_empty :
      codePrefixParserNormalizerMachine.transition current none = none)
    (hstuck_bad :
      forall symbol : MachineCodeSymbol,
        symbol ≠ MachineCodeSymbol.moveLeft ->
        symbol ≠ MachineCodeSymbol.moveRight ->
          codePrefixParserNormalizerMachine.transition current
            (some symbol) = none)
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeDirection tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  cases tokens with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_stuck_boundary
          current hboundary leftSymbols prefixLeft [] (by
            simpa [transitionListParserOptionTape, Tape.read] using
              hstuck_empty)
  | cons symbol rest =>
      cases symbol with
      | moveLeft =>
          simp [MachineDescription.decodeDirection] at hdecode
      | moveRight =>
          simp [MachineDescription.decodeDirection] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.header :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.header (by simp) (by simp))
      | transition =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.transition :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.transition
                    (by simp) (by simp))
      | tick =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.tick :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.tick (by simp) (by simp))
      | done =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.done :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.done (by simp) (by simp))
      | blank =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.blank :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.blank (by simp) (by simp))
      | zero =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.zero :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.zero (by simp) (by simp))
      | one =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.one :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.one (by simp) (by simp))

theorem codePrefixParserBranch_failure_sourceNat_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.sourceNat
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_boundary
    (current := CodePrefixParserNormalizerState.sourceNat)
    (by rfl)
    codePrefixParserNormalizerMachine_step_sourceNat_tick
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol htick hdone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
      leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_failure_seekCountDoneInitial_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          (CodePrefixParserNormalizerState.seekCountDone
            TransitionListParserMarker.initial)
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_boundary
    (current :=
      CodePrefixParserNormalizerState.seekCountDone
        TransitionListParserMarker.initial)
    (by rfl)
    codePrefixParserNormalizerMachine_step_seekCountDone_initial_tick
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol htick hdone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
    leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_failure_findInitialCount_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.findInitialCount
        tape :=
            transitionListParserOptionTape
              (List.append (leftSymbols.map some)
                (none :: prefixLeft.map some))
              (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  cases tokens with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_stuck_boundary
          CodePrefixParserNormalizerState.findInitialCount
          (by rfl) leftSymbols prefixLeft [] (by
            simp [codePrefixParserNormalizerMachine,
              transitionListParserOptionTape, Tape.read])
  | cons symbol rest =>
      cases symbol with
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases htail : MachineDescription.decodeNat rest with
          | none =>
              have hstep :
                  TuringMachine.Step codePrefixParserBranchMachine
                    { state := CodePrefixParserBranchState.normalizer
                        CodePrefixParserNormalizerState.findInitialCount
                      tape :=
                        transitionListParserOptionTape
                          (List.append (leftSymbols.map some)
                            (none :: prefixLeft.map some))
                          ((MachineCodeSymbol.tick :: rest).map some) }
                    { state := CodePrefixParserBranchState.normalizer
                        (CodePrefixParserNormalizerState.seekCountDone
                          TransitionListParserMarker.initial)
                      tape :=
                        transitionListParserOptionTape
                          (List.append
                            ((MachineCodeSymbol.blank :: leftSymbols).map
                              some)
                            (none :: prefixLeft.map some))
                          (rest.map some) } := by
                simpa [List.append_assoc] using
                  codePrefixParserBranchMachine_step_of_normalizer_step
                    (codePrefixParserNormalizerMachine_step_findInitialCount_tick
                      (List.append (leftSymbols.map some)
                        (none :: prefixLeft.map some))
                      (rest.map some))
              rcases
                  codePrefixParserBranch_failure_seekCountDoneInitial_boundary
                    (MachineCodeSymbol.blank :: leftSymbols)
                    prefixLeft rest htail with
                ⟨final, hcomp, hhalt, hout⟩
              exact
                ⟨final, TuringMachine.Computes.step hstep hcomp,
                  hhalt, hout⟩
          | some parsed =>
              simp [htail] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.header :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | transition =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.transition :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | blank =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.blank :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | zero =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.zero :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | one =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.one :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | moveLeft =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.moveLeft :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | moveRight =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.moveRight :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])

theorem codePrefixParserBranch_failure_targetNat_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.targetNat
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_boundary
    (current := CodePrefixParserNormalizerState.targetNat)
    (by rfl)
    codePrefixParserNormalizerMachine_step_targetNat_tick
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol htick hdone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
    leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_failure_readCell_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeCell tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.readCell
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_cell_boundary
    (current := CodePrefixParserNormalizerState.readCell)
    (by rfl)
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol hblank hzero hone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at hblank hzero hone ⊢)
    leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_failure_writeCell_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeCell tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.writeCell
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_cell_boundary
    (current := CodePrefixParserNormalizerState.writeCell)
    (by rfl)
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol hblank hzero hone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at hblank hzero hone ⊢)
    leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_failure_moveField_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeDirection tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.moveField
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_direction_boundary
    (current := CodePrefixParserNormalizerState.moveField)
    (by rfl)
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol hleft hright
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at hleft hright ⊢)
    leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_computes_needTransition_transition
    (leftSymbols prefixLeft suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            ((MachineCodeSymbol.transition :: suffix).map some) }
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.sourceNat
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineCodeSymbol.transition :: leftSymbols).map some)
              (none :: prefixLeft.map some))
            (suffix.map some) } := by
  simpa [List.append_assoc] using
    codePrefixParserBranchMachine_computes_of_normalizer_computes
      (codePrefixParserNormalizerMachine_computes_needTransition
        (List.append (leftSymbols.map some)
          (none :: prefixLeft.map some))
        suffix)

theorem codePrefixParserBranch_computes_nat_boundary
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
    (leftSymbols prefixLeft tokens suffix : Word MachineCodeSymbol)
    (n : Nat)
    (hdecode : MachineDescription.decodeNat tokens = some (n, suffix)) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      { state := CodePrefixParserBranchState.normalizer next
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append (MachineDescription.encodeNat n).reverse
                leftSymbols).map some)
              (none :: prefixLeft.map some))
            (suffix.map some) } := by
  have htokens :
      tokens = MachineDescription.encodeNatAppend n suffix :=
    MachineDescription.decodeNat_eq_some_encodeNatAppend hdecode
  have hcomp :=
    codePrefixParserNormalizerMachine_computes_nat_option
      htick hdone
      (List.append (leftSymbols.map some)
        (none :: prefixLeft.map some))
      n suffix
  simpa [htokens, List.map_append, List.map_reverse,
    List.append_assoc] using
    codePrefixParserBranchMachine_computes_of_normalizer_computes hcomp

theorem codePrefixParserBranch_computes_readCell_boundary
    (leftSymbols prefixLeft tokens suffix : Word MachineCodeSymbol)
    (cell : Option Bool)
    (hdecode : MachineDescription.decodeCell tokens = some (cell, suffix)) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.readCell
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.writeCell
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append (MachineDescription.encodeCell cell).reverse
                leftSymbols).map some)
              (none :: prefixLeft.map some))
            (suffix.map some) } := by
  have htokens :
      tokens = MachineDescription.encodeCellAppend cell suffix :=
    MachineDescription.decodeCell_eq_some_encodeCellAppend hdecode
  have hcomp :=
    codePrefixParserNormalizerMachine_computes_readCell
      cell
      (List.append (leftSymbols.map some)
        (none :: prefixLeft.map some))
      suffix
  simpa [htokens, List.map_append, List.map_reverse,
    List.append_assoc] using
    codePrefixParserBranchMachine_computes_of_normalizer_computes hcomp

theorem codePrefixParserBranch_computes_writeCell_boundary
    (leftSymbols prefixLeft tokens suffix : Word MachineCodeSymbol)
    (cell : Option Bool)
    (hdecode : MachineDescription.decodeCell tokens = some (cell, suffix)) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.writeCell
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.moveField
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append (MachineDescription.encodeCell cell).reverse
                leftSymbols).map some)
              (none :: prefixLeft.map some))
            (suffix.map some) } := by
  have htokens :
      tokens = MachineDescription.encodeCellAppend cell suffix :=
    MachineDescription.decodeCell_eq_some_encodeCellAppend hdecode
  have hcomp :=
    codePrefixParserNormalizerMachine_computes_writeCell
      cell
      (List.append (leftSymbols.map some)
        (none :: prefixLeft.map some))
      suffix
  simpa [htokens, List.map_append, List.map_reverse,
    List.append_assoc] using
    codePrefixParserBranchMachine_computes_of_normalizer_computes hcomp

theorem codePrefixParserBranch_computes_moveField_boundary
    (leftSymbols prefixLeft tokens suffix : Word MachineCodeSymbol)
    (dir : Direction)
    (hdecode :
      MachineDescription.decodeDirection tokens = some (dir, suffix)) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.moveField
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.targetNat
        tape :=
          transitionListParserOptionTape
            (List.append
              ((List.append (MachineDescription.encodeDirection dir).reverse
                leftSymbols).map some)
              (none :: prefixLeft.map some))
            (suffix.map some) } := by
  have htokens :
      tokens = MachineDescription.encodeDirectionAppend dir suffix :=
    MachineDescription.decodeDirection_eq_some_encodeDirectionAppend hdecode
  have hcomp :=
    codePrefixParserNormalizerMachine_computes_moveField
      dir
      (List.append (leftSymbols.map some)
        (none :: prefixLeft.map some))
      suffix
  simpa [htokens, List.map_append, List.map_reverse,
    List.append_assoc] using
    codePrefixParserBranchMachine_computes_of_normalizer_computes hcomp

theorem codePrefixParserBranch_failure_transitionRecord_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeTransition tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  cases tokens with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_stuck_boundary
          CodePrefixParserNormalizerState.needTransition
          (by rfl) leftSymbols prefixLeft [] (by
            simp [codePrefixParserNormalizerMachine,
              transitionListParserOptionTape, Tape.read])
  | cons symbol rest =>
      cases symbol with
      | transition =>
          simp [MachineDescription.decodeTransition] at hdecode
          let afterTransition : Word MachineCodeSymbol :=
            MachineCodeSymbol.transition :: leftSymbols
          have hneed :=
            codePrefixParserBranch_computes_needTransition_transition
              leftSymbols prefixLeft rest
          cases hsource : MachineDescription.decodeNat rest with
          | none =>
              rcases
                  codePrefixParserBranch_failure_sourceNat_boundary
                    afterTransition prefixLeft rest hsource with
                ⟨final, hcomp, hhalt, hout⟩
              exact
                ⟨final, TuringMachine.computes_trans hneed hcomp,
                  hhalt, hout⟩
          | some parsedSource =>
              rcases parsedSource with ⟨source, restAfterSource⟩
              simp [hsource] at hdecode
              let afterSource : Word MachineCodeSymbol :=
                List.append (MachineDescription.encodeNat source).reverse
                  afterTransition
              have hsourceComp :=
                codePrefixParserBranch_computes_nat_boundary
                  codePrefixParserNormalizerMachine_step_sourceNat_tick
                  codePrefixParserNormalizerMachine_step_sourceNat_done
                  afterTransition prefixLeft rest restAfterSource
                  source hsource
              cases hread : MachineDescription.decodeCell restAfterSource with
              | none =>
                  rcases
                      codePrefixParserBranch_failure_readCell_boundary
                        afterSource prefixLeft restAfterSource hread with
                    ⟨final, hcomp, hhalt, hout⟩
                  refine ⟨final, ?_, hhalt, hout⟩
                  exact
                    TuringMachine.computes_trans hneed
                      (TuringMachine.computes_trans
                          (by
                            simpa [afterSource, List.map_append,
                              List.map_reverse, List.append_assoc] using
                              hsourceComp)
                        hcomp)
              | some parsedRead =>
                  rcases parsedRead with ⟨read, restAfterRead⟩
                  simp [hread] at hdecode
                  let afterRead : Word MachineCodeSymbol :=
                    List.append (MachineDescription.encodeCell read).reverse
                      afterSource
                  have hreadComp :=
                    codePrefixParserBranch_computes_readCell_boundary
                      afterSource prefixLeft restAfterSource
                      restAfterRead read hread
                  cases hwrite :
                      MachineDescription.decodeCell restAfterRead with
                  | none =>
                      rcases
                          codePrefixParserBranch_failure_writeCell_boundary
                            afterRead prefixLeft restAfterRead hwrite with
                        ⟨final, hcomp, hhalt, hout⟩
                      refine ⟨final, ?_, hhalt, hout⟩
                      exact
                        TuringMachine.computes_trans hneed
                          (TuringMachine.computes_trans
                              (by
                                simpa [afterSource, List.map_append,
                                  List.map_reverse, List.append_assoc] using
                                  hsourceComp)
                              (TuringMachine.computes_trans
                                (by
                                  simpa [afterRead, afterSource,
                                    List.map_append, List.map_reverse,
                                    List.append_assoc] using hreadComp)
                                hcomp))
                  | some parsedWrite =>
                      rcases parsedWrite with ⟨write, restAfterWrite⟩
                      simp [hwrite] at hdecode
                      let afterWrite : Word MachineCodeSymbol :=
                        List.append
                          (MachineDescription.encodeCell write).reverse
                          afterRead
                      have hwriteComp :=
                        codePrefixParserBranch_computes_writeCell_boundary
                          afterRead prefixLeft restAfterRead
                          restAfterWrite write hwrite
                      cases hmove :
                          MachineDescription.decodeDirection
                            restAfterWrite with
                      | none =>
                          rcases
                              codePrefixParserBranch_failure_moveField_boundary
                                afterWrite prefixLeft restAfterWrite
                                hmove with
                            ⟨final, hcomp, hhalt, hout⟩
                          refine ⟨final, ?_, hhalt, hout⟩
                          exact
                            TuringMachine.computes_trans hneed
                              (TuringMachine.computes_trans
                                  (by
                                    simpa [afterSource, List.map_append,
                                      List.map_reverse,
                                      List.append_assoc] using hsourceComp)
                                  (TuringMachine.computes_trans
                                    (by
                                      simpa [afterRead, afterSource,
                                        List.map_append, List.map_reverse,
                                        List.append_assoc] using hreadComp)
                                    (TuringMachine.computes_trans
                                      (by
                                        simpa [afterWrite, afterRead,
                                          afterSource, List.map_append,
                                          List.map_reverse,
                                          List.append_assoc] using
                                          hwriteComp)
                                    hcomp)))
                      | some parsedMove =>
                          rcases parsedMove with ⟨move, restAfterMove⟩
                          simp [hmove] at hdecode
                          let afterMove : Word MachineCodeSymbol :=
                            List.append
                              (MachineDescription.encodeDirection move).reverse
                              afterWrite
                          have hmoveComp :=
                            codePrefixParserBranch_computes_moveField_boundary
                              afterWrite prefixLeft restAfterWrite
                              restAfterMove move hmove
                          cases htarget :
                              MachineDescription.decodeNat
                                restAfterMove with
                          | none =>
                              rcases
                                  codePrefixParserBranch_failure_targetNat_boundary
                                    afterMove prefixLeft restAfterMove
                                    htarget with
                                ⟨final, hcomp, hhalt, hout⟩
                              refine ⟨final, ?_, hhalt, hout⟩
                              exact
                                TuringMachine.computes_trans hneed
                                  (TuringMachine.computes_trans
                                    (by
                                        simpa [afterSource, List.map_append,
                                          List.map_reverse,
                                          List.append_assoc] using
                                          hsourceComp)
                                      (TuringMachine.computes_trans
                                        (by
                                          simpa [afterRead, afterSource,
                                            List.map_append,
                                            List.map_reverse,
                                            List.append_assoc] using hreadComp)
                                        (TuringMachine.computes_trans
                                          (by
                                            simpa [afterWrite, afterRead,
                                              afterSource, List.map_append,
                                              List.map_reverse,
                                              List.append_assoc] using
                                              hwriteComp)
                                          (TuringMachine.computes_trans
                                            (by
                                              simpa [afterMove, afterWrite,
                                                afterRead, afterSource,
                                                List.map_append,
                                                List.map_reverse,
                                                List.append_assoc] using
                                                hmoveComp)
                                            hcomp))))
                          | some parsedTarget =>
                              rcases parsedTarget with
                                ⟨target, restAfterTarget⟩
                              simp [htarget] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.header :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | tick =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.tick :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | done =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.done :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | blank =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.blank :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | zero =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.zero :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | one =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.one :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | moveLeft =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.moveLeft :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | moveRight =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.needTransition
              (by rfl) leftSymbols prefixLeft
                (MachineCodeSymbol.moveRight :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])

theorem codePrefixParserBranch_failure_decodeTransitions_needTransition_boundary
    (count : Nat)
    (prefixLeft : Word MachineCodeSymbol)
    (blanks : Nat)
    (pre tokens : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (hdecode :
      MachineDescription.decodeTransitions (count + 1) tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              (prefixLeft.map some) blanks count pre)
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  induction count generalizing blanks pre tokens with
  | zero =>
      let leftSymbols : Word MachineCodeSymbol :=
        (List.append
          (List.append
            (List.replicate blanks MachineCodeSymbol.blank)
            (MachineDescription.encodeNat 0))
          pre).reverse
      have hleft :
          codePrefixParserNormalizerMarkedContextLeft
              (prefixLeft.map some) blanks 0 pre =
            List.append (leftSymbols.map some)
              (none :: prefixLeft.map some) := by
        simp [leftSymbols, codePrefixParserNormalizerMarkedContextLeft,
          List.reverse_append, List.map_append, List.map_reverse,
          List.append_assoc]
      cases htransition : MachineDescription.decodeTransition tokens with
      | none =>
          rcases
              codePrefixParserBranch_failure_transitionRecord_boundary
                leftSymbols prefixLeft tokens htransition with
            ⟨final, hcomp, hhalt, hout⟩
          exact
            ⟨final, by simpa [hleft] using hcomp, hhalt, hout⟩
      | some parsed =>
          simp [MachineDescription.decodeTransitions, htransition] at hdecode
  | succ count ih =>
      let leftSymbols : Word MachineCodeSymbol :=
        (List.append
          (List.append
            (List.replicate blanks MachineCodeSymbol.blank)
            (MachineDescription.encodeNat (count + 1)))
          pre).reverse
      have hleft :
          codePrefixParserNormalizerMarkedContextLeft
              (prefixLeft.map some) blanks (count + 1) pre =
            List.append (leftSymbols.map some)
              (none :: prefixLeft.map some) := by
        simp [leftSymbols, codePrefixParserNormalizerMarkedContextLeft,
          List.reverse_append, List.map_append, List.map_reverse,
          List.append_assoc]
      cases htransition : MachineDescription.decodeTransition tokens with
      | none =>
          rcases
              codePrefixParserBranch_failure_transitionRecord_boundary
                leftSymbols prefixLeft tokens htransition with
            ⟨final, hcomp, hhalt, hout⟩
          exact
            ⟨final, by simpa [hleft] using hcomp, hhalt, hout⟩
      | some parsed =>
          rcases parsed with ⟨transition, restTokens⟩
          have htail :
              MachineDescription.decodeTransitions (count + 1)
                restTokens = none := by
            have hdecodeTail :
                (match
                    MachineDescription.decodeTransitions (count + 1)
                      restTokens with
                  | none => none
                  | some (transitions, suffix) =>
                      some (transition :: transitions, suffix)) = none := by
              simpa [MachineDescription.decodeTransitions, htransition] using
                hdecode
            cases htail :
                MachineDescription.decodeTransitions (count + 1)
                  restTokens with
            | none =>
                rfl
            | some parsedTail =>
                rw [htail] at hdecodeTail
                cases hdecodeTail
          let pre' : Word MachineCodeSymbol :=
            List.append pre (MachineDescription.encodeTransition transition)
          have htokens :
              tokens =
                MachineDescription.encodeTransitionAppend transition
                  restTokens :=
            MachineDescription.decodeTransition_eq_some_encodeTransitionAppend
              htransition
          have hparseNorm :=
            codePrefixParserNormalizerMachine_computes_transition
              transition
              (codePrefixParserNormalizerMarkedContextLeft
                (prefixLeft.map some) blanks (count + 1) pre)
              restTokens
          have hparse :
              TuringMachine.Computes codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.normalizer
                    CodePrefixParserNormalizerState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        (prefixLeft.map some) blanks (count + 1) pre)
                      (tokens.map some) }
                { state := CodePrefixParserBranchState.normalizer
                    CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        (prefixLeft.map some) blanks (count + 1) pre')
                      (restTokens.map some) } := by
            have hbranch :=
              codePrefixParserBranchMachine_computes_of_normalizer_computes
                hparseNorm
            simpa [htokens, pre', codePrefixParserNormalizerMarkedContextLeft,
              MachineDescription.encodeTransition,
              MachineDescription.encodeTransitionAppend,
              MachineDescription.encodeNatAppend,
              MachineDescription.encodeCellAppend,
              MachineDescription.encodeDirectionAppend,
              List.reverse_append, List.map_append, List.map_reverse,
              List.map_replicate, List.append_assoc] using hbranch
          have htransitionNoHeader :
              transitionListParserNoHeader
                (MachineDescription.encodeTransition transition) := by
            simpa [MachineDescription.encodeTransition] using
              transitionListParser_encodeTransitionAppend_noHeader
                transition (suffix := []) (by
                  intro symbol hmem
                  simp at hmem)
          have hpre' : transitionListParserNoHeader pre' :=
            transitionListParserNoHeader_append hpre htransitionNoHeader
          have hmark :
              TuringMachine.Computes codePrefixParserBranchMachine
                { state := CodePrefixParserBranchState.normalizer
                    CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        (prefixLeft.map some) blanks (count + 1) pre')
                      (restTokens.map some) }
                { state := CodePrefixParserBranchState.normalizer
                    CodePrefixParserNormalizerState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        (prefixLeft.map some) (blanks + 1) count pre')
                      (restTokens.map some) } := by
            cases restTokens with
            | nil =>
                have hnorm :=
                  codePrefixParserNormalizerMachine_computes_markPosition_context_empty_to_needTransition
                    (prefixLeft.map some) blanks count pre' hpre'
                have hbranch :=
                  codePrefixParserBranchMachine_computes_of_normalizer_computes
                    hnorm
                simpa [transitionListParserOptionTape] using hbranch
            | cons symbol suffix =>
                have hnorm :=
                  codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition
                    (prefixLeft.map some) blanks count pre' hpre'
                    symbol suffix
                exact
                  codePrefixParserBranchMachine_computes_of_normalizer_computes
                    hnorm
          rcases ih (blanks + 1) pre' restTokens hpre' htail with
            ⟨final, hcomp, hhalt, hout⟩
          exact
            ⟨final,
              TuringMachine.computes_trans hparse
                (TuringMachine.computes_trans hmark hcomp),
              hhalt, hout⟩

theorem codePrefixParserBranch_failure_decodeTransitions_findInitialCount
    (count : Nat)
    (prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode :
      MachineDescription.decodeTransitions count tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.findInitialCount
        tape :=
          transitionListParserOptionTape
            (none :: prefixLeft.map some)
            ((MachineDescription.encodeNatAppend count tokens).map some) }
      codePrefixParserBranchFalseOutput := by
  cases count with
  | zero =>
      simp [MachineDescription.decodeTransitions] at hdecode
  | succ count =>
      have hcountNorm :=
        codePrefixParserNormalizerMachine_computes_findInitialCount_succ
          count (none :: prefixLeft.map some) tokens
      have hcount :
          TuringMachine.Computes codePrefixParserBranchMachine
            { state := CodePrefixParserBranchState.normalizer
                CodePrefixParserNormalizerState.findInitialCount
              tape :=
                transitionListParserOptionTape
                  (none :: prefixLeft.map some)
                  ((MachineDescription.encodeNatAppend (count + 1)
                    tokens).map some) }
            { state := CodePrefixParserBranchState.normalizer
                CodePrefixParserNormalizerState.needTransition
              tape :=
                transitionListParserOptionTape
                  (codePrefixParserNormalizerMarkedContextLeft
                    (prefixLeft.map some) 1 count [])
                  (tokens.map some) } := by
        have hbranch :=
          codePrefixParserBranchMachine_computes_of_normalizer_computes
            hcountNorm
        simpa [codePrefixParserNormalizerMarkedContextLeft,
          MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
          List.reverse_append, List.map_append, List.map_reverse,
          List.map_replicate, List.append_assoc] using hbranch
      have hpre : transitionListParserNoHeader ([] : Word MachineCodeSymbol) := by
        simp [transitionListParserNoHeader]
      rcases
          codePrefixParserBranch_failure_decodeTransitions_needTransition_boundary
            count prefixLeft 1 [] tokens hpre
            (by simpa [Nat.succ_eq_add_one] using hdecode) with
        ⟨final, hcomp, hhalt, hout⟩
      exact
        ⟨final, TuringMachine.computes_trans hcount hcomp, hhalt, hout⟩

theorem codePrefixParserBranch_failure_decodeDescriptionPrefix
    (tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeDescriptionPrefix tokens = none) :
    TuringMachine.HaltsWithOutput codePrefixParserBranchMachine tokens
      codePrefixParserBranchFalseOutput := by
  have hfrom :
      codePrefixParserBranchHaltsFromWithOutput
        { state := CodePrefixParserBranchState.normalizer
            CodePrefixParserNormalizerState.needHeader
          tape := transitionListParserOptionTape [] (tokens.map some) }
        codePrefixParserBranchFalseOutput := by
    cases tokens with
    | nil =>
        exact
          codePrefixParserBranch_failure_from_clean_stuck_noBoundary
            CodePrefixParserNormalizerState.needHeader
            (by intro h; cases h)
            (by rfl) [] [] (by
              simp [codePrefixParserNormalizerMachine,
                transitionListParserOptionTape, Tape.read])
    | cons symbol rest =>
        cases symbol with
        | header =>
            simp [MachineDescription.decodeDescriptionPrefix] at hdecode
            let leftAfterHeader : Word MachineCodeSymbol :=
              [MachineCodeSymbol.header]
            have hheaderStep :
                TuringMachine.Step codePrefixParserBranchMachine
                  { state := CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.needHeader
                    tape :=
                      transitionListParserOptionTape []
                        ((MachineCodeSymbol.header :: rest).map some) }
                  { state := CodePrefixParserBranchState.normalizer
                      CodePrefixParserNormalizerState.stateCount
                    tape :=
                      transitionListParserOptionTape
                        (leftAfterHeader.map some)
                        (rest.map some) } := by
              have hstep :=
                codePrefixParserBranchMachine_step_of_normalizer_step
                  (codePrefixParserNormalizer_step_header
                    ([] : Word MachineCodeSymbol) rest)
              simpa [leftAfterHeader, codePrefixParserBranchLiftConfig,
                codePrefixParserNormalizerTape,
                transitionListParserTape_eq_optionTape_map] using hstep
            cases hstate : MachineDescription.decodeNat rest with
            | none =>
                rcases
                    codePrefixParserBranch_failure_stateCount_noBoundary
                      leftAfterHeader rest hstate with
                  ⟨final, hcomp, hhalt, hout⟩
                exact
                  ⟨final, TuringMachine.Computes.step hheaderStep hcomp,
                    hhalt, hout⟩
            | some parsedState =>
                rcases parsedState with ⟨stateCount, restAfterState⟩
                simp [hstate] at hdecode
                let leftAfterState : Word MachineCodeSymbol :=
                  List.append (MachineDescription.encodeNat stateCount).reverse
                    leftAfterHeader
                have hstateComp :=
                  codePrefixParserBranch_computes_nat_noBoundary
                    codePrefixParserNormalizer_step_tick_stateCount
                    codePrefixParserNormalizer_step_done_stateCount
                    leftAfterHeader rest restAfterState stateCount hstate
                cases hstart :
                    MachineDescription.decodeNat restAfterState with
                | none =>
                    rcases
                        codePrefixParserBranch_failure_startField_noBoundary
                          leftAfterState restAfterState hstart with
                      ⟨final, hcomp, hhalt, hout⟩
                    exact
                      ⟨final,
                        TuringMachine.Computes.step hheaderStep
                          (TuringMachine.computes_trans
                            (by simpa [leftAfterState] using hstateComp)
                            hcomp),
                        hhalt, hout⟩
                | some parsedStart =>
                    rcases parsedStart with ⟨start, restAfterStart⟩
                    simp [hstart] at hdecode
                    let leftAfterStart : Word MachineCodeSymbol :=
                      List.append (MachineDescription.encodeNat start).reverse
                        leftAfterState
                    have hstartComp :=
                      codePrefixParserBranch_computes_nat_noBoundary
                        codePrefixParserNormalizer_step_tick_startField
                        codePrefixParserNormalizer_step_done_startField
                        leftAfterState restAfterState restAfterStart
                        start hstart
                    cases hhaltNat :
                        MachineDescription.decodeNat restAfterStart with
                    | none =>
                        rcases
                            codePrefixParserBranch_failure_haltField_noBoundary
                              leftAfterStart restAfterStart hhaltNat with
                          ⟨final, hcomp, hhalt, hout⟩
                        exact
                          ⟨final,
                            TuringMachine.Computes.step hheaderStep
                              (TuringMachine.computes_trans
                                (by simpa [leftAfterState] using hstateComp)
                                  (TuringMachine.computes_trans
                                    (by
                                      simpa [leftAfterStart,
                                        leftAfterState, List.map_append,
                                        List.map_reverse,
                                        List.append_assoc] using
                                        hstartComp)
                                  hcomp)),
                            hhalt, hout⟩
                    | some parsedHalt =>
                        rcases parsedHalt with ⟨halt, restAfterHalt⟩
                        simp [hhaltNat] at hdecode
                        let D0 : MachineDescription :=
                          { stateCount := stateCount
                            start := start
                            halt := halt
                            transitions := [] }
                        let headerPrefixLeft : Word MachineCodeSymbol :=
                          List.append
                            (List.replicate halt MachineCodeSymbol.tick)
                            (List.append
                              (MachineDescription.encodeNat start).reverse
                              (List.append
                                (MachineDescription.encodeNat
                                  stateCount).reverse
                                [MachineCodeSymbol.header]))
                        have hmarked :
                            codePrefixParserNormalizerMarkedHeaderLeft D0 =
                              none :: headerPrefixLeft.map some := by
                          simp [D0, headerPrefixLeft,
                            codePrefixParserNormalizerMarkedHeaderLeft,
                              codePrefixParserNormalizerMarkedNatReverse_eq,
                              List.map_append]
                        have hhaltTokens :
                            restAfterStart =
                              MachineDescription.encodeNatAppend halt
                                restAfterHalt :=
                          MachineDescription.decodeNat_eq_some_encodeNatAppend
                            hhaltNat
                        have hhaltNorm :=
                          codePrefixParserNormalizerMachine_computes_haltField_marked
                            leftAfterStart halt restAfterHalt
                        have hhaltComp :
                            TuringMachine.Computes
                              codePrefixParserBranchMachine
                              { state :=
                                  CodePrefixParserBranchState.normalizer
                                    CodePrefixParserNormalizerState.haltField
                                tape :=
                                  transitionListParserOptionTape
                                    (leftAfterStart.map some)
                                    (restAfterStart.map some) }
                              { state :=
                                  CodePrefixParserBranchState.normalizer
                                    CodePrefixParserNormalizerState.findInitialCount
                                tape :=
                                  transitionListParserOptionTape
                                    (codePrefixParserNormalizerMarkedHeaderLeft
                                      D0)
                                    (restAfterHalt.map some) } := by
                          have hbranch :=
                            codePrefixParserBranchMachine_computes_of_normalizer_computes
                              hhaltNorm
                          exact
                            by
                              simpa [hhaltTokens, D0, leftAfterStart,
                                leftAfterState, leftAfterHeader,
                                codePrefixParserNormalizerMarkedHeaderLeft,
                                codePrefixParserNormalizerMarkedNatReverse_eq,
                                codePrefixParserBranchLiftConfig,
                                codePrefixParserNormalizerTape,
                                transitionListParserTape_eq_optionTape_map,
                                List.map_append, List.map_reverse,
                                List.append_assoc] using hbranch
                        have hprefixComp :
                            TuringMachine.Computes
                              codePrefixParserBranchMachine
                              { state :=
                                  CodePrefixParserBranchState.normalizer
                                    CodePrefixParserNormalizerState.needHeader
                                tape :=
                                  transitionListParserOptionTape []
                                    ((MachineCodeSymbol.header ::
                                      rest).map some) }
                              { state :=
                                  CodePrefixParserBranchState.normalizer
                                    CodePrefixParserNormalizerState.findInitialCount
                                tape :=
                                  transitionListParserOptionTape
                                    (codePrefixParserNormalizerMarkedHeaderLeft
                                      D0)
                                    (restAfterHalt.map some) } :=
                          TuringMachine.Computes.step hheaderStep
                            (TuringMachine.computes_trans
                              (by simpa [leftAfterState] using hstateComp)
                                (TuringMachine.computes_trans
                                  (by
                                    simpa [leftAfterStart,
                                      leftAfterState, List.map_append,
                                      List.map_reverse,
                                      List.append_assoc] using
                                      hstartComp)
                                hhaltComp))
                        cases hcount :
                            MachineDescription.decodeNat restAfterHalt with
                        | none =>
                            rcases
                                codePrefixParserBranch_failure_findInitialCount_boundary
                                  [] headerPrefixLeft restAfterHalt hcount with
                              ⟨final, hcomp, hhalt, hout⟩
                            exact
                              ⟨final,
                                TuringMachine.computes_trans hprefixComp
                                  (by simpa [hmarked] using hcomp),
                                hhalt, hout⟩
                        | some parsedCount =>
                            rcases parsedCount with
                              ⟨transitionCount, restAfterCount⟩
                            simp [hcount] at hdecode
                            cases htrans :
                                MachineDescription.decodeTransitions
                                  transitionCount restAfterCount with
                            | none =>
                                have hcountTokens :
                                    restAfterHalt =
                                      MachineDescription.encodeNatAppend
                                        transitionCount restAfterCount :=
                                  MachineDescription.decodeNat_eq_some_encodeNatAppend
                                    hcount
                                rcases
                                    codePrefixParserBranch_failure_decodeTransitions_findInitialCount
                                      transitionCount headerPrefixLeft
                                      restAfterCount htrans with
                                  ⟨final, hcomp, hhalt, hout⟩
                                exact
                                  ⟨final,
                                    TuringMachine.computes_trans hprefixComp
                                      (by
                                        simpa [hmarked, hcountTokens] using
                                          hcomp),
                                    hhalt, hout⟩
                            | some parsedTransitions =>
                                simp [htrans] at hdecode
        | tick =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.tick :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | done =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.done :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | transition =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.transition :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | blank =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.blank :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | zero =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.zero :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | one =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.one :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | moveLeft =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.moveLeft :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
        | moveRight =>
            exact
              codePrefixParserBranch_failure_from_clean_stuck_noBoundary
                CodePrefixParserNormalizerState.needHeader
                (by intro h; cases h)
                (by rfl) [] (MachineCodeSymbol.moveRight :: rest) (by
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read])
  rcases hfrom with ⟨final, hcomp, hhalt, hout⟩
  exact
    ⟨final,
      by
        simpa [TuringMachine.initial, codePrefixParserBranchMachine,
          transitionListParserOptionTape_nil_eq_input] using hcomp,
      hhalt, hout⟩

end Computability
end FoC
