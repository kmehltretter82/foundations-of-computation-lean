import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Soundness.Final
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

end Computability
end FoC
