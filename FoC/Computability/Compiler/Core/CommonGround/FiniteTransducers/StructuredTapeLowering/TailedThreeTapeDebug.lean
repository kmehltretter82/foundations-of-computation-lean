import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ThreeTapeHelpers

set_option doc.verso true

/-!
# Tailed three-tape structured debugger

This module provides a small opt-in debug layer for lowerer-facing
three-logical-tape machines whose primary payload lives on tape 0.  It wraps the
generic structured debugger with views that expose the source tape as a left
prefix plus the head/right live tail, while keeping scratch and work tapes
visible enough to catch accidental mutations.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape

private def wordDebugString (w : Word Bool) : String :=
  reprStr (show List Bool from w)

def sourceTape (c : Configuration) : Tape Bool :=
  Description.tapeAt c.tapes 0

def scratchTape (c : Configuration) : Tape Bool :=
  Description.tapeAt c.tapes 1

def workTape (c : Configuration) : Tape Bool :=
  Description.tapeAt c.tapes 2

/--
A tape view tailored to live-tail constructions.

{lit}`leftBits` is the visible prefix to the left of the head, in natural
left-to-right order.  {lit}`headRightBits` is the nonblank live tail starting
at the head and continuing rightward.
-/
structure TailedTapeView where
  leftCells : List (Option Bool)
  leftBits : Word Bool
  head : Option Bool
  rightCells : List (Option Bool)
  headRightCells : List (Option Bool)
  headRightBits : Word Bool
  cells : List (Option Bool)
  normalizedOutput : Word Bool
deriving DecidableEq

def tailedTapeView (T : Tape Bool) : TailedTapeView where
  leftCells := T.left.reverse
  leftBits := T.left.reverse.filterMap (fun cell => cell)
  head := T.head
  rightCells := T.right
  headRightCells := T.head :: T.right
  headRightBits := (T.head :: T.right).filterMap (fun cell => cell)
  cells := Tape.cells T
  normalizedOutput := Tape.normalizedOutput T

/-- Compact summary of a non-primary tape. -/
structure AuxiliaryTapeView where
  head : Option Bool
  cells : List (Option Bool)
  normalizedOutput : Word Bool
deriving DecidableEq

def auxiliaryTapeView (T : Tape Bool) : AuxiliaryTapeView where
  head := T.head
  cells := Tape.cells T
  normalizedOutput := Tape.normalizedOutput T

/-- Three-tape configuration view specialized to tailed source-tape layouts. -/
structure TailedThreeTapeConfigView where
  state : Nat
  source : TailedTapeView
  scratch : AuxiliaryTapeView
  work : AuxiliaryTapeView
deriving DecidableEq

def tailedThreeTapeConfigView
    (c : Configuration) : TailedThreeTapeConfigView where
  state := c.state
  source := tailedTapeView (sourceTape c)
  scratch := auxiliaryTapeView (scratchTape c)
  work := auxiliaryTapeView (workTape c)

structure TailedThreeTapeStepView where
  step : Nat
  before : TailedThreeTapeConfigView
  reads : List (Option Bool)
  transition : Option TransitionDebugView
  after : TailedThreeTapeConfigView
deriving DecidableEq

def tailedThreeTapeStepView
    (row : StepDebugView) : TailedThreeTapeStepView where
  step := row.step
  before :=
    { state := row.before.state
      source :=
        match row.before.tapes with
        | source :: _ => tailedTapeView
            { left := source.left, head := source.head, right := source.right }
        | [] => tailedTapeView Tape.blank
      scratch :=
        match row.before.tapes.drop 1 with
        | scratch :: _ => auxiliaryTapeView
            { left := scratch.left, head := scratch.head,
              right := scratch.right }
        | [] => auxiliaryTapeView Tape.blank
      work :=
        match row.before.tapes.drop 2 with
        | work :: _ => auxiliaryTapeView
            { left := work.left, head := work.head, right := work.right }
        | [] => auxiliaryTapeView Tape.blank }
  reads := row.reads
  transition := row.transition
  after :=
    { state := row.after.state
      source :=
        match row.after.tapes with
        | source :: _ => tailedTapeView
            { left := source.left, head := source.head, right := source.right }
        | [] => tailedTapeView Tape.blank
      scratch :=
        match row.after.tapes.drop 1 with
        | scratch :: _ => auxiliaryTapeView
            { left := scratch.left, head := scratch.head,
              right := scratch.right }
        | [] => auxiliaryTapeView Tape.blank
      work :=
        match row.after.tapes.drop 2 with
        | work :: _ => auxiliaryTapeView
            { left := work.left, head := work.head, right := work.right }
        | [] => auxiliaryTapeView Tape.blank }

def debugTraceTailed
    (D : Description) (fuel : Nat)
    (c : Configuration) : List TailedThreeTapeStepView :=
  (D.debugTrace fuel c).map tailedThreeTapeStepView

def debugRunFinalTailed
    (D : Description) (fuel : Nat)
    (c : Configuration) : TailedThreeTapeConfigView :=
  tailedThreeTapeConfigView (D.runConfig fuel c)

def tailedTapeViewString (view : TailedTapeView) : String :=
  "leftBits=" ++ wordDebugString view.leftBits ++
    ", head=" ++ reprStr view.head ++
    ", headRightBits=" ++ wordDebugString view.headRightBits ++
    ", cells=" ++ reprStr view.cells

def auxiliaryTapeViewString (label : String)
    (view : AuxiliaryTapeView) : String :=
  label ++ "(head=" ++ reprStr view.head ++
    ", output=" ++ wordDebugString view.normalizedOutput ++
    ", cells=" ++ reprStr view.cells ++ ")"

def tailedThreeTapeConfigViewString
    (view : TailedThreeTapeConfigView) : String :=
  "state=" ++ reprStr view.state ++
    ", source(" ++ tailedTapeViewString view.source ++ ")" ++
    ", " ++ auxiliaryTapeViewString "scratch" view.scratch ++
    ", " ++ auxiliaryTapeViewString "work" view.work

def tailedThreeTapeStepViewString
    (row : TailedThreeTapeStepView) : String :=
  "#" ++ reprStr row.step ++
    " before(" ++ tailedThreeTapeConfigViewString row.before ++ ")" ++
    " reads=" ++ reprStr row.reads ++
    " transition=" ++ Description.optionTransitionDebugString row.transition ++
    " after(" ++ tailedThreeTapeConfigViewString row.after ++ ")"

def debugTraceTailedString
    (D : Description) (fuel : Nat)
    (c : Configuration) : String :=
  Description.joinStrings "\n"
    ((debugTraceTailed D fuel c).map tailedThreeTapeStepViewString)

def debugTraceTailedRange
    (D : Description) (fuel : Nat)
    (c : Configuration) (start stop : Nat) :
    List TailedThreeTapeStepView :=
  (debugTraceTailed D fuel c).filter
    (fun row => decide (start ≤ row.step ∧ row.step < stop))

def debugTraceTailedFrom
    (D : Description) (fuel : Nat)
    (c : Configuration) (start : Nat) :
    List TailedThreeTapeStepView :=
  (debugTraceTailed D fuel c).filter
    (fun row => decide (start ≤ row.step))

def breakOnSourceHead (cell : Option Bool) :
    Description.DebugBreakpoint where
  name := "source head " ++ reprStr cell
  predicate := fun _ c => Tape.read (sourceTape c) == cell

def breakOnSourceLeftBits (bits : Word Bool) :
    Description.DebugBreakpoint where
  name := "source left bits " ++ wordDebugString bits
  predicate := fun _ c => (tailedTapeView (sourceTape c)).leftBits == bits

def breakOnSourceHeadRightBits (bits : Word Bool) :
    Description.DebugBreakpoint where
  name := "source head/right bits " ++ wordDebugString bits
  predicate := fun _ c =>
    (tailedTapeView (sourceTape c)).headRightBits == bits

def breakOnScratchNonempty : Description.DebugBreakpoint where
  name := "scratch nonempty output"
  predicate := fun _ c => Tape.normalizedOutput (scratchTape c) != []

def breakOnWorkNonempty : Description.DebugBreakpoint where
  name := "work nonempty output"
  predicate := fun _ c => Tape.normalizedOutput (workTape c) != []

structure TailedSourceExpectation where
  expectedState? : Option Nat := none
  expectedSourceLeftBits? : Option (Word Bool) := none
  expectedSourceHeadRightBits? : Option (Word Bool) := none
  expectedSourceExact? : Option (Tape Bool) := none
  expectedScratchExact? : Option (Tape Bool) := none
  expectedWorkExact? : Option (Tape Bool) := none
deriving DecidableEq

private def checkNat?
    (label : String) (expected? : Option Nat) (actual : Nat) :
    Except String Unit :=
  match expected? with
  | none => Except.ok ()
  | some expected =>
      if actual = expected then
        Except.ok ()
      else
        Except.error
          (label ++ " mismatch: actual=" ++ reprStr actual ++
            ", expected=" ++ reprStr expected)

private def checkWord?
    (label : String) (expected? : Option (Word Bool))
    (actual : Word Bool) : Except String Unit :=
  match expected? with
  | none => Except.ok ()
  | some expected =>
      if actual = expected then
        Except.ok ()
      else
        Except.error
          (label ++ " mismatch: actual=" ++ wordDebugString actual ++
            ", expected=" ++ wordDebugString expected)

private def checkTape?
    (label : String) (expected? : Option (Tape Bool))
    (actual : Tape Bool) : Except String Unit :=
  match expected? with
  | none => Except.ok ()
  | some expected =>
      match compareTapeExact actual expected with
      | none => Except.ok ()
      | some mismatch =>
          Except.error
            (label ++ " " ++ tapeMismatchString mismatch)

def checkTailedSourceExpectation
    (expectation : TailedSourceExpectation)
    (c : Configuration) : Except String Unit := do
  let sourceView := tailedTapeView (sourceTape c)
  checkNat? "state" expectation.expectedState? c.state
  checkWord? "source left bits"
    expectation.expectedSourceLeftBits? sourceView.leftBits
  checkWord? "source head/right bits"
    expectation.expectedSourceHeadRightBits? sourceView.headRightBits
  checkTape? "source tape"
    expectation.expectedSourceExact? (sourceTape c)
  checkTape? "scratch tape"
    expectation.expectedScratchExact? (scratchTape c)
  checkTape? "work tape"
    expectation.expectedWorkExact? (workTape c)

structure TailedStepExpectation where
  step : Nat
  expectation : TailedSourceExpectation
deriving DecidableEq

def checkTailedStepExpectation
    (expectation : TailedStepExpectation)
    (step : Nat) (c : Configuration) : Except String Unit :=
  if step = expectation.step then
    checkTailedSourceExpectation expectation.expectation c
  else
    Except.ok ()

def checkTailedStepExpectations
    (expectations : List TailedStepExpectation)
    (step : Nat) (c : Configuration) : Except String Unit :=
  match expectations with
  | [] => Except.ok ()
  | expectation :: rest =>
      match checkTailedStepExpectation expectation step c with
      | Except.ok () => checkTailedStepExpectations rest step c
      | Except.error msg => Except.error msg

def debugFirstTailedExpectationFailure
    (D : Description) (fuel : Nat)
    (c : Configuration)
    (expectations : List TailedStepExpectation) : Option DebugFailure :=
  D.debugFirstFailure fuel c
    (checkTailedStepExpectations expectations)

def debugTraceAroundFirstTailedExpectationFailure
    (D : Description) (fuel : Nat)
    (c : Configuration)
    (expectations : List TailedStepExpectation)
    (radius : Nat) : List TailedThreeTapeStepView :=
  match debugFirstTailedExpectationFailure D fuel c expectations with
  | none => []
  | some failure =>
      debugTraceTailedRange D fuel c
        (failure.step - radius) (failure.step + radius + 1)

def debugFinalTailedReport
    (D : Description) (fuel : Nat)
    (c : Configuration)
    (expectation : TailedSourceExpectation) : String :=
  let final := D.runConfig fuel c
  match checkTailedSourceExpectation expectation final with
  | Except.ok () =>
      "ok\nactual(" ++
        tailedThreeTapeConfigViewString
          (tailedThreeTapeConfigView final) ++ ")"
  | Except.error msg =>
      "mismatch: " ++ msg ++ "\nactual(" ++
        tailedThreeTapeConfigViewString
          (tailedThreeTapeConfigView final) ++ ")"

namespace Examples

private def exampleSource : Tape Bool :=
  inputWithLiveTail [] [false] [true] []

private def exampleBlank : Tape Bool :=
  outputFromBits []

private def exampleConfig : Configuration :=
  config 7 exampleSource exampleBlank exampleBlank

private theorem exampleConfig_tailed_view :
    (tailedThreeTapeConfigView exampleConfig).source.leftBits = [] ∧
      (tailedThreeTapeConfigView exampleConfig).source.head = some false ∧
      (tailedThreeTapeConfigView exampleConfig).source.headRightBits =
        [false, true] := by
  decide

end Examples

end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
