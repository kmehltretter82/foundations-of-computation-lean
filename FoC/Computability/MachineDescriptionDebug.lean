import FoC.Computability.MachineDescription

set_option doc.verso true

/-!
# Machine-description debugging utilities

This module contains opt-in helpers for inspecting concrete
{name (full := FoC.Computability.MachineDescription)}`MachineDescription`
runs.  It deliberately defines debug views instead of adding representation
instances to the executable core datatypes.  The helpers support full traces,
trace windows, breakpoints, watchpoints, compact summaries, and exact or
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv` comparisons.
-/

namespace FoC
namespace Computability

open MachineDescription

namespace MachineDescription

/-- Printable direction view for machine traces. -/
inductive DirectionDebugView where
  | left : DirectionDebugView
  | right : DirectionDebugView
deriving Repr, DecidableEq

def DirectionDebugView.toString : DirectionDebugView -> String
  | DirectionDebugView.left => "L"
  | DirectionDebugView.right => "R"

def directionDebugView : Direction -> DirectionDebugView
  | Direction.left => DirectionDebugView.left
  | Direction.right => DirectionDebugView.right

/-- Printable view of the concrete tape representation. -/
structure TapeDebugView where
  left : List (Option Bool)
  head : Option Bool
  right : List (Option Bool)
deriving Repr, DecidableEq

/-- Printable view of a machine configuration. -/
structure ConfigDebugView where
  state : Nat
  tape : TapeDebugView
deriving Repr, DecidableEq

/-- Printable view of a transition table entry. -/
structure TransitionDebugView where
  source : Nat
  read : Option Bool
  write : Option Bool
  move : DirectionDebugView
  target : Nat
deriving Repr, DecidableEq

/-- Printable view of one executed machine step. -/
structure StepDebugView where
  step : Nat
  before : ConfigDebugView
  read : Option Bool
  transition : Option TransitionDebugView
  after : ConfigDebugView
deriving Repr, DecidableEq

/--
Exact tape comparison failure.  The fields store the actual value first and
the expected value second.
-/
inductive TapeMismatch where
  | leftMismatch
      (actual expected : List (Option Bool))
  | headMismatch
      (actual expected : Option Bool)
  | rightMismatch
      (actual expected : List (Option Bool))
deriving Repr, DecidableEq

/--
Exact configuration comparison failure.  The fields store the actual value
first and the expected value second.
-/
inductive ConfigMismatch where
  | stateMismatch (actual expected : Nat)
  | tapeMismatch (mismatch : TapeMismatch)
deriving Repr, DecidableEq

structure StepExpectation where
  step : Nat
  expectedState? : Option Nat := none
  expectedTape? : Option (Tape Bool) := none
deriving DecidableEq

structure DebugFailure where
  step : Nat
  config : ConfigDebugView
  message : String
deriving Repr, DecidableEq

/-- A named predicate over step-indexed configurations. -/
structure DebugBreakpoint where
  name : String
  predicate : Nat -> Configuration -> Bool

/-- The first configuration that satisfies a breakpoint. -/
structure DebugBreakpointHit where
  name : String
  step : Nat
  config : ConfigDebugView
deriving Repr, DecidableEq

/-- A named predicate comparing the views before and after one executed step. -/
structure DebugWatchpoint where
  name : String
  changed : ConfigDebugView -> ConfigDebugView -> Bool

/-- One executed step where a watchpoint changed. -/
structure DebugWatchpointHit where
  name : String
  step : Nat
  before : ConfigDebugView
  after : ConfigDebugView
deriving Repr, DecidableEq

/-- Compact tape view for long traces. -/
structure TapeSummary where
  leftLength : Nat
  leftPrefix : List (Option Bool)
  head : Option Bool
  rightPrefix : List (Option Bool)
  rightLength : Nat
  outputPrefix : List Bool
  outputLength : Nat
deriving Repr, DecidableEq

def tapeDebugView (T : Tape Bool) : TapeDebugView where
  left := T.left
  head := T.head
  right := T.right

def configDebugView (c : Configuration) : ConfigDebugView where
  state := c.state
  tape := tapeDebugView c.tape

def transitionDebugView
    (t : TransitionDescription) : TransitionDebugView where
  source := t.source
  read := t.read
  write := t.write
  move := directionDebugView t.move
  target := t.target

def TapeDebugView.toTape (T : TapeDebugView) : Tape Bool where
  left := T.left
  head := T.head
  right := T.right

def ConfigDebugView.toConfiguration
    (c : ConfigDebugView) : Configuration where
  state := c.state
  tape := c.tape.toTape

end MachineDescription

namespace Tape

/-- Printable view of the concrete tape representation. -/
def debugView (T : Tape Bool) :
    MachineDescription.TapeDebugView :=
  MachineDescription.tapeDebugView T

end Tape

namespace MachineDescription

namespace Configuration

/-- Printable view of a machine configuration. -/
def debugView (c : Configuration) : ConfigDebugView :=
  configDebugView c

end Configuration

def transitionDebugString (t : TransitionDebugView) : String :=
  "q" ++ reprStr t.source ++ " read=" ++ reprStr t.read ++
    " write=" ++ reprStr t.write ++ " move=" ++
    t.move.toString ++ " -> q" ++ reprStr t.target

def optionTransitionDebugString :
    Option TransitionDebugView -> String
  | none => "none"
  | some t => transitionDebugString t

def tapeDebugString (T : TapeDebugView) : String :=
  "left=" ++ reprStr T.left ++ ", head=" ++ reprStr T.head ++
    ", right=" ++ reprStr T.right

def configDebugString (c : ConfigDebugView) : String :=
  "state=" ++ reprStr c.state ++ ", " ++ tapeDebugString c.tape

def stepDebugString (s : StepDebugView) : String :=
  "#" ++ reprStr s.step ++
    " before(" ++ configDebugString s.before ++ ")" ++
    " read=" ++ reprStr s.read ++
    " transition=" ++ optionTransitionDebugString s.transition ++
    " after(" ++ configDebugString s.after ++ ")"

def joinStrings (sep : String) : List String -> String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ sep ++ joinStrings sep rest

def stepConfigDebug
    (D : MachineDescription) (c : Configuration) :
    Option TransitionDescription × Configuration :=
  let read := Tape.read c.tape
  match D.lookupTransition c.state read with
  | none => (none, c)
  | some t =>
      (some t,
        { state := t.target
          tape := Tape.move t.move (Tape.write t.write c.tape) })

private def debugTraceAux
    (stopAtHalt : Bool) (D : MachineDescription) :
    Nat -> Nat -> Configuration -> List StepDebugView
  | 0, _, _ => []
  | fuel + 1, step, c =>
      if stopAtHalt && c.state == D.halt then
        []
      else
        let read := Tape.read c.tape
        let (transition?, next) := stepConfigDebug D c
        let row : StepDebugView :=
          { step := step
            before := c.debugView
            read := read
            transition := transition?.map transitionDebugView
            after := next.debugView }
        match transition? with
        | none => [row]
        | some _ =>
            row :: debugTraceAux stopAtHalt D fuel (step + 1) next

/--
Trace a run, stopping early if the current state is the machine halt state or
if no transition matches the current state and tape cell.
-/
def debugTrace
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) : List StepDebugView :=
  debugTraceAux true D fuel 0 c

/--
Trace a run without treating the halt state specially.  This follows the
operational shape of {name}`runConfig`, which only stops early when no
transition matches.
-/
def debugTraceFixed
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) : List StepDebugView :=
  debugTraceAux false D fuel 0 c

def debugRunFinal
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) : ConfigDebugView :=
  (D.runConfig fuel c).debugView

def debugTraceString
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) : String :=
  joinStrings "\n" ((D.debugTrace fuel c).map stepDebugString)

/--
Return the trace rows with indexes in the half-open interval
{lit}`[start, stop)`.
-/
def debugTraceRange
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) (start stop : Nat) :
    List StepDebugView :=
  (D.debugTrace fuel c).filter
    (fun row => decide (start ≤ row.step ∧ row.step < stop))

/-- Return all trace rows from the given step onward. -/
def debugTraceFrom
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) (start : Nat) :
    List StepDebugView :=
  (D.debugTrace fuel c).filter
    (fun row => decide (start ≤ row.step))

def debugTraceStringRange
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) (start stop : Nat) : String :=
  joinStrings "\n" ((D.debugTraceRange fuel c start stop).map stepDebugString)

def debugTraceStringFrom
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) (start : Nat) : String :=
  joinStrings "\n" ((D.debugTraceFrom fuel c start).map stepDebugString)

private def debugBreakpointHit
    (breakpoint : DebugBreakpoint) (step : Nat)
    (c : Configuration) : DebugBreakpointHit where
  name := breakpoint.name
  step := step
  config := c.debugView

private def debugFirstBreakpointAux
    (D : MachineDescription) (breakpoint : DebugBreakpoint) :
    Nat -> Nat -> Configuration -> Option DebugBreakpointHit
  | 0, step, c =>
      if breakpoint.predicate step c then
        some (debugBreakpointHit breakpoint step c)
      else
        none
  | fuel + 1, step, c =>
      if breakpoint.predicate step c then
        some (debugBreakpointHit breakpoint step c)
      else if c.state == D.halt then
        none
      else
        match D.stepConfig c with
        | none => none
        | some next =>
            debugFirstBreakpointAux D breakpoint fuel (step + 1) next

/--
Search the current configuration at each step for the first breakpoint hit.
Unlike {name}`debugTrace`, this can report the final halt configuration even
though no transition row is emitted for it.
-/
def debugFirstBreakpoint
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) (breakpoint : DebugBreakpoint) :
    Option DebugBreakpointHit :=
  debugFirstBreakpointAux D breakpoint fuel 0 c

/-- Return trace rows up to and including the row for the first breakpoint. -/
def debugTraceUntilBreakpoint
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) (breakpoint : DebugBreakpoint) :
    List StepDebugView :=
  match D.debugFirstBreakpoint fuel c breakpoint with
  | none => D.debugTrace fuel c
  | some hit => D.debugTraceRange fuel c 0 (hit.step + 1)

/-- Return a trace window around the first breakpoint hit. -/
def debugTraceAroundBreakpoint
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) (breakpoint : DebugBreakpoint)
    (radius : Nat) : List StepDebugView :=
  match D.debugFirstBreakpoint fuel c breakpoint with
  | none => []
  | some hit =>
      D.debugTraceRange fuel c
        (hit.step - radius) (hit.step + radius + 1)

/-- Break when the current state equals the given state. -/
def breakOnState (state : Nat) : DebugBreakpoint where
  name := "state q" ++ reprStr state
  predicate := fun _ c => c.state == state

/-- Break when the current tape cell equals the given cell. -/
def breakOnRead (cell : Option Bool) : DebugBreakpoint where
  name := "read " ++ reprStr cell
  predicate := fun _ c => Tape.read c.tape == cell

/-- Break when the current transition-table key is reached. -/
def breakOnTransitionKey
    (state : Nat) (cell : Option Bool) : DebugBreakpoint where
  name := "transition key q" ++ reprStr state ++ "/" ++ reprStr cell
  predicate := fun _ c => c.state == state && Tape.read c.tape == cell

/-- Break when the machine is in its halt state. -/
def breakOnHalt (D : MachineDescription) : DebugBreakpoint where
  name := "halt q" ++ reprStr D.halt
  predicate := fun _ c => c.state == D.halt

/-- Break when the current configuration has no matching transition. -/
def breakOnStuck (D : MachineDescription) : DebugBreakpoint where
  name := "stuck"
  predicate := fun _ c =>
    if c.state == D.halt then
      false
    else
      match D.lookupTransition c.state (Tape.read c.tape) with
      | none => true
      | some _ => false

def compareTapeExact
    (actual expected : Tape Bool) : Option TapeMismatch :=
  if actual.left = expected.left then
    if actual.head = expected.head then
      if actual.right = expected.right then
        none
      else
        some (TapeMismatch.rightMismatch actual.right expected.right)
    else
      some (TapeMismatch.headMismatch actual.head expected.head)
  else
    some (TapeMismatch.leftMismatch actual.left expected.left)

def compareConfigExact
    (actual expected : Configuration) : Option ConfigMismatch :=
  if actual.state = expected.state then
    match compareTapeExact actual.tape expected.tape with
    | none => none
    | some mismatch => some (ConfigMismatch.tapeMismatch mismatch)
  else
    some (ConfigMismatch.stateMismatch actual.state expected.state)

def compareTapeEquiv
    (actual expected : Tape Bool) : Option TapeMismatch :=
  let actualLeft := Tape.dropTrailingNone actual.left
  let expectedLeft := Tape.dropTrailingNone expected.left
  let actualRight := Tape.dropTrailingNone actual.right
  let expectedRight := Tape.dropTrailingNone expected.right
  if actualLeft = expectedLeft then
    if actual.head = expected.head then
      if actualRight = expectedRight then
        none
      else
        some (TapeMismatch.rightMismatch actualRight expectedRight)
    else
      some (TapeMismatch.headMismatch actual.head expected.head)
  else
    some (TapeMismatch.leftMismatch actualLeft expectedLeft)

def compareConfigEquiv
    (actual expected : Configuration) : Option ConfigMismatch :=
  if actual.state = expected.state then
    match compareTapeEquiv actual.tape expected.tape with
    | none => none
    | some mismatch => some (ConfigMismatch.tapeMismatch mismatch)
  else
    some (ConfigMismatch.stateMismatch actual.state expected.state)

def tapeMismatchString : TapeMismatch -> String
  | TapeMismatch.leftMismatch actual expected =>
      "left mismatch: actual=" ++ reprStr actual ++
        ", expected=" ++ reprStr expected
  | TapeMismatch.headMismatch actual expected =>
      "head mismatch: actual=" ++ reprStr actual ++
        ", expected=" ++ reprStr expected
  | TapeMismatch.rightMismatch actual expected =>
      "right mismatch: actual=" ++ reprStr actual ++
        ", expected=" ++ reprStr expected

def configMismatchString : ConfigMismatch -> String
  | ConfigMismatch.stateMismatch actual expected =>
      "state mismatch: actual=" ++ reprStr actual ++
        ", expected=" ++ reprStr expected
  | ConfigMismatch.tapeMismatch mismatch =>
      tapeMismatchString mismatch

private def checkTapeExpectation
    (expected? : Option (Tape Bool)) (c : Configuration) :
    Except String Unit :=
  match expected? with
  | none => Except.ok ()
  | some expected =>
      match compareTapeExact c.tape expected with
      | none => Except.ok ()
      | some mismatch => Except.error (tapeMismatchString mismatch)

def checkStepExpectation
    (expectation : StepExpectation)
    (step : Nat) (c : Configuration) : Except String Unit :=
  if step = expectation.step then
    match expectation.expectedState? with
    | none => checkTapeExpectation expectation.expectedTape? c
    | some expectedState =>
        if c.state = expectedState then
          checkTapeExpectation expectation.expectedTape? c
        else
          Except.error
            ("state mismatch: actual=" ++ reprStr c.state ++
              ", expected=" ++ reprStr expectedState)
  else
    Except.ok ()

def checkStepExpectations
    (expectations : List StepExpectation)
    (step : Nat) (c : Configuration) : Except String Unit :=
  match expectations with
  | [] => Except.ok ()
  | expectation :: rest =>
      match checkStepExpectation expectation step c with
      | Except.ok () => checkStepExpectations rest step c
      | Except.error msg => Except.error msg

private def debugFirstFailureAux
    (D : MachineDescription)
    (check : Nat -> Configuration -> Except String Unit) :
    Nat -> Nat -> Configuration -> Option DebugFailure
  | 0, step, c =>
      match check step c with
      | Except.ok () => none
      | Except.error msg =>
          some { step := step, config := c.debugView, message := msg }
  | fuel + 1, step, c =>
      match check step c with
      | Except.error msg =>
          some { step := step, config := c.debugView, message := msg }
      | Except.ok () =>
          if c.state == D.halt then
            none
          else
            match D.stepConfig c with
            | none => none
            | some next =>
                debugFirstFailureAux D check fuel (step + 1) next

/--
Run a step-indexed checker over the initial configuration and each subsequent
configuration until fuel runs out, the halt state is reached, or execution gets
stuck.
-/
def debugFirstFailure
    (D : MachineDescription)
    (fuel : Nat)
    (c : Configuration)
    (check : Nat -> Configuration -> Except String Unit) :
    Option DebugFailure :=
  debugFirstFailureAux D check fuel 0 c

def debugFirstExpectationFailure
    (D : MachineDescription)
    (fuel : Nat)
    (c : Configuration)
    (expectations : List StepExpectation) : Option DebugFailure :=
  D.debugFirstFailure fuel c
    (checkStepExpectations expectations)

/-- Return a trace window around the first checker failure. -/
def debugTraceAroundFirstFailure
    (D : MachineDescription)
    (fuel : Nat)
    (c : Configuration)
    (check : Nat -> Configuration -> Except String Unit)
    (radius : Nat) : List StepDebugView :=
  match D.debugFirstFailure fuel c check with
  | none => []
  | some failure =>
      D.debugTraceRange fuel c
        (failure.step - radius) (failure.step + radius + 1)

/-- Return a trace window around the first failed step expectation. -/
def debugTraceAroundFirstExpectationFailure
    (D : MachineDescription)
    (fuel : Nat)
    (c : Configuration)
    (expectations : List StepExpectation)
    (radius : Nat) : List StepDebugView :=
  D.debugTraceAroundFirstFailure fuel c
    (checkStepExpectations expectations) radius

/-- Report all executed rows where a watchpoint changed. -/
def debugWatchpointHits
    (D : MachineDescription)
    (fuel : Nat)
    (c : Configuration)
    (watchpoint : DebugWatchpoint) : List DebugWatchpointHit :=
  (D.debugTrace fuel c).filterMap
    (fun row =>
      if watchpoint.changed row.before row.after then
        some
          { name := watchpoint.name
            step := row.step
            before := row.before
            after := row.after }
      else
        none)

/-- Watch for state changes across executed rows. -/
def watchStateChanged : DebugWatchpoint where
  name := "state changed"
  changed := fun before after => decide (before.state ≠ after.state)

/-- Watch for head-cell changes across executed rows. -/
def watchHeadChanged : DebugWatchpoint where
  name := "head changed"
  changed := fun before after =>
    decide (before.tape.head ≠ after.tape.head)

private def nonblankCells (cells : List (Option Bool)) : List Bool :=
  cells.filterMap (fun cell => cell)

/-- Watch for changes in the nonblank portion of the stored left context. -/
def watchLeftNonblankChanged : DebugWatchpoint where
  name := "left nonblank changed"
  changed := fun before after =>
    decide (nonblankCells before.tape.left ≠ nonblankCells after.tape.left)

/-- Watch for changes in the nonblank portion of the stored right context. -/
def watchRightNonblankChanged : DebugWatchpoint where
  name := "right nonblank changed"
  changed := fun before after =>
    decide (nonblankCells before.tape.right ≠ nonblankCells after.tape.right)

private def normalizedOutputList (T : Tape Bool) : List Bool :=
  T.normalizedOutput

/-- Watch for changes in the tape's normalized nonblank output word. -/
def watchNormalizedOutputChanged : DebugWatchpoint where
  name := "normalized output changed"
  changed := fun before after =>
    decide
      (normalizedOutputList before.tape.toTape ≠
        normalizedOutputList after.tape.toTape)

def tapeDebugSummary
    (prefixLimit : Nat) (T : TapeDebugView) : TapeSummary where
  leftLength := T.left.length
  leftPrefix := T.left.take prefixLimit
  head := T.head
  rightPrefix := T.right.take prefixLimit
  rightLength := T.right.length
  outputPrefix := (normalizedOutputList T.toTape).take prefixLimit
  outputLength := (normalizedOutputList T.toTape).length

/-- Compact summary of a concrete tape. -/
def tapeSummary (prefixLimit : Nat) (T : Tape Bool) : TapeSummary :=
  tapeDebugSummary prefixLimit T.debugView

def tapeSummaryString (summary : TapeSummary) : String :=
  "leftLen=" ++ reprStr summary.leftLength ++
    ", leftPrefix=" ++ reprStr summary.leftPrefix ++
    ", head=" ++ reprStr summary.head ++
    ", rightPrefix=" ++ reprStr summary.rightPrefix ++
    ", rightLen=" ++ reprStr summary.rightLength ++
    ", outputPrefix=" ++ reprStr summary.outputPrefix ++
    ", outputLen=" ++ reprStr summary.outputLength

def configSummaryString
    (prefixLimit : Nat) (c : ConfigDebugView) : String :=
  "state=" ++ reprStr c.state ++
    ", " ++ tapeSummaryString (tapeDebugSummary prefixLimit c.tape)

/-- Compact one-line string for a trace row with long tape contexts truncated. -/
def stepSummaryString
    (prefixLimit : Nat) (row : StepDebugView) : String :=
  "#" ++ reprStr row.step ++
    " before(" ++ configSummaryString prefixLimit row.before ++ ")" ++
    " read=" ++ reprStr row.read ++
    " transition=" ++ optionTransitionDebugString row.transition ++
    " after(" ++ configSummaryString prefixLimit row.after ++ ")"

def debugTraceSummaryString
    (D : MachineDescription) (fuel : Nat)
    (c : Configuration) (prefixLimit : Nat) : String :=
  joinStrings "\n"
    ((D.debugTrace fuel c).map (stepSummaryString prefixLimit))

private def configComparisonStatus
    (mismatch? : Option ConfigMismatch) : String :=
  match mismatch? with
  | none => "ok"
  | some mismatch => configMismatchString mismatch

/--
Run the machine for the given fuel and return a string report comparing the
final configuration against an expected configuration.
-/
def debugCompareFinalReport
    (D : MachineDescription) (fuel : Nat)
    (start expected : Configuration) : String :=
  let actual := D.runConfig fuel start
  "actual(" ++ configDebugString actual.debugView ++ ")" ++ "\n" ++
    "expected(" ++ configDebugString expected.debugView ++ ")" ++ "\n" ++
    "exact=" ++
      configComparisonStatus (compareConfigExact actual expected) ++ "\n" ++
    "equiv=" ++
      configComparisonStatus (compareConfigEquiv actual expected) ++ "\n" ++
    "actualOutput=" ++
      reprStr (normalizedOutputList actual.tape) ++ "\n" ++
    "expectedOutput=" ++
      reprStr (normalizedOutputList expected.tape)

end MachineDescription

end Computability
end FoC
