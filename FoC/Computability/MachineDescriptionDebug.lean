import FoC.Computability.Encoding

set_option doc.verso true

/-!
# Machine-description debugging utilities

This module contains opt-in helpers for inspecting concrete
{name (full := FoC.Computability.MachineDescription)}`MachineDescription`
runs.  It deliberately defines debug views instead of adding representation
instances to the executable core datatypes.
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

end MachineDescription

end Computability
end FoC
