import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Assembly
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.FinalCompare
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.SavedCell.Handoff
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.RestagedEdits
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.ParserAssembly
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep

/-!
# Verified final gate from retained header metadata

Every final branch first passes through the saved transition-table parser.
Count zero reaches its parser halt immediately; positive count with carried
zero fuel runs through the parser's saved-ready endpoint.  Only then does the
finite extractor discard the count/table/input payload and the older
state-count/header/fuel metadata.  The parsed `halt` and `start` fields are the
two nearest reversed unary fields on the physical left stack, and the
extractor leaves exactly

`encodeNat start ++ encodeNat halt ++ [blank]`

up to trailing physical blank padding.  Two existing bounded insertions then
add the comparator header and its `blank, transition` separator.
-/

theorem encodeNat_eq_ticks_done (value : Nat) :
    MachineDescription.encodeNat value =
      List.append
        (List.replicate value MachineCodeSymbol.tick)
        [MachineCodeSymbol.done] := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simp [MachineDescription.encodeNat, List.replicate_succ, ih]

theorem encodeNat_reverse_eq_done_ticks (value : Nat) :
    (MachineDescription.encodeNat value).reverse =
      MachineCodeSymbol.done ::
        List.replicate value MachineCodeSymbol.tick := by
  rw [encodeNat_eq_ticks_done]
  simp [List.reverse_append]

theorem replicate_append_self_cons {α : Type}
    (value : α) (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: List.replicate count value ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ]
      exact congrArg (fun cells => value :: cells) ih

def metadataLeftRev
    (fuel stateCount start halt : Nat) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat halt).reverse
    (List.append (MachineDescription.encodeNat start).reverse
      (List.append (MachineDescription.encodeNat stateCount).reverse
        (MachineCodeSymbol.header ::
          (MachineDescription.encodeNat fuel).reverse)))

theorem metadataLeftRev_eq_headerAfterHaltLeftRev
    (D : MachineDescription) (fuel : Nat) :
    metadataLeftRev fuel D.stateCount D.start D.halt =
      headerAfterHaltLeftRev D fuel := by
  rfl

def extractedWord (start halt : Nat) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend start
    (MachineDescription.encodeNatAppend halt
      [MachineCodeSymbol.blank])

inductive Control where
  | preserveBlank
  | eraseRight
  | cleanupRight
  | preserveContextBlank
  | eraseContextRight
  | cleanupContextRight
  | preserveNoBarrierBlank
  | eraseNoBarrierRight
  | cleanupNoBarrierRight
  | bubbleSingleDone
  | bubbleSingleErase
  | bubbleSingleMove
  | bubbleCell
  | bubbleEraseCell
  | bubbleMoveCell
  | bubbleEraseBarrier
  | bubbleMoveBarrier
  | crossHaltDone
  | crossHaltTicks
  | crossStartTicks
  | eraseLeft
  | cleanupLeft
  | readyBounce
  | ready
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.preserveBlank, .eraseRight, .cleanupRight,
    .preserveContextBlank, .eraseContextRight, .cleanupContextRight,
    .preserveNoBarrierBlank, .eraseNoBarrierRight, .cleanupNoBarrierRight,
    .bubbleSingleDone, .bubbleSingleErase, .bubbleSingleMove,
    .bubbleCell, .bubbleEraseCell, .bubbleMoveCell,
    .bubbleEraseBarrier, .bubbleMoveBarrier,
    .crossHaltDone, .crossHaltTicks, .crossStartTicks,
    .eraseLeft, .cleanupLeft, .readyBounce, .ready, .halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .preserveBlank, some _ =>
      some (some MachineCodeSymbol.blank, Direction.right, .eraseRight)
  | .eraseRight, some _ =>
      some (some MachineCodeSymbol.moveRight, Direction.right, .eraseRight)
  | .eraseRight, none =>
      some (none, Direction.left, .cleanupRight)
  | .cleanupRight, some MachineCodeSymbol.moveRight =>
      some (none, Direction.left, .cleanupRight)
  | .cleanupRight, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.left, .crossHaltDone)
  | .preserveContextBlank, some _ =>
      some (some MachineCodeSymbol.blank, Direction.right,
        .eraseContextRight)
  | .eraseContextRight, some _ =>
      some (some MachineCodeSymbol.moveRight, Direction.right,
        .eraseContextRight)
  | .eraseContextRight, none =>
      some (none, Direction.left, .cleanupContextRight)
  | .cleanupContextRight, some MachineCodeSymbol.moveRight =>
      some (none, Direction.left, .cleanupContextRight)
  | .cleanupContextRight, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.left, .bubbleCell)
  | .preserveNoBarrierBlank, _ =>
      some (some MachineCodeSymbol.blank, Direction.right,
        .eraseNoBarrierRight)
  | .eraseNoBarrierRight, some _ =>
      some (some MachineCodeSymbol.moveRight, Direction.right,
        .eraseNoBarrierRight)
  | .eraseNoBarrierRight, none =>
      some (none, Direction.left, .cleanupNoBarrierRight)
  | .cleanupNoBarrierRight, some MachineCodeSymbol.moveRight =>
      some (none, Direction.left, .cleanupNoBarrierRight)
  | .cleanupNoBarrierRight, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.left,
        .bubbleSingleDone)
  | .bubbleSingleDone, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.blank, Direction.right,
        .bubbleSingleErase)
  | .bubbleSingleErase, some MachineCodeSymbol.blank =>
      some (none, Direction.left, .bubbleSingleMove)
  | .bubbleSingleMove, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.left,
        .crossHaltDone)
  | .bubbleCell, some _ =>
      some (some MachineCodeSymbol.blank, Direction.right,
        .bubbleEraseCell)
  | .bubbleCell, none =>
      some (some MachineCodeSymbol.blank, Direction.right,
        .bubbleEraseBarrier)
  | .bubbleEraseCell, some MachineCodeSymbol.blank =>
      some (none, Direction.left, .bubbleMoveCell)
  | .bubbleMoveCell, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.left, .bubbleCell)
  | .bubbleEraseBarrier, some MachineCodeSymbol.blank =>
      some (none, Direction.left, .bubbleMoveBarrier)
  | .bubbleMoveBarrier, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.left, .crossHaltDone)
  | .crossHaltDone, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .crossHaltTicks)
  | .crossHaltTicks, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left, .crossHaltTicks)
  | .crossHaltTicks, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .crossStartTicks)
  | .crossStartTicks, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left, .crossStartTicks)
  | .crossStartTicks, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.moveLeft, Direction.left, .eraseLeft)
  | .eraseLeft, some _ =>
      some (some MachineCodeSymbol.moveLeft, Direction.left, .eraseLeft)
  | .eraseLeft, none =>
      some (none, Direction.right, .cleanupLeft)
  | .cleanupLeft, some MachineCodeSymbol.moveLeft =>
      some (none, Direction.right, .cleanupLeft)
  | .cleanupLeft, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left, .readyBounce)
  | .cleanupLeft, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .readyBounce)
  | .readyBounce, none =>
      some (none, Direction.right, .ready)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .preserveBlank
  halt := .halt
  transition := transition
  statesFinite := Control.finite

theorem computes_of_run_exact
    {steps : Nat}
    {source target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : machine.runConfigExact? steps source = some target) :
    TuringMachine.Computes machine source target :=
  TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)

theorem computes_one_of_stepConfig
    {source target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hstep : machine.stepConfig source = some target) :
    TuringMachine.Computes machine source target :=
  TuringMachine.computes_of_step
    (TuringMachine.stepConfig_eq_some_iff_step.mp hstep)

def sourceConfig
    (fuel stateCount start halt : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .preserveBlank
  tape := headerFieldsParserTape
    (metadataLeftRev fuel stateCount start halt) (first :: rest)

def eraseRightConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (erased : Nat)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .eraseRight
  tape := headerFieldsParserTape
    (List.append
      (List.replicate erased MachineCodeSymbol.moveRight)
      baseLeftRev)
    remaining

theorem preserveBlank_step
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .preserveBlank
          tape := headerFieldsParserTape baseLeftRev (first :: rest) } =
      some (eraseRightConfig
        (MachineCodeSymbol.blank :: baseLeftRev) 0 rest) := by
  cases first <;> cases rest <;> rfl

theorem eraseRight_step
    (baseLeftRev : Word MachineCodeSymbol)
    (erased : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (eraseRightConfig baseLeftRev erased (first :: rest)) =
      some (eraseRightConfig baseLeftRev erased.succ rest) := by
  cases erased <;> cases first <;> cases rest <;>
    simp [eraseRightConfig, machine, transition,
      TuringMachine.stepConfig, headerFieldsParserTape,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

theorem eraseRight_run_exact
    (baseLeftRev remaining : Word MachineCodeSymbol)
    (erased : Nat) :
    machine.runConfigExact? remaining.length
        (eraseRightConfig baseLeftRev erased remaining) =
      some
        (eraseRightConfig baseLeftRev
          (remaining.length + erased) []) := by
  induction remaining generalizing erased with
  | nil =>
      change some (eraseRightConfig baseLeftRev erased []) = _
      simp only [List.length_nil, Nat.zero_add]
  | cons first rest ih =>
      change machine.runConfigExact? (rest.length + 1)
        (eraseRightConfig baseLeftRev erased (first :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [eraseRight_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih erased.succ

def cleanupRightTape
    (metadata : Word MachineCodeSymbol)
    (remainingMarkers rightPadding : Nat) : Tape MachineCodeSymbol :=
  match remainingMarkers with
  | 0 =>
      { left := metadata.map some
        head := some MachineCodeSymbol.blank
        right := List.replicate rightPadding none }
  | remaining + 1 =>
      { left :=
          (List.append
            (List.replicate remaining MachineCodeSymbol.moveRight)
            (MachineCodeSymbol.blank :: metadata)).map some
        head := some MachineCodeSymbol.moveRight
        right := List.replicate rightPadding none }

def cleanupRightConfig
    (metadata : Word MachineCodeSymbol)
    (remainingMarkers rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .cleanupRight
  tape := cleanupRightTape metadata remainingMarkers rightPadding

theorem eraseRight_finish_step
    (metadata : Word MachineCodeSymbol)
    (erased : Nat) :
    machine.stepConfig
        (eraseRightConfig
          (MachineCodeSymbol.blank :: metadata) erased []) =
      some (cleanupRightConfig metadata erased 1) := by
  cases erased with
  | zero =>
      cases metadata <;> rfl
  | succ erased =>
      cases erased <;> cases metadata <;>
        simp [eraseRightConfig, cleanupRightConfig, cleanupRightTape,
          machine, transition, TuringMachine.stepConfig,
          headerFieldsParserTape, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, List.replicate_succ]

theorem cleanupRight_marker_step
    (metadata : Word MachineCodeSymbol)
    (remaining rightPadding : Nat) :
    machine.stepConfig
        (cleanupRightConfig metadata remaining.succ rightPadding) =
      some
        (cleanupRightConfig metadata remaining rightPadding.succ) := by
  cases remaining <;> cases rightPadding <;> cases metadata <;>
    simp [cleanupRightConfig, cleanupRightTape, machine, transition,
      TuringMachine.stepConfig, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, List.replicate_succ]

theorem cleanupRight_run_exact
    (metadata : Word MachineCodeSymbol)
    (remaining rightPadding : Nat) :
    machine.runConfigExact? remaining
        (cleanupRightConfig metadata remaining rightPadding) =
      some
        (cleanupRightConfig metadata 0
          (remaining + rightPadding)) := by
  induction remaining generalizing rightPadding with
  | zero =>
      simp only [TuringMachine.runConfigExact?, Nat.zero_add]
  | succ remaining ih =>
      rw [TuringMachine.runConfigExact?]
      rw [cleanupRight_marker_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih rightPadding.succ

def contextCursorTape
    (left : List (Option MachineCodeSymbol))
    (rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] => { left := left, head := none, right := [] }
  | first :: suffix =>
      { left := left, head := some first, right := suffix.map some }

def contextSourceConfig
    (baseLeft : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .preserveContextBlank
  tape := contextCursorTape baseLeft (first :: rest)

def contextEraseRightConfig
    (baseLeft : List (Option MachineCodeSymbol))
    (erased : Nat)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .eraseContextRight
  tape := contextCursorTape
    (List.replicate erased (some MachineCodeSymbol.moveRight) ++
      baseLeft)
    remaining

theorem context_preserveBlank_step
    (baseLeft : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig (contextSourceConfig baseLeft first rest) =
      some
        (contextEraseRightConfig
          (some MachineCodeSymbol.blank :: baseLeft) 0 rest) := by
  cases first <;> cases rest <;> rfl

theorem context_eraseRight_step
    (baseLeft : List (Option MachineCodeSymbol))
    (erased : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (contextEraseRightConfig baseLeft erased (first :: rest)) =
      some
        (contextEraseRightConfig baseLeft erased.succ rest) := by
  cases erased <;> cases first <;> cases rest <;> cases baseLeft <;>
    simp [contextEraseRightConfig, contextCursorTape,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

theorem context_eraseRight_run_exact
    (baseLeft : List (Option MachineCodeSymbol))
    (remaining : Word MachineCodeSymbol)
    (erased : Nat) :
    machine.runConfigExact? remaining.length
        (contextEraseRightConfig baseLeft erased remaining) =
      some
        (contextEraseRightConfig baseLeft
          (remaining.length + erased) []) := by
  induction remaining generalizing erased with
  | nil =>
      simp only [List.length_nil, TuringMachine.runConfigExact?,
        Nat.zero_add]
  | cons first rest ih =>
      change machine.runConfigExact? (rest.length + 1)
        (contextEraseRightConfig baseLeft erased (first :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [context_eraseRight_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih erased.succ

def cleanupContextRightTape
    (baseLeft : List (Option MachineCodeSymbol))
    (remainingMarkers rightPadding : Nat) : Tape MachineCodeSymbol :=
  match remainingMarkers with
  | 0 =>
      { left := baseLeft
        head := some MachineCodeSymbol.blank
        right := List.replicate rightPadding none }
  | remaining + 1 =>
      { left :=
          List.replicate remaining (some MachineCodeSymbol.moveRight) ++
            some MachineCodeSymbol.blank :: baseLeft
        head := some MachineCodeSymbol.moveRight
        right := List.replicate rightPadding none }

def cleanupContextRightConfig
    (baseLeft : List (Option MachineCodeSymbol))
    (remainingMarkers rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .cleanupContextRight
  tape := cleanupContextRightTape baseLeft remainingMarkers rightPadding

theorem context_eraseRight_finish_step
    (baseLeft : List (Option MachineCodeSymbol))
    (erased : Nat) :
    machine.stepConfig
        (contextEraseRightConfig
          (some MachineCodeSymbol.blank :: baseLeft) erased []) =
      some (cleanupContextRightConfig baseLeft erased 1) := by
  cases erased <;> cases baseLeft <;>
    simp [contextEraseRightConfig, contextCursorTape,
      cleanupContextRightConfig, cleanupContextRightTape,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

theorem cleanupContextRight_marker_step
    (baseLeft : List (Option MachineCodeSymbol))
    (remaining rightPadding : Nat) :
    machine.stepConfig
        (cleanupContextRightConfig baseLeft remaining.succ rightPadding) =
      some
        (cleanupContextRightConfig baseLeft remaining
          rightPadding.succ) := by
  cases remaining <;> cases rightPadding <;> cases baseLeft <;>
    simp [cleanupContextRightConfig, cleanupContextRightTape,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

theorem cleanupContextRight_run_exact
    (baseLeft : List (Option MachineCodeSymbol))
    (remaining rightPadding : Nat) :
    machine.runConfigExact? remaining
        (cleanupContextRightConfig baseLeft remaining rightPadding) =
      some
        (cleanupContextRightConfig baseLeft 0
          (remaining + rightPadding)) := by
  induction remaining generalizing rightPadding with
  | zero =>
      simp only [TuringMachine.runConfigExact?, Nat.zero_add]
  | succ remaining ih =>
      rw [TuringMachine.runConfigExact?]
      rw [cleanupContextRight_marker_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih rightPadding.succ

def noBarrierSourceConfig
    (metadata payload : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .preserveNoBarrierBlank
  tape := contextCursorTape
    (some MachineCodeSymbol.done :: metadata.map some) payload

def noBarrierEraseRightConfig
    (metadata : Word MachineCodeSymbol)
    (erased : Nat)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .eraseNoBarrierRight
  tape := contextCursorTape
    (List.replicate erased (some MachineCodeSymbol.moveRight) ++
      some MachineCodeSymbol.blank ::
        some MachineCodeSymbol.done :: metadata.map some)
    remaining

def noBarrierPayloadTail
    (payload : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  match payload with
  | [] => []
  | _ :: rest => rest

theorem noBarrier_preserveBlank_step
    (metadata payload : Word MachineCodeSymbol) :
    machine.stepConfig (noBarrierSourceConfig metadata payload) =
      some
        (noBarrierEraseRightConfig metadata 0
          (noBarrierPayloadTail payload)) := by
  cases payload with
  | nil => rfl
  | cons first rest =>
      cases first <;> cases rest <;> cases metadata <;>
        simp [noBarrierSourceConfig, noBarrierEraseRightConfig,
          noBarrierPayloadTail, contextCursorTape,
          machine, transition, TuringMachine.stepConfig,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem noBarrier_eraseRight_step
    (metadata : Word MachineCodeSymbol)
    (erased : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (noBarrierEraseRightConfig metadata erased (first :: rest)) =
      some
        (noBarrierEraseRightConfig metadata erased.succ rest) := by
  cases erased <;> cases first <;> cases rest <;> cases metadata <;>
    simp [noBarrierEraseRightConfig, contextCursorTape,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

theorem noBarrier_eraseRight_run_exact
    (metadata remaining : Word MachineCodeSymbol)
    (erased : Nat) :
    machine.runConfigExact? remaining.length
        (noBarrierEraseRightConfig metadata erased remaining) =
      some
        (noBarrierEraseRightConfig metadata
          (remaining.length + erased) []) := by
  induction remaining generalizing erased with
  | nil =>
      simp only [List.length_nil, TuringMachine.runConfigExact?,
        Nat.zero_add]
  | cons first rest ih =>
      change machine.runConfigExact? (rest.length + 1)
        (noBarrierEraseRightConfig metadata erased (first :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [noBarrier_eraseRight_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih erased.succ

def noBarrierCleanupRightConfig
    (metadata : Word MachineCodeSymbol)
    (remainingMarkers rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .cleanupNoBarrierRight
  tape := cleanupContextRightTape
    (some MachineCodeSymbol.done :: metadata.map some)
    remainingMarkers rightPadding

theorem noBarrier_eraseRight_finish_step
    (metadata : Word MachineCodeSymbol)
    (erased : Nat) :
    machine.stepConfig
        (noBarrierEraseRightConfig metadata erased []) =
      some (noBarrierCleanupRightConfig metadata erased 1) := by
  cases erased <;> cases metadata <;>
    simp [noBarrierEraseRightConfig, noBarrierCleanupRightConfig,
      contextCursorTape, cleanupContextRightTape,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

theorem noBarrier_cleanupRight_marker_step
    (metadata : Word MachineCodeSymbol)
    (remaining rightPadding : Nat) :
    machine.stepConfig
        (noBarrierCleanupRightConfig metadata remaining.succ rightPadding) =
      some
        (noBarrierCleanupRightConfig metadata remaining
          rightPadding.succ) := by
  cases remaining <;> cases rightPadding <;> cases metadata <;>
    simp [noBarrierCleanupRightConfig, cleanupContextRightTape,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

theorem noBarrier_cleanupRight_run_exact
    (metadata : Word MachineCodeSymbol)
    (remaining rightPadding : Nat) :
    machine.runConfigExact? remaining
        (noBarrierCleanupRightConfig metadata remaining rightPadding) =
      some
        (noBarrierCleanupRightConfig metadata 0
          (remaining + rightPadding)) := by
  induction remaining generalizing rightPadding with
  | zero =>
      simp only [TuringMachine.runConfigExact?, Nat.zero_add]
  | succ remaining ih =>
      rw [TuringMachine.runConfigExact?]
      rw [noBarrier_cleanupRight_marker_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih rightPadding.succ

def bubbleSingleDoneConfig
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .bubbleSingleDone
  tape :=
    { left := metadata.map some
      head := some MachineCodeSymbol.done
      right := some MachineCodeSymbol.blank ::
        List.replicate rightPadding none }

def bubbleSingleEraseConfig
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .bubbleSingleErase
  tape :=
    { left := some MachineCodeSymbol.blank :: metadata.map some
      head := some MachineCodeSymbol.blank
      right := List.replicate rightPadding none }

def bubbleSingleMoveConfig
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .bubbleSingleMove
  tape :=
    { left := metadata.map some
      head := some MachineCodeSymbol.blank
      right := none :: List.replicate rightPadding none }

theorem noBarrier_cleanupRight_boundary_step
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    machine.stepConfig
        (noBarrierCleanupRightConfig metadata 0 rightPadding) =
      some (bubbleSingleDoneConfig metadata rightPadding) := by
  cases metadata <;> cases rightPadding <;>
    simp [noBarrierCleanupRightConfig, cleanupContextRightTape,
      bubbleSingleDoneConfig, machine, transition,
      TuringMachine.stepConfig, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, List.replicate_succ]

theorem bubbleSingleDone_step
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    machine.stepConfig (bubbleSingleDoneConfig metadata rightPadding) =
      some (bubbleSingleEraseConfig metadata rightPadding) := by
  cases metadata <;> cases rightPadding <;>
    simp [bubbleSingleDoneConfig, bubbleSingleEraseConfig,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

theorem bubbleSingleErase_step
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    machine.stepConfig (bubbleSingleEraseConfig metadata rightPadding) =
      some (bubbleSingleMoveConfig metadata rightPadding) := by
  cases metadata <;> cases rightPadding <;>
    simp [bubbleSingleEraseConfig, bubbleSingleMoveConfig,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

def bubbleCellConfig
    (remaining : Word MachineCodeSymbol)
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .bubbleCell
  tape :=
    match remaining with
    | [] =>
        { left := metadata.map some
          head := none
          right :=
            some MachineCodeSymbol.blank ::
              List.replicate rightPadding none }
    | current :: more =>
        { left :=
            more.map some ++ none :: metadata.map some
          head := some current
          right :=
            some MachineCodeSymbol.blank ::
              List.replicate rightPadding none }

def bubbleEraseCellConfig
    (more metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .bubbleEraseCell
  tape :=
    { left :=
        some MachineCodeSymbol.blank ::
          (more.map some ++ none :: metadata.map some)
      head := some MachineCodeSymbol.blank
      right := List.replicate rightPadding none }

def bubbleMoveCellConfig
    (more metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .bubbleMoveCell
  tape :=
    { left := more.map some ++ none :: metadata.map some
      head := some MachineCodeSymbol.blank
      right := none :: List.replicate rightPadding none }

def bubbleEraseBarrierConfig
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .bubbleEraseBarrier
  tape :=
    { left := some MachineCodeSymbol.blank :: metadata.map some
      head := some MachineCodeSymbol.blank
      right := List.replicate rightPadding none }

def bubbleMoveBarrierConfig
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .bubbleMoveBarrier
  tape :=
    { left := metadata.map some
      head := some MachineCodeSymbol.blank
      right := none :: List.replicate rightPadding none }

theorem cleanupContextRight_boundary_step
    (rowCount rightPadding : Nat)
    (metadata : Word MachineCodeSymbol) :
    machine.stepConfig
        (cleanupContextRightConfig
          (parsedTableLeftRev rowCount ++ metadata.map some)
          0 rightPadding) =
      some
        (bubbleCellConfig
          (MachineCodeSymbol.done ::
            List.replicate rowCount MachineCodeSymbol.blank)
          metadata rightPadding) := by
  cases rowCount <;> cases rightPadding <;> cases metadata <;>
    simp [cleanupContextRightConfig, cleanupContextRightTape,
      parsedTableLeftRev, bubbleCellConfig,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ, List.append_assoc]

theorem bubbleCell_step
    (current : MachineCodeSymbol)
    (more metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    machine.stepConfig
        (bubbleCellConfig (current :: more) metadata rightPadding) =
      some (bubbleEraseCellConfig more metadata rightPadding) := by
  cases current <;> cases more <;> cases metadata <;>
    cases rightPadding <;>
      simp [bubbleCellConfig, bubbleEraseCellConfig,
        machine, transition, TuringMachine.stepConfig,
        Tape.read, Tape.write, Tape.move, Tape.moveRight,
        List.replicate_succ]

theorem bubbleEraseCell_step
    (more metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    machine.stepConfig
        (bubbleEraseCellConfig more metadata rightPadding) =
      some (bubbleMoveCellConfig more metadata rightPadding) := by
  cases more <;> cases metadata <;> cases rightPadding <;>
    simp [bubbleEraseCellConfig, bubbleMoveCellConfig,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

theorem bubbleMoveCell_step
    (more metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    machine.stepConfig
        (bubbleMoveCellConfig more metadata rightPadding) =
      some (bubbleCellConfig more metadata rightPadding.succ) := by
  cases more <;> cases metadata <;> cases rightPadding <;>
    simp [bubbleMoveCellConfig, bubbleCellConfig,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

theorem bubbleBarrier_step
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    machine.stepConfig
        (bubbleCellConfig [] metadata rightPadding) =
      some (bubbleEraseBarrierConfig metadata rightPadding) := by
  cases metadata <;> cases rightPadding <;>
    simp [bubbleCellConfig, bubbleEraseBarrierConfig,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

theorem bubbleEraseBarrier_step
    (metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    machine.stepConfig
        (bubbleEraseBarrierConfig metadata rightPadding) =
      some (bubbleMoveBarrierConfig metadata rightPadding) := by
  cases metadata <;> cases rightPadding <;>
    simp [bubbleEraseBarrierConfig, bubbleMoveBarrierConfig,
      machine, transition, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ]

def crossHaltDoneConfig
    (fuel stateCount start halt rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .crossHaltDone
  tape :=
    { left :=
        (List.append
          (List.replicate halt MachineCodeSymbol.tick)
          (List.append (MachineDescription.encodeNat start).reverse
            (List.append
              (MachineDescription.encodeNat stateCount).reverse
              (MachineCodeSymbol.header ::
                (MachineDescription.encodeNat fuel).reverse)))).map some
      head := some MachineCodeSymbol.done
      right :=
        some MachineCodeSymbol.blank ::
          List.replicate rightPadding none }

theorem bubbleSingleMove_step
    (fuel stateCount start halt rightPadding : Nat) :
    machine.stepConfig
        (bubbleSingleMoveConfig
          (metadataLeftRev fuel stateCount start halt) rightPadding) =
      some
        (crossHaltDoneConfig fuel stateCount start halt
          rightPadding.succ) := by
  cases fuel <;> cases stateCount <;> cases start <;> cases halt <;>
    cases rightPadding <;>
      simp [bubbleSingleMoveConfig, crossHaltDoneConfig,
        metadataLeftRev, machine, transition,
        TuringMachine.stepConfig, MachineDescription.encodeNat,
        encodeNat_reverse_eq_done_ticks,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        List.map_append, List.replicate_succ, replicate_append_self_cons]

theorem noBarrier_cleanup_computes_to_crossHaltDone
    (fuel stateCount start halt : Nat)
    (payload : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (noBarrierSourceConfig
        (metadataLeftRev fuel stateCount start halt) payload)
      (crossHaltDoneConfig fuel stateCount start halt
        (((noBarrierPayloadTail payload).length + 1).succ)) := by
  let metadata := metadataLeftRev fuel stateCount start halt
  let tail := noBarrierPayloadTail payload
  have hpreserve := computes_one_of_stepConfig
    (noBarrier_preserveBlank_step metadata payload)
  have herase := computes_of_run_exact
    (noBarrier_eraseRight_run_exact metadata tail 0)
  have hfinish := computes_one_of_stepConfig
    (noBarrier_eraseRight_finish_step metadata tail.length)
  have hcleanup := computes_of_run_exact
    (noBarrier_cleanupRight_run_exact metadata tail.length 1)
  have hboundary := computes_one_of_stepConfig
    (noBarrier_cleanupRight_boundary_step metadata (tail.length + 1))
  have hdone := computes_one_of_stepConfig
    (bubbleSingleDone_step metadata (tail.length + 1))
  have heraseSingle := computes_one_of_stepConfig
    (bubbleSingleErase_step metadata (tail.length + 1))
  have hmove := computes_one_of_stepConfig
    (bubbleSingleMove_step fuel stateCount start halt (tail.length + 1))
  apply TuringMachine.computes_trans
    (by simpa [metadata, tail] using hpreserve)
  apply TuringMachine.computes_trans
    (by simpa [tail] using herase)
  apply TuringMachine.computes_trans
    (by simpa [tail] using hfinish)
  apply TuringMachine.computes_trans
    (by simpa [tail] using hcleanup)
  apply TuringMachine.computes_trans
    (by simpa [tail] using hboundary)
  apply TuringMachine.computes_trans
    (by simpa [tail] using hdone)
  apply TuringMachine.computes_trans
    (by simpa [tail] using heraseSingle)
  simpa [metadata, tail] using hmove

theorem bubbleMoveBarrier_step
    (fuel stateCount start halt rightPadding : Nat) :
    machine.stepConfig
        (bubbleMoveBarrierConfig
          (metadataLeftRev fuel stateCount start halt) rightPadding) =
      some
        (crossHaltDoneConfig fuel stateCount start halt
          rightPadding.succ) := by
  cases fuel <;> cases stateCount <;> cases start <;> cases halt <;>
    cases rightPadding <;>
      simp [bubbleMoveBarrierConfig, crossHaltDoneConfig,
        metadataLeftRev, machine, transition,
        TuringMachine.stepConfig, MachineDescription.encodeNat,
        encodeNat_reverse_eq_done_ticks,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        List.map_append, List.replicate_succ, replicate_append_self_cons]

theorem bubbleCells_computes
    (remaining metadata : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Computes machine
      (bubbleCellConfig remaining metadata rightPadding)
      (bubbleCellConfig [] metadata
        (remaining.length + rightPadding)) := by
  induction remaining generalizing rightPadding with
  | nil =>
      simpa using
        (TuringMachine.Computes.refl
          (bubbleCellConfig [] metadata rightPadding))
  | cons current more ih =>
      have hcell := computes_one_of_stepConfig
        (bubbleCell_step current more metadata rightPadding)
      have herase := computes_one_of_stepConfig
        (bubbleEraseCell_step more metadata rightPadding)
      have hmove := computes_one_of_stepConfig
        (bubbleMoveCell_step more metadata rightPadding)
      apply TuringMachine.computes_trans hcell
      apply TuringMachine.computes_trans herase
      apply TuringMachine.computes_trans hmove
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih rightPadding.succ

theorem bubbleBarrier_computes
    (fuel stateCount start halt rightPadding : Nat) :
    TuringMachine.Computes machine
      (bubbleCellConfig []
        (metadataLeftRev fuel stateCount start halt) rightPadding)
      (crossHaltDoneConfig fuel stateCount start halt
        rightPadding.succ) := by
  apply TuringMachine.computes_trans
    (computes_one_of_stepConfig
      (bubbleBarrier_step
        (metadataLeftRev fuel stateCount start halt) rightPadding))
  apply TuringMachine.computes_trans
    (computes_one_of_stepConfig
      (bubbleEraseBarrier_step
        (metadataLeftRev fuel stateCount start halt) rightPadding))
  exact computes_one_of_stepConfig
    (bubbleMoveBarrier_step fuel stateCount start halt rightPadding)

theorem contextual_cleanup_computes_to_crossHaltDone
    (fuel stateCount start halt rowCount : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (contextSourceConfig
        (parsedTableLeftRev rowCount ++
          (metadataLeftRev fuel stateCount start halt).map some)
        first rest)
      (crossHaltDoneConfig fuel stateCount start halt
        ((MachineCodeSymbol.done ::
          List.replicate rowCount MachineCodeSymbol.blank).length +
          (rest.length + 1)).succ) := by
  let metadata := metadataLeftRev fuel stateCount start halt
  let tablePrefix : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      List.replicate rowCount MachineCodeSymbol.blank
  have hpreserve := computes_one_of_stepConfig
    (context_preserveBlank_step
      (parsedTableLeftRev rowCount ++ metadata.map some) first rest)
  have herase := computes_of_run_exact
    (context_eraseRight_run_exact
      (some MachineCodeSymbol.blank ::
        (parsedTableLeftRev rowCount ++ metadata.map some)) rest 0)
  have hfinish := computes_one_of_stepConfig
    (context_eraseRight_finish_step
      (parsedTableLeftRev rowCount ++ metadata.map some) rest.length)
  have hcleanup := computes_of_run_exact
    (cleanupContextRight_run_exact
      (parsedTableLeftRev rowCount ++ metadata.map some)
      rest.length 1)
  have hboundary := computes_one_of_stepConfig
    (cleanupContextRight_boundary_step rowCount (rest.length + 1)
      metadata)
  have hbubble := bubbleCells_computes tablePrefix metadata (rest.length + 1)
  have hbarrier := bubbleBarrier_computes fuel stateCount start halt
    (tablePrefix.length + (rest.length + 1))
  apply TuringMachine.computes_trans hpreserve
  apply TuringMachine.computes_trans
    (by simpa using herase)
  apply TuringMachine.computes_trans hfinish
  apply TuringMachine.computes_trans
    (by simpa [Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hcleanup)
  apply TuringMachine.computes_trans
    (by simpa [metadata] using hboundary)
  apply TuringMachine.computes_trans
    (by simpa [tablePrefix] using hbubble)
  simpa [metadata, tablePrefix] using hbarrier

theorem cleanupRight_boundary_step
    (fuel stateCount start halt rightPadding : Nat) :
    machine.stepConfig
        (cleanupRightConfig
          (metadataLeftRev fuel stateCount start halt) 0 rightPadding) =
      some
        (crossHaltDoneConfig fuel stateCount start halt rightPadding) := by
  cases rightPadding <;>
    simp [cleanupRightConfig, cleanupRightTape, crossHaltDoneConfig,
      metadataLeftRev, machine, transition,
      TuringMachine.stepConfig, encodeNat_reverse_eq_done_ticks,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.map_append]

end FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal
end Computability
end FoC
