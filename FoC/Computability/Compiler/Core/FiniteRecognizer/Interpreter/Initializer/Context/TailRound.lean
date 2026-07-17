import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.Locator

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.BooleanContextRawTail

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.RuntimeEncodedList
open FiniteRecognizer.Interpreter.BooleanContextMaterializer

/-!
# Boolean-context raw-tail round

The machine starts on the unary count of an encoded Boolean right list. It
crosses the payload, recognizes the preserved header before the raw input
tail, scans to the physical right blank, stores and deletes the rightmost raw
symbol, and rewinds to the far-left canonical word. Raw symbols may equal
header; only the physical right blank terminates the scan.
-/

namespace RawTailPop

inductive Control where
  | locate (inner : PayloadLocator.Control)
  | bounce
  | payload
  | inspect
  | scanRaw
  | takeLast
  | rewind (saved : MachineCodeSymbol)
  | ready (saved : MachineCodeSymbol)
  | empty
deriving DecidableEq

namespace Control

def elems : List Control :=
  PayloadLocator.Control.finite.elems.map Control.locate ++
    [.bounce, .payload, .inspect, .scanRaw, .takeLast, .empty] ++
    MachineCodeSymbol.finite.elems.map Control.rewind ++
    MachineCodeSymbol.finite.elems.map Control.ready

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate inner =>
        simp [elems, PayloadLocator.Control.finite.complete inner]
    | bounce => simp [elems]
    | payload => simp [elems]
    | inspect => simp [elems]
    | scanRaw => simp [elems]
    | takeLast => simp [elems]
    | rewind saved =>
        simp [elems, MachineCodeSymbol.finite.complete saved]
    | ready saved =>
        simp [elems, MachineCodeSymbol.finite.complete saved]
    | empty => simp [elems]

end Control

def isCellSymbol : MachineCodeSymbol -> Bool
  | MachineCodeSymbol.blank
  | MachineCodeSymbol.zero
  | MachineCodeSymbol.one => true
  | _ => false

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate .gate, read =>
      some (read, Direction.left, .bounce)
  | .locate inner, read =>
      match PayloadLocator.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .locate target)
  | .bounce, read =>
      some (read, Direction.right, .payload)
  | .payload, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .inspect)
  | .payload, some symbol =>
      if isCellSymbol symbol then
        some (some symbol, Direction.right, .payload)
      else none
  | .inspect, some symbol =>
      some (some symbol, Direction.right, .scanRaw)
  | .inspect, none =>
      some (none, Direction.left, .empty)
  | .scanRaw, some symbol =>
      some (some symbol, Direction.right, .scanRaw)
  | .scanRaw, none =>
      some (none, Direction.left, .takeLast)
  | .takeLast, some saved =>
      some (none, Direction.left, .rewind saved)
  | .rewind saved, some symbol =>
      some (some symbol, Direction.left, .rewind saved)
  | .rewind saved, none =>
      some (none, Direction.right, .ready saved)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .locate .count
  halt := .empty
  transition := transition
  statesFinite := Control.finite

def locateConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      PayloadLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .locate config.state
    tape := config.tape }

theorem locate_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      PayloadLocator.Control)
    (hstep : PayloadLocator.machine.stepConfig source = some target) :
    machine.stepConfig (locateConfig source) =
      some (locateConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [PayloadLocator.machine] at hstep
      cases htransition :
          PayloadLocator.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot : inner ≠ PayloadLocator.Control.gate := by
            intro hgate
            subst inner
            simp [PayloadLocator.transition] at htransition
          simp [machine, transition, locateConfig, htransition]

theorem locate_run_of_some :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        PayloadLocator.Control),
      PayloadLocator.machine.runConfigExact? steps source = some target ->
        machine.runConfigExact? steps (locateConfig source) =
          some (locateConfig target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using
        congrArg locateConfig (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : PayloadLocator.machine.stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [locate_step_of_some source next hstep]
          simp only
          exact ih next target hrun

theorem locate_payload_handoff_exact
    (leftHead rightHead : MachineCodeSymbol)
    (leftRev right : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.locate .gate
          tape := SerializedShift.cursorTape (leftHead :: leftRev)
            (rightHead :: right) } =
      some
        { state := Control.payload
          tape := SerializedShift.cursorTape (leftHead :: leftRev)
            (rightHead :: right) } := by
  rfl

theorem step_payload_cell
    (cell : Option Bool)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.payload
          tape := SerializedShift.cursorTape leftRev
            (Prepend.cellSymbol cell :: suffix) } =
      some
        { state := Control.payload
          tape := SerializedShift.cursorTape
            (Prepend.cellSymbol cell :: leftRev) suffix } := by
  cases cell with
  | none => cases suffix <;> rfl
  | some bit => cases bit <;> cases suffix <;> rfl

def payloadLeftRev
    (baseLeftRev : Word MachineCodeSymbol) :
    List (Option Bool) -> Word MachineCodeSymbol
  | [] => baseLeftRev
  | cell :: cells =>
      payloadLeftRev (Prepend.cellSymbol cell :: baseLeftRev) cells

theorem run_payload_cells
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? cells.length
        { state := Control.payload
          tape := SerializedShift.cursorTape baseLeftRev
            (MachineDescription.encodeCellsAppend cells suffix) } =
      some
        { state := Control.payload
          tape := SerializedShift.cursorTape
            (payloadLeftRev baseLeftRev cells) suffix } := by
  induction cells generalizing baseLeftRev with
  | nil => rfl
  | cons cell cells ih =>
      change machine.runConfigExact? (cells.length + 1)
        { state := Control.payload
          tape := SerializedShift.cursorTape baseLeftRev
            (MachineDescription.encodeCellAppend cell
              (MachineDescription.encodeCellsAppend cells suffix)) } = _
      have hcell :
          MachineDescription.encodeCellAppend cell
              (MachineDescription.encodeCellsAppend cells suffix) =
            Prepend.cellSymbol cell ::
              MachineDescription.encodeCellsAppend cells suffix := by
        cases cell with
        | none => rfl
        | some bit => cases bit <;> rfl
      rw [hcell, TuringMachine.runConfigExact?, step_payload_cell]
      simp only
      simpa [payloadLeftRev] using
        ih (Prepend.cellSymbol cell :: baseLeftRev)

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  locateConfig
    (PayloadLocator.sourceConfig baseLeftRev cells.length
      (MachineDescription.encodeCellsAppend cells
        (MachineCodeSymbol.header :: raw)))

def payloadBaseLeftRev
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) : Word MachineCodeSymbol :=
  payloadLeftRev
    (PayloadLocator.targetLeftRev baseLeftRev cells.length) cells

def rawBaseLeftRev
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header :: payloadBaseLeftRev baseLeftRev cells

def wordBeforeRaw
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) : Word MachineCodeSymbol :=
  List.append baseLeftRev.reverse
    (MachineDescription.encodeCellListAppend cells
      [MachineCodeSymbol.header])

theorem payloadLeftRev_reverse
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    (payloadLeftRev baseLeftRev cells).reverse =
      List.append baseLeftRev.reverse
        (MachineDescription.encodeCells cells) := by
  have hencode : forall (cell : Option Bool) (rest : List (Option Bool)),
      MachineDescription.encodeCells (cell :: rest) =
        Prepend.cellSymbol cell :: MachineDescription.encodeCells rest := by
    intro cell rest
    cases cell with
    | none => rfl
    | some bit => cases bit <;> rfl
  induction cells generalizing baseLeftRev with
  | nil =>
      simp [payloadLeftRev, MachineDescription.encodeCells,
        MachineDescription.encodeCellsAppend]
  | cons cell cells ih =>
      rw [payloadLeftRev, ih]
      rw [hencode]
      simp [List.append_assoc]

theorem locatorTargetLeftRev_reverse
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) :
    (PayloadLocator.targetLeftRev baseLeftRev count).reverse =
      List.append baseLeftRev.reverse
        (MachineDescription.encodeNat count) := by
  rw [FiniteRecognizer.Interpreter.UniformInterpreterOneStep.runtimeKey_encodeNat_eq_replicate_tick_done]
  simp [PayloadLocator.targetLeftRev, PayloadLocator.ticks,
    List.reverse_replicate, List.append_assoc]

theorem rawBaseLeftRev_reverse
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    (rawBaseLeftRev baseLeftRev cells).reverse =
      wordBeforeRaw baseLeftRev cells := by
  rw [rawBaseLeftRev, List.reverse_cons, payloadBaseLeftRev,
    payloadLeftRev_reverse, locatorTargetLeftRev_reverse]
  simp [wordBeforeRaw, MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend, MachineDescription.encodeCells,
    List.append_assoc]
  change
    (List.append (MachineDescription.encodeCellsAppend cells [])
      [MachineCodeSymbol.header] : Word MachineCodeSymbol) =
      MachineDescription.encodeCellsAppend cells
        [MachineCodeSymbol.header]
  exact (encodeCellsAppend_append cells []
    [MachineCodeSymbol.header]).symm

theorem payload_header_step
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol) :
    machine.runConfigExact? 1
        { state := Control.payload
          tape := SerializedShift.cursorTape
            (payloadBaseLeftRev baseLeftRev cells)
            (MachineCodeSymbol.header :: raw) } =
      some
        { state := Control.inspect
          tape := SerializedShift.cursorTape
            (rawBaseLeftRev baseLeftRev cells) raw } := by
  cases raw <;> rfl

theorem scanRaw_run_exact
    (leftRev raw : Word MachineCodeSymbol) :
    machine.runConfigExact? raw.length
        { state := Control.scanRaw
          tape := SerializedShift.cursorTape leftRev raw } =
      some
        { state := Control.scanRaw
          tape := SerializedShift.cursorTape
            (List.append raw.reverse leftRev) [] } := by
  induction raw generalizing leftRev with
  | nil => rfl
  | cons current rest ih =>
      change machine.runConfigExact? (rest.length + 1) _ = _
      rw [TuringMachine.runConfigExact?]
      have hstep : machine.stepConfig
          { state := Control.scanRaw
            tape := SerializedShift.cursorTape leftRev (current :: rest) } =
        some
          { state := Control.scanRaw
            tape := SerializedShift.cursorTape (current :: leftRev) rest } := by
        cases rest <;> rfl
      rw [hstep]
      simp only
      simpa [List.reverse_cons, List.append_assoc] using
        ih (current :: leftRev)

theorem inspect_nonempty_run_exact
    (leftRev rawPrefix : Word MachineCodeSymbol)
    (last : MachineCodeSymbol) :
    machine.runConfigExact? (rawPrefix.length + 1)
        { state := Control.inspect
          tape := SerializedShift.cursorTape leftRev
            (List.append rawPrefix [last]) } =
      some
        { state := Control.scanRaw
          tape := SerializedShift.cursorTape
            (last :: List.append rawPrefix.reverse leftRev) [] } := by
  cases rawPrefix with
  | nil => rfl
  | cons first rest =>
      let restW : Word MachineCodeSymbol := rest
      change machine.runConfigExact? ((rest.length + 1) + 1) _ = _
      rw [TuringMachine.runConfigExact?]
      have hstep : machine.stepConfig
          { state := Control.inspect
            tape := SerializedShift.cursorTape leftRev
              (first :: List.append restW [last]) } =
        some
          { state := Control.scanRaw
            tape := SerializedShift.cursorTape (first :: leftRev)
              (List.append restW [last]) } := by
        cases restW <;> rfl
      have hsource :
          (List.append (first :: rest) [last] :
            Word MachineCodeSymbol) =
            first :: List.append restW [last] := by
        rfl
      rw [hsource, hstep]
      simp only
      have hscan := scanRaw_run_exact (first :: leftRev)
        (List.append restW [last])
      simpa [List.reverse_append, List.reverse_cons,
        List.append_assoc, restW] using hscan

def rewindConfig
    (saved : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .rewind saved
    tape := RewindWord.scanTape remainingRev crossed 1 }

def readyConfig
    (saved : MachineCodeSymbol)
    (word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .ready saved
    tape := RewindWord.gateTape word 1 }

theorem delete_last_handoff_exact
    (wordBeforeLast : Word MachineCodeSymbol)
    (last : MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.scanRaw
          tape := SerializedShift.cursorTape
            (last :: wordBeforeLast.reverse) [] } =
      some (rewindConfig last wordBeforeLast.reverse []) := by
  cases hreverse : wordBeforeLast.reverse <;> rfl

theorem rewind_scan_step
    (saved current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindConfig saved (current :: remainingRev) crossed) =
      some (rewindConfig saved remainingRev (current :: crossed)) := by
  cases remainingRev <;> rfl

theorem rewind_scan_finish
    (saved : MachineCodeSymbol)
    (crossed : Word MachineCodeSymbol) :
    machine.stepConfig (rewindConfig saved [] crossed) =
      some (readyConfig saved crossed) := by
  cases crossed <;> rfl

theorem rewind_scan_run_exact
    (saved : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    machine.runConfigExact? (remainingRev.length + 1)
        (rewindConfig saved remainingRev crossed) =
      some
        (readyConfig saved
          (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil => exact rewind_scan_finish saved crossed
  | cons current remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1) _ = _
      rw [TuringMachine.runConfigExact?, rewind_scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

def emptyConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .empty
    tape := Tape.move Direction.left
      (SerializedShift.cursorTape (rawBaseLeftRev baseLeftRev cells) []) }

theorem inspect_empty_run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    machine.runConfigExact? 1
        { state := Control.inspect
          tape := SerializedShift.cursorTape
            (rawBaseLeftRev baseLeftRev cells) [] } =
      some (emptyConfig baseLeftRev cells) := by
  rfl

theorem empty_computes
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    TuringMachine.Computes machine
      (sourceConfig baseLeftRev cells [])
      (emptyConfig baseLeftRev cells) := by
  have hlocateInner := PayloadLocator.run_exact baseLeftRev cells.length
    (MachineDescription.encodeCellsAppend cells
      [MachineCodeSymbol.header])
  have hlocate := locate_run_of_some _ _ _ hlocateInner
  have hhandoff : machine.runConfigExact? 2
      (locateConfig
        (PayloadLocator.targetConfig baseLeftRev cells.length
          (MachineDescription.encodeCellsAppend cells
            [MachineCodeSymbol.header]))) =
    some
      { state := Control.payload
        tape := SerializedShift.cursorTape
          (PayloadLocator.targetLeftRev baseLeftRev cells.length)
          (MachineDescription.encodeCellsAppend cells
            [MachineCodeSymbol.header]) } := by
    cases cells with
    | nil => rfl
    | cons cell cells =>
        cases cell with
        | none => rfl
        | some bit => cases bit <;> rfl
  have hpayload := run_payload_cells
    (PayloadLocator.targetLeftRev baseLeftRev cells.length) cells
    [MachineCodeSymbol.header]
  have hheader := payload_header_step baseLeftRev cells []
  have hempty := inspect_empty_run_exact baseLeftRev cells
  exact TuringMachine.computes_trans
    (TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hlocate))
    (TuringMachine.computes_trans
      (TuringMachine.computesIn_to_computes
        (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hhandoff))
      (TuringMachine.computes_trans
        (TuringMachine.computesIn_to_computes
          (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hpayload))
        (TuringMachine.computes_trans
          (TuringMachine.computesIn_to_computes
            (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hheader))
          (TuringMachine.computesIn_to_computes
            (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
              hempty)))))

def runSteps
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (rawPrefix : Word MachineCodeSymbol) : Nat :=
  (cells.length + 1) + 2 + cells.length + 1 +
    (rawPrefix.length + 1) + 2 +
    ((List.append (wordBeforeRaw baseLeftRev cells) rawPrefix).length + 1)

theorem nonempty_run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (rawPrefix : Word MachineCodeSymbol)
    (last : MachineCodeSymbol) :
    machine.runConfigExact? (runSteps baseLeftRev cells rawPrefix)
        (sourceConfig baseLeftRev cells
          (List.append rawPrefix [last])) =
      some
        (readyConfig last
          (List.append (wordBeforeRaw baseLeftRev cells) rawPrefix)) := by
  have hlocateInner := PayloadLocator.run_exact baseLeftRev cells.length
    (MachineDescription.encodeCellsAppend cells
      (MachineCodeSymbol.header :: List.append rawPrefix [last]))
  have hlocate := locate_run_of_some _ _ _ hlocateInner
  have hhandoff' : machine.runConfigExact? 2
      (locateConfig
        (PayloadLocator.targetConfig baseLeftRev cells.length
          (MachineDescription.encodeCellsAppend cells
            (MachineCodeSymbol.header :: List.append rawPrefix [last])))) =
    some
      { state := Control.payload
        tape := SerializedShift.cursorTape
          (PayloadLocator.targetLeftRev baseLeftRev cells.length)
          (MachineDescription.encodeCellsAppend cells
            (MachineCodeSymbol.header :: List.append rawPrefix [last])) } := by
    cases cells with
    | nil => rfl
    | cons cell cells =>
        cases cell with
        | none => rfl
        | some bit => cases bit <;> rfl
  have hpref := TuringMachine.runConfigExact?_trans hlocate hhandoff'
  have hpayload := run_payload_cells
    (PayloadLocator.targetLeftRev baseLeftRev cells.length) cells
    (MachineCodeSymbol.header :: List.append rawPrefix [last])
  have hpref := TuringMachine.runConfigExact?_trans hpref hpayload
  have hheader := payload_header_step baseLeftRev cells
    (List.append rawPrefix [last])
  have hpref := TuringMachine.runConfigExact?_trans hpref hheader
  have hraw := inspect_nonempty_run_exact
    (rawBaseLeftRev baseLeftRev cells) rawPrefix last
  have hpref := TuringMachine.runConfigExact?_trans hpref hraw
  let wordBeforeLast :=
    List.append (wordBeforeRaw baseLeftRev cells) rawPrefix
  have hleft :
      last :: List.append rawPrefix.reverse
          (rawBaseLeftRev baseLeftRev cells) =
        last :: wordBeforeLast.reverse := by
    simp only [wordBeforeLast]
    rw [← rawBaseLeftRev_reverse baseLeftRev cells]
    simp
  have hdelete := delete_last_handoff_exact wordBeforeLast last
  rw [← hleft] at hdelete
  have hpref := TuringMachine.runConfigExact?_trans hpref hdelete
  have hrewind := rewind_scan_run_exact last wordBeforeLast.reverse []
  have hrewind' : machine.runConfigExact?
      (wordBeforeLast.length + 1)
      (rewindConfig last wordBeforeLast.reverse []) =
    some (readyConfig last wordBeforeLast) := by
    simpa [wordBeforeLast, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hrewind
  have hrun := TuringMachine.runConfigExact?_trans hpref hrewind'
  simpa [runSteps, sourceConfig, payloadBaseLeftRev,
    wordBeforeLast, List.length_append, Nat.add_assoc] using hrun

theorem nonempty_target_equiv_input
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (rawPrefix : Word MachineCodeSymbol)
    (last : MachineCodeSymbol) :
    Tape.Equiv
      (readyConfig last
        (List.append (wordBeforeRaw baseLeftRev cells) rawPrefix)).tape
      (Tape.input
        (List.append (wordBeforeRaw baseLeftRev cells) rawPrefix)) := by
  exact RewindWord.gateTape_equiv_input _ 1


end RawTailPop

end FiniteRecognizer.Interpreter.BooleanContextRawTail

end Computability
end FoC
