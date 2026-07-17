import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Positioned left-field edits

Finite location, insertion, and count-update phases at the serialized left-side
frame boundaries.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Edits
namespace PositionedLeft

open SerializedFieldComposer

namespace Locator

inductive Boundary where
  | leftPayload
  | leftCountDone
deriving DecidableEq

inductive Control where
  | fields (inner : FieldLocator.Control)
  | countScan
  | countReturn
  | gate
deriving DecidableEq

namespace Control

def elems : List Control :=
  (FieldLocator.Control.finite.elems.map Control.fields) ++
    [.countScan, .countReturn, .gate]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | fields inner =>
        have h := FieldLocator.Control.finite.complete inner
        simp [elems, h]
    | countScan => simp [elems]
    | countReturn => simp [elems]
    | gate => simp [elems]

end Control

def fieldBoundary : Boundary -> FieldLocator.Boundary
  | .leftPayload => .leftPayload
  | .leftCountDone => .leftCount

def transition (boundary : Boundary) :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .fields .gate, read =>
      match boundary, read with
      | .leftPayload, _ => none
      | .leftCountDone, some MachineCodeSymbol.tick =>
          some (some MachineCodeSymbol.tick, Direction.right, .countScan)
      | .leftCountDone, some MachineCodeSymbol.done =>
          some (some MachineCodeSymbol.done, Direction.right, .countReturn)
      | .leftCountDone, _ => none
  | .fields inner, read =>
      match FieldLocator.transition (fieldBoundary boundary) inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .fields target)
  | .countScan, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .countScan)
  | .countScan, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .countReturn)
  | .countReturn, read =>
      some (read, Direction.left, .gate)
  | _, _ => none

def halt : Boundary -> Control
  | .leftPayload => .fields .gate
  | .leftCountDone => .gate

def machine (boundary : Boundary) :
    TuringMachine MachineCodeSymbol Control where
  start := .fields .header
  halt := halt boundary
  transition := transition boundary
  statesFinite := Control.finite

def fieldsConfig
    (c : TuringMachine.Configuration MachineCodeSymbol FieldLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .fields c.state
  tape := c.tape

def config (control : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := SerializedShift.cursorTape leftRev rest

theorem fields_step_of_some
    (boundary : Boundary)
    (c d : TuringMachine.Configuration MachineCodeSymbol FieldLocator.Control)
    (hstep : (FieldLocator.machine (fieldBoundary boundary)).stepConfig c =
      some d) :
    (machine boundary).stepConfig (fieldsConfig c) =
      some (fieldsConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FieldLocator.machine] at hstep
      cases htransition :
          FieldLocator.transition (fieldBoundary boundary) inner
            (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have hnot : inner ≠ FieldLocator.Control.gate := by
            intro hgate
            subst inner
            simp [FieldLocator.transition] at htransition
          simp [machine, transition, fieldsConfig, htransition]

theorem fields_run_of_some (boundary : Boundary) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        FieldLocator.Control),
      (FieldLocator.machine (fieldBoundary boundary)).runConfigExact?
          steps source = some target ->
        (machine boundary).runConfigExact? steps
            (fieldsConfig source) = some (fieldsConfig target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using congrArg fieldsConfig
        (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep :
          (FieldLocator.machine (fieldBoundary boundary)).stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [fields_step_of_some boundary source next hstep]
          simp only
          exact ih next target hrun

def leftPayloadSteps {stateCount : Nat} (L : Layout stateCount) : Nat :=
  FieldLocator.leftPayloadSteps L

theorem leftPayload_exact {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    (machine .leftPayload).runConfigExact? (leftPayloadSteps L)
        (fieldsConfig (FieldLocator.startConfig L callerData)) =
      some
        (config (.fields .gate)
          (LeftPrepend.leftPayloadPrefix L).reverse
          (LeftPrepend.leftPayloadSuffix L callerData)) := by
  exact fields_run_of_some .leftPayload _ _ _
    (FieldLocator.locate_leftPayload_exact L callerData)

def leftCountPrefixSteps (fuel state : Nat) : Nat :=
  1 + ((fuel + 1) + (state + 1))

def rawLeftCountPrefix
    (fuel state : Nat) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    MachineDescription.encodeNatAppend fuel
      (MachineDescription.encodeNat state)

theorem field_leftCount_prefix_exact
    (fuel state : Nat) (suffix : Word MachineCodeSymbol) :
    (FieldLocator.machine .leftCount).runConfigExact?
        (leftCountPrefixSteps fuel state)
        (FieldLocator.config .header []
          (MachineCodeSymbol.header ::
            MachineDescription.encodeNatAppend fuel
              (MachineDescription.encodeNatAppend state suffix))) =
      some
        (FieldLocator.config .gate
          (rawLeftCountPrefix fuel state).reverse suffix) := by
  unfold leftCountPrefixSteps
  rw [TuringMachine.runConfigExact?_add]
  have hheader :
      (FieldLocator.machine .leftCount).runConfigExact? 1
          (FieldLocator.config .header []
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend fuel
                (MachineDescription.encodeNatAppend state suffix))) =
        some
          (FieldLocator.config .fuel [MachineCodeSymbol.header]
            (MachineDescription.encodeNatAppend fuel
              (MachineDescription.encodeNatAppend state suffix))) := by
    rw [TuringMachine.runConfigExact?]
    rw [FieldLocator.header_step]
    rfl
  rw [hheader]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [FieldLocator.fuel_run_later .leftCount (by decide)]
  simp only
  rw [FieldLocator.state_run_leftCount]
  simp [rawLeftCountPrefix, MachineDescription.encodeNatAppend,
    List.reverse_cons, List.reverse_append, List.append_assoc]

theorem fields_leftCount_prefix_exact
    (fuel state : Nat) (suffix : Word MachineCodeSymbol) :
    (machine .leftCountDone).runConfigExact?
        (leftCountPrefixSteps fuel state)
        (config (.fields .header) []
          (MachineCodeSymbol.header ::
            MachineDescription.encodeNatAppend fuel
              (MachineDescription.encodeNatAppend state suffix))) =
      some
        (config (.fields .gate)
          (rawLeftCountPrefix fuel state).reverse suffix) := by
  exact fields_run_of_some .leftCountDone _ _ _
    (field_leftCount_prefix_exact fuel state suffix)

def countScanSteps (count : Nat) : Nat := count + 2

def countTicksLeftRev (count : Nat)
    (leftRev : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (HeadLocator.ticks count).reverse leftRev

def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)

theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape T) T :=
  Machine.moveLeft_moveRight_equiv_self T

def countGateConfig
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate
  tape := roundTripTape
    (SerializedShift.cursorTape (countTicksLeftRev count leftRev)
      (MachineCodeSymbol.done :: suffix))

theorem count_done_bounce_inner_exact
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine .leftCountDone).runConfigExact? 2
        (config .countScan leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some (countGateConfig 0 leftRev suffix) := by
  cases suffix <;> rfl

theorem count_scan_inner_exact
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    (machine .leftCountDone).runConfigExact? (countScanSteps count)
        (config .countScan leftRev
          (MachineDescription.encodeNatAppend count suffix)) =
      some (countGateConfig count leftRev suffix) := by
  induction count generalizing leftRev with
  | zero => exact count_done_bounce_inner_exact leftRev suffix
  | succ count ih =>
      change
        (machine .leftCountDone).runConfigExact? ((count + 2) + 1)
            (config .countScan leftRev
              (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend count suffix)) = _
      rw [TuringMachine.runConfigExact?]
      have hstep :
          (machine .leftCountDone).stepConfig
              (config .countScan leftRev
                (MachineCodeSymbol.tick ::
                  MachineDescription.encodeNatAppend count suffix)) =
            some
              (config .countScan (MachineCodeSymbol.tick :: leftRev)
                (MachineDescription.encodeNatAppend count suffix)) := by
        cases leftRev <;> cases count <;> cases suffix <;> rfl
      rw [hstep]
      simp only
      change
        (machine .leftCountDone).runConfigExact? (countScanSteps count)
            (config .countScan
              ((MachineCodeSymbol.tick :: leftRev) :
                Word MachineCodeSymbol)
              (MachineDescription.encodeNatAppend count suffix)) = _
      rw [ih]
      simp [countGateConfig, countTicksLeftRev, HeadLocator.ticks,
        roundTripTape, List.reverse_cons, List.append_assoc]

theorem count_done_bounce_fields_exact
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine .leftCountDone).runConfigExact? 2
        (config (.fields .gate) leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some (countGateConfig 0 leftRev suffix) := by
  cases suffix <;> rfl

theorem count_scan_exact
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    (machine .leftCountDone).runConfigExact? (countScanSteps count)
        (config (.fields .gate) leftRev
          (MachineDescription.encodeNatAppend count suffix)) =
      some (countGateConfig count leftRev suffix) := by
  cases count with
  | zero => exact count_done_bounce_fields_exact leftRev suffix
  | succ count =>
      change
        (machine .leftCountDone).runConfigExact? ((count + 2) + 1)
            (config (.fields .gate) leftRev
              (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend count suffix)) = _
      rw [TuringMachine.runConfigExact?]
      have hstep :
          (machine .leftCountDone).stepConfig
              (config (.fields .gate) leftRev
                (MachineCodeSymbol.tick ::
                  MachineDescription.encodeNatAppend count suffix)) =
            some
              (config .countScan (MachineCodeSymbol.tick :: leftRev)
                (MachineDescription.encodeNatAppend count suffix)) := by
        cases leftRev <;> cases count <;> cases suffix <;> rfl
      rw [hstep]
      simp only
      change
        (machine .leftCountDone).runConfigExact? (countScanSteps count)
            (config .countScan
              ((MachineCodeSymbol.tick :: leftRev) :
                Word MachineCodeSymbol)
              (MachineDescription.encodeNatAppend count suffix)) = _
      rw [count_scan_inner_exact count
        ((MachineCodeSymbol.tick :: leftRev) :
          Word MachineCodeSymbol) suffix]
      simp [countGateConfig, countTicksLeftRev, HeadLocator.ticks,
        roundTripTape, List.reverse_cons, List.append_assoc]

def leftCountDoneSteps (fuel state count : Nat) : Nat :=
  leftCountPrefixSteps fuel state + countScanSteps count

theorem leftCountDone_raw_exact
    (fuel state count : Nat) (suffix : Word MachineCodeSymbol) :
    (machine .leftCountDone).runConfigExact?
        (leftCountDoneSteps fuel state count)
        (config (.fields .header) []
          (MachineCodeSymbol.header ::
            MachineDescription.encodeNatAppend fuel
              (MachineDescription.encodeNatAppend state
                (MachineDescription.encodeNatAppend count suffix)))) =
      some
        (countGateConfig count
          (rawLeftCountPrefix fuel state).reverse suffix) := by
  unfold leftCountDoneSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [fields_leftCount_prefix_exact]
  simp only
  exact count_scan_exact count
    (rawLeftCountPrefix fuel state).reverse suffix

def afterWriteTail {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (optionalCellWord write)
    (LeftPrepend.leftPayloadSuffix L callerData)

theorem afterWriteWord_shape {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) :
    LeftPrepend.afterWriteWord L write callerData =
      MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend L.fuel
          (MachineDescription.encodeNatAppend L.state.val
            (MachineDescription.encodeNatAppend L.left.length
              (afterWriteTail L write callerData))) := by
  unfold LeftPrepend.afterWriteWord LeftPrepend.leftPayloadPrefix
    LeftPrepend.leftCountPrefix afterWriteTail
  simp [MachineDescription.encodeNatAppend, List.append_assoc]

def canonicalLeftCountDoneSteps {stateCount : Nat}
    (L : Layout stateCount) : Nat :=
  leftCountDoneSteps L.fuel L.state.val L.left.length

theorem canonical_leftCountDone_exact {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) :
    (machine .leftCountDone).runConfigExact?
        (canonicalLeftCountDoneSteps L)
        (config (.fields .header) []
          (LeftPrepend.afterWriteWord L write callerData)) =
      some
        (countGateConfig L.left.length
          (LeftPrepend.leftCountPrefix L).reverse
          (afterWriteTail L write callerData)) := by
  rw [afterWriteWord_shape]
  simpa [canonicalLeftCountDoneSteps, rawLeftCountPrefix,
    LeftPrepend.leftCountPrefix] using
    leftCountDone_raw_exact L.fuel L.state.val L.left.length
      (afterWriteTail L write callerData)

end Locator

inductive Control where
  | locate (inner : Locator.Control)
  | handoffReturn
  | insert (inner : InsertRestagedMachine.Control)
deriving DecidableEq

namespace Control

def elems : List Control :=
  (Locator.Control.finite.elems.map Control.locate) ++
    [Control.handoffReturn] ++
    (InsertRestagedMachine.Control.finite.elems.map Control.insert)

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate inner =>
        have h := Locator.Control.finite.complete inner
        simp [elems, h]
    | handoffReturn => simp [elems]
    | insert inner =>
        have h := InsertRestagedMachine.Control.finite.complete inner
        simp [elems, h]

end Control

def transition (boundary : Locator.Boundary)
    (buffer : InsertBlock.Buffer) :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate inner, read =>
      if inner = Locator.halt boundary then
        some (read, Direction.right, .handoffReturn)
      else
        match Locator.transition boundary inner read with
        | none => none
        | some (write, direction, target) =>
            some (write, direction, .locate target)
  | .handoffReturn, read =>
      some
        (read, Direction.left,
          .insert (.edit (.carry buffer)))
  | .insert inner, read =>
      match InsertRestagedMachine.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .insert target)

def machine (boundary : Locator.Boundary)
    (buffer : InsertBlock.Buffer) :
    TuringMachine MachineCodeSymbol Control where
  start := .locate (.fields .header)
  halt := .insert (.rewind .gate)
  transition := transition boundary buffer
  statesFinite := Control.finite

def locateConfig
    (c : TuringMachine.Configuration MachineCodeSymbol Locator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .locate c.state
  tape := c.tape

def insertConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.insert c

def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)

theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape T) T :=
  Machine.moveLeft_moveRight_equiv_self T

theorem locate_step_of_some
    (boundary : Locator.Boundary)
    (buffer : InsertBlock.Buffer)
    (c d : TuringMachine.Configuration MachineCodeSymbol Locator.Control)
    (hstep : (Locator.machine boundary).stepConfig c = some d) :
    (machine boundary buffer).stepConfig (locateConfig c) =
      some (locateConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Locator.machine] at hstep
      cases htransition : Locator.transition boundary inner
          (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          have hnot : inner ≠ Locator.halt boundary := by
            intro heq
            subst inner
            cases boundary <;>
              simp [Locator.halt, Locator.transition] at htransition
          simp [machine, transition, locateConfig, hnot, htransition]

theorem locate_run_of_some
    (boundary : Locator.Boundary)
    (buffer : InsertBlock.Buffer) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        Locator.Control),
      (Locator.machine boundary).runConfigExact? steps source = some target ->
        (machine boundary buffer).runConfigExact? steps
            (locateConfig source) = some (locateConfig target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using congrArg locateConfig
        (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : (Locator.machine boundary).stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [locate_step_of_some boundary buffer source next hstep]
          simp only
          exact ih next target hrun

theorem handoff_run_exact
    (boundary : Locator.Boundary)
    (buffer : InsertBlock.Buffer) (T : Tape MachineCodeSymbol) :
    (machine boundary buffer).runConfigExact? 2
        { state := Control.locate (Locator.halt boundary), tape := T } =
      some
        (insertConfig
          { state := InsertRestagedMachine.Control.edit (.carry buffer)
            tape := roundTripTape T }) := by
  cases boundary <;>
    simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
      machine, transition, insertConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      roundTripTape, Tape.write_read_eq_self, Locator.halt]

theorem insert_run_of_some
    (boundary : Locator.Boundary)
    (buffer : InsertBlock.Buffer)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control}
    (hrun : (InsertRestagedMachine.machine buffer).runConfigExact?
      steps source = some target) :
    (machine boundary buffer).runConfigExact? steps
        (insertConfig source) = some (insertConfig target) := by
  apply TuringMachine.PhaseEmbedding.runConfigExact?_lift_of_eq_some
    (inner := InsertRestagedMachine.machine buffer)
    (outer := machine boundary buffer) Control.insert
  · intro c
    cases c with
    | mk inner tape =>
        unfold TuringMachine.stepConfig
        simp only [TuringMachine.PhaseEmbedding.liftConfig,
          machine, transition, InsertRestagedMachine.machine]
        cases htransition : InsertRestagedMachine.transition inner
            (Tape.read tape) with
        | none => rfl
        | some action =>
            rcases action with ⟨write, direction, target⟩
            rfl
  · exact hrun

def payloadSteps {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) : Nat :=
  (Locator.leftPayloadSteps L + 2) +
    InsertRestagedMachine.runSteps (InsertBlock.optionalBuffer write)
      (LeftPrepend.leftPayloadPrefix L).reverse
      (LeftPrepend.leftPayloadSuffix L callerData)

/-- Locate the left payload, insert the written cell, and rewind to the
protected-word header. -/
theorem payload_insert_exact {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) :
    exists endpoint,
      (machine .leftPayload (InsertBlock.optionalBuffer write)).runConfigExact?
          (payloadSteps L write callerData)
          (locateConfig
            (Locator.fieldsConfig
              (FieldLocator.startConfig L callerData))) =
        some endpoint ∧
      endpoint.state = Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input (LeftPrepend.afterWriteWord L write callerData))
        endpoint.tape := by
  let buffer := InsertBlock.optionalBuffer write
  let leftRev : Word MachineCodeSymbol :=
    (LeftPrepend.leftPayloadPrefix L).reverse
  let suffix : Word MachineCodeSymbol :=
    LeftPrepend.leftPayloadSuffix L callerData
  have hlocate := Locator.leftPayload_exact L callerData
  have hlocateOuter := locate_run_of_some .leftPayload buffer _ _ _ hlocate
  have hhandoff := handoff_run_exact .leftPayload buffer
    (Locator.config (.fields .gate) leftRev suffix).tape
  have hinsertTape :
      Tape.Equiv
        (InsertRestagedMachine.editConfig
          (InsertBlock.config buffer leftRev suffix)).tape
        (roundTripTape
          (Locator.config (.fields .gate) leftRev suffix).tape) := by
    exact Tape.Equiv.symm
      (roundTripTape_equiv
        (Locator.config (.fields .gate) leftRev suffix).tape)
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (InsertRestagedMachine.run_exact buffer leftRev suffix
          (InsertBlock.optionalBuffer_nonempty write)) hinsertTape with
    ⟨insertEndpoint, hinsert, hinsertState, hinsertTapeFinal⟩
  have hinsertOuter := insert_run_of_some .leftPayload buffer hinsert
  have hpref := TuringMachine.runConfigExact?_trans
    hlocateOuter hhandoff
  have hrun := TuringMachine.runConfigExact?_trans hpref hinsertOuter
  refine ⟨insertConfig insertEndpoint, ?_, ?_, ?_⟩
  · simpa [payloadSteps, buffer, leftRev, suffix, Nat.add_assoc] using hrun
  · simpa [insertConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      InsertRestagedMachine.rewindConfig,
      RewindWord.gateConfig] using hinsertState
  · have hgateInput := RewindWord.gateTape_equiv_input
      (PhysicalBranch.insertOutput buffer leftRev suffix) 0
    have houtput :
        PhysicalBranch.insertOutput buffer leftRev suffix =
          LeftPrepend.afterWriteWord L write callerData := by
      simp [buffer, leftRev, suffix, PhysicalBranch.insertOutput,
        InsertBlock.optionalBuffer, LeftPrepend.afterWriteWord]
    have hinputClean :
        Tape.Equiv
          (Tape.input (LeftPrepend.afterWriteWord L write callerData))
          (InsertRestagedMachine.rewindConfig
            (RewindWord.gateConfig
              (PhysicalBranch.insertOutput buffer leftRev suffix) 0)).tape := by
      rw [← houtput]
      simpa [InsertRestagedMachine.rewindConfig,
        RewindWord.gateConfig] using Tape.Equiv.symm hgateInput
    exact Tape.Equiv.trans hinputClean hinsertTapeFinal

theorem canonical_countGate_tape {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) :
    (Locator.countGateConfig L.left.length
      (LeftPrepend.leftCountPrefix L).reverse
      (Locator.afterWriteTail L write callerData)).tape =
      Locator.roundTripTape
        (SerializedShift.cursorTape
          (LeftPrepend.leftCountTicksPrefix L).reverse
          (LeftPrepend.afterCountDoneSuffix L write callerData)) := by
  simp [Locator.countGateConfig, Locator.countTicksLeftRev,
    LeftPrepend.leftCountTicksPrefix, LeftPrepend.afterCountDoneSuffix,
    Locator.afterWriteTail, List.reverse_append]

def countIncrementSteps {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) : Nat :=
  (Locator.canonicalLeftCountDoneSteps L + 2) +
    InsertRestagedMachine.runSteps
      (InsertBlock.singletonBuffer MachineCodeSymbol.tick)
      (LeftPrepend.leftCountTicksPrefix L).reverse
      (LeftPrepend.afterCountDoneSuffix L write callerData)

/-- Starting on the stale-count intermediate word, insert one unary left-count
tick and rewind to the canonical left-prepended layout. -/
theorem count_increment_exact {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) :
    exists endpoint,
      (machine .leftCountDone
          (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).runConfigExact?
          (countIncrementSteps L write callerData)
          (locateConfig
            (Locator.config (.fields .header) []
              (LeftPrepend.afterWriteWord L write callerData))) =
        some endpoint ∧
      endpoint.state = Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (LeftPrepend.prependedLeftLayout L write) callerData))
        endpoint.tape := by
  let buffer := InsertBlock.singletonBuffer MachineCodeSymbol.tick
  let leftRev : Word MachineCodeSymbol :=
    (LeftPrepend.leftCountTicksPrefix L).reverse
  let suffix : Word MachineCodeSymbol :=
    LeftPrepend.afterCountDoneSuffix L write callerData
  let cleanCursor := SerializedShift.cursorTape leftRev suffix
  let locatorConfig := Locator.countGateConfig L.left.length
    (LeftPrepend.leftCountPrefix L).reverse
    (Locator.afterWriteTail L write callerData)
  let locatorTape := locatorConfig.tape
  have hlocate := Locator.canonical_leftCountDone_exact L write callerData
  have hlocateOuter := locate_run_of_some
    .leftCountDone buffer _ _ _ hlocate
  have hhandoff := handoff_run_exact .leftCountDone buffer locatorTape
  have hlocatorTape : locatorTape = Locator.roundTripTape cleanCursor := by
    exact canonical_countGate_tape L write callerData
  have hlocatorEquiv : Tape.Equiv locatorTape cleanCursor := by
    rw [hlocatorTape]
    exact Locator.roundTripTape_equiv cleanCursor
  have houterEquiv : Tape.Equiv (roundTripTape locatorTape) locatorTape :=
    roundTripTape_equiv locatorTape
  have hinsertTape :
      Tape.Equiv
        (InsertRestagedMachine.editConfig
          (InsertBlock.config buffer leftRev suffix)).tape
        (roundTripTape locatorTape) := by
    exact Tape.Equiv.trans (Tape.Equiv.symm hlocatorEquiv)
      (Tape.Equiv.symm houterEquiv)
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (InsertRestagedMachine.run_exact buffer leftRev suffix
          (InsertBlock.singletonBuffer_nonempty MachineCodeSymbol.tick))
        hinsertTape with
    ⟨insertEndpoint, hinsert, hinsertState, hinsertTapeFinal⟩
  have hinsertOuter := insert_run_of_some .leftCountDone buffer hinsert
  have hpref := TuringMachine.runConfigExact?_trans
    hlocateOuter hhandoff
  have hrun := TuringMachine.runConfigExact?_trans
    hpref hinsertOuter
  refine ⟨insertConfig insertEndpoint, ?_, ?_, ?_⟩
  · simpa [countIncrementSteps, buffer, leftRev, suffix,
      cleanCursor, locatorConfig, locatorTape, Nat.add_assoc] using hrun
  · simpa [insertConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      InsertRestagedMachine.rewindConfig,
      RewindWord.gateConfig] using hinsertState
  · have hgateInput := RewindWord.gateTape_equiv_input
      (PhysicalBranch.insertOutput buffer leftRev suffix) 0
    have houtput :
        PhysicalBranch.insertOutput buffer leftRev suffix =
          Frame.protectedWord
            (LeftPrepend.prependedLeftLayout L write) callerData := by
      simpa [buffer, leftRev, suffix] using
        PhysicalBranch.prependLeft_output_eq_protectedWord
          L write callerData
    have hinputClean :
        Tape.Equiv
          (Tape.input
            (Frame.protectedWord
              (LeftPrepend.prependedLeftLayout L write) callerData))
          (InsertRestagedMachine.rewindConfig
            (RewindWord.gateConfig
              (PhysicalBranch.insertOutput buffer leftRev suffix) 0)).tape := by
      rw [← houtput]
      simpa [InsertRestagedMachine.rewindConfig,
        RewindWord.gateConfig] using Tape.Equiv.symm hgateInput
    exact Tape.Equiv.trans hinputClean hinsertTapeFinal

theorem payload_insert_exact_of_tape_equiv {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol)
    (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input (Frame.protectedWord L callerData)) T) :
    exists endpoint,
      (machine .leftPayload (InsertBlock.optionalBuffer write)).runConfigExact?
          (payloadSteps L write callerData)
          { state :=
              (machine .leftPayload
                (InsertBlock.optionalBuffer write)).start
            tape := T } = some endpoint ∧
      endpoint.state = Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input (LeftPrepend.afterWriteWord L write callerData))
        endpoint.tape := by
  let buffer := InsertBlock.optionalBuffer write
  rcases payload_insert_exact L write callerData with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  have hsourceConfig :
      (locateConfig
        (Locator.fieldsConfig (FieldLocator.startConfig L callerData)) :
        TuringMachine.Configuration MachineCodeSymbol Control) =
        { state := (machine .leftPayload buffer).start
          tape := Tape.input (Frame.protectedWord L callerData) } := by
    rfl
  rw [hsourceConfig] at hclean
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, ?_, Tape.Equiv.trans hcleanTape htape⟩
  · simpa [buffer] using hrun
  · exact hstate.trans hcleanState

theorem count_increment_exact_of_tape_equiv {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol)
    (T : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input (LeftPrepend.afterWriteWord L write callerData)) T) :
    exists endpoint,
      (machine .leftCountDone
          (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).runConfigExact?
          (countIncrementSteps L write callerData)
          { state :=
              (machine .leftCountDone
                (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).start
            tape := T } = some endpoint ∧
      endpoint.state = Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (LeftPrepend.prependedLeftLayout L write) callerData))
        endpoint.tape := by
  let buffer := InsertBlock.singletonBuffer MachineCodeSymbol.tick
  rcases count_increment_exact L write callerData with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  have hsourceConfig :
      (locateConfig
        (Locator.config (.fields .header) []
          (LeftPrepend.afterWriteWord L write callerData)) :
        TuringMachine.Configuration MachineCodeSymbol Control) =
        { state := (machine .leftCountDone buffer).start
          tape := Tape.input
            (LeftPrepend.afterWriteWord L write callerData) } := by
    rfl
  rw [hsourceConfig] at hclean
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, ?_, Tape.Equiv.trans hcleanTape htape⟩
  · simpa [buffer] using hrun
  · exact hstate.trans hcleanState

end PositionedLeft
end Edits
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
