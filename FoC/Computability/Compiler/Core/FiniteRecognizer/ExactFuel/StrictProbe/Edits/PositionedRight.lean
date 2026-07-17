import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.PositionedRightLocator
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Positioned right-field edits

Insertion and count-update phases at the serialized right-side frame
boundaries.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Edits
namespace PositionedRight

open SerializedFieldComposer

inductive Control where
  | locate (inner : Edits.PositionedRightLocator.Control)
  | handoffReturn
  | insert (inner : InsertRestagedMachine.Control)
deriving DecidableEq

namespace Control

def elems : List Control :=
  (Edits.PositionedRightLocator.Control.finite.elems.map Control.locate) ++
    [Control.handoffReturn] ++
    (InsertRestagedMachine.Control.finite.elems.map Control.insert)

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate inner =>
        have h := Edits.PositionedRightLocator.Control.finite.complete inner
        simp [elems, h]
    | handoffReturn => simp [elems]
    | insert inner =>
        have h := InsertRestagedMachine.Control.finite.complete inner
        simp [elems, h]

end Control

def transition (boundary : Edits.PositionedRightLocator.Boundary)
    (buffer : InsertBlock.Buffer) :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate .gate, read =>
      some (read, Direction.right, .handoffReturn)
  | .locate inner, read =>
      match Edits.PositionedRightLocator.transition boundary inner read with
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

def machine (boundary : Edits.PositionedRightLocator.Boundary)
    (buffer : InsertBlock.Buffer) :
    TuringMachine MachineCodeSymbol Control where
  start := .locate (.head ⟨0, by decide⟩)
  halt := .insert (.rewind .gate)
  transition := transition boundary buffer
  statesFinite := Control.finite

def locateConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      Edits.PositionedRightLocator.Control) :
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
    (boundary : Edits.PositionedRightLocator.Boundary)
    (buffer : InsertBlock.Buffer)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      Edits.PositionedRightLocator.Control)
    (hstep : (Edits.PositionedRightLocator.machine boundary).stepConfig c =
      some d) :
    (machine boundary buffer).stepConfig (locateConfig c) =
      some (locateConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Edits.PositionedRightLocator.machine] at hstep
      cases htransition : Edits.PositionedRightLocator.transition boundary
          inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | gate =>
              cases boundary <;>
                simp [Edits.PositionedRightLocator.transition] at htransition
          | head count | rightCount | returnToCountDone =>
              simp [machine, transition, locateConfig, htransition]

theorem locate_run_of_some
    (boundary : Edits.PositionedRightLocator.Boundary)
    (buffer : InsertBlock.Buffer) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        Edits.PositionedRightLocator.Control),
      (Edits.PositionedRightLocator.machine boundary).runConfigExact?
          steps source = some target ->
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
      cases hstep :
          (Edits.PositionedRightLocator.machine boundary).stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [locate_step_of_some boundary buffer source next hstep]
          simp only
          exact ih next target hrun

theorem handoff_run_exact
    (boundary : Edits.PositionedRightLocator.Boundary)
    (buffer : InsertBlock.Buffer) (T : Tape MachineCodeSymbol) :
    (machine boundary buffer).runConfigExact? 2
        { state := Control.locate .gate, tape := T } =
      some
        (insertConfig
          { state := InsertRestagedMachine.Control.edit (.carry buffer)
            tape := roundTripTape T }) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, insertConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    roundTripTape, Tape.write_read_eq_self]

theorem insert_run_of_some
    (boundary : Edits.PositionedRightLocator.Boundary)
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
  (Edits.PositionedRightLocator.rightPayloadSteps
      L.head L.right.length + 2) +
    InsertRestagedMachine.runSteps (InsertBlock.optionalBuffer write)
      (RightPrepend.rightPayloadPrefix L).reverse
      (RightPrepend.rightPayloadSuffix L callerData)

/-- From the canonical head cursor, physically insert the written symbol at
the front of the right payload and rewind to the header. -/
theorem payload_insert_exact {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) :
    exists endpoint,
      (machine .rightPayload (InsertBlock.optionalBuffer write)).runConfigExact?
          (payloadSteps L write callerData)
          (locateConfig
            (Edits.PositionedRightLocator.sourceConfig
              (headPrefix L).reverse L.head L.right.length
              (RightPrepend.rightPayloadSuffix L callerData))) =
        some endpoint ∧
      endpoint.state = Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input (RightPrepend.afterWriteWord L write callerData))
        endpoint.tape := by
  let buffer := InsertBlock.optionalBuffer write
  let leftRev : Word MachineCodeSymbol :=
    (RightPrepend.rightPayloadPrefix L).reverse
  let suffix : Word MachineCodeSymbol :=
    RightPrepend.rightPayloadSuffix L callerData
  have hlocate := Edits.PositionedRightLocator.canonical_rightPayload_exact
    L callerData
  have hlocateOuter := locate_run_of_some .rightPayload buffer _ _ _ hlocate
  have hhandoff := handoff_run_exact .rightPayload buffer
    (Edits.PositionedRightLocator.config .gate leftRev suffix).tape
  have hinsertTape :
      Tape.Equiv
        (InsertRestagedMachine.editConfig
          (InsertBlock.config buffer leftRev suffix)).tape
        (roundTripTape
          (Edits.PositionedRightLocator.config .gate leftRev suffix).tape) := by
    exact Tape.Equiv.symm
      (roundTripTape_equiv
        (Edits.PositionedRightLocator.config .gate leftRev suffix).tape)
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (InsertRestagedMachine.run_exact buffer leftRev suffix
          (InsertBlock.optionalBuffer_nonempty write)) hinsertTape with
    ⟨insertEndpoint, hinsert, hinsertState, hinsertTapeFinal⟩
  have hinsertOuter := insert_run_of_some .rightPayload buffer hinsert
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
          RightPrepend.afterWriteWord L write callerData := by
      simp [buffer, leftRev, suffix, PhysicalBranch.insertOutput,
        InsertBlock.optionalBuffer, RightPrepend.afterWriteWord]
    have hinputClean :
        Tape.Equiv
          (Tape.input (RightPrepend.afterWriteWord L write callerData))
          (InsertRestagedMachine.rewindConfig
            (RewindWord.gateConfig
              (PhysicalBranch.insertOutput buffer leftRev suffix) 0)).tape := by
      rw [← houtput]
      simpa [InsertRestagedMachine.rewindConfig,
        RewindWord.gateConfig] using
        Tape.Equiv.symm hgateInput
    exact Tape.Equiv.trans hinputClean hinsertTapeFinal

def countIncrementSteps {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) : Nat :=
  (Edits.PositionedRightLocator.rightCountTicksSteps
      L.head L.right.length + 2) +
    InsertRestagedMachine.runSteps
      (InsertBlock.singletonBuffer MachineCodeSymbol.tick)
      (RightPrepend.rightCountTicksPrefix L).reverse
      (RightPrepend.afterCountDoneSuffix L write callerData)

/-- From the head cursor on the stale-count intermediate word, insert the new
unary count tick and rewind to the fully canonical right-prepended layout. -/
theorem count_increment_exact {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) :
    exists endpoint,
      (machine .rightCountTicks
          (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).runConfigExact?
          (countIncrementSteps L write callerData)
          (locateConfig
            (Edits.PositionedRightLocator.sourceConfig
              (headPrefix L).reverse L.head L.right.length
              (List.append (optionalCellWord write)
                (RightPrepend.rightPayloadSuffix L callerData)))) =
        some endpoint ∧
      endpoint.state = Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (RightPrepend.prependedRightLayout L write) callerData))
        endpoint.tape := by
  let buffer := InsertBlock.singletonBuffer MachineCodeSymbol.tick
  let leftRev : Word MachineCodeSymbol :=
    (RightPrepend.rightCountTicksPrefix L).reverse
  let suffix : Word MachineCodeSymbol :=
    RightPrepend.afterCountDoneSuffix L write callerData
  let cleanCursor := SerializedShift.cursorTape leftRev suffix
  let locatorTape := Edits.PositionedRightLocator.roundTripTape cleanCursor
  have hlocate :=
    Edits.PositionedRightLocator.canonical_rightCountTicks_exact
      L write callerData
  have hlocateOuter := locate_run_of_some
    .rightCountTicks buffer _ _ _ hlocate
  have hhandoff := handoff_run_exact .rightCountTicks buffer locatorTape
  have hlocatorEquiv : Tape.Equiv locatorTape cleanCursor := by
    exact Edits.PositionedRightLocator.roundTripTape_equiv cleanCursor
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
  have hinsertOuter := insert_run_of_some
    .rightCountTicks buffer hinsert
  have hpref := TuringMachine.runConfigExact?_trans
    hlocateOuter hhandoff
  have hrun := TuringMachine.runConfigExact?_trans
    hpref hinsertOuter
  refine ⟨insertConfig insertEndpoint, ?_, ?_, ?_⟩
  · simpa [countIncrementSteps, buffer, leftRev, suffix,
      cleanCursor, locatorTape, Nat.add_assoc] using hrun
  · simpa [insertConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      InsertRestagedMachine.rewindConfig,
      RewindWord.gateConfig] using hinsertState
  · have hgateInput := RewindWord.gateTape_equiv_input
      (PhysicalBranch.insertOutput buffer leftRev suffix) 0
    have houtput :
        PhysicalBranch.insertOutput buffer leftRev suffix =
          Frame.protectedWord
            (RightPrepend.prependedRightLayout L write) callerData := by
      simpa [buffer, leftRev, suffix] using
        PhysicalBranch.prependRight_output_eq_protectedWord
          L write callerData
    have hinputClean :
        Tape.Equiv
          (Tape.input
            (Frame.protectedWord
              (RightPrepend.prependedRightLayout L write) callerData))
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
      (Edits.PositionedRightLocator.sourceConfig
        (headPrefix L).reverse L.head L.right.length
        (RightPrepend.rightPayloadSuffix L callerData)).tape T) :
    exists endpoint,
      (machine .rightPayload (InsertBlock.optionalBuffer write)).runConfigExact?
          (payloadSteps L write callerData)
          { state :=
              (machine .rightPayload
                (InsertBlock.optionalBuffer write)).start
            tape := T } = some endpoint ∧
      endpoint.state = Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input (RightPrepend.afterWriteWord L write callerData))
        endpoint.tape := by
  let buffer := InsertBlock.optionalBuffer write
  rcases payload_insert_exact L write callerData with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  have hsourceConfig :
      (locateConfig
        (Edits.PositionedRightLocator.sourceConfig
          (headPrefix L).reverse L.head L.right.length
          (RightPrepend.rightPayloadSuffix L callerData)) :
        TuringMachine.Configuration MachineCodeSymbol Control) =
        { state := (machine .rightPayload buffer).start
          tape :=
            (Edits.PositionedRightLocator.sourceConfig
              (headPrefix L).reverse L.head L.right.length
              (RightPrepend.rightPayloadSuffix L callerData)).tape } := by
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
      (Edits.PositionedRightLocator.sourceConfig
        (headPrefix L).reverse L.head L.right.length
        (List.append (optionalCellWord write)
          (RightPrepend.rightPayloadSuffix L callerData))).tape T) :
    exists endpoint,
      (machine .rightCountTicks
          (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).runConfigExact?
          (countIncrementSteps L write callerData)
          { state :=
              (machine .rightCountTicks
                (InsertBlock.singletonBuffer MachineCodeSymbol.tick)).start
            tape := T } = some endpoint ∧
      endpoint.state = Control.insert (.rewind .gate) ∧
      Tape.Equiv
        (Tape.input
          (Frame.protectedWord
            (RightPrepend.prependedRightLayout L write) callerData))
        endpoint.tape := by
  let buffer := InsertBlock.singletonBuffer MachineCodeSymbol.tick
  rcases count_increment_exact L write callerData with
    ⟨cleanEndpoint, hclean, hcleanState, hcleanTape⟩
  have hsourceConfig :
      (locateConfig
        (Edits.PositionedRightLocator.sourceConfig
          (headPrefix L).reverse L.head L.right.length
          (List.append (optionalCellWord write)
            (RightPrepend.rightPayloadSuffix L callerData))) :
        TuringMachine.Configuration MachineCodeSymbol Control) =
        { state := (machine .rightCountTicks buffer).start
          tape :=
            (Edits.PositionedRightLocator.sourceConfig
              (headPrefix L).reverse L.head L.right.length
              (List.append (optionalCellWord write)
                (RightPrepend.rightPayloadSuffix L callerData))).tape } := by
    rfl
  rw [hsourceConfig] at hclean
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, ?_, Tape.Equiv.trans hcleanTape htape⟩
  · simpa [buffer] using hrun
  · exact hstate.trans hcleanState

end PositionedRight
end Edits
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
