import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.Rollover
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.CandidateReset

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Scheduler.Rollover

inductive Field where
  | fuel
  | outer
  | inner
deriving DecidableEq

namespace Field

def finite : Foundation.FiniteType Field where
  elems := [.fuel, .outer, .inner]
  complete := by
    intro field
    cases field <;> simp

def target : Field -> Scheduler.Rollover.Locator.Target
  | .fuel => .candidateFuel
  | .outer => .candidateOuter
  | .inner => .candidateInner

end Field

inductive Control where
  | locate (field : Field)
      (inner : Scheduler.Rollover.Locator.Control)
  | delete (field : Field) (inner : DeleteRestagedMachine.Control)
  | bounceRight (field : Field)
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  List.append
    (Field.finite.elems.flatMap fun field =>
      Scheduler.Rollover.Locator.Control.finite.elems.map
        (Control.locate field))
    (List.append
      (Field.finite.elems.flatMap fun field =>
        DeleteRestagedMachine.Control.finite.elems.map
          (Control.delete field))
      (List.append (Field.finite.elems.map Control.bounceRight) [.halt]))

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate field inner =>
        simp [elems, Field.finite.complete field,
          Scheduler.Rollover.Locator.Control.finite.complete inner]
    | delete field inner =>
        simp [elems, Field.finite.complete field,
          DeleteRestagedMachine.Control.finite.complete inner]
    | bounceRight field =>
        simp [elems]
        exact Field.finite.complete field
    | halt =>
        simp [elems]

end Control

def mapAction (wrap : inner -> Control)
    (action : Option MachineCodeSymbol × Direction × inner) :
    Option MachineCodeSymbol × Direction × Control :=
  (action.1, action.2.1, wrap action.2.2)

def transition : Control -> Option MachineCodeSymbol ->
    Option (Option MachineCodeSymbol × Direction × Control)
  | .locate field .halt, some .tick =>
      match DeleteRestagedMachine.transition none
          (.edit (.erase (DeleteBlock.optionalGap none)))
          (some MachineCodeSymbol.tick) with
      | none => none
      | some action => some (mapAction (Control.delete field) action)
  | .locate .fuel .halt, some .done =>
      some (some .done, Direction.right, .locate .outer .halt)
  | .locate .outer .halt, some .done =>
      some (some .done, Direction.right, .locate .inner .halt)
  | .locate .inner .halt, some .done =>
      some (some .done, Direction.right, .halt)
  | .locate field inner, read =>
      match Scheduler.Rollover.Locator.transition
          field.target inner read with
      | none => none
      | some action => some (mapAction (Control.locate field) action)
  | .delete field (.rewind .gate), read =>
      some (read, Direction.left, .bounceRight field)
  | .delete field inner, read =>
      match DeleteRestagedMachine.transition none inner read with
      | none => none
      | some action => some (mapAction (Control.delete field) action)
  | .bounceRight field, read =>
      some (read, Direction.right, .locate field .header)
  | .halt, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .locate .fuel .header
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def locateConfig (field : Field)
    (c : TuringMachine.Configuration MachineCodeSymbol
      Scheduler.Rollover.Locator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (Control.locate field) c

def deleteConfig (field : Field)
    (c : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (Control.delete field) c

theorem locate_step_of_some (field : Field)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      Scheduler.Rollover.Locator.Control)
    (hstep : (Scheduler.Rollover.Locator.machine
      field.target).stepConfig c = some d) :
    machine.stepConfig (locateConfig field c) =
      some (locateConfig field d) := by
  cases c with
  | mk state tape =>
      cases d with
      | mk nextState nextTape =>
          unfold TuringMachine.stepConfig at hstep ⊢
          dsimp [Scheduler.Rollover.Locator.machine] at hstep
          cases haction : Scheduler.Rollover.Locator.transition
              field.target state (Tape.read tape) with
          | none =>
              rw [haction] at hstep
              contradiction
          | some action =>
              rcases action with ⟨write, direction, targetState⟩
              rw [haction] at hstep
              simp only at hstep
              cases hstep
              cases state <;>
                simp_all [machine, transition, locateConfig, mapAction,
                  TuringMachine.PhaseEmbedding.liftConfig,
                  Scheduler.Rollover.Locator.transition]

theorem delete_step_of_some (field : Field)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control)
    (hstep : (DeleteRestagedMachine.machine none).stepConfig c = some d) :
    machine.stepConfig (deleteConfig field c) =
      some (deleteConfig field d) := by
  cases c with
  | mk state tape =>
      cases d with
      | mk nextState nextTape =>
          unfold TuringMachine.stepConfig at hstep ⊢
          dsimp [DeleteRestagedMachine.machine] at hstep
          cases haction : DeleteRestagedMachine.transition none state
              (Tape.read tape) with
          | none =>
              rw [haction] at hstep
              contradiction
          | some action =>
              rcases action with ⟨write, direction, targetState⟩
              rw [haction] at hstep
              simp only at hstep
              cases hstep
              cases state with
              | edit inner =>
                  cases inner <;>
                    simp_all [machine, transition, deleteConfig, mapAction,
                      TuringMachine.PhaseEmbedding.liftConfig]
              | rewind inner =>
                  cases inner <;>
                    simp_all [machine, transition, deleteConfig, mapAction,
                      TuringMachine.PhaseEmbedding.liftConfig,
                      DeleteRestagedMachine.transition,
                      DeleteEndpointRewind.transition]

theorem locate_run_of_eq_some (field : Field) {steps : Nat}
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        Scheduler.Rollover.Locator.Control}
    (hrun : (Scheduler.Rollover.Locator.machine
      field.target).runConfigExact? steps source =
      some target) :
    machine.runConfigExact? steps (locateConfig field source) =
      some (locateConfig field target) := by
  exact TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    (Control.locate field) (locate_step_of_some field) hrun

theorem delete_run_of_eq_some (field : Field) {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control}
    (hrun : (DeleteRestagedMachine.machine none).runConfigExact? steps source =
      some target) :
    machine.runConfigExact? steps (deleteConfig field source) =
      some (deleteConfig field target) := by
  exact TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    (Control.delete field) (delete_step_of_some field) hrun

def deleteTickSteps (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  DeleteBlock.runOneSteps suffix +
    DeleteEndpointRewind.runSteps none
      (List.append suffix.reverse leftRev)

theorem delete_tick_exact (leftRev suffix : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact?
        (deleteTickSteps leftRev suffix)
        (DeleteRestagedMachine.editConfig
          (DeleteBlock.oneSourceConfig MachineCodeSymbol.tick
            leftRev suffix)) =
      some (DeleteRestagedMachine.rewindConfig
        (DeleteEndpointRewind.gateConfig
          (PhysicalBranch.deleteOutput leftRev suffix) none)) := by
  unfold deleteTickSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [DeleteRestagedMachine.edit_run_of_eq_some none _ _ _
    (DeleteBlock.run_one_exact MachineCodeSymbol.tick leftRev suffix)]
  simp only
  rw [DeleteRestagedMachine.rewind_run_exact]
  simp [PhysicalBranch.deleteOutput, List.reverse_append]

def gateLocateConfig (field : Field) (word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .locate field .header
    tape := (DeleteEndpointRewind.gateConfig word none).tape }

theorem gateLocate_tape_equiv_input (field : Field)
    (word : Word MachineCodeSymbol) :
    Tape.Equiv (gateLocateConfig field word).tape (Tape.input word) := by
  exact DeleteEndpointRewind.gateTape_equiv_input word none

theorem bounce_exact (field : Field) (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (deleteConfig field
          (DeleteRestagedMachine.rewindConfig
            (DeleteEndpointRewind.gateConfig word none))) =
      some (gateLocateConfig field word) := by
  cases field <;> cases word <;> rfl

def deleteTickTailSteps (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  ((2 * (DeleteBlock.optionalGap none).val + 1) * suffix.length + 1) +
    DeleteEndpointRewind.runSteps none
      (List.append suffix.reverse leftRev)

theorem delete_tick_tail_exact (leftRev suffix : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact?
        (deleteTickTailSteps leftRev suffix)
        (DeleteRestagedMachine.editConfig
          (DeleteBlock.pullConfig (DeleteBlock.optionalGap none)
            leftRev suffix)) =
      some (DeleteRestagedMachine.rewindConfig
        (DeleteEndpointRewind.gateConfig
          (PhysicalBranch.deleteOutput leftRev suffix) none)) := by
  unfold deleteTickTailSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [DeleteRestagedMachine.edit_run_of_eq_some none _ _ _
    (DeleteBlock.pull_run_exact none leftRev suffix)]
  simp only
  rw [DeleteRestagedMachine.rewind_run_exact]
  simp [PhysicalBranch.deleteOutput, List.reverse_append]

theorem enter_delete_tick_step (field : Field)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (locateConfig field
          (Scheduler.Rollover.Locator.config .halt leftRev
            (MachineCodeSymbol.tick :: suffix))) =
      some (deleteConfig field
        (DeleteRestagedMachine.editConfig
          (DeleteBlock.pullConfig (DeleteBlock.optionalGap none)
            leftRev suffix))) := by
  cases field <;> cases leftRev <;> cases suffix <;> rfl

def deleteLoopSteps (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  1 + deleteTickTailSteps leftRev suffix + 2

theorem delete_loop_exact (field : Field)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (deleteLoopSteps leftRev suffix)
        (locateConfig field
          (Scheduler.Rollover.Locator.config .halt leftRev
            (MachineCodeSymbol.tick :: suffix))) =
      some (gateLocateConfig field
        (PhysicalBranch.deleteOutput leftRev suffix)) := by
  unfold deleteLoopSteps
  rw [show 1 + deleteTickTailSteps leftRev suffix + 2 =
      1 + (deleteTickTailSteps leftRev suffix + 2) by lia]
  rw [InitialMaterializer.ExactRun.append machine 1
    (deleteTickTailSteps leftRev suffix + 2)]
  rw [TuringMachine.runConfigExact?, enter_delete_tick_step]
  change machine.runConfigExact?
    (deleteTickTailSteps leftRev suffix + 2)
    (deleteConfig field
      (DeleteRestagedMachine.editConfig
        (DeleteBlock.pullConfig (DeleteBlock.optionalGap none)
          leftRev suffix))) = _
  rw [InitialMaterializer.ExactRun.append machine
    (deleteTickTailSteps leftRev suffix) 2]
  rw [delete_run_of_eq_some field
    (delete_tick_tail_exact leftRev suffix)]
  simp only
  rw [bounce_exact]

theorem fuel_done_step (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (locateConfig .fuel
          (Scheduler.Rollover.Locator.config .halt leftRev
            (MachineCodeSymbol.done :: suffix))) =
      some (locateConfig .outer
        (Scheduler.Rollover.Locator.config .halt
          (MachineCodeSymbol.done :: leftRev) suffix)) := by
  cases leftRev <;> cases suffix <;> rfl

theorem outer_done_step (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (locateConfig .outer
          (Scheduler.Rollover.Locator.config .halt leftRev
            (MachineCodeSymbol.done :: suffix))) =
      some (locateConfig .inner
        (Scheduler.Rollover.Locator.config .halt
          (MachineCodeSymbol.done :: leftRev) suffix)) := by
  cases leftRev <;> cases suffix <;> rfl

def pendingWord (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round
    0 fuelRemaining 0 outerRemaining 0 innerRemaining
    candidateFuel candidateOuter candidateInner input

def mainPrefixRev (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining : Nat) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.candidatePrefixRev geometry round
    0 fuelRemaining 0 outerRemaining 0 innerRemaining

def candidateSuffix (candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend candidateFuel
    (MachineDescription.encodeNatAppend candidateOuter
      (MachineDescription.encodeNatAppend candidateInner input))

theorem nestedStageCode_eq_candidate_tail
    (candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    GeneratedCode.nestedStageCode input candidateInner candidateOuter =
      MachineDescription.encodeNatAppend candidateOuter
        (MachineDescription.encodeNatAppend candidateInner input) := by
  rfl

theorem pendingWord_fuel_decomp
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    pendingWord geometry round fuelRemaining outerRemaining innerRemaining
        candidateFuel candidateOuter candidateInner input =
      List.append
        (mainPrefixRev geometry round fuelRemaining outerRemaining
          innerRemaining).reverse
        (candidateSuffix candidateFuel candidateOuter candidateInner input) := by
  cases geometry with
  | unbounded =>
      simp [pendingWord, mainPrefixRev, candidateSuffix,
        Scheduler.Rollover.word,
        Scheduler.Rollover.Locator.candidatePrefixRev,
        Scheduler.Rollover.Locator.splitPrefixRev,
        Scheduler.Rollover.Locator.natPrefixRev,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.SplitLayout.encodeSplitAppend,
        MachineDescription.encodeNatAppend,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        nestedStageCode_eq_candidate_tail,
        List.reverse_append, List.append_assoc]
  | bounded budget =>
      simp [pendingWord, mainPrefixRev, candidateSuffix,
        Scheduler.Rollover.word,
        Scheduler.Rollover.Locator.candidatePrefixRev,
        Scheduler.Rollover.Locator.splitPrefixRev,
        Scheduler.Rollover.Locator.natPrefixRev,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.SplitLayout.encodeSplitAppend,
        MachineDescription.encodeNatAppend,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        nestedStageCode_eq_candidate_tail,
        List.reverse_append, List.append_assoc]

theorem pendingWord_outer_decomp
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    pendingWord geometry round fuelRemaining outerRemaining innerRemaining
        0 candidateOuter candidateInner input =
      List.append
        (Scheduler.Rollover.Locator.natPrefixRev 0
          (mainPrefixRev geometry round fuelRemaining outerRemaining
            innerRemaining)).reverse
        (MachineDescription.encodeNatAppend candidateOuter
          (MachineDescription.encodeNatAppend candidateInner input)) := by
  rw [pendingWord_fuel_decomp]
  simp [candidateSuffix,
    Scheduler.Rollover.Locator.natPrefixRev,
    Scheduler.Advance.ExhaustedSplitReset.ticks,
    MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
    List.reverse_append, List.append_assoc]

theorem pendingWord_inner_decomp
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    pendingWord geometry round fuelRemaining outerRemaining innerRemaining
        0 0 candidateInner input =
      List.append
        (Scheduler.Rollover.Locator.natPrefixRev 0
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (mainPrefixRev geometry round fuelRemaining outerRemaining
              innerRemaining))).reverse
        (MachineDescription.encodeNatAppend candidateInner input) := by
  rw [pendingWord_outer_decomp]
  simp [Scheduler.Rollover.Locator.natPrefixRev,
    Scheduler.Advance.ExhaustedSplitReset.ticks,
    MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
    List.reverse_append, List.append_assoc]

def withTape
    (c : TuringMachine.Configuration MachineCodeSymbol Control)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := c.state, tape := tape }

theorem computes_exact_from_equiv {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol Control}
    {tape : Tape MachineCodeSymbol}
    (hrun : machine.runConfigExact? steps source = some target)
    (htape : Tape.Equiv source.tape tape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine (withTape source tape)
        (withTape target targetTape) ∧
      Tape.Equiv target.tape targetTape := by
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun htape with
    ⟨⟨targetState, targetTape⟩, hrun', hstate, htape'⟩
  simp only at hstate
  subst targetState
  exact ⟨targetTape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun'),
    htape'⟩

def fuelConfig (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  locateConfig .fuel
    (Scheduler.Rollover.Locator.config .halt
      (mainPrefixRev geometry round fuelRemaining outerRemaining
        innerRemaining)
      (candidateSuffix candidateFuel candidateOuter candidateInner input))

def outerConfig (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  locateConfig .outer
    (Scheduler.Rollover.Locator.config .halt
      (Scheduler.Rollover.Locator.natPrefixRev 0
        (mainPrefixRev geometry round fuelRemaining outerRemaining
          innerRemaining))
      (MachineDescription.encodeNatAppend candidateOuter
        (MachineDescription.encodeNatAppend candidateInner input)))

def innerConfig (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  locateConfig .inner
    (Scheduler.Rollover.Locator.config .halt
      (Scheduler.Rollover.Locator.natPrefixRev 0
        (Scheduler.Rollover.Locator.natPrefixRev 0
          (mainPrefixRev geometry round fuelRemaining outerRemaining
            innerRemaining)))
      (MachineDescription.encodeNatAppend candidateInner input))

def finalConfig (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .halt
    tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
      (MachineCodeSymbol.done ::
        Scheduler.Rollover.Locator.natPrefixRev 0
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (mainPrefixRev geometry round fuelRemaining outerRemaining
              innerRemaining)))
      input }

theorem inner_done_step (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (locateConfig .inner
          (Scheduler.Rollover.Locator.config .halt leftRev
            (MachineCodeSymbol.done :: suffix))) =
      some
        { state := .halt
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  cases leftRev <;> cases suffix <;> rfl

theorem fuel_zero_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact? 1
        (fuelConfig geometry round fuelRemaining outerRemaining
          innerRemaining 0 candidateOuter candidateInner input) =
      some (outerConfig geometry round fuelRemaining outerRemaining
        innerRemaining candidateOuter candidateInner input) := by
  change machine.runConfigExact? 1
    (locateConfig .fuel
      (Scheduler.Rollover.Locator.config .halt
        (mainPrefixRev geometry round fuelRemaining outerRemaining
          innerRemaining)
        (MachineCodeSymbol.done ::
          MachineDescription.encodeNatAppend candidateOuter
            (MachineDescription.encodeNatAppend candidateInner input)))) =
    some (locateConfig .outer
      (Scheduler.Rollover.Locator.config .halt
        (MachineCodeSymbol.done ::
          mainPrefixRev geometry round fuelRemaining outerRemaining
            innerRemaining)
        (MachineDescription.encodeNatAppend candidateOuter
          (MachineDescription.encodeNatAppend candidateInner input))))
  unfold TuringMachine.runConfigExact?
  rw [fuel_done_step]
  rfl

theorem outer_zero_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact? 1
        (outerConfig geometry round fuelRemaining outerRemaining
          innerRemaining 0 candidateInner input) =
      some (innerConfig geometry round fuelRemaining outerRemaining
        innerRemaining candidateInner input) := by
  change machine.runConfigExact? 1
    (locateConfig .outer
      (Scheduler.Rollover.Locator.config .halt
        (MachineCodeSymbol.done ::
          mainPrefixRev geometry round fuelRemaining outerRemaining
            innerRemaining)
        (MachineCodeSymbol.done ::
          MachineDescription.encodeNatAppend candidateInner input))) =
    some (locateConfig .inner
      (Scheduler.Rollover.Locator.config .halt
        (MachineCodeSymbol.done :: MachineCodeSymbol.done ::
          mainPrefixRev geometry round fuelRemaining outerRemaining
            innerRemaining)
        (MachineDescription.encodeNatAppend candidateInner input)))
  unfold TuringMachine.runConfigExact?
  rw [outer_done_step]
  rfl

theorem inner_zero_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact? 1
        (innerConfig geometry round fuelRemaining outerRemaining
          innerRemaining 0 input) =
      some (finalConfig geometry round fuelRemaining outerRemaining
        innerRemaining input) := by
  change machine.runConfigExact? 1
    (locateConfig .inner
      (Scheduler.Rollover.Locator.config .halt
        (MachineCodeSymbol.done :: MachineCodeSymbol.done ::
          mainPrefixRev geometry round fuelRemaining outerRemaining
            innerRemaining)
        (MachineCodeSymbol.done :: input))) =
    some
      { state := .halt
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          (MachineCodeSymbol.done :: MachineCodeSymbol.done ::
            MachineCodeSymbol.done ::
              mainPrefixRev geometry round fuelRemaining outerRemaining
                innerRemaining)
          input }
  unfold TuringMachine.runConfigExact?
  rw [inner_done_step]
  rfl

theorem fuel_delete_succ_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (deleteLoopSteps
          (mainPrefixRev geometry round fuelRemaining outerRemaining
            innerRemaining)
          (candidateSuffix candidateFuel candidateOuter candidateInner input))
        (fuelConfig geometry round fuelRemaining outerRemaining
          innerRemaining (candidateFuel + 1) candidateOuter candidateInner
          input) =
      some (gateLocateConfig .fuel
        (pendingWord geometry round fuelRemaining outerRemaining
          innerRemaining candidateFuel candidateOuter candidateInner input)) := by
  change machine.runConfigExact?
      (deleteLoopSteps
        (mainPrefixRev geometry round fuelRemaining outerRemaining
          innerRemaining)
        (candidateSuffix candidateFuel candidateOuter candidateInner input))
      (locateConfig .fuel
        (Scheduler.Rollover.Locator.config .halt
          (mainPrefixRev geometry round fuelRemaining outerRemaining
            innerRemaining)
          (MachineCodeSymbol.tick ::
            candidateSuffix candidateFuel candidateOuter candidateInner
              input))) = _
  rw [delete_loop_exact]
  rw [pendingWord_fuel_decomp]
  rfl

theorem outer_delete_succ_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (deleteLoopSteps
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (mainPrefixRev geometry round fuelRemaining outerRemaining
              innerRemaining))
          (MachineDescription.encodeNatAppend candidateOuter
            (MachineDescription.encodeNatAppend candidateInner input)))
        (outerConfig geometry round fuelRemaining outerRemaining
          innerRemaining (candidateOuter + 1) candidateInner input) =
      some (gateLocateConfig .outer
        (pendingWord geometry round fuelRemaining outerRemaining
          innerRemaining 0 candidateOuter candidateInner input)) := by
  change machine.runConfigExact?
      (deleteLoopSteps
        (Scheduler.Rollover.Locator.natPrefixRev 0
          (mainPrefixRev geometry round fuelRemaining outerRemaining
            innerRemaining))
        (MachineDescription.encodeNatAppend candidateOuter
          (MachineDescription.encodeNatAppend candidateInner input)))
      (locateConfig .outer
        (Scheduler.Rollover.Locator.config .halt
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (mainPrefixRev geometry round fuelRemaining outerRemaining
              innerRemaining))
          (MachineCodeSymbol.tick ::
            MachineDescription.encodeNatAppend candidateOuter
              (MachineDescription.encodeNatAppend candidateInner input)))) = _
  rw [delete_loop_exact]
  rw [pendingWord_outer_decomp]
  rfl

theorem inner_delete_succ_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (deleteLoopSteps
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (Scheduler.Rollover.Locator.natPrefixRev 0
              (mainPrefixRev geometry round fuelRemaining outerRemaining
                innerRemaining)))
          (MachineDescription.encodeNatAppend candidateInner input))
        (innerConfig geometry round fuelRemaining outerRemaining
          innerRemaining (candidateInner + 1) input) =
      some (gateLocateConfig .inner
        (pendingWord geometry round fuelRemaining outerRemaining
          innerRemaining 0 0 candidateInner input)) := by
  change machine.runConfigExact?
      (deleteLoopSteps
        (Scheduler.Rollover.Locator.natPrefixRev 0
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (mainPrefixRev geometry round fuelRemaining outerRemaining
              innerRemaining)))
        (MachineDescription.encodeNatAppend candidateInner input))
      (locateConfig .inner
        (Scheduler.Rollover.Locator.config .halt
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (Scheduler.Rollover.Locator.natPrefixRev 0
              (mainPrefixRev geometry round fuelRemaining outerRemaining
                innerRemaining)))
          (MachineCodeSymbol.tick ::
            MachineDescription.encodeNatAppend candidateInner input))) = _
  rw [delete_loop_exact]
  rw [pendingWord_inner_decomp]
  rfl

theorem locate_fuel_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (Scheduler.Rollover.Locator.toCandidateMarkerSteps geometry
          round 0 fuelRemaining 0 outerRemaining 0 innerRemaining + 1)
        (locateConfig .fuel
          (Scheduler.Rollover.Locator.config .header []
            (pendingWord geometry round fuelRemaining outerRemaining
              innerRemaining candidateFuel candidateOuter candidateInner
              input))) =
      some (fuelConfig geometry round fuelRemaining outerRemaining
        innerRemaining candidateFuel candidateOuter candidateInner input) := by
  simpa [pendingWord, fuelConfig, mainPrefixRev, candidateSuffix,
    Scheduler.Rollover.word, nestedStageCode_eq_candidate_tail]
    using locate_run_of_eq_some .fuel
      (Scheduler.Rollover.Locator.locate_candidateFuel_exact
        geometry round 0 fuelRemaining 0 outerRemaining 0 innerRemaining
        (candidateSuffix candidateFuel candidateOuter candidateInner input))

theorem locate_outer_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (Scheduler.Rollover.Locator.locateCandidateOuterSteps geometry
          round 0 fuelRemaining 0 outerRemaining 0 innerRemaining 0)
        (locateConfig .outer
          (Scheduler.Rollover.Locator.config .header []
            (pendingWord geometry round fuelRemaining outerRemaining
              innerRemaining 0 candidateOuter candidateInner input))) =
      some (outerConfig geometry round fuelRemaining outerRemaining
        innerRemaining candidateOuter candidateInner input) := by
  simpa [pendingWord, outerConfig, mainPrefixRev,
    Scheduler.Rollover.word, nestedStageCode_eq_candidate_tail]
    using locate_run_of_eq_some .outer
      (Scheduler.Rollover.Locator.locate_candidateOuter_exact
        geometry round 0 fuelRemaining 0 outerRemaining 0 innerRemaining 0
        (MachineDescription.encodeNatAppend candidateOuter
          (MachineDescription.encodeNatAppend candidateInner input)))

theorem locate_inner_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (Scheduler.Rollover.Locator.locateCandidateInnerSteps geometry
          round 0 fuelRemaining 0 outerRemaining 0 innerRemaining 0 0)
        (locateConfig .inner
          (Scheduler.Rollover.Locator.config .header []
            (pendingWord geometry round fuelRemaining outerRemaining
              innerRemaining 0 0 candidateInner input))) =
      some (innerConfig geometry round fuelRemaining outerRemaining
        innerRemaining candidateInner input) := by
  simpa [pendingWord, innerConfig, mainPrefixRev,
    Scheduler.Rollover.word, nestedStageCode_eq_candidate_tail]
    using locate_run_of_eq_some .inner
      (Scheduler.Rollover.Locator.locate_candidateInner_exact
        geometry round 0 fuelRemaining 0 outerRemaining 0 innerRemaining 0 0
        (MachineDescription.encodeNatAppend candidateInner input))

theorem reset_inner
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining candidateInner : Nat)
    (input : Word MachineCodeSymbol) (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (innerConfig geometry round fuelRemaining outerRemaining
        innerRemaining candidateInner input).tape tape) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (withTape
          (innerConfig geometry round fuelRemaining outerRemaining
            innerRemaining candidateInner input) tape)
        (withTape
          (finalConfig geometry round fuelRemaining outerRemaining
            innerRemaining input) finalTape) ∧
      Tape.Equiv
        (finalConfig geometry round fuelRemaining outerRemaining
          innerRemaining input).tape finalTape := by
  induction candidateInner generalizing tape with
  | zero =>
      exact computes_exact_from_equiv
        (inner_zero_exact geometry round fuelRemaining outerRemaining
          innerRemaining input) htape
  | succ candidateInner ih =>
      let nextWord := pendingWord geometry round fuelRemaining outerRemaining
        innerRemaining 0 0 candidateInner input
      rcases computes_exact_from_equiv
          (inner_delete_succ_exact geometry round fuelRemaining outerRemaining
            innerRemaining candidateInner input) htape with
        ⟨gateTape, hdelete, hgate⟩
      have hinputGate : Tape.Equiv (Tape.input nextWord) gateTape := by
        exact Tape.Equiv.trans
          (Tape.Equiv.symm
            (gateLocate_tape_equiv_input .inner nextWord)) hgate
      rcases computes_exact_from_equiv
          (locate_inner_exact geometry round fuelRemaining outerRemaining
            innerRemaining candidateInner input) hinputGate with
        ⟨innerTape, hlocate, hinner⟩
      rcases ih innerTape hinner with
        ⟨finalTape, htail, hfinal⟩
      exact ⟨finalTape,
        TuringMachine.computes_trans hdelete
          (TuringMachine.computes_trans hlocate htail),
        hfinal⟩

theorem reset_outer
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (outerConfig geometry round fuelRemaining outerRemaining
        innerRemaining candidateOuter candidateInner input).tape tape) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (withTape
          (outerConfig geometry round fuelRemaining outerRemaining
            innerRemaining candidateOuter candidateInner input) tape)
        (withTape
          (finalConfig geometry round fuelRemaining outerRemaining
            innerRemaining input) finalTape) ∧
      Tape.Equiv
        (finalConfig geometry round fuelRemaining outerRemaining
          innerRemaining input).tape finalTape := by
  induction candidateOuter generalizing tape with
  | zero =>
      rcases computes_exact_from_equiv
          (outer_zero_exact geometry round fuelRemaining outerRemaining
            innerRemaining candidateInner input) htape with
        ⟨innerTape, hdone, hinner⟩
      rcases reset_inner geometry round fuelRemaining outerRemaining
          innerRemaining candidateInner input innerTape hinner with
        ⟨finalTape, htail, hfinal⟩
      exact ⟨finalTape, TuringMachine.computes_trans hdone htail, hfinal⟩
  | succ candidateOuter ih =>
      let nextWord := pendingWord geometry round fuelRemaining outerRemaining
        innerRemaining 0 candidateOuter candidateInner input
      rcases computes_exact_from_equiv
          (outer_delete_succ_exact geometry round fuelRemaining outerRemaining
            innerRemaining candidateOuter candidateInner input) htape with
        ⟨gateTape, hdelete, hgate⟩
      have hinputGate : Tape.Equiv (Tape.input nextWord) gateTape := by
        exact Tape.Equiv.trans
          (Tape.Equiv.symm
            (gateLocate_tape_equiv_input .outer nextWord)) hgate
      rcases computes_exact_from_equiv
          (locate_outer_exact geometry round fuelRemaining outerRemaining
            innerRemaining candidateOuter candidateInner input) hinputGate with
        ⟨outerTape, hlocate, houter⟩
      rcases ih outerTape houter with
        ⟨finalTape, htail, hfinal⟩
      exact ⟨finalTape,
        TuringMachine.computes_trans hdelete
          (TuringMachine.computes_trans hlocate htail),
        hfinal⟩

theorem reset_fuel
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (fuelConfig geometry round fuelRemaining outerRemaining
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      tape) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (withTape
          (fuelConfig geometry round fuelRemaining outerRemaining
            innerRemaining candidateFuel candidateOuter candidateInner input)
          tape)
        (withTape
          (finalConfig geometry round fuelRemaining outerRemaining
            innerRemaining input) finalTape) ∧
      Tape.Equiv
        (finalConfig geometry round fuelRemaining outerRemaining
          innerRemaining input).tape finalTape := by
  induction candidateFuel generalizing tape with
  | zero =>
      rcases computes_exact_from_equiv
          (fuel_zero_exact geometry round fuelRemaining outerRemaining
            innerRemaining candidateOuter candidateInner input) htape with
        ⟨outerTape, hdone, houter⟩
      rcases reset_outer geometry round fuelRemaining outerRemaining
          innerRemaining candidateOuter candidateInner input outerTape houter with
        ⟨finalTape, htail, hfinal⟩
      exact ⟨finalTape, TuringMachine.computes_trans hdone htail, hfinal⟩
  | succ candidateFuel ih =>
      let nextWord := pendingWord geometry round fuelRemaining outerRemaining
        innerRemaining candidateFuel candidateOuter candidateInner input
      rcases computes_exact_from_equiv
          (fuel_delete_succ_exact geometry round fuelRemaining outerRemaining
            innerRemaining candidateFuel candidateOuter candidateInner input)
          htape with
        ⟨gateTape, hdelete, hgate⟩
      have hinputGate : Tape.Equiv (Tape.input nextWord) gateTape := by
        exact Tape.Equiv.trans
          (Tape.Equiv.symm
            (gateLocate_tape_equiv_input .fuel nextWord)) hgate
      rcases computes_exact_from_equiv
          (locate_fuel_exact geometry round fuelRemaining outerRemaining
            innerRemaining candidateFuel candidateOuter candidateInner input)
          hinputGate with
        ⟨fuelTape, hlocate, hfuel⟩
      rcases ih fuelTape hfuel with
        ⟨finalTape, htail, hfinal⟩
      exact ⟨finalTape,
        TuringMachine.computes_trans hdelete
          (TuringMachine.computes_trans hlocate htail),
        hfinal⟩

theorem filterMap_map_some (word : Word MachineCodeSymbol) :
    List.filterMap (fun cell : Option MachineCodeSymbol => cell)
        (word.map some) = word := by
  induction word with
  | nil => rfl
  | cons symbol word ih =>
      simp [ih]

theorem filterMap_some_comp (word : Word MachineCodeSymbol) :
    List.filterMap
        ((fun cell : Option MachineCodeSymbol => cell) ∘ some) word = word := by
  induction word with
  | nil => rfl
  | cons symbol word ih =>
      simp [ih]

theorem normalizedOutput_cursorTape
    (leftRev rest : Word MachineCodeSymbol) :
    Tape.normalizedOutput
        (ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev rest) =
      List.append leftRev.reverse rest := by
  cases rest <;>
    simp [ExactFuel.StrictProbe.SerializedShift.cursorTape,
      Tape.normalizedOutput, Tape.cells, filterMap_map_some,
      filterMap_some_comp, Tape.filterMap_append_lemma,
      List.map_reverse, List.append_assoc]

theorem finalConfig_normalizedOutput
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining : Nat)
    (input : Word MachineCodeSymbol) :
    Tape.normalizedOutput
        (finalConfig geometry round fuelRemaining outerRemaining
          innerRemaining input).tape =
      pendingWord geometry round fuelRemaining outerRemaining
        innerRemaining 0 0 0 input := by
  rw [pendingWord_inner_decomp]
  simp [finalConfig, normalizedOutput_cursorTape,
    Scheduler.Rollover.Locator.natPrefixRev,
    Scheduler.Advance.ExhaustedSplitReset.ticks,
    MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
    List.reverse_append, List.append_assoc]

theorem reset_candidates
    (geometry : Scheduler.Layout.Geometry)
    (round fuelRemaining outerRemaining innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input
        (pendingWord geometry round fuelRemaining outerRemaining
          innerRemaining candidateFuel candidateOuter candidateInner input))
      tape) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start, tape := tape }
        { state := machine.halt, tape := finalTape } ∧
      Tape.Equiv
        (finalConfig geometry round fuelRemaining outerRemaining
          innerRemaining input).tape finalTape ∧
      Tape.normalizedOutput finalTape =
        pendingWord geometry round fuelRemaining outerRemaining
          innerRemaining 0 0 0 input := by
  rcases computes_exact_from_equiv
      (locate_fuel_exact geometry round fuelRemaining outerRemaining
        innerRemaining candidateFuel candidateOuter candidateInner input)
      htape with
    ⟨fuelTape, hlocate, hfuel⟩
  rcases reset_fuel geometry round fuelRemaining outerRemaining
      innerRemaining candidateFuel candidateOuter candidateInner input
      fuelTape hfuel with
    ⟨finalTape, htail, hfinal⟩
  refine ⟨finalTape, ?_, hfinal, ?_⟩
  · exact TuringMachine.computes_trans hlocate htail
  · rw [← Tape.Equiv.normalizedOutput_eq hfinal]
    exact finalConfig_normalizedOutput geometry round fuelRemaining
      outerRemaining innerRemaining input

theorem pendingWord_after_rollover_eq_targetWord
    (geometry : Scheduler.Layout.Geometry) (round newBound : Nat)
    (input : Word MachineCodeSymbol) :
    pendingWord geometry (round + 1) (round + 1) newBound newBound
        0 0 0 input =
      Scheduler.Rollover.targetWord geometry round newBound input := by
  rfl

theorem reset_candidates_after_rollover
    (geometry : Scheduler.Layout.Geometry)
    (round newBound candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input
        (pendingWord geometry (round + 1) (round + 1) newBound newBound
          candidateFuel candidateOuter candidateInner input)) tape) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start, tape := tape }
        { state := machine.halt, tape := finalTape } ∧
      Tape.Equiv
        (finalConfig geometry (round + 1) (round + 1) newBound newBound
          input).tape finalTape ∧
      Tape.normalizedOutput finalTape =
        Scheduler.Rollover.targetWord geometry round newBound input := by
  rcases reset_candidates geometry (round + 1) (round + 1) newBound
      newBound candidateFuel candidateOuter candidateInner input tape htape with
    ⟨finalTape, hrun, hequiv, hout⟩
  exact ⟨finalTape, hrun, hequiv,
    hout.trans (pendingWord_after_rollover_eq_targetWord geometry round
      newBound input)⟩

theorem afterInnerWord_eq_pendingWord
    (geometry : Scheduler.Layout.Geometry)
    (round oldBound newBound : Nat) (input : Word MachineCodeSymbol) :
    Scheduler.Rollover.afterInnerWord geometry round oldBound newBound
        input =
      pendingWord geometry (round + 1) (round + 1) newBound newBound
        round oldBound oldBound input := by
  rfl

theorem reset_after_main_rollover
    (geometry : Scheduler.Layout.Geometry)
    (round oldBound newBound : Nat) (input : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input
        (Scheduler.Rollover.afterInnerWord geometry round oldBound
          newBound input)) tape) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start, tape := tape }
        { state := machine.halt, tape := finalTape } ∧
      Tape.Equiv
        (finalConfig geometry (round + 1) (round + 1) newBound newBound
          input).tape finalTape ∧
      Tape.normalizedOutput finalTape =
        Scheduler.Rollover.targetWord geometry round newBound input := by
  rw [afterInnerWord_eq_pendingWord] at htape
  exact reset_candidates_after_rollover geometry round newBound round oldBound
    oldBound input tape htape

theorem reset_after_main_rollover_unbounded
    (round : Nat) (input : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input
        (Scheduler.Rollover.afterInnerWord .unbounded round round
          (round + 1) input)) tape) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start, tape := tape }
        { state := machine.halt, tape := finalTape } ∧
      Tape.Equiv
        (finalConfig .unbounded (round + 1) (round + 1) (round + 1)
          (round + 1) input).tape finalTape ∧
      Tape.normalizedOutput finalTape =
        Scheduler.Rollover.targetWord .unbounded round (round + 1)
          input ∧
      Scheduler.SplitLayout.decode
          (Tape.normalizedOutput finalTape) =
        some (Scheduler.Rollover.targetFrame .unbounded round input) := by
  rcases reset_after_main_rollover .unbounded round round (round + 1) input
      tape htape with
    ⟨finalTape, hrun, hequiv, hout⟩
  refine ⟨finalTape, hrun, hequiv, hout, ?_⟩
  rw [hout]
  exact Scheduler.Rollover.target_decode_unbounded round input

theorem reset_after_main_rollover_bounded
    (budget round : Nat) (input : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input
        (Scheduler.Rollover.afterInnerWord (.bounded budget) round budget
          budget input)) tape) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start, tape := tape }
        { state := machine.halt, tape := finalTape } ∧
      Tape.Equiv
        (finalConfig (.bounded budget) (round + 1) (round + 1) budget
          budget input).tape finalTape ∧
      Tape.normalizedOutput finalTape =
        Scheduler.Rollover.targetWord (.bounded budget) round budget
          input ∧
      Scheduler.SplitLayout.decode
          (Tape.normalizedOutput finalTape) =
        some
          (Scheduler.Rollover.targetFrame (.bounded budget) round
            input) := by
  rcases reset_after_main_rollover (.bounded budget) round budget budget input
      tape htape with
    ⟨finalTape, hrun, hequiv, hout⟩
  refine ⟨finalTape, hrun, hequiv, hout, ?_⟩
  rw [hout]
  exact Scheduler.Rollover.target_decode_bounded budget round input

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.CandidateReset
