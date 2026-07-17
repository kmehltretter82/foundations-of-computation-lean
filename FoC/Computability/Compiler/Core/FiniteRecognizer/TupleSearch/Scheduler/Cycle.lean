import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.SplitStaging
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.CandidateRecovery
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.DispatchRuns
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.UnboundedInitializer
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.Reachability

set_option doc.verso true

/-!
**Candidate-attempt cycle.** This machine finitely composes one split-scheduler
candidate attempt.

Each component halt is followed by a right/left bounce.  The bounce keeps the
next phase at the same logical tape position modulo
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv`, while using only
ordinary left/right Turing-machine moves.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Cycle

open Languages
open ExactFuel.StrictProbe

abbrev Frame := Scheduler.Layout.Frame
abbrev EraseControl := Scheduler.SplitStaging.Control
abbrev GapControl := ProductGapExpander.Control 2

inductive Control {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) where
  | duplicate (inner : ProductDuplicator.Control)
  | duplicateReturn
  | erase (inner : EraseControl)
  | eraseReturn
  | gap (inner : GapControl)
  | gapReturn
  | materialize (inner : Scheduler.CandidateMaterializer.Control selected)
  | materializeReturn
  | probe (inner : CandidateKernel.ProbeReturn.Control stateCount)
  | probeHitReturn
  | probeMissReturn
  | recovery (inner : ProductHandoff.Control)
  | recoveryReturn
  | dispatch (inner : Scheduler.Dispatch.Control)
  | dispatchReturn
  | halt
deriving DecidableEq

namespace Control

def elems {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    List (Control selected) :=
  ProductDuplicator.Control.finite.elems.map Control.duplicate ++
    [.duplicateReturn] ++
  Scheduler.SplitStaging.Control.finite.elems.map Control.erase ++
    [.eraseReturn] ++
  (ProductGapExpander.Control.finite 2).elems.map Control.gap ++
    [.gapReturn] ++
  (Scheduler.CandidateMaterializer.Control.finite selected).elems.map
      Control.materialize ++
    [.materializeReturn] ++
  (CandidateKernel.ProbeReturn.Control.finite stateCount).elems.map
      Control.probe ++
    [.probeHitReturn, .probeMissReturn] ++
  ProductHandoff.Control.finite.elems.map Control.recovery ++
    [.recoveryReturn] ++
  Scheduler.Dispatch.Control.finite.elems.map Control.dispatch ++
    [.dispatchReturn, .halt]

def finite {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Foundation.FiniteType (Control selected) where
  elems := elems selected
  complete := by
    intro control
    cases control with
    | duplicate inner =>
        simp [elems, ProductDuplicator.Control.finite.complete inner]
    | duplicateReturn => simp [elems]
    | erase inner =>
        simp [elems,
          Scheduler.SplitStaging.Control.finite.complete inner]
    | eraseReturn => simp [elems]
    | gap inner =>
        simp [elems, (ProductGapExpander.Control.finite 2).complete inner]
    | gapReturn => simp [elems]
    | materialize inner =>
        simp [elems,
          (Scheduler.CandidateMaterializer.Control.finite selected).complete
            inner]
    | materializeReturn => simp [elems]
    | probe inner =>
        simp [elems,
          (CandidateKernel.ProbeReturn.Control.finite stateCount).complete
            inner]
    | probeHitReturn => simp [elems]
    | probeMissReturn => simp [elems]
    | recovery inner =>
        simp [elems, ProductHandoff.Control.finite.complete inner]
    | recoveryReturn => simp [elems]
    | dispatch inner =>
        simp [elems, Scheduler.Dispatch.Control.finite.complete inner]
    | dispatchReturn => simp [elems]
    | halt => simp [elems]

end Control

def mapAction {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (embed : inner -> Control selected) :
    Option (Option MachineCodeSymbol × Direction × inner) ->
      Option (Option MachineCodeSymbol × Direction × Control selected)
  | none => none
  | some (write, direction, target) =>
      some (write, direction, embed target)

def materializerEntry {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Scheduler.CandidateMaterializer.Control selected :=
  .materializer (.tail .capture)

def transition {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Control selected -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control selected)
  | .duplicate inner, read =>
      if inner = ProductDuplicator.machine.halt then
        some (read, Direction.right, .duplicateReturn)
      else
        mapAction Control.duplicate
          (ProductDuplicator.transition inner read)
  | .duplicateReturn, read =>
      some (read, Direction.left,
        .erase Scheduler.SplitStaging.machine.start)
  | .erase inner, read =>
      if inner = Scheduler.SplitStaging.machine.halt then
        some (read, Direction.right, .eraseReturn)
      else
        mapAction Control.erase
          (Scheduler.SplitStaging.transition inner read)
  | .eraseReturn, read =>
      some (read, Direction.left,
        .gap (ProductGapExpander.machine (by decide : 0 < 2)).start)
  | .gap inner, read =>
      if inner = (ProductGapExpander.machine (by decide : 0 < 2)).halt then
        some (read, Direction.right, .gapReturn)
      else
        mapAction Control.gap
          (ProductGapExpander.transition (by decide : 0 < 2) inner read)
  | .gapReturn, read =>
      some (read, Direction.left,
        .materialize (materializerEntry selected))
  | .materialize inner, read =>
      if inner = (Scheduler.CandidateMaterializer.machine selected).halt then
        some (read, Direction.right, .materializeReturn)
      else
        mapAction Control.materialize
          (Scheduler.CandidateMaterializer.transition selected inner read)
  | .materializeReturn, read =>
      some (read, Direction.left,
        .probe (CandidateKernel.ProbeReturn.machine selected).start)
  | .probe inner, read =>
      if inner = CandidateKernel.ProbeReturn.Control.hit then
        some (read, Direction.right, .probeHitReturn)
      else if inner = CandidateKernel.ProbeReturn.Control.miss then
        some (read, Direction.right, .probeMissReturn)
      else
        mapAction Control.probe
          (CandidateKernel.ProbeReturn.transition selected inner read)
  | .probeHitReturn, read =>
      some (read, Direction.left, .halt)
  | .probeMissReturn, read =>
      some (read, Direction.left, .recovery ProductHandoff.machine.start)
  | .recovery inner, read =>
      if inner = ProductHandoff.machine.halt then
        some (read, Direction.right, .recoveryReturn)
      else
        mapAction Control.recovery (ProductHandoff.transition inner read)
  | .recoveryReturn, read =>
      some (read, Direction.left,
        .dispatch Scheduler.Dispatch.machine.start)
  | .dispatch inner, read =>
      if inner = Scheduler.Dispatch.machine.halt then
        some (read, Direction.right, .dispatchReturn)
      else
        mapAction Control.dispatch
          (Scheduler.Dispatch.transition inner read)
  | .dispatchReturn, read =>
      some (read, Direction.left,
        .duplicate ProductDuplicator.machine.start)
  | .halt, _ => none

def machine {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine MachineCodeSymbol (Control selected) where
  start := .duplicate ProductDuplicator.machine.start
  halt := .halt
  transition := transition selected
  statesFinite := Control.finite selected

theorem machine_haltingTransitionsDisabled {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine.HaltingTransitionsDisabled (machine selected) := by
  intro read
  rfl

theorem step_of_mapped_transition
    {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control selected)
    (hmap : ∀ (state : innerState) (read : Option MachineCodeSymbol)
        (action : Option MachineCodeSymbol × Direction × innerState),
      inner.transition state read = some action ->
      transition selected (embed state) read = mapAction embed (some action))
    (source target : TuringMachine.Configuration MachineCodeSymbol innerState)
    (hstep : inner.stepConfig source = some target) :
    (machine selected).stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig embed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  cases source with
  | mk state tape =>
      cases target with
      | mk targetState targetTape =>
          unfold TuringMachine.stepConfig at hstep ⊢
          dsimp [machine]
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          cases haction : inner.transition state (Tape.read tape) with
          | none =>
              rw [haction] at hstep
              contradiction
          | some action =>
              rcases action with ⟨write, direction, nextState⟩
              rw [haction] at hstep
              simp only at hstep
              have hmapped := hmap state (Tape.read tape)
                (write, direction, nextState) haction
              rw [hmapped]
              cases hstep
              rfl

theorem duplicate_map {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : ProductDuplicator.Control) (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      ProductDuplicator.Control)
    (haction : ProductDuplicator.machine.transition state read =
      some action) :
    transition selected (.duplicate state) read =
      mapAction Control.duplicate (some action) := by
  by_cases hhalt : state = ProductDuplicator.machine.halt
  · subst state
    simp [ProductDuplicator.machine, ProductDuplicator.transition] at haction
  · change ProductDuplicator.transition state read = some action at haction
    change state ≠ ProductDuplicator.Control.halt at hhalt
    simp [transition, ProductDuplicator.machine, hhalt, haction]

theorem erase_map {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : EraseControl) (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × EraseControl)
    (haction : Scheduler.SplitStaging.machine.transition state read =
      some action) :
    transition selected (.erase state) read =
      mapAction Control.erase (some action) := by
  by_cases hhalt : state = Scheduler.SplitStaging.machine.halt
  · subst state
    simp [Scheduler.SplitStaging.machine,
      Scheduler.SplitStaging.transition] at haction
  · change Scheduler.SplitStaging.transition state read =
      some action at haction
    change state ≠ Scheduler.SplitStaging.Control.halt at hhalt
    simp [transition, Scheduler.SplitStaging.machine, hhalt, haction]

theorem gap_map {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : GapControl) (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × GapControl)
    (haction :
      (ProductGapExpander.machine (by decide : 0 < 2)).transition state read =
        some action) :
    transition selected (.gap state) read =
      mapAction Control.gap (some action) := by
  by_cases hhalt :
      state = (ProductGapExpander.machine (by decide : 0 < 2)).halt
  · subst state
    simp [ProductGapExpander.machine,
      ProductGapExpander.transition] at haction
  · change ProductGapExpander.transition (by decide : 0 < 2)
      state read = some action at haction
    change state ≠ ProductGapExpander.Control.halt at hhalt
    simp [transition, ProductGapExpander.machine, hhalt, haction]

theorem materialize_map {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : Scheduler.CandidateMaterializer.Control selected)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      Scheduler.CandidateMaterializer.Control selected)
    (haction : (Scheduler.CandidateMaterializer.machine selected).transition
      state read = some action) :
    transition selected (.materialize state) read =
      mapAction Control.materialize (some action) := by
  by_cases hhalt :
      state = (Scheduler.CandidateMaterializer.machine selected).halt
  · subst state
    simp [Scheduler.CandidateMaterializer.machine,
      Scheduler.CandidateMaterializer.transition] at haction
  · change Scheduler.CandidateMaterializer.transition selected state read =
      some action at haction
    change state ≠ Scheduler.CandidateMaterializer.Control.halt at hhalt
    simp [transition, Scheduler.CandidateMaterializer.machine, hhalt, haction]

theorem probe_map {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : CandidateKernel.ProbeReturn.Control stateCount)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      CandidateKernel.ProbeReturn.Control stateCount)
    (haction : (CandidateKernel.ProbeReturn.machine selected).transition
      state read = some action) :
    transition selected (.probe state) read =
      mapAction Control.probe (some action) := by
  by_cases hhit : state = CandidateKernel.ProbeReturn.Control.hit
  · subst state
    simp [CandidateKernel.ProbeReturn.machine,
      CandidateKernel.ProbeReturn.transition] at haction
  · by_cases hmiss : state = CandidateKernel.ProbeReturn.Control.miss
    · subst state
      simp [CandidateKernel.ProbeReturn.machine,
        CandidateKernel.ProbeReturn.transition] at haction
    · change CandidateKernel.ProbeReturn.transition selected state read =
        some action at haction
      simp [transition, hhit, hmiss, haction]

theorem recovery_map {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : ProductHandoff.Control) (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      ProductHandoff.Control)
    (haction : ProductHandoff.machine.transition state read = some action) :
    transition selected (.recovery state) read =
      mapAction Control.recovery (some action) := by
  by_cases hhalt : state = ProductHandoff.machine.halt
  · subst state
    simp [ProductHandoff.machine, ProductHandoff.transition] at haction
  · change ProductHandoff.transition state read = some action at haction
    change state ≠ ProductHandoff.Control.gate at hhalt
    simp [transition, ProductHandoff.machine, hhalt, haction]

theorem dispatch_map {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (state : Scheduler.Dispatch.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      Scheduler.Dispatch.Control)
    (haction : Scheduler.Dispatch.machine.transition state read =
      some action) :
    transition selected (.dispatch state) read =
      mapAction Control.dispatch (some action) := by
  by_cases hhalt : state = Scheduler.Dispatch.machine.halt
  · subst state
    simp [Scheduler.Dispatch.machine,
      Scheduler.Dispatch.transition] at haction
  · change Scheduler.Dispatch.transition state read =
      some action at haction
    change state ≠ Scheduler.Dispatch.Control.halt at hhalt
    simp [transition, Scheduler.Dispatch.machine, hhalt, haction]

theorem computes_lift_active
    {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {inner : TuringMachine MachineCodeSymbol innerState}
    (embed : innerState -> Control selected)
    (hstep : ∀
      (source target : TuringMachine.Configuration MachineCodeSymbol
        innerState),
      inner.stepConfig source = some target ->
        (machine selected).stepConfig
            (TuringMachine.PhaseEmbedding.liftConfig embed source) =
          some (TuringMachine.PhaseEmbedding.liftConfig embed target))
    {source target : TuringMachine.Configuration MachineCodeSymbol innerState}
    (hrun : TuringMachine.Computes inner source target) :
    TuringMachine.Computes (machine selected)
      (TuringMachine.PhaseEmbedding.liftConfig embed source)
      (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    embed hstep
  exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

theorem duplicate_computes_lift
    {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control}
    (hrun : TuringMachine.Computes ProductDuplicator.machine source target) :
    TuringMachine.Computes (machine selected)
      (TuringMachine.PhaseEmbedding.liftConfig Control.duplicate source)
      (TuringMachine.PhaseEmbedding.liftConfig Control.duplicate target) := by
  exact computes_lift_active Control.duplicate
    (step_of_mapped_transition ProductDuplicator.machine Control.duplicate
      (duplicate_map selected)) hrun

theorem erase_computes_lift
    {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      EraseControl}
    (hrun : TuringMachine.Computes Scheduler.SplitStaging.machine
      source target) :
    TuringMachine.Computes (machine selected)
      (TuringMachine.PhaseEmbedding.liftConfig Control.erase source)
      (TuringMachine.PhaseEmbedding.liftConfig Control.erase target) := by
  exact computes_lift_active Control.erase
    (step_of_mapped_transition Scheduler.SplitStaging.machine
      Control.erase (erase_map selected)) hrun

theorem gap_computes_lift
    {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      GapControl}
    (hrun : TuringMachine.Computes
      (ProductGapExpander.machine (by decide : 0 < 2)) source target) :
    TuringMachine.Computes (machine selected)
      (TuringMachine.PhaseEmbedding.liftConfig Control.gap source)
      (TuringMachine.PhaseEmbedding.liftConfig Control.gap target) := by
  exact computes_lift_active Control.gap
    (step_of_mapped_transition
      (ProductGapExpander.machine (by decide : 0 < 2))
      Control.gap (gap_map selected)) hrun

theorem materialize_computes_lift
    {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.CandidateMaterializer.Control selected)}
    (hrun : TuringMachine.Computes
      (Scheduler.CandidateMaterializer.machine selected) source target) :
    TuringMachine.Computes (machine selected)
      (TuringMachine.PhaseEmbedding.liftConfig Control.materialize source)
      (TuringMachine.PhaseEmbedding.liftConfig Control.materialize target) := by
  exact computes_lift_active Control.materialize
    (step_of_mapped_transition
      (Scheduler.CandidateMaterializer.machine selected)
      Control.materialize (materialize_map selected)) hrun

theorem probe_computes_lift
    {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (CandidateKernel.ProbeReturn.Control stateCount)}
    (hrun : TuringMachine.Computes
      (CandidateKernel.ProbeReturn.machine selected) source target) :
    TuringMachine.Computes (machine selected)
      (TuringMachine.PhaseEmbedding.liftConfig Control.probe source)
      (TuringMachine.PhaseEmbedding.liftConfig Control.probe target) := by
  exact computes_lift_active Control.probe
    (step_of_mapped_transition
      (CandidateKernel.ProbeReturn.machine selected)
      Control.probe (probe_map selected)) hrun

theorem recovery_computes_lift
    {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      ProductHandoff.Control}
    (hrun : TuringMachine.Computes ProductHandoff.machine source target) :
    TuringMachine.Computes (machine selected)
      (TuringMachine.PhaseEmbedding.liftConfig Control.recovery source)
      (TuringMachine.PhaseEmbedding.liftConfig Control.recovery target) := by
  exact computes_lift_active Control.recovery
    (step_of_mapped_transition ProductHandoff.machine Control.recovery
      (recovery_map selected)) hrun

theorem dispatch_computes_lift
    {stateCount : Nat}
    {selected : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Scheduler.Dispatch.Control}
    (hrun : TuringMachine.Computes Scheduler.Dispatch.machine
      source target) :
    TuringMachine.Computes (machine selected)
      (TuringMachine.PhaseEmbedding.liftConfig Control.dispatch source)
      (TuringMachine.PhaseEmbedding.liftConfig Control.dispatch target) := by
  exact computes_lift_active Control.dispatch
    (step_of_mapped_transition Scheduler.Dispatch.machine
      Control.dispatch (dispatch_map selected)) hrun

theorem computes_of_run_exact
    {M : TuringMachine symbol state}
    {steps : Nat}
    {source target : TuringMachine.Configuration symbol state}
    (hrun : M.runConfigExact? steps source = some target) :
    TuringMachine.Computes M source target := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)

theorem duplicate_bounce_run_exact
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tape : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := .duplicate ProductDuplicator.machine.halt
          tape := tape } =
      some
        { state := .erase Scheduler.SplitStaging.machine.start
          tape := CyclicDriverIntegration.roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, ProductDuplicator.machine,
    CyclicDriverIntegration.roundTripTape, Tape.write_read_eq_self]

theorem erase_bounce_run_exact
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tape : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := .erase Scheduler.SplitStaging.machine.halt
          tape := tape } =
      some
        { state := .gap
            (ProductGapExpander.machine (by decide : 0 < 2)).start
          tape := CyclicDriverIntegration.roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, Scheduler.SplitStaging.machine,
    CyclicDriverIntegration.roundTripTape, Tape.write_read_eq_self]

theorem gap_bounce_run_exact
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tape : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := .gap
            (ProductGapExpander.machine (by decide : 0 < 2)).halt
          tape := tape } =
      some
        { state := .materialize (materializerEntry selected)
          tape := CyclicDriverIntegration.roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, ProductGapExpander.machine,
    CyclicDriverIntegration.roundTripTape, Tape.write_read_eq_self]

theorem materialize_bounce_run_exact
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tape : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := .materialize
            (Scheduler.CandidateMaterializer.machine selected).halt
          tape := tape } =
      some
        { state := .probe
            (CandidateKernel.ProbeReturn.machine selected).start
          tape := CyclicDriverIntegration.roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, Scheduler.CandidateMaterializer.machine,
    CyclicDriverIntegration.roundTripTape, Tape.write_read_eq_self]

theorem probe_hit_bounce_run_exact
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tape : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := .probe CandidateKernel.ProbeReturn.Control.hit
          tape := tape } =
      some
        { state := Control.halt
          tape := CyclicDriverIntegration.roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, CyclicDriverIntegration.roundTripTape,
    Tape.write_read_eq_self]

theorem probe_miss_bounce_run_exact
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tape : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := .probe CandidateKernel.ProbeReturn.Control.miss
          tape := tape } =
      some
        { state := .recovery ProductHandoff.machine.start
          tape := CyclicDriverIntegration.roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, ProductHandoff.machine,
    CyclicDriverIntegration.roundTripTape, Tape.write_read_eq_self]

theorem recovery_bounce_run_exact
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tape : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := .recovery ProductHandoff.machine.halt
          tape := tape } =
      some
        { state := .dispatch Scheduler.Dispatch.machine.start
          tape := CyclicDriverIntegration.roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, ProductHandoff.machine,
    CyclicDriverIntegration.roundTripTape, Tape.write_read_eq_self]

theorem dispatch_bounce_run_exact
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tape : Tape MachineCodeSymbol) :
    (machine selected).runConfigExact? 2
        { state := .dispatch Scheduler.Dispatch.machine.halt
          tape := tape } =
      some
        { state := .duplicate ProductDuplicator.machine.start
          tape := CyclicDriverIntegration.roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, Scheduler.Dispatch.machine,
    ProductDuplicator.machine, CyclicDriverIntegration.roundTripTape,
    Tape.write_read_eq_self]

theorem roundTripTape_equiv_self (tape : Tape MachineCodeSymbol) :
    Tape.Equiv (CyclicDriverIntegration.roundTripTape tape) tape := by
  exact ExactFuel.StrictProbe.Machine.moveLeft_moveRight_equiv_self tape

theorem computes_from_tape_equiv
    {M : TuringMachine symbol state}
    {source target : TuringMachine.Configuration symbol state}
    {sourceTape : Tape symbol}
    (hrun : TuringMachine.Computes M source target)
    (htape : Tape.Equiv source.tape sourceTape) :
    exists actual : TuringMachine.Configuration symbol state,
      TuringMachine.Computes M
        { state := source.state, tape := sourceTape } actual ∧
      actual.state = target.state ∧
      Tape.Equiv target.tape actual.tape := by
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hrunIn htape with ⟨actual, hactual, hstate, htargetTape⟩
  exact ⟨actual, TuringMachine.computesIn_to_computes hactual,
    hstate, htargetTape⟩

theorem splitTailSource_state_eq_entry
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) :
    (Scheduler.SplitStaging.splitTailSource selected frame).state =
      materializerEntry selected := by
  rfl

theorem staging_to_probe_start
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input (Scheduler.SplitLayout.encode frame)) sourceTape) :
    exists probeTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine selected)
        { state := (machine selected).start, tape := sourceTape }
        { state := .probe
            (CandidateKernel.ProbeReturn.machine selected).start
          tape := probeTape } ∧
      Tape.Equiv
        (CandidateKernel.ProbeReturn.candidateTape selected
          (Scheduler.SplitLayout.encode frame) frame.input
          frame.cursor.inner frame.cursor.outer
          frame.cursor.selectedFuel)
        probeTape := by
  rcases Scheduler.SplitStaging.recovered_frame_to_candidate_phases
      selected frame sourceTape hsource with
    ⟨duplicatorEndpoint, eraseSteps, erasedEndpoint, gapEndpoint,
      materializeSteps, candidateEndpoint,
      hduplicate, hduplicateState, herase, heraseState,
      hgap, hgapState, hmaterialize, hcandidateState, hcandidateTape⟩
  rcases duplicatorEndpoint with ⟨duplicatorState, duplicatorTape⟩
  simp only at hduplicateState hduplicate
  subst duplicatorState
  have hduplicateOuter := duplicate_computes_lift
    (selected := selected) (computes_of_run_exact hduplicate)
  have hduplicateOuter' : TuringMachine.Computes (machine selected)
      { state := (machine selected).start, tape := sourceTape }
      { state := .duplicate ProductDuplicator.machine.halt,
        tape := duplicatorTape } := by
    simpa [machine, TuringMachine.PhaseEmbedding.liftConfig] using
      hduplicateOuter
  have hduplicateBounce := computes_of_run_exact
    (duplicate_bounce_run_exact selected duplicatorTape)
  have hthroughDuplicate := TuringMachine.computes_trans
    hduplicateOuter' hduplicateBounce

  rcases erasedEndpoint with ⟨erasedState, erasedTape⟩
  simp only at heraseState herase
  subst erasedState
  have heraseSource : Tape.Equiv duplicatorTape
      (CyclicDriverIntegration.roundTripTape duplicatorTape) :=
    Tape.Equiv.symm (roundTripTape_equiv_self duplicatorTape)
  rcases computes_from_tape_equiv (computes_of_run_exact herase)
      heraseSource with
    ⟨actualErase, heraseActual, hactualEraseState, heraseTape⟩
  rcases actualErase with ⟨actualEraseState, actualEraseTape⟩
  simp only at hactualEraseState heraseActual heraseTape
  subst actualEraseState
  have heraseOuter := erase_computes_lift
    (selected := selected) heraseActual
  have heraseOuter' : TuringMachine.Computes (machine selected)
      { state := .erase Scheduler.SplitStaging.machine.start,
        tape := CyclicDriverIntegration.roundTripTape duplicatorTape }
      { state := .erase Scheduler.SplitStaging.machine.halt,
        tape := actualEraseTape } := by
    simpa [TuringMachine.PhaseEmbedding.liftConfig,
      Scheduler.SplitStaging.config,
      Scheduler.SplitStaging.machine] using heraseOuter
  have heraseBounce := computes_of_run_exact
    (erase_bounce_run_exact selected actualEraseTape)
  have hthroughErase := TuringMachine.computes_trans hthroughDuplicate
    (TuringMachine.computes_trans heraseOuter' heraseBounce)

  rcases gapEndpoint with ⟨gapState, gapTape⟩
  simp only at hgapState hgap
  subst gapState
  have hgapSource : Tape.Equiv erasedTape
      (CyclicDriverIntegration.roundTripTape actualEraseTape) :=
    Tape.Equiv.trans heraseTape
      (Tape.Equiv.symm (roundTripTape_equiv_self actualEraseTape))
  rcases computes_from_tape_equiv (computes_of_run_exact hgap)
      hgapSource with
    ⟨actualGap, hgapActual, hactualGapState, hgapTape⟩
  rcases actualGap with ⟨actualGapState, actualGapTape⟩
  simp only at hactualGapState hgapActual hgapTape
  subst actualGapState
  have hgapOuter := gap_computes_lift
    (selected := selected) hgapActual
  have hgapOuter' : TuringMachine.Computes (machine selected)
      { state := .gap
          (ProductGapExpander.machine (by decide : 0 < 2)).start,
        tape := CyclicDriverIntegration.roundTripTape actualEraseTape }
      { state := .gap
          (ProductGapExpander.machine (by decide : 0 < 2)).halt,
        tape := actualGapTape } := by
    simpa [TuringMachine.PhaseEmbedding.liftConfig] using hgapOuter
  have hgapBounce := computes_of_run_exact
    (gap_bounce_run_exact selected actualGapTape)
  have hthroughGap := TuringMachine.computes_trans hthroughErase
    (TuringMachine.computes_trans hgapOuter' hgapBounce)

  rcases candidateEndpoint with ⟨candidateState, canonicalCandidateTape⟩
  simp only at hcandidateState hmaterialize hcandidateTape
  subst candidateState
  have hmaterializeSource : Tape.Equiv gapTape
      (CyclicDriverIntegration.roundTripTape actualGapTape) :=
    Tape.Equiv.trans hgapTape
      (Tape.Equiv.symm (roundTripTape_equiv_self actualGapTape))
  rcases computes_from_tape_equiv (computes_of_run_exact hmaterialize)
      hmaterializeSource with
    ⟨actualMaterialize, hmaterializeActual, hactualMaterializeState,
      hmaterializeTape⟩
  rcases actualMaterialize with
    ⟨actualMaterializeState, actualMaterializeTape⟩
  simp only at hactualMaterializeState hmaterializeActual hmaterializeTape
  subst actualMaterializeState
  have hmaterializeOuter := materialize_computes_lift
    (selected := selected) hmaterializeActual
  have hmaterializeOuter' : TuringMachine.Computes (machine selected)
      { state := .materialize (materializerEntry selected),
        tape := CyclicDriverIntegration.roundTripTape actualGapTape }
      { state := .materialize
          (Scheduler.CandidateMaterializer.machine selected).halt,
        tape := actualMaterializeTape } := by
    simpa [TuringMachine.PhaseEmbedding.liftConfig,
      splitTailSource_state_eq_entry] using hmaterializeOuter
  have hmaterializeBounce := computes_of_run_exact
    (materialize_bounce_run_exact selected actualMaterializeTape)
  let probeTape := CyclicDriverIntegration.roundTripTape actualMaterializeTape
  refine ⟨probeTape, ?_, ?_⟩
  · exact TuringMachine.computes_trans hthroughGap
      (TuringMachine.computes_trans hmaterializeOuter'
        hmaterializeBounce)
  · exact Tape.Equiv.trans (Tape.Equiv.symm hcandidateTape)
      (Tape.Equiv.trans hmaterializeTape
        (Tape.Equiv.symm
          (roundTripTape_equiv_self actualMaterializeTape)))

theorem candidateSource_state_eq_probe_start
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (callerData input : Word MachineCodeSymbol)
    (inner outer selectedFuel : Nat) :
    (CandidateKernel.ProbeReturn.candidateSource selected callerData input
      inner outer selectedFuel).state =
      (CandidateKernel.ProbeReturn.machine selected).start := by
  rfl

theorem exact_candidate_reaches_public_halt
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input (Scheduler.SplitLayout.encode frame)) sourceTape)
    (hexact : TuringMachine.HaltsOnInputIn selected
      frame.cursor.selectedFuel
      (GeneratedCode.nestedStageCode frame.input
        frame.cursor.inner frame.cursor.outer)) :
    exists finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine selected)
        { state := (machine selected).start, tape := sourceTape }
        { state := (machine selected).halt, tape := finalTape } := by
  rcases staging_to_probe_start selected frame sourceTape hsource with
    ⟨probeTape, hstaging, hprobeTape⟩
  rcases CandidateKernel.ProbeReturn.candidate_hit_of_exact selected
      (Scheduler.SplitLayout.encode frame) frame.input
      frame.cursor.inner frame.cursor.outer frame.cursor.selectedFuel
      hexact with ⟨canonicalHitBase, hhit⟩
  rcases computes_from_tape_equiv hhit hprobeTape with
    ⟨actualHit, hhitActual, hhitState, hhitTape⟩
  rcases actualHit with ⟨actualHitState, actualHitTape⟩
  simp only [CandidateKernel.ProbeReturn.hitConfig] at hhitState hhitActual hhitTape
  subst actualHitState
  have hhitOuter := probe_computes_lift
    (selected := selected) hhitActual
  have hhitOuter' : TuringMachine.Computes (machine selected)
      { state := .probe
          (CandidateKernel.ProbeReturn.machine selected).start,
        tape := probeTape }
      { state := .probe CandidateKernel.ProbeReturn.Control.hit,
        tape := actualHitTape } := by
    simpa [candidateSource_state_eq_probe_start,
      TuringMachine.PhaseEmbedding.liftConfig] using hhitOuter
  have hhitBounce := computes_of_run_exact
    (probe_hit_bounce_run_exact selected actualHitTape)
  refine ⟨CyclicDriverIntegration.roundTripTape actualHitTape, ?_⟩
  exact TuringMachine.computes_trans hstaging
    (TuringMachine.computes_trans hhitOuter' hhitBounce)

theorem nonexact_candidate_reaches_dispatch
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input (Scheduler.SplitLayout.encode frame)) sourceTape)
    (hnot : ¬ TuringMachine.HaltsOnInputIn selected
      frame.cursor.selectedFuel
      (GeneratedCode.nestedStageCode frame.input
        frame.cursor.inner frame.cursor.outer)) :
    exists dispatchTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine selected)
        { state := (machine selected).start, tape := sourceTape }
        { state := .dispatch Scheduler.Dispatch.machine.start,
          tape := dispatchTape } ∧
      Tape.Equiv
        (Tape.input (Scheduler.SplitLayout.encode frame))
        dispatchTape := by
  rcases staging_to_probe_start selected frame sourceTape hsource with
    ⟨probeTape, hstaging, hprobeTape⟩
  rcases CandidateKernel.ProbeReturn.Recovery.candidate_miss_recovers_caller_of_not_exact
      selected
      (Scheduler.SplitLayout.encode frame) frame.input
      frame.cursor.inner frame.cursor.outer frame.cursor.selectedFuel hnot with
    ⟨remainingFuel, finalFrame, endpointTape, recoveryEndpoint,
      _hrep, hmiss, hrecovery, hrecoveryState, hcaller,
      _hread, _hnormalized⟩
  rcases computes_from_tape_equiv hmiss hprobeTape with
    ⟨actualMiss, hmissActual, hmissState, hmissTape⟩
  rcases actualMiss with ⟨actualMissState, actualMissTape⟩
  simp only [CandidateKernel.ProbeReturn.missConfig] at hmissState hmissActual hmissTape
  subst actualMissState
  have hmissOuter := probe_computes_lift
    (selected := selected) hmissActual
  have hmissOuter' : TuringMachine.Computes (machine selected)
      { state := .probe
          (CandidateKernel.ProbeReturn.machine selected).start,
        tape := probeTape }
      { state := .probe CandidateKernel.ProbeReturn.Control.miss,
        tape := actualMissTape } := by
    simpa [candidateSource_state_eq_probe_start,
      TuringMachine.PhaseEmbedding.liftConfig] using hmissOuter
  have hmissBounce := computes_of_run_exact
    (probe_miss_bounce_run_exact selected actualMissTape)
  have hthroughMiss := TuringMachine.computes_trans hstaging
    (TuringMachine.computes_trans hmissOuter' hmissBounce)

  rcases recoveryEndpoint with
    ⟨canonicalRecoveryState, canonicalRecoveryTape⟩
  simp only at hrecoveryState hrecovery hcaller
  subst canonicalRecoveryState
  have hrecoverySource : Tape.Equiv
      (CyclicDriverIntegration.roundTripTape endpointTape)
      (CyclicDriverIntegration.roundTripTape actualMissTape) :=
    Tape.Equiv.trans hmissTape
      (Tape.Equiv.symm (roundTripTape_equiv_self actualMissTape))
  rcases computes_from_tape_equiv (computes_of_run_exact hrecovery)
      hrecoverySource with
    ⟨actualRecovery, hrecoveryActual, hactualRecoveryState,
      hrecoveryTape⟩
  rcases actualRecovery with
    ⟨actualRecoveryState, actualRecoveryTape⟩
  simp only at hactualRecoveryState hrecoveryActual hrecoveryTape
  subst actualRecoveryState
  have hrecoveryOuter := recovery_computes_lift
    (selected := selected) hrecoveryActual
  have hrecoveryOuter' : TuringMachine.Computes (machine selected)
      { state := .recovery ProductHandoff.machine.start,
        tape := CyclicDriverIntegration.roundTripTape actualMissTape }
      { state := .recovery ProductHandoff.machine.halt,
        tape := actualRecoveryTape } := by
    simpa [ProductHandoff.machine,
      TuringMachine.PhaseEmbedding.liftConfig] using hrecoveryOuter
  have hrecoveryBounce := computes_of_run_exact
    (recovery_bounce_run_exact selected actualRecoveryTape)
  let dispatchTape := CyclicDriverIntegration.roundTripTape actualRecoveryTape
  refine ⟨dispatchTape, ?_, ?_⟩
  · exact TuringMachine.computes_trans hthroughMiss
      (TuringMachine.computes_trans hrecoveryOuter' hrecoveryBounce)
  · exact Tape.Equiv.trans (Tape.Equiv.symm hcaller)
      (Tape.Equiv.trans hrecoveryTape
        (Tape.Equiv.symm
          (roundTripTape_equiv_self actualRecoveryTape)))

theorem dispatch_advances_normalized
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) (dispatchTape : Tape MachineCodeSymbol)
    (hvalid : frame.cursor.Valid frame.geometry)
    (hdispatch : Tape.Equiv
      (Tape.input (Scheduler.SplitLayout.encode frame)) dispatchTape) :
    exists nextTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine selected)
        { state := .dispatch Scheduler.Dispatch.machine.start,
          tape := dispatchTape }
        { state := .duplicate ProductDuplicator.machine.start,
          tape := nextTape } ∧
      Tape.normalizedOutput nextTape =
        Scheduler.SplitLayout.encode frame.advance ∧
      Scheduler.SplitLayout.decode
          (Tape.normalizedOutput nextTape) = some frame.advance ∧
      Tape.Equiv
        (Tape.input (Scheduler.SplitLayout.encode frame.advance))
        nextTape := by
  rcases frame with ⟨geometry, cursor, input⟩
  rcases cursor with ⟨round, inner, outer, selectedFuel⟩
  rcases Scheduler.Dispatch.run_advance geometry round inner outer
      selectedFuel input hvalid with
    ⟨canonicalFinalTape, hcanonical, hcanonicalOutput, hcanonicalDecode,
      hcanonicalTape⟩
  rcases computes_from_tape_equiv hcanonical hdispatch with
    ⟨actualDispatch, hdispatchActual, hdispatchState, hdispatchFinalTape⟩
  rcases actualDispatch with ⟨actualDispatchState, actualDispatchTape⟩
  simp only at hdispatchState hdispatchActual hdispatchFinalTape
  subst actualDispatchState
  have hdispatchOuter := dispatch_computes_lift
    (selected := selected) hdispatchActual
  have hdispatchOuter' : TuringMachine.Computes (machine selected)
      { state := .dispatch Scheduler.Dispatch.machine.start,
        tape := dispatchTape }
      { state := .dispatch Scheduler.Dispatch.machine.halt,
        tape := actualDispatchTape } := by
    simpa [TuringMachine.PhaseEmbedding.liftConfig] using hdispatchOuter
  have hdispatchBounce := computes_of_run_exact
    (dispatch_bounce_run_exact selected actualDispatchTape)
  let nextTape := CyclicDriverIntegration.roundTripTape actualDispatchTape
  have hfinalEquiv : Tape.Equiv canonicalFinalTape nextTape :=
    Tape.Equiv.trans hdispatchFinalTape
      (Tape.Equiv.symm (roundTripTape_equiv_self actualDispatchTape))
  refine ⟨nextTape,
    TuringMachine.computes_trans hdispatchOuter' hdispatchBounce,
    ?_, ?_, Tape.Equiv.trans hcanonicalTape hfinalEquiv⟩
  · exact (Tape.Equiv.normalizedOutput_eq hfinalEquiv).symm.trans
      hcanonicalOutput
  · rw [← Tape.Equiv.normalizedOutput_eq hfinalEquiv]
    simpa [Scheduler.Dispatch.frame] using hcanonicalDecode

theorem nonexact_candidate_advances_normalized
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) (sourceTape : Tape MachineCodeSymbol)
    (hvalid : frame.cursor.Valid frame.geometry)
    (hsource : Tape.Equiv
      (Tape.input (Scheduler.SplitLayout.encode frame)) sourceTape)
    (hnot : ¬ TuringMachine.HaltsOnInputIn selected
      frame.cursor.selectedFuel
      (GeneratedCode.nestedStageCode frame.input
        frame.cursor.inner frame.cursor.outer)) :
    exists nextTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine selected)
        { state := (machine selected).start, tape := sourceTape }
        { state := (machine selected).start, tape := nextTape } ∧
      Tape.normalizedOutput nextTape =
        Scheduler.SplitLayout.encode frame.advance ∧
      Scheduler.SplitLayout.decode
          (Tape.normalizedOutput nextTape) = some frame.advance ∧
      Tape.Equiv
        (Tape.input (Scheduler.SplitLayout.encode frame.advance))
        nextTape := by
  rcases nonexact_candidate_reaches_dispatch selected frame sourceTape
      hsource hnot with ⟨dispatchTape, hprefix, hdispatch⟩
  rcases dispatch_advances_normalized selected frame dispatchTape hvalid
      hdispatch with ⟨nextTape, hdispatchRun, houtput, hdecode, hequiv⟩
  refine ⟨nextTape, ?_, houtput, hdecode, hequiv⟩
  simpa [machine] using TuringMachine.computes_trans hprefix hdispatchRun

def Represents
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame)
    (config : TuringMachine.Configuration MachineCodeSymbol
      (Control selected)) : Prop :=
  frame.cursor.Valid frame.geometry ∧
    config.state = (machine selected).start ∧
    Tape.Equiv
      (Tape.input (Scheduler.SplitLayout.encode frame)) config.tape

theorem start_represents
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame)
    (hvalid : frame.cursor.Valid frame.geometry) :
    Represents selected frame
      { state := (machine selected).start
        tape := Tape.input (Scheduler.SplitLayout.encode frame) } := by
  exact ⟨hvalid, rfl, Tape.Equiv.refl _⟩

theorem success_haltsFrom
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame)
    (config : TuringMachine.Configuration MachineCodeSymbol
      (Control selected))
    (hrep : Represents selected frame config)
    (hsuccess : Scheduler.Reachability.CandidateSucceeds selected frame) :
    TuringMachine.HaltsFrom (machine selected) config := by
  rcases hrep with ⟨_hvalid, hstate, htape⟩
  rcases config with ⟨state, tape⟩
  simp only at hstate htape ⊢
  subst state
  rcases exact_candidate_reaches_public_halt selected frame tape htape
      hsuccess with ⟨finalTape, hrun⟩
  exact TuringMachine.halts_from_of_computes hrun rfl

theorem failure_advances
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame)
    (config : TuringMachine.Configuration MachineCodeSymbol
      (Control selected))
    (hrep : Represents selected frame config)
    (hfailure :
      ¬ Scheduler.Reachability.CandidateSucceeds selected frame) :
    exists steps : Nat,
    exists nextConfig : TuringMachine.Configuration MachineCodeSymbol
      (Control selected),
      0 < steps ∧
        TuringMachine.ComputesIn (machine selected) steps config nextConfig ∧
        Represents selected frame.advance nextConfig := by
  rcases hrep with ⟨hvalid, hstate, htape⟩
  rcases config with ⟨state, tape⟩
  simp only at hstate htape ⊢
  subst state
  rcases nonexact_candidate_reaches_dispatch selected frame tape htape
      hfailure with ⟨dispatchTape, hprefix, hdispatch⟩
  rcases dispatch_advances_normalized selected frame dispatchTape hvalid
      hdispatch with
    ⟨nextTape, hdispatchRun, _houtput, _hdecode, hnextTape⟩
  rcases TuringMachine.computes_to_computesIn hprefix with
    ⟨prefixSteps, hprefixIn⟩
  rcases TuringMachine.computes_to_computesIn hdispatchRun with
    ⟨dispatchSteps, hdispatchIn⟩
  have hprefixPositive : 0 < prefixSteps := by
    cases prefixSteps with
    | zero =>
        have hsame := TuringMachine.computesIn_zero_eq hprefixIn
        have hstates := congrArg
          (fun c : TuringMachine.Configuration MachineCodeSymbol
            (Control selected) => c.state) hsame
        simp [machine] at hstates
    | succ steps =>
        exact Nat.zero_lt_succ steps
  let nextConfig : TuringMachine.Configuration MachineCodeSymbol
      (Control selected) :=
    { state := (machine selected).start, tape := nextTape }
  refine ⟨prefixSteps + dispatchSteps, nextConfig, ?_, ?_, ?_⟩
  · exact Nat.lt_of_lt_of_le hprefixPositive
      (Nat.le_add_right prefixSteps dispatchSteps)
  · have hrun := TuringMachine.computesIn_trans hprefixIn hdispatchIn
    simpa [nextConfig, machine] using hrun
  · exact
      ⟨Scheduler.Layout.Cursor.advance_valid hvalid, rfl, hnextTape⟩

theorem transition_to_public_halt_inversion
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (source : Control selected) (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (htransition : transition selected source read =
      some (write, direction, Control.halt)) :
    source = Control.probeHitReturn ∧
      write = read ∧ direction = Direction.left := by
  cases source <;>
    simp only [transition] at htransition
  all_goals
    repeat
      first
      | split at htransition
      | simp_all [mapAction]

theorem step_to_public_halt_inversion
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (Control selected)}
    (hstep : TuringMachine.Step (machine selected) source target)
    (htarget : target.state = (machine selected).halt) :
    source.state = Control.probeHitReturn := by
  cases hstep
  rename_i write direction nextState haction
  change nextState = Control.halt at htarget
  subst nextState
  rcases transition_to_public_halt_inversion selected source.state
      (Tape.read source.tape) write direction (by
        simpa [machine] using haction) with
    ⟨hsource, _hwrite, _hdirection⟩
  exact hsource

theorem halted_iff_public_halt_state
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (config : TuringMachine.Configuration MachineCodeSymbol
      (Control selected)) :
    TuringMachine.Halted (machine selected) config ↔
      config.state = Control.halt := by
  rfl

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Cycle
