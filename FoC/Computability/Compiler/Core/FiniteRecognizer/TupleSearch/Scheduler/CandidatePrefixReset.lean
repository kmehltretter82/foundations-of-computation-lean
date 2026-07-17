import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.CandidateGrow

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.CandidatePrefixReset

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Scheduler.CandidateReset

def word (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round fuelUsed fuelRemaining
    outerUsed outerRemaining innerUsed innerRemaining candidateFuel
    candidateOuter candidateInner input

def mainPrefixRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining : Nat) : Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.candidatePrefixRev geometry round
    fuelUsed fuelRemaining outerUsed outerRemaining innerUsed innerRemaining

def candidateSuffix (candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend candidateFuel
    (MachineDescription.encodeNatAppend candidateOuter
      (MachineDescription.encodeNatAppend candidateInner input))

theorem nestedStageCode_eq_tail (outer inner : Nat)
    (input : Word MachineCodeSymbol) :
    GeneratedCode.nestedStageCode input inner outer =
      MachineDescription.encodeNatAppend outer
        (MachineDescription.encodeNatAppend inner input) := by
  rfl

theorem word_fuel_decomp
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    word geometry round fuelUsed fuelRemaining outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input =
      List.append
        (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining).reverse
        (candidateSuffix candidateFuel candidateOuter candidateInner input) := by
  cases geometry <;>
    simp [word, mainPrefixRev, candidateSuffix,
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
      nestedStageCode_eq_tail, List.reverse_append, List.append_assoc]

theorem word_outer_decomp
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    word geometry round fuelUsed fuelRemaining outerUsed outerRemaining
        innerUsed innerRemaining 0 candidateOuter candidateInner input =
      List.append
        (Scheduler.Rollover.Locator.natPrefixRev 0
          (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining)).reverse
        (MachineDescription.encodeNatAppend candidateOuter
          (MachineDescription.encodeNatAppend candidateInner input)) := by
  rw [word_fuel_decomp]
  simp [candidateSuffix, Scheduler.Rollover.Locator.natPrefixRev,
    Scheduler.Advance.ExhaustedSplitReset.ticks,
    MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
    List.append_assoc]

def fuelConfig (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Scheduler.CandidateReset.Control :=
  Scheduler.CandidateReset.locateConfig .fuel
    (Scheduler.Rollover.Locator.config .halt
      (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining)
      (candidateSuffix candidateFuel candidateOuter candidateInner input))

def outerConfig (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Scheduler.CandidateReset.Control :=
  Scheduler.CandidateReset.locateConfig .outer
    (Scheduler.Rollover.Locator.config .halt
      (Scheduler.Rollover.Locator.natPrefixRev 0
        (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining))
      (MachineDescription.encodeNatAppend candidateOuter
        (MachineDescription.encodeNatAppend candidateInner input)))

def innerConfig (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Scheduler.CandidateReset.Control :=
  Scheduler.CandidateReset.locateConfig .inner
    (Scheduler.Rollover.Locator.config .halt
      (Scheduler.Rollover.Locator.natPrefixRev 0
        (Scheduler.Rollover.Locator.natPrefixRev 0
          (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining)))
      (MachineDescription.encodeNatAppend candidateInner input))

theorem fuel_zero_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.CandidateReset.machine.runConfigExact? 1
        (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining 0 candidateOuter
          candidateInner input) =
      some (outerConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateOuter candidateInner
        input) := by
  change Scheduler.CandidateReset.machine.runConfigExact? 1
    (Scheduler.CandidateReset.locateConfig .fuel
      (Scheduler.Rollover.Locator.config .halt
        (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining)
        (MachineCodeSymbol.done ::
          MachineDescription.encodeNatAppend candidateOuter
            (MachineDescription.encodeNatAppend candidateInner input)))) = _
  rw [TuringMachine.runConfigExact?]
  rw [Scheduler.CandidateReset.fuel_done_step]
  rfl

theorem outer_zero_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.CandidateReset.machine.runConfigExact? 1
        (outerConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining 0 candidateInner input) =
      some (innerConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateInner input) := by
  change Scheduler.CandidateReset.machine.runConfigExact? 1
    (Scheduler.CandidateReset.locateConfig .outer
      (Scheduler.Rollover.Locator.config .halt
        (MachineCodeSymbol.done ::
          mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining)
        (MachineCodeSymbol.done ::
          MachineDescription.encodeNatAppend candidateInner input))) = _
  rw [TuringMachine.runConfigExact?]
  rw [Scheduler.CandidateReset.outer_done_step]
  rfl

theorem fuel_delete_succ_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Scheduler.CandidateReset.machine.runConfigExact?
        (Scheduler.CandidateReset.deleteLoopSteps
          (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining)
          (candidateSuffix candidateFuel candidateOuter candidateInner input))
        (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining (candidateFuel + 1)
          candidateOuter candidateInner input) =
      some (Scheduler.CandidateReset.gateLocateConfig .fuel
        (word geometry round fuelUsed fuelRemaining outerUsed outerRemaining
          innerUsed innerRemaining candidateFuel candidateOuter candidateInner
          input)) := by
  change Scheduler.CandidateReset.machine.runConfigExact?
      (Scheduler.CandidateReset.deleteLoopSteps
        (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining)
        (candidateSuffix candidateFuel candidateOuter candidateInner input))
      (Scheduler.CandidateReset.locateConfig .fuel
        (Scheduler.Rollover.Locator.config .halt
          (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining)
          (MachineCodeSymbol.tick ::
            candidateSuffix candidateFuel candidateOuter candidateInner
              input))) = _
  rw [Scheduler.CandidateReset.delete_loop_exact]
  rw [word_fuel_decomp]
  rfl

theorem outer_delete_succ_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.CandidateReset.machine.runConfigExact?
        (Scheduler.CandidateReset.deleteLoopSteps
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining))
          (MachineDescription.encodeNatAppend candidateOuter
            (MachineDescription.encodeNatAppend candidateInner input)))
        (outerConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining (candidateOuter + 1)
          candidateInner input) =
      some (Scheduler.CandidateReset.gateLocateConfig .outer
        (word geometry round fuelUsed fuelRemaining outerUsed outerRemaining
          innerUsed innerRemaining 0 candidateOuter candidateInner input)) := by
  change Scheduler.CandidateReset.machine.runConfigExact? _
      (Scheduler.CandidateReset.locateConfig .outer
        (Scheduler.Rollover.Locator.config .halt
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining))
          (MachineCodeSymbol.tick ::
            MachineDescription.encodeNatAppend candidateOuter
              (MachineDescription.encodeNatAppend candidateInner input)))) = _
  rw [Scheduler.CandidateReset.delete_loop_exact]
  rw [word_outer_decomp]
  rfl

theorem locate_fuel_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Scheduler.CandidateReset.machine.runConfigExact?
        (Scheduler.Rollover.Locator.toCandidateMarkerSteps geometry
          round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
          innerRemaining + 1)
        (Scheduler.CandidateReset.locateConfig .fuel
          (Scheduler.Rollover.Locator.config .header []
            (word geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining candidateFuel
              candidateOuter candidateInner input))) =
      some (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input) := by
  simpa [word, fuelConfig, mainPrefixRev, candidateSuffix,
    Scheduler.Rollover.word, nestedStageCode_eq_tail]
    using Scheduler.CandidateReset.locate_run_of_eq_some .fuel
      (Scheduler.Rollover.Locator.locate_candidateFuel_exact geometry
        round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
        innerRemaining
        (candidateSuffix candidateFuel candidateOuter candidateInner input))

theorem locate_outer_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.CandidateReset.machine.runConfigExact?
        (Scheduler.Rollover.Locator.locateCandidateOuterSteps geometry
          round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
          innerRemaining 0)
        (Scheduler.CandidateReset.locateConfig .outer
          (Scheduler.Rollover.Locator.config .header []
            (word geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining 0 candidateOuter
              candidateInner input))) =
      some (outerConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateOuter candidateInner
        input) := by
  simpa [word, outerConfig, mainPrefixRev,
    Scheduler.Rollover.word, nestedStageCode_eq_tail]
    using Scheduler.CandidateReset.locate_run_of_eq_some .outer
      (Scheduler.Rollover.Locator.locate_candidateOuter_exact geometry
        round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
        innerRemaining 0
        (MachineDescription.encodeNatAppend candidateOuter
          (MachineDescription.encodeNatAppend candidateInner input)))

theorem reset_fuel_only
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input).tape tape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Scheduler.CandidateReset.machine
        (Scheduler.CandidateReset.withTape
          (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input) tape)
        (Scheduler.CandidateReset.withTape
          (outerConfig geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateOuter
            candidateInner input) targetTape) ∧
      Tape.Equiv
        (outerConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateOuter candidateInner
          input).tape targetTape := by
  induction candidateFuel generalizing tape with
  | zero =>
      exact Scheduler.CandidateReset.computes_exact_from_equiv
        (fuel_zero_exact geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateOuter
          candidateInner input) htape
  | succ candidateFuel ih =>
      let nextWord := word geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input
      rcases Scheduler.CandidateReset.computes_exact_from_equiv
          (fuel_delete_succ_exact geometry round fuelUsed fuelRemaining
            outerUsed outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input) htape with
        ⟨gateTape, hdelete, hgate⟩
      have hinputGate : Tape.Equiv (Tape.input nextWord) gateTape :=
        Tape.Equiv.trans
          (Tape.Equiv.symm
            (Scheduler.CandidateReset.gateLocate_tape_equiv_input
              .fuel nextWord)) hgate
      rcases Scheduler.CandidateReset.computes_exact_from_equiv
          (locate_fuel_exact geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input) hinputGate with
        ⟨fuelTape, hlocate, hfuel⟩
      rcases ih fuelTape hfuel with ⟨targetTape, htail, htarget⟩
      exact ⟨targetTape,
        TuringMachine.computes_trans hdelete
          (TuringMachine.computes_trans hlocate htail), htarget⟩

theorem reset_outer_only
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (outerConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateOuter candidateInner
        input).tape tape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Scheduler.CandidateReset.machine
        (Scheduler.CandidateReset.withTape
          (outerConfig geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateOuter
            candidateInner input) tape)
        (Scheduler.CandidateReset.withTape
          (innerConfig geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateInner input)
          targetTape) ∧
      Tape.Equiv
        (innerConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateInner input).tape
        targetTape := by
  induction candidateOuter generalizing tape with
  | zero =>
      exact Scheduler.CandidateReset.computes_exact_from_equiv
        (outer_zero_exact geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateInner input) htape
  | succ candidateOuter ih =>
      let nextWord := word geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining 0 candidateOuter
        candidateInner input
      rcases Scheduler.CandidateReset.computes_exact_from_equiv
          (outer_delete_succ_exact geometry round fuelUsed fuelRemaining
            outerUsed outerRemaining innerUsed innerRemaining candidateOuter
            candidateInner input) htape with
        ⟨gateTape, hdelete, hgate⟩
      have hinputGate : Tape.Equiv (Tape.input nextWord) gateTape :=
        Tape.Equiv.trans
          (Tape.Equiv.symm
            (Scheduler.CandidateReset.gateLocate_tape_equiv_input
              .outer nextWord)) hgate
      rcases Scheduler.CandidateReset.computes_exact_from_equiv
          (locate_outer_exact geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateOuter
            candidateInner input) hinputGate with
        ⟨outerTape, hlocate, houter⟩
      rcases ih outerTape houter with ⟨targetTape, htail, htarget⟩
      exact ⟨targetTape,
        TuringMachine.computes_trans hdelete
          (TuringMachine.computes_trans hlocate htail), htarget⟩

namespace PrefixMachine

inductive Stop where
  | fuel
  | outer
deriving DecidableEq

def stopControl : Stop -> Scheduler.CandidateReset.Control
  | .fuel => .locate .outer .halt
  | .outer => .locate .inner .halt

def transition (stop : Stop) :
    Scheduler.CandidateReset.Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction ×
        Scheduler.CandidateReset.Control) :=
  fun state read =>
    if state = stopControl stop then none
    else Scheduler.CandidateReset.transition state read

def machine (stop : Stop) : TuringMachine MachineCodeSymbol
    Scheduler.CandidateReset.Control where
  start := Scheduler.CandidateReset.machine.start
  halt := stopControl stop
  transition := transition stop
  statesFinite := Scheduler.CandidateReset.Control.finite

theorem locate_step_of_some (stop : Stop)
    (field : Scheduler.CandidateReset.Field)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Scheduler.Rollover.Locator.Control)
    (hstep : (Scheduler.Rollover.Locator.machine field.target).stepConfig
      source = some target) :
    (machine stop).stepConfig
        (Scheduler.CandidateReset.locateConfig field source) =
      some (Scheduler.CandidateReset.locateConfig field target) := by
  cases source with
  | mk state tape =>
      cases target with
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
              cases stop <;> cases field <;> cases state <;>
                simp_all [machine, transition, stopControl,
                  Scheduler.CandidateReset.locateConfig,
                  Scheduler.CandidateReset.transition,
                  Scheduler.CandidateReset.mapAction,
                  TuringMachine.PhaseEmbedding.liftConfig,
                  Scheduler.Rollover.Locator.transition]

theorem delete_step_of_some (stop : Stop)
    (field : Scheduler.CandidateReset.Field)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control)
    (hstep : (DeleteRestagedMachine.machine none).stepConfig source =
      some target) :
    (machine stop).stepConfig
        (Scheduler.CandidateReset.deleteConfig field source) =
      some (Scheduler.CandidateReset.deleteConfig field target) := by
  cases source with
  | mk state tape =>
      cases target with
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
              cases stop <;> cases field <;> cases state with
              | edit inner =>
                  cases inner <;>
                    simp_all [machine, transition, stopControl,
                      Scheduler.CandidateReset.deleteConfig,
                      Scheduler.CandidateReset.transition,
                      Scheduler.CandidateReset.mapAction,
                      TuringMachine.PhaseEmbedding.liftConfig]
              | rewind inner =>
                  cases inner <;>
                    simp_all [machine, transition, stopControl,
                      Scheduler.CandidateReset.deleteConfig,
                      Scheduler.CandidateReset.transition,
                      Scheduler.CandidateReset.mapAction,
                      TuringMachine.PhaseEmbedding.liftConfig,
                      DeleteRestagedMachine.transition,
                      DeleteEndpointRewind.transition]

theorem locate_run_of_eq_some (stop : Stop)
    (field : Scheduler.CandidateReset.Field) {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Scheduler.Rollover.Locator.Control}
    (hrun : (Scheduler.Rollover.Locator.machine field.target).runConfigExact?
      steps source = some target) :
    (machine stop).runConfigExact? steps
        (Scheduler.CandidateReset.locateConfig field source) =
      some (Scheduler.CandidateReset.locateConfig field target) := by
  exact TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    (Scheduler.CandidateReset.Control.locate field)
    (locate_step_of_some stop field) hrun

theorem delete_run_of_eq_some (stop : Stop)
    (field : Scheduler.CandidateReset.Field) {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control}
    (hrun : (DeleteRestagedMachine.machine none).runConfigExact? steps source =
      some target) :
    (machine stop).runConfigExact? steps
        (Scheduler.CandidateReset.deleteConfig field source) =
      some (Scheduler.CandidateReset.deleteConfig field target) := by
  exact TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    (Scheduler.CandidateReset.Control.delete field)
    (delete_step_of_some stop field) hrun

theorem bounce_exact (stop : Stop)
    (field : Scheduler.CandidateReset.Field)
    (currentWord : Word MachineCodeSymbol) :
    (machine stop).runConfigExact? 2
        (Scheduler.CandidateReset.deleteConfig field
          (DeleteRestagedMachine.rewindConfig
            (DeleteEndpointRewind.gateConfig currentWord none))) =
      some (Scheduler.CandidateReset.gateLocateConfig field
        currentWord) := by
  cases stop <;> cases field <;> cases currentWord <;> rfl

def CanDelete : Stop -> Scheduler.CandidateReset.Field -> Prop
  | .fuel, .fuel => True
  | .outer, .fuel => True
  | .outer, .outer => True
  | _, _ => False

theorem enter_delete_tick_step (stop : Stop)
    (field : Scheduler.CandidateReset.Field)
    (hcan : CanDelete stop field)
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine stop).stepConfig
        (Scheduler.CandidateReset.locateConfig field
          (Scheduler.Rollover.Locator.config .halt leftRev
            (MachineCodeSymbol.tick :: suffix))) =
      some (Scheduler.CandidateReset.deleteConfig field
        (DeleteRestagedMachine.editConfig
          (DeleteBlock.pullConfig (DeleteBlock.optionalGap none)
            leftRev suffix))) := by
  cases stop <;> cases field <;> simp_all [CanDelete] <;>
    cases leftRev <;> cases suffix <;> rfl

theorem delete_loop_exact (stop : Stop)
    (field : Scheduler.CandidateReset.Field)
    (hcan : CanDelete stop field)
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine stop).runConfigExact?
        (Scheduler.CandidateReset.deleteLoopSteps leftRev suffix)
        (Scheduler.CandidateReset.locateConfig field
          (Scheduler.Rollover.Locator.config .halt leftRev
            (MachineCodeSymbol.tick :: suffix))) =
      some (Scheduler.CandidateReset.gateLocateConfig field
        (PhysicalBranch.deleteOutput leftRev suffix)) := by
  unfold Scheduler.CandidateReset.deleteLoopSteps
  rw [show 1 + Scheduler.CandidateReset.deleteTickTailSteps
      leftRev suffix + 2 =
      1 + (Scheduler.CandidateReset.deleteTickTailSteps
        leftRev suffix + 2) by lia]
  rw [InitialMaterializer.ExactRun.append (machine stop) 1
    (Scheduler.CandidateReset.deleteTickTailSteps leftRev suffix + 2)]
  rw [TuringMachine.runConfigExact?, enter_delete_tick_step stop field hcan]
  change (machine stop).runConfigExact?
    (Scheduler.CandidateReset.deleteTickTailSteps leftRev suffix + 2)
    (Scheduler.CandidateReset.deleteConfig field
      (DeleteRestagedMachine.editConfig
        (DeleteBlock.pullConfig (DeleteBlock.optionalGap none)
          leftRev suffix))) = _
  rw [InitialMaterializer.ExactRun.append (machine stop)
    (Scheduler.CandidateReset.deleteTickTailSteps leftRev suffix) 2]
  rw [delete_run_of_eq_some stop field
    (Scheduler.CandidateReset.delete_tick_tail_exact leftRev suffix)]
  simp only
  rw [bounce_exact]

theorem fuel_done_step (stop : Stop)
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine stop).stepConfig
        (Scheduler.CandidateReset.locateConfig .fuel
          (Scheduler.Rollover.Locator.config .halt leftRev
            (MachineCodeSymbol.done :: suffix))) =
      some (Scheduler.CandidateReset.locateConfig .outer
        (Scheduler.Rollover.Locator.config .halt
          (MachineCodeSymbol.done :: leftRev) suffix)) := by
  cases stop <;> cases leftRev <;> cases suffix <;> rfl

theorem outer_done_step (leftRev suffix : Word MachineCodeSymbol) :
    (machine .outer).stepConfig
        (Scheduler.CandidateReset.locateConfig .outer
          (Scheduler.Rollover.Locator.config .halt leftRev
            (MachineCodeSymbol.done :: suffix))) =
      some (Scheduler.CandidateReset.locateConfig .inner
        (Scheduler.Rollover.Locator.config .halt
          (MachineCodeSymbol.done :: leftRev) suffix)) := by
  cases leftRev <;> cases suffix <;> rfl

theorem fuel_zero_exact_prefix (stop : Stop)
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    (machine stop).runConfigExact? 1
        (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining 0 candidateOuter
          candidateInner input) =
      some (outerConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateOuter candidateInner
        input) := by
  rw [TuringMachine.runConfigExact?]
  rw [show (machine stop).stepConfig
      (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining 0 candidateOuter
        candidateInner input) =
    some (outerConfig geometry round fuelUsed fuelRemaining outerUsed
      outerRemaining innerUsed innerRemaining candidateOuter candidateInner
      input) by
        change (machine stop).stepConfig
          (Scheduler.CandidateReset.locateConfig .fuel
            (Scheduler.Rollover.Locator.config .halt
              (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
                outerRemaining innerUsed innerRemaining)
              (MachineCodeSymbol.done ::
                MachineDescription.encodeNatAppend candidateOuter
                  (MachineDescription.encodeNatAppend candidateInner
                    input)))) = _
        exact fuel_done_step stop _ _]
  rfl

theorem outer_zero_exact_prefix
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    (machine .outer).runConfigExact? 1
        (outerConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining 0 candidateInner input) =
      some (innerConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateInner input) := by
  rw [TuringMachine.runConfigExact?]
  rw [show (machine .outer).stepConfig
      (outerConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining 0 candidateInner input) =
    some (innerConfig geometry round fuelUsed fuelRemaining outerUsed
      outerRemaining innerUsed innerRemaining candidateInner input) by
        change (machine .outer).stepConfig
          (Scheduler.CandidateReset.locateConfig .outer
            (Scheduler.Rollover.Locator.config .halt
              (MachineCodeSymbol.done ::
                mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
                  outerRemaining innerUsed innerRemaining)
              (MachineCodeSymbol.done ::
                MachineDescription.encodeNatAppend candidateInner input))) = _
        exact outer_done_step _ _]
  rfl

theorem fuel_delete_succ_exact_prefix (stop : Stop)
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    (machine stop).runConfigExact?
        (Scheduler.CandidateReset.deleteLoopSteps
          (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining)
          (candidateSuffix candidateFuel candidateOuter candidateInner input))
        (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining (candidateFuel + 1)
          candidateOuter candidateInner input) =
      some (Scheduler.CandidateReset.gateLocateConfig .fuel
        (word geometry round fuelUsed fuelRemaining outerUsed outerRemaining
          innerUsed innerRemaining candidateFuel candidateOuter candidateInner
          input)) := by
  change (machine stop).runConfigExact? _
      (Scheduler.CandidateReset.locateConfig .fuel
        (Scheduler.Rollover.Locator.config .halt
          (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining)
          (MachineCodeSymbol.tick ::
            candidateSuffix candidateFuel candidateOuter candidateInner
              input))) = _
  rw [delete_loop_exact stop .fuel (by cases stop <;> trivial)]
  rw [word_fuel_decomp]
  rfl

theorem outer_delete_succ_exact_prefix
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    (machine .outer).runConfigExact?
        (Scheduler.CandidateReset.deleteLoopSteps
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining))
          (MachineDescription.encodeNatAppend candidateOuter
            (MachineDescription.encodeNatAppend candidateInner input)))
        (outerConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining (candidateOuter + 1)
          candidateInner input) =
      some (Scheduler.CandidateReset.gateLocateConfig .outer
        (word geometry round fuelUsed fuelRemaining outerUsed outerRemaining
          innerUsed innerRemaining 0 candidateOuter candidateInner input)) := by
  change (machine .outer).runConfigExact? _
      (Scheduler.CandidateReset.locateConfig .outer
        (Scheduler.Rollover.Locator.config .halt
          (Scheduler.Rollover.Locator.natPrefixRev 0
            (mainPrefixRev geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining))
          (MachineCodeSymbol.tick ::
            MachineDescription.encodeNatAppend candidateOuter
              (MachineDescription.encodeNatAppend candidateInner input)))) = _
  rw [delete_loop_exact .outer .outer (by simp [CanDelete])]
  rw [word_outer_decomp]
  rfl

theorem locate_fuel_exact_prefix (stop : Stop)
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    (machine stop).runConfigExact?
        (Scheduler.Rollover.Locator.toCandidateMarkerSteps geometry
          round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
          innerRemaining + 1)
        (Scheduler.CandidateReset.locateConfig .fuel
          (Scheduler.Rollover.Locator.config .header []
            (word geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining candidateFuel
              candidateOuter candidateInner input))) =
      some (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input) := by
  simpa [word, fuelConfig, mainPrefixRev, candidateSuffix,
    Scheduler.Rollover.word, nestedStageCode_eq_tail]
    using locate_run_of_eq_some stop .fuel
      (Scheduler.Rollover.Locator.locate_candidateFuel_exact geometry
        round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
        innerRemaining
        (candidateSuffix candidateFuel candidateOuter candidateInner input))

theorem locate_outer_exact_prefix
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    (machine .outer).runConfigExact?
        (Scheduler.Rollover.Locator.locateCandidateOuterSteps geometry
          round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
          innerRemaining 0)
        (Scheduler.CandidateReset.locateConfig .outer
          (Scheduler.Rollover.Locator.config .header []
            (word geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining 0 candidateOuter
              candidateInner input))) =
      some (outerConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateOuter candidateInner
        input) := by
  simpa [word, outerConfig, mainPrefixRev,
    Scheduler.Rollover.word, nestedStageCode_eq_tail]
    using locate_run_of_eq_some .outer .outer
      (Scheduler.Rollover.Locator.locate_candidateOuter_exact geometry
        round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
        innerRemaining 0
        (MachineDescription.encodeNatAppend candidateOuter
          (MachineDescription.encodeNatAppend candidateInner input)))

def withTape (c : TuringMachine.Configuration MachineCodeSymbol
    Scheduler.CandidateReset.Control) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Scheduler.CandidateReset.Control :=
  { state := c.state, tape := tape }

theorem computes_exact_from_equiv (stop : Stop) {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Scheduler.CandidateReset.Control}
    {tape : Tape MachineCodeSymbol}
    (hrun : (machine stop).runConfigExact? steps source = some target)
    (htape : Tape.Equiv source.tape tape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine stop) (withTape source tape)
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

theorem reset_fuel_prefix (stop : Stop)
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input).tape tape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine stop)
        (withTape
          (fuelConfig geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input) tape)
        (withTape
          (outerConfig geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateOuter
            candidateInner input) targetTape) ∧
      Tape.Equiv
        (outerConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateOuter candidateInner
          input).tape targetTape := by
  induction candidateFuel generalizing tape with
  | zero =>
      exact computes_exact_from_equiv stop
        (fuel_zero_exact_prefix stop geometry round fuelUsed fuelRemaining
          outerUsed outerRemaining innerUsed innerRemaining candidateOuter
          candidateInner input) htape
  | succ candidateFuel ih =>
      let nextWord := word geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input
      rcases computes_exact_from_equiv stop
          (fuel_delete_succ_exact_prefix stop geometry round fuelUsed
            fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
            candidateFuel candidateOuter candidateInner input) htape with
        ⟨gateTape, hdelete, hgate⟩
      have hinputGate : Tape.Equiv (Tape.input nextWord) gateTape :=
        Tape.Equiv.trans
          (Tape.Equiv.symm
            (Scheduler.CandidateReset.gateLocate_tape_equiv_input
              .fuel nextWord)) hgate
      rcases computes_exact_from_equiv stop
          (locate_fuel_exact_prefix stop geometry round fuelUsed fuelRemaining
            outerUsed outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input) hinputGate with
        ⟨fuelTape, hlocate, hfuel⟩
      rcases ih fuelTape hfuel with ⟨targetTape, htail, htarget⟩
      exact ⟨targetTape,
        TuringMachine.computes_trans hdelete
          (TuringMachine.computes_trans hlocate htail), htarget⟩

theorem reset_outer_prefix
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (outerConfig geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateOuter candidateInner
        input).tape tape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine .outer)
        (withTape
          (outerConfig geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateOuter
            candidateInner input) tape)
        (withTape
          (innerConfig geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateInner input)
          targetTape) ∧
      Tape.Equiv
        (innerConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateInner input).tape
        targetTape := by
  induction candidateOuter generalizing tape with
  | zero =>
      exact computes_exact_from_equiv .outer
        (outer_zero_exact_prefix geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateInner input) htape
  | succ candidateOuter ih =>
      let nextWord := word geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining 0 candidateOuter
        candidateInner input
      rcases computes_exact_from_equiv .outer
          (outer_delete_succ_exact_prefix geometry round fuelUsed
            fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
            candidateOuter candidateInner input) htape with
        ⟨gateTape, hdelete, hgate⟩
      have hinputGate : Tape.Equiv (Tape.input nextWord) gateTape :=
        Tape.Equiv.trans
          (Tape.Equiv.symm
            (Scheduler.CandidateReset.gateLocate_tape_equiv_input
              .outer nextWord)) hgate
      rcases computes_exact_from_equiv .outer
          (locate_outer_exact_prefix geometry round fuelUsed fuelRemaining
            outerUsed outerRemaining innerUsed innerRemaining candidateOuter
            candidateInner input) hinputGate with
        ⟨outerTape, hlocate, houter⟩
      rcases ih outerTape houter with ⟨targetTape, htail, htarget⟩
      exact ⟨targetTape,
        TuringMachine.computes_trans hdelete
          (TuringMachine.computes_trans hlocate htail), htarget⟩

theorem reset_fuel_from_input
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input
        (word geometry round fuelUsed fuelRemaining outerUsed outerRemaining
          innerUsed innerRemaining candidateFuel candidateOuter candidateInner
          input)) tape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine .fuel)
        { state := (machine .fuel).start, tape := tape }
        { state := (machine .fuel).halt, tape := targetTape } ∧
      Tape.Equiv
        (outerConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateOuter candidateInner
          input).tape targetTape := by
  rcases computes_exact_from_equiv .fuel
      (locate_fuel_exact_prefix .fuel geometry round fuelUsed fuelRemaining
        outerUsed outerRemaining innerUsed innerRemaining candidateFuel
        candidateOuter candidateInner input) htape with
    ⟨fuelTape, hlocate, hfuel⟩
  rcases reset_fuel_prefix .fuel geometry round fuelUsed fuelRemaining
      outerUsed outerRemaining innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner input fuelTape hfuel with
    ⟨targetTape, htail, htarget⟩
  exact ⟨targetTape, TuringMachine.computes_trans hlocate htail, htarget⟩

theorem reset_fuel_outer_from_input
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (Tape.input
        (word geometry round fuelUsed fuelRemaining outerUsed outerRemaining
          innerUsed innerRemaining candidateFuel candidateOuter candidateInner
          input)) tape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine .outer)
        { state := (machine .outer).start, tape := tape }
        { state := (machine .outer).halt, tape := targetTape } ∧
      Tape.Equiv
        (innerConfig geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateInner input).tape
        targetTape := by
  rcases computes_exact_from_equiv .outer
      (locate_fuel_exact_prefix .outer geometry round fuelUsed fuelRemaining
        outerUsed outerRemaining innerUsed innerRemaining candidateFuel
        candidateOuter candidateInner input) htape with
    ⟨fuelTape, hlocate, hfuel⟩
  rcases reset_fuel_prefix .outer geometry round fuelUsed fuelRemaining
      outerUsed outerRemaining innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner input fuelTape hfuel with
    ⟨outerTape, hfuelReset, houter⟩
  rcases reset_outer_prefix geometry round fuelUsed fuelRemaining outerUsed
      outerRemaining innerUsed innerRemaining candidateOuter candidateInner
      input outerTape houter with
    ⟨targetTape, houterReset, htarget⟩
  exact ⟨targetTape,
    TuringMachine.computes_trans hlocate
      (TuringMachine.computes_trans hfuelReset houterReset), htarget⟩

end PrefixMachine

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.CandidatePrefixReset
