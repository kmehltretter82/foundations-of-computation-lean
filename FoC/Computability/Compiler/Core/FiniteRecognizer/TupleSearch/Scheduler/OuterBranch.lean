import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.FuelBranch

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.OuterBranch

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

abbrev LocatorControl := Scheduler.Rollover.Locator.Control
abbrev SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.Control
abbrev SplitAdvanceControl := Scheduler.SplitAdvance.Control
abbrev CandidateResetControl := Scheduler.CandidateReset.Control
abbrev CandidateGrowControl := Scheduler.CandidateGrow.Control

def splitResetMachine :=
  Scheduler.Advance.ExhaustedSplitReset.machine

inductive Control where
  | locateFuel (inner : LocatorControl)
  | resetFuel (inner : SplitResetControl)
  | rewindFuel (inner : RewindWord.Control)
  | locateOuter (inner : LocatorControl)
  | splitOuter (inner : SplitAdvanceControl)
  | candidateReset (inner : CandidateResetControl)
  | candidateGrow (inner : CandidateGrowControl)
  | halt
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems :=
    Scheduler.Rollover.Locator.Control.finite.elems.map
        Control.locateFuel ++
      Scheduler.Advance.ExhaustedSplitReset.Control.finite.elems.map
        Control.resetFuel ++
      RewindWord.Control.finite.elems.map Control.rewindFuel ++
      Scheduler.Rollover.Locator.Control.finite.elems.map
        Control.locateOuter ++
      Scheduler.SplitAdvance.Control.finite.elems.map
        Control.splitOuter ++
      Scheduler.CandidateReset.Control.finite.elems.map
        Control.candidateReset ++
      Scheduler.CandidateGrow.Control.finite.elems.map
        Control.candidateGrow ++ [.halt]
  complete := by
    intro control
    cases control with
    | locateFuel inner =>
        simp
        exact Scheduler.Rollover.Locator.Control.finite.complete inner
    | resetFuel inner =>
        simp
        exact
          Scheduler.Advance.ExhaustedSplitReset.Control.finite.complete
            inner
    | rewindFuel inner =>
        simp
        exact RewindWord.Control.finite.complete inner
    | locateOuter inner =>
        simp
        exact Scheduler.Rollover.Locator.Control.finite.complete inner
    | splitOuter inner =>
        simp
        exact Scheduler.SplitAdvance.Control.finite.complete inner
    | candidateReset inner =>
        simp
        exact Scheduler.CandidateReset.Control.finite.complete inner
    | candidateGrow inner =>
        simp
        exact Scheduler.CandidateGrow.Control.finite.complete inner
    | halt => simp

end Control

def mapAction (embed : inner -> Control) :
    Option (Option MachineCodeSymbol × Direction × inner) ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | none => none
  | some (write, direction, target) =>
      some (write, direction, embed target)

def locateFuelEmbed : LocatorControl -> Control
  | .halt => .resetFuel splitResetMachine.start
  | inner => .locateFuel inner

def resetFuelEmbed : SplitResetControl -> Control
  | .halt => .rewindFuel RewindWord.machine.start
  | inner => .resetFuel inner

def rewindFuelEmbed : RewindWord.Control -> Control
  | .gate => .locateOuter .header
  | inner => .rewindFuel inner

def locateOuterEmbed : LocatorControl -> Control
  | .halt => .splitOuter Scheduler.SplitAdvance.machine.start
  | inner => .locateOuter inner

def splitOuterEmbed : SplitAdvanceControl -> Control
  | .rewind .gate =>
      .candidateReset
        (Scheduler.CandidatePrefixReset.PrefixMachine.machine
          .fuel).start
  | inner => .splitOuter inner

def candidateResetEmbed : CandidateResetControl -> Control
  | .locate .outer .halt =>
      .candidateGrow
        (.grow
          (InsertRestagedMachine.machine
            Scheduler.CandidateGrow.growBuffer).start)
  | inner => .candidateReset inner

def candidateGrowEmbed : CandidateGrowControl -> Control
  | .halt => .halt
  | inner => .candidateGrow inner

def transition : Control -> Option MachineCodeSymbol ->
    Option (Option MachineCodeSymbol × Direction × Control)
  | .locateFuel inner, read =>
      mapAction locateFuelEmbed
        (Scheduler.Rollover.Locator.transition .fuel inner read)
  | .resetFuel inner, read =>
      mapAction resetFuelEmbed
        (Scheduler.Advance.ExhaustedSplitReset.transition inner read)
  | .rewindFuel inner, read =>
      mapAction rewindFuelEmbed (RewindWord.transition inner read)
  | .locateOuter inner, read =>
      mapAction locateOuterEmbed
        (Scheduler.Rollover.Locator.transition .outer inner read)
  | .splitOuter inner, read =>
      mapAction splitOuterEmbed
        (Scheduler.SplitAdvance.transition inner read)
  | .candidateReset inner, read =>
      mapAction candidateResetEmbed
        ((Scheduler.CandidatePrefixReset.PrefixMachine.machine
          .fuel).transition inner read)
  | .candidateGrow inner, read =>
      mapAction candidateGrowEmbed
        ((Scheduler.CandidateGrow.machine .candidateOuter).transition
          inner read)
  | .halt, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .locateFuel .header
  halt := .halt
  transition := transition
  statesFinite := Control.finite

theorem step_of_mapped_transition
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hmap : ∀ (state : innerState) (read : Option MachineCodeSymbol)
        (action : Option MachineCodeSymbol × Direction × innerState),
      inner.transition state read = some action ->
      transition (embed state) read = mapAction embed (some action))
    (source target : TuringMachine.Configuration MachineCodeSymbol innerState)
    (hstep : inner.stepConfig source = some target) :
    machine.stepConfig
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

theorem locateFuel_map (state : LocatorControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × LocatorControl)
    (haction : (Scheduler.Rollover.Locator.machine .fuel).transition
      state read = some action) :
    transition (locateFuelEmbed state) read =
      mapAction locateFuelEmbed (some action) := by
  cases state <;>
    simp_all [Scheduler.Rollover.Locator.machine,
      Scheduler.Rollover.Locator.transition, transition,
      locateFuelEmbed, mapAction]

theorem resetFuel_map (state : SplitResetControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × SplitResetControl)
    (haction : splitResetMachine.transition state read = some action) :
    transition (resetFuelEmbed state) read =
      mapAction resetFuelEmbed (some action) := by
  cases state <;>
    simp_all [splitResetMachine,
      Scheduler.Advance.ExhaustedSplitReset.machine,
      Scheduler.Advance.ExhaustedSplitReset.transition,
      transition, resetFuelEmbed, mapAction]

theorem rewindFuel_map (state : RewindWord.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × RewindWord.Control)
    (haction : RewindWord.machine.transition state read = some action) :
    transition (rewindFuelEmbed state) read =
      mapAction rewindFuelEmbed (some action) := by
  cases state <;>
    simp_all [RewindWord.machine, RewindWord.transition,
      transition, rewindFuelEmbed, mapAction]

theorem locateOuter_map (state : LocatorControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × LocatorControl)
    (haction : (Scheduler.Rollover.Locator.machine .outer).transition
      state read = some action) :
    transition (locateOuterEmbed state) read =
      mapAction locateOuterEmbed (some action) := by
  cases state <;>
    simp_all [Scheduler.Rollover.Locator.machine,
      Scheduler.Rollover.Locator.transition, transition,
      locateOuterEmbed, mapAction]

theorem splitOuter_map (state : SplitAdvanceControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      SplitAdvanceControl)
    (haction : Scheduler.SplitAdvance.machine.transition state read =
      some action) :
    transition (splitOuterEmbed state) read =
      mapAction splitOuterEmbed (some action) := by
  cases state with
  | used =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitOuterEmbed,
        mapAction]
  | marker =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitOuterEmbed,
        mapAction]
  | takeRemaining =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitOuterEmbed,
        mapAction]
  | writeDone =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitOuterEmbed,
        mapAction]
  | writeTick =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitOuterEmbed,
        mapAction]
  | rewind inner =>
      cases inner <;>
        simp_all [Scheduler.SplitAdvance.machine,
          Scheduler.SplitAdvance.transition, RewindWord.transition,
          transition, splitOuterEmbed, mapAction,
          Scheduler.SplitAdvance.mapAction]

theorem candidateReset_map (state : CandidateResetControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      CandidateResetControl)
    (haction :
      (Scheduler.CandidatePrefixReset.PrefixMachine.machine
        .fuel).transition state read = some action) :
    transition (candidateResetEmbed state) read =
      mapAction candidateResetEmbed (some action) := by
  cases state with
  | locate field inner =>
      cases field <;> cases inner <;>
        simp_all [Scheduler.CandidatePrefixReset.PrefixMachine.machine,
          Scheduler.CandidatePrefixReset.PrefixMachine.transition,
          Scheduler.CandidatePrefixReset.PrefixMachine.stopControl,
          Scheduler.CandidateReset.transition,
          Scheduler.CandidateReset.mapAction,
          transition, candidateResetEmbed, mapAction]
  | delete field inner =>
      cases field <;> cases inner with
      | edit editInner =>
          cases editInner <;>
            simp_all [
              Scheduler.CandidatePrefixReset.PrefixMachine.machine,
              Scheduler.CandidatePrefixReset.PrefixMachine.transition,
              Scheduler.CandidatePrefixReset.PrefixMachine.stopControl,
              Scheduler.CandidateReset.transition,
              Scheduler.CandidateReset.mapAction,
              transition, candidateResetEmbed, mapAction]
      | rewind rewindInner =>
          cases rewindInner <;>
            simp_all [
              Scheduler.CandidatePrefixReset.PrefixMachine.machine,
              Scheduler.CandidatePrefixReset.PrefixMachine.transition,
              Scheduler.CandidatePrefixReset.PrefixMachine.stopControl,
              Scheduler.CandidateReset.transition,
              Scheduler.CandidateReset.mapAction,
              DeleteRestagedMachine.transition,
              DeleteEndpointRewind.transition,
              transition, candidateResetEmbed, mapAction]
  | bounceRight field =>
      cases field <;>
        simp_all [Scheduler.CandidatePrefixReset.PrefixMachine.machine,
          Scheduler.CandidatePrefixReset.PrefixMachine.transition,
          Scheduler.CandidatePrefixReset.PrefixMachine.stopControl,
          Scheduler.CandidateReset.transition,
          transition, candidateResetEmbed, mapAction]
  | halt =>
      simp_all [Scheduler.CandidatePrefixReset.PrefixMachine.machine,
        Scheduler.CandidatePrefixReset.PrefixMachine.transition,
        Scheduler.CandidatePrefixReset.PrefixMachine.stopControl,
        Scheduler.CandidateReset.transition]

theorem candidateGrow_map (state : CandidateGrowControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      CandidateGrowControl)
    (haction :
      (Scheduler.CandidateGrow.machine .candidateOuter).transition
        state read = some action) :
    transition (candidateGrowEmbed state) read =
      mapAction candidateGrowEmbed (some action) := by
  cases state with
  | locate inner =>
      cases inner <;>
        simp_all [Scheduler.CandidateGrow.machine,
          Scheduler.CandidateGrow.transition,
          Scheduler.CandidateGrow.mapAction,
          Scheduler.CandidateGrow.locateEmbed,
          Scheduler.Rollover.Locator.transition,
          transition, candidateGrowEmbed, mapAction]
  | grow inner =>
      cases inner with
      | edit editInner =>
          cases editInner <;>
            simp_all [Scheduler.CandidateGrow.machine,
              Scheduler.CandidateGrow.transition,
              Scheduler.CandidateGrow.mapAction,
              Scheduler.CandidateGrow.growEmbed,
              InsertRestagedMachine.transition,
              transition, candidateGrowEmbed, mapAction]
      | rewind rewindInner =>
          cases rewindInner <;>
            simp_all [Scheduler.CandidateGrow.machine,
              Scheduler.CandidateGrow.transition,
              Scheduler.CandidateGrow.mapAction,
              Scheduler.CandidateGrow.growEmbed,
              InsertRestagedMachine.transition, RewindWord.transition,
              transition, candidateGrowEmbed, mapAction]
  | halt =>
      simp_all [Scheduler.CandidateGrow.machine,
        Scheduler.CandidateGrow.transition]

theorem lift_computes
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hmap : ∀ (state : innerState) (read : Option MachineCodeSymbol)
        (action : Option MachineCodeSymbol × Direction × innerState),
      inner.transition state read = some action ->
      transition (embed state) read = mapAction embed (some action))
    {source target : TuringMachine.Configuration MachineCodeSymbol innerState}
    (hrun : TuringMachine.Computes inner source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig embed source)
      (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  rcases TuringMachine.computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    embed (step_of_mapped_transition inner embed hmap)
  exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

theorem computes_lift_exact_from_equiv
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hmap : ∀ (state : innerState) (read : Option MachineCodeSymbol)
        (action : Option MachineCodeSymbol × Direction × innerState),
      inner.transition state read = some action ->
      transition (embed state) read = mapAction embed (some action))
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol innerState}
    {tape : Tape MachineCodeSymbol}
    (hrun : inner.runConfigExact? steps source = some target)
    (htape : Tape.Equiv source.tape tape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (TuringMachine.PhaseEmbedding.liftConfig embed
          { state := source.state, tape := tape })
        (TuringMachine.PhaseEmbedding.liftConfig embed
          { state := target.state, tape := targetTape }) ∧
      Tape.Equiv target.tape targetTape := by
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun htape with
    ⟨⟨targetState, targetTape⟩, hactual, hstate, htape'⟩
  simp only at hstate
  subst targetState
  have houter :=
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      embed (step_of_mapped_transition inner embed hmap) hactual
  exact ⟨targetTape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp houter),
    htape'⟩

def outerSuffix (innerUsed innerRemaining candidateFuel candidateOuter
    candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.SplitLayout.encodeSplitAppend innerUsed innerRemaining
    (Scheduler.SplitLayout.candidateMarker ::
      MachineDescription.encodeNatAppend candidateFuel
        (GeneratedCode.nestedStageCode input candidateInner candidateOuter))

def fuelSuffix (outerUsed outerRemaining innerUsed innerRemaining
    candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  Scheduler.SplitLayout.encodeSplitAppend outerUsed
    (outerRemaining + 1)
    (outerSuffix innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input)

def sourceWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round fuelUsed 0 outerUsed
    (outerRemaining + 1) innerUsed innerRemaining candidateFuel
    candidateOuter candidateInner input

def afterFuelWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round 0 fuelUsed outerUsed
    (outerRemaining + 1) innerUsed innerRemaining candidateFuel
    candidateOuter candidateInner input

def afterOuterWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round 0 fuelUsed (outerUsed + 1)
    outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
    candidateInner input

def targetWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      _candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round 0 fuelUsed (outerUsed + 1)
    outerRemaining innerUsed innerRemaining 0 (candidateOuter + 1)
    candidateInner input

def fuelBaseRev (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Word MachineCodeSymbol :=
  List.append (Scheduler.Advance.ExhaustedSplitReset.ticks round)
    (Scheduler.Rollover.Locator.geometryPrefixRev geometry)

def fuelLocatorSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .header []
    (sourceWord geometry round fuelUsed outerUsed outerRemaining innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner input)

def fuelLocatorTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .halt
    (Scheduler.Rollover.Locator.natPrefixRev round
      (Scheduler.Rollover.Locator.geometryPrefixRev geometry))
    (Scheduler.SplitLayout.encodeSplitAppend fuelUsed 0
      (fuelSuffix outerUsed outerRemaining innerUsed innerRemaining
        candidateFuel candidateOuter candidateInner input))

def fuelLocateSteps (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Nat :=
  Scheduler.Rollover.Locator.geometrySteps geometry + (round + 1)

theorem locate_fuel_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    (Scheduler.Rollover.Locator.machine .fuel).runConfigExact?
        (fuelLocateSteps geometry round)
        (fuelLocatorSource geometry round fuelUsed outerUsed outerRemaining
          innerUsed innerRemaining candidateFuel candidateOuter candidateInner
          input) =
      some (fuelLocatorTarget geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input) := by
  simpa [fuelLocateSteps, fuelLocatorSource, fuelLocatorTarget, sourceWord,
    fuelSuffix, outerSuffix, Scheduler.Rollover.word]
    using Scheduler.FuelBranch.locate_fuel_exact geometry round
      (Scheduler.SplitLayout.encodeSplitAppend fuelUsed 0
        (fuelSuffix outerUsed outerRemaining innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input))

def fuelResetSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.sourceConfig fuelUsed
    (fuelBaseRev geometry round)
    (fuelSuffix outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input)

def fuelResetTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.targetConfig fuelUsed
    (fuelBaseRev geometry round)
    (fuelSuffix outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input)

theorem fuelLocatorTarget_tape_eq_resetSource
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    (fuelLocatorTarget geometry round fuelUsed outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter candidateInner
      input).tape =
    (fuelResetSource geometry round fuelUsed outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter candidateInner
      input).tape := by
  rfl

theorem fuel_reset_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    splitResetMachine.runConfigExact?
        (Scheduler.Advance.ExhaustedSplitReset.runSteps fuelUsed)
        (fuelResetSource geometry round fuelUsed outerUsed outerRemaining
          innerUsed innerRemaining candidateFuel candidateOuter candidateInner
          input) =
      some (fuelResetTarget geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input) := by
  exact Scheduler.Advance.ExhaustedSplitReset.run_exact fuelUsed
    (fuelBaseRev geometry round)
    (fuelSuffix outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input)

def fuelRewindLeftRev (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Word MachineCodeSymbol :=
  Scheduler.SplitLayout.splitMarker :: MachineCodeSymbol.done ::
    MachineCodeSymbol.done :: fuelBaseRev geometry round

def fuelRewindRest (fuelUsed outerUsed outerRemaining innerUsed
    innerRemaining candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend fuelUsed
    (fuelSuffix outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input)

def fuelRewindSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  Scheduler.MainRollover.ExactRewind.startConfig
    (fuelRewindLeftRev geometry round)
    (fuelRewindRest fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input)

def fuelRewindTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  RewindWord.gateConfig
    (afterFuelWord geometry round fuelUsed outerUsed outerRemaining innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner input) 0

theorem fuelResetTarget_tape_equiv_rewindSource
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    Tape.Equiv
      (fuelRewindSource geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input).tape
      (fuelResetTarget geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input).tape := by
  simpa [fuelRewindSource, fuelRewindLeftRev, fuelRewindRest,
    fuelResetTarget, Scheduler.MainRollover.ExactRewind.startConfig,
    Scheduler.Advance.ExhaustedSplitReset.targetConfig,
    Scheduler.Advance.ExhaustedSplitReset.config]
    using
      Scheduler.MainRollover.ExactRewind.startTape_equiv_cursorTape
        (fuelRewindLeftRev geometry round)
        (fuelRewindRest fuelUsed outerUsed outerRemaining innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input)

theorem fuel_rewind_output
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    List.append (fuelRewindLeftRev geometry round).reverse
        (fuelRewindRest fuelUsed outerUsed outerRemaining innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) =
      afterFuelWord geometry round fuelUsed outerUsed outerRemaining innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input := by
  cases geometry <;>
    simp [fuelRewindLeftRev, fuelRewindRest, fuelBaseRev, fuelSuffix,
      outerSuffix, afterFuelWord, Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.reverse_append, List.append_assoc]

theorem fuel_rewind_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    RewindWord.machine.runConfigExact?
        ((fuelRewindLeftRev geometry round).length + 2)
        (fuelRewindSource geometry round fuelUsed outerUsed outerRemaining
          innerUsed innerRemaining candidateFuel candidateOuter candidateInner
          input) =
      some (fuelRewindTarget geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input) := by
  unfold fuelRewindSource fuelRewindTarget
  rw [Scheduler.MainRollover.ExactRewind.run_exact]
  rw [fuel_rewind_output]

def outerBaseRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed : Nat) : Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.splitPrefixRev 0 fuelUsed
    (Scheduler.Rollover.Locator.natPrefixRev round
      (Scheduler.Rollover.Locator.geometryPrefixRev geometry))

def outerLocatorSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .header []
    (afterFuelWord geometry round fuelUsed outerUsed outerRemaining innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner input)

def outerLocatorTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .halt
    (outerBaseRev geometry round fuelUsed)
    (Scheduler.SplitLayout.encodeSplitAppend outerUsed
      (outerRemaining + 1)
      (outerSuffix innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input))

def outerLocateSteps (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed : Nat) : Nat :=
  (Scheduler.Rollover.Locator.geometrySteps geometry + (round + 1)) +
    Scheduler.Rollover.Locator.splitSteps 0 fuelUsed

theorem locate_outer_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    (Scheduler.Rollover.Locator.machine .outer).runConfigExact?
        (outerLocateSteps geometry round fuelUsed)
        (outerLocatorSource geometry round fuelUsed outerUsed outerRemaining
          innerUsed innerRemaining candidateFuel candidateOuter candidateInner
          input) =
      some (outerLocatorTarget geometry round fuelUsed outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input) := by
  unfold outerLocateSteps outerLocatorSource outerLocatorTarget
  rw [show afterFuelWord geometry round fuelUsed outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input =
      MachineCodeSymbol.header ::
        Scheduler.Layout.encodeGeometryAppend geometry
          (MachineDescription.encodeNatAppend round
            (Scheduler.SplitLayout.encodeSplitAppend 0 fuelUsed
              (Scheduler.SplitLayout.encodeSplitAppend outerUsed
                (outerRemaining + 1)
                (outerSuffix innerUsed innerRemaining candidateFuel
                  candidateOuter candidateInner input)))) by rfl]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (Scheduler.Rollover.Locator.machine .outer)
    (Scheduler.Rollover.Locator.geometrySteps geometry + (round + 1))
    (Scheduler.Rollover.Locator.splitSteps 0 fuelUsed)]
  rw [Scheduler.Rollover.Locator.to_fuelUsed_exact .outer geometry
    round
    (Scheduler.SplitLayout.encodeSplitAppend 0 fuelUsed
      (Scheduler.SplitLayout.encodeSplitAppend outerUsed
        (outerRemaining + 1)
        (outerSuffix innerUsed innerRemaining candidateFuel candidateOuter
          candidateInner input))) (by decide) (by decide)]
  simp only
  rw [Scheduler.Rollover.Locator.split_run_exact .outer
    .fuelUsed .fuelMarker .fuelRemaining .halt 0 fuelUsed
    (Scheduler.Rollover.Locator.natPrefixRev round
      (Scheduler.Rollover.Locator.geometryPrefixRev geometry))
    (Scheduler.SplitLayout.encodeSplitAppend outerUsed
      (outerRemaining + 1)
      (outerSuffix innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input))
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
  rfl

theorem outerLocatorTarget_tape_eq_splitSource
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    (outerLocatorTarget geometry round fuelUsed outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter candidateInner
      input).tape =
      (Scheduler.SplitAdvance.sourceConfig outerUsed outerRemaining
        (outerBaseRev geometry round fuelUsed)
        (outerSuffix innerUsed innerRemaining candidateFuel candidateOuter
          candidateInner input)).tape := by
  rfl

theorem outer_split_output_eq_afterOuterWord
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.SplitAdvance.outputWord outerUsed outerRemaining
        (outerBaseRev geometry round fuelUsed)
        (outerSuffix innerUsed innerRemaining candidateFuel candidateOuter
          candidateInner input) =
      afterOuterWord geometry round fuelUsed outerUsed outerRemaining innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input := by
  cases geometry <;>
    simp [Scheduler.SplitAdvance.outputWord, outerBaseRev, outerSuffix,
      afterOuterWord, Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.splitPrefixRev,
      Scheduler.Rollover.Locator.natPrefixRev,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.reverse_append, List.append_assoc]

def candidateOuterBaseRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining : Nat) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.natPrefixRev 0
    (Scheduler.Rollover.Locator.candidatePrefixRev geometry round
      0 fuelUsed (outerUsed + 1) outerRemaining innerUsed innerRemaining)

def candidateOuterSuffix (candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend candidateInner input

theorem ticks_append_tick_cons (count : Nat)
    (suffix : List MachineCodeSymbol) :
    List.append
        (List.replicate count MachineCodeSymbol.tick)
        (MachineCodeSymbol.tick :: suffix) =
      MachineCodeSymbol.tick ::
        List.append (List.replicate count MachineCodeSymbol.tick) suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change MachineCodeSymbol.tick ::
          List.append (List.replicate count MachineCodeSymbol.tick)
            (MachineCodeSymbol.tick :: suffix) =
        MachineCodeSymbol.tick :: MachineCodeSymbol.tick ::
          List.append (List.replicate count MachineCodeSymbol.tick) suffix
      exact congrArg (fun rest => MachineCodeSymbol.tick :: rest) ih

theorem candidate_grow_output_eq_targetWord
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.CandidateGrow.growOutput
        (candidateOuterBaseRev geometry round fuelUsed outerUsed
          outerRemaining innerUsed innerRemaining)
        candidateOuter (candidateOuterSuffix candidateInner input) =
      targetWord geometry round fuelUsed outerUsed outerRemaining innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input := by
  unfold Word at input ⊢
  cases geometry <;>
    simp [Scheduler.CandidateGrow.growOutput, candidateOuterBaseRev,
      candidateOuterSuffix, targetWord, Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.candidatePrefixRev,
      Scheduler.Rollover.Locator.splitPrefixRev,
      Scheduler.Rollover.Locator.natPrefixRev,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      Scheduler.CandidateGrow.nestedStageCode_eq_tail,
      List.replicate_succ, List.reverse_append, List.append_assoc] <;>
    exact ticks_append_tick_cons outerUsed _

theorem run_outer_branch
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (sourceWord geometry round fuelUsed outerUsed outerRemaining
              innerUsed innerRemaining candidateFuel candidateOuter
              candidateInner input) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        targetWord geometry round fuelUsed outerUsed outerRemaining innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input ∧
      Tape.Equiv
        (Tape.input
          (targetWord geometry round fuelUsed outerUsed outerRemaining
            innerUsed innerRemaining candidateFuel candidateOuter
            candidateInner input)) finalTape := by
  have hfuelSource : Tape.Equiv
      (fuelLocatorSource geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input).tape
      (Tape.input
        (sourceWord geometry round fuelUsed outerUsed outerRemaining innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input)) :=
    Tape.Equiv.refl _
  rcases computes_lift_exact_from_equiv
      (Scheduler.Rollover.Locator.machine .fuel) locateFuelEmbed
      locateFuel_map
      (locate_fuel_exact geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input) hfuelSource with
    ⟨fuelLocatedTape, hlocateFuel, hfuelLocated⟩
  have hresetFuelSource : Tape.Equiv
      (fuelResetSource geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input).tape fuelLocatedTape := by
    rw [← fuelLocatorTarget_tape_eq_resetSource]
    exact hfuelLocated
  rcases computes_lift_exact_from_equiv splitResetMachine resetFuelEmbed
      resetFuel_map
      (fuel_reset_exact geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input) hresetFuelSource with
    ⟨fuelResetTape, hresetFuel, hfuelReset⟩
  have hrewindFuelSource : Tape.Equiv
      (fuelRewindSource geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input).tape fuelResetTape :=
    Tape.Equiv.trans
      (fuelResetTarget_tape_equiv_rewindSource geometry round fuelUsed
        outerUsed outerRemaining innerUsed innerRemaining candidateFuel
        candidateOuter candidateInner input)
      hfuelReset
  rcases computes_lift_exact_from_equiv RewindWord.machine rewindFuelEmbed
      rewindFuel_map
      (fuel_rewind_exact geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input) hrewindFuelSource with
    ⟨fuelRewoundTape, hrewindFuel, hfuelRewound⟩
  have houterInputToGate : Tape.Equiv
      (outerLocatorSource geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input).tape
      (fuelRewindTarget geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input).tape := by
    exact Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (afterFuelWord geometry round fuelUsed outerUsed outerRemaining
          innerUsed innerRemaining candidateFuel candidateOuter candidateInner
          input) 0)
  have hlocateOuterSource : Tape.Equiv
      (outerLocatorSource geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input).tape fuelRewoundTape :=
    Tape.Equiv.trans houterInputToGate hfuelRewound
  rcases computes_lift_exact_from_equiv
      (Scheduler.Rollover.Locator.machine .outer) locateOuterEmbed
      locateOuter_map
      (locate_outer_exact geometry round fuelUsed outerUsed outerRemaining
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input) hlocateOuterSource with
    ⟨outerLocatedTape, hlocateOuter, houterLocated⟩
  have hsplitSource : Tape.Equiv
      (Scheduler.SplitAdvance.sourceConfig outerUsed outerRemaining
        (outerBaseRev geometry round fuelUsed)
        (outerSuffix innerUsed innerRemaining candidateFuel candidateOuter
          candidateInner input)).tape outerLocatedTape := by
    rw [← outerLocatorTarget_tape_eq_splitSource]
    exact houterLocated
  rcases Scheduler.SplitAdvance.advance outerUsed outerRemaining
      (outerBaseRev geometry round fuelUsed)
      (outerSuffix innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input) with
    ⟨canonicalSplitTape, hsplitCanonical, hcanonicalSplit⟩
  rcases TuringMachine.computes_to_computesIn hsplitCanonical with
    ⟨splitSteps, hsplitCanonicalIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hsplitCanonicalIn hsplitSource with
    ⟨actualSplitConfig, hsplitActualIn, hsplitState, hsplitFinal⟩
  rcases actualSplitConfig with ⟨actualSplitState, actualSplitTape⟩
  simp only at hsplitState hsplitActualIn hsplitFinal
  subst actualSplitState
  have hsplitInner : TuringMachine.Computes
      Scheduler.SplitAdvance.machine
      { state := Scheduler.SplitAdvance.machine.start
        tape := outerLocatedTape }
      { state := Scheduler.SplitAdvance.machine.halt
        tape := actualSplitTape } :=
    TuringMachine.computesIn_to_computes hsplitActualIn
  have hsplitOuter := lift_computes Scheduler.SplitAdvance.machine
    splitOuterEmbed splitOuter_map hsplitInner
  have hafterOuter : Tape.Equiv
      (Tape.input
        (afterOuterWord geometry round fuelUsed outerUsed outerRemaining
          innerUsed innerRemaining candidateFuel candidateOuter candidateInner
          input)) actualSplitTape := by
    rw [← outer_split_output_eq_afterOuterWord]
    exact Tape.Equiv.trans hcanonicalSplit hsplitFinal
  rcases
      Scheduler.CandidatePrefixReset.PrefixMachine.reset_fuel_from_input
        geometry round 0 fuelUsed (outerUsed + 1) outerRemaining innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input
        actualSplitTape hafterOuter with
    ⟨candidateResetTape, hcandidateResetInner, hcandidateResetTape⟩
  have hcandidateReset := lift_computes
    (Scheduler.CandidatePrefixReset.PrefixMachine.machine .fuel)
    candidateResetEmbed candidateReset_map hcandidateResetInner
  let growBase := candidateOuterBaseRev geometry round fuelUsed outerUsed
    outerRemaining innerUsed innerRemaining
  let growSuffix := candidateOuterSuffix candidateInner input
  have hgrowExact := Scheduler.CandidateGrow.grow_run_of_eq_some
    .candidateOuter
    (Scheduler.CandidateGrow.grow_exact growBase candidateOuter
      growSuffix)
  have hgrowSource : Tape.Equiv
      (TuringMachine.PhaseEmbedding.liftConfig
        Scheduler.CandidateGrow.growEmbed
        (Scheduler.CandidateGrow.growSource growBase candidateOuter
          growSuffix)).tape candidateResetTape := by
    simpa [growBase, growSuffix, candidateOuterBaseRev,
      candidateOuterSuffix,
      Scheduler.CandidateGrow.growSource,
      Scheduler.CandidatePrefixReset.outerConfig,
      Scheduler.CandidatePrefixReset.mainPrefixRev,
      Scheduler.CandidatePrefixReset.word,
      Scheduler.CandidateReset.locateConfig,
      Scheduler.Rollover.Locator.config,
      Scheduler.CandidateGrow.growBuffer,
      Scheduler.Advance.GrowResetInsertion.buffer,
      InsertBlock.singletonBuffer,
      Scheduler.CandidateGrow.growEmbed,
      InsertRestagedMachine.editConfig, InsertBlock.config,
      TuringMachine.PhaseEmbedding.liftConfig]
      using hcandidateResetTape
  rcases computes_lift_exact_from_equiv
      (Scheduler.CandidateGrow.machine .candidateOuter)
      candidateGrowEmbed candidateGrow_map hgrowExact hgrowSource with
    ⟨finalTape, hgrow, hfinal⟩
  refine ⟨finalTape,
    TuringMachine.computes_trans hlocateFuel
      (TuringMachine.computes_trans hresetFuel
          (TuringMachine.computes_trans hrewindFuel
          (TuringMachine.computes_trans hlocateOuter
            (TuringMachine.computes_trans hsplitOuter
              (TuringMachine.computes_trans hcandidateReset hgrow))))),
    ?_, ?_⟩
  have hcanonicalOutput : Tape.normalizedOutput
      (TuringMachine.PhaseEmbedding.liftConfig candidateGrowEmbed
        (TuringMachine.PhaseEmbedding.liftConfig
          Scheduler.CandidateGrow.growEmbed
          (Scheduler.CandidateGrow.growTarget growBase candidateOuter
            growSuffix))).tape =
      targetWord geometry round fuelUsed outerUsed outerRemaining innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input := by
    change Tape.normalizedOutput
      (RewindWord.gateTape
        (Scheduler.CandidateGrow.growOutput growBase candidateOuter
          growSuffix) 0) = _
    rw [Tape.Equiv.normalizedOutput_eq
      (RewindWord.gateTape_equiv_input
        (Scheduler.CandidateGrow.growOutput growBase candidateOuter
          growSuffix) 0)]
    rw [show Scheduler.CandidateGrow.growOutput growBase candidateOuter
        growSuffix =
      targetWord geometry round fuelUsed outerUsed outerRemaining innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input by
      exact candidate_grow_output_eq_targetWord geometry round fuelUsed
        outerUsed outerRemaining innerUsed innerRemaining candidateFuel
        candidateOuter candidateInner input]
    simpa [Tape.output] using Tape.normalizedOutput_output
      (targetWord geometry round fuelUsed outerUsed outerRemaining innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input)
  have hnormalized := Tape.Equiv.normalizedOutput_eq hfinal
  exact hnormalized.symm.trans hcanonicalOutput
  have hcanonicalEquiv : Tape.Equiv
      (Tape.input
        (targetWord geometry round fuelUsed outerUsed outerRemaining innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input))
      (TuringMachine.PhaseEmbedding.liftConfig candidateGrowEmbed
        (TuringMachine.PhaseEmbedding.liftConfig
          Scheduler.CandidateGrow.growEmbed
          (Scheduler.CandidateGrow.growTarget growBase candidateOuter
            growSuffix))).tape := by
    change Tape.Equiv
      (Tape.input
        (targetWord geometry round fuelUsed outerUsed outerRemaining innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input))
      (RewindWord.gateTape
        (Scheduler.CandidateGrow.growOutput growBase candidateOuter
          growSuffix) 0)
    rw [show Scheduler.CandidateGrow.growOutput growBase candidateOuter
        growSuffix =
      targetWord geometry round fuelUsed outerUsed outerRemaining innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input by
      exact candidate_grow_output_eq_targetWord geometry round fuelUsed
        outerUsed outerRemaining innerUsed innerRemaining candidateFuel
        candidateOuter candidateInner input]
    exact Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (targetWord geometry round fuelUsed outerUsed outerRemaining innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) 0)
  exact Tape.Equiv.trans hcanonicalEquiv hfinal

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.OuterBranch
