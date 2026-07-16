import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.OuterBranch

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.InnerBranch

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
  | resetOuter (inner : SplitResetControl)
  | rewindOuter (inner : RewindWord.Control)
  | locateInner (inner : LocatorControl)
  | splitInner (inner : SplitAdvanceControl)
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
      Scheduler.Advance.ExhaustedSplitReset.Control.finite.elems.map
        Control.resetOuter ++
      RewindWord.Control.finite.elems.map Control.rewindOuter ++
      Scheduler.Rollover.Locator.Control.finite.elems.map
        Control.locateInner ++
      Scheduler.SplitAdvance.Control.finite.elems.map
        Control.splitInner ++
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
    | resetOuter inner =>
        simp
        exact
          Scheduler.Advance.ExhaustedSplitReset.Control.finite.complete
            inner
    | rewindOuter inner =>
        simp
        exact RewindWord.Control.finite.complete inner
    | locateInner inner =>
        simp
        exact Scheduler.Rollover.Locator.Control.finite.complete inner
    | splitInner inner =>
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
  | .halt => .resetOuter splitResetMachine.start
  | inner => .locateOuter inner

def resetOuterEmbed : SplitResetControl -> Control
  | .halt => .rewindOuter RewindWord.machine.start
  | inner => .resetOuter inner

def rewindOuterEmbed : RewindWord.Control -> Control
  | .gate => .locateInner .header
  | inner => .rewindOuter inner

def locateInnerEmbed : LocatorControl -> Control
  | .halt => .splitInner Scheduler.SplitAdvance.machine.start
  | inner => .locateInner inner

def splitInnerEmbed : SplitAdvanceControl -> Control
  | .rewind .gate =>
      .candidateReset
        (Scheduler.CandidatePrefixReset.PrefixMachine.machine
          .outer).start
  | inner => .splitInner inner

def candidateResetEmbed : CandidateResetControl -> Control
  | .locate .inner .halt =>
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
  | .resetOuter inner, read =>
      mapAction resetOuterEmbed
        (Scheduler.Advance.ExhaustedSplitReset.transition inner read)
  | .rewindOuter inner, read =>
      mapAction rewindOuterEmbed (RewindWord.transition inner read)
  | .locateInner inner, read =>
      mapAction locateInnerEmbed
        (Scheduler.Rollover.Locator.transition .inner inner read)
  | .splitInner inner, read =>
      mapAction splitInnerEmbed
        (Scheduler.SplitAdvance.transition inner read)
  | .candidateReset inner, read =>
      mapAction candidateResetEmbed
        ((Scheduler.CandidatePrefixReset.PrefixMachine.machine
          .outer).transition inner read)
  | .candidateGrow inner, read =>
      mapAction candidateGrowEmbed
        ((Scheduler.CandidateGrow.machine .candidateInner).transition
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

theorem resetOuter_map (state : SplitResetControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × SplitResetControl)
    (haction : splitResetMachine.transition state read = some action) :
    transition (resetOuterEmbed state) read =
      mapAction resetOuterEmbed (some action) := by
  cases state <;>
    simp_all [splitResetMachine,
      Scheduler.Advance.ExhaustedSplitReset.machine,
      Scheduler.Advance.ExhaustedSplitReset.transition,
      transition, resetOuterEmbed, mapAction]

theorem rewindOuter_map (state : RewindWord.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × RewindWord.Control)
    (haction : RewindWord.machine.transition state read = some action) :
    transition (rewindOuterEmbed state) read =
      mapAction rewindOuterEmbed (some action) := by
  cases state <;>
    simp_all [RewindWord.machine, RewindWord.transition,
      transition, rewindOuterEmbed, mapAction]

theorem locateInner_map (state : LocatorControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × LocatorControl)
    (haction : (Scheduler.Rollover.Locator.machine .inner).transition
      state read = some action) :
    transition (locateInnerEmbed state) read =
      mapAction locateInnerEmbed (some action) := by
  cases state <;>
    simp_all [Scheduler.Rollover.Locator.machine,
      Scheduler.Rollover.Locator.transition, transition,
      locateInnerEmbed, mapAction]

theorem splitInner_map (state : SplitAdvanceControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      SplitAdvanceControl)
    (haction : Scheduler.SplitAdvance.machine.transition state read =
      some action) :
    transition (splitInnerEmbed state) read =
      mapAction splitInnerEmbed (some action) := by
  cases state with
  | used =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitInnerEmbed,
        mapAction]
  | marker =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitInnerEmbed,
        mapAction]
  | takeRemaining =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitInnerEmbed,
        mapAction]
  | writeDone =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitInnerEmbed,
        mapAction]
  | writeTick =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitInnerEmbed,
        mapAction]
  | rewind inner =>
      cases inner <;>
        simp_all [Scheduler.SplitAdvance.machine,
          Scheduler.SplitAdvance.transition, RewindWord.transition,
          transition, splitInnerEmbed, mapAction,
          Scheduler.SplitAdvance.mapAction]

theorem candidateReset_map (state : CandidateResetControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      CandidateResetControl)
    (haction :
      (Scheduler.CandidatePrefixReset.PrefixMachine.machine
        .outer).transition state read = some action) :
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
      (Scheduler.CandidateGrow.machine .candidateInner).transition
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

def candidateTail (candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  Scheduler.SplitLayout.candidateMarker ::
    MachineDescription.encodeNatAppend candidateFuel
      (GeneratedCode.nestedStageCode input candidateInner candidateOuter)

def innerSuffix (innerUsed innerRemaining candidateFuel candidateOuter
    candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.SplitLayout.encodeSplitAppend innerUsed
    (innerRemaining + 1)
    (candidateTail candidateFuel candidateOuter candidateInner input)

def outerSuffix (outerUsed innerUsed innerRemaining candidateFuel
    candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.SplitLayout.encodeSplitAppend outerUsed 0
    (innerSuffix innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input)

def sourceWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round fuelUsed 0 outerUsed 0
    innerUsed (innerRemaining + 1) candidateFuel candidateOuter candidateInner
    input

def afterFuelWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round 0 fuelUsed outerUsed 0
    innerUsed (innerRemaining + 1) candidateFuel candidateOuter candidateInner
    input

def afterOuterWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round 0 fuelUsed 0 outerUsed
    innerUsed (innerRemaining + 1) candidateFuel candidateOuter candidateInner
    input

def afterInnerWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round 0 fuelUsed 0 outerUsed
    (innerUsed + 1) innerRemaining candidateFuel candidateOuter candidateInner
    input

def targetWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining _candidateFuel
      _candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round 0 fuelUsed 0 outerUsed
    (innerUsed + 1) innerRemaining 0 0 (candidateInner + 1) input

def fuelSuffix (outerUsed innerUsed innerRemaining candidateFuel
    candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  outerSuffix outerUsed innerUsed innerRemaining candidateFuel candidateOuter
    candidateInner input

def fuelBaseRev (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Word MachineCodeSymbol :=
  List.append (Scheduler.Advance.ExhaustedSplitReset.ticks round)
    (Scheduler.Rollover.Locator.geometryPrefixRev geometry)

def fuelLocatorSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .header []
    (sourceWord geometry round fuelUsed outerUsed innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input)

def fuelLocatorTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .halt
    (Scheduler.Rollover.Locator.natPrefixRev round
      (Scheduler.Rollover.Locator.geometryPrefixRev geometry))
    (Scheduler.SplitLayout.encodeSplitAppend fuelUsed 0
      (fuelSuffix outerUsed innerUsed innerRemaining candidateFuel
        candidateOuter candidateInner input))

def fuelLocateSteps (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Nat :=
  Scheduler.Rollover.Locator.geometrySteps geometry + (round + 1)

theorem locate_fuel_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    (Scheduler.Rollover.Locator.machine .fuel).runConfigExact?
        (fuelLocateSteps geometry round)
        (fuelLocatorSource geometry round fuelUsed outerUsed innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) =
      some (fuelLocatorTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input) := by
  simpa [fuelLocateSteps, fuelLocatorSource, fuelLocatorTarget, sourceWord,
    fuelSuffix, outerSuffix, innerSuffix, candidateTail,
    Scheduler.Rollover.word]
    using Scheduler.FuelBranch.locate_fuel_exact geometry round
      (Scheduler.SplitLayout.encodeSplitAppend fuelUsed 0
        (fuelSuffix outerUsed innerUsed innerRemaining candidateFuel
          candidateOuter candidateInner input))

def fuelResetSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.sourceConfig fuelUsed
    (fuelBaseRev geometry round)
    (fuelSuffix outerUsed innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input)

def fuelResetTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.targetConfig fuelUsed
    (fuelBaseRev geometry round)
    (fuelSuffix outerUsed innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input)

theorem fuelLocatorTarget_tape_eq_resetSource
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    (fuelLocatorTarget geometry round fuelUsed outerUsed innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner input).tape =
      (fuelResetSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape :=
  rfl

theorem fuel_reset_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    splitResetMachine.runConfigExact?
        (Scheduler.Advance.ExhaustedSplitReset.runSteps fuelUsed)
        (fuelResetSource geometry round fuelUsed outerUsed innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) =
      some (fuelResetTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input) := by
  exact Scheduler.Advance.ExhaustedSplitReset.run_exact fuelUsed
    (fuelBaseRev geometry round)
    (fuelSuffix outerUsed innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input)

def fuelRewindLeftRev (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Word MachineCodeSymbol :=
  Scheduler.SplitLayout.splitMarker :: MachineCodeSymbol.done ::
    MachineCodeSymbol.done :: fuelBaseRev geometry round

def fuelRewindRest (fuelUsed outerUsed innerUsed innerRemaining candidateFuel
    candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend fuelUsed
    (fuelSuffix outerUsed innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input)

def fuelRewindSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  Scheduler.MainRollover.ExactRewind.startConfig
    (fuelRewindLeftRev geometry round)
    (fuelRewindRest fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner input)

def fuelRewindTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  RewindWord.gateConfig
    (afterFuelWord geometry round fuelUsed outerUsed innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input) 0

theorem fuelResetTarget_tape_equiv_rewindSource
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Tape.Equiv
      (fuelRewindSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      (fuelResetTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape := by
  simpa [fuelRewindSource, fuelRewindLeftRev, fuelRewindRest,
    fuelResetTarget, Scheduler.MainRollover.ExactRewind.startConfig,
    Scheduler.Advance.ExhaustedSplitReset.targetConfig,
    Scheduler.Advance.ExhaustedSplitReset.config]
    using
      Scheduler.MainRollover.ExactRewind.startTape_equiv_cursorTape
        (fuelRewindLeftRev geometry round)
        (fuelRewindRest fuelUsed outerUsed innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input)

theorem fuel_rewind_output
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    List.append (fuelRewindLeftRev geometry round).reverse
        (fuelRewindRest fuelUsed outerUsed innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input) =
      afterFuelWord geometry round fuelUsed outerUsed innerUsed innerRemaining
        candidateFuel candidateOuter candidateInner input := by
  cases geometry <;>
    simp [fuelRewindLeftRev, fuelRewindRest, fuelBaseRev, fuelSuffix,
      outerSuffix, innerSuffix, candidateTail, afterFuelWord,
      Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.reverse_append, List.append_assoc]

theorem fuel_rewind_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    RewindWord.machine.runConfigExact?
        ((fuelRewindLeftRev geometry round).length + 2)
        (fuelRewindSource geometry round fuelUsed outerUsed innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) =
      some (fuelRewindTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input) := by
  unfold fuelRewindSource fuelRewindTarget
  rw [Scheduler.MainRollover.ExactRewind.run_exact]
  rw [fuel_rewind_output]

def outerPrefixRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed : Nat) : Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.splitPrefixRev 0 fuelUsed
    (Scheduler.Rollover.Locator.natPrefixRev round
      (Scheduler.Rollover.Locator.geometryPrefixRev geometry))

def outerResetBaseRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed : Nat) : Word MachineCodeSymbol :=
  List.append (Scheduler.Advance.ExhaustedSplitReset.ticks fuelUsed)
    (Scheduler.SplitLayout.splitMarker ::
      Scheduler.Rollover.Locator.natPrefixRev 0
        (Scheduler.Rollover.Locator.natPrefixRev round
          (Scheduler.Rollover.Locator.geometryPrefixRev geometry)))

def outerLocatorSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .header []
    (afterFuelWord geometry round fuelUsed outerUsed innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input)

def outerLocatorTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .halt
    (outerPrefixRev geometry round fuelUsed)
    (Scheduler.SplitLayout.encodeSplitAppend outerUsed 0
      (innerSuffix innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input))

def outerLocateSteps (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed : Nat) : Nat :=
  (Scheduler.Rollover.Locator.geometrySteps geometry + (round + 1)) +
    Scheduler.Rollover.Locator.splitSteps 0 fuelUsed

theorem locate_outer_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    (Scheduler.Rollover.Locator.machine .outer).runConfigExact?
        (outerLocateSteps geometry round fuelUsed)
        (outerLocatorSource geometry round fuelUsed outerUsed innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) =
      some (outerLocatorTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input) := by
  unfold outerLocateSteps outerLocatorSource outerLocatorTarget
  rw [show afterFuelWord geometry round fuelUsed outerUsed innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner input =
    MachineCodeSymbol.header ::
      Scheduler.Layout.encodeGeometryAppend geometry
        (MachineDescription.encodeNatAppend round
          (Scheduler.SplitLayout.encodeSplitAppend 0 fuelUsed
            (Scheduler.SplitLayout.encodeSplitAppend outerUsed 0
              (innerSuffix innerUsed innerRemaining candidateFuel
                candidateOuter candidateInner input)))) by rfl]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (Scheduler.Rollover.Locator.machine .outer)
    (Scheduler.Rollover.Locator.geometrySteps geometry + (round + 1))
    (Scheduler.Rollover.Locator.splitSteps 0 fuelUsed)]
  rw [Scheduler.Rollover.Locator.to_fuelUsed_exact .outer geometry
    round
    (Scheduler.SplitLayout.encodeSplitAppend 0 fuelUsed
      (Scheduler.SplitLayout.encodeSplitAppend outerUsed 0
        (innerSuffix innerUsed innerRemaining candidateFuel candidateOuter
          candidateInner input))) (by decide) (by decide)]
  simp only
  rw [Scheduler.Rollover.Locator.split_run_exact .outer
    .fuelUsed .fuelMarker .fuelRemaining .halt 0 fuelUsed
    (Scheduler.Rollover.Locator.natPrefixRev round
      (Scheduler.Rollover.Locator.geometryPrefixRev geometry))
    (Scheduler.SplitLayout.encodeSplitAppend outerUsed 0
      (innerSuffix innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input))
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
  rfl

def outerResetSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.sourceConfig outerUsed
    (outerResetBaseRev geometry round fuelUsed)
    (innerSuffix innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input)

def outerResetTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.targetConfig outerUsed
    (outerResetBaseRev geometry round fuelUsed)
    (innerSuffix innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input)

theorem outerLocatorTarget_tape_eq_resetSource
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    (outerLocatorTarget geometry round fuelUsed outerUsed innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner input).tape =
      (outerResetSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape :=
  rfl

theorem outer_reset_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    splitResetMachine.runConfigExact?
        (Scheduler.Advance.ExhaustedSplitReset.runSteps outerUsed)
        (outerResetSource geometry round fuelUsed outerUsed innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) =
      some (outerResetTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input) := by
  exact Scheduler.Advance.ExhaustedSplitReset.run_exact outerUsed
    (outerResetBaseRev geometry round fuelUsed)
    (innerSuffix innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input)

def outerRewindLeftRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed : Nat) : Word MachineCodeSymbol :=
  Scheduler.SplitLayout.splitMarker :: MachineCodeSymbol.done ::
    MachineCodeSymbol.done :: outerResetBaseRev geometry round fuelUsed

def outerRewindRest (outerUsed innerUsed innerRemaining candidateFuel
    candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend outerUsed
    (innerSuffix innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input)

def outerRewindSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  Scheduler.MainRollover.ExactRewind.startConfig
    (outerRewindLeftRev geometry round fuelUsed)
    (outerRewindRest outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner input)

def outerRewindTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  RewindWord.gateConfig
    (afterOuterWord geometry round fuelUsed outerUsed innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input) 0

theorem outerResetTarget_tape_equiv_rewindSource
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Tape.Equiv
      (outerRewindSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      (outerResetTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape := by
  simpa [outerRewindSource, outerRewindLeftRev, outerRewindRest,
    outerResetTarget, Scheduler.MainRollover.ExactRewind.startConfig,
    Scheduler.Advance.ExhaustedSplitReset.targetConfig,
    Scheduler.Advance.ExhaustedSplitReset.config]
    using
      Scheduler.MainRollover.ExactRewind.startTape_equiv_cursorTape
        (outerRewindLeftRev geometry round fuelUsed)
        (outerRewindRest outerUsed innerUsed innerRemaining candidateFuel
          candidateOuter candidateInner input)

theorem outer_rewind_output
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    List.append (outerRewindLeftRev geometry round fuelUsed).reverse
        (outerRewindRest outerUsed innerUsed innerRemaining candidateFuel
          candidateOuter candidateInner input) =
      afterOuterWord geometry round fuelUsed outerUsed innerUsed innerRemaining
        candidateFuel candidateOuter candidateInner input := by
  cases geometry <;>
    simp [outerRewindLeftRev, outerRewindRest, outerResetBaseRev,
      innerSuffix, candidateTail, afterOuterWord,
      Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Rollover.Locator.natPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.reverse_append, List.append_assoc]

theorem outer_rewind_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    RewindWord.machine.runConfigExact?
        ((outerRewindLeftRev geometry round fuelUsed).length + 2)
        (outerRewindSource geometry round fuelUsed outerUsed innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) =
      some (outerRewindTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input) := by
  unfold outerRewindSource outerRewindTarget
  rw [Scheduler.MainRollover.ExactRewind.run_exact]
  rw [outer_rewind_output]

def innerBaseRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed : Nat) : Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.splitPrefixRev 0 outerUsed
    (Scheduler.Rollover.Locator.splitPrefixRev 0 fuelUsed
      (Scheduler.Rollover.Locator.natPrefixRev round
        (Scheduler.Rollover.Locator.geometryPrefixRev geometry)))

def innerLocatorSource (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .header []
    (afterOuterWord geometry round fuelUsed outerUsed innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input)

def innerLocatorTarget (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .halt
    (innerBaseRev geometry round fuelUsed outerUsed)
    (Scheduler.SplitLayout.encodeSplitAppend innerUsed
      (innerRemaining + 1)
      (candidateTail candidateFuel candidateOuter candidateInner input))

def innerLocateSteps (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed : Nat) : Nat :=
  Scheduler.Rollover.Locator.toOuterSteps geometry round 0 fuelUsed +
    Scheduler.Rollover.Locator.splitSteps 0 outerUsed

theorem locate_inner_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    (Scheduler.Rollover.Locator.machine .inner).runConfigExact?
        (innerLocateSteps geometry round fuelUsed outerUsed)
        (innerLocatorSource geometry round fuelUsed outerUsed innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) =
      some (innerLocatorTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input) := by
  unfold innerLocateSteps innerLocatorSource innerLocatorTarget
  rw [show afterOuterWord geometry round fuelUsed outerUsed innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner input =
    MachineCodeSymbol.header ::
      Scheduler.Layout.encodeGeometryAppend geometry
        (MachineDescription.encodeNatAppend round
          (Scheduler.SplitLayout.encodeSplitAppend 0 fuelUsed
            (Scheduler.SplitLayout.encodeSplitAppend 0 outerUsed
              (Scheduler.SplitLayout.encodeSplitAppend innerUsed
                (innerRemaining + 1)
                (candidateTail candidateFuel candidateOuter candidateInner
                  input))))) by rfl]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (Scheduler.Rollover.Locator.machine .inner)
    (Scheduler.Rollover.Locator.toOuterSteps geometry round 0 fuelUsed)
    (Scheduler.Rollover.Locator.splitSteps 0 outerUsed)]
  rw [Scheduler.Rollover.Locator.to_outerUsed_exact .inner geometry
    round 0 fuelUsed
    (Scheduler.SplitLayout.encodeSplitAppend 0 outerUsed
      (Scheduler.SplitLayout.encodeSplitAppend innerUsed
        (innerRemaining + 1)
        (candidateTail candidateFuel candidateOuter candidateInner input)))
    (by decide) (by decide) (by decide)]
  simp only
  rw [Scheduler.Rollover.Locator.split_run_exact .inner
    .outerUsed .outerMarker .outerRemaining .halt 0 outerUsed
    (Scheduler.Rollover.Locator.splitPrefixRev 0 fuelUsed
      (Scheduler.Rollover.Locator.natPrefixRev round
        (Scheduler.Rollover.Locator.geometryPrefixRev geometry)))
    (Scheduler.SplitLayout.encodeSplitAppend innerUsed
      (innerRemaining + 1)
      (candidateTail candidateFuel candidateOuter candidateInner input))
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
  rfl

theorem innerLocatorTarget_tape_eq_splitSource
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    (innerLocatorTarget geometry round fuelUsed outerUsed innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner input).tape =
      (Scheduler.SplitAdvance.sourceConfig innerUsed innerRemaining
        (innerBaseRev geometry round fuelUsed outerUsed)
        (candidateTail candidateFuel candidateOuter candidateInner input)).tape :=
  rfl

theorem inner_split_output_eq_afterInnerWord
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Scheduler.SplitAdvance.outputWord innerUsed innerRemaining
        (innerBaseRev geometry round fuelUsed outerUsed)
        (candidateTail candidateFuel candidateOuter candidateInner input) =
      afterInnerWord geometry round fuelUsed outerUsed innerUsed innerRemaining
        candidateFuel candidateOuter candidateInner input := by
  cases geometry <;>
    simp [Scheduler.SplitAdvance.outputWord, innerBaseRev,
      candidateTail, afterInnerWord, Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.splitPrefixRev,
      Scheduler.Rollover.Locator.natPrefixRev,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.reverse_append, List.append_assoc]

def candidateInnerBaseRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining : Nat) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.natPrefixRev 0
    (Scheduler.Rollover.Locator.natPrefixRev 0
      (Scheduler.Rollover.Locator.candidatePrefixRev geometry round
        0 fuelUsed 0 outerUsed (innerUsed + 1) innerRemaining))

theorem candidate_grow_output_eq_targetWord
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Scheduler.CandidateGrow.growOutput
        (candidateInnerBaseRev geometry round fuelUsed outerUsed innerUsed
          innerRemaining) candidateInner input =
      targetWord geometry round fuelUsed outerUsed innerUsed innerRemaining
        candidateFuel candidateOuter candidateInner input := by
  unfold Word at input ⊢
  cases geometry <;>
    simp [Scheduler.CandidateGrow.growOutput, candidateInnerBaseRev,
      targetWord, Scheduler.Rollover.word,
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
    exact Scheduler.OuterBranch.ticks_append_tick_cons innerUsed _

theorem run_inner_branch
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (sourceWord geometry round fuelUsed outerUsed innerUsed
              innerRemaining candidateFuel candidateOuter candidateInner
              input) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        targetWord geometry round fuelUsed outerUsed innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input ∧
      Tape.Equiv
        (Tape.input
          (targetWord geometry round fuelUsed outerUsed innerUsed
            innerRemaining candidateFuel candidateOuter candidateInner input))
        finalTape := by
  have hfuelSource : Tape.Equiv
      (fuelLocatorSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      (Tape.input
        (sourceWord geometry round fuelUsed outerUsed innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input)) :=
    Tape.Equiv.refl _
  rcases computes_lift_exact_from_equiv
      (Scheduler.Rollover.Locator.machine .fuel) locateFuelEmbed
      locateFuel_map
      (locate_fuel_exact geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input)
      hfuelSource with
    ⟨fuelLocatedTape, hlocateFuel, hfuelLocated⟩
  have hresetFuelSource : Tape.Equiv
      (fuelResetSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      fuelLocatedTape := by
    rw [← fuelLocatorTarget_tape_eq_resetSource]
    exact hfuelLocated
  rcases computes_lift_exact_from_equiv splitResetMachine resetFuelEmbed
      resetFuel_map
      (fuel_reset_exact geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input)
      hresetFuelSource with
    ⟨fuelResetTape, hresetFuel, hfuelReset⟩
  have hrewindFuelSource : Tape.Equiv
      (fuelRewindSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      fuelResetTape :=
    Tape.Equiv.trans
      (fuelResetTarget_tape_equiv_rewindSource geometry round fuelUsed
        outerUsed innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input) hfuelReset
  rcases computes_lift_exact_from_equiv RewindWord.machine rewindFuelEmbed
      rewindFuel_map
      (fuel_rewind_exact geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input)
      hrewindFuelSource with
    ⟨fuelRewoundTape, hrewindFuel, hfuelRewound⟩
  have houterInputToGate : Tape.Equiv
      (outerLocatorSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      (fuelRewindTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape :=
    Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (afterFuelWord geometry round fuelUsed outerUsed innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) 0)
  have hlocateOuterSource : Tape.Equiv
      (outerLocatorSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      fuelRewoundTape :=
    Tape.Equiv.trans houterInputToGate hfuelRewound
  rcases computes_lift_exact_from_equiv
      (Scheduler.Rollover.Locator.machine .outer) locateOuterEmbed
      locateOuter_map
      (locate_outer_exact geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input)
      hlocateOuterSource with
    ⟨outerLocatedTape, hlocateOuter, houterLocated⟩
  have hresetOuterSource : Tape.Equiv
      (outerResetSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      outerLocatedTape := by
    rw [← outerLocatorTarget_tape_eq_resetSource]
    exact houterLocated
  rcases computes_lift_exact_from_equiv splitResetMachine resetOuterEmbed
      resetOuter_map
      (outer_reset_exact geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input)
      hresetOuterSource with
    ⟨outerResetTape, hresetOuter, houterReset⟩
  have hrewindOuterSource : Tape.Equiv
      (outerRewindSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      outerResetTape :=
    Tape.Equiv.trans
      (outerResetTarget_tape_equiv_rewindSource geometry round fuelUsed
        outerUsed innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input) houterReset
  rcases computes_lift_exact_from_equiv RewindWord.machine rewindOuterEmbed
      rewindOuter_map
      (outer_rewind_exact geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input)
      hrewindOuterSource with
    ⟨outerRewoundTape, hrewindOuter, houterRewound⟩
  have hinnerInputToGate : Tape.Equiv
      (innerLocatorSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      (outerRewindTarget geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape :=
    Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (afterOuterWord geometry round fuelUsed outerUsed innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input) 0)
  have hlocateInnerSource : Tape.Equiv
      (innerLocatorSource geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input).tape
      outerRewoundTape :=
    Tape.Equiv.trans hinnerInputToGate houterRewound
  rcases computes_lift_exact_from_equiv
      (Scheduler.Rollover.Locator.machine .inner) locateInnerEmbed
      locateInner_map
      (locate_inner_exact geometry round fuelUsed outerUsed innerUsed
        innerRemaining candidateFuel candidateOuter candidateInner input)
      hlocateInnerSource with
    ⟨innerLocatedTape, hlocateInner, hinnerLocated⟩
  have hsplitSource : Tape.Equiv
      (Scheduler.SplitAdvance.sourceConfig innerUsed innerRemaining
        (innerBaseRev geometry round fuelUsed outerUsed)
        (candidateTail candidateFuel candidateOuter candidateInner input)).tape
      innerLocatedTape := by
    rw [← innerLocatorTarget_tape_eq_splitSource]
    exact hinnerLocated
  rcases Scheduler.SplitAdvance.advance innerUsed innerRemaining
      (innerBaseRev geometry round fuelUsed outerUsed)
      (candidateTail candidateFuel candidateOuter candidateInner input) with
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
        tape := innerLocatedTape }
      { state := Scheduler.SplitAdvance.machine.halt
        tape := actualSplitTape } :=
    TuringMachine.computesIn_to_computes hsplitActualIn
  have hsplitOuter := lift_computes Scheduler.SplitAdvance.machine
    splitInnerEmbed splitInner_map hsplitInner
  have hafterInner : Tape.Equiv
      (Tape.input
        (afterInnerWord geometry round fuelUsed outerUsed innerUsed
          innerRemaining candidateFuel candidateOuter candidateInner input))
      actualSplitTape := by
    rw [← inner_split_output_eq_afterInnerWord]
    exact Tape.Equiv.trans hcanonicalSplit hsplitFinal
  rcases
      Scheduler.CandidatePrefixReset.PrefixMachine.reset_fuel_outer_from_input
        geometry round 0 fuelUsed 0 outerUsed (innerUsed + 1) innerRemaining
        candidateFuel candidateOuter candidateInner input actualSplitTape
        hafterInner with
    ⟨candidateResetTape, hcandidateResetInner, hcandidateResetTape⟩
  have hcandidateReset := lift_computes
    (Scheduler.CandidatePrefixReset.PrefixMachine.machine .outer)
    candidateResetEmbed candidateReset_map hcandidateResetInner
  let growBase := candidateInnerBaseRev geometry round fuelUsed outerUsed
    innerUsed innerRemaining
  have hgrowExact := Scheduler.CandidateGrow.grow_run_of_eq_some
    .candidateInner
    (Scheduler.CandidateGrow.grow_exact growBase candidateInner input)
  have hgrowSource : Tape.Equiv
      (TuringMachine.PhaseEmbedding.liftConfig
        Scheduler.CandidateGrow.growEmbed
        (Scheduler.CandidateGrow.growSource growBase candidateInner
          input)).tape candidateResetTape := by
    simpa [growBase, candidateInnerBaseRev,
      Scheduler.CandidateGrow.growSource,
      Scheduler.CandidatePrefixReset.innerConfig,
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
      (Scheduler.CandidateGrow.machine .candidateInner)
      candidateGrowEmbed candidateGrow_map hgrowExact hgrowSource with
    ⟨finalTape, hgrow, hfinal⟩
  refine ⟨finalTape,
    TuringMachine.computes_trans hlocateFuel
      (TuringMachine.computes_trans hresetFuel
        (TuringMachine.computes_trans hrewindFuel
          (TuringMachine.computes_trans hlocateOuter
            (TuringMachine.computes_trans hresetOuter
              (TuringMachine.computes_trans hrewindOuter
                (TuringMachine.computes_trans hlocateInner
                  (TuringMachine.computes_trans hsplitOuter
                    (TuringMachine.computes_trans hcandidateReset
                      hgrow)))))))), ?_, ?_⟩
  have hcanonicalOutput : Tape.normalizedOutput
      (TuringMachine.PhaseEmbedding.liftConfig candidateGrowEmbed
        (TuringMachine.PhaseEmbedding.liftConfig
          Scheduler.CandidateGrow.growEmbed
          (Scheduler.CandidateGrow.growTarget growBase candidateInner
            input))).tape =
      targetWord geometry round fuelUsed outerUsed innerUsed innerRemaining
        candidateFuel candidateOuter candidateInner input := by
    change Tape.normalizedOutput
      (RewindWord.gateTape
        (Scheduler.CandidateGrow.growOutput growBase candidateInner input)
        0) = _
    rw [Tape.Equiv.normalizedOutput_eq
      (RewindWord.gateTape_equiv_input
        (Scheduler.CandidateGrow.growOutput growBase candidateInner input)
        0)]
    rw [show Scheduler.CandidateGrow.growOutput growBase candidateInner
        input =
      targetWord geometry round fuelUsed outerUsed innerUsed innerRemaining
        candidateFuel candidateOuter candidateInner input by
      exact candidate_grow_output_eq_targetWord geometry round fuelUsed
        outerUsed innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input]
    simpa [Tape.output] using Tape.normalizedOutput_output
      (targetWord geometry round fuelUsed outerUsed innerUsed innerRemaining
        candidateFuel candidateOuter candidateInner input)
  have hnormalized := Tape.Equiv.normalizedOutput_eq hfinal
  exact hnormalized.symm.trans hcanonicalOutput
  have hcanonicalEquiv : Tape.Equiv
      (Tape.input
        (targetWord geometry round fuelUsed outerUsed innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input))
      (TuringMachine.PhaseEmbedding.liftConfig candidateGrowEmbed
        (TuringMachine.PhaseEmbedding.liftConfig
          Scheduler.CandidateGrow.growEmbed
          (Scheduler.CandidateGrow.growTarget growBase candidateInner
            input))).tape := by
    change Tape.Equiv
      (Tape.input
        (targetWord geometry round fuelUsed outerUsed innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input))
      (RewindWord.gateTape
        (Scheduler.CandidateGrow.growOutput growBase candidateInner input)
        0)
    rw [show Scheduler.CandidateGrow.growOutput growBase candidateInner
        input =
      targetWord geometry round fuelUsed outerUsed innerUsed innerRemaining
        candidateFuel candidateOuter candidateInner input by
      exact candidate_grow_output_eq_targetWord geometry round fuelUsed
        outerUsed innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input]
    exact Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (targetWord geometry round fuelUsed outerUsed innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input) 0)
  exact Tape.Equiv.trans hcanonicalEquiv hfinal

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.InnerBranch
