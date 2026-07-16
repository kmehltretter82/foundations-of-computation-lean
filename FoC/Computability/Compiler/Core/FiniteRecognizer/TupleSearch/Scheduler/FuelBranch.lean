import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.CandidatePrefixReset

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.FuelBranch

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

abbrev LocatorControl := Scheduler.Rollover.Locator.Control
abbrev SplitControl := Scheduler.SplitAdvance.Control
abbrev CandidateGrowControl := Scheduler.CandidateGrow.Control

inductive Control where
  | locate (inner : LocatorControl)
  | split (inner : SplitControl)
  | candidate (inner : CandidateGrowControl)
  | halt
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems :=
    Scheduler.Rollover.Locator.Control.finite.elems.map Control.locate ++
      Scheduler.SplitAdvance.Control.finite.elems.map Control.split ++
      Scheduler.CandidateGrow.Control.finite.elems.map
        Control.candidate ++ [.halt]
  complete := by
    intro control
    cases control with
    | locate inner =>
        simp
        exact Scheduler.Rollover.Locator.Control.finite.complete inner
    | split inner =>
        simp
        exact Scheduler.SplitAdvance.Control.finite.complete inner
    | candidate inner =>
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

def locateEmbed : LocatorControl -> Control
  | .halt => .split Scheduler.SplitAdvance.machine.start
  | inner => .locate inner

def splitEmbed : SplitControl -> Control
  | .rewind .gate =>
      .candidate
        (Scheduler.CandidateGrow.machine .candidateFuel).start
  | inner => .split inner

def candidateEmbed : CandidateGrowControl -> Control
  | .halt => .halt
  | inner => .candidate inner

def transition : Control -> Option MachineCodeSymbol ->
    Option (Option MachineCodeSymbol × Direction × Control)
  | .locate inner, read =>
      mapAction locateEmbed
        (Scheduler.Rollover.Locator.transition .fuel inner read)
  | .split inner, read =>
      mapAction splitEmbed
        (Scheduler.SplitAdvance.transition inner read)
  | .candidate inner, read =>
      mapAction candidateEmbed
        (Scheduler.CandidateGrow.transition .candidateFuel inner read)
  | .halt, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .locate .header
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

theorem locate_map (state : LocatorControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × LocatorControl)
    (haction : (Scheduler.Rollover.Locator.machine .fuel).transition
      state read = some action) :
    transition (locateEmbed state) read =
      mapAction locateEmbed (some action) := by
  cases state <;>
    simp_all [Scheduler.Rollover.Locator.machine,
      Scheduler.Rollover.Locator.transition, transition,
      locateEmbed, mapAction]

theorem split_map (state : SplitControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × SplitControl)
    (haction : Scheduler.SplitAdvance.machine.transition state read =
      some action) :
    transition (splitEmbed state) read =
      mapAction splitEmbed (some action) := by
  cases state with
  | used =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitEmbed,
        mapAction]
  | marker =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitEmbed,
        mapAction]
  | takeRemaining =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitEmbed,
        mapAction]
  | writeDone =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitEmbed,
        mapAction]
  | writeTick =>
      simp_all [Scheduler.SplitAdvance.machine,
        Scheduler.SplitAdvance.transition, transition, splitEmbed,
        mapAction]
  | rewind inner =>
      cases inner <;>
        simp_all [Scheduler.SplitAdvance.machine,
          Scheduler.SplitAdvance.transition, RewindWord.transition,
          transition, splitEmbed, mapAction,
          Scheduler.SplitAdvance.mapAction]

theorem candidate_map (state : CandidateGrowControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      CandidateGrowControl)
    (haction : (Scheduler.CandidateGrow.machine .candidateFuel).transition
      state read = some action) :
    transition (candidateEmbed state) read =
      mapAction candidateEmbed (some action) := by
  cases state with
  | locate inner =>
      cases inner <;>
        simp_all [Scheduler.CandidateGrow.machine,
          Scheduler.CandidateGrow.transition,
          Scheduler.CandidateGrow.mapAction,
          Scheduler.CandidateGrow.locateEmbed,
          Scheduler.Rollover.Locator.transition,
          transition, candidateEmbed, mapAction]
  | grow inner =>
      cases inner with
      | edit editInner =>
          cases editInner <;>
            simp_all [Scheduler.CandidateGrow.machine,
              Scheduler.CandidateGrow.transition,
              Scheduler.CandidateGrow.mapAction,
              Scheduler.CandidateGrow.growEmbed,
              InsertRestagedMachine.transition,
              transition, candidateEmbed, mapAction]
      | rewind rewindInner =>
          cases rewindInner <;>
            simp_all [Scheduler.CandidateGrow.machine,
              Scheduler.CandidateGrow.transition,
              Scheduler.CandidateGrow.mapAction,
              Scheduler.CandidateGrow.growEmbed,
              InsertRestagedMachine.transition, RewindWord.transition,
              transition, candidateEmbed, mapAction]
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

theorem locate_fuel_exact
    (geometry : Scheduler.Layout.Geometry) (round : Nat)
    (suffix : Word MachineCodeSymbol) :
    (Scheduler.Rollover.Locator.machine .fuel).runConfigExact?
        (Scheduler.Rollover.Locator.geometrySteps geometry +
          (round + 1))
        (Scheduler.Rollover.Locator.config .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round suffix))) =
      some (Scheduler.Rollover.Locator.config .halt
        (Scheduler.Rollover.Locator.natPrefixRev round
          (Scheduler.Rollover.Locator.geometryPrefixRev geometry))
        suffix) := by
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (Scheduler.Rollover.Locator.machine .fuel)
    (Scheduler.Rollover.Locator.geometrySteps geometry) (round + 1)]
  unfold Scheduler.Rollover.Locator.geometrySteps
  rw [Scheduler.Rollover.Locator.geometry_to_round_exact .fuel geometry
    (MachineDescription.encodeNatAppend round suffix) (by decide)]
  simp only
  rw [Scheduler.Rollover.Locator.nat_run_exact .fuel .round .halt
    round
    (MachineCodeSymbol.header ::
      Scheduler.Layout.encodeGeometryAppend geometry []).reverse
    suffix (by rfl) (by rfl)]
  rfl

def tail (outerUsed outerRemaining innerUsed innerRemaining
    candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  Scheduler.SplitLayout.encodeSplitAppend outerUsed outerRemaining
    (Scheduler.SplitLayout.encodeSplitAppend innerUsed innerRemaining
      (Scheduler.SplitLayout.candidateMarker ::
        MachineDescription.encodeNatAppend candidateFuel
          (GeneratedCode.nestedStageCode input candidateInner
            candidateOuter)))

def sourceWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round fuelUsed (fuelRemaining + 1)
    outerUsed outerRemaining innerUsed innerRemaining candidateFuel
    candidateOuter candidateInner input

def afterMainWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round (fuelUsed + 1) fuelRemaining
    outerUsed outerRemaining innerUsed innerRemaining candidateFuel
    candidateOuter candidateInner input

def targetWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round (fuelUsed + 1) fuelRemaining
    outerUsed outerRemaining innerUsed innerRemaining (candidateFuel + 1)
    candidateOuter candidateInner input

theorem split_output_eq_afterMainWord
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Scheduler.SplitAdvance.outputWord fuelUsed fuelRemaining
        (Scheduler.Rollover.Locator.natPrefixRev round
          (Scheduler.Rollover.Locator.geometryPrefixRev geometry))
        (tail outerUsed outerRemaining innerUsed innerRemaining candidateFuel
          candidateOuter candidateInner input) =
      afterMainWord geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input := by
  cases geometry <;>
    simp [Scheduler.SplitAdvance.outputWord, afterMainWord, tail,
      Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.natPrefixRev,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.reverse_append, List.append_assoc]

theorem run_fuel_branch
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (sourceWord geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining candidateFuel
              candidateOuter candidateInner input) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        targetWord geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
          candidateInner input ∧
      Tape.Equiv
        (Tape.input
          (targetWord geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input)) finalTape := by
  let baseRev := Scheduler.Rollover.Locator.natPrefixRev round
    (Scheduler.Rollover.Locator.geometryPrefixRev geometry)
  let suffix := tail outerUsed outerRemaining innerUsed innerRemaining
    candidateFuel candidateOuter candidateInner input
  have hlocateInner := locate_fuel_exact geometry round
    (Scheduler.SplitLayout.encodeSplitAppend fuelUsed
      (fuelRemaining + 1) suffix)
  have hlocateOuter :=
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      locateEmbed
      (step_of_mapped_transition
        (Scheduler.Rollover.Locator.machine .fuel) locateEmbed
        locate_map) hlocateInner
  have hlocate : TuringMachine.Computes machine
      { state := machine.start
        tape := Tape.input
          (sourceWord geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input) }
      (TuringMachine.PhaseEmbedding.liftConfig splitEmbed
        (Scheduler.SplitAdvance.sourceConfig fuelUsed fuelRemaining
          baseRev suffix)) := by
    apply TuringMachine.computesIn_to_computes
    apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
    simpa [machine, sourceWord, baseRev, suffix, tail,
      Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.config,
      Scheduler.SplitAdvance.sourceConfig,
      Scheduler.SplitAdvance.machine,
      TuringMachine.PhaseEmbedding.liftConfig,
      locateEmbed, splitEmbed, Tape.input,
      ExactFuel.StrictProbe.SerializedShift.cursorTape]
      using hlocateOuter
  rcases Scheduler.SplitAdvance.advance fuelUsed fuelRemaining
      baseRev suffix with ⟨splitTape, hsplitInner, hsplitTape⟩
  have hsplit := lift_computes Scheduler.SplitAdvance.machine splitEmbed
    split_map hsplitInner
  have hafterMain : Tape.Equiv
      (Tape.input
        (afterMainWord geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
          candidateInner input)) splitTape := by
    rw [← split_output_eq_afterMainWord]
    exact hsplitTape
  rcases Scheduler.CandidateGrow.grow_candidateFuel geometry round
      (fuelUsed + 1) fuelRemaining outerUsed outerRemaining innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner input with
    ⟨canonicalFinal, hcandidateCanonical, hcanonicalOutput,
      hcanonicalEquiv⟩
  rcases TuringMachine.computes_to_computesIn hcandidateCanonical with
    ⟨candidateSteps, hcandidateIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcandidateIn hafterMain with
    ⟨actualFinal, hcandidateActual, hstate, hfinalEquiv⟩
  rcases actualFinal with ⟨actualState, actualTape⟩
  simp only at hstate hcandidateActual hfinalEquiv ⊢
  subst actualState
  have hcandidateInner : TuringMachine.Computes
      (Scheduler.CandidateGrow.machine .candidateFuel)
      { state := (Scheduler.CandidateGrow.machine .candidateFuel).start
        tape := splitTape }
      { state := (Scheduler.CandidateGrow.machine .candidateFuel).halt
        tape := actualTape } :=
    TuringMachine.computesIn_to_computes hcandidateActual
  have hcandidate := lift_computes
    (Scheduler.CandidateGrow.machine .candidateFuel) candidateEmbed
    candidate_map hcandidateInner
  let finalTape := actualTape
  refine ⟨finalTape,
    TuringMachine.computes_trans hlocate
      (TuringMachine.computes_trans hsplit hcandidate), ?_, ?_⟩
  · have hnormalized := Tape.Equiv.normalizedOutput_eq hfinalEquiv
    exact hnormalized.symm.trans hcanonicalOutput
  · exact Tape.Equiv.trans hcanonicalEquiv hfinalEquiv

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.FuelBranch
