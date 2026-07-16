import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.SplitAdvance

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.CandidateGrow

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

abbrev LocatorControl := Scheduler.Rollover.Locator.Control

inductive Control where
  | locate (inner : LocatorControl)
  | grow (inner : InsertRestagedMachine.Control)
  | halt
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems :=
    Scheduler.Rollover.Locator.Control.finite.elems.map Control.locate ++
      InsertRestagedMachine.Control.finite.elems.map Control.grow ++ [.halt]
  complete := by
    intro control
    cases control with
    | locate inner =>
        simp
        exact Scheduler.Rollover.Locator.Control.finite.complete inner
    | grow inner =>
        simp
        exact InsertRestagedMachine.Control.finite.complete inner
    | halt => simp

end Control

def growBuffer : InsertBlock.Buffer :=
  Scheduler.Advance.GrowResetInsertion.buffer

def mapAction (embed : inner -> Control) :
    Option (Option MachineCodeSymbol × Direction × inner) ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | none => none
  | some (write, direction, target) =>
      some (write, direction, embed target)

def locateEmbed : LocatorControl -> Control
  | .halt => .grow (InsertRestagedMachine.machine growBuffer).start
  | inner => .locate inner

def growEmbed : InsertRestagedMachine.Control -> Control
  | .rewind .gate => .halt
  | inner => .grow inner

def transition (target : Scheduler.Rollover.Locator.Target) :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate inner, read =>
      mapAction locateEmbed
        (Scheduler.Rollover.Locator.transition target inner read)
  | .grow inner, read =>
      mapAction growEmbed (InsertRestagedMachine.transition inner read)
  | .halt, _ => none

def machine (target : Scheduler.Rollover.Locator.Target) :
    TuringMachine MachineCodeSymbol Control where
  start := .locate .header
  halt := .halt
  transition := transition target
  statesFinite := Control.finite

theorem step_of_mapped_transition
    {innerState : Type}
    (target : Scheduler.Rollover.Locator.Target)
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hmap : ∀ (state : innerState) (read : Option MachineCodeSymbol)
        (action : Option MachineCodeSymbol × Direction × innerState),
      inner.transition state read = some action ->
      transition target (embed state) read = mapAction embed (some action))
    (source destination :
      TuringMachine.Configuration MachineCodeSymbol innerState)
    (hstep : inner.stepConfig source = some destination) :
    (machine target).stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig embed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed destination) := by
  cases source with
  | mk state tape =>
      cases destination with
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

theorem locate_map (target : Scheduler.Rollover.Locator.Target)
    (state : LocatorControl) (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × LocatorControl)
    (haction : (Scheduler.Rollover.Locator.machine target).transition
      state read = some action) :
    transition target (locateEmbed state) read =
      mapAction locateEmbed (some action) := by
  cases state <;>
    simp_all [Scheduler.Rollover.Locator.machine,
      Scheduler.Rollover.Locator.transition, transition,
      locateEmbed, mapAction]

theorem grow_map (target : Scheduler.Rollover.Locator.Target)
    (state : InsertRestagedMachine.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      InsertRestagedMachine.Control)
    (haction : (InsertRestagedMachine.machine growBuffer).transition
      state read = some action) :
    transition target (growEmbed state) read =
      mapAction growEmbed (some action) := by
  cases state with
  | edit inner =>
      cases inner <;>
        simp_all [InsertRestagedMachine.machine,
          InsertRestagedMachine.transition, transition, growEmbed, mapAction]
  | rewind inner =>
      cases inner <;>
        simp_all [InsertRestagedMachine.machine,
          InsertRestagedMachine.transition, RewindWord.transition,
          transition, growEmbed, mapAction]

theorem locate_run_of_eq_some
    (target : Scheduler.Rollover.Locator.Target) {steps : Nat}
    {source destination :
      TuringMachine.Configuration MachineCodeSymbol LocatorControl}
    (hrun : (Scheduler.Rollover.Locator.machine target).runConfigExact?
      steps source = some destination) :
    (machine target).runConfigExact? steps
        (TuringMachine.PhaseEmbedding.liftConfig locateEmbed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig locateEmbed
        destination) := by
  exact TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    locateEmbed
    (step_of_mapped_transition target
      (Scheduler.Rollover.Locator.machine target) locateEmbed
      (locate_map target)) hrun

theorem grow_run_of_eq_some
    (target : Scheduler.Rollover.Locator.Target) {steps : Nat}
    {source destination : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control}
    (hrun : (InsertRestagedMachine.machine growBuffer).runConfigExact?
      steps source = some destination) :
    (machine target).runConfigExact? steps
        (TuringMachine.PhaseEmbedding.liftConfig growEmbed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig growEmbed
        destination) := by
  exact TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    growEmbed
    (step_of_mapped_transition target
      (InsertRestagedMachine.machine growBuffer) growEmbed
      (grow_map target)) hrun

def growSource (leftRev : Word MachineCodeSymbol) (count : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  InsertRestagedMachine.editConfig
    (InsertBlock.config growBuffer leftRev
      (MachineDescription.encodeNatAppend count suffix))

def growOutput (leftRev : Word MachineCodeSymbol) (count : Nat)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append leftRev.reverse
    (MachineDescription.encodeNatAppend (count + 1) suffix)

def growTarget (leftRev : Word MachineCodeSymbol) (count : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  InsertRestagedMachine.rewindConfig
    (RewindWord.gateConfig (growOutput leftRev count suffix) 0)

def growSteps (leftRev : Word MachineCodeSymbol) (count : Nat)
    (suffix : Word MachineCodeSymbol) : Nat :=
  InsertRestagedMachine.runSteps growBuffer leftRev
    (MachineDescription.encodeNatAppend count suffix)

theorem insert_output_eq_growOutput (leftRev : Word MachineCodeSymbol)
    (count : Nat) (suffix : Word MachineCodeSymbol) :
    PhysicalBranch.insertOutput growBuffer leftRev
        (MachineDescription.encodeNatAppend count suffix) =
      growOutput leftRev count suffix := by
  simp [PhysicalBranch.insertOutput, growBuffer,
    Scheduler.Advance.GrowResetInsertion.buffer,
    InsertBlock.singletonBuffer, growOutput,
    MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
    List.append_assoc]

theorem grow_exact (leftRev : Word MachineCodeSymbol) (count : Nat)
    (suffix : Word MachineCodeSymbol) :
    (InsertRestagedMachine.machine growBuffer).runConfigExact?
        (growSteps leftRev count suffix)
        (growSource leftRev count suffix) =
      some (growTarget leftRev count suffix) := by
  unfold growSteps growSource growTarget
  rw [InsertRestagedMachine.run_exact growBuffer leftRev
    (MachineDescription.encodeNatAppend count suffix)]
  · rw [insert_output_eq_growOutput]
  · simp [growBuffer, Scheduler.Advance.GrowResetInsertion.buffer,
      InsertBlock.singletonBuffer]

def schedulerWord (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.Rollover.word geometry round fuelUsed fuelRemaining
    outerUsed outerRemaining innerUsed innerRemaining candidateFuel
    candidateOuter candidateInner input

def candidatePrefixRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining : Nat) : Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.candidatePrefixRev geometry round
    fuelUsed fuelRemaining outerUsed outerRemaining innerUsed innerRemaining

def candidateTail (candidateFuel candidateOuter candidateInner : Nat)
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

theorem schedulerWord_eq_layout
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    schedulerWord geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input =
      MachineCodeSymbol.header ::
        Scheduler.Layout.encodeGeometryAppend geometry
          (MachineDescription.encodeNatAppend round
            (Scheduler.SplitLayout.encodeSplitAppend fuelUsed
              fuelRemaining
              (Scheduler.SplitLayout.encodeSplitAppend outerUsed
                outerRemaining
                (Scheduler.SplitLayout.encodeSplitAppend innerUsed
                  innerRemaining
                  (Scheduler.SplitLayout.candidateMarker ::
                    candidateTail candidateFuel candidateOuter candidateInner
                      input))))) := by
  rfl

theorem grow_candidateFuel
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine .candidateFuel)
        { state := (machine .candidateFuel).start
          tape := Tape.input
            (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining candidateFuel
              candidateOuter candidateInner input) }
        { state := (machine .candidateFuel).halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        schedulerWord geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining (candidateFuel + 1)
          candidateOuter candidateInner input ∧
      Tape.Equiv
        (Tape.input
          (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining (candidateFuel + 1)
            candidateOuter candidateInner input)) finalTape := by
  let baseRev := candidatePrefixRev geometry round fuelUsed fuelRemaining
    outerUsed outerRemaining innerUsed innerRemaining
  let suffix := MachineDescription.encodeNatAppend candidateOuter
    (MachineDescription.encodeNatAppend candidateInner input)
  have hlocate := locate_run_of_eq_some .candidateFuel
    (Scheduler.Rollover.Locator.locate_candidateFuel_exact geometry
      round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
      innerRemaining (candidateTail candidateFuel candidateOuter
        candidateInner input))
  have hgrowSource :
      TuringMachine.PhaseEmbedding.liftConfig locateEmbed
          (Scheduler.Rollover.Locator.config .halt baseRev
            (MachineDescription.encodeNatAppend candidateFuel suffix)) =
        TuringMachine.PhaseEmbedding.liftConfig growEmbed
          (growSource baseRev candidateFuel suffix) := by
    rfl
  have hgrow := grow_run_of_eq_some .candidateFuel
    (grow_exact baseRev candidateFuel suffix)
  have hrun : TuringMachine.Computes (machine .candidateFuel)
      { state := (machine .candidateFuel).start
        tape := Tape.input
          (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input) }
      (TuringMachine.PhaseEmbedding.liftConfig growEmbed
        (growTarget baseRev candidateFuel suffix)) := by
    have hlocate' : TuringMachine.Computes (machine .candidateFuel)
        { state := (machine .candidateFuel).start
          tape := Tape.input
            (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining candidateFuel
              candidateOuter candidateInner input) }
        (TuringMachine.PhaseEmbedding.liftConfig locateEmbed
          (Scheduler.Rollover.Locator.config .halt baseRev
            (MachineDescription.encodeNatAppend candidateFuel suffix))) :=
      TuringMachine.computesIn_to_computes
        (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp (by
          simpa [machine, schedulerWord, candidateTail, suffix, baseRev,
            candidatePrefixRev, locateEmbed, nestedStageCode_eq_tail,
            Scheduler.Rollover.word,
            Scheduler.Rollover.Locator.config,
            TuringMachine.PhaseEmbedding.liftConfig,
            ExactFuel.StrictProbe.SerializedShift.cursorTape, Tape.input]
            using hlocate))
    rw [hgrowSource] at hlocate'
    exact TuringMachine.computes_trans hlocate'
      (TuringMachine.computesIn_to_computes
        (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hgrow))
  let finalTape :=
      (TuringMachine.PhaseEmbedding.liftConfig growEmbed
      (growTarget baseRev candidateFuel suffix)).tape
  have houtput : growOutput baseRev candidateFuel suffix =
      schedulerWord geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining (candidateFuel + 1)
        candidateOuter candidateInner input := by
    cases geometry <;>
      simp [schedulerWord, growOutput, baseRev, suffix,
        candidatePrefixRev, candidateTail, nestedStageCode_eq_tail,
        Scheduler.Rollover.word,
        Scheduler.Rollover.Locator.candidatePrefixRev,
        Scheduler.Rollover.Locator.splitPrefixRev,
        Scheduler.Rollover.Locator.natPrefixRev,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.SplitLayout.encodeSplitAppend,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
        List.reverse_append, List.append_assoc]
  refine ⟨finalTape, hrun, ?_, ?_⟩
  change Tape.normalizedOutput
      (RewindWord.gateTape (growOutput baseRev candidateFuel suffix) 0) = _
  rw [Tape.Equiv.normalizedOutput_eq
    (RewindWord.gateTape_equiv_input
      (growOutput baseRev candidateFuel suffix) 0)]
  rw [houtput]
  simpa [Tape.output] using Tape.normalizedOutput_output
    (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
      outerRemaining innerUsed innerRemaining (candidateFuel + 1)
      candidateOuter candidateInner input)
  change Tape.Equiv
    (Tape.input
      (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining (candidateFuel + 1)
        candidateOuter candidateInner input))
    (RewindWord.gateTape (growOutput baseRev candidateFuel suffix) 0)
  rw [← houtput]
  exact Tape.Equiv.symm
    (RewindWord.gateTape_equiv_input
      (growOutput baseRev candidateFuel suffix) 0)

theorem grow_candidateOuter
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine .candidateOuter)
        { state := (machine .candidateOuter).start
          tape := Tape.input
            (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining candidateFuel
              candidateOuter candidateInner input) }
        { state := (machine .candidateOuter).halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        schedulerWord geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateFuel
          (candidateOuter + 1) candidateInner input ∧
      Tape.Equiv
        (Tape.input
          (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateFuel
            (candidateOuter + 1) candidateInner input)) finalTape := by
  let baseRev := Scheduler.Rollover.Locator.natPrefixRev candidateFuel
    (candidatePrefixRev geometry round fuelUsed fuelRemaining outerUsed
      outerRemaining innerUsed innerRemaining)
  let suffix := MachineDescription.encodeNatAppend candidateInner input
  have hlocate := locate_run_of_eq_some .candidateOuter
    (Scheduler.Rollover.Locator.locate_candidateOuter_exact geometry
      round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
      innerRemaining candidateFuel
      (MachineDescription.encodeNatAppend candidateOuter suffix))
  have hgrowSource :
      TuringMachine.PhaseEmbedding.liftConfig locateEmbed
          (Scheduler.Rollover.Locator.config .halt baseRev
            (MachineDescription.encodeNatAppend candidateOuter suffix)) =
        TuringMachine.PhaseEmbedding.liftConfig growEmbed
          (growSource baseRev candidateOuter suffix) := by
    rfl
  have hgrow := grow_run_of_eq_some .candidateOuter
    (grow_exact baseRev candidateOuter suffix)
  have hlocate' : TuringMachine.Computes (machine .candidateOuter)
      { state := (machine .candidateOuter).start
        tape := Tape.input
          (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input) }
      (TuringMachine.PhaseEmbedding.liftConfig locateEmbed
        (Scheduler.Rollover.Locator.config .halt baseRev
          (MachineDescription.encodeNatAppend candidateOuter suffix))) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp (by
        simpa [machine, schedulerWord, candidateTail, suffix, baseRev,
          candidatePrefixRev, locateEmbed, nestedStageCode_eq_tail,
          Scheduler.Rollover.word,
          Scheduler.Rollover.Locator.config,
          TuringMachine.PhaseEmbedding.liftConfig,
          ExactFuel.StrictProbe.SerializedShift.cursorTape, Tape.input]
          using hlocate))
  rw [hgrowSource] at hlocate'
  have hrun := TuringMachine.computes_trans hlocate'
    (TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hgrow))
  let finalTape :=
    (TuringMachine.PhaseEmbedding.liftConfig growEmbed
      (growTarget baseRev candidateOuter suffix)).tape
  have houtput : growOutput baseRev candidateOuter suffix =
      schedulerWord geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel
        (candidateOuter + 1) candidateInner input := by
    cases geometry <;>
      simp [schedulerWord, growOutput, baseRev, suffix,
        candidatePrefixRev, nestedStageCode_eq_tail,
        Scheduler.Rollover.word,
        Scheduler.Rollover.Locator.candidatePrefixRev,
        Scheduler.Rollover.Locator.splitPrefixRev,
        Scheduler.Rollover.Locator.natPrefixRev,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.SplitLayout.encodeSplitAppend,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
        List.reverse_append, List.append_assoc]
  refine ⟨finalTape, hrun, ?_, ?_⟩
  change Tape.normalizedOutput
      (RewindWord.gateTape (growOutput baseRev candidateOuter suffix) 0) = _
  rw [Tape.Equiv.normalizedOutput_eq
    (RewindWord.gateTape_equiv_input
      (growOutput baseRev candidateOuter suffix) 0)]
  rw [houtput]
  simpa [Tape.output] using Tape.normalizedOutput_output
    (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
      outerRemaining innerUsed innerRemaining candidateFuel
      (candidateOuter + 1) candidateInner input)
  change Tape.Equiv
    (Tape.input
      (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel
        (candidateOuter + 1) candidateInner input))
    (RewindWord.gateTape (growOutput baseRev candidateOuter suffix) 0)
  rw [← houtput]
  exact Tape.Equiv.symm
    (RewindWord.gateTape_equiv_input
      (growOutput baseRev candidateOuter suffix) 0)

theorem grow_candidateInner
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat) (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (machine .candidateInner)
        { state := (machine .candidateInner).start
          tape := Tape.input
            (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
              outerRemaining innerUsed innerRemaining candidateFuel
              candidateOuter candidateInner input) }
        { state := (machine .candidateInner).halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        schedulerWord geometry round fuelUsed fuelRemaining outerUsed
          outerRemaining innerUsed innerRemaining candidateFuel
          candidateOuter (candidateInner + 1) input ∧
      Tape.Equiv
        (Tape.input
          (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter (candidateInner + 1) input)) finalTape := by
  let baseRev := Scheduler.Rollover.Locator.natPrefixRev candidateOuter
    (Scheduler.Rollover.Locator.natPrefixRev candidateFuel
      (candidatePrefixRev geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining))
  let suffix := input
  have hlocate := locate_run_of_eq_some .candidateInner
    (Scheduler.Rollover.Locator.locate_candidateInner_exact geometry
      round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
      innerRemaining candidateFuel candidateOuter
      (MachineDescription.encodeNatAppend candidateInner input))
  have hgrowSource :
      TuringMachine.PhaseEmbedding.liftConfig locateEmbed
          (Scheduler.Rollover.Locator.config .halt baseRev
            (MachineDescription.encodeNatAppend candidateInner suffix)) =
        TuringMachine.PhaseEmbedding.liftConfig growEmbed
          (growSource baseRev candidateInner suffix) := by
    rfl
  have hgrow := grow_run_of_eq_some .candidateInner
    (grow_exact baseRev candidateInner suffix)
  have hlocate' : TuringMachine.Computes (machine .candidateInner)
      { state := (machine .candidateInner).start
        tape := Tape.input
          (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
            outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input) }
      (TuringMachine.PhaseEmbedding.liftConfig locateEmbed
        (Scheduler.Rollover.Locator.config .halt baseRev
          (MachineDescription.encodeNatAppend candidateInner suffix))) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp (by
        simpa [machine, schedulerWord, candidateTail, suffix, baseRev,
          candidatePrefixRev, locateEmbed, nestedStageCode_eq_tail,
          Scheduler.Rollover.word,
          Scheduler.Rollover.Locator.config,
          TuringMachine.PhaseEmbedding.liftConfig,
          ExactFuel.StrictProbe.SerializedShift.cursorTape, Tape.input]
          using hlocate))
  rw [hgrowSource] at hlocate'
  have hrun := TuringMachine.computes_trans hlocate'
    (TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hgrow))
  let finalTape :=
    (TuringMachine.PhaseEmbedding.liftConfig growEmbed
      (growTarget baseRev candidateInner suffix)).tape
  have houtput : growOutput baseRev candidateInner suffix =
      schedulerWord geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        (candidateInner + 1) input := by
    cases geometry <;>
      simp [schedulerWord, growOutput, baseRev, suffix,
        candidatePrefixRev, nestedStageCode_eq_tail,
        Scheduler.Rollover.word,
        Scheduler.Rollover.Locator.candidatePrefixRev,
        Scheduler.Rollover.Locator.splitPrefixRev,
        Scheduler.Rollover.Locator.natPrefixRev,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.SplitLayout.encodeSplitAppend,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
        List.reverse_append, List.append_assoc]
  refine ⟨finalTape, hrun, ?_, ?_⟩
  change Tape.normalizedOutput
      (RewindWord.gateTape (growOutput baseRev candidateInner suffix) 0) = _
  rw [Tape.Equiv.normalizedOutput_eq
    (RewindWord.gateTape_equiv_input
      (growOutput baseRev candidateInner suffix) 0)]
  rw [houtput]
  simpa [Tape.output] using Tape.normalizedOutput_output
    (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
      outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
      (candidateInner + 1) input)
  change Tape.Equiv
    (Tape.input
      (schedulerWord geometry round fuelUsed fuelRemaining outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        (candidateInner + 1) input))
    (RewindWord.gateTape (growOutput baseRev candidateInner suffix) 0)
  rw [← houtput]
  exact Tape.Equiv.symm
    (RewindWord.gateTape_equiv_input
      (growOutput baseRev candidateInner suffix) 0)

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.CandidateGrow
