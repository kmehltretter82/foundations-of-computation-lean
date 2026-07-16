import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.DispatchCore

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Dispatch

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

theorem select_fuel
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (scanConfig .header []
          (Scheduler.FuelBranch.sourceWord geometry round fuelUsed
            fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
            candidateFuel candidateOuter candidateInner input))
        { state := branchStart .fuel, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.FuelBranch.sourceWord geometry round fuelUsed
            fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
            candidateFuel candidateOuter candidateInner input)) targetTape := by
  let tail := Scheduler.FuelBranch.tail outerUsed outerRemaining
    innerUsed innerRemaining candidateFuel candidateOuter candidateInner input
  have hprefixExact := scan_to_fuelRemaining_exact geometry round fuelUsed
    (fuelRemaining + 1) tail
  rw [encodeNatAppend_succ] at hprefixExact
  have hprefix : TuringMachine.Computes machine
      (scanConfig .header []
        (Scheduler.FuelBranch.sourceWord geometry round fuelUsed
          fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input))
      (scanConfig .fuelRemaining
        (fuelRemainingPrefixRev geometry round fuelUsed)
        (MachineCodeSymbol.tick ::
          MachineDescription.encodeNatAppend fuelRemaining tail)) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp (by
        simpa [Scheduler.FuelBranch.sourceWord, tail,
          Scheduler.Rollover.word,
          Scheduler.FuelBranch.tail]
          using hprefixExact))
  rcases decision_rewind .fuel .fuelRemaining MachineCodeSymbol.tick
      (fuelRemainingPrefixRev geometry round fuelUsed)
      (MachineDescription.encodeNatAppend fuelRemaining tail) (by rfl) with
    ⟨targetTape, hrewind, htape⟩
  refine ⟨targetTape, TuringMachine.computes_trans hprefix hrewind, ?_⟩
  rw [fuel_decision_word] at htape
  exact htape

theorem select_outer
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (scanConfig .header []
          (Scheduler.OuterBranch.sourceWord geometry round fuelUsed
            outerUsed outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input))
        { state := branchStart .outer, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.OuterBranch.sourceWord geometry round fuelUsed
            outerUsed outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input)) targetTape := by
  let tail := Scheduler.OuterBranch.outerSuffix innerUsed innerRemaining
    candidateFuel candidateOuter candidateInner input
  have hprefixExact := scan_to_outerRemaining_exact geometry round fuelUsed
    outerUsed (outerRemaining + 1) tail
  rw [encodeNatAppend_succ] at hprefixExact
  have hprefix : TuringMachine.Computes machine
      (scanConfig .header []
        (Scheduler.OuterBranch.sourceWord geometry round fuelUsed
          outerUsed outerRemaining innerUsed innerRemaining candidateFuel
          candidateOuter candidateInner input))
      (scanConfig .outerRemaining
        (outerRemainingPrefixRev geometry round fuelUsed outerUsed)
        (MachineCodeSymbol.tick ::
          MachineDescription.encodeNatAppend outerRemaining tail)) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp (by
        simpa [Scheduler.OuterBranch.sourceWord, tail,
          Scheduler.Rollover.word,
          Scheduler.OuterBranch.outerSuffix]
          using hprefixExact))
  rcases decision_rewind .outer .outerRemaining MachineCodeSymbol.tick
      (outerRemainingPrefixRev geometry round fuelUsed outerUsed)
      (MachineDescription.encodeNatAppend outerRemaining tail) (by rfl) with
    ⟨targetTape, hrewind, htape⟩
  refine ⟨targetTape, TuringMachine.computes_trans hprefix hrewind, ?_⟩
  rw [outer_decision_word] at htape
  exact htape

theorem select_inner
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (scanConfig .header []
          (Scheduler.InnerBranch.sourceWord geometry round fuelUsed
            outerUsed innerUsed innerRemaining candidateFuel candidateOuter
            candidateInner input))
        { state := branchStart .inner, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.InnerBranch.sourceWord geometry round fuelUsed
            outerUsed innerUsed innerRemaining candidateFuel candidateOuter
            candidateInner input)) targetTape := by
  let tail := Scheduler.InnerBranch.candidateTail candidateFuel
    candidateOuter candidateInner input
  have hprefixExact := scan_to_innerRemaining_exact geometry round fuelUsed
    outerUsed innerUsed (innerRemaining + 1) tail
  rw [encodeNatAppend_succ] at hprefixExact
  have hprefix : TuringMachine.Computes machine
      (scanConfig .header []
        (Scheduler.InnerBranch.sourceWord geometry round fuelUsed
          outerUsed innerUsed innerRemaining candidateFuel candidateOuter
          candidateInner input))
      (scanConfig .innerRemaining
        (innerRemainingPrefixRev geometry round fuelUsed outerUsed innerUsed)
        (MachineCodeSymbol.tick ::
          MachineDescription.encodeNatAppend innerRemaining tail)) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp (by
        simpa [Scheduler.InnerBranch.sourceWord, tail,
          Scheduler.Rollover.word,
          Scheduler.InnerBranch.candidateTail]
          using hprefixExact))
  rcases decision_rewind .inner .innerRemaining MachineCodeSymbol.tick
      (innerRemainingPrefixRev geometry round fuelUsed outerUsed innerUsed)
      (MachineDescription.encodeNatAppend innerRemaining tail) (by rfl) with
    ⟨targetTape, hrewind, htape⟩
  refine ⟨targetTape, TuringMachine.computes_trans hprefix hrewind, ?_⟩
  rw [inner_decision_word] at htape
  exact htape

theorem select_rollover
    (geometry : Scheduler.Layout.Geometry) (round bound : Nat)
    (input : Word MachineCodeSymbol) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (scanConfig .header []
          (Scheduler.Rollover.sourceWord geometry round bound input))
        { state := branchStart .rollover, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.Rollover.sourceWord geometry round bound input))
        targetTape := by
  let tail := Scheduler.SplitLayout.candidateMarker ::
    MachineDescription.encodeNatAppend round
      (GeneratedCode.nestedStageCode input bound bound)
  have hprefixExact := scan_to_innerRemaining_exact geometry round round bound
    bound 0 tail
  have hzero : MachineDescription.encodeNatAppend 0 tail =
      MachineCodeSymbol.done :: tail := by
    simp [MachineDescription.encodeNatAppend, MachineDescription.encodeNat]
  rw [hzero] at hprefixExact
  have hprefix : TuringMachine.Computes machine
      (scanConfig .header []
        (Scheduler.Rollover.sourceWord geometry round bound input))
      (scanConfig .innerRemaining
        (innerRemainingPrefixRev geometry round round bound bound)
        (MachineCodeSymbol.done :: tail)) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp (by
        simpa [Scheduler.Rollover.sourceWord,
          Scheduler.Rollover.word, tail]
          using hprefixExact))
  rcases decision_rewind .rollover .innerRemaining MachineCodeSymbol.done
      (innerRemainingPrefixRev geometry round round bound bound) tail
      (by rfl) with
    ⟨targetTape, hrewind, htape⟩
  refine ⟨targetTape, TuringMachine.computes_trans hprefix hrewind, ?_⟩
  rw [rollover_decision_word] at htape
  exact htape

theorem scan_start_tape_equiv_input (word : Word MachineCodeSymbol) :
    Tape.Equiv (scanConfig .header [] word).tape (Tape.input word) := by
  cases word with
  | nil =>
      simp [scanConfig, Scheduler.MainRollover.ExactRewind.startTape,
        ExactFuel.StrictProbe.SerializedShift.cursorTape,
        Tape.input, Tape.blank, Tape.Equiv, Tape.dropTrailingNone]
  | cons first rest =>
      simpa [scanConfig, Tape.input,
        ExactFuel.StrictProbe.SerializedShift.cursorTape]
        using
          Scheduler.MainRollover.ExactRewind.startTape_equiv_cursorTape
            ([] : Word MachineCodeSymbol) (first :: rest)

theorem computes_from_input
    {word : Word MachineCodeSymbol} {targetState : Control}
    {targetTape : Tape MachineCodeSymbol}
    (hrun : TuringMachine.Computes machine
      (scanConfig .header [] word)
      { state := targetState, tape := targetTape }) :
    ∃ actualTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start, tape := Tape.input word }
        { state := targetState, tape := actualTape } ∧
      Tape.Equiv targetTape actualTape := by
  rcases TuringMachine.computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hrunIn (scan_start_tape_equiv_input word) with
    ⟨⟨actualState, actualTape⟩, hactual, hstate, htape⟩
  simp only at hstate hactual htape
  subst actualState
  exact ⟨actualTape, TuringMachine.computesIn_to_computes hactual, htape⟩

theorem run_fuel_dispatch
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (Scheduler.FuelBranch.sourceWord geometry round fuelUsed
              fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
              candidateFuel candidateOuter candidateInner input) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        Scheduler.FuelBranch.targetWord geometry round fuelUsed
          fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.FuelBranch.targetWord geometry round fuelUsed
            fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
            candidateFuel candidateOuter candidateInner input)) finalTape := by
  rcases select_fuel geometry round fuelUsed fuelRemaining outerUsed
      outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input with
    ⟨selectedTape, hselectCanonical, hinputSelected⟩
  rcases computes_from_input hselectCanonical with
    ⟨actualSelectedTape, hselect, hselectedActual⟩
  have hbranchSource : Tape.Equiv
      (Tape.input
        (Scheduler.FuelBranch.sourceWord geometry round fuelUsed
          fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
          candidateFuel candidateOuter candidateInner input))
      actualSelectedTape :=
    Tape.Equiv.trans hinputSelected hselectedActual
  rcases Scheduler.FuelBranch.run_fuel_branch geometry round fuelUsed
      fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner input with
    ⟨canonicalFinalTape, hbranchCanonical, hcanonicalOutput,
      hcanonicalTape⟩
  rcases TuringMachine.computes_to_computesIn hbranchCanonical with
    ⟨branchSteps, hbranchCanonicalIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hbranchCanonicalIn hbranchSource with
    ⟨⟨actualFinalState, actualFinalTape⟩, hbranchActualIn,
      hfinalState, hfinalEquiv⟩
  simp only at hfinalState hbranchActualIn hfinalEquiv
  subst actualFinalState
  have hbranchActual : TuringMachine.Computes
      Scheduler.FuelBranch.machine
      { state := Scheduler.FuelBranch.machine.start
        tape := actualSelectedTape }
      { state := Scheduler.FuelBranch.machine.halt
        tape := actualFinalTape } :=
    TuringMachine.computesIn_to_computes hbranchActualIn
  have hbranchLifted := lift_computes Scheduler.FuelBranch.machine
    fuelEmbed fuel_map hbranchActual
  have hbranch : TuringMachine.Computes machine
      { state := branchStart .fuel, tape := actualSelectedTape }
      { state := machine.halt, tape := actualFinalTape } := by
    simpa [branchStart, fuelEmbed, Scheduler.FuelBranch.machine,
      TuringMachine.PhaseEmbedding.liftConfig, machine]
      using hbranchLifted
  refine ⟨actualFinalTape,
    TuringMachine.computes_trans hselect hbranch, ?_,
    Tape.Equiv.trans hcanonicalTape hfinalEquiv⟩
  have hnormalized := Tape.Equiv.normalizedOutput_eq hfinalEquiv
  exact hnormalized.symm.trans hcanonicalOutput

theorem run_outer_dispatch
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (Scheduler.OuterBranch.sourceWord geometry round fuelUsed
              outerUsed outerRemaining innerUsed innerRemaining candidateFuel
              candidateOuter candidateInner input) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        Scheduler.OuterBranch.targetWord geometry round fuelUsed
          outerUsed outerRemaining innerUsed innerRemaining candidateFuel
          candidateOuter candidateInner input ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.OuterBranch.targetWord geometry round fuelUsed
            outerUsed outerRemaining innerUsed innerRemaining candidateFuel
            candidateOuter candidateInner input)) finalTape := by
  rcases select_outer geometry round fuelUsed outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter candidateInner
      input with
    ⟨selectedTape, hselectCanonical, hinputSelected⟩
  rcases computes_from_input hselectCanonical with
    ⟨actualSelectedTape, hselect, hselectedActual⟩
  have hbranchSource : Tape.Equiv
      (Tape.input
        (Scheduler.OuterBranch.sourceWord geometry round fuelUsed
          outerUsed outerRemaining innerUsed innerRemaining candidateFuel
          candidateOuter candidateInner input)) actualSelectedTape :=
    Tape.Equiv.trans hinputSelected hselectedActual
  rcases Scheduler.OuterBranch.run_outer_branch geometry round fuelUsed
      outerUsed outerRemaining innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner input with
    ⟨canonicalFinalTape, hbranchCanonical, hcanonicalOutput,
      hcanonicalTape⟩
  rcases TuringMachine.computes_to_computesIn hbranchCanonical with
    ⟨branchSteps, hbranchCanonicalIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hbranchCanonicalIn hbranchSource with
    ⟨⟨actualFinalState, actualFinalTape⟩, hbranchActualIn,
      hfinalState, hfinalEquiv⟩
  simp only at hfinalState hbranchActualIn hfinalEquiv
  subst actualFinalState
  have hbranchActual : TuringMachine.Computes
      Scheduler.OuterBranch.machine
      { state := Scheduler.OuterBranch.machine.start
        tape := actualSelectedTape }
      { state := Scheduler.OuterBranch.machine.halt
        tape := actualFinalTape } :=
    TuringMachine.computesIn_to_computes hbranchActualIn
  have hbranchLifted := lift_computes Scheduler.OuterBranch.machine
    outerEmbed outer_map hbranchActual
  have hbranch : TuringMachine.Computes machine
      { state := branchStart .outer, tape := actualSelectedTape }
      { state := machine.halt, tape := actualFinalTape } := by
    simpa [branchStart, outerEmbed, Scheduler.OuterBranch.machine,
      TuringMachine.PhaseEmbedding.liftConfig, machine]
      using hbranchLifted
  refine ⟨actualFinalTape,
    TuringMachine.computes_trans hselect hbranch, ?_,
    Tape.Equiv.trans hcanonicalTape hfinalEquiv⟩
  have hnormalized := Tape.Equiv.normalizedOutput_eq hfinalEquiv
  exact hnormalized.symm.trans hcanonicalOutput

theorem run_inner_dispatch
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (Scheduler.InnerBranch.sourceWord geometry round fuelUsed
              outerUsed innerUsed innerRemaining candidateFuel candidateOuter
              candidateInner input) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        Scheduler.InnerBranch.targetWord geometry round fuelUsed
          outerUsed innerUsed innerRemaining candidateFuel candidateOuter
          candidateInner input ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.InnerBranch.targetWord geometry round fuelUsed
            outerUsed innerUsed innerRemaining candidateFuel candidateOuter
            candidateInner input)) finalTape := by
  rcases select_inner geometry round fuelUsed outerUsed innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner input with
    ⟨selectedTape, hselectCanonical, hinputSelected⟩
  rcases computes_from_input hselectCanonical with
    ⟨actualSelectedTape, hselect, hselectedActual⟩
  have hbranchSource : Tape.Equiv
      (Tape.input
        (Scheduler.InnerBranch.sourceWord geometry round fuelUsed
          outerUsed innerUsed innerRemaining candidateFuel candidateOuter
          candidateInner input)) actualSelectedTape :=
    Tape.Equiv.trans hinputSelected hselectedActual
  rcases Scheduler.InnerBranch.run_inner_branch geometry round fuelUsed
      outerUsed innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner input with
    ⟨canonicalFinalTape, hbranchCanonical, hcanonicalOutput,
      hcanonicalTape⟩
  rcases TuringMachine.computes_to_computesIn hbranchCanonical with
    ⟨branchSteps, hbranchCanonicalIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hbranchCanonicalIn hbranchSource with
    ⟨⟨actualFinalState, actualFinalTape⟩, hbranchActualIn,
      hfinalState, hfinalEquiv⟩
  simp only at hfinalState hbranchActualIn hfinalEquiv
  subst actualFinalState
  have hbranchActual : TuringMachine.Computes
      Scheduler.InnerBranch.machine
      { state := Scheduler.InnerBranch.machine.start
        tape := actualSelectedTape }
      { state := Scheduler.InnerBranch.machine.halt
        tape := actualFinalTape } :=
    TuringMachine.computesIn_to_computes hbranchActualIn
  have hbranchLifted := lift_computes Scheduler.InnerBranch.machine
    innerEmbed inner_map hbranchActual
  have hbranch : TuringMachine.Computes machine
      { state := branchStart .inner, tape := actualSelectedTape }
      { state := machine.halt, tape := actualFinalTape } := by
    simpa [branchStart, innerEmbed, Scheduler.InnerBranch.machine,
      TuringMachine.PhaseEmbedding.liftConfig, machine]
      using hbranchLifted
  refine ⟨actualFinalTape,
    TuringMachine.computes_trans hselect hbranch, ?_,
    Tape.Equiv.trans hcanonicalTape hfinalEquiv⟩
  have hnormalized := Tape.Equiv.normalizedOutput_eq hfinalEquiv
  exact hnormalized.symm.trans hcanonicalOutput

theorem run_rollover_dispatch
    (geometry : Scheduler.Layout.Geometry) (round : Nat)
    (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (Scheduler.Rollover.sourceWord geometry round
              (geometry.pairBound round) input) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        Scheduler.Rollover.targetWord geometry round
          (geometry.pairBound (round + 1)) input ∧
      Scheduler.SplitLayout.decode
          (Tape.normalizedOutput finalTape) =
        some (Scheduler.Rollover.targetFrame geometry round input) ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.Rollover.targetWord geometry round
            (geometry.pairBound (round + 1)) input)) finalTape := by
  rcases select_rollover geometry round (geometry.pairBound round) input with
    ⟨selectedTape, hselectCanonical, hinputSelected⟩
  rcases computes_from_input hselectCanonical with
    ⟨actualSelectedTape, hselect, hselectedActual⟩
  have hbranchSource : Tape.Equiv
      (Tape.input
        (Scheduler.Rollover.sourceWord geometry round
          (geometry.pairBound round) input)) actualSelectedTape :=
    Tape.Equiv.trans hinputSelected hselectedActual
  rcases Scheduler.MainRollover.run_main_rollover geometry round input with
    ⟨canonicalFinalTape, hbranchCanonical, hcanonicalEndpoint,
      hcanonicalOutput, hcanonicalDecode⟩
  rcases TuringMachine.computes_to_computesIn hbranchCanonical with
    ⟨branchSteps, hbranchCanonicalIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hbranchCanonicalIn hbranchSource with
    ⟨⟨actualFinalState, actualFinalTape⟩, hbranchActualIn,
      hfinalState, hfinalEquiv⟩
  simp only at hfinalState hbranchActualIn hfinalEquiv
  subst actualFinalState
  have hbranchActual : TuringMachine.Computes
      Scheduler.MainRollover.machine
      { state := Scheduler.MainRollover.machine.start
        tape := actualSelectedTape }
      { state := Scheduler.MainRollover.machine.halt
        tape := actualFinalTape } :=
    TuringMachine.computesIn_to_computes hbranchActualIn
  have hbranchLifted := lift_computes Scheduler.MainRollover.machine
    rolloverEmbed rollover_map hbranchActual
  have hbranch : TuringMachine.Computes machine
      { state := branchStart .rollover, tape := actualSelectedTape }
      { state := .rolloverRewind RewindWord.machine.start,
        tape := actualFinalTape } := by
    simpa [branchStart, rolloverEmbed,
      Scheduler.MainRollover.machine,
      TuringMachine.PhaseEmbedding.liftConfig, machine]
      using hbranchLifted
  have hrewindSource : Tape.Equiv
      (Scheduler.CandidateReset.finalConfig geometry (round + 1)
        (round + 1) (geometry.pairBound (round + 1))
        (geometry.pairBound (round + 1)) input).tape actualFinalTape :=
    Tape.Equiv.trans hcanonicalEndpoint hfinalEquiv
  rcases Scheduler.RolloverRewind.rewind_from_finalConfig_equiv
      geometry round (geometry.pairBound (round + 1)) input
      actualFinalTape hrewindSource with
    ⟨gateTape, hrewindCanonical, hgateEquiv⟩
  have hrewindLifted := lift_computes RewindWord.machine
    rolloverRewindEmbed rolloverRewind_map hrewindCanonical
  have hrewind : TuringMachine.Computes machine
      { state := .rolloverRewind RewindWord.machine.start,
        tape := actualFinalTape }
      { state := machine.halt, tape := gateTape } := by
    simpa [rolloverRewindEmbed, RewindWord.machine,
      TuringMachine.PhaseEmbedding.liftConfig, machine]
      using hrewindLifted
  have houtput : Tape.normalizedOutput gateTape =
      Scheduler.Rollover.targetWord geometry round
        (geometry.pairBound (round + 1)) input := by
    have hnormalized := Tape.Equiv.normalizedOutput_eq hgateEquiv
    exact hnormalized.symm.trans (by
      simpa [Tape.output] using Tape.normalizedOutput_output
        (Scheduler.Rollover.targetWord geometry round
          (geometry.pairBound (round + 1)) input))
  refine ⟨gateTape,
    TuringMachine.computes_trans hselect
      (TuringMachine.computes_trans hbranch hrewind),
    houtput, ?_, hgateEquiv⟩
  rw [houtput]
  rw [← hcanonicalOutput]
  exact hcanonicalDecode

def frame (geometry : Scheduler.Layout.Geometry)
    (round inner outer selectedFuel : Nat)
    (input : Word MachineCodeSymbol) : Scheduler.Layout.Frame :=
  { geometry := geometry
    cursor :=
      { round := round
        inner := inner
        outer := outer
        selectedFuel := selectedFuel }
    input := input }

theorem run_advance
    (geometry : Scheduler.Layout.Geometry)
    (round inner outer selectedFuel : Nat)
    (input : Word MachineCodeSymbol)
    (hvalid :
      (frame geometry round inner outer selectedFuel input).cursor.Valid
        geometry) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (Scheduler.SplitLayout.encode
              (frame geometry round inner outer selectedFuel input)) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.normalizedOutput finalTape =
        Scheduler.SplitLayout.encode
          (frame geometry round inner outer selectedFuel input).advance ∧
      Scheduler.SplitLayout.decode
          (Tape.normalizedOutput finalTape) =
        some (frame geometry round inner outer selectedFuel input).advance ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.SplitLayout.encode
            (frame geometry round inner outer selectedFuel input).advance))
        finalTape := by
  let bound := geometry.pairBound round
  have hbounds : inner ≤ bound ∧ outer ≤ bound ∧
      selectedFuel ≤ round := by
    simpa [frame, bound, Scheduler.Layout.Cursor.Valid] using hvalid
  rcases hbounds with ⟨hinner, houter, hfuel⟩
  by_cases hfuelStep : selectedFuel < round
  · let fuelRemaining := round - selectedFuel - 1
    have hfuelRemaining : round - selectedFuel = fuelRemaining + 1 := by
      dsimp [fuelRemaining]
      lia
    have hfuelAfter : round - (selectedFuel + 1) = fuelRemaining := by
      dsimp [fuelRemaining]
      lia
    have hsource :
        Scheduler.SplitLayout.encode
            (frame geometry round inner outer selectedFuel input) =
          Scheduler.FuelBranch.sourceWord geometry round selectedFuel
            fuelRemaining outer (bound - outer) inner (bound - inner)
            selectedFuel outer inner input := by
      cases geometry <;>
        simp [frame, bound, Scheduler.SplitLayout.encode,
          Scheduler.SplitLayout.candidateWord,
          Scheduler.FuelBranch.sourceWord,
          Scheduler.Rollover.word,
          Scheduler.Layout.Geometry.pairBound, hfuelRemaining]
    have htarget :
        Scheduler.FuelBranch.targetWord geometry round selectedFuel
            fuelRemaining outer (bound - outer) inner (bound - inner)
            selectedFuel outer inner input =
          Scheduler.SplitLayout.encode
            (frame geometry round inner outer selectedFuel input).advance := by
      cases geometry <;>
        simp [frame, bound, Scheduler.Layout.Frame.advance,
          Scheduler.Layout.Cursor.advance, hfuelStep,
          Scheduler.SplitLayout.encode,
          Scheduler.SplitLayout.candidateWord,
          Scheduler.FuelBranch.targetWord,
          Scheduler.Rollover.word,
          Scheduler.Layout.Geometry.pairBound, hfuelAfter]
    rcases run_fuel_dispatch geometry round selectedFuel fuelRemaining outer
        (bound - outer) inner (bound - inner) selectedFuel outer inner input with
      ⟨finalTape, hrun, houtput, hequiv⟩
    refine ⟨finalTape, ?_, houtput.trans htarget, ?_, ?_⟩
    · simpa [hsource] using hrun
    · rw [houtput.trans htarget]
      apply Scheduler.SplitLayout.decode_encode
      exact Scheduler.Layout.Cursor.advance_valid hvalid
    · rw [← htarget]
      exact hequiv
  · have hfuelEnd : selectedFuel = round := by lia
    subst selectedFuel
    by_cases houterStep : outer < bound
    · let outerRemaining := bound - outer - 1
      have houterRemaining : bound - outer = outerRemaining + 1 := by
        dsimp [outerRemaining]
        lia
      have houterAfter : bound - (outer + 1) = outerRemaining := by
        dsimp [outerRemaining]
        lia
      have houterStep' : outer < geometry.pairBound round := by
        simpa [bound] using houterStep
      have houterRemaining' :
          geometry.pairBound round - outer = outerRemaining + 1 := by
        simpa [bound] using houterRemaining
      have houterAfter' :
          geometry.pairBound round - (outer + 1) = outerRemaining := by
        simpa [bound] using houterAfter
      have hsource :
          Scheduler.SplitLayout.encode
              (frame geometry round inner outer round input) =
            Scheduler.OuterBranch.sourceWord geometry round round outer
              outerRemaining inner (bound - inner) round outer inner input := by
        simp [frame, bound, Scheduler.SplitLayout.encode,
          Scheduler.SplitLayout.candidateWord,
          Scheduler.OuterBranch.sourceWord,
          Scheduler.Rollover.word, houterRemaining']
      have htarget :
          Scheduler.OuterBranch.targetWord geometry round round outer
              outerRemaining inner (bound - inner) round outer inner input =
            Scheduler.SplitLayout.encode
              (frame geometry round inner outer round input).advance := by
        simp [frame, bound, Scheduler.Layout.Frame.advance,
          Scheduler.Layout.Cursor.advance, houterStep',
          Scheduler.SplitLayout.encode,
          Scheduler.SplitLayout.candidateWord,
          Scheduler.OuterBranch.targetWord,
          Scheduler.Rollover.word, houterAfter']
      rcases run_outer_dispatch geometry round round outer outerRemaining inner
          (bound - inner) round outer inner input with
        ⟨finalTape, hrun, houtput, hequiv⟩
      refine ⟨finalTape, ?_, houtput.trans htarget, ?_, ?_⟩
      · simpa [hsource] using hrun
      · rw [houtput.trans htarget]
        apply Scheduler.SplitLayout.decode_encode
        exact Scheduler.Layout.Cursor.advance_valid hvalid
      · rw [← htarget]
        exact hequiv
    · have houterEnd : outer = bound := by lia
      subst outer
      by_cases hinnerStep : inner < bound
      · let innerRemaining := bound - inner - 1
        have hinnerRemaining : bound - inner = innerRemaining + 1 := by
          dsimp [innerRemaining]
          lia
        have hinnerAfter : bound - (inner + 1) = innerRemaining := by
          dsimp [innerRemaining]
          lia
        have hinnerStep' : inner < geometry.pairBound round := by
          simpa [bound] using hinnerStep
        have hinnerRemaining' :
            geometry.pairBound round - inner = innerRemaining + 1 := by
          simpa [bound] using hinnerRemaining
        have hinnerAfter' :
            geometry.pairBound round - (inner + 1) = innerRemaining := by
          simpa [bound] using hinnerAfter
        have hsource :
            Scheduler.SplitLayout.encode
                (frame geometry round inner bound round input) =
              Scheduler.InnerBranch.sourceWord geometry round round bound
                inner innerRemaining round bound inner input := by
          simp [frame, bound, Scheduler.SplitLayout.encode,
            Scheduler.SplitLayout.candidateWord,
            Scheduler.InnerBranch.sourceWord,
            Scheduler.Rollover.word, hinnerRemaining']
        have htarget :
            Scheduler.InnerBranch.targetWord geometry round round bound
                inner innerRemaining round bound inner input =
              Scheduler.SplitLayout.encode
                (frame geometry round inner bound round input).advance := by
          simp [frame, bound, Scheduler.Layout.Frame.advance,
            Scheduler.Layout.Cursor.advance, hinnerStep',
            Scheduler.SplitLayout.encode,
            Scheduler.SplitLayout.candidateWord,
            Scheduler.InnerBranch.targetWord,
            Scheduler.Rollover.word, hinnerAfter']
        rcases run_inner_dispatch geometry round round bound inner
            innerRemaining round bound inner input with
          ⟨finalTape, hrun, houtput, hequiv⟩
        refine ⟨finalTape, ?_, houtput.trans htarget, ?_, ?_⟩
        · simpa [hsource] using hrun
        · rw [houtput.trans htarget]
          apply Scheduler.SplitLayout.decode_encode
          exact Scheduler.Layout.Cursor.advance_valid hvalid
        · rw [← htarget]
          exact hequiv
      · have hinnerEnd : inner = bound := by lia
        subst inner
        rcases run_rollover_dispatch geometry round input with
          ⟨finalTape, hrun, houtput, hdecode, hequiv⟩
        have hsource :
            Scheduler.SplitLayout.encode
                (frame geometry round bound bound round input) =
              Scheduler.Rollover.sourceWord geometry round bound input := by
          cases geometry <;>
            simp [frame, bound, Scheduler.SplitLayout.encode,
              Scheduler.SplitLayout.candidateWord,
              Scheduler.Rollover.sourceWord,
              Scheduler.Rollover.word,
              Scheduler.Layout.Geometry.pairBound]
        have htarget :
            Scheduler.Rollover.targetWord geometry round
                (geometry.pairBound (round + 1)) input =
              Scheduler.SplitLayout.encode
                (frame geometry round bound bound round input).advance := by
          cases geometry <;>
            simp [frame, bound, Scheduler.Layout.Frame.advance,
              Scheduler.Layout.Cursor.advance,
              Scheduler.SplitLayout.encode,
              Scheduler.SplitLayout.candidateWord,
              Scheduler.Rollover.targetWord,
              Scheduler.Rollover.word,
              Scheduler.Layout.Geometry.pairBound]
        refine ⟨finalTape, ?_, houtput.trans htarget, ?_, ?_⟩
        · simpa [hsource] using hrun
        · rw [houtput.trans htarget]
          apply Scheduler.SplitLayout.decode_encode
          exact Scheduler.Layout.Cursor.advance_valid hvalid
        · rw [← htarget]
          exact hequiv

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Dispatch
