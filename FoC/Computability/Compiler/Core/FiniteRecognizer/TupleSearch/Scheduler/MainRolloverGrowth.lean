import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.MainRolloverCore

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.MainRollover

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Scheduler.Rollover

def outerSuffix (round bound : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.SplitLayout.encodeSplitAppend bound 0
    (Scheduler.SplitLayout.candidateMarker ::
      MachineDescription.encodeNatAppend round
        (GeneratedCode.nestedStageCode input bound bound))

def outerPrefixRev (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.splitPrefixRev 0 (round + 1)
    (Scheduler.Rollover.Locator.natPrefixRev (round + 1)
      (Scheduler.Rollover.Locator.geometryPrefixRev geometry))

def outerBaseRev (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Word MachineCodeSymbol :=
  List.append
    (Scheduler.Advance.ExhaustedSplitReset.ticks (round + 1))
    (Scheduler.SplitLayout.splitMarker ::
      Scheduler.Rollover.Locator.natPrefixRev 0
        (Scheduler.Rollover.Locator.natPrefixRev (round + 1)
          (Scheduler.Rollover.Locator.geometryPrefixRev geometry)))

def outerLocatorSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .header []
    (Scheduler.Rollover.afterFuelWord geometry round bound input)

def outerLocatorTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .halt
    (outerPrefixRev geometry round)
    (Scheduler.SplitLayout.encodeSplitAppend bound 0
      (outerSuffix round bound input))

def outerLocateSteps (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Nat :=
  Scheduler.Rollover.Locator.toOuterSteps geometry (round + 1)
    0 (round + 1)

theorem locate_outer_main_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (Scheduler.Rollover.Locator.machine .outer).runConfigExact?
        (outerLocateSteps geometry round)
        (outerLocatorSource geometry round bound input) =
      some (outerLocatorTarget geometry round bound input) := by
  unfold outerLocateSteps outerLocatorSource outerLocatorTarget
  rw [show Scheduler.Rollover.afterFuelWord geometry round bound input =
      List.cons MachineCodeSymbol.header
        (Scheduler.Layout.encodeGeometryAppend geometry
          (MachineDescription.encodeNatAppend (round + 1)
            (Scheduler.SplitLayout.encodeSplitAppend 0 (round + 1)
              (Scheduler.SplitLayout.encodeSplitAppend bound 0
                (outerSuffix round bound input))))) by rfl]
  unfold Scheduler.Rollover.Locator.toOuterSteps
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (Scheduler.Rollover.Locator.machine .outer)
    (Scheduler.Rollover.Locator.geometrySteps geometry +
      ((round + 1) + 1))
    (Scheduler.Rollover.Locator.splitSteps 0 (round + 1))]
  rw [Scheduler.Rollover.Locator.to_fuelUsed_exact .outer geometry
    (round + 1)
    (Scheduler.SplitLayout.encodeSplitAppend 0 (round + 1)
      (Scheduler.SplitLayout.encodeSplitAppend bound 0
        (outerSuffix round bound input))) (by decide) (by decide)]
  simp only
  rw [Scheduler.Rollover.Locator.split_run_exact .outer
    .fuelUsed .fuelMarker .fuelRemaining .halt 0 (round + 1)
    (Scheduler.Rollover.Locator.natPrefixRev (round + 1)
      (Scheduler.Rollover.Locator.geometryPrefixRev geometry))
    (Scheduler.SplitLayout.encodeSplitAppend bound 0
      (outerSuffix round bound input))
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
  rfl

def outerResetSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.sourceConfig bound
    (outerBaseRev geometry round) (outerSuffix round bound input)

def outerResetTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.targetConfig bound
    (outerBaseRev geometry round) (outerSuffix round bound input)

theorem outerLocatorTarget_tape_eq_resetSource
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (outerLocatorTarget geometry round bound input).tape =
      (outerResetSource geometry round bound input).tape := by
  rfl

theorem outer_reset_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    splitResetMachine.runConfigExact?
        (Scheduler.Advance.ExhaustedSplitReset.runSteps bound)
        (outerResetSource geometry round bound input) =
      some (outerResetTarget geometry round bound input) := by
  exact Scheduler.Advance.ExhaustedSplitReset.run_exact bound
    (outerBaseRev geometry round) (outerSuffix round bound input)

def outerGrowSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  Scheduler.Advance.GrowResetInsertion.sourceConfig bound
    (outerBaseRev geometry round) (outerSuffix round bound input)

def outerGrowTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  InsertRestagedMachine.rewindConfig
    (RewindWord.gateConfig
      (Scheduler.Rollover.afterOuterWord geometry round bound
        (bound + 1) input) 0)

theorem outerResetTarget_tape_eq_growSource
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (outerResetTarget geometry round bound input).tape =
      (outerGrowSource geometry round bound input).tape := by
  rfl

theorem outer_grow_output
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    Scheduler.Advance.GrowResetInsertion.outputWord bound
        (outerBaseRev geometry round) (outerSuffix round bound input) =
      Scheduler.Rollover.afterOuterWord geometry round bound
        (bound + 1) input := by
  cases geometry with
  | unbounded =>
      simp [Scheduler.Advance.GrowResetInsertion.outputWord,
        outerBaseRev, outerSuffix,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Rollover.Locator.natPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.Rollover.afterOuterWord,
        Scheduler.Rollover.word,
        Scheduler.SplitLayout.encodeSplitAppend,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        MachineDescription.encodeNatAppend, List.reverse_append,
        List.append_assoc]
  | bounded budget =>
      simp [Scheduler.Advance.GrowResetInsertion.outputWord,
        outerBaseRev, outerSuffix,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Rollover.Locator.natPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.Rollover.afterOuterWord,
        Scheduler.Rollover.word,
        Scheduler.SplitLayout.encodeSplitAppend,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        MachineDescription.encodeNatAppend, List.reverse_append,
        List.append_assoc]

theorem outer_grow_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (InsertRestagedMachine.machine growBuffer).runConfigExact?
        (Scheduler.Advance.GrowResetInsertion.runSteps bound
          (outerBaseRev geometry round) (outerSuffix round bound input))
        (outerGrowSource geometry round bound input) =
      some (outerGrowTarget geometry round bound input) := by
  unfold outerGrowSource outerGrowTarget growBuffer
  rw [Scheduler.Advance.GrowResetInsertion.run_exact bound
    (outerBaseRev geometry round) (outerSuffix round bound input)]
  change some (InsertRestagedMachine.rewindConfig
      (RewindWord.gateConfig
        (Scheduler.Advance.GrowResetInsertion.outputWord bound
          (outerBaseRev geometry round) (outerSuffix round bound input)) 0)) = _
  rw [outer_grow_output]

theorem outer_grow_phase
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (Scheduler.Rollover.afterFuelWord geometry round bound input))
      sourceTape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .locateOuter .unbounded .header, tape := sourceTape }
        { state := .locateInner .unbounded .header, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.Rollover.afterOuterWord geometry round bound
            (bound + 1) input)) targetTape := by
  rcases computes_lift_exact_from_equiv
      (Scheduler.Rollover.Locator.machine .outer)
      (locateOuterEmbed .unbounded) (locateOuter_map .unbounded)
      (locate_outer_main_exact geometry round bound input) hsource with
    ⟨locatedTape, hlocate, hlocated⟩
  have hresetSource : Tape.Equiv
      (outerResetSource geometry round bound input).tape locatedTape := by
    rw [← outerLocatorTarget_tape_eq_resetSource]
    exact hlocated
  rcases computes_lift_exact_from_equiv splitResetMachine
      (resetOuterEmbed .unbounded) (resetOuter_map .unbounded)
      (outer_reset_exact geometry round bound input) hresetSource with
    ⟨resetTape, hreset, hresetTape⟩
  have hgrowSource : Tape.Equiv
      (outerGrowSource geometry round bound input).tape resetTape := by
    rw [← outerResetTarget_tape_eq_growSource]
    exact hresetTape
  rcases computes_lift_exact_from_equiv
      (InsertRestagedMachine.machine growBuffer)
      (growOuterEmbed .unbounded) (growOuter_map .unbounded)
      (outer_grow_exact geometry round bound input) hgrowSource with
    ⟨targetTape, hgrow, htarget⟩
  refine ⟨targetTape,
    TuringMachine.computes_trans hlocate
      (TuringMachine.computes_trans hreset hgrow), ?_⟩
  exact Tape.Equiv.trans
    (Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (Scheduler.Rollover.afterOuterWord geometry round bound
          (bound + 1) input) 0)) htarget

def candidateTail (round bound : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.SplitLayout.candidateMarker ::
    MachineDescription.encodeNatAppend round
      (GeneratedCode.nestedStageCode input bound bound)

def innerPrefixRev (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) : Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.splitPrefixRev 0 (bound + 1)
    (Scheduler.Rollover.Locator.splitPrefixRev 0 (round + 1)
      (Scheduler.Rollover.Locator.natPrefixRev (round + 1)
        (Scheduler.Rollover.Locator.geometryPrefixRev geometry)))

def innerBaseRev (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) : Word MachineCodeSymbol :=
  List.append
    (Scheduler.Advance.ExhaustedSplitReset.ticks (bound + 1))
    (Scheduler.SplitLayout.splitMarker ::
      Scheduler.Rollover.Locator.natPrefixRev 0
        (Scheduler.Rollover.Locator.splitPrefixRev 0 (round + 1)
          (Scheduler.Rollover.Locator.natPrefixRev (round + 1)
            (Scheduler.Rollover.Locator.geometryPrefixRev geometry))))

def innerLocatorSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .header []
    (Scheduler.Rollover.afterOuterWord geometry round bound
      (bound + 1) input)

def innerLocatorTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .halt
    (innerPrefixRev geometry round bound)
    (Scheduler.SplitLayout.encodeSplitAppend bound 0
      (candidateTail round bound input))

def innerLocateSteps (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) : Nat :=
  Scheduler.Rollover.Locator.toInnerSteps geometry (round + 1)
    0 (round + 1) 0 (bound + 1)

theorem locate_inner_main_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (Scheduler.Rollover.Locator.machine .inner).runConfigExact?
        (innerLocateSteps geometry round bound)
        (innerLocatorSource geometry round bound input) =
      some (innerLocatorTarget geometry round bound input) := by
  unfold innerLocateSteps innerLocatorSource innerLocatorTarget
  rw [show Scheduler.Rollover.afterOuterWord geometry round bound
      (bound + 1) input =
    List.cons MachineCodeSymbol.header
      (Scheduler.Layout.encodeGeometryAppend geometry
        (MachineDescription.encodeNatAppend (round + 1)
          (Scheduler.SplitLayout.encodeSplitAppend 0 (round + 1)
            (Scheduler.SplitLayout.encodeSplitAppend 0 (bound + 1)
              (Scheduler.SplitLayout.encodeSplitAppend bound 0
                (candidateTail round bound input)))))) by rfl]
  unfold Scheduler.Rollover.Locator.toInnerSteps
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (Scheduler.Rollover.Locator.machine .inner)
    (Scheduler.Rollover.Locator.toOuterSteps geometry (round + 1)
      0 (round + 1))
    (Scheduler.Rollover.Locator.splitSteps 0 (bound + 1))]
  rw [Scheduler.Rollover.Locator.to_outerUsed_exact .inner geometry
    (round + 1) 0 (round + 1)
    (Scheduler.SplitLayout.encodeSplitAppend 0 (bound + 1)
      (Scheduler.SplitLayout.encodeSplitAppend bound 0
        (candidateTail round bound input)))
    (by decide) (by decide) (by decide)]
  simp only
  rw [Scheduler.Rollover.Locator.split_run_exact .inner
    .outerUsed .outerMarker .outerRemaining .halt 0 (bound + 1)
    (Scheduler.Rollover.Locator.splitPrefixRev 0 (round + 1)
      (Scheduler.Rollover.Locator.natPrefixRev (round + 1)
        (Scheduler.Rollover.Locator.geometryPrefixRev geometry)))
    (Scheduler.SplitLayout.encodeSplitAppend bound 0
      (candidateTail round bound input))
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
  rfl

def innerResetSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.sourceConfig bound
    (innerBaseRev geometry round bound) (candidateTail round bound input)

def innerResetTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.targetConfig bound
    (innerBaseRev geometry round bound) (candidateTail round bound input)

theorem innerLocatorTarget_tape_eq_resetSource
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (innerLocatorTarget geometry round bound input).tape =
      (innerResetSource geometry round bound input).tape := by
  rfl

theorem inner_reset_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    splitResetMachine.runConfigExact?
        (Scheduler.Advance.ExhaustedSplitReset.runSteps bound)
        (innerResetSource geometry round bound input) =
      some (innerResetTarget geometry round bound input) := by
  exact Scheduler.Advance.ExhaustedSplitReset.run_exact bound
    (innerBaseRev geometry round bound) (candidateTail round bound input)

def innerGrowSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  Scheduler.Advance.GrowResetInsertion.sourceConfig bound
    (innerBaseRev geometry round bound) (candidateTail round bound input)

def innerGrowTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  InsertRestagedMachine.rewindConfig
    (RewindWord.gateConfig
      (Scheduler.Rollover.afterInnerWord geometry round bound
        (bound + 1) input) 0)

theorem innerResetTarget_tape_eq_growSource
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (innerResetTarget geometry round bound input).tape =
      (innerGrowSource geometry round bound input).tape := by
  rfl

theorem inner_grow_output
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    Scheduler.Advance.GrowResetInsertion.outputWord bound
        (innerBaseRev geometry round bound) (candidateTail round bound input) =
      Scheduler.Rollover.afterInnerWord geometry round bound
        (bound + 1) input := by
  cases geometry with
  | unbounded =>
      simp [Scheduler.Advance.GrowResetInsertion.outputWord,
        innerBaseRev, candidateTail,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Rollover.Locator.natPrefixRev,
        Scheduler.Rollover.Locator.splitPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.Rollover.afterInnerWord,
        Scheduler.Rollover.word,
        Scheduler.SplitLayout.encodeSplitAppend,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        MachineDescription.encodeNatAppend, List.reverse_append,
        List.append_assoc]
  | bounded budget =>
      simp [Scheduler.Advance.GrowResetInsertion.outputWord,
        innerBaseRev, candidateTail,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Rollover.Locator.natPrefixRev,
        Scheduler.Rollover.Locator.splitPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.Rollover.afterInnerWord,
        Scheduler.Rollover.word,
        Scheduler.SplitLayout.encodeSplitAppend,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        MachineDescription.encodeNatAppend, List.reverse_append,
        List.append_assoc]

theorem inner_grow_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (InsertRestagedMachine.machine growBuffer).runConfigExact?
        (Scheduler.Advance.GrowResetInsertion.runSteps bound
          (innerBaseRev geometry round bound) (candidateTail round bound input))
        (innerGrowSource geometry round bound input) =
      some (innerGrowTarget geometry round bound input) := by
  unfold innerGrowSource innerGrowTarget growBuffer
  rw [Scheduler.Advance.GrowResetInsertion.run_exact bound
    (innerBaseRev geometry round bound) (candidateTail round bound input)]
  change some (InsertRestagedMachine.rewindConfig
      (RewindWord.gateConfig
        (Scheduler.Advance.GrowResetInsertion.outputWord bound
          (innerBaseRev geometry round bound)
          (candidateTail round bound input)) 0)) = _
  rw [inner_grow_output]

theorem inner_grow_phase
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (Scheduler.Rollover.afterOuterWord geometry round bound
          (bound + 1) input)) sourceTape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .locateInner .unbounded .header, tape := sourceTape }
        { state := .candidates candidateMachine.start, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.Rollover.afterInnerWord geometry round bound
            (bound + 1) input)) targetTape := by
  rcases computes_lift_exact_from_equiv
      (Scheduler.Rollover.Locator.machine .inner)
      (locateInnerEmbed .unbounded) (locateInner_map .unbounded)
      (locate_inner_main_exact geometry round bound input) hsource with
    ⟨locatedTape, hlocate, hlocated⟩
  have hresetSource : Tape.Equiv
      (innerResetSource geometry round bound input).tape locatedTape := by
    rw [← innerLocatorTarget_tape_eq_resetSource]
    exact hlocated
  rcases computes_lift_exact_from_equiv splitResetMachine
      (resetInnerEmbed .unbounded) (resetInner_map .unbounded)
      (inner_reset_exact geometry round bound input) hresetSource with
    ⟨resetTape, hreset, hresetTape⟩
  have hgrowSource : Tape.Equiv
      (innerGrowSource geometry round bound input).tape resetTape := by
    rw [← innerResetTarget_tape_eq_growSource]
    exact hresetTape
  rcases computes_lift_exact_from_equiv
      (InsertRestagedMachine.machine growBuffer)
      (growInnerEmbed .unbounded) (growInner_map .unbounded)
      (inner_grow_exact geometry round bound input) hgrowSource with
    ⟨targetTape, hgrow, htarget⟩
  refine ⟨targetTape,
    TuringMachine.computes_trans hlocate
      (TuringMachine.computes_trans hreset hgrow), ?_⟩
  exact Tape.Equiv.trans
    (Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (Scheduler.Rollover.afterInnerWord geometry round bound
          (bound + 1) input) 0)) htarget

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.MainRollover
