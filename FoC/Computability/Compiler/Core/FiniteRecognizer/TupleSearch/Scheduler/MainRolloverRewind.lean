import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.MainRolloverGrowth

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.MainRollover

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Scheduler.Rollover

namespace ExactRewind

def startTape (leftRev rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] => ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev []
  | first :: suffix =>
      { left := leftRev.map some
        head := some first
        right := List.append (suffix.map some) [none] }

def startConfig (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  { state := RewindWord.machine.start
    tape := startTape leftRev rest }

theorem startTape_equiv_cursorTape (leftRev rest : Word MachineCodeSymbol) :
    Tape.Equiv (startTape leftRev rest)
      (ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev rest) := by
  cases rest with
  | nil =>
      exact Tape.Equiv.refl _
  | cons first suffix =>
      refine ⟨rfl, rfl, ?_⟩
      exact dropTrailingNone_append_none (suffix.map some)

theorem start_step (leftRev rest : Word MachineCodeSymbol) :
    RewindWord.machine.stepConfig (startConfig leftRev rest) =
      some (RewindWord.scanConfig leftRev rest 0) := by
  cases leftRev <;> cases rest <;> rfl

theorem scan_step (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    RewindWord.machine.stepConfig
        (RewindWord.scanConfig (current :: remainingRev) crossed 0) =
      some (RewindWord.scanConfig remainingRev (current :: crossed) 0) := by
  cases remainingRev <;> cases crossed <;> rfl

theorem scan_finish (crossed : Word MachineCodeSymbol) :
    RewindWord.machine.stepConfig (RewindWord.scanConfig [] crossed 0) =
      some (RewindWord.gateConfig crossed 0) := by
  cases crossed <;> rfl

theorem scan_run_exact (remainingRev crossed : Word MachineCodeSymbol) :
    RewindWord.machine.runConfigExact? (remainingRev.length + 1)
        (RewindWord.scanConfig remainingRev crossed 0) =
      some (RewindWord.gateConfig
        (List.append remainingRev.reverse crossed) 0) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact scan_finish crossed
  | cons current remainingRev ih =>
      change RewindWord.machine.runConfigExact?
          ((remainingRev.length + 1) + 1)
          (RewindWord.scanConfig (current :: remainingRev) crossed 0) = _
      rw [TuringMachine.runConfigExact?, scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

theorem run_exact (leftRev rest : Word MachineCodeSymbol) :
    RewindWord.machine.runConfigExact? (leftRev.length + 2)
        (startConfig leftRev rest) =
      some (RewindWord.gateConfig
        (List.append leftRev.reverse rest) 0) := by
  change RewindWord.machine.runConfigExact?
      ((leftRev.length + 1) + 1) (startConfig leftRev rest) = _
  rw [TuringMachine.runConfigExact?, start_step]
  simp only
  exact scan_run_exact leftRev rest

end ExactRewind

def outerRewindLeftRev (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Word MachineCodeSymbol :=
  Scheduler.SplitLayout.splitMarker :: MachineCodeSymbol.done ::
    MachineCodeSymbol.done :: outerBaseRev geometry round

def outerRewindRest (round bound : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend bound (outerSuffix round bound input)

def outerRewindSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  ExactRewind.startConfig (outerRewindLeftRev geometry round)
    (outerRewindRest round bound input)

def outerRewindTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  RewindWord.gateConfig
    (Scheduler.Rollover.afterOuterWord geometry round bound bound input) 0

theorem outerResetTarget_tape_equiv_rewindSource
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    Tape.Equiv (outerRewindSource geometry round bound input).tape
      (outerResetTarget geometry round bound input).tape := by
  simpa [outerRewindSource, outerRewindLeftRev, outerRewindRest,
    outerResetTarget, ExactRewind.startConfig,
    Scheduler.Advance.ExhaustedSplitReset.targetConfig,
    Scheduler.Advance.ExhaustedSplitReset.config]
    using ExactRewind.startTape_equiv_cursorTape
      (outerRewindLeftRev geometry round)
      (outerRewindRest round bound input)

theorem outer_rewind_output
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    List.append (outerRewindLeftRev geometry round).reverse
        (outerRewindRest round bound input) =
      Scheduler.Rollover.afterOuterWord geometry round bound bound
        input := by
  cases geometry with
  | unbounded =>
      simp [outerRewindLeftRev, outerRewindRest, outerBaseRev, outerSuffix,
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
      simp [outerRewindLeftRev, outerRewindRest, outerBaseRev, outerSuffix,
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

theorem outer_rewind_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    RewindWord.machine.runConfigExact?
        ((outerRewindLeftRev geometry round).length + 2)
        (outerRewindSource geometry round bound input) =
      some (outerRewindTarget geometry round bound input) := by
  unfold outerRewindSource outerRewindTarget
  rw [ExactRewind.run_exact]
  rw [outer_rewind_output]

theorem outer_rewind_phase (budget round : Nat)
    (input : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (Scheduler.Rollover.afterFuelWord (.bounded budget) round
          budget input)) sourceTape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .locateOuter .bounded .header, tape := sourceTape }
        { state := .locateInner .bounded .header, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.Rollover.afterOuterWord (.bounded budget) round
            budget budget input)) targetTape := by
  rcases computes_lift_exact_from_equiv
      (Scheduler.Rollover.Locator.machine .outer)
      (locateOuterEmbed .bounded) (locateOuter_map .bounded)
      (locate_outer_main_exact (.bounded budget) round budget input)
      hsource with
    ⟨locatedTape, hlocate, hlocated⟩
  have hresetSource : Tape.Equiv
      (outerResetSource (.bounded budget) round budget input).tape
        locatedTape := by
    rw [← outerLocatorTarget_tape_eq_resetSource]
    exact hlocated
  rcases computes_lift_exact_from_equiv splitResetMachine
      (resetOuterEmbed .bounded) (resetOuter_map .bounded)
      (outer_reset_exact (.bounded budget) round budget input)
      hresetSource with
    ⟨resetTape, hreset, hresetTape⟩
  have hrewindSource : Tape.Equiv
      (outerRewindSource (.bounded budget) round budget input).tape
        resetTape :=
    Tape.Equiv.trans
      (outerResetTarget_tape_equiv_rewindSource
        (.bounded budget) round budget input) hresetTape
  rcases computes_lift_exact_from_equiv RewindWord.machine
      (rewindOuterEmbed .bounded) (rewindOuter_map .bounded)
      (outer_rewind_exact (.bounded budget) round budget input)
      hrewindSource with
    ⟨targetTape, hrewind, htarget⟩
  refine ⟨targetTape,
    TuringMachine.computes_trans hlocate
      (TuringMachine.computes_trans hreset hrewind), ?_⟩
  exact Tape.Equiv.trans
    (Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (Scheduler.Rollover.afterOuterWord (.bounded budget) round
          budget budget input) 0)) htarget

def boundedInnerPrefixRev (budget round : Nat) : Word MachineCodeSymbol :=
  Scheduler.Rollover.Locator.splitPrefixRev 0 budget
    (Scheduler.Rollover.Locator.splitPrefixRev 0 (round + 1)
      (Scheduler.Rollover.Locator.natPrefixRev (round + 1)
        (Scheduler.Rollover.Locator.geometryPrefixRev
          (.bounded budget))))

def boundedInnerBaseRev (budget round : Nat) : Word MachineCodeSymbol :=
  List.append
    (Scheduler.Advance.ExhaustedSplitReset.ticks budget)
    (Scheduler.SplitLayout.splitMarker ::
      Scheduler.Rollover.Locator.natPrefixRev 0
        (Scheduler.Rollover.Locator.splitPrefixRev 0 (round + 1)
          (Scheduler.Rollover.Locator.natPrefixRev (round + 1)
            (Scheduler.Rollover.Locator.geometryPrefixRev
              (.bounded budget)))))

def boundedInnerLocatorSource (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .header []
    (Scheduler.Rollover.afterOuterWord (.bounded budget) round budget
      budget input)

def boundedInnerLocatorTarget (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .halt
    (boundedInnerPrefixRev budget round)
    (Scheduler.SplitLayout.encodeSplitAppend budget 0
      (candidateTail round budget input))

def boundedInnerLocateSteps (budget round : Nat) : Nat :=
  Scheduler.Rollover.Locator.toInnerSteps (.bounded budget) (round + 1)
    0 (round + 1) 0 budget

theorem locate_bounded_inner_exact (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    (Scheduler.Rollover.Locator.machine .inner).runConfigExact?
        (boundedInnerLocateSteps budget round)
        (boundedInnerLocatorSource budget round input) =
      some (boundedInnerLocatorTarget budget round input) := by
  unfold boundedInnerLocateSteps boundedInnerLocatorSource
    boundedInnerLocatorTarget
  rw [show Scheduler.Rollover.afterOuterWord (.bounded budget) round
      budget budget input =
    List.cons MachineCodeSymbol.header
      (Scheduler.Layout.encodeGeometryAppend (.bounded budget)
        (MachineDescription.encodeNatAppend (round + 1)
          (Scheduler.SplitLayout.encodeSplitAppend 0 (round + 1)
            (Scheduler.SplitLayout.encodeSplitAppend 0 budget
              (Scheduler.SplitLayout.encodeSplitAppend budget 0
                (candidateTail round budget input)))))) by rfl]
  unfold Scheduler.Rollover.Locator.toInnerSteps
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (Scheduler.Rollover.Locator.machine .inner)
    (Scheduler.Rollover.Locator.toOuterSteps (.bounded budget)
      (round + 1) 0 (round + 1))
    (Scheduler.Rollover.Locator.splitSteps 0 budget)]
  rw [Scheduler.Rollover.Locator.to_outerUsed_exact .inner
    (.bounded budget) (round + 1) 0 (round + 1)
    (Scheduler.SplitLayout.encodeSplitAppend 0 budget
      (Scheduler.SplitLayout.encodeSplitAppend budget 0
        (candidateTail round budget input)))
    (by decide) (by decide) (by decide)]
  simp only
  rw [Scheduler.Rollover.Locator.split_run_exact .inner
    .outerUsed .outerMarker .outerRemaining .halt 0 budget
    (Scheduler.Rollover.Locator.splitPrefixRev 0 (round + 1)
      (Scheduler.Rollover.Locator.natPrefixRev (round + 1)
        (Scheduler.Rollover.Locator.geometryPrefixRev
          (.bounded budget))))
    (Scheduler.SplitLayout.encodeSplitAppend budget 0
      (candidateTail round budget input))
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
  rfl

def boundedInnerResetSource (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.sourceConfig budget
    (boundedInnerBaseRev budget round) (candidateTail round budget input)

def boundedInnerResetTarget (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.targetConfig budget
    (boundedInnerBaseRev budget round) (candidateTail round budget input)

theorem boundedInnerLocatorTarget_tape_eq_resetSource
    (budget round : Nat) (input : Word MachineCodeSymbol) :
    (boundedInnerLocatorTarget budget round input).tape =
      (boundedInnerResetSource budget round input).tape := by
  rfl

theorem bounded_inner_reset_exact (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    splitResetMachine.runConfigExact?
        (Scheduler.Advance.ExhaustedSplitReset.runSteps budget)
        (boundedInnerResetSource budget round input) =
      some (boundedInnerResetTarget budget round input) := by
  exact Scheduler.Advance.ExhaustedSplitReset.run_exact budget
    (boundedInnerBaseRev budget round) (candidateTail round budget input)

def boundedInnerRewindLeftRev (budget round : Nat) :
    Word MachineCodeSymbol :=
  Scheduler.SplitLayout.splitMarker :: MachineCodeSymbol.done ::
    MachineCodeSymbol.done :: boundedInnerBaseRev budget round

def boundedInnerRewindRest (budget round : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend budget (candidateTail round budget input)

def boundedInnerRewindSource (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  ExactRewind.startConfig (boundedInnerRewindLeftRev budget round)
    (boundedInnerRewindRest budget round input)

def boundedInnerRewindTarget (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RewindWord.Control :=
  RewindWord.gateConfig
    (Scheduler.Rollover.afterInnerWord (.bounded budget) round budget
      budget input) 0

theorem boundedInnerResetTarget_tape_equiv_rewindSource
    (budget round : Nat) (input : Word MachineCodeSymbol) :
    Tape.Equiv (boundedInnerRewindSource budget round input).tape
      (boundedInnerResetTarget budget round input).tape := by
  simpa [boundedInnerRewindSource, boundedInnerRewindLeftRev,
    boundedInnerRewindRest, boundedInnerResetTarget,
    ExactRewind.startConfig,
    Scheduler.Advance.ExhaustedSplitReset.targetConfig,
    Scheduler.Advance.ExhaustedSplitReset.config]
    using ExactRewind.startTape_equiv_cursorTape
      (boundedInnerRewindLeftRev budget round)
      (boundedInnerRewindRest budget round input)

theorem bounded_inner_rewind_output (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    List.append (boundedInnerRewindLeftRev budget round).reverse
        (boundedInnerRewindRest budget round input) =
      Scheduler.Rollover.afterInnerWord (.bounded budget) round budget
        budget input := by
  simp [boundedInnerRewindLeftRev, boundedInnerRewindRest,
    boundedInnerBaseRev, candidateTail,
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

theorem bounded_inner_rewind_exact (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    RewindWord.machine.runConfigExact?
        ((boundedInnerRewindLeftRev budget round).length + 2)
        (boundedInnerRewindSource budget round input) =
      some (boundedInnerRewindTarget budget round input) := by
  unfold boundedInnerRewindSource boundedInnerRewindTarget
  rw [ExactRewind.run_exact]
  rw [bounded_inner_rewind_output]

theorem bounded_inner_rewind_phase (budget round : Nat)
    (input : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (Scheduler.Rollover.afterOuterWord (.bounded budget) round
          budget budget input)) sourceTape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .locateInner .bounded .header, tape := sourceTape }
        { state := .candidates candidateMachine.start, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.Rollover.afterInnerWord (.bounded budget) round
            budget budget input)) targetTape := by
  rcases computes_lift_exact_from_equiv
      (Scheduler.Rollover.Locator.machine .inner)
      (locateInnerEmbed .bounded) (locateInner_map .bounded)
      (locate_bounded_inner_exact budget round input) hsource with
    ⟨locatedTape, hlocate, hlocated⟩
  have hresetSource : Tape.Equiv
      (boundedInnerResetSource budget round input).tape locatedTape := by
    rw [← boundedInnerLocatorTarget_tape_eq_resetSource]
    exact hlocated
  rcases computes_lift_exact_from_equiv splitResetMachine
      (resetInnerEmbed .bounded) (resetInner_map .bounded)
      (bounded_inner_reset_exact budget round input) hresetSource with
    ⟨resetTape, hreset, hresetTape⟩
  have hrewindSource : Tape.Equiv
      (boundedInnerRewindSource budget round input).tape resetTape :=
    Tape.Equiv.trans
      (boundedInnerResetTarget_tape_equiv_rewindSource budget round input)
      hresetTape
  rcases computes_lift_exact_from_equiv RewindWord.machine
      (rewindInnerEmbed .bounded) (rewindInner_map .bounded)
      (bounded_inner_rewind_exact budget round input) hrewindSource with
    ⟨targetTape, hrewind, htarget⟩
  refine ⟨targetTape,
    TuringMachine.computes_trans hlocate
      (TuringMachine.computes_trans hreset hrewind), ?_⟩
  exact Tape.Equiv.trans
    (Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (Scheduler.Rollover.afterInnerWord (.bounded budget) round
          budget budget input) 0)) htarget

theorem run_main_rollover_unbounded (round : Nat)
    (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (Scheduler.Rollover.sourceWord .unbounded round round
              input) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.Equiv
        (Scheduler.CandidateReset.finalConfig .unbounded (round + 1)
          (round + 1) (round + 1) (round + 1) input).tape finalTape ∧
      Tape.normalizedOutput finalTape =
        Scheduler.Rollover.targetWord .unbounded round (round + 1)
          input ∧
      Scheduler.SplitLayout.decode
          (Tape.normalizedOutput finalTape) =
        some (Scheduler.Rollover.targetFrame .unbounded round input) := by
  have hround : TuringMachine.Computes machine
      { state := machine.start
        tape := Tape.input
          (Scheduler.Rollover.sourceWord .unbounded round round input) }
      (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .unbounded)
        (roundInsertTarget .unbounded round round input)) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        (round_phase_unbounded_exact round round input))
  rcases fuel_phase .unbounded .unbounded round round input
      (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .unbounded)
        (roundInsertTarget .unbounded round round input)).tape
      (Tape.Equiv.symm
        (round_phase_unbounded_target_equiv round round input)) with
    ⟨fuelTape, hfuel, hfuelTape⟩
  rcases outer_grow_phase .unbounded round round input fuelTape hfuelTape with
    ⟨outerTape, houter, houterTape⟩
  rcases inner_grow_phase .unbounded round round input outerTape houterTape with
    ⟨candidateTape, hinner, hcandidateTape⟩
  rcases Scheduler.CandidateReset.reset_after_main_rollover_unbounded
      round input candidateTape hcandidateTape with
    ⟨finalTape, hcandidate, hequiv, hout, hdecode⟩
  have hcandidate' := computes_lift candidateMachine candidatesEmbed
    candidates_map hcandidate
  refine ⟨finalTape, ?_, hequiv, hout, hdecode⟩
  exact TuringMachine.computes_trans hround
    (TuringMachine.computes_trans hfuel
      (TuringMachine.computes_trans houter
        (TuringMachine.computes_trans hinner hcandidate')))

theorem run_main_rollover_bounded (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (Scheduler.Rollover.sourceWord (.bounded budget) round
              budget input) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.Equiv
        (Scheduler.CandidateReset.finalConfig (.bounded budget)
          (round + 1) (round + 1) budget budget input).tape finalTape ∧
      Tape.normalizedOutput finalTape =
        Scheduler.Rollover.targetWord (.bounded budget) round budget
          input ∧
      Scheduler.SplitLayout.decode
          (Tape.normalizedOutput finalTape) =
        some
          (Scheduler.Rollover.targetFrame (.bounded budget) round
            input) := by
  have hround : TuringMachine.Computes machine
      { state := machine.start
        tape := Tape.input
          (Scheduler.Rollover.sourceWord (.bounded budget) round budget
            input) }
      (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .bounded)
        (roundInsertTarget (.bounded budget) round budget input)) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        (round_phase_bounded_exact budget round input))
  rcases fuel_phase .bounded (.bounded budget) round budget input
      (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .bounded)
        (roundInsertTarget (.bounded budget) round budget input)).tape
      (Tape.Equiv.symm
        (round_phase_bounded_target_equiv budget round input)) with
    ⟨fuelTape, hfuel, hfuelTape⟩
  rcases outer_rewind_phase budget round input fuelTape hfuelTape with
    ⟨outerTape, houter, houterTape⟩
  rcases bounded_inner_rewind_phase budget round input outerTape houterTape with
    ⟨candidateTape, hinner, hcandidateTape⟩
  rcases Scheduler.CandidateReset.reset_after_main_rollover_bounded
      budget round input candidateTape hcandidateTape with
    ⟨finalTape, hcandidate, hequiv, hout, hdecode⟩
  have hcandidate' := computes_lift candidateMachine candidatesEmbed
    candidates_map hcandidate
  refine ⟨finalTape, ?_, hequiv, hout, hdecode⟩
  exact TuringMachine.computes_trans hround
    (TuringMachine.computes_trans hfuel
      (TuringMachine.computes_trans houter
        (TuringMachine.computes_trans hinner hcandidate')))

theorem run_main_rollover
    (geometry : Scheduler.Layout.Geometry) (round : Nat)
    (input : Word MachineCodeSymbol) :
    ∃ finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := machine.start
          tape := Tape.input
            (Scheduler.Rollover.sourceWord geometry round
              (geometry.pairBound round) input) }
        { state := machine.halt, tape := finalTape } ∧
      Tape.Equiv
        (Scheduler.CandidateReset.finalConfig geometry (round + 1)
          (round + 1) (geometry.pairBound (round + 1))
          (geometry.pairBound (round + 1)) input).tape finalTape ∧
      Tape.normalizedOutput finalTape =
        Scheduler.Rollover.targetWord geometry round
          (geometry.pairBound (round + 1)) input ∧
      Scheduler.SplitLayout.decode
          (Tape.normalizedOutput finalTape) =
        some (Scheduler.Rollover.targetFrame geometry round input) := by
  cases geometry with
  | unbounded =>
      exact run_main_rollover_unbounded round input
  | bounded budget =>
      exact run_main_rollover_bounded budget round input

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.MainRollover
