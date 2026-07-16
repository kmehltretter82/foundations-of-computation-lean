import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.Advance

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Rollover

open Languages
open Scheduler.SplitLayout

def word (geometry : Geometry) (round : Nat)
    (fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter
      candidateInner : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    Scheduler.Layout.encodeGeometryAppend geometry
      (MachineDescription.encodeNatAppend round
        (encodeSplitAppend fuelUsed fuelRemaining
          (encodeSplitAppend outerUsed outerRemaining
            (encodeSplitAppend innerUsed innerRemaining
              (candidateMarker ::
                MachineDescription.encodeNatAppend candidateFuel
                  (GeneratedCode.nestedStageCode input
                    candidateInner candidateOuter))))))

def sourceFrame (geometry : Geometry) (round bound : Nat)
    (input : Word MachineCodeSymbol) : Frame :=
  { geometry := geometry
    cursor :=
      { round := round
        inner := bound
        outer := bound
        selectedFuel := round }
    input := input }

def targetFrame (geometry : Geometry) (round : Nat)
    (input : Word MachineCodeSymbol) : Frame :=
  { geometry := geometry
    cursor :=
      { round := round + 1
        inner := 0
        outer := 0
        selectedFuel := 0 }
    input := input }

def sourceWord (geometry : Geometry) (round bound : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  word geometry round round 0 bound 0 bound 0 round bound bound input

def afterRoundWord (geometry : Geometry) (round bound : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  word geometry (round + 1) round 0 bound 0 bound 0 round bound bound input

def afterFuelWord (geometry : Geometry) (round bound : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  word geometry (round + 1) 0 (round + 1) bound 0 bound 0
    round bound bound input

def afterOuterWord (geometry : Geometry) (round oldBound newBound : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  word geometry (round + 1) 0 (round + 1) 0 newBound oldBound 0
    round oldBound oldBound input

def afterInnerWord (geometry : Geometry) (round oldBound newBound : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  word geometry (round + 1) 0 (round + 1) 0 newBound 0 newBound
    round oldBound oldBound input

def targetWord (geometry : Geometry) (round newBound : Nat)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  word geometry (round + 1) 0 (round + 1) 0 newBound 0 newBound
    0 0 0 input

theorem source_encode_unbounded (round : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.SplitLayout.encode
        (sourceFrame .unbounded round round input) =
      sourceWord .unbounded round round input := by
  simp [Scheduler.SplitLayout.encode, sourceFrame, sourceWord,
    word, Scheduler.SplitLayout.candidateWord,
    Scheduler.Layout.Geometry.pairBound]

theorem source_encode_bounded (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.SplitLayout.encode
        (sourceFrame (.bounded budget) round budget input) =
      sourceWord (.bounded budget) round budget input := by
  simp [Scheduler.SplitLayout.encode, sourceFrame, sourceWord,
    word, Scheduler.SplitLayout.candidateWord,
    Scheduler.Layout.Geometry.pairBound]

theorem source_advance_unbounded (round : Nat)
    (input : Word MachineCodeSymbol) :
    (sourceFrame .unbounded round round input).advance =
      targetFrame .unbounded round input := by
  simp [sourceFrame, targetFrame, Scheduler.Layout.Frame.advance,
    Scheduler.Layout.Cursor.advance,
    Scheduler.Layout.Geometry.pairBound]

theorem source_advance_bounded (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    (sourceFrame (.bounded budget) round budget input).advance =
      targetFrame (.bounded budget) round input := by
  simp [sourceFrame, targetFrame, Scheduler.Layout.Frame.advance,
    Scheduler.Layout.Cursor.advance,
    Scheduler.Layout.Geometry.pairBound]

theorem target_encode_unbounded (round : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.SplitLayout.encode
        (targetFrame .unbounded round input) =
      targetWord .unbounded round (round + 1) input := by
  rfl

theorem target_encode_bounded (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.SplitLayout.encode
        (targetFrame (.bounded budget) round input) =
      targetWord (.bounded budget) round budget input := by
  simp [Scheduler.SplitLayout.encode, targetFrame,
    targetWord, word, Scheduler.SplitLayout.candidateWord,
    Scheduler.Layout.Geometry.pairBound]

theorem target_decode_unbounded (round : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.SplitLayout.decode
        (targetWord .unbounded round (round + 1) input) =
      some (targetFrame .unbounded round input) := by
  rw [← target_encode_unbounded]
  apply Scheduler.SplitLayout.decode_encode
  simp [targetFrame, Scheduler.Layout.Cursor.Valid,
    Scheduler.Layout.Geometry.pairBound]

theorem target_decode_bounded (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    Scheduler.SplitLayout.decode
        (targetWord (.bounded budget) round budget input) =
      some (targetFrame (.bounded budget) round input) := by
  rw [← target_encode_bounded]
  apply Scheduler.SplitLayout.decode_encode
  simp [targetFrame, Scheduler.Layout.Cursor.Valid,
    Scheduler.Layout.Geometry.pairBound]

namespace Locator

inductive Target where
  | round
  | fuel
  | outer
  | inner
  | candidateFuel
  | candidateOuter
  | candidateInner
deriving DecidableEq

inductive Control where
  | header
  | geometry
  | budget
  | round
  | fuelUsed
  | fuelMarker
  | fuelRemaining
  | outerUsed
  | outerMarker
  | outerRemaining
  | innerUsed
  | innerMarker
  | innerRemaining
  | candidateMarker
  | candidateFuel
  | candidateOuter
  | halt
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems := [.header, .geometry, .budget, .round, .fuelUsed,
    .fuelMarker, .fuelRemaining, .outerUsed, .outerMarker,
    .outerRemaining, .innerUsed, .innerMarker, .innerRemaining,
    .candidateMarker, .candidateFuel, .candidateOuter, .halt]
  complete := by
    intro control
    cases control <;> simp

end Control

def afterGeometry (target : Target) : Control :=
  if target = .round then .halt else .round

def afterRound (target : Target) : Control :=
  if target = .fuel then .halt else .fuelUsed

def afterFuel (target : Target) : Control :=
  if target = .outer then .halt else .outerUsed

def afterOuter (target : Target) : Control :=
  if target = .inner then .halt else .innerUsed

def afterCandidateMarker (target : Target) : Control :=
  if target = .candidateFuel then .halt else .candidateFuel

def afterCandidateFuel (target : Target) : Control :=
  if target = .candidateOuter then .halt else .candidateOuter

def transition (target : Target) :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .header, some .header =>
      some (some .header, Direction.right, .geometry)
  | .geometry, some .blank =>
      some (some .blank, Direction.right, afterGeometry target)
  | .geometry, some .zero =>
      some (some .zero, Direction.right, .budget)
  | .budget, some .tick =>
      some (some .tick, Direction.right, .budget)
  | .budget, some .done =>
      some (some .done, Direction.right, afterGeometry target)
  | .round, some .tick =>
      some (some .tick, Direction.right, .round)
  | .round, some .done =>
      some (some .done, Direction.right, afterRound target)
  | .fuelUsed, some .tick =>
      some (some .tick, Direction.right, .fuelUsed)
  | .fuelUsed, some .done =>
      some (some .done, Direction.right, .fuelMarker)
  | .fuelMarker, some .transition =>
      some (some .transition, Direction.right, .fuelRemaining)
  | .fuelRemaining, some .tick =>
      some (some .tick, Direction.right, .fuelRemaining)
  | .fuelRemaining, some .done =>
      some (some .done, Direction.right, afterFuel target)
  | .outerUsed, some .tick =>
      some (some .tick, Direction.right, .outerUsed)
  | .outerUsed, some .done =>
      some (some .done, Direction.right, .outerMarker)
  | .outerMarker, some .transition =>
      some (some .transition, Direction.right, .outerRemaining)
  | .outerRemaining, some .tick =>
      some (some .tick, Direction.right, .outerRemaining)
  | .outerRemaining, some .done =>
      some (some .done, Direction.right, afterOuter target)
  | .innerUsed, some .tick =>
      some (some .tick, Direction.right, .innerUsed)
  | .innerUsed, some .done =>
      some (some .done, Direction.right, .innerMarker)
  | .innerMarker, some .transition =>
      some (some .transition, Direction.right, .innerRemaining)
  | .innerRemaining, some .tick =>
      some (some .tick, Direction.right, .innerRemaining)
  | .innerRemaining, some .done =>
      some (some .done, Direction.right, .candidateMarker)
  | .candidateMarker, some .moveLeft =>
      some (some .moveLeft, Direction.right,
        afterCandidateMarker target)
  | .candidateFuel, some .tick =>
      some (some .tick, Direction.right, .candidateFuel)
  | .candidateFuel, some .done =>
      some (some .done, Direction.right, afterCandidateFuel target)
  | .candidateOuter, some .tick =>
      some (some .tick, Direction.right, .candidateOuter)
  | .candidateOuter, some .done =>
      some (some .done, Direction.right, .halt)
  | _, _ => none

def machine (target : Target) : TuringMachine MachineCodeSymbol Control where
  start := .header
  halt := .halt
  transition := transition target
  statesFinite := Control.finite

def config (state : Control) (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := state
    tape := ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev rest }

theorem symbol_step (target : Target) (state next : Control)
    (current : MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol)
    (htransition : transition target state (some current) =
      some (some current, Direction.right, next)) :
    (machine target).stepConfig
        (config state leftRev (current :: suffix)) =
      some (config next (current :: leftRev) suffix) := by
  cases leftRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, config,
      ExactFuel.StrictProbe.SerializedShift.cursorTape,
      Tape.read, Tape.write, Tape.move, Tape.moveRight, htransition]

theorem ticks_run_exact (target : Target) (state : Control)
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol)
    (htick : transition target state (some MachineCodeSymbol.tick) =
      some (some MachineCodeSymbol.tick, Direction.right, state)) :
    (machine target).runConfigExact? count
        (config state leftRev
          (List.append (Scheduler.Advance.ExhaustedSplitReset.ticks count)
            suffix)) =
      some (config state
        (List.append
          (Scheduler.Advance.ExhaustedSplitReset.ticks count) leftRev)
        suffix) := by
  induction count generalizing leftRev with
  | zero => rfl
  | succ count ih =>
      change (machine target).runConfigExact? (count + 1)
        (config state leftRev
          (MachineCodeSymbol.tick ::
            List.append
              (Scheduler.Advance.ExhaustedSplitReset.ticks count)
              suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [symbol_step target state state MachineCodeSymbol.tick
        leftRev _ htick]
      simp only
      rw [ih (MachineCodeSymbol.tick :: leftRev)]
      have hleft :
          List.append
              (Scheduler.Advance.ExhaustedSplitReset.ticks count)
              (MachineCodeSymbol.tick :: leftRev) =
            List.append
              (Scheduler.Advance.ExhaustedSplitReset.ticks (count + 1))
              leftRev := by
        simp [Scheduler.Advance.ExhaustedSplitReset.ticks,
          List.replicate_succ', List.append_assoc]
      rw [hleft]

theorem nat_run_exact (target : Target) (state next : Control)
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol)
    (htick : transition target state (some MachineCodeSymbol.tick) =
      some (some MachineCodeSymbol.tick, Direction.right, state))
    (hdone : transition target state (some MachineCodeSymbol.done) =
      some (some MachineCodeSymbol.done, Direction.right, next)) :
    (machine target).runConfigExact? (count + 1)
        (config state leftRev
          (MachineDescription.encodeNatAppend count suffix)) =
      some (config next
        (MachineCodeSymbol.done ::
          List.append
            (Scheduler.Advance.ExhaustedSplitReset.ticks count)
            leftRev)
        suffix) := by
  rw [show count + 1 = count + 1 by rfl]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine target) count 1]
  rw [show MachineDescription.encodeNatAppend count suffix =
      List.append
        (Scheduler.Advance.ExhaustedSplitReset.ticks count)
        (MachineCodeSymbol.done :: suffix) by
    simp [MachineDescription.encodeNatAppend,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      List.append_assoc]]
  rw [ticks_run_exact target state count leftRev
    (MachineCodeSymbol.done :: suffix) htick]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [symbol_step target state next MachineCodeSymbol.done _ suffix hdone]
  rfl

def splitSteps (used remaining : Nat) : Nat :=
  (used + 1) + 1 + (remaining + 1)

theorem split_run_exact (target : Target)
    (usedState markerState remainingState next : Control)
    (used remaining : Nat) (leftRev suffix : Word MachineCodeSymbol)
    (husedTick : transition target usedState
        (some MachineCodeSymbol.tick) =
      some (some MachineCodeSymbol.tick, Direction.right, usedState))
    (husedDone : transition target usedState
        (some MachineCodeSymbol.done) =
      some (some MachineCodeSymbol.done, Direction.right, markerState))
    (hmarker : transition target markerState (some splitMarker) =
      some (some splitMarker, Direction.right, remainingState))
    (hremainingTick : transition target remainingState
        (some MachineCodeSymbol.tick) =
      some (some MachineCodeSymbol.tick, Direction.right, remainingState))
    (hremainingDone : transition target remainingState
        (some MachineCodeSymbol.done) =
      some (some MachineCodeSymbol.done, Direction.right, next)) :
    (machine target).runConfigExact? (splitSteps used remaining)
        (config usedState leftRev
          (encodeSplitAppend used remaining suffix)) =
      some (config next
        (MachineCodeSymbol.done ::
          List.append
            (Scheduler.Advance.ExhaustedSplitReset.ticks remaining)
            (splitMarker :: MachineCodeSymbol.done ::
              List.append
                (Scheduler.Advance.ExhaustedSplitReset.ticks used)
                leftRev))
        suffix) := by
  unfold splitSteps
  rw [show (used + 1) + 1 + (remaining + 1) =
      (used + 1) + (1 + (remaining + 1)) by lia]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  rw [show encodeSplitAppend used remaining suffix =
      MachineDescription.encodeNatAppend used
        (splitMarker ::
          MachineDescription.encodeNatAppend remaining suffix) by rfl]
  rw [nat_run_exact target usedState markerState used leftRev
    (splitMarker ::
      MachineDescription.encodeNatAppend remaining suffix)
    husedTick husedDone]
  simp only
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine target) 1 (remaining + 1)]
  rw [TuringMachine.runConfigExact?]
  rw [symbol_step target markerState remainingState splitMarker _ _ hmarker]
  change (machine target).runConfigExact? (remaining + 1)
    (config remainingState
      (splitMarker :: MachineCodeSymbol.done ::
        List.append
          (Scheduler.Advance.ExhaustedSplitReset.ticks used)
          leftRev)
      (MachineDescription.encodeNatAppend remaining suffix)) = _
  rw [nat_run_exact target remainingState next remaining _ suffix
    hremainingTick hremainingDone]

theorem geometry_to_round_exact (target : Target)
    (geometry : Scheduler.Layout.Geometry)
    (rest : Word MachineCodeSymbol) (hnotRound : target ≠ .round) :
    (machine target).runConfigExact?
        (MachineCodeSymbol.header ::
          Scheduler.Layout.encodeGeometryAppend geometry []).length
        (config .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry rest)) =
      some (config .round
        (MachineCodeSymbol.header ::
          Scheduler.Layout.encodeGeometryAppend geometry []).reverse
        rest) := by
  have hafter : afterGeometry target = .round := by
    simp [afterGeometry, hnotRound]
  cases geometry with
  | unbounded =>
      change (machine target).runConfigExact? 2
        (config .header ([] : Word MachineCodeSymbol)
          (MachineCodeSymbol.header :: MachineCodeSymbol.blank :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [symbol_step target .header .geometry MachineCodeSymbol.header
        ([] : Word MachineCodeSymbol) _ (by rfl)]
      simp only
      rw [TuringMachine.runConfigExact?]
      rw [symbol_step target .geometry .round MachineCodeSymbol.blank
        [MachineCodeSymbol.header] rest (by
          simp [transition, hafter])]
      rfl
  | bounded budget =>
      rw [show
        (MachineCodeSymbol.header ::
          Scheduler.Layout.encodeGeometryAppend
            (.bounded budget) []).length = 2 + (budget + 1) by
        simp [Scheduler.Layout.encodeGeometryAppend,
          MachineDescription.encodeNatAppend,
          Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
          Scheduler.Advance.ExhaustedSplitReset.ticks]
        <;> lia]
      rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
        (machine target) 2 (budget + 1)]
      change (match
        (machine target).runConfigExact? 2
          (config .header []
            (MachineCodeSymbol.header :: MachineCodeSymbol.zero ::
              MachineDescription.encodeNatAppend budget rest)) with
        | none => none
        | some middle =>
            (machine target).runConfigExact? (budget + 1) middle) = _
      rw [TuringMachine.runConfigExact?]
      rw [symbol_step target .header .geometry MachineCodeSymbol.header
        [] _ (by rfl)]
      simp only
      rw [TuringMachine.runConfigExact?]
      rw [symbol_step target .geometry .budget MachineCodeSymbol.zero
        [MachineCodeSymbol.header] _ (by rfl)]
      change (machine target).runConfigExact? (budget + 1)
        (config .budget
          [MachineCodeSymbol.zero, MachineCodeSymbol.header]
          (MachineDescription.encodeNatAppend budget rest)) = _
      rw [nat_run_exact target .budget .round budget _ rest
        (by rfl) (by simp [transition, hafter])]
      simp [Scheduler.Layout.encodeGeometryAppend,
        MachineDescription.encodeNatAppend,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        List.reverse_append, List.append_assoc]

def geometrySteps (geometry : Scheduler.Layout.Geometry) : Nat :=
  (MachineCodeSymbol.header ::
    Scheduler.Layout.encodeGeometryAppend geometry []).length

def geometryPrefixRev
    (geometry : Scheduler.Layout.Geometry) :
    Word MachineCodeSymbol :=
  (MachineCodeSymbol.header ::
    Scheduler.Layout.encodeGeometryAppend geometry []).reverse

def natPrefixRev (count : Nat) (leftRev : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.done ::
    List.append
      (Scheduler.Advance.ExhaustedSplitReset.ticks count) leftRev

def splitPrefixRev (used remaining : Nat)
    (leftRev : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.done ::
    List.append
      (Scheduler.Advance.ExhaustedSplitReset.ticks remaining)
      (splitMarker :: natPrefixRev used leftRev)

theorem to_fuelUsed_exact (target : Target)
    (geometry : Scheduler.Layout.Geometry) (round : Nat)
    (suffix : Word MachineCodeSymbol)
    (hnotRound : target ≠ .round) (hnotFuel : target ≠ .fuel) :
    (machine target).runConfigExact?
        (geometrySteps geometry + (round + 1))
        (config .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round suffix))) =
      some (config .fuelUsed
        (natPrefixRev round (geometryPrefixRev geometry)) suffix) := by
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine target) (geometrySteps geometry) (round + 1)]
  unfold geometrySteps geometryPrefixRev
  rw [geometry_to_round_exact target geometry
    (MachineDescription.encodeNatAppend round suffix) hnotRound]
  change (machine target).runConfigExact? (round + 1)
    (config .round
      (MachineCodeSymbol.header ::
        Scheduler.Layout.encodeGeometryAppend geometry []).reverse
      (MachineDescription.encodeNatAppend round suffix)) = _
  rw [nat_run_exact target .round .fuelUsed round _ suffix
    (by rfl) (by simp [transition, afterRound, hnotFuel])]
  rfl

def toOuterSteps (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining : Nat) : Nat :=
  (geometrySteps geometry + (round + 1)) +
    splitSteps fuelUsed fuelRemaining

theorem to_outerUsed_exact (target : Target)
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining : Nat)
    (suffix : Word MachineCodeSymbol)
    (hnotRound : target ≠ .round) (hnotFuel : target ≠ .fuel)
    (hnotOuter : target ≠ .outer) :
    (machine target).runConfigExact?
        (toOuterSteps geometry round fuelUsed fuelRemaining)
        (config .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round
                (encodeSplitAppend fuelUsed fuelRemaining suffix)))) =
      some (config .outerUsed
        (splitPrefixRev fuelUsed fuelRemaining
          (natPrefixRev round (geometryPrefixRev geometry))) suffix) := by
  unfold toOuterSteps
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine target) (geometrySteps geometry + (round + 1))
      (splitSteps fuelUsed fuelRemaining)]
  rw [to_fuelUsed_exact target geometry round
    (encodeSplitAppend fuelUsed fuelRemaining suffix)
    hnotRound hnotFuel]
  change (machine target).runConfigExact?
    (splitSteps fuelUsed fuelRemaining)
    (config .fuelUsed
      (natPrefixRev round (geometryPrefixRev geometry))
      (encodeSplitAppend fuelUsed fuelRemaining suffix)) = _
  rw [split_run_exact target .fuelUsed .fuelMarker .fuelRemaining
    .outerUsed fuelUsed fuelRemaining _ suffix
    (by rfl) (by rfl) (by rfl) (by rfl)
    (by simp [transition, afterFuel, hnotOuter])]
  rfl

def toInnerSteps (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining : Nat) : Nat :=
  toOuterSteps geometry round fuelUsed fuelRemaining +
    splitSteps outerUsed outerRemaining

theorem to_innerUsed_exact (target : Target)
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining : Nat)
    (suffix : Word MachineCodeSymbol)
    (hnotRound : target ≠ .round) (hnotFuel : target ≠ .fuel)
    (hnotOuter : target ≠ .outer) (hnotInner : target ≠ .inner) :
    (machine target).runConfigExact?
        (toInnerSteps geometry round fuelUsed fuelRemaining
          outerUsed outerRemaining)
        (config .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round
                (encodeSplitAppend fuelUsed fuelRemaining
                  (encodeSplitAppend outerUsed outerRemaining suffix))))) =
      some (config .innerUsed
        (splitPrefixRev outerUsed outerRemaining
          (splitPrefixRev fuelUsed fuelRemaining
            (natPrefixRev round (geometryPrefixRev geometry)))) suffix) := by
  unfold toInnerSteps
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine target)
      (toOuterSteps geometry round fuelUsed fuelRemaining)
      (splitSteps outerUsed outerRemaining)]
  rw [to_outerUsed_exact target geometry round fuelUsed fuelRemaining
    (encodeSplitAppend outerUsed outerRemaining suffix)
    hnotRound hnotFuel hnotOuter]
  change (machine target).runConfigExact?
    (splitSteps outerUsed outerRemaining)
    (config .outerUsed
      (splitPrefixRev fuelUsed fuelRemaining
        (natPrefixRev round (geometryPrefixRev geometry)))
      (encodeSplitAppend outerUsed outerRemaining suffix)) = _
  rw [split_run_exact target .outerUsed .outerMarker .outerRemaining
    .innerUsed outerUsed outerRemaining _ suffix
    (by rfl) (by rfl) (by rfl) (by rfl)
    (by simp [transition, afterOuter, hnotInner])]
  rfl

def toCandidateMarkerSteps
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining : Nat) : Nat :=
  toInnerSteps geometry round fuelUsed fuelRemaining
      outerUsed outerRemaining +
    splitSteps innerUsed innerRemaining

theorem to_candidateMarker_exact (target : Target)
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining : Nat)
    (candidateSuffix : Word MachineCodeSymbol)
    (hnotRound : target ≠ .round) (hnotFuel : target ≠ .fuel)
    (hnotOuter : target ≠ .outer) (hnotInner : target ≠ .inner) :
    (machine target).runConfigExact?
        (toCandidateMarkerSteps geometry round fuelUsed fuelRemaining
          outerUsed outerRemaining innerUsed innerRemaining)
        (config .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round
                (encodeSplitAppend fuelUsed fuelRemaining
                  (encodeSplitAppend outerUsed outerRemaining
                    (encodeSplitAppend innerUsed innerRemaining
                      (candidateMarker :: candidateSuffix))))))) =
      some (config .candidateMarker
        (splitPrefixRev innerUsed innerRemaining
          (splitPrefixRev outerUsed outerRemaining
            (splitPrefixRev fuelUsed fuelRemaining
              (natPrefixRev round (geometryPrefixRev geometry)))))
        (candidateMarker :: candidateSuffix)) := by
  unfold toCandidateMarkerSteps
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine target)
      (toInnerSteps geometry round fuelUsed fuelRemaining
        outerUsed outerRemaining)
      (splitSteps innerUsed innerRemaining)]
  rw [to_innerUsed_exact target geometry round fuelUsed fuelRemaining
    outerUsed outerRemaining
    (encodeSplitAppend innerUsed innerRemaining
      (candidateMarker :: candidateSuffix))
    hnotRound hnotFuel hnotOuter hnotInner]
  change (machine target).runConfigExact?
    (splitSteps innerUsed innerRemaining)
    (config .innerUsed
      (splitPrefixRev outerUsed outerRemaining
        (splitPrefixRev fuelUsed fuelRemaining
          (natPrefixRev round (geometryPrefixRev geometry))))
      (encodeSplitAppend innerUsed innerRemaining
        (candidateMarker :: candidateSuffix))) = _
  rw [split_run_exact target .innerUsed .innerMarker .innerRemaining
    .candidateMarker innerUsed innerRemaining _
    (candidateMarker :: candidateSuffix)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
  rfl

def candidatePrefixRev
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining : Nat) : Word MachineCodeSymbol :=
  candidateMarker ::
    splitPrefixRev innerUsed innerRemaining
      (splitPrefixRev outerUsed outerRemaining
        (splitPrefixRev fuelUsed fuelRemaining
          (natPrefixRev round (geometryPrefixRev geometry))))

theorem locate_candidateFuel_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining : Nat)
    (candidateSuffix : Word MachineCodeSymbol) :
    (machine .candidateFuel).runConfigExact?
        (toCandidateMarkerSteps geometry round fuelUsed fuelRemaining
          outerUsed outerRemaining innerUsed innerRemaining + 1)
        (config .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round
                (encodeSplitAppend fuelUsed fuelRemaining
                  (encodeSplitAppend outerUsed outerRemaining
                    (encodeSplitAppend innerUsed innerRemaining
                      (candidateMarker :: candidateSuffix))))))) =
      some (config .halt
        (candidatePrefixRev geometry round fuelUsed fuelRemaining
          outerUsed outerRemaining innerUsed innerRemaining)
        candidateSuffix) := by
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine .candidateFuel)
      (toCandidateMarkerSteps geometry round fuelUsed fuelRemaining
        outerUsed outerRemaining innerUsed innerRemaining) 1]
  rw [to_candidateMarker_exact .candidateFuel geometry round
    fuelUsed fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
    candidateSuffix (by decide) (by decide) (by decide) (by decide)]
  change (machine .candidateFuel).runConfigExact? 1
    (config .candidateMarker
      (splitPrefixRev innerUsed innerRemaining
        (splitPrefixRev outerUsed outerRemaining
          (splitPrefixRev fuelUsed fuelRemaining
            (natPrefixRev round (geometryPrefixRev geometry)))))
      (candidateMarker :: candidateSuffix)) = _
  rw [TuringMachine.runConfigExact?]
  rw [symbol_step .candidateFuel .candidateMarker .halt candidateMarker
    _ candidateSuffix (by rfl)]
  rfl

def locateCandidateOuterSteps
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel : Nat) : Nat :=
  toCandidateMarkerSteps geometry round fuelUsed fuelRemaining
      outerUsed outerRemaining innerUsed innerRemaining +
    (1 + (candidateFuel + 1))

theorem locate_candidateOuter_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel : Nat)
    (candidateSuffix : Word MachineCodeSymbol) :
    (machine .candidateOuter).runConfigExact?
        (locateCandidateOuterSteps geometry round fuelUsed fuelRemaining
          outerUsed outerRemaining innerUsed innerRemaining candidateFuel)
        (config .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round
                (encodeSplitAppend fuelUsed fuelRemaining
                  (encodeSplitAppend outerUsed outerRemaining
                    (encodeSplitAppend innerUsed innerRemaining
                      (candidateMarker ::
                        MachineDescription.encodeNatAppend candidateFuel
                          candidateSuffix))))))) =
      some (config .halt
        (natPrefixRev candidateFuel
          (candidatePrefixRev geometry round fuelUsed fuelRemaining
            outerUsed outerRemaining innerUsed innerRemaining))
        candidateSuffix) := by
  unfold locateCandidateOuterSteps
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine .candidateOuter)
      (toCandidateMarkerSteps geometry round fuelUsed fuelRemaining
        outerUsed outerRemaining innerUsed innerRemaining)
      (1 + (candidateFuel + 1))]
  rw [to_candidateMarker_exact .candidateOuter geometry round
    fuelUsed fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
    (MachineDescription.encodeNatAppend candidateFuel candidateSuffix)
    (by decide) (by decide) (by decide) (by decide)]
  change (machine .candidateOuter).runConfigExact?
    (1 + (candidateFuel + 1))
    (config .candidateMarker
      (splitPrefixRev innerUsed innerRemaining
        (splitPrefixRev outerUsed outerRemaining
          (splitPrefixRev fuelUsed fuelRemaining
            (natPrefixRev round (geometryPrefixRev geometry)))))
      (candidateMarker ::
        MachineDescription.encodeNatAppend candidateFuel candidateSuffix)) = _
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine .candidateOuter) 1 (candidateFuel + 1)]
  rw [TuringMachine.runConfigExact?]
  rw [symbol_step .candidateOuter .candidateMarker .candidateFuel
    candidateMarker _ _ (by rfl)]
  change (machine .candidateOuter).runConfigExact? (candidateFuel + 1)
    (config .candidateFuel
      (candidatePrefixRev geometry round fuelUsed fuelRemaining
        outerUsed outerRemaining innerUsed innerRemaining)
      (MachineDescription.encodeNatAppend candidateFuel candidateSuffix)) = _
  rw [nat_run_exact .candidateOuter .candidateFuel .halt candidateFuel
    _ candidateSuffix (by rfl) (by rfl)]
  rfl

def locateCandidateInnerSteps
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter : Nat) : Nat :=
  toCandidateMarkerSteps geometry round fuelUsed fuelRemaining
      outerUsed outerRemaining innerUsed innerRemaining +
    (1 + (candidateFuel + 1) + (candidateOuter + 1))

theorem locate_candidateInner_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining
      innerUsed innerRemaining candidateFuel candidateOuter : Nat)
    (candidateSuffix : Word MachineCodeSymbol) :
    (machine .candidateInner).runConfigExact?
        (locateCandidateInnerSteps geometry round fuelUsed fuelRemaining
          outerUsed outerRemaining innerUsed innerRemaining
          candidateFuel candidateOuter)
        (config .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round
                (encodeSplitAppend fuelUsed fuelRemaining
                  (encodeSplitAppend outerUsed outerRemaining
                    (encodeSplitAppend innerUsed innerRemaining
                      (candidateMarker ::
                        MachineDescription.encodeNatAppend candidateFuel
                          (MachineDescription.encodeNatAppend candidateOuter
                            candidateSuffix)))))))) =
      some (config .halt
        (natPrefixRev candidateOuter
          (natPrefixRev candidateFuel
            (candidatePrefixRev geometry round fuelUsed fuelRemaining
              outerUsed outerRemaining innerUsed innerRemaining)))
        candidateSuffix) := by
  unfold locateCandidateInnerSteps
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine .candidateInner)
      (toCandidateMarkerSteps geometry round fuelUsed fuelRemaining
        outerUsed outerRemaining innerUsed innerRemaining)
      (1 + (candidateFuel + 1) + (candidateOuter + 1))]
  rw [to_candidateMarker_exact .candidateInner geometry round
    fuelUsed fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
    (MachineDescription.encodeNatAppend candidateFuel
      (MachineDescription.encodeNatAppend candidateOuter candidateSuffix))
    (by decide) (by decide) (by decide) (by decide)]
  change (machine .candidateInner).runConfigExact?
    (1 + (candidateFuel + 1) + (candidateOuter + 1))
    (config .candidateMarker
      (splitPrefixRev innerUsed innerRemaining
        (splitPrefixRev outerUsed outerRemaining
          (splitPrefixRev fuelUsed fuelRemaining
            (natPrefixRev round (geometryPrefixRev geometry)))))
      (candidateMarker ::
        MachineDescription.encodeNatAppend candidateFuel
          (MachineDescription.encodeNatAppend candidateOuter
            candidateSuffix))) = _
  rw [show 1 + (candidateFuel + 1) + (candidateOuter + 1) =
      1 + ((candidateFuel + 1) + (candidateOuter + 1)) by lia]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine .candidateInner) 1
      ((candidateFuel + 1) + (candidateOuter + 1))]
  rw [TuringMachine.runConfigExact?]
  rw [symbol_step .candidateInner .candidateMarker .candidateFuel
    candidateMarker _ _ (by rfl)]
  change (machine .candidateInner).runConfigExact?
    ((candidateFuel + 1) + (candidateOuter + 1))
    (config .candidateFuel
      (candidatePrefixRev geometry round fuelUsed fuelRemaining
        outerUsed outerRemaining innerUsed innerRemaining)
      (MachineDescription.encodeNatAppend candidateFuel
        (MachineDescription.encodeNatAppend candidateOuter candidateSuffix))) = _
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (machine .candidateInner) (candidateFuel + 1) (candidateOuter + 1)]
  rw [nat_run_exact .candidateInner .candidateFuel .candidateOuter
    candidateFuel _
    (MachineDescription.encodeNatAppend candidateOuter candidateSuffix)
    (by rfl) (by rfl)]
  change (machine .candidateInner).runConfigExact? (candidateOuter + 1)
    (config .candidateOuter
      (natPrefixRev candidateFuel
        (candidatePrefixRev geometry round fuelUsed fuelRemaining
          outerUsed outerRemaining innerUsed innerRemaining))
      (MachineDescription.encodeNatAppend candidateOuter candidateSuffix)) = _
  rw [nat_run_exact .candidateInner .candidateOuter .halt candidateOuter
    _ candidateSuffix (by rfl) (by rfl)]
  rfl

end Locator

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Rollover
