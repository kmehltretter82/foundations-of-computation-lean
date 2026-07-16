import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.InnerBranch
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.RolloverRewind

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Dispatch

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

inductive Branch where
  | fuel
  | outer
  | inner
  | rollover
deriving DecidableEq

namespace Branch

def finite : Foundation.FiniteType Branch where
  elems := [.fuel, .outer, .inner, .rollover]
  complete := by
    intro branch
    cases branch <;> simp

end Branch

inductive Scan where
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
deriving DecidableEq

namespace Scan

def finite : Foundation.FiniteType Scan where
  elems := [.header, .geometry, .budget, .round, .fuelUsed, .fuelMarker,
    .fuelRemaining, .outerUsed, .outerMarker, .outerRemaining, .innerUsed,
    .innerMarker, .innerRemaining]
  complete := by
    intro scan
    cases scan <;> simp

end Scan

abbrev FuelControl := Scheduler.FuelBranch.Control
abbrev OuterControl := Scheduler.OuterBranch.Control
abbrev InnerControl := Scheduler.InnerBranch.Control
abbrev RolloverControl := Scheduler.MainRollover.Control

inductive Control where
  | scan (inner : Scan)
  | rewind (branch : Branch) (inner : RewindWord.Control)
  | fuel (inner : FuelControl)
  | outer (inner : OuterControl)
  | inner (inner : InnerControl)
  | rollover (inner : RolloverControl)
  | rolloverRewind (inner : RewindWord.Control)
  | halt
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems :=
    Scan.finite.elems.map Control.scan ++
      (Branch.finite.elems.flatMap fun branch =>
        RewindWord.Control.finite.elems.map (Control.rewind branch)) ++
      Scheduler.FuelBranch.Control.finite.elems.map Control.fuel ++
      Scheduler.OuterBranch.Control.finite.elems.map Control.outer ++
      Scheduler.InnerBranch.Control.finite.elems.map Control.inner ++
      Scheduler.MainRollover.Control.finite.elems.map
        Control.rollover ++
      RewindWord.Control.finite.elems.map Control.rolloverRewind ++ [.halt]
  complete := by
    intro control
    cases control with
    | scan inner =>
        simp
        exact Scan.finite.complete inner
    | rewind branch inner =>
        simp
        exact ⟨Branch.finite.complete branch,
          RewindWord.Control.finite.complete inner⟩
    | fuel inner =>
        simp
        exact Scheduler.FuelBranch.Control.finite.complete inner
    | outer inner =>
        simp
        exact Scheduler.OuterBranch.Control.finite.complete inner
    | inner inner =>
        simp
        exact Scheduler.InnerBranch.Control.finite.complete inner
    | rollover inner =>
        simp
        exact Scheduler.MainRollover.Control.finite.complete inner
    | rolloverRewind inner =>
        simp
        exact RewindWord.Control.finite.complete inner
    | halt => simp

end Control

def mapAction (embed : inner -> Control) :
    Option (Option MachineCodeSymbol × Direction × inner) ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | none => none
  | some (write, direction, target) =>
      some (write, direction, embed target)

def branchStart : Branch -> Control
  | .fuel => .fuel Scheduler.FuelBranch.machine.start
  | .outer => .outer Scheduler.OuterBranch.machine.start
  | .inner => .inner Scheduler.InnerBranch.machine.start
  | .rollover => .rollover Scheduler.MainRollover.machine.start

def rewindEmbed (branch : Branch) : RewindWord.Control -> Control
  | .gate => branchStart branch
  | inner => .rewind branch inner

def fuelEmbed (inner : FuelControl) : Control :=
  if inner = Scheduler.FuelBranch.machine.halt then .halt
  else .fuel inner

def outerEmbed (inner : OuterControl) : Control :=
  if inner = Scheduler.OuterBranch.machine.halt then .halt
  else .outer inner

def innerEmbed (inner : InnerControl) : Control :=
  if inner = Scheduler.InnerBranch.machine.halt then .halt
  else .inner inner

def rolloverEmbed (inner : RolloverControl) : Control :=
  if inner = Scheduler.MainRollover.machine.halt then
    .rolloverRewind RewindWord.machine.start
  else .rollover inner

def rolloverRewindEmbed : RewindWord.Control -> Control
  | .gate => .halt
  | inner => .rolloverRewind inner

def decideBranch (branch : Branch) (read : Option MachineCodeSymbol) :
    Option (Option MachineCodeSymbol × Direction × Control) :=
  some (read, Direction.left, .rewind branch .scan)

def transition : Control -> Option MachineCodeSymbol ->
    Option (Option MachineCodeSymbol × Direction × Control)
  | .scan .header, some .header =>
      some (some .header, Direction.right, .scan .geometry)
  | .scan .geometry, some .blank =>
      some (some .blank, Direction.right, .scan .round)
  | .scan .geometry, some .zero =>
      some (some .zero, Direction.right, .scan .budget)
  | .scan .budget, some .tick =>
      some (some .tick, Direction.right, .scan .budget)
  | .scan .budget, some .done =>
      some (some .done, Direction.right, .scan .round)
  | .scan .round, some .tick =>
      some (some .tick, Direction.right, .scan .round)
  | .scan .round, some .done =>
      some (some .done, Direction.right, .scan .fuelUsed)
  | .scan .fuelUsed, some .tick =>
      some (some .tick, Direction.right, .scan .fuelUsed)
  | .scan .fuelUsed, some .done =>
      some (some .done, Direction.right, .scan .fuelMarker)
  | .scan .fuelMarker, some .transition =>
      some (some .transition, Direction.right, .scan .fuelRemaining)
  | .scan .fuelRemaining, some .tick =>
      decideBranch .fuel (some .tick)
  | .scan .fuelRemaining, some .done =>
      some (some .done, Direction.right, .scan .outerUsed)
  | .scan .outerUsed, some .tick =>
      some (some .tick, Direction.right, .scan .outerUsed)
  | .scan .outerUsed, some .done =>
      some (some .done, Direction.right, .scan .outerMarker)
  | .scan .outerMarker, some .transition =>
      some (some .transition, Direction.right, .scan .outerRemaining)
  | .scan .outerRemaining, some .tick =>
      decideBranch .outer (some .tick)
  | .scan .outerRemaining, some .done =>
      some (some .done, Direction.right, .scan .innerUsed)
  | .scan .innerUsed, some .tick =>
      some (some .tick, Direction.right, .scan .innerUsed)
  | .scan .innerUsed, some .done =>
      some (some .done, Direction.right, .scan .innerMarker)
  | .scan .innerMarker, some .transition =>
      some (some .transition, Direction.right, .scan .innerRemaining)
  | .scan .innerRemaining, some .tick =>
      decideBranch .inner (some .tick)
  | .scan .innerRemaining, some .done =>
      decideBranch .rollover (some .done)
  | .rewind branch inner, read =>
      mapAction (rewindEmbed branch) (RewindWord.transition inner read)
  | .fuel inner, read =>
      mapAction fuelEmbed (Scheduler.FuelBranch.transition inner read)
  | .outer inner, read =>
      mapAction outerEmbed (Scheduler.OuterBranch.transition inner read)
  | .inner inner, read =>
      mapAction innerEmbed (Scheduler.InnerBranch.transition inner read)
  | .rollover inner, read =>
      mapAction rolloverEmbed
        (Scheduler.MainRollover.transition inner read)
  | .rolloverRewind inner, read =>
      mapAction rolloverRewindEmbed (RewindWord.transition inner read)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .scan .header
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

theorem rewind_map (branch : Branch) (state : RewindWord.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × RewindWord.Control)
    (haction : RewindWord.machine.transition state read = some action) :
    transition (rewindEmbed branch state) read =
      mapAction (rewindEmbed branch) (some action) := by
  cases branch <;> cases state <;>
    simp_all [RewindWord.machine, RewindWord.transition, transition,
      rewindEmbed, branchStart, mapAction]

theorem fuel_map (state : FuelControl) (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × FuelControl)
    (haction : Scheduler.FuelBranch.machine.transition state read =
      some action) :
    transition (fuelEmbed state) read = mapAction fuelEmbed (some action) := by
  by_cases hhalt : state = Scheduler.FuelBranch.machine.halt
  · subst state
    simp [Scheduler.FuelBranch.machine,
      Scheduler.FuelBranch.transition] at haction
  · change Scheduler.FuelBranch.transition state read =
      some action at haction
    simp [fuelEmbed, hhalt, transition, haction]

theorem outer_map (state : OuterControl) (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × OuterControl)
    (haction : Scheduler.OuterBranch.machine.transition state read =
      some action) :
    transition (outerEmbed state) read = mapAction outerEmbed (some action) := by
  by_cases hhalt : state = Scheduler.OuterBranch.machine.halt
  · subst state
    simp [Scheduler.OuterBranch.machine,
      Scheduler.OuterBranch.transition] at haction
  · change Scheduler.OuterBranch.transition state read =
      some action at haction
    simp [outerEmbed, hhalt, transition, haction]

theorem inner_map (state : InnerControl) (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × InnerControl)
    (haction : Scheduler.InnerBranch.machine.transition state read =
      some action) :
    transition (innerEmbed state) read = mapAction innerEmbed (some action) := by
  by_cases hhalt : state = Scheduler.InnerBranch.machine.halt
  · subst state
    simp [Scheduler.InnerBranch.machine,
      Scheduler.InnerBranch.transition] at haction
  · change Scheduler.InnerBranch.transition state read =
      some action at haction
    simp [innerEmbed, hhalt, transition, haction]

theorem rollover_map (state : RolloverControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × RolloverControl)
    (haction : Scheduler.MainRollover.machine.transition state read =
      some action) :
    transition (rolloverEmbed state) read =
      mapAction rolloverEmbed (some action) := by
  by_cases hhalt : state = Scheduler.MainRollover.machine.halt
  · subst state
    simp [Scheduler.MainRollover.machine,
      Scheduler.MainRollover.transition] at haction
  · change Scheduler.MainRollover.transition state read =
      some action at haction
    simp [rolloverEmbed, hhalt, transition, haction]

theorem rolloverRewind_map (state : RewindWord.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × RewindWord.Control)
    (haction : RewindWord.machine.transition state read = some action) :
    transition (rolloverRewindEmbed state) read =
      mapAction rolloverRewindEmbed (some action) := by
  cases state <;>
    simp_all [RewindWord.machine, RewindWord.transition, transition,
      rolloverRewindEmbed, mapAction]

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

def scanConfig (state : Scan) (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .scan state
    tape := Scheduler.MainRollover.ExactRewind.startTape leftRev rest }

theorem scan_symbol_step (state next : Scan) (current : MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol)
    (htransition : transition (.scan state) (some current) =
      some (some current, Direction.right, .scan next)) :
    machine.stepConfig (scanConfig state leftRev (current :: suffix)) =
      some (scanConfig next (current :: leftRev) suffix) := by
  cases leftRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, scanConfig,
      Scheduler.MainRollover.ExactRewind.startTape,
      ExactFuel.StrictProbe.SerializedShift.cursorTape,
      Tape.read, Tape.write, Tape.move, Tape.moveRight, htransition]

theorem scan_ticks_exact (state : Scan) (count : Nat)
    (leftRev suffix : Word MachineCodeSymbol)
    (htick : transition (.scan state) (some MachineCodeSymbol.tick) =
      some (some MachineCodeSymbol.tick, Direction.right, .scan state)) :
    machine.runConfigExact? count
        (scanConfig state leftRev
          (List.append
            (Scheduler.Advance.ExhaustedSplitReset.ticks count)
            suffix)) =
      some (scanConfig state
        (List.append
          (Scheduler.Advance.ExhaustedSplitReset.ticks count) leftRev)
        suffix) := by
  induction count generalizing leftRev with
  | zero => rfl
  | succ count ih =>
      change machine.runConfigExact? (count + 1)
        (scanConfig state leftRev
          (MachineCodeSymbol.tick ::
            List.append
              (Scheduler.Advance.ExhaustedSplitReset.ticks count)
              suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_symbol_step state state MachineCodeSymbol.tick leftRev _ htick]
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

theorem scan_nat_exact (state next : Scan) (count : Nat)
    (leftRev suffix : Word MachineCodeSymbol)
    (htick : transition (.scan state) (some MachineCodeSymbol.tick) =
      some (some MachineCodeSymbol.tick, Direction.right, .scan state))
    (hdone : transition (.scan state) (some MachineCodeSymbol.done) =
      some (some MachineCodeSymbol.done, Direction.right, .scan next)) :
    machine.runConfigExact? (count + 1)
        (scanConfig state leftRev
          (MachineDescription.encodeNatAppend count suffix)) =
      some (scanConfig next
        (MachineCodeSymbol.done ::
          List.append
            (Scheduler.Advance.ExhaustedSplitReset.ticks count)
            leftRev)
        suffix) := by
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append machine
    count 1]
  rw [show MachineDescription.encodeNatAppend count suffix =
      List.append
        (Scheduler.Advance.ExhaustedSplitReset.ticks count)
        (MachineCodeSymbol.done :: suffix) by
    simp [MachineDescription.encodeNatAppend,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      List.append_assoc]]
  rw [scan_ticks_exact state count leftRev
    (MachineCodeSymbol.done :: suffix) htick]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [scan_symbol_step state next MachineCodeSymbol.done _ suffix hdone]
  rfl

theorem scan_zero_exact (state next : Scan)
    (leftRev suffix : Word MachineCodeSymbol)
    (hdone : transition (.scan state) (some MachineCodeSymbol.done) =
      some (some MachineCodeSymbol.done, Direction.right, .scan next)) :
    machine.runConfigExact? 1
        (scanConfig state leftRev
          (MachineDescription.encodeNatAppend 0 suffix)) =
      some (scanConfig next (MachineCodeSymbol.done :: leftRev) suffix) := by
  have hzero : MachineDescription.encodeNatAppend 0 suffix =
      MachineCodeSymbol.done :: suffix := by
    simp [MachineDescription.encodeNatAppend, MachineDescription.encodeNat]
  rw [hzero, TuringMachine.runConfigExact?]
  rw [scan_symbol_step state next MachineCodeSymbol.done leftRev suffix hdone]
  simp only [TuringMachine.runConfigExact?]

def geometrySteps : Scheduler.Layout.Geometry -> Nat
  | .unbounded => 2
  | .bounded budget => 2 + (budget + 1)

theorem scan_geometry_exact (geometry : Scheduler.Layout.Geometry)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (geometrySteps geometry)
        (scanConfig .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry suffix)) =
      some (scanConfig .round
        (Scheduler.Rollover.Locator.geometryPrefixRev geometry)
        suffix) := by
  cases geometry with
  | unbounded =>
      change machine.runConfigExact? 2
        (scanConfig .header []
          (MachineCodeSymbol.header :: MachineCodeSymbol.blank :: suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_symbol_step .header .geometry MachineCodeSymbol.header []
        (MachineCodeSymbol.blank :: suffix) (by rfl)]
      simp only
      rw [TuringMachine.runConfigExact?]
      rw [scan_symbol_step .geometry .round MachineCodeSymbol.blank
        [MachineCodeSymbol.header] suffix (by rfl)]
      rfl
  | bounded budget =>
      change machine.runConfigExact? (2 + (budget + 1))
        (scanConfig .header []
          (MachineCodeSymbol.header :: MachineCodeSymbol.zero ::
            MachineDescription.encodeNatAppend budget suffix)) = _
      rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append machine
        2 (budget + 1)]
      rw [TuringMachine.runConfigExact?]
      rw [scan_symbol_step .header .geometry MachineCodeSymbol.header []
        (MachineCodeSymbol.zero ::
          MachineDescription.encodeNatAppend budget suffix) (by rfl)]
      simp only
      rw [TuringMachine.runConfigExact?]
      rw [scan_symbol_step .geometry .budget MachineCodeSymbol.zero
        [MachineCodeSymbol.header]
        (MachineDescription.encodeNatAppend budget suffix) (by rfl)]
      simp only [TuringMachine.runConfigExact?]
      have hprefix :
          Scheduler.Rollover.Locator.geometryPrefixRev
              (.bounded budget) =
            MachineCodeSymbol.done ::
              List.append
                (Scheduler.Advance.ExhaustedSplitReset.ticks budget)
                [MachineCodeSymbol.zero, MachineCodeSymbol.header] := by
        simp [Scheduler.Rollover.Locator.geometryPrefixRev,
          Scheduler.Layout.encodeGeometryAppend,
          MachineDescription.encodeNatAppend,
          Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
          Scheduler.Advance.ExhaustedSplitReset.ticks,
          List.reverse_append, List.reverse_replicate, List.append_assoc]
      rw [hprefix]
      exact scan_nat_exact .budget .round budget
        ([MachineCodeSymbol.zero, MachineCodeSymbol.header] :
          Word MachineCodeSymbol) suffix (by rfl) (by rfl)

def fuelRemainingPrefixRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed : Nat) : Word MachineCodeSymbol :=
  Scheduler.SplitLayout.splitMarker ::
    Scheduler.Rollover.Locator.natPrefixRev fuelUsed
      (Scheduler.Rollover.Locator.natPrefixRev round
        (Scheduler.Rollover.Locator.geometryPrefixRev geometry))

def toFuelRemainingSteps (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed : Nat) : Nat :=
  geometrySteps geometry + (round + 1) + (fuelUsed + 1) + 1

theorem scan_to_fuelRemaining_exact
    (geometry : Scheduler.Layout.Geometry) (round fuelUsed : Nat)
    (fuelRemaining : Nat) (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (toFuelRemainingSteps geometry round fuelUsed)
        (scanConfig .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round
                (Scheduler.SplitLayout.encodeSplitAppend fuelUsed
                  fuelRemaining suffix)))) =
      some (scanConfig .fuelRemaining
        (fuelRemainingPrefixRev geometry round fuelUsed)
        (MachineDescription.encodeNatAppend fuelRemaining suffix)) := by
  unfold toFuelRemainingSteps
  rw [show geometrySteps geometry + (round + 1) + (fuelUsed + 1) + 1 =
      geometrySteps geometry + ((round + 1) + (fuelUsed + 1) + 1) by lia]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  rw [scan_geometry_exact geometry
    (MachineDescription.encodeNatAppend round
      (Scheduler.SplitLayout.encodeSplitAppend fuelUsed fuelRemaining
        suffix))]
  simp only
  rw [show (round + 1) + (fuelUsed + 1) + 1 =
      (round + 1) + ((fuelUsed + 1) + 1) by lia]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  rw [scan_nat_exact .round .fuelUsed round
    (Scheduler.Rollover.Locator.geometryPrefixRev geometry)
    (Scheduler.SplitLayout.encodeSplitAppend fuelUsed fuelRemaining
      suffix)
    (by rfl) (by rfl)]
  simp only
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  unfold Scheduler.SplitLayout.encodeSplitAppend
  rw [scan_nat_exact .fuelUsed .fuelMarker fuelUsed
    (MachineCodeSymbol.done ::
      List.append (Scheduler.Advance.ExhaustedSplitReset.ticks round)
        (Scheduler.Rollover.Locator.geometryPrefixRev geometry))
    (Scheduler.SplitLayout.splitMarker ::
      MachineDescription.encodeNatAppend fuelRemaining suffix)
    (by rfl) (by rfl)]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [scan_symbol_step .fuelMarker .fuelRemaining
    Scheduler.SplitLayout.splitMarker
    (MachineCodeSymbol.done ::
      List.append (Scheduler.Advance.ExhaustedSplitReset.ticks fuelUsed)
        (MachineCodeSymbol.done ::
          List.append (Scheduler.Advance.ExhaustedSplitReset.ticks round)
            (Scheduler.Rollover.Locator.geometryPrefixRev geometry)))
    (MachineDescription.encodeNatAppend fuelRemaining suffix) (by rfl)]
  rfl

def outerRemainingPrefixRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed : Nat) : Word MachineCodeSymbol :=
  Scheduler.SplitLayout.splitMarker ::
    Scheduler.Rollover.Locator.natPrefixRev outerUsed
      (MachineCodeSymbol.done ::
        fuelRemainingPrefixRev geometry round fuelUsed)

def toOuterRemainingSteps (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed : Nat) : Nat :=
  toFuelRemainingSteps geometry round fuelUsed + 1 + (outerUsed + 1) + 1

theorem scan_to_outerRemaining_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (toOuterRemainingSteps geometry round fuelUsed outerUsed)
        (scanConfig .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round
                (Scheduler.SplitLayout.encodeSplitAppend fuelUsed 0
                  (Scheduler.SplitLayout.encodeSplitAppend outerUsed
                    outerRemaining suffix))))) =
      some (scanConfig .outerRemaining
        (outerRemainingPrefixRev geometry round fuelUsed outerUsed)
        (MachineDescription.encodeNatAppend outerRemaining suffix)) := by
  unfold toOuterRemainingSteps
  rw [show toFuelRemainingSteps geometry round fuelUsed + 1 +
      (outerUsed + 1) + 1 =
    toFuelRemainingSteps geometry round fuelUsed +
      (1 + (outerUsed + 1) + 1) by lia]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  rw [scan_to_fuelRemaining_exact geometry round fuelUsed
    0 (Scheduler.SplitLayout.encodeSplitAppend outerUsed outerRemaining
      suffix)]
  simp only
  rw [show 1 + (outerUsed + 1) + 1 = 1 + ((outerUsed + 1) + 1) by lia]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  rw [scan_zero_exact .fuelRemaining .outerUsed
    (fuelRemainingPrefixRev geometry round fuelUsed)
    (Scheduler.SplitLayout.encodeSplitAppend outerUsed outerRemaining
      suffix) (by rfl)]
  simp only
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  unfold Scheduler.SplitLayout.encodeSplitAppend
  rw [scan_nat_exact .outerUsed .outerMarker outerUsed
    (MachineCodeSymbol.done ::
      fuelRemainingPrefixRev geometry round fuelUsed)
    (Scheduler.SplitLayout.splitMarker ::
      MachineDescription.encodeNatAppend outerRemaining suffix)
    (by rfl) (by rfl)]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [scan_symbol_step .outerMarker .outerRemaining
    Scheduler.SplitLayout.splitMarker
    (MachineCodeSymbol.done ::
      List.append
        (Scheduler.Advance.ExhaustedSplitReset.ticks outerUsed)
        (MachineCodeSymbol.done ::
          fuelRemainingPrefixRev geometry round fuelUsed))
    (MachineDescription.encodeNatAppend outerRemaining suffix) (by rfl)]
  rfl

def innerRemainingPrefixRev (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed : Nat) : Word MachineCodeSymbol :=
  Scheduler.SplitLayout.splitMarker ::
    Scheduler.Rollover.Locator.natPrefixRev innerUsed
      (MachineCodeSymbol.done ::
        outerRemainingPrefixRev geometry round fuelUsed outerUsed)

def toInnerRemainingSteps (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed : Nat) : Nat :=
  toOuterRemainingSteps geometry round fuelUsed outerUsed + 1 +
    (innerUsed + 1) + 1

theorem scan_to_innerRemaining_exact
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (toInnerRemainingSteps geometry round fuelUsed outerUsed innerUsed)
        (scanConfig .header []
          (MachineCodeSymbol.header ::
            Scheduler.Layout.encodeGeometryAppend geometry
              (MachineDescription.encodeNatAppend round
                (Scheduler.SplitLayout.encodeSplitAppend fuelUsed 0
                  (Scheduler.SplitLayout.encodeSplitAppend outerUsed 0
                    (Scheduler.SplitLayout.encodeSplitAppend innerUsed
                      innerRemaining suffix)))))) =
      some (scanConfig .innerRemaining
        (innerRemainingPrefixRev geometry round fuelUsed outerUsed innerUsed)
        (MachineDescription.encodeNatAppend innerRemaining suffix)) := by
  unfold toInnerRemainingSteps
  rw [show toOuterRemainingSteps geometry round fuelUsed outerUsed + 1 +
      (innerUsed + 1) + 1 =
    toOuterRemainingSteps geometry round fuelUsed outerUsed +
      (1 + (innerUsed + 1) + 1) by lia]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  rw [scan_to_outerRemaining_exact geometry round fuelUsed outerUsed
    0 (Scheduler.SplitLayout.encodeSplitAppend innerUsed innerRemaining
      suffix)]
  simp only
  rw [show 1 + (innerUsed + 1) + 1 = 1 + ((innerUsed + 1) + 1) by lia]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  rw [scan_zero_exact .outerRemaining .innerUsed
    (outerRemainingPrefixRev geometry round fuelUsed outerUsed)
    (Scheduler.SplitLayout.encodeSplitAppend innerUsed innerRemaining
      suffix) (by rfl)]
  simp only
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  unfold Scheduler.SplitLayout.encodeSplitAppend
  rw [scan_nat_exact .innerUsed .innerMarker innerUsed
    (MachineCodeSymbol.done ::
      outerRemainingPrefixRev geometry round fuelUsed outerUsed)
    (Scheduler.SplitLayout.splitMarker ::
      MachineDescription.encodeNatAppend innerRemaining suffix)
    (by rfl) (by rfl)]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [scan_symbol_step .innerMarker .innerRemaining
    Scheduler.SplitLayout.splitMarker
    (MachineCodeSymbol.done ::
      List.append
        (Scheduler.Advance.ExhaustedSplitReset.ticks innerUsed)
        (MachineCodeSymbol.done ::
          outerRemainingPrefixRev geometry round fuelUsed outerUsed))
    (MachineDescription.encodeNatAppend innerRemaining suffix) (by rfl)]
  rfl

theorem decision_step (branch : Branch) (state : Scan)
    (current : MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol)
    (hdecision : transition (.scan state) (some current) =
      decideBranch branch (some current)) :
    machine.stepConfig (scanConfig state leftRev (current :: suffix)) =
      some (TuringMachine.PhaseEmbedding.liftConfig (rewindEmbed branch)
        (RewindWord.scanConfig leftRev (current :: suffix) 0)) := by
  unfold TuringMachine.stepConfig
  dsimp [machine]
  cases branch <;> cases leftRev <;> cases suffix <;>
    simp only [scanConfig,
      Scheduler.MainRollover.ExactRewind.startTape, Tape.read] at * <;>
    rw [hdecision] <;>
    simp only [decideBranch] <;>
    rfl

theorem decision_rewind_exact (branch : Branch) (state : Scan)
    (current : MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol)
    (hdecision : transition (.scan state) (some current) =
      decideBranch branch (some current)) :
    machine.runConfigExact? (1 + (leftRev.length + 1))
        (scanConfig state leftRev (current :: suffix)) =
      some (TuringMachine.PhaseEmbedding.liftConfig (rewindEmbed branch)
        (RewindWord.gateConfig
          (List.append leftRev.reverse (current :: suffix)) 0)) := by
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append machine 1
    (leftRev.length + 1)]
  rw [TuringMachine.runConfigExact?]
  rw [decision_step branch state current leftRev suffix hdecision]
  simp only [TuringMachine.runConfigExact?]
  exact
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (rewindEmbed branch)
      (step_of_mapped_transition RewindWord.machine (rewindEmbed branch)
        (rewind_map branch))
      (Scheduler.MainRollover.ExactRewind.scan_run_exact leftRev
        (current :: suffix))

theorem decision_rewind (branch : Branch) (state : Scan)
    (current : MachineCodeSymbol) (leftRev suffix : Word MachineCodeSymbol)
    (hdecision : transition (.scan state) (some current) =
      decideBranch branch (some current)) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (scanConfig state leftRev (current :: suffix))
        { state := branchStart branch, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input (List.append leftRev.reverse (current :: suffix)))
        targetTape := by
  let targetTape := RewindWord.gateTape
    (List.append leftRev.reverse (current :: suffix)) 0
  refine ⟨targetTape, ?_, ?_⟩
  · exact TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        (decision_rewind_exact branch state current leftRev suffix hdecision))
  · exact Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (List.append leftRev.reverse (current :: suffix)) 0)

theorem encodeNatAppend_succ (count : Nat)
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeNatAppend (count + 1) suffix =
      MachineCodeSymbol.tick ::
        MachineDescription.encodeNatAppend count suffix := by
  rfl

theorem fuel_decision_word
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed fuelRemaining outerUsed outerRemaining innerUsed
      innerRemaining candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    List.append (fuelRemainingPrefixRev geometry round fuelUsed).reverse
        (MachineCodeSymbol.tick ::
          MachineDescription.encodeNatAppend fuelRemaining
            (Scheduler.FuelBranch.tail outerUsed outerRemaining
              innerUsed innerRemaining candidateFuel candidateOuter
              candidateInner input)) =
      Scheduler.FuelBranch.sourceWord geometry round fuelUsed
        fuelRemaining outerUsed outerRemaining innerUsed innerRemaining
        candidateFuel candidateOuter candidateInner input := by
  cases geometry <;>
    simp [fuelRemainingPrefixRev, Scheduler.FuelBranch.sourceWord,
      Scheduler.FuelBranch.tail, Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.natPrefixRev,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.reverse_append, List.append_assoc]

theorem outer_decision_word
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed outerRemaining innerUsed innerRemaining
      candidateFuel candidateOuter candidateInner : Nat)
    (input : Word MachineCodeSymbol) :
    List.append
        (outerRemainingPrefixRev geometry round fuelUsed outerUsed).reverse
        (MachineCodeSymbol.tick ::
          MachineDescription.encodeNatAppend outerRemaining
            (Scheduler.OuterBranch.outerSuffix innerUsed innerRemaining
              candidateFuel candidateOuter candidateInner input)) =
      Scheduler.OuterBranch.sourceWord geometry round fuelUsed outerUsed
        outerRemaining innerUsed innerRemaining candidateFuel candidateOuter
        candidateInner input := by
  cases geometry <;>
    simp [outerRemainingPrefixRev, fuelRemainingPrefixRev,
      Scheduler.OuterBranch.sourceWord,
      Scheduler.OuterBranch.outerSuffix,
      Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.natPrefixRev,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.reverse_append, List.append_assoc]

theorem inner_decision_word
    (geometry : Scheduler.Layout.Geometry)
    (round fuelUsed outerUsed innerUsed innerRemaining candidateFuel
      candidateOuter candidateInner : Nat) (input : Word MachineCodeSymbol) :
    List.append
        (innerRemainingPrefixRev geometry round fuelUsed outerUsed
          innerUsed).reverse
        (MachineCodeSymbol.tick ::
          MachineDescription.encodeNatAppend innerRemaining
            (Scheduler.InnerBranch.candidateTail candidateFuel
              candidateOuter candidateInner input)) =
      Scheduler.InnerBranch.sourceWord geometry round fuelUsed outerUsed
        innerUsed innerRemaining candidateFuel candidateOuter candidateInner
        input := by
  cases geometry <;>
    simp [innerRemainingPrefixRev, outerRemainingPrefixRev,
      fuelRemainingPrefixRev, Scheduler.InnerBranch.sourceWord,
      Scheduler.InnerBranch.candidateTail,
      Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.natPrefixRev,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.reverse_append, List.append_assoc]

theorem rollover_decision_word
    (geometry : Scheduler.Layout.Geometry) (round bound : Nat)
    (input : Word MachineCodeSymbol) :
    List.append
        (innerRemainingPrefixRev geometry round round bound bound).reverse
        (MachineCodeSymbol.done ::
          Scheduler.SplitLayout.candidateMarker ::
            MachineDescription.encodeNatAppend round
              (GeneratedCode.nestedStageCode input bound bound)) =
      Scheduler.Rollover.sourceWord geometry round bound input := by
  cases geometry <;>
    simp [innerRemainingPrefixRev, outerRemainingPrefixRev,
      fuelRemainingPrefixRev, Scheduler.Rollover.sourceWord,
      Scheduler.Rollover.word,
      Scheduler.Rollover.Locator.natPrefixRev,
      Scheduler.Rollover.Locator.geometryPrefixRev,
      Scheduler.Layout.encodeGeometryAppend,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      List.reverse_append, List.append_assoc]

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Dispatch
