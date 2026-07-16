import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CleanupDelete
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CleanupGap
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CleanupShapes
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

set_option doc.verso true

/-!
# Dynamic retained-right-fuel cleanup

A single finite machine opens the protected caller boundary, repeatedly scans
the retained left-fuel field, deletes the dynamically sized right-fuel
encoding, and restores the one-gap frame. The machine stops before any
empty/nonempty branch-specific packing.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductCleanup
namespace DynamicRightFuel

private abbrev Config (state : Type) :=
  TuringMachine.Configuration MachineCodeSymbol state

/-! ## Canonical endpoint frame -/

private def oneGapTape (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := [none]
        head := none
        right := callerCells }
  | first :: rest =>
      { left := [none]
        head := some first
        right := List.append (rest.map some) (none :: callerCells) }

private def protectedOpaque
    (opaqueRight : List (Option MachineCodeSymbol)) :
    List (Option MachineCodeSymbol) :=
  some MachineCodeSymbol.header :: opaqueRight

private theorem encodeNatAppend_ne_nil (fuel : Nat)
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeNatAppend fuel suffix ≠ [] := by
  cases fuel <;> simp [MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat]

/-! ## Left-fuel scanner -/

namespace LeftFuelScanner

private inductive Control where
  | scan
  | gate
deriving DecidableEq

namespace Control

private def finite : Foundation.FiniteType Control where
  elems := [.scan, .gate]
  complete := by intro control; cases control <;> simp

end Control

private def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .scan, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .scan)
  | .scan, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .gate)
  | _, _ => none

private def machine : TuringMachine MachineCodeSymbol Control where
  start := .scan
  halt := .gate
  transition := transition
  statesFinite := Control.finite

private def tape (leftRev rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := List.append (leftRev.map some) [none]
        head := none
        right := callerCells }
  | first :: suffix =>
      { left := List.append (leftRev.map some) [none]
        head := some first
        right := List.append (suffix.map some) (none :: callerCells) }

private def config (control : Control)
    (leftRev rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Config Control :=
  { state := control
    tape := tape leftRev rest callerCells }

private theorem tick_step (leftRev suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (config .scan leftRev
          (MachineCodeSymbol.tick :: suffix) callerCells) =
      some
        (config .scan (MachineCodeSymbol.tick :: leftRev)
          suffix callerCells) := by
  cases suffix <;> cases callerCells <;> rfl

private theorem done_step (leftRev suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (config .scan leftRev
          (MachineCodeSymbol.done :: suffix) callerCells) =
      some
        (config .gate (MachineCodeSymbol.done :: leftRev)
          suffix callerCells) := by
  cases suffix <;> cases callerCells <;> rfl

private theorem run_exact_with_left (fuel : Nat)
    (leftRev suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (fuel + 1)
        (config .scan leftRev
          (MachineDescription.encodeNatAppend fuel suffix) callerCells) =
      some
        (config .gate
          (List.append (MachineDescription.encodeNat fuel).reverse leftRev)
          suffix callerCells) := by
  induction fuel generalizing leftRev with
  | zero =>
      change
        (match machine.stepConfig
            (config .scan leftRev
              (MachineCodeSymbol.done :: suffix) callerCells) with
          | none => none
          | some next => some next) =
        some
          (config .gate (MachineCodeSymbol.done :: leftRev)
            suffix callerCells)
      rw [done_step]
  | succ fuel ih =>
      change machine.runConfigExact? ((fuel + 1) + 1)
          (config .scan leftRev
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend fuel suffix) callerCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [tick_step]
      simp only
      rw [ih (MachineCodeSymbol.tick :: leftRev)]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

private theorem run_exact (fuel : Nat)
    (suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (fuel + 1)
        (config .scan []
          (MachineDescription.encodeNatAppend fuel suffix) callerCells) =
      some
        (config .gate
          (MachineDescription.encodeNat fuel).reverse suffix callerCells) := by
  simpa using run_exact_with_left fuel
    ([] : Word MachineCodeSymbol) suffix callerCells

end LeftFuelScanner

private theorem deleteOne_output_eq_encodeNatAppend
    (fuel : Nat) (suffix : Word MachineCodeSymbol) :
    ProductCleanup.DeleteOne.output
        (MachineDescription.encodeNat fuel).reverse suffix =
      MachineDescription.encodeNatAppend fuel suffix := by
  simp [ProductCleanup.DeleteOne.output,
    MachineDescription.encodeNatAppend]

private theorem deleteGate_eq_prefixRightPaddedSource
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    ProductCleanup.DeleteOne.gateTape (first :: rest) callerCells =
    ProductCleanupGap.PrefixRightShiftOne.paddedSourceTape
        (first :: rest) callerCells := by
  rfl

private theorem prefixRightTarget_eq_oneGapTape
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    ProductCleanupGap.PrefixRightShiftOne.targetTape
        (first :: rest) callerCells =
      oneGapTape (first :: rest) callerCells := by
  rfl

private theorem retainedRawPrefix_eq_nestedEncodeNatAppend
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    ProductCleanupShapes.retainedRawPrefix input leftFuel rightFuel =
      MachineDescription.encodeNatAppend leftFuel
        (MachineDescription.encodeNatAppend rightFuel input) := by
  rfl

private theorem retainedRawPrefix_ne_nil
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    ProductCleanupShapes.retainedRawPrefix input leftFuel rightFuel ≠ [] := by
  rw [retainedRawPrefix_eq_nestedEncodeNatAppend]
  exact encodeNatAppend_ne_nil leftFuel _

/-! ## Fixed dynamic cleanup machine -/

private def tokenSymbol : Bool -> MachineCodeSymbol
  | false => MachineCodeSymbol.tick
  | true => MachineCodeSymbol.done

/-- Control states for the fixed retained-right-fuel cleanup machine. The
Boolean carried by deletion and right-shift phases is true exactly for the
terminal fuel token. -/
inductive Control where
  | leftShift
      (inner : ProductCleanupGap.PrefixLeftShiftOne.Control)
  | scan
  | choose
  | delete (isDone : Bool)
      (inner : SerializedFieldComposer.DeleteOneRestagedMachine.Control)
  | rightShift (isDone : Bool)
      (inner : ProductCleanupGap.PrefixRightShiftOne.Control)
  | deleted
deriving DecidableEq

namespace Control

private def elems : List Control :=
  List.append
    (ProductCleanupGap.PrefixLeftShiftOne.machine.statesFinite.elems.map
      Control.leftShift)
    (List.append [.scan, .choose, .deleted]
      (List.append
        (SerializedFieldComposer.DeleteOneRestagedMachine.machine.statesFinite.elems.map
          (Control.delete false))
        (List.append
          (SerializedFieldComposer.DeleteOneRestagedMachine.machine.statesFinite.elems.map
            (Control.delete true))
          (List.append
            (ProductCleanupGap.PrefixRightShiftOne.machine.statesFinite.elems.map
              (Control.rightShift false))
            (ProductCleanupGap.PrefixRightShiftOne.machine.statesFinite.elems.map
              (Control.rightShift true))))))

private def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | leftShift inner =>
        simp [elems]
        exact
          ProductCleanupGap.PrefixLeftShiftOne.machine.statesFinite.complete
            inner
    | scan => simp [elems]
    | choose => simp [elems]
    | delete kind inner =>
        cases kind <;> simp [elems] <;>
          exact
            SerializedFieldComposer.DeleteOneRestagedMachine.machine.statesFinite.complete
              inner
    | rightShift kind inner =>
        cases kind <;> simp [elems] <;>
          exact
            ProductCleanupGap.PrefixRightShiftOne.machine.statesFinite.complete
              inner
    | deleted => simp [elems]

end Control

private def mapTransition {inner : Type}
    (embed : inner -> Control) :
    Option (Option MachineCodeSymbol × Direction × inner) ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | none => none
  | some (write, direction, target) =>
      some (write, direction, embed target)

private def leftEmbed :
    ProductCleanupGap.PrefixLeftShiftOne.Control -> Control
  | .halt => .scan
  | inner => .leftShift inner

private def deleteEmbed (isDone : Bool) :
    SerializedFieldComposer.DeleteOneRestagedMachine.Control -> Control
  | .rewind .gate => .rightShift isDone .takeFirst
  | inner => .delete isDone inner

private def rightEmbed (isDone : Bool) :
    ProductCleanupGap.PrefixRightShiftOne.Control -> Control
  | .halt =>
      if isDone then .deleted else .scan
  | inner => .rightShift isDone inner

private def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .leftShift inner, read =>
      mapTransition leftEmbed
        (ProductCleanupGap.PrefixLeftShiftOne.machine.transition inner read)
  | .scan, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .scan)
  | .scan, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .choose)
  | .scan, _ => none
  | .choose, some MachineCodeSymbol.tick =>
      some (none, Direction.right,
        .delete false (.edit .pull))
  | .choose, some MachineCodeSymbol.done =>
      some (none, Direction.right,
        .delete true (.edit .pull))
  | .choose, _ => none
  | .delete kind inner, read =>
      mapTransition (deleteEmbed kind)
        (SerializedFieldComposer.DeleteOneRestagedMachine.machine.transition
          inner read)
  | .rightShift kind inner, read =>
      mapTransition (rightEmbed kind)
        (ProductCleanupGap.PrefixRightShiftOne.machine.transition inner read)
  | .deleted, _ => none

/-- The fixed machine that opens the protected boundary and deletes the
dynamically sized retained right-fuel field. -/
def machine : TuringMachine MachineCodeSymbol Control where
  start := .leftShift
    ProductCleanupGap.PrefixLeftShiftOne.machine.start
  halt := .deleted
  transition := transition
  statesFinite := Control.finite

private def leftConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      ProductCleanupGap.PrefixLeftShiftOne.Control) : Config Control :=
  TuringMachine.PhaseEmbedding.liftConfig leftEmbed c

private theorem stepConfig_some_of_transition_some
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : innerState -> outerState)
    (htransition : forall state read written direction target,
      inner.transition state read = some (written, direction, target) ->
        outer.transition (embed state) read =
          some (written, direction, embed target))
    {source target : TuringMachine.Configuration symbol innerState}
    (hstep : inner.stepConfig source = some target) :
    outer.stepConfig (TuringMachine.PhaseEmbedding.liftConfig embed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  cases source with
  | mk state tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      cases hinner : inner.transition state (Tape.read tape) with
      | none =>
          rw [hinner] at hstep
          contradiction
      | some action =>
          rcases action with ⟨written, direction, next⟩
          rw [hinner] at hstep
          simp only at hstep
          cases hstep
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          rw [htransition state (Tape.read tape)
            written direction next hinner]

private theorem left_step_active
    (c d : TuringMachine.Configuration MachineCodeSymbol
      ProductCleanupGap.PrefixLeftShiftOne.Control)
    (hstep :
      ProductCleanupGap.PrefixLeftShiftOne.machine.stepConfig c = some d) :
    machine.stepConfig (leftConfig c) = some (leftConfig d) := by
  apply stepConfig_some_of_transition_some leftEmbed ?_ hstep
  intro state read written direction target htransition
  cases state <;>
    simp [machine, transition, leftEmbed, mapTransition, htransition]
  case halt =>
    change (none : Option
      (Option MachineCodeSymbol × Direction ×
        ProductCleanupGap.PrefixLeftShiftOne.Control)) =
      some (written, direction, target) at htransition
    contradiction

private theorem left_run_exact (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    machine.runConfigExact?
        (ProductCleanupGap.PrefixLeftShiftOne.runSteps (first :: rest))
        (leftConfig
          (ProductCleanupGap.PrefixLeftShiftOne.sourceConfig
            (first :: rest) opaqueRight)) =
      some
        { state := .scan
          tape := ProductCleanupGap.PrefixLeftShiftOne.targetTape
            (first :: rest) opaqueRight } := by
  change machine.runConfigExact?
      (ProductCleanupGap.PrefixLeftShiftOne.runSteps (first :: rest))
      (TuringMachine.PhaseEmbedding.liftConfig leftEmbed
        (ProductCleanupGap.PrefixLeftShiftOne.sourceConfig
          (first :: rest) opaqueRight)) =
    some (TuringMachine.PhaseEmbedding.liftConfig leftEmbed
      (ProductCleanupGap.PrefixLeftShiftOne.targetConfig
        (first :: rest) opaqueRight))
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    leftEmbed left_step_active
  exact ProductCleanupGap.PrefixLeftShiftOne.run_exact
    first rest opaqueRight

private def scanEmbed : LeftFuelScanner.Control -> Control
  | .scan => .scan
  | .gate => .choose

private def scanConfig (c : Config LeftFuelScanner.Control) : Config Control :=
  TuringMachine.PhaseEmbedding.liftConfig scanEmbed c

private theorem scan_step_active
    (c d : Config LeftFuelScanner.Control)
    (hstep : LeftFuelScanner.machine.stepConfig c = some d) :
    machine.stepConfig (scanConfig c) = some (scanConfig d) := by
  apply stepConfig_some_of_transition_some scanEmbed ?_ hstep
  intro state read written direction target htransition
  cases state with
  | scan =>
      cases read with
      | none =>
          simp [LeftFuelScanner.machine, LeftFuelScanner.transition]
            at htransition
      | some symbol =>
          cases symbol <;>
            simp [LeftFuelScanner.machine, LeftFuelScanner.transition,
              scanEmbed, machine, transition] at htransition ⊢ <;>
            rcases htransition with ⟨rfl, rfl, rfl⟩ <;>
            simp
  | gate =>
      cases read <;>
        simp [LeftFuelScanner.machine, LeftFuelScanner.transition]
          at htransition

private theorem scan_run_exact (fuel : Nat)
    (suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (fuel + 1)
        (scanConfig (LeftFuelScanner.config .scan []
          (MachineDescription.encodeNatAppend fuel suffix) callerCells)) =
      some (scanConfig
        (LeftFuelScanner.config .gate
          (MachineDescription.encodeNat fuel).reverse suffix callerCells)) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    scanEmbed scan_step_active
  exact LeftFuelScanner.run_exact fuel suffix callerCells

private def RunsToEquiv (source target : Config Control) : Prop :=
  exists (steps : Nat) (endpoint : Config Control),
    machine.runConfigExact? steps source = some endpoint ∧
    endpoint.state = target.state ∧
    Tape.Equiv target.tape endpoint.tape

namespace RunsToEquiv

private theorem of_run {source target : Config Control} {steps : Nat}
    (hrun : machine.runConfigExact? steps source = some target) :
    RunsToEquiv source target :=
  ⟨steps, target, hrun, rfl, Tape.Equiv.refl _⟩

private theorem runConfigExact?_add (first second : Nat)
    (c : Config Control) :
    machine.runConfigExact? (first + second) c =
      match machine.runConfigExact? first c with
      | none => none
      | some middle => machine.runConfigExact? second middle := by
  induction first generalizing c with
  | zero =>
      simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add]
      rw [TuringMachine.runConfigExact?]
      rw [TuringMachine.runConfigExact?]
      cases hstep : machine.stepConfig c with
      | none => rfl
      | some next =>
          simp only
          exact ih next

private theorem trans {source middle target : Config Control}
    (first : RunsToEquiv source middle)
    (second : RunsToEquiv middle target) :
    RunsToEquiv source target := by
  rcases first with ⟨firstSteps, firstEndpoint,
    hfirst, hfirstState, hfirstTape⟩
  rcases second with ⟨secondSteps, secondEndpoint,
    hsecond, hsecondState, hsecondTape⟩
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hsecond hfirstTape with
    ⟨actualEndpoint, hsecondActual, hactualState, hactualTape⟩
  have hsourceEq :
      ({ state := middle.state, tape := firstEndpoint.tape } :
        Config Control) = firstEndpoint := by
    cases firstEndpoint with
    | mk endpointState endpointTape =>
        simp only at hfirstState ⊢
        rw [← hfirstState]
  have hsecondActual' :
      machine.runConfigExact? secondSteps firstEndpoint =
        some actualEndpoint := by
    rw [← hsourceEq]
    exact hsecondActual
  refine
    ⟨firstSteps + secondSteps, actualEndpoint, ?_,
      hactualState.trans hsecondState,
      Tape.Equiv.trans hsecondTape hactualTape⟩
  rw [runConfigExact?_add, hfirst]
  exact hsecondActual'

end RunsToEquiv

private def deleteConfig (kind : Bool)
    (c : Config
      SerializedFieldComposer.DeleteOneRestagedMachine.Control) :
    Config Control :=
  TuringMachine.PhaseEmbedding.liftConfig (deleteEmbed kind) c

private theorem delete_step_active (kind : Bool)
    (c d : Config
      SerializedFieldComposer.DeleteOneRestagedMachine.Control)
    (hstep :
      SerializedFieldComposer.DeleteOneRestagedMachine.machine.stepConfig c =
        some d) :
    machine.stepConfig (deleteConfig kind c) =
      some (deleteConfig kind d) := by
  apply stepConfig_some_of_transition_some (deleteEmbed kind) ?_ hstep
  intro state read written direction target htransition
  cases state with
  | edit inner =>
      simp [machine, transition, deleteEmbed, mapTransition, htransition]
  | rewind inner =>
      cases inner <;>
        simp [machine, transition, deleteEmbed, mapTransition,
          htransition]
      case gate =>
        change (none : Option
          (Option MachineCodeSymbol × Direction ×
            SerializedFieldComposer.DeleteOneRestagedMachine.Control)) =
          some (written, direction, target) at htransition
        contradiction

private def chooseConfig (kind : Bool)
    (leftRev suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Config Control :=
  scanConfig
    (LeftFuelScanner.config .gate leftRev
      (tokenSymbol kind :: suffix) callerCells)

private def chooseActualConfig (kind : Bool)
    (leftRev suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Config Control :=
  { state := .delete kind (.edit .pull)
    tape := Tape.move Direction.right
      (Tape.write none
        (LeftFuelScanner.config .gate leftRev
          (tokenSymbol kind :: suffix) callerCells).tape) }

private theorem choose_step_exact (kind : Bool)
    (leftRev suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? 1
        (chooseConfig kind leftRev suffix callerCells) =
      some (chooseActualConfig kind leftRev suffix callerCells) := by
  cases kind <;> rfl

private theorem chooseActual_tape_equiv_pull
    (kind : Bool)
    (leftRev suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    Tape.Equiv
      (deleteConfig kind
        (ProductCleanup.DeleteOne.pullConfig
          leftRev suffix callerCells)).tape
      (chooseActualConfig kind leftRev suffix callerCells).tape := by
  cases suffix <;>
    simp [deleteConfig, TuringMachine.PhaseEmbedding.liftConfig,
      ProductCleanup.DeleteOne.pullConfig,
      ProductCleanup.DeleteOne.pullTape,
      chooseActualConfig, LeftFuelScanner.config,
      LeftFuelScanner.tape, Tape.move, Tape.moveRight, Tape.write,
      Tape.Equiv] <;>
    exact Tape.dropTrailingNone_cons_eq rfl
      (FoC.Computability.dropTrailingNone_append_none _).symm

private theorem choose_runs_to_pull (kind : Bool)
    (leftRev suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    RunsToEquiv
      (chooseConfig kind leftRev suffix callerCells)
      (deleteConfig kind
        (ProductCleanup.DeleteOne.pullConfig
          leftRev suffix callerCells)) := by
  refine
    ⟨1, chooseActualConfig kind leftRev suffix callerCells,
      choose_step_exact kind leftRev suffix callerCells, rfl, ?_⟩
  exact chooseActual_tape_equiv_pull kind leftRev suffix callerCells

private theorem delete_pull_run_exact (kind : Bool)
    (leftRev suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (3 * suffix.length + 1)
        (deleteConfig kind
          (ProductCleanup.DeleteOne.pullConfig
            leftRev suffix callerCells)) =
      some
        (deleteConfig kind
          (ProductCleanup.DeleteOne.exitConfig
            (List.append suffix.reverse leftRev) callerCells)) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (deleteEmbed kind) (delete_step_active kind)
  exact ProductCleanup.DeleteOne.pull_run_exact
    leftRev suffix callerCells

private theorem delete_rewind_run_exact (kind : Bool)
    (wordRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (wordRev.length + 2)
        (deleteConfig kind
          (ProductCleanup.DeleteOne.exitConfig wordRev callerCells)) =
      some
        (deleteConfig kind
          (ProductCleanup.DeleteOne.gateConfig
            wordRev.reverse callerCells)) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (deleteEmbed kind) (delete_step_active kind)
  exact ProductCleanup.DeleteOne.rewind_run_exact wordRev callerCells

private theorem delete_tail_runs_to_gate (kind : Bool)
    (leftRev suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    RunsToEquiv
      (deleteConfig kind
        (ProductCleanup.DeleteOne.pullConfig
          leftRev suffix callerCells))
      (deleteConfig kind
        (ProductCleanup.DeleteOne.gateConfig
          (ProductCleanup.DeleteOne.output leftRev suffix)
          callerCells)) := by
  apply RunsToEquiv.trans
    (RunsToEquiv.of_run
      (delete_pull_run_exact kind leftRev suffix callerCells))
  simpa [ProductCleanup.DeleteOne.output, List.reverse_append] using
    (RunsToEquiv.of_run
      (delete_rewind_run_exact kind
        (List.append suffix.reverse leftRev) callerCells))

private def rightConfig (kind : Bool)
    (c : Config ProductCleanupGap.PrefixRightShiftOne.Control) :
    Config Control :=
  TuringMachine.PhaseEmbedding.liftConfig (rightEmbed kind) c

private theorem right_step_active (kind : Bool)
    (c d : Config ProductCleanupGap.PrefixRightShiftOne.Control)
    (hstep :
      ProductCleanupGap.PrefixRightShiftOne.machine.stepConfig c = some d) :
    machine.stepConfig (rightConfig kind c) = some (rightConfig kind d) := by
  apply stepConfig_some_of_transition_some (rightEmbed kind) ?_ hstep
  intro state read written direction target htransition
  cases state <;>
    simp [machine, transition, rightEmbed, mapTransition, htransition]
  case halt =>
    change (none : Option
      (Option MachineCodeSymbol × Direction ×
        ProductCleanupGap.PrefixRightShiftOne.Control)) =
      some (written, direction, target) at htransition
    contradiction

private def resumedConfig (kind : Bool)
    (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Config Control :=
  { state := rightEmbed kind .halt
    tape := oneGapTape word callerCells }

private theorem deleteGateConfig_eq_rightPaddedSource
    (kind : Bool)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    deleteConfig kind
        (ProductCleanup.DeleteOne.gateConfig
          (first :: rest) callerCells) =
      rightConfig kind
        (ProductCleanupGap.PrefixRightShiftOne.paddedSourceConfig
          (first :: rest) callerCells) := by
  cases kind <;> rfl

private theorem right_shift_runs_from_gate (kind : Bool)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    RunsToEquiv
      (deleteConfig kind
        (ProductCleanup.DeleteOne.gateConfig
          (first :: rest) callerCells))
      (resumedConfig kind (first :: rest) callerCells) := by
  rcases
      ProductCleanupGap.PrefixRightShiftOne.run_from_padded_source
        first rest callerCells with
    ⟨endpoint, hrun, hstate, htape⟩
  have hlift :
      machine.runConfigExact?
          (ProductCleanupGap.PrefixRightShiftOne.runSteps (first :: rest))
          (rightConfig kind
            (ProductCleanupGap.PrefixRightShiftOne.paddedSourceConfig
              (first :: rest) callerCells)) =
        some (rightConfig kind endpoint) := by
    apply
      TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
        (rightEmbed kind) (right_step_active kind)
    exact hrun
  refine
    ⟨ProductCleanupGap.PrefixRightShiftOne.runSteps (first :: rest),
      rightConfig kind endpoint, ?_, ?_, ?_⟩
  · rw [deleteGateConfig_eq_rightPaddedSource]
    exact hlift
  · simp [rightConfig, resumedConfig,
      TuringMachine.PhaseEmbedding.liftConfig, hstate]
  · simpa [rightConfig, resumedConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      prefixRightTarget_eq_oneGapTape] using htape

private theorem resumedTick_eq_scanSource
    (fuel : Nat) (suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    resumedConfig false
        (MachineDescription.encodeNatAppend fuel suffix) callerCells =
      scanConfig
        (LeftFuelScanner.config .scan []
          (MachineDescription.encodeNatAppend fuel suffix) callerCells) := by
  cases fuel <;> rfl

private theorem scan_runs_to_choose (fuel : Nat)
    (kind : Bool) (suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    RunsToEquiv
      (resumedConfig false
        (MachineDescription.encodeNatAppend fuel
          (tokenSymbol kind :: suffix)) callerCells)
      (chooseConfig kind (MachineDescription.encodeNat fuel).reverse
        suffix callerCells) := by
  apply RunsToEquiv.of_run
  rw [resumedTick_eq_scanSource]
  exact scan_run_exact fuel (tokenSymbol kind :: suffix) callerCells

private theorem right_shift_after_delete (kind : Bool)
    (fuel : Nat) (suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    RunsToEquiv
      (deleteConfig kind
        (ProductCleanup.DeleteOne.gateConfig
          (MachineDescription.encodeNatAppend fuel suffix) callerCells))
      (resumedConfig kind
        (MachineDescription.encodeNatAppend fuel suffix) callerCells) := by
  have hne := encodeNatAppend_ne_nil fuel suffix
  cases hword : MachineDescription.encodeNatAppend fuel suffix with
  | nil => exact False.elim (hne hword)
  | cons first rest =>
      simpa [hword] using
        (right_shift_runs_from_gate kind first rest callerCells)

private theorem delete_token_cycle (fuel : Nat)
    (kind : Bool) (suffix : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    RunsToEquiv
      (resumedConfig false
        (MachineDescription.encodeNatAppend fuel
          (tokenSymbol kind :: suffix)) callerCells)
      (resumedConfig kind
        (MachineDescription.encodeNatAppend fuel suffix) callerCells) := by
  apply RunsToEquiv.trans
    (scan_runs_to_choose fuel kind suffix callerCells)
  apply RunsToEquiv.trans
    (choose_runs_to_pull kind
      (MachineDescription.encodeNat fuel).reverse suffix callerCells)
  apply RunsToEquiv.trans
    (delete_tail_runs_to_gate kind
      (MachineDescription.encodeNat fuel).reverse suffix callerCells)
  simpa [deleteOne_output_eq_encodeNatAppend] using
    (right_shift_after_delete kind fuel suffix callerCells)

private theorem delete_right_fuel (leftFuel rightFuel : Nat)
    (input : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    RunsToEquiv
      (resumedConfig false
        (MachineDescription.encodeNatAppend leftFuel
          (MachineDescription.encodeNatAppend rightFuel input))
        callerCells)
      (resumedConfig true
        (MachineDescription.encodeNatAppend leftFuel input)
        callerCells) := by
  induction rightFuel with
  | zero =>
      simpa [MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, tokenSymbol] using
        (delete_token_cycle leftFuel true input callerCells)
  | succ rightFuel ih =>
      have hfirst :=
        delete_token_cycle leftFuel false
          (MachineDescription.encodeNatAppend rightFuel input)
          callerCells
      apply RunsToEquiv.trans
        (by
          simpa [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat,
            tokenSymbol] using hfirst)
      exact ih

private theorem left_runs_to_scan (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    RunsToEquiv
      (leftConfig
        (ProductCleanupGap.PrefixLeftShiftOne.sourceConfig
          (first :: rest) opaqueRight))
      (resumedConfig false (first :: rest)
        (protectedOpaque opaqueRight)) := by
  apply RunsToEquiv.of_run
  simpa [resumedConfig, rightEmbed, protectedOpaque, oneGapTape,
    ProductCleanupGap.PrefixLeftShiftOne.targetTape] using
    left_run_exact first rest opaqueRight

/-- Canonical cleanup source with the retained raw prefix immediately left of
the protected caller boundary. -/
def sourceConfig (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  leftConfig
    (ProductCleanupGap.PrefixLeftShiftOne.sourceConfig
      (ProductCleanupShapes.retainedRawPrefix input leftFuel rightFuel)
      opaqueRight)

/-- Branch-neutral endpoint after right-fuel deletion, retaining the left-fuel
encoding and input in a one-gap protected frame. -/
def deletedConfig (input : Word MachineCodeSymbol)
    (leftFuel : Nat)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .deleted
    tape := oneGapTape
      (MachineDescription.encodeNatAppend leftFuel input)
      (protectedOpaque opaqueRight) }

/-- The fixed machine reaches its deleted state at a physical tape equivalent
to the canonical branch-neutral endpoint. -/
theorem run_to_deleted (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (opaqueRight : List (Option MachineCodeSymbol)) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol Control),
      machine.runConfigExact? steps
          (sourceConfig input leftFuel rightFuel opaqueRight) =
        some endpoint ∧
      endpoint.state = .deleted ∧
      Tape.Equiv (deletedConfig input leftFuel opaqueRight).tape
        endpoint.tape := by
  change RunsToEquiv
    (sourceConfig input leftFuel rightFuel opaqueRight)
    (deletedConfig input leftFuel opaqueRight)
  have hne := retainedRawPrefix_ne_nil input leftFuel rightFuel
  cases hword :
      ProductCleanupShapes.retainedRawPrefix input leftFuel rightFuel with
  | nil => exact False.elim (hne hword)
  | cons first rest =>
      have hnested :
          MachineDescription.encodeNatAppend leftFuel
              (MachineDescription.encodeNatAppend rightFuel input) =
            first :: rest := by
        rw [← retainedRawPrefix_eq_nestedEncodeNatAppend]
        exact hword
      apply RunsToEquiv.trans
        (by
          simpa [sourceConfig, hword] using
            (left_runs_to_scan first rest opaqueRight))
      simpa [deletedConfig, resumedConfig, rightEmbed, hnested] using
        (delete_right_fuel leftFuel rightFuel input
          (protectedOpaque opaqueRight))

end DynamicRightFuel
end ProductCleanup
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
