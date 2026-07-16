import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.FinishMachine
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.DynamicRightFuel
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.FixedGapExpander

/-!
# Product pair-prefix materializer machine

Fixed finite phase graph and active phase embeddings for the pair-prefix
materializer. Input-indexed executions are proved in the companion runs module.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductPairMaterializer

open InitialMaterializer

abbrev Config (state : Type) :=
  TuringMachine.Configuration MachineCodeSymbol state

/-! ## Fixed branch positioners -/

namespace EmptyHeaderPositioner

inductive Control where
  | fuel
  | gap
  | halt
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems := [.fuel, .gap, .halt]
  complete := by intro control; cases control <;> simp

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .fuel, some .tick =>
      some (some .tick, Direction.right, .fuel)
  | .fuel, some .done =>
      some (some .done, Direction.right, .gap)
  | .gap, none =>
      some (none, Direction.right, .halt)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .fuel
  halt := .halt
  transition := transition
  statesFinite := Control.finite

end EmptyHeaderPositioner

namespace NonemptyPackPositioner

inductive Control where
  | scan
  | header
  | halt
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems := [.scan, .header, .halt]
  complete := by intro control; cases control <;> simp

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .scan, some symbol =>
      some (some symbol, Direction.right, .scan)
  | .scan, none =>
      some (none, Direction.right, .header)
  | .header, some .header =>
      some (some .header, Direction.right, .halt)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .scan
  halt := .halt
  transition := transition
  statesFinite := Control.finite

end NonemptyPackPositioner

namespace EmptyHeaderPositioner

def scanTape (leftRev remaining : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match remaining with
  | [] =>
      { left := List.append (leftRev.map some) [none]
        head := none
        right := callerCells }
  | current :: rest =>
      { left := List.append (leftRev.map some) [none]
        head := some current
        right := List.append (rest.map some) (none :: callerCells) }

def scanConfig (control : Control)
    (leftRev remaining : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Config Control :=
  { state := control
    tape := scanTape leftRev remaining callerCells }

def sourceConfig (fuel : Nat)
    (callerCells : List (Option MachineCodeSymbol)) : Config Control :=
  scanConfig .fuel [] (MachineDescription.encodeNat fuel) callerCells

def gapConfig (fuel : Nat)
    (callerCells : List (Option MachineCodeSymbol)) : Config Control :=
  scanConfig .gap (MachineDescription.encodeNat fuel).reverse [] callerCells

def paddedTargetConfig (fuel : Nat)
    (callerCells : List (Option MachineCodeSymbol)) : Config Control :=
  { state := .halt
    tape := Tape.move Direction.right (gapConfig fuel callerCells).tape }

theorem tick_step (leftRev rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (scanConfig .fuel leftRev
          (MachineCodeSymbol.tick :: rest) callerCells) =
      some (scanConfig .fuel (MachineCodeSymbol.tick :: leftRev)
        rest callerCells) := by
  cases rest <;> cases callerCells <;> rfl

theorem done_step (leftRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (scanConfig .fuel leftRev [MachineCodeSymbol.done] callerCells) =
      some (scanConfig .gap (MachineCodeSymbol.done :: leftRev)
        [] callerCells) := by
  cases callerCells <;> rfl

theorem fuel_run_exact (fuel : Nat)
    (leftRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (MachineDescription.encodeNat fuel).length
        (scanConfig .fuel leftRev
          (MachineDescription.encodeNat fuel) callerCells) =
      some (scanConfig .gap
        (List.append (MachineDescription.encodeNat fuel).reverse leftRev)
        [] callerCells) := by
  induction fuel generalizing leftRev with
  | zero =>
      change machine.runConfigExact? 1
          (scanConfig .fuel leftRev [MachineCodeSymbol.done]
            callerCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [done_step]
      simp [TuringMachine.runConfigExact?, MachineDescription.encodeNat]
  | succ fuel ih =>
      change machine.runConfigExact?
          ((MachineDescription.encodeNat fuel).length + 1)
          (scanConfig .fuel leftRev
            (MachineCodeSymbol.tick :: MachineDescription.encodeNat fuel)
            callerCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [tick_step]
      simp only
      rw [ih (MachineCodeSymbol.tick :: leftRev)]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

theorem gap_step (fuel : Nat)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (gapConfig fuel callerCells) =
      some (paddedTargetConfig fuel callerCells) := by
  rfl

def runSteps (fuel : Nat) : Nat :=
  (MachineDescription.encodeNat fuel).length + 1

theorem run_exact (fuel : Nat)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (runSteps fuel)
        (sourceConfig fuel callerCells) =
      some (paddedTargetConfig fuel callerCells) := by
  unfold runSteps sourceConfig
  rw [InitialMaterializer.ExactRun.append]
  rw [fuel_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?]
  have hgap : machine.stepConfig
      (scanConfig .gap
        (List.append (MachineDescription.encodeNat fuel).reverse [])
        [] callerCells) =
      some (paddedTargetConfig fuel callerCells) := by
    simpa [gapConfig, Word] using gap_step fuel callerCells
  rw [hgap]
  rfl

end EmptyHeaderPositioner

/-! ## Master control graph -/

abbrev emptyExtra {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount)) : Nat :=
  ProductGapExpander.emptyExtra left

theorem emptyExtra_positive {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount)) :
    0 < emptyExtra left := by
  exact ProductGapExpander.emptyExtra_positive left

inductive Control {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) where
  | finish (inner : ProductFinish.Control
      left right)
  | cleanupEmpty (inner : ProductCleanup.DynamicRightFuel.Control)
  | cleanupNonempty (inner : ProductCleanup.DynamicRightFuel.Control)
  | positionEmpty (inner : EmptyHeaderPositioner.Control)
  | positionNonempty (inner : NonemptyPackPositioner.Control)
  | compactor (inner : StageInput.TwoBlankCompactor.Control)
  | gapEmpty
      (inner : ProductGapExpander.Control (emptyExtra left))
  | gapNonempty
      (inner : ProductGapExpander.Control 2)
deriving DecidableEq

namespace Control

def elems {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    List (Control left right) :=
  List.append
    ((ProductFinish.machine left right
      ).statesFinite.elems.map Control.finish)
    (List.append
      (ProductCleanup.DynamicRightFuel.machine.statesFinite.elems.map
        Control.cleanupEmpty)
      (List.append
        (ProductCleanup.DynamicRightFuel.machine.statesFinite.elems.map
          Control.cleanupNonempty)
        (List.append
          (EmptyHeaderPositioner.machine.statesFinite.elems.map
            Control.positionEmpty)
          (List.append
            (NonemptyPackPositioner.machine.statesFinite.elems.map
              Control.positionNonempty)
            (List.append
              (StageInput.TwoBlankCompactor.machine.statesFinite.elems.map
                Control.compactor)
              (List.append
                ((ProductGapExpander.machine
                  (emptyExtra_positive left)).statesFinite.elems.map
                    Control.gapEmpty)
                ((ProductGapExpander.machine
                  (show 0 < 2 by decide)).statesFinite.elems.map
                    Control.gapNonempty)))))))

def finite {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    Foundation.FiniteType (Control left right) where
  elems := elems left right
  complete := by
    intro control
    cases control with
    | finish inner =>
        have h :=
          (ProductFinish.machine
            left right).statesFinite.complete inner
        simp [elems, h]
    | cleanupEmpty inner =>
        have h :=
          ProductCleanup.DynamicRightFuel.machine.statesFinite.complete inner
        simp [elems, h]
    | cleanupNonempty inner =>
        have h :=
          ProductCleanup.DynamicRightFuel.machine.statesFinite.complete inner
        simp [elems, h]
    | positionEmpty inner =>
        have h := EmptyHeaderPositioner.machine.statesFinite.complete inner
        simp [elems, h]
    | positionNonempty inner =>
        have h := NonemptyPackPositioner.machine.statesFinite.complete inner
        simp [elems, h]
    | compactor inner =>
        have h :=
          StageInput.TwoBlankCompactor.machine.statesFinite.complete inner
        simp [elems, h]
    | gapEmpty inner =>
        have h := (ProductGapExpander.machine
          (emptyExtra_positive left)).statesFinite.complete inner
        simp [elems, h]
    | gapNonempty inner =>
        have h := (ProductGapExpander.machine
          (show 0 < 2 by decide)).statesFinite.complete inner
        simp [elems, h]

end Control

def emptyPrefixEndpoint {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)} :
    ProductFinish.Control left right :=
  .prefixPhase (.materializer (.emptyPrepend .gate))

def nonemptyPrefixEndpoint {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)} :
    ProductFinish.Control left right :=
  .prefixPhase (.materializer (.header .halt))

def cleanupEmptyEmbed {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)} :
    ProductCleanup.DynamicRightFuel.Control -> Control left right :=
  fun inner =>
    if inner = ProductCleanup.DynamicRightFuel.machine.halt then
      .positionEmpty EmptyHeaderPositioner.machine.start
    else
      .cleanupEmpty inner

def cleanupNonemptyEmbed {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)} :
    ProductCleanup.DynamicRightFuel.Control -> Control left right :=
  fun inner =>
    if inner = ProductCleanup.DynamicRightFuel.machine.halt then
      .positionNonempty NonemptyPackPositioner.machine.start
    else
      .cleanupNonempty inner

def positionEmptyEmbed {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)} :
    EmptyHeaderPositioner.Control -> Control left right :=
  fun inner =>
    if inner = EmptyHeaderPositioner.machine.halt then
      .gapEmpty
        (ProductGapExpander.machine
          (emptyExtra_positive left)).start
    else
      .positionEmpty inner

def positionNonemptyEmbed {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)} :
    NonemptyPackPositioner.Control -> Control left right :=
  fun inner =>
    if inner = NonemptyPackPositioner.machine.halt then
      .compactor StageInput.TwoBlankCompactor.machine.start
    else
      .positionNonempty inner

def compactorEmbed {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (inner : StageInput.TwoBlankCompactor.Control) : Control left right :=
  if inner = StageInput.TwoBlankCompactor.machine.halt then
    .gapNonempty
      (ProductGapExpander.machine
        (show 0 < 2 by decide)).start
  else
    .compactor inner

def emptyWriterStart {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount)) :
    FullMaterializerMachine.Control left :=
  .emptyWrite
    (FixedWordWriter.stateAt (EmptyInputSuffix.suffix left) 0 (by simp))

def gapEmptyEmbed {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)} :
    ProductGapExpander.Control (emptyExtra left) ->
      Control left right :=
  fun inner =>
    if inner = (ProductGapExpander.machine
        (emptyExtra_positive left)).halt then
      .finish (.materializer (emptyWriterStart left))
    else
      .gapEmpty inner

def gapNonemptyEmbed {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)} :
    ProductGapExpander.Control 2 -> Control left right :=
  fun inner =>
    if inner = (ProductGapExpander.machine
        (show 0 < 2 by decide)).halt then
      .finish (.materializer (.tail .capture))
    else
      .gapNonempty inner

private def mapTransition {inner outer : Type}
    (embed : inner -> outer) :
    Option (Option MachineCodeSymbol × Direction × inner) ->
      Option (Option MachineCodeSymbol × Direction × outer)
  | none => none
  | some (write, direction, target) =>
      some (write, direction, embed target)

def transition {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    Control left right -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control left right)
  | .finish inner, read =>
      if inner = emptyPrefixEndpoint then
        some (read, Direction.left,
          cleanupEmptyEmbed ProductCleanup.DynamicRightFuel.machine.start)
      else if inner = nonemptyPrefixEndpoint then
        some (read, Direction.left,
          cleanupNonemptyEmbed
            ProductCleanup.DynamicRightFuel.machine.start)
      else
        mapTransition Control.finish
          ((ProductFinish.machine
            left right).transition inner read)
  | .cleanupEmpty inner, read =>
      mapTransition cleanupEmptyEmbed
        (ProductCleanup.DynamicRightFuel.machine.transition inner read)
  | .cleanupNonempty inner, read =>
      mapTransition cleanupNonemptyEmbed
        (ProductCleanup.DynamicRightFuel.machine.transition inner read)
  | .positionEmpty inner, read =>
      mapTransition positionEmptyEmbed
        (EmptyHeaderPositioner.machine.transition inner read)
  | .positionNonempty inner, read =>
      mapTransition positionNonemptyEmbed
        (NonemptyPackPositioner.machine.transition inner read)
  | .compactor inner, read =>
      mapTransition compactorEmbed
        (StageInput.TwoBlankCompactor.machine.transition inner read)
  | .gapEmpty inner, read =>
      mapTransition gapEmptyEmbed
        ((ProductGapExpander.machine
          (emptyExtra_positive left)).transition inner read)
  | .gapNonempty inner, read =>
      mapTransition gapNonemptyEmbed
        ((ProductGapExpander.machine
          (show 0 < 2 by decide)).transition inner read)

def machine {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    TuringMachine MachineCodeSymbol (Control left right) where
  start := .finish
    (ProductFinish.machine
      left right).start
  halt := .finish
    (ProductFinish.machine
      left right).halt
  transition := transition left right
  statesFinite := Control.finite left right

/-! ## Phase configuration embeddings -/

def finishConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : Config
      (ProductFinish.Control
        left right)) : Config (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.finish c

def cleanupEmptyConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : Config ProductCleanup.DynamicRightFuel.Control) :
    Config (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig cleanupEmptyEmbed c

def cleanupNonemptyConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : Config ProductCleanup.DynamicRightFuel.Control) :
    Config (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig cleanupNonemptyEmbed c

def positionEmptyConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : Config EmptyHeaderPositioner.Control) :
    Config (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig positionEmptyEmbed c

def positionNonemptyConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : Config NonemptyPackPositioner.Control) :
    Config (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig positionNonemptyEmbed c

def compactorConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : Config StageInput.TwoBlankCompactor.Control) :
    Config (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig compactorEmbed c

def gapEmptyConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : Config
      (ProductGapExpander.Control (emptyExtra left))) :
    Config (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig gapEmptyEmbed c

def gapNonemptyConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : Config (ProductGapExpander.Control 2)) :
    Config (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig gapNonemptyEmbed c

/-! ## Stable active phase lifts -/

private theorem stepConfig_some_of_transition_some
    {innerState outerState : Type}
    {inner : TuringMachine MachineCodeSymbol innerState}
    {outer : TuringMachine MachineCodeSymbol outerState}
    (embed : innerState -> outerState)
    (htransition : forall state read write direction target,
      inner.transition state read = some (write, direction, target) ->
        outer.transition (embed state) read =
          some (write, direction, embed target))
    {source target : Config innerState}
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
          rcases action with ⟨write, direction, next⟩
          rw [hinner] at hstep
          simp only at hstep
          cases hstep
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          rw [htransition state (Tape.read tape)
            write direction next hinner]

theorem finish_empty_endpoint_transition_none
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (read : Option MachineCodeSymbol) :
    (ProductFinish.machine
      left right).transition emptyPrefixEndpoint read = none := by
  rfl

theorem finish_nonempty_endpoint_transition_none
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (read : Option MachineCodeSymbol) :
    (ProductFinish.machine
      left right).transition nonemptyPrefixEndpoint read = none := by
  rfl

private theorem finish_transition_some
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (state : ProductFinish.Control
      left right)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : ProductFinish.Control
      left right)
    (htransition :
      (ProductFinish.machine
        left right).transition state read =
          some (write, direction, target)) :
    (machine left right).transition (.finish state) read =
      some (write, direction, .finish target) := by
  have hempty : state ≠ emptyPrefixEndpoint := by
    intro hstate
    subst state
    rw [finish_empty_endpoint_transition_none] at htransition
    contradiction
  have hnonempty : state ≠ nonemptyPrefixEndpoint := by
    intro hstate
    subst state
    rw [finish_nonempty_endpoint_transition_none] at htransition
    contradiction
  simp [machine, transition, hempty, hnonempty, mapTransition,
    htransition]

theorem finish_step_active
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {source target : Config
      (ProductFinish.Control
        left right)}
    (hstep :
      (ProductFinish.machine
        left right).stepConfig source = some target) :
    (machine left right).stepConfig (finishConfig source) =
      some (finishConfig target) := by
  exact stepConfig_some_of_transition_some Control.finish
    (finish_transition_some left right) hstep

theorem finish_run_lift
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : Config
      (ProductFinish.Control
        left right)}
    (hrun :
      (ProductFinish.machine
        left right).runConfigExact? steps source = some target) :
    (machine left right).runConfigExact? steps (finishConfig source) =
      some (finishConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    Control.finish
  · intro c d hstep
    exact finish_step_active left right hstep
  · exact hrun

theorem cleanup_halt_transition_none
    (read : Option MachineCodeSymbol) :
    ProductCleanup.DynamicRightFuel.machine.transition
      ProductCleanup.DynamicRightFuel.machine.halt read = none := by
  rfl

private theorem cleanupEmpty_transition_some
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (state : ProductCleanup.DynamicRightFuel.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : ProductCleanup.DynamicRightFuel.Control)
    (htransition :
      ProductCleanup.DynamicRightFuel.machine.transition state read =
        some (write, direction, target)) :
    (machine left right).transition (cleanupEmptyEmbed state) read =
      some (write, direction, cleanupEmptyEmbed target) := by
  have hactive : state ≠ ProductCleanup.DynamicRightFuel.machine.halt := by
    intro hstate
    subst state
    rw [cleanup_halt_transition_none] at htransition
    contradiction
  simp [machine, transition, cleanupEmptyEmbed, hactive,
    mapTransition, htransition]

theorem cleanupEmpty_step_active
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {source target : Config ProductCleanup.DynamicRightFuel.Control}
    (hstep : ProductCleanup.DynamicRightFuel.machine.stepConfig source =
      some target) :
    (machine left right).stepConfig (cleanupEmptyConfig source) =
      some (cleanupEmptyConfig target) := by
  exact stepConfig_some_of_transition_some cleanupEmptyEmbed
    (cleanupEmpty_transition_some left right) hstep

theorem cleanupEmpty_run_lift
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : Config ProductCleanup.DynamicRightFuel.Control}
    (hrun : ProductCleanup.DynamicRightFuel.machine.runConfigExact?
      steps source = some target) :
    (machine left right).runConfigExact? steps (cleanupEmptyConfig source) =
      some (cleanupEmptyConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    cleanupEmptyEmbed
  · intro c d hstep
    exact cleanupEmpty_step_active left right hstep
  · exact hrun

private theorem cleanupNonempty_transition_some
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (state : ProductCleanup.DynamicRightFuel.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : ProductCleanup.DynamicRightFuel.Control)
    (htransition :
      ProductCleanup.DynamicRightFuel.machine.transition state read =
        some (write, direction, target)) :
    (machine left right).transition (cleanupNonemptyEmbed state) read =
      some (write, direction, cleanupNonemptyEmbed target) := by
  have hactive : state ≠ ProductCleanup.DynamicRightFuel.machine.halt := by
    intro hstate
    subst state
    rw [cleanup_halt_transition_none] at htransition
    contradiction
  simp [machine, transition, cleanupNonemptyEmbed, hactive,
    mapTransition, htransition]

theorem cleanupNonempty_step_active
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {source target : Config ProductCleanup.DynamicRightFuel.Control}
    (hstep : ProductCleanup.DynamicRightFuel.machine.stepConfig source =
      some target) :
    (machine left right).stepConfig (cleanupNonemptyConfig source) =
      some (cleanupNonemptyConfig target) := by
  exact stepConfig_some_of_transition_some cleanupNonemptyEmbed
    (cleanupNonempty_transition_some left right) hstep

theorem cleanupNonempty_run_lift
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : Config ProductCleanup.DynamicRightFuel.Control}
    (hrun : ProductCleanup.DynamicRightFuel.machine.runConfigExact?
      steps source = some target) :
    (machine left right).runConfigExact? steps
        (cleanupNonemptyConfig source) =
      some (cleanupNonemptyConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    cleanupNonemptyEmbed
  · intro c d hstep
    exact cleanupNonempty_step_active left right hstep
  · exact hrun

theorem emptyPosition_halt_transition_none
    (read : Option MachineCodeSymbol) :
    EmptyHeaderPositioner.machine.transition
      EmptyHeaderPositioner.machine.halt read = none := by
  rfl

private theorem positionEmpty_transition_some
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (state : EmptyHeaderPositioner.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : EmptyHeaderPositioner.Control)
    (htransition : EmptyHeaderPositioner.machine.transition state read =
      some (write, direction, target)) :
    (machine left right).transition (positionEmptyEmbed state) read =
      some (write, direction, positionEmptyEmbed target) := by
  have hactive : state ≠ EmptyHeaderPositioner.machine.halt := by
    intro hstate
    subst state
    rw [emptyPosition_halt_transition_none] at htransition
    contradiction
  simp [machine, transition, positionEmptyEmbed, hactive,
    mapTransition, htransition]

theorem positionEmpty_step_active
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {source target : Config EmptyHeaderPositioner.Control}
    (hstep : EmptyHeaderPositioner.machine.stepConfig source = some target) :
    (machine left right).stepConfig (positionEmptyConfig source) =
      some (positionEmptyConfig target) := by
  exact stepConfig_some_of_transition_some positionEmptyEmbed
    (positionEmpty_transition_some left right) hstep

theorem positionEmpty_run_lift
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : Config EmptyHeaderPositioner.Control}
    (hrun : EmptyHeaderPositioner.machine.runConfigExact? steps source =
      some target) :
    (machine left right).runConfigExact? steps
        (positionEmptyConfig source) =
      some (positionEmptyConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    positionEmptyEmbed
  · intro c d hstep
    exact positionEmpty_step_active left right hstep
  · exact hrun

theorem nonemptyPosition_halt_transition_none
    (read : Option MachineCodeSymbol) :
    NonemptyPackPositioner.machine.transition
      NonemptyPackPositioner.machine.halt read = none := by
  rfl

private theorem positionNonempty_transition_some
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (state : NonemptyPackPositioner.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : NonemptyPackPositioner.Control)
    (htransition : NonemptyPackPositioner.machine.transition state read =
      some (write, direction, target)) :
    (machine left right).transition (positionNonemptyEmbed state) read =
      some (write, direction, positionNonemptyEmbed target) := by
  have hactive : state ≠ NonemptyPackPositioner.machine.halt := by
    intro hstate
    subst state
    rw [nonemptyPosition_halt_transition_none] at htransition
    contradiction
  simp [machine, transition, positionNonemptyEmbed, hactive,
    mapTransition, htransition]

theorem positionNonempty_step_active
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {source target : Config NonemptyPackPositioner.Control}
    (hstep : NonemptyPackPositioner.machine.stepConfig source =
      some target) :
    (machine left right).stepConfig (positionNonemptyConfig source) =
      some (positionNonemptyConfig target) := by
  exact stepConfig_some_of_transition_some positionNonemptyEmbed
    (positionNonempty_transition_some left right) hstep

theorem positionNonempty_run_lift
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : Config NonemptyPackPositioner.Control}
    (hrun : NonemptyPackPositioner.machine.runConfigExact? steps source =
      some target) :
    (machine left right).runConfigExact? steps
        (positionNonemptyConfig source) =
      some (positionNonemptyConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    positionNonemptyEmbed
  · intro c d hstep
    exact positionNonempty_step_active left right hstep
  · exact hrun

private theorem compactor_transition_some
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (state : StageInput.TwoBlankCompactor.Control)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : StageInput.TwoBlankCompactor.Control)
    (htransition :
      StageInput.TwoBlankCompactor.machine.transition state read =
        some (write, direction, target)) :
    (machine left right).transition (compactorEmbed state) read =
      some (write, direction, compactorEmbed target) := by
  have hactive : state ≠ StageInput.TwoBlankCompactor.machine.halt := by
    intro hstate
    subst state
    rw [StageRunner.compactor_halt_transition_none] at htransition
    contradiction
  simp [machine, transition, compactorEmbed, hactive,
    mapTransition, htransition]

theorem compactor_step_active
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {source target : Config StageInput.TwoBlankCompactor.Control}
    (hstep : StageInput.TwoBlankCompactor.machine.stepConfig source =
      some target) :
    (machine left right).stepConfig (compactorConfig source) =
      some (compactorConfig target) := by
  exact stepConfig_some_of_transition_some compactorEmbed
    (compactor_transition_some left right) hstep

theorem compactor_run_lift
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : Config StageInput.TwoBlankCompactor.Control}
    (hrun : StageInput.TwoBlankCompactor.machine.runConfigExact?
      steps source = some target) :
    (machine left right).runConfigExact? steps (compactorConfig source) =
      some (compactorConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    compactorEmbed
  · intro c d hstep
    exact compactor_step_active left right hstep
  · exact hrun

theorem gapEmpty_halt_transition_none
    {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (read : Option MachineCodeSymbol) :
    (ProductGapExpander.machine
      (emptyExtra_positive left)).transition
        (ProductGapExpander.machine
          (emptyExtra_positive left)).halt read = none := by
  rfl

private theorem gapEmpty_transition_some
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (state : ProductGapExpander.Control (emptyExtra left))
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : ProductGapExpander.Control (emptyExtra left))
    (htransition :
      (ProductGapExpander.machine
        (emptyExtra_positive left)).transition state read =
          some (write, direction, target)) :
    (machine left right).transition (gapEmptyEmbed state) read =
      some (write, direction, gapEmptyEmbed target) := by
  have hactive : state ≠
      (ProductGapExpander.machine
        (emptyExtra_positive left)).halt := by
    intro hstate
    subst state
    rw [gapEmpty_halt_transition_none] at htransition
    contradiction
  simp [machine, transition, gapEmptyEmbed, hactive,
    mapTransition, htransition]

theorem gapEmpty_step_active
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {source target : Config
      (ProductGapExpander.Control (emptyExtra left))}
    (hstep :
      (ProductGapExpander.machine
        (emptyExtra_positive left)).stepConfig source = some target) :
    (machine left right).stepConfig (gapEmptyConfig source) =
      some (gapEmptyConfig target) := by
  exact stepConfig_some_of_transition_some gapEmptyEmbed
    (gapEmpty_transition_some left right) hstep

theorem gapEmpty_run_lift
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : Config
      (ProductGapExpander.Control (emptyExtra left))}
    (hrun :
      (ProductGapExpander.machine
        (emptyExtra_positive left)).runConfigExact? steps source =
          some target) :
    (machine left right).runConfigExact? steps (gapEmptyConfig source) =
      some (gapEmptyConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    gapEmptyEmbed
  · intro c d hstep
    exact gapEmpty_step_active left right hstep
  · exact hrun

theorem gapNonempty_halt_transition_none
    (read : Option MachineCodeSymbol) :
    (ProductGapExpander.machine (show 0 < 2 by decide)).transition
        (ProductGapExpander.machine (show 0 < 2 by decide)).halt read =
      none := by
  rfl

private theorem gapNonempty_transition_some
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (state : ProductGapExpander.Control 2)
    (read write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : ProductGapExpander.Control 2)
    (htransition :
      (ProductGapExpander.machine (show 0 < 2 by decide)).transition
          state read = some (write, direction, target)) :
    (machine left right).transition (gapNonemptyEmbed state) read =
      some (write, direction, gapNonemptyEmbed target) := by
  have hactive : state ≠
      (ProductGapExpander.machine (show 0 < 2 by decide)).halt := by
    intro hstate
    subst state
    rw [gapNonempty_halt_transition_none] at htransition
    contradiction
  simp [machine, transition, gapNonemptyEmbed, hactive,
    mapTransition, htransition]

theorem gapNonempty_step_active
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {source target : Config (ProductGapExpander.Control 2)}
    (hstep :
      (ProductGapExpander.machine (show 0 < 2 by decide)).stepConfig
        source = some target) :
    (machine left right).stepConfig (gapNonemptyConfig source) =
      some (gapNonemptyConfig target) := by
  exact stepConfig_some_of_transition_some gapNonemptyEmbed
    (gapNonempty_transition_some left right) hstep

theorem gapNonempty_run_lift
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : Config (ProductGapExpander.Control 2)}
    (hrun :
      (ProductGapExpander.machine (show 0 < 2 by decide)).runConfigExact?
        steps source = some target) :
    (machine left right).runConfigExact? steps
        (gapNonemptyConfig source) =
      some (gapNonemptyConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    gapNonemptyEmbed
  · intro c d hstep
    exact gapNonempty_step_active left right hstep
  · exact hrun

theorem haltingTransitionsDisabled {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    TuringMachine.HaltingTransitionsDisabled (machine left right) := by
  intro read
  rfl

end ProductPairMaterializer
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
