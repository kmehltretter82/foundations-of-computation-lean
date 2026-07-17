import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Prefix
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.TwoBlankCompactor
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageRunner.Runs

set_option doc.verso true

/-!
# Product pair-prefix finish machine

Embed the product prefix and left stage-input materializer, then compact the
two internal workspace blanks before halting on the canonical pair frame.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe

open InitialMaterializer

namespace ProductFinish

inductive Control {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) where
  | prefixPhase (inner : ProductPrefix.Control right)
  | materializer
      (inner : FullMaterializerMachine.Control left)
  | materializerReturn
  | compactor (inner : StageInput.TwoBlankCompactor.Control)
  | compactorReturn
  | halt
deriving DecidableEq

namespace Control

def elems {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    List (Control left right) :=
  List.append
    ((ProductPrefix.machine right).statesFinite.elems.map Control.prefixPhase)
    (List.append
      ((FullMaterializerMachine.machine left).statesFinite.elems.map
        Control.materializer)
      (List.append [.materializerReturn]
        (List.append
          (StageInput.TwoBlankCompactor.machine.statesFinite.elems.map
            Control.compactor)
          [.compactorReturn, .halt])))

def finite {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    Foundation.FiniteType (Control left right) where
  elems := elems left right
  complete := by
    intro control
    cases control with
    | prefixPhase inner =>
        have h := (ProductPrefix.machine right).statesFinite.complete inner
        simp [elems, h]
    | materializer inner =>
        have h :=
          (FullMaterializerMachine.machine left).statesFinite.complete inner
        simp [elems, h]
    | materializerReturn => simp [elems]
    | compactor inner =>
        have h :=
          StageInput.TwoBlankCompactor.machine.statesFinite.complete inner
        simp [elems, h]
    | compactorReturn => simp [elems]
    | halt => simp [elems]

end Control

def materializerEndpoint {leftCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)} :
    FullMaterializerMachine.Control left :=
  .header .halt

def emptyMaterializerEndpoint {leftCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)} :
    FullMaterializerMachine.Control left :=
  .emptyPrepend .gate

def transition {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    Control left right -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control left right)
  | .prefixPhase inner, read =>
      match (ProductPrefix.machine right).transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .prefixPhase target)
  | .materializer inner, read =>
      if inner = emptyMaterializerEndpoint then
        some (read, Direction.left, .halt)
      else if inner = materializerEndpoint then
        some (read, Direction.right, .materializerReturn)
      else
        match FullMaterializerMachine.transition left inner read with
        | none => none
        | some (write, direction, target) =>
            some (write, direction, .materializer target)
  | .materializerReturn, read =>
      some (read, Direction.left, .compactor .seek)
  | .compactor inner, read =>
      if inner = StageInput.TwoBlankCompactor.machine.halt then
        some (read, Direction.right, .compactorReturn)
      else
        match StageInput.TwoBlankCompactor.transition inner read with
        | none => none
        | some (write, direction, target) =>
            some (write, direction, .compactor target)
  | .compactorReturn, read =>
      some (read, Direction.left, .halt)
  | .halt, _ => none

def machine {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    TuringMachine MachineCodeSymbol (Control left right) where
  start := .prefixPhase (ProductPrefix.machine right).start
  halt := .halt
  transition := transition left right
  statesFinite := Control.finite left right

def prefixConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      (ProductPrefix.Control right)) :
    TuringMachine.Configuration MachineCodeSymbol (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.prefixPhase c

def materializerConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      (FullMaterializerMachine.Control left)) :
    TuringMachine.Configuration MachineCodeSymbol (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.materializer c

def compactorConfig {leftCount rightCount : Nat}
    {left : TuringMachine MachineCodeSymbol (Fin leftCount)}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control left right) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.compactor c

theorem prefix_stepConfig_of_some {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (c d : TuringMachine.Configuration MachineCodeSymbol
      (ProductPrefix.Control right))
    (hstep : (ProductPrefix.machine right).stepConfig c = some d) :
    (machine left right).stepConfig (prefixConfig c) =
      some (prefixConfig d) := by
  unfold TuringMachine.stepConfig at hstep ⊢
  simp only [machine, prefixConfig,
    TuringMachine.PhaseEmbedding.liftConfig, transition]
  cases htransition :
      (ProductPrefix.machine right).transition
        c.state (Tape.read c.tape) with
  | none =>
      simp [htransition] at hstep
  | some action =>
      rcases action with ⟨write, direction, target⟩
      simp [htransition] at hstep ⊢
      cases hstep
      exact ⟨rfl, rfl⟩

theorem prefix_run_lift {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (ProductPrefix.Control right)}
    (hrun : (ProductPrefix.machine right).runConfigExact? steps source =
      some target) :
    (machine left right).runConfigExact? steps (prefixConfig source) =
      some (prefixConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    Control.prefixPhase
  · exact prefix_stepConfig_of_some left right
  · exact hrun

theorem materializer_endpoint_transition_none {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (read : Option MachineCodeSymbol) :
    (FullMaterializerMachine.machine left).transition
        materializerEndpoint read = none := by
  rfl

theorem materializer_empty_endpoint_transition_none {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (read : Option MachineCodeSymbol) :
    (FullMaterializerMachine.machine left).transition
        emptyMaterializerEndpoint read = none := by
  rfl

theorem materializer_stepConfig_of_some {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (c d : TuringMachine.Configuration MachineCodeSymbol
      (FullMaterializerMachine.Control left))
    (hstep : (FullMaterializerMachine.machine left).stepConfig c =
      some d) :
    (machine left right).stepConfig (materializerConfig c) =
      some (materializerConfig d) := by
  have hactive : c.state ≠ materializerEndpoint := by
    intro hc
    unfold TuringMachine.stepConfig at hstep
    rw [hc, materializer_endpoint_transition_none] at hstep
    contradiction
  have hempty : c.state ≠ emptyMaterializerEndpoint := by
    intro hc
    unfold TuringMachine.stepConfig at hstep
    rw [hc, materializer_empty_endpoint_transition_none] at hstep
    contradiction
  unfold TuringMachine.stepConfig at hstep ⊢
  simp only [machine, materializerConfig,
    TuringMachine.PhaseEmbedding.liftConfig, transition,
    hactive, hempty, ↓reduceIte]
  cases htransition :
      FullMaterializerMachine.transition
        left c.state (Tape.read c.tape) with
  | none =>
      simp [FullMaterializerMachine.machine, htransition] at hstep
  | some action =>
      rcases action with ⟨write, direction, target⟩
      simp [FullMaterializerMachine.machine, htransition] at hstep ⊢
      cases hstep
      exact ⟨rfl, rfl⟩

theorem materializer_run_lift {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (FullMaterializerMachine.Control left)}
    (hrun : (FullMaterializerMachine.machine left).runConfigExact? steps
      source = some target) :
    (machine left right).runConfigExact? steps (materializerConfig source) =
      some (materializerConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    Control.materializer
  · exact materializer_stepConfig_of_some left right
  · exact hrun

theorem compactor_stepConfig_of_some {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (c d : TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control)
    (hstep : StageInput.TwoBlankCompactor.machine.stepConfig c = some d) :
    (machine left right).stepConfig (compactorConfig c) =
      some (compactorConfig d) := by
  have hactive :
      c.state ≠ StageInput.TwoBlankCompactor.machine.halt := by
    intro hc
    unfold TuringMachine.stepConfig at hstep
    rw [hc, StageRunner.compactor_halt_transition_none] at hstep
    contradiction
  unfold TuringMachine.stepConfig at hstep ⊢
  simp only [machine, compactorConfig,
    TuringMachine.PhaseEmbedding.liftConfig, transition,
    hactive, ↓reduceIte]
  cases htransition :
      StageInput.TwoBlankCompactor.transition
        c.state (Tape.read c.tape) with
  | none =>
      simp [StageInput.TwoBlankCompactor.machine, htransition] at hstep
  | some action =>
      rcases action with ⟨write, direction, target⟩
      simp [StageInput.TwoBlankCompactor.machine, htransition] at hstep ⊢
      cases hstep
      exact ⟨rfl, rfl⟩

theorem compactor_run_lift {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control}
    (hrun : StageInput.TwoBlankCompactor.machine.runConfigExact? steps
      source = some target) :
    (machine left right).runConfigExact? steps (compactorConfig source) =
      some (compactorConfig target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    Control.compactor
  · exact compactor_stepConfig_of_some left right
  · exact hrun

theorem materializer_handoff_run_exact {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (tape : Tape MachineCodeSymbol) :
    (machine left right).runConfigExact? 2
        { state := .materializer materializerEndpoint, tape := tape } =
      some
        (compactorConfig
          (StageInput.TwoBlankCompactor.config .seek
            (StageRunner.roundTripTape tape))) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, materializerEndpoint, emptyMaterializerEndpoint,
    compactorConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    StageInput.TwoBlankCompactor.config, StageRunner.roundTripTape,
    Tape.write_read_eq_self]

theorem empty_materializer_handoff_run_exact {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (tape : Tape MachineCodeSymbol) :
    (machine left right).runConfigExact? 1
        { state := .materializer emptyMaterializerEndpoint
          tape := tape } =
      some
        { state := (machine left right).halt
          tape := Tape.move Direction.left tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, emptyMaterializerEndpoint,
    Tape.write_read_eq_self]

theorem compactor_handoff_run_exact {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (tape : Tape MachineCodeSymbol) :
    (machine left right).runConfigExact? 2
        { state := .compactor
            StageInput.TwoBlankCompactor.machine.halt,
          tape := tape } =
      some
        { state := (machine left right).halt
          tape := StageRunner.roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, StageRunner.roundTripTape,
    Tape.write_read_eq_self]

theorem haltingTransitionsDisabled {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    TuringMachine.HaltingTransitionsDisabled (machine left right) := by
  intro read
  rfl


end ProductFinish
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
