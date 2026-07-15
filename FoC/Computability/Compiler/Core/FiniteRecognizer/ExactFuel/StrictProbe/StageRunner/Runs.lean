import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.Contracts
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageRunner.Machine
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Spec

set_option doc.verso true

/-!
# Exact-fuel stage-runner executions

Exact phase lifts and boundary handoffs connect stage-input construction with
the cyclic driver's representative-indexed semantics.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace StageRunner

theorem materializer_empty_transition_none {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (read : Option MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).transition
        emptyEndpoint read = none := by
  rfl

theorem materializer_nonempty_transition_none {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (read : Option MachineCodeSymbol) :
    (InitialMaterializer.FullMaterializerMachine.machine M).transition
        nonemptyEndpoint read = none := by
  rfl

theorem materializer_stepConfig_of_some {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      (InitialMaterializer.FullMaterializerMachine.Control M))
    (hstep :
      (InitialMaterializer.FullMaterializerMachine.machine M).stepConfig
          c = some d) :
    (machine M K).stepConfig (materializerConfig c) =
      some (materializerConfig d) := by
  have hempty : c.state ≠ emptyEndpoint := by
    intro hc
    unfold TuringMachine.stepConfig at hstep
    rw [hc, materializer_empty_transition_none] at hstep
    contradiction
  have hnonempty : c.state ≠ nonemptyEndpoint := by
    intro hc
    unfold TuringMachine.stepConfig at hstep
    rw [hc, materializer_nonempty_transition_none] at hstep
    contradiction
  unfold TuringMachine.stepConfig at hstep ⊢
  simp only [machine, materializerConfig,
    TuringMachine.PhaseEmbedding.liftConfig, transition,
    hempty, hnonempty, ↓reduceIte]
  cases htransition :
      InitialMaterializer.FullMaterializerMachine.transition
        M c.state (Tape.read c.tape) with
  | none =>
      simp [InitialMaterializer.FullMaterializerMachine.machine,
        htransition] at hstep
  | some action =>
      rcases action with ⟨write, direction, target⟩
      simp [InitialMaterializer.FullMaterializerMachine.machine,
        htransition] at hstep ⊢
      cases hstep
      exact ⟨rfl, rfl⟩

theorem materializer_run_lift {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      (InitialMaterializer.FullMaterializerMachine.Control M)}
    (hrun :
      (InitialMaterializer.FullMaterializerMachine.machine M).runConfigExact?
          steps source = some target) :
    (machine M K).runConfigExact? steps (materializerConfig source) =
      some (materializerConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.materializer
  · exact materializer_stepConfig_of_some M K
  · exact hrun

theorem compactor_halt_transition_none
    (read : Option MachineCodeSymbol) :
    StageInput.TwoBlankCompactor.machine.transition
        StageInput.TwoBlankCompactor.machine.halt
        read = none := by
  rfl

theorem compactor_stepConfig_of_some {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control)
    (hstep :
      StageInput.TwoBlankCompactor.machine.stepConfig
          c = some d) :
    (machine M K).stepConfig (compactorConfig c) =
      some (compactorConfig d) := by
  have hactive :
      c.state ≠
        StageInput.TwoBlankCompactor.machine.halt := by
    intro hc
    unfold TuringMachine.stepConfig at hstep
    rw [hc, compactor_halt_transition_none] at hstep
    contradiction
  unfold TuringMachine.stepConfig at hstep ⊢
  simp only [machine, compactorConfig,
    TuringMachine.PhaseEmbedding.liftConfig, transition,
    hactive, ↓reduceIte]
  cases htransition :
      StageInput.TwoBlankCompactor.transition
        c.state (Tape.read c.tape) with
  | none =>
      simp [StageInput.TwoBlankCompactor.machine,
        htransition] at hstep
  | some action =>
      rcases action with ⟨write, direction, target⟩
      simp [StageInput.TwoBlankCompactor.machine,
        htransition] at hstep ⊢
      cases hstep
      exact ⟨rfl, rfl⟩

theorem compactor_run_lift {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control}
    (hrun :
      StageInput.TwoBlankCompactor.machine.runConfigExact?
          steps source = some target) :
    (machine M K).runConfigExact? steps (compactorConfig source) =
      some (compactorConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.compactor
  · exact compactor_stepConfig_of_some M K
  · exact hrun

theorem cyclic_stepConfig {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (c : TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control stateCount updateState)) :
    (machine M K).stepConfig (cyclicConfig c) =
      Option.map cyclicConfig
        ((CyclicDriverIntegration.machine M K).stepConfig c) := by
  unfold TuringMachine.stepConfig
  simp only [machine, cyclicConfig,
    TuringMachine.PhaseEmbedding.liftConfig, transition]
  cases htransition : CyclicDriverIntegration.transition
      M K c.state (Tape.read c.tape) with
  | none =>
      simp [CyclicDriverIntegration.machine, htransition]
  | some action =>
      rcases action with ⟨write, direction, target⟩
      simp [CyclicDriverIntegration.machine, htransition,
        cyclicConfig, TuringMachine.PhaseEmbedding.liftConfig]

private theorem write_read_eq_self (T : Tape MachineCodeSymbol) :
    Tape.write (Tape.read T) T = T := by
  cases T
  rfl

def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)

theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape T) T := by
  exact Machine.moveLeft_moveRight_equiv_self T

def cyclicStartConfig {stateCount : Nat} {updateState : Type}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (T : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control M updateState) where
  state := .cyclic (.gate (.header M.start))
  tape := T

theorem empty_handoff_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (T : Tape MachineCodeSymbol) :
    (machine M K).runConfigExact? 1
        { state := .materializer emptyEndpoint, tape := T } =
      some (cyclicStartConfig M (Tape.move Direction.left T)) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, emptyEndpoint, cyclicStartConfig,
    write_read_eq_self]

theorem nonempty_handoff_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (T : Tape MachineCodeSymbol) :
    (machine M K).runConfigExact? 2
        { state := .materializer nonemptyEndpoint, tape := T } =
      some
        (compactorConfig
          (StageInput.TwoBlankCompactor.config
            .seek (roundTripTape T))) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, emptyEndpoint, nonemptyEndpoint, compactorConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    StageInput.TwoBlankCompactor.config,
    roundTripTape, write_read_eq_self]

theorem compactor_handoff_run_exact {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (T : Tape MachineCodeSymbol) :
    (machine M K).runConfigExact? 2
        { state := .compactor
            StageInput.TwoBlankCompactor.machine.halt,
          tape := T } =
      some (cyclicStartConfig M (roundTripTape T)) := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, cyclicStartConfig, roundTripTape,
    write_read_eq_self]

/-- Once the public prefix enters the cyclic phase, the outer and inner
machines have exactly the same finite runs and halt at the same embedded
state. -/
theorem cyclic_haltsFrom_iff {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (source : TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control stateCount updateState)) :
    TuringMachine.HaltsFrom (machine M K) (cyclicConfig source) ↔
      TuringMachine.HaltsFrom
        (CyclicDriverIntegration.machine M K) source := by
  constructor
  · rintro ⟨outerFinal, houter, hhalt⟩
    rcases TuringMachine.computes_to_computesIn houter with
      ⟨steps, houterIn⟩
    have houterExact :=
      TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr houterIn
    have hlift :=
      TuringMachine.PhaseEmbedding.runConfigExact?_lift
        Control.cyclic (cyclic_stepConfig M K) steps source
    have hlift' :
        (machine M K).runConfigExact? steps (cyclicConfig source) =
          Option.map
            (TuringMachine.PhaseEmbedding.liftConfig Control.cyclic)
            ((CyclicDriverIntegration.machine M K).runConfigExact?
              steps source) := by
      change
        (machine M K).runConfigExact? steps
            (TuringMachine.PhaseEmbedding.liftConfig
              Control.cyclic source) = _
      exact hlift
    rw [hlift'] at houterExact
    cases hinner :
        (CyclicDriverIntegration.machine M K).runConfigExact?
          steps source with
    | none =>
        simp [hinner] at houterExact
    | some innerFinal =>
        simp [hinner] at houterExact
        cases houterExact
        refine ⟨innerFinal, ?_, ?_⟩
        · exact TuringMachine.computesIn_to_computes
            (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hinner)
        · simpa [TuringMachine.Halted, cyclicConfig,
            TuringMachine.PhaseEmbedding.liftConfig,
            machine, CyclicDriverIntegration.machine] using hhalt
  · rintro ⟨innerFinal, hinner, hhalt⟩
    refine ⟨cyclicConfig innerFinal, ?_, ?_⟩
    · exact TuringMachine.PhaseEmbedding.computes_lift
        Control.cyclic (cyclic_stepConfig M K) hinner
    · simpa [TuringMachine.Halted, cyclicConfig,
        TuringMachine.PhaseEmbedding.liftConfig,
        machine, CyclicDriverIntegration.machine] using hhalt

def initialFrame {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    SerializedFieldComposer.CarriedStateFrame.LoopFrame stateCount :=
  SerializedFieldComposer.CarriedStateFrame.ofParsed
    (Layout.initial M input fuel)

theorem initialFrame_withFuel_physicalFrame {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    (SerializedFieldComposer.CarriedStateFrame.withFuel
      fuel (initialFrame M input fuel)).physicalFrame =
        Layout.initial M input fuel := by
  cases input <;> rfl

theorem initialFrame_semanticConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    RelationalDriverInduction.semanticConfig
        (initialFrame M input fuel) =
      TuringMachine.initial M input := by
  unfold RelationalDriverInduction.semanticConfig initialFrame
  rw [SerializedFieldComposer.CarriedStateFrame.semanticLayout_ofParsed]
  exact Layout.config_initial M input fuel

theorem cyclicStartConfig_eq_sourceConfig {stateCount : Nat}
    {updateState : Type}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat)
    (T : Tape MachineCodeSymbol) :
    cyclicStartConfig (updateState := updateState) M T =
      cyclicConfig
        (CyclicRelationalContract.sourceConfig
          fuel (initialFrame M input fuel) T) := by
  cases input <;> rfl

theorem initial_eq_materializerConfig {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState)
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    TuringMachine.initial (machine M K)
        (StageProgram.stageCode input fuel) =
      materializerConfig
        (InitialMaterializer.FullMaterializerMachine.sourceConfig
          M fuel input) := by
  rw [InitialMaterializer.FullMaterializerMachine.sourceConfig_eq_initial]
  rfl

theorem computes_of_runConfigExact?_eq_some
    {M : TuringMachine symbol state} {steps : Nat}
    {source target : TuringMachine.Configuration symbol state}
    (hrun : M.runConfigExact? steps source = some target) :
    TuringMachine.Computes M source target :=
  TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)

end StageRunner
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
