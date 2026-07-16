import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Branch.PhaseSum
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.PhaseExit

namespace FoC
namespace Computability

namespace FiniteRecognizer.Interpreter.ParserBranchProjection

open FiniteRecognizer.Interpreter.ParserBranchPhaseSum

private theorem stepConfig_eq_map_of_parserTarget_eq_parser
    (state : FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control)
    (tape : Tape MachineCodeSymbol)
    (hstate : parserTarget state = .parser state) :
    FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine.stepConfig
        (parserConfig { state := state, tape := tape }) =
      Option.map parserConfig
        (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine.stepConfig
          { state := state, tape := tape }) := by
  unfold TuringMachine.stepConfig
  simp only [parserConfig, TuringMachine.PhaseEmbedding.liftConfig]
  rw [hstate]
  simp only [FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine,
    FiniteRecognizer.Interpreter.ParserBranchPhaseSum.transition]
  cases htransition : FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine.transition state
      (Tape.read tape) with
  | none => simp
  | some action =>
      rcases action with ⟨write, direction, nextState⟩
      simp [mapAction, parserConfig,
        TuringMachine.PhaseEmbedding.liftConfig]

/-- Until the prefix reaches one of its honest successful terminals, one
branch-machine step from an embedded prefix configuration is exactly one
prefix-machine step with the target embedded by `parserTarget`. -/
theorem active_stepConfig_eq_map
    (source : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control)
    (hactive : ¬ FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.SuccessfulTerminal source) :
    FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine.stepConfig
        (parserConfig source) =
      Option.map parserConfig
        (FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine.stepConfig source) := by
  rcases source with ⟨state, tape⟩
  cases state with
  | fuel fuelZero state =>
      exact stepConfig_eq_map_of_parserTarget_eq_parser _ _ rfl
  | header fuelZero state =>
      exact stepConfig_eq_map_of_parserTarget_eq_parser _ _ rfl
  | shift fuelZero state =>
      exact stepConfig_eq_map_of_parserTarget_eq_parser _ _ rfl
  | countValidate fuelZero =>
      exact stepConfig_eq_map_of_parserTarget_eq_parser _ _ rfl
  | countRewind fuelZero =>
      exact stepConfig_eq_map_of_parserTarget_eq_parser _ _ rfl
  | table fuelZero state =>
      cases state with
      | parser parserState =>
          cases parserState <;>
            try exact stepConfig_eq_map_of_parserTarget_eq_parser _ _ rfl
          exact False.elim (hactive ⟨fuelZero, Or.inl rfl⟩)
      | ready saved =>
          exact False.elim (hactive ⟨fuelZero, Or.inr ⟨saved, rfl⟩⟩)
      | halt =>
          simp [TuringMachine.stepConfig, parserConfig, parserTarget,
            TuringMachine.PhaseEmbedding.liftConfig,
            FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine,
            FiniteRecognizer.Interpreter.ParserBranchPhaseSum.transition,
            FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine,
            FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.transition,
            FiniteRecognizer.Interpreter.SavedCellTransitionParser.machine,
            FiniteRecognizer.Interpreter.SavedCellTransitionParser.transition]

/-- Invert an outer step while the embedded parser prefix is still active. -/
theorem active_step_inversion
    (source : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control)
    (target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.Control)
    (hactive : ¬ FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.SuccessfulTerminal source)
    (hstep : TuringMachine.Step FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
      (parserConfig source) target) :
    exists innerTarget : TuringMachine.Configuration MachineCodeSymbol
        FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control,
      TuringMachine.Step FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine
          source innerTarget ∧
        target = parserConfig innerTarget := by
  have houter := TuringMachine.stepConfig_eq_some_iff_step.mpr hstep
  rw [active_stepConfig_eq_map source hactive] at houter
  cases hinner : FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine.stepConfig source with
  | none =>
      simp [hinner] at houter
  | some innerTarget =>
      simp [hinner] at houter
      subst target
      exact ⟨innerTarget,
        TuringMachine.stepConfig_eq_some_iff_step.mp hinner, rfl⟩

/-- No embedded parser-prefix configuration is the branch machine's accepting
halt state; in particular this holds throughout the active prefix. -/
theorem active_parserConfig_not_halted
    (source : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control)
    (_hactive : ¬ FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.SuccessfulTerminal source) :
    ¬ TuringMachine.Halted FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine
      (parserConfig source) := by
  rcases source with ⟨state, tape⟩
  cases state with
  | fuel fuelZero state =>
      cases state <;>
        simp [TuringMachine.Halted, parserConfig, parserTarget,
          TuringMachine.PhaseEmbedding.liftConfig,
          FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine]
  | header fuelZero state =>
      cases state <;>
        simp [TuringMachine.Halted, parserConfig, parserTarget,
          TuringMachine.PhaseEmbedding.liftConfig,
          FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine]
  | shift fuelZero state =>
      cases state <;>
        simp [TuringMachine.Halted, parserConfig, parserTarget,
          TuringMachine.PhaseEmbedding.liftConfig,
          FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine]
  | countValidate fuelZero =>
      simp [TuringMachine.Halted, parserConfig, parserTarget,
        TuringMachine.PhaseEmbedding.liftConfig,
        FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine]
  | countRewind fuelZero =>
      simp [TuringMachine.Halted, parserConfig, parserTarget,
        TuringMachine.PhaseEmbedding.liftConfig,
        FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine]
  | table fuelZero state =>
      cases state with
      | parser parserState =>
          cases parserState <;>
            simp [TuringMachine.Halted, parserConfig, parserTarget,
              TuringMachine.PhaseEmbedding.liftConfig,
              FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine]
      | ready saved =>
          cases fuelZero <;>
            simp [TuringMachine.Halted, parserConfig, parserTarget,
              TuringMachine.PhaseEmbedding.liftConfig,
              FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine]
      | halt =>
          simp [TuringMachine.Halted, parserConfig, parserTarget,
            TuringMachine.PhaseEmbedding.liftConfig,
            FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine]

/-- Any exact branch-machine halting run from an embedded parser source must
cross an honest successful parser-prefix terminal first. -/
theorem exists_successfulTerminal_of_haltsFromIn
    {steps : Nat}
    {source : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control}
    (hhalts : TuringMachine.HaltsFromIn
      FiniteRecognizer.Interpreter.ParserBranchPhaseSum.machine steps (parserConfig source)) :
    exists innerSteps : Nat,
    exists target : TuringMachine.Configuration MachineCodeSymbol
        FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.Control,
      innerSteps ≤ steps ∧
      TuringMachine.ComputesIn FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.machine
          innerSteps source target ∧
        FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.SuccessfulTerminal target := by
  exact
    TuringMachine.PhaseExitProjection.exists_bounded_inner_exit_of_haltsFromIn_lift
      parserTarget FiniteRecognizer.Interpreter.ParserPrefixPhaseSum.SuccessfulTerminal
      active_step_inversion active_parserConfig_not_halted hhalts


end FiniteRecognizer.Interpreter.ParserBranchProjection
end Computability
end FoC
