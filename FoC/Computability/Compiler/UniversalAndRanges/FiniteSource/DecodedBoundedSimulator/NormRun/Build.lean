import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.DecodedBoundedSimulator.NormRun.Transform

set_option doc.verso true

/-!
# Normalized runner constructions

Construction adapters and final finite leaves for the normalized decoded bounded simulator runner.
-/

namespace FoC
namespace Computability

open Languages


/--
Finite-machine spec for the explicit normalized transition-loop pipeline
transform.
-/
def DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineSpec
    (runner : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      decodedBoundedSimulatorTransitionLoopPipelineCode tokens =
        some ([] : Word MachineCodeSymbol)

/--
Finite-machine construction target for the explicit transition-loop pipeline
transform.
-/
def DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction :
    Prop :=
  exists state : Type,
  exists runner : TuringMachine MachineCodeSymbol state,
    DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineSpec runner

def DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineSpec
    (runner : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      decodedBoundedSimulatorTransitionLoopPipelineIterateCode tokens =
        some ([] : Word MachineCodeSymbol)

def DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction :
    Prop :=
  exists state : Type,
  exists runner : TuringMachine MachineCodeSymbol state,
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineSpec runner

def DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineFinStateConstruction :
    Prop :=
  exists n : Nat,
  exists runner : TuringMachine MachineCodeSymbol (Fin n),
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineSpec runner

def DecodedBoundedSimulatorTransitionLoopInitialHaltMachineSpec
    (runner : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (decodedBoundedSimulatorTransitionLoopFromConfig stage D
            (D.initial
              (MachineDescription.encodeCodeWordAsInput input))).state =
            D.halt

def DecodedBoundedSimulatorTransitionLoopInitialHaltMachineFinStateConstruction :
    Prop :=
  exists n : Nat,
  exists runner : TuringMachine MachineCodeSymbol (Fin n),
    DecodedBoundedSimulatorTransitionLoopInitialHaltMachineSpec runner

def DecodedBoundedSimulatorTransitionLoopInitialHaltMachineConstruction :
    Prop :=
  exists state : Type,
  exists runner : TuringMachine MachineCodeSymbol state,
    DecodedBoundedSimulatorTransitionLoopInitialHaltMachineSpec runner

theorem decodedBoundedSimulatorTransitionLoopInitialHaltMachineConstruction_of_finState
    (hfin :
      DecodedBoundedSimulatorTransitionLoopInitialHaltMachineFinStateConstruction) :
    DecodedBoundedSimulatorTransitionLoopInitialHaltMachineConstruction := by
  rcases hfin with ⟨n, runner, hrunner⟩
  exact ⟨Fin n, runner, hrunner⟩

theorem decodedBoundedSimulatorTransitionLoopInitialHaltMachineFinStateConstruction_of_construction
    (hrunner :
      DecodedBoundedSimulatorTransitionLoopInitialHaltMachineConstruction) :
    DecodedBoundedSimulatorTransitionLoopInitialHaltMachineFinStateConstruction := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  refine
    ⟨runner.statesFinite.elems.length,
      TuringMachine.indexed runner, ?_⟩
  intro tokens
  exact
    Iff.trans
      (TuringMachine.indexed_haltsOnInput_iff runner tokens)
      (hrunner tokens)

theorem decodedBoundedSimulatorTransitionLoopInitialHaltMachineConstruction_iff_finState :
    DecodedBoundedSimulatorTransitionLoopInitialHaltMachineConstruction <->
      DecodedBoundedSimulatorTransitionLoopInitialHaltMachineFinStateConstruction := by
  constructor
  · exact
      decodedBoundedSimulatorTransitionLoopInitialHaltMachineFinStateConstruction_of_construction
  · exact
      decodedBoundedSimulatorTransitionLoopInitialHaltMachineConstruction_of_finState

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_of_finState
    (hfin :
      DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineFinStateConstruction) :
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction := by
  rcases hfin with ⟨n, runner, hrunner⟩
  exact ⟨Fin n, runner, hrunner⟩

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineFinStateConstruction_of_construction
    (hiter :
      DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction) :
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineFinStateConstruction := by
  rcases hiter with ⟨state, runner, hrunner⟩
  refine
    ⟨runner.statesFinite.elems.length,
      TuringMachine.indexed runner, ?_⟩
  intro tokens
  exact
    Iff.trans
      (TuringMachine.indexed_haltsOnInput_iff runner tokens)
      (hrunner tokens)

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_iff_finState :
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction <->
      DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineFinStateConstruction := by
  constructor
  · exact
      decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineFinStateConstruction_of_construction
  · exact
      decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_of_finState

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_of_initialHaltMachine
    (hrunner :
      DecodedBoundedSimulatorTransitionLoopInitialHaltMachineConstruction) :
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff_initial_halt
            tokens))⟩

theorem decodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction_of_iterateCodeMachine
    (hiter :
      DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction) :
    DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction := by
  rcases hiter with ⟨state, runner, hrunner⟩
  refine ⟨state, runner, ?_⟩
  intro tokens
  exact
    Iff.trans (hrunner tokens) (by
      rw [
        decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_pipelineCode
          tokens])

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_of_pipelineCodeMachine
    (hpipeline :
      DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction) :
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction := by
  rcases hpipeline with ⟨state, runner, hrunner⟩
  refine ⟨state, runner, ?_⟩
  intro tokens
  exact
    Iff.trans (hrunner tokens) (by
      rw [
        decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_pipelineCode
          tokens])

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_iff_pipelineCodeMachine :
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction <->
      DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction := by
  constructor
  · exact
      decodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction_of_iterateCodeMachine
  · exact
      decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_of_pipelineCodeMachine

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_of_codeMachine
    (hcode : CodePrefixDecodedBoundedSimulatorCodeMachineConstruction) :
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction := by
  rcases hcode with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_iff_code
            tokens ([] : Word MachineCodeSymbol)))⟩

theorem codeMachineConstruction_of_decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachine
    (hiter :
      DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction) :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  rcases hiter with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_iff_code
          tokens ([] : Word MachineCodeSymbol))⟩

theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_iff_codeMachine :
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction <->
      CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  constructor
  · exact
      codeMachineConstruction_of_decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachine
  · exact
      decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_of_codeMachine

theorem decodedBoundedSimulatorStageProgramRunnerConstruction_of_pipelineIterateCodeMachine
    (hiter :
      DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction) :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists encoded : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens = some (stage, encoded) ∧
              CodePrefixRecognizerProgram.run encoded stage = some [] := by
  rcases hiter with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_stageProgramRun_iff
          tokens)⟩

theorem decodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction_of_codeMachine
    (hcode : CodePrefixDecodedBoundedSimulatorCodeMachineConstruction) :
    DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction := by
  rcases hcode with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_iff_code
            tokens ([] : Word MachineCodeSymbol)))⟩

theorem codeMachineConstruction_of_decodedBoundedSimulatorTransitionLoopPipelineCodeMachine
    (hcode :
      DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction) :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  rcases hcode with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_iff_code
          tokens ([] : Word MachineCodeSymbol))⟩

theorem decodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction_iff_codeMachine :
    DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction <->
      CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  constructor
  · exact
      codeMachineConstruction_of_decodedBoundedSimulatorTransitionLoopPipelineCodeMachine
  · exact
      decodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction_of_codeMachine

/--
Transition-loop form of the normalized bounded simulator runner.  This is the
actual uniform-runner leaf: the machine must interpret the decoded description
as transition-table data for exactly the parsed stage count.
-/
def DecodedBoundedSimulatorTransitionLoopRunnerSpec
    (runner : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (decodedBoundedSimulatorTransitionLoopConfig
            stage D input).state = D.halt

/--
Finite-machine construction target for the decoded transition-loop runner.
-/
def DecodedBoundedSimulatorTransitionLoopRunnerConstruction : Prop :=
  exists state : Type,
  exists runner : TuringMachine MachineCodeSymbol state,
    DecodedBoundedSimulatorTransitionLoopRunnerSpec runner

theorem decodedBoundedSimulatorTransitionLoopRunnerConstruction_of_pipelineCodeMachine
    (hcode :
      DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction) :
    DecodedBoundedSimulatorTransitionLoopRunnerConstruction := by
  rcases hcode with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorTransitionLoopPipelineCode_eq_some_nil_iff
          tokens)⟩

theorem decodedBoundedSimulatorTransitionLoopRunnerConstruction_of_pipelineIterateCodeMachine
    (hcode :
      DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction) :
    DecodedBoundedSimulatorTransitionLoopRunnerConstruction := by
  rcases hcode with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff
          tokens)⟩

/--
Canonical simulator layout for a decoded bounded-simulator call after the
stage, description, and residual code input have been parsed.
-/
def decodedBoundedSimulatorExactInitialLayout
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    MachineDescription.SimulatorLayout :=
  MachineDescription.SimulatorLayout.initial D
    (MachineDescription.encodeCodeWordAsInput input) stage

/-- The exact initial layout carries the requested stage. -/
theorem decodedBoundedSimulatorExactInitialLayout_stage
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    (decodedBoundedSimulatorExactInitialLayout stage D input).stage =
      stage :=
  rfl

/-- The exact initial layout carries the encoded code-word input. -/
theorem decodedBoundedSimulatorExactInitialLayout_input
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    (decodedBoundedSimulatorExactInitialLayout stage D input).input =
      MachineDescription.encodeCodeWordAsInput input :=
  rfl

/-- The exact initial layout starts from the decoded machine's initial config. -/
theorem decodedBoundedSimulatorExactInitialLayout_config
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    (decodedBoundedSimulatorExactInitialLayout stage D input).config =
      D.initial (MachineDescription.encodeCodeWordAsInput input) :=
  rfl

/-- The exact initial layout has no pre-existing hit flag. -/
theorem decodedBoundedSimulatorExactInitialLayout_hit
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    (decodedBoundedSimulatorExactInitialLayout stage D input).hit =
      false :=
  rfl

/--
Running the exact simulator layout for its stage exposes exactly the decoded
machine's bounded run configuration.
-/
theorem decodedBoundedSimulatorExactInitialLayout_afterRun_config
    (stage : Nat) (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    (MachineDescription.SimulatorLayout.afterRun D
        (decodedBoundedSimulatorExactInitialLayout stage D input)
        stage).config =
      D.runConfig stage
        (D.initial (MachineDescription.encodeCodeWordAsInput input)) :=
  rfl

/--
Exact simulator-layout form of the normalized bounded simulator runner.
-/
def DecodedBoundedSimulatorExactLayoutRunnerSpec
    (runner : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (MachineDescription.SimulatorLayout.afterRun D
            (decodedBoundedSimulatorExactInitialLayout stage D input)
            stage).config.state = D.halt

/--
Finite-machine construction target for the exact simulator-layout runner.
-/
def DecodedBoundedSimulatorExactLayoutRunnerConstruction : Prop :=
  exists state : Type,
  exists runner : TuringMachine MachineCodeSymbol state,
    DecodedBoundedSimulatorExactLayoutRunnerSpec runner

/--
The stage-program acceptance predicate is equivalent to the normalized boolean
bounded-trace predicate.
-/
theorem decodedBoundedSimulatorStageProgramRun_iff_haltsInBool
    (tokens : Word MachineCodeSymbol) :
    (exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens = some (stage, encoded) ∧
          CodePrefixRecognizerProgram.run encoded stage = some []) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          MachineDescription.haltsInBool D stage
            (MachineDescription.encodeCodeWordAsInput input) = true := by
  constructor
  · intro h
    rcases h with ⟨stage, encoded, hstage, hprogram⟩
    rcases
        (codePrefixRecognizerProgram_run_eq_some_nil_iff_haltsInBool
          encoded stage).mp hprogram with
      ⟨D, input, hdecode, hhalts⟩
    have hencoded :
        encoded =
          List.append (MachineDescription.encodeDescription D) input :=
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        hdecode
    exact ⟨stage, D, input, by simpa [hencoded] using! hstage, hhalts⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalts⟩
    exact
      ⟨stage,
        List.append (MachineDescription.encodeDescription D) input,
        hstage,
        (codePrefixRecognizerProgram_run_eq_some_nil_iff_haltsInBool
          (List.append (MachineDescription.encodeDescription D) input)
          stage).mpr
          ⟨D, input,
            MachineDescription.decodeDescriptionPrefix_encodeDescription_append
              D input,
            hhalts⟩⟩

/--
The normalized boolean bounded-trace predicate is exactly the run-config halt
state predicate.
-/
theorem decodedBoundedSimulatorHaltsInBool_iff_runConfig
    (tokens : Word MachineCodeSymbol) :
    (exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          MachineDescription.haltsInBool D stage
            (MachineDescription.encodeCodeWordAsInput input) = true) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (D.runConfig stage
            (D.initial
              (MachineDescription.encodeCodeWordAsInput input))).state =
            D.halt := by
  constructor
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalts⟩
    have hhaltsIn :
        D.HaltsIn stage
          (MachineDescription.encodeCodeWordAsInput input) :=
      (MachineDescription.haltsInBool_eq_true_iff D stage
        (MachineDescription.encodeCodeWordAsInput input)).mp hhalts
    exact ⟨stage, D, input, hstage, by
      simpa [MachineDescription.HaltsIn] using hhaltsIn⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hrun⟩
    have hhaltsIn :
        D.HaltsIn stage
          (MachineDescription.encodeCodeWordAsInput input) := by
      simpa [MachineDescription.HaltsIn] using hrun
    exact
      ⟨stage, D, input, hstage,
        (MachineDescription.haltsInBool_eq_true_iff D stage
          (MachineDescription.encodeCodeWordAsInput input)).mpr hhaltsIn⟩

/--
The exact simulator-layout predicate is the same run-config halt-state
predicate in layout form.
-/
theorem decodedBoundedSimulatorExactLayoutRun_iff_runConfig
    (tokens : Word MachineCodeSymbol) :
    (exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (MachineDescription.SimulatorLayout.afterRun D
            (decodedBoundedSimulatorExactInitialLayout stage D input)
            stage).config.state = D.halt) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (D.runConfig stage
            (D.initial
              (MachineDescription.encodeCodeWordAsInput input))).state =
            D.halt := by
  constructor
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalt⟩
    exact ⟨stage, D, input, hstage, by
      simpa [
        decodedBoundedSimulatorExactInitialLayout_afterRun_config
          stage D input] using hhalt⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalt⟩
    exact ⟨stage, D, input, hstage, by
      simpa [
        decodedBoundedSimulatorExactInitialLayout_afterRun_config
          stage D input] using hhalt⟩

/--
The transition-loop predicate is the same run-config halt-state predicate,
with the loop operation named explicitly for the remaining finite runner.
-/
theorem decodedBoundedSimulatorTransitionLoopRun_iff_runConfig
    (tokens : Word MachineCodeSymbol) :
    (exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (decodedBoundedSimulatorTransitionLoopConfig
            stage D input).state = D.halt) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (D.runConfig stage
            (D.initial
              (MachineDescription.encodeCodeWordAsInput input))).state =
            D.halt := by
  constructor
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalt⟩
    exact ⟨stage, D, input, hstage, by
      simpa [decodedBoundedSimulatorTransitionLoopConfig] using! hhalt⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalt⟩
    exact ⟨stage, D, input, hstage, by
      simpa [decodedBoundedSimulatorTransitionLoopConfig] using! hhalt⟩

/--
The exact layout wrapper and the transition-loop leaf expose the same
acceptance predicate.
-/
theorem decodedBoundedSimulatorExactLayoutRun_iff_transitionLoop
    (tokens : Word MachineCodeSymbol) :
    (exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (MachineDescription.SimulatorLayout.afterRun D
            (decodedBoundedSimulatorExactInitialLayout stage D input)
            stage).config.state = D.halt) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (decodedBoundedSimulatorTransitionLoopConfig
            stage D input).state = D.halt :=
  Iff.trans
    (decodedBoundedSimulatorExactLayoutRun_iff_runConfig tokens)
    (Iff.symm
      (decodedBoundedSimulatorTransitionLoopRun_iff_runConfig tokens))

theorem decodedBoundedSimulatorTransitionLoopInitialHalt_iff_haltsIn
    (tokens : Word MachineCodeSymbol) :
    (exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          (decodedBoundedSimulatorTransitionLoopFromConfig stage D
            (D.initial
              (MachineDescription.encodeCodeWordAsInput input))).state =
            D.halt) <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input) := by
  constructor
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalt⟩
    exact ⟨stage, D, input, hstage, by
      simpa [MachineDescription.HaltsIn,
        decodedBoundedSimulatorTransitionLoopFromConfig] using hhalt⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalt⟩
    exact ⟨stage, D, input, hstage, by
      simpa [MachineDescription.HaltsIn,
        decodedBoundedSimulatorTransitionLoopFromConfig] using hhalt⟩

/--
Any independently supplied machine for the code primitive is already a
normalized decoded bounded-simulator runner.
-/
theorem decodedBoundedSimulatorNormalizedRunnerConstruction_of_codeMachine
    (hcode : CodePrefixDecodedBoundedSimulatorCodeMachineConstruction) :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists D : MachineDescription,
          exists input : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens =
                some (stage,
                  List.append (MachineDescription.encodeDescription D)
                    input) ∧
              D.HaltsIn stage
                (MachineDescription.encodeCodeWordAsInput input) := by
  rcases hcode with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorNormalizedCode_transform_eq_some_nil_iff
          tokens)⟩

theorem decodedBoundedSimulatorNormalizedRunnerConstruction_of_initialHaltMachine
    (hrunner :
      DecodedBoundedSimulatorTransitionLoopInitialHaltMachineConstruction) :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists D : MachineDescription,
          exists input : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens =
                some (stage,
                  List.append (MachineDescription.encodeDescription D)
                    input) ∧
              D.HaltsIn stage
                (MachineDescription.encodeCodeWordAsInput input) := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorTransitionLoopInitialHalt_iff_haltsIn
          tokens)⟩

/--
Concrete finite-state leaf for the direct initial-halt transition-loop runner.
-/
theorem decodedBoundedSimulatorTransitionLoopInitialHaltMachineFiniteLeaf :
    DecodedBoundedSimulatorTransitionLoopInitialHaltMachineConstruction := by
  rcases FiniteRecognizer.decodedDescriptionInterpreterFiniteLeaf with
    ⟨state, runner, hrunner⟩
  refine ⟨state, runner, ?_⟩
  intro tokens
  exact
    Iff.trans (hrunner tokens)
      (Iff.symm
        (decodedBoundedSimulatorTransitionLoopInitialHalt_iff_haltsIn
          tokens))

/--
Concrete finite-table leaf for the direct initial-halt transition-loop runner.
-/
theorem decodedBoundedSimulatorTransitionLoopInitialHaltMachineFinStateFiniteLeaf :
    DecodedBoundedSimulatorTransitionLoopInitialHaltMachineFinStateConstruction := by
  exact
    decodedBoundedSimulatorTransitionLoopInitialHaltMachineFinStateConstruction_of_construction
      decodedBoundedSimulatorTransitionLoopInitialHaltMachineFiniteLeaf

/--
Concrete finite-table leaf for the explicit iterative transition-loop pipeline.
-/
theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineFinStateFiniteLeaf :
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineFinStateConstruction := by
  rcases decodedBoundedSimulatorTransitionLoopInitialHaltMachineFinStateFiniteLeaf with
    ⟨n, runner, hrunner⟩
  exact
    ⟨n, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorTransitionLoopPipelineIterateCode_eq_some_nil_iff_initial_halt
            tokens))⟩

/--
Finite-machine leaf for the explicit iterative transition-loop pipeline.
-/
theorem decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction :
    DecodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction := by
  exact
    decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction_of_finState
      decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineFinStateFiniteLeaf

/--
Finite-machine leaf for the explicit transition-loop pipeline transform.
-/
theorem decodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction :
    DecodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction := by
  exact
    decodedBoundedSimulatorTransitionLoopPipelineCodeMachineConstruction_of_iterateCodeMachine
      decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction

/--
Transition-loop finite-machine construction for the normalized decoded simulator.
-/
theorem decodedBoundedSimulatorTransitionLoopRunnerConstruction :
    DecodedBoundedSimulatorTransitionLoopRunnerConstruction := by
  exact
    decodedBoundedSimulatorTransitionLoopRunnerConstruction_of_pipelineIterateCodeMachine
      decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction

/--
The transition-loop runner is enough to realize the exact simulator-layout
runner.
-/
theorem decodedBoundedSimulatorExactLayoutRunnerConstruction_of_transitionLoopRunner
    (hrunner : DecodedBoundedSimulatorTransitionLoopRunnerConstruction) :
    DecodedBoundedSimulatorExactLayoutRunnerConstruction := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorExactLayoutRun_iff_transitionLoop
            tokens))⟩

/--
Exact simulator-layout finite-machine leaf for the normalized decoded
simulator.
-/
theorem decodedBoundedSimulatorExactLayoutRunnerConstruction :
    DecodedBoundedSimulatorExactLayoutRunnerConstruction := by
  exact
    decodedBoundedSimulatorExactLayoutRunnerConstruction_of_transitionLoopRunner
      decodedBoundedSimulatorTransitionLoopRunnerConstruction

/--
The exact simulator-layout runner is enough to realize the run-config runner.
-/
theorem decodedBoundedSimulatorRunConfigRunnerConstruction_of_exactLayoutRunner
    (hrunner : DecodedBoundedSimulatorExactLayoutRunnerConstruction) :
    DecodedBoundedSimulatorRunConfigRunnerConstruction := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorExactLayoutRun_iff_runConfig tokens)⟩

/--
Run-config finite-machine leaf for the normalized decoded simulator.
-/
theorem decodedBoundedSimulatorRunConfigRunnerConstruction :
    DecodedBoundedSimulatorRunConfigRunnerConstruction := by
  exact
    decodedBoundedSimulatorRunConfigRunnerConstruction_of_exactLayoutRunner
      decodedBoundedSimulatorExactLayoutRunnerConstruction

/--
The run-config runner is enough to realize the Boolean bounded-trace runner.
-/
theorem decodedBoundedSimulatorBooleanRunnerConstruction_of_runConfigRunner
    (hrunner : DecodedBoundedSimulatorRunConfigRunnerConstruction) :
    DecodedBoundedSimulatorBooleanRunnerConstruction := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorHaltsInBool_iff_runConfig tokens))⟩

/--
Boolean bounded-trace finite-machine leaf for the normalized decoded simulator.
-/
theorem decodedBoundedSimulatorBooleanRunnerConstruction :
    DecodedBoundedSimulatorBooleanRunnerConstruction := by
  exact
    decodedBoundedSimulatorBooleanRunnerConstruction_of_runConfigRunner
      decodedBoundedSimulatorRunConfigRunnerConstruction

/--
The normalized boolean runner is enough to realize the staged-program runner.
-/
theorem decodedBoundedSimulatorStageProgramRunnerConstruction_of_booleanRunner
    (hrunner : DecodedBoundedSimulatorBooleanRunnerConstruction) :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists encoded : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens = some (stage, encoded) ∧
              CodePrefixRecognizerProgram.run encoded stage = some [] := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorStageProgramRun_iff_haltsInBool
            tokens))⟩

/--
Stage-coded evaluator construction for the fixed staged program
{name}`CodePrefixRecognizerProgram`.

The construction parses the outer unary stage field and evaluates the fixed
staged program at that exact stage.
-/
theorem decodedBoundedSimulatorStageProgramRunnerConstruction :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists encoded : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens = some (stage, encoded) ∧
              CodePrefixRecognizerProgram.run encoded stage = some [] := by
  exact
    decodedBoundedSimulatorStageProgramRunnerConstruction_of_pipelineIterateCodeMachine
      decodedBoundedSimulatorTransitionLoopPipelineIterateCodeMachineConstruction

/--
The stage-program runner is enough to realize the decoded bounded simulator
code primitive.
-/
theorem decodedBoundedSimulatorUniformCodeMachineConstruction_of_stageProgramRunner
    (hrunner :
      exists state : Type,
      exists runner : TuringMachine MachineCodeSymbol state,
        forall tokens : Word MachineCodeSymbol,
          TuringMachine.HaltsOnInput runner tokens <->
            exists stage : Nat,
            exists encoded : Word MachineCodeSymbol,
              MachineDescription.decodeNat tokens = some (stage, encoded) ∧
                CodePrefixRecognizerProgram.run encoded stage = some []) :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  rcases hrunner with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (Iff.symm
          (decodedBoundedSimulatorCode_transform_eq_stageProgramRun_iff
            tokens))⟩

/--
Conversely, a machine realizing the code primitive is a stage-program runner.
Together with
{name}`decodedBoundedSimulatorUniformCodeMachineConstruction_of_stageProgramRunner`,
this identifies the two construction surfaces exactly.
-/
theorem decodedBoundedSimulatorStageProgramRunnerConstruction_of_codeMachine
    (hcode : CodePrefixDecodedBoundedSimulatorCodeMachineConstruction) :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists encoded : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens = some (stage, encoded) ∧
              CodePrefixRecognizerProgram.run encoded stage = some [] := by
  rcases hcode with ⟨state, runner, hrunner⟩
  exact
    ⟨state, runner, fun tokens =>
      Iff.trans (hrunner tokens)
        (decodedBoundedSimulatorCode_transform_eq_stageProgramRun_iff
          tokens)⟩

/--
Uniform code-machine leaf for the decoded bounded simulator primitive.

One fixed machine realizes the transform of
{name}`CodePrefixDecodedBoundedSimulatorCode`, interpreting the decoded
description as tape data rather than selecting a generated
description-specific simulator.
-/
theorem decodedBoundedSimulatorUniformCodeMachineConstruction :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  exact
    decodedBoundedSimulatorUniformCodeMachineConstruction_of_stageProgramRunner
      decodedBoundedSimulatorStageProgramRunnerConstruction

/--
Uniform normalized decoded-bounded-simulator runner construction.

The witness machine must parse the outer unary stage code, recover one
canonical encoded description prefix, and interpret the decoded description as
tape data for exactly the parsed bound.
-/
theorem decodedBoundedSimulatorNormalizedRunnerConstruction :
    exists state : Type,
    exists runner : TuringMachine MachineCodeSymbol state,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          exists stage : Nat,
          exists D : MachineDescription,
          exists input : Word MachineCodeSymbol,
            MachineDescription.decodeNat tokens =
                some (stage,
                  List.append (MachineDescription.encodeDescription D)
                    input) ∧
              D.HaltsIn stage
                (MachineDescription.encodeCodeWordAsInput input) := by
  exact
    decodedBoundedSimulatorNormalizedRunnerConstruction_of_initialHaltMachine
      decodedBoundedSimulatorTransitionLoopInitialHaltMachineFiniteLeaf


end Computability
end FoC
