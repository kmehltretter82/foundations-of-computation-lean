import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.InitialLayout

set_option doc.verso true

/-!
# Protected exact-fuel layout code runner

Interface between the raw stage-program materializer and the protected layout
runner.  The assembly theorem here keeps the public stage-program code-machine
construction independent from the concrete implementation details of either
phase.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel

/--
Semantic code recognizer for protected exact-fuel layouts.  A concrete finite
table should realize this predicate by parsing the encoded layout and running
the selected finite transition table for the protected fuel.
-/
def layoutCodeRun {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match Layout.decode stateCount tokens with
  | none => none
  | some (L, suffix) =>
      match suffix with
      | [] =>
          if TuringMachine.HaltsFromIn M L.fuel L.config then
            some ([] : Word MachineCodeSymbol)
          else
            none
      | _ :: _ => none

/--
Semantic one-step transformer for protected exact-fuel layouts.  This is the
code-level target for the eventual finite table that parses one encoded layout,
performs one selected-machine step, decrements the protected fuel, and emits
the next encoded layout.
-/
def layoutStepCode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match Layout.decode stateCount tokens with
  | none => none
  | some (L, suffix) =>
      match suffix with
      | [] =>
          match Layout.step M L with
          | none => none
          | some L' => some (Layout.encode L')
      | _ :: _ => none

theorem layoutCodeRun_eq_some_iff_decode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    layoutCodeRun M tokens = some ([] : Word MachineCodeSymbol) <->
      exists L : Layout stateCount,
        Layout.decode stateCount tokens = some (L, []) /\
          Layout.accepts M L := by
  constructor
  · intro hrun
    unfold layoutCodeRun at hrun
    cases hdecode : Layout.decode stateCount tokens with
    | none =>
        rw [hdecode] at hrun
        cases hrun
    | some decoded =>
        rcases decoded with ⟨L, suffix⟩
        cases suffix with
        | nil =>
            by_cases hhalt :
                TuringMachine.HaltsFromIn M L.fuel L.config
            · exact
                ⟨L, rfl, by
                  simpa [Layout.accepts] using hhalt⟩
            · simp [hdecode, hhalt] at hrun
        | cons _ _ =>
            simp [hdecode] at hrun
  · intro h
    rcases h with ⟨L, hdecode, haccepts⟩
    unfold layoutCodeRun
    rw [hdecode]
    have hhalt :
        TuringMachine.HaltsFromIn M L.fuel L.config := by
      simpa [Layout.accepts] using haccepts
    simp [hhalt]
    rfl

theorem layoutCodeRun_encode_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) :
    layoutCodeRun M (Layout.encode L) =
        some ([] : Word MachineCodeSymbol) <->
      Layout.accepts M L := by
  constructor
  · intro hrun
    by_cases hhalt : TuringMachine.HaltsFromIn M L.fuel L.config
    · simpa [Layout.accepts] using hhalt
    · simp [layoutCodeRun, Layout.decode_encode, hhalt] at hrun
  · intro haccepts
    have hhalt : TuringMachine.HaltsFromIn M L.fuel L.config := by
      simpa [Layout.accepts] using haccepts
    simp [layoutCodeRun, Layout.decode_encode, hhalt]
    rfl

theorem layoutCodeRun_encode_initial_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    layoutCodeRun M (Layout.encode (Layout.initial M input fuel)) =
        some ([] : Word MachineCodeSymbol) <->
      TuringMachine.HaltsOnInputIn M fuel input := by
  exact Iff.trans
    (layoutCodeRun_encode_eq_some_iff M
      (Layout.initial M input fuel))
    (Layout.accepts_initial_iff_haltsOnInputIn M input fuel)

theorem layoutStepCode_encode_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) (output : Word MachineCodeSymbol) :
    layoutStepCode M (Layout.encode L) = some output <->
      exists L' : Layout stateCount,
        Layout.step M L = some L' /\ output = Layout.encode L' := by
  constructor
  · intro hstepCode
    unfold layoutStepCode at hstepCode
    simp [Layout.decode_encode] at hstepCode
    cases hstep : Layout.step M L with
    | none =>
        simp [hstep] at hstepCode
    | some L' =>
        simp [hstep] at hstepCode
        exact ⟨L', rfl, hstepCode.symm⟩
  · intro h
    rcases h with ⟨L', hstep, houtput⟩
    subst output
    simp [layoutStepCode, Layout.decode_encode, hstep]

theorem layoutStepCode_eq_some_iff_decode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens output : Word MachineCodeSymbol) :
    layoutStepCode M tokens = some output <->
      exists L : Layout stateCount,
      exists L' : Layout stateCount,
        Layout.decode stateCount tokens = some (L, []) /\
          Layout.step M L = some L' /\
            output = Layout.encode L' := by
  constructor
  · intro hstepCode
    unfold layoutStepCode at hstepCode
    cases hdecode : Layout.decode stateCount tokens with
    | none =>
        rw [hdecode] at hstepCode
        cases hstepCode
    | some decoded =>
        rcases decoded with ⟨L, suffix⟩
        cases suffix with
        | nil =>
            cases hstep : Layout.step M L with
            | none =>
                simp [hdecode, hstep] at hstepCode
            | some L' =>
                simp [hdecode, hstep] at hstepCode
                exact ⟨L, L', rfl, hstep, hstepCode.symm⟩
        | cons _ _ =>
            simp [hdecode] at hstepCode
  · intro h
    rcases h with ⟨L, L', hdecode, hstep, houtput⟩
    subst output
    simp [layoutStepCode, hdecode, hstep]

theorem layoutCodeRun_encode_succ_iff_step {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) (fuel : Nat)
    (hfuel : L.fuel = fuel + 1) :
    layoutCodeRun M (Layout.encode L) =
        some ([] : Word MachineCodeSymbol) <->
      exists L' : Layout stateCount,
        Layout.step M L = some L' /\
          layoutCodeRun M (Layout.encode L') =
            some ([] : Word MachineCodeSymbol) := by
  rw [layoutCodeRun_encode_eq_some_iff]
  constructor
  · intro haccepts
    rcases
        (Layout.accepts_succ_iff_step
          (M := M) L fuel hfuel).mp haccepts with
      ⟨L', hstep, htail⟩
    exact
      ⟨L', hstep,
        (layoutCodeRun_encode_eq_some_iff M L').mpr htail⟩
  · intro h
    rcases h with ⟨L', hstep, htailRun⟩
    have htail :
        Layout.accepts M L' :=
      (layoutCodeRun_encode_eq_some_iff M L').mp htailRun
    exact
      (Layout.accepts_succ_iff_step
        (M := M) L fuel hfuel).mpr
        ⟨L', hstep, htail⟩

def LayoutCodeMachineSpec {stateCount : Nat}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens <->
      layoutCodeRun M tokens = some ([] : Word MachineCodeSymbol)

def LayoutCodeMachineConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    LayoutCodeMachineSpec runner M

def FinStateLayoutCodeMachineConstruction : Prop :=
  forall stateCount : Nat,
  forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
    LayoutCodeMachineConstruction M

def LayoutCodeRunnerSpec {stateCount : Nat}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  forall L : Layout stateCount,
    TuringMachine.HaltsOnInput runner (Layout.encode L) <->
      Layout.accepts M L

def LayoutCodeRunnerConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    LayoutCodeRunnerSpec runner M

theorem layoutCodeRunnerSpec_of_codeMachineSpec {stateCount : Nat}
    {runnerState : Type}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hrunner : LayoutCodeMachineSpec runner M) :
    LayoutCodeRunnerSpec runner M := by
  intro L
  exact Iff.trans (hrunner (Layout.encode L))
    (layoutCodeRun_encode_eq_some_iff M L)

theorem layoutCodeRunnerConstruction_of_codeMachine
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcode : LayoutCodeMachineConstruction M) :
    LayoutCodeRunnerConstruction M := by
  rcases hcode with ⟨runnerState, runner, hrunner⟩
  exact
    ⟨runnerState, runner,
      layoutCodeRunnerSpec_of_codeMachineSpec hrunner⟩

theorem layoutCodeMachineFinStateFiniteLeaf :
    FinStateLayoutCodeMachineConstruction := by
  intro stateCount M
  cases stateCount with
  | zero =>
      exact False.elim (Fin.elim0 M.start)
  | succ _ =>
      sorry

theorem layoutCodeRunnerConstructionFiniteLeaf {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    LayoutCodeRunnerConstruction M :=
  layoutCodeRunnerConstruction_of_codeMachine
    (layoutCodeMachineFinStateFiniteLeaf stateCount M)

namespace StageProgram

theorem codeMachineConstruction_of_materializer_layoutRunner_compose
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcompose : OutputThenRecognizeConstruction)
    (hmaterializer : InitialLayoutMaterializerConstruction M)
    (hlayout : LayoutCodeRunnerConstruction M) :
    CodeMachineConstruction M := by
  rcases hmaterializer with
    ⟨materializerState, materializer, hmaterializer⟩
  rcases hlayout with ⟨layoutState, layoutRunner, hlayoutRunner⟩
  let P : Word MachineCodeSymbol -> Prop :=
    fun output => TuringMachine.HaltsOnInput layoutRunner output
  have hrecognizes : FiniteRecognizer.Recognizes layoutRunner P := by
    intro output
    rfl
  rcases
      hcompose materializer layoutRunner
        (Layout.stageCodeToInitialLayoutCode M) P
        hmaterializer hrecognizes with
    ⟨pipelineState, pipeline, hpipeline⟩
  refine ⟨pipelineState, pipeline, ?_⟩
  intro tokens
  exact Iff.trans (hpipeline tokens) (by
    rw [run_eq_some_iff_decodeNat M tokens]
    constructor
    · intro h
      rcases h with ⟨output, houtput, hrunner⟩
      unfold Layout.stageCodeToInitialLayoutCode at houtput
      cases hdecode : MachineDescription.decodeNat tokens with
      | none =>
          rw [hdecode] at houtput
          cases houtput
      | some decoded =>
          rcases decoded with ⟨fuel, input⟩
          rw [hdecode] at houtput
          cases houtput
          have haccept :
              Layout.accepts M (Layout.initial M input fuel) :=
            (hlayoutRunner (Layout.initial M input fuel)).mp hrunner
          have hhalt :
              TuringMachine.HaltsOnInputIn M fuel input :=
            (Layout.accepts_initial_iff_haltsOnInputIn
              M input fuel).mp haccept
          exact ⟨fuel, input, rfl, hhalt⟩
    · intro h
      rcases h with ⟨fuel, input, hdecode, hhalt⟩
      refine
        ⟨Layout.encode (Layout.initial M input fuel), ?_, ?_⟩
      · simp [Layout.stageCodeToInitialLayoutCode, hdecode]
      · exact
          (hlayoutRunner (Layout.initial M input fuel)).mpr
            ((Layout.accepts_initial_iff_haltsOnInputIn
              M input fuel).mpr hhalt))

theorem codeMachineConstruction_of_materializer_layoutCodeMachine_compose
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcompose : OutputThenRecognizeConstruction)
    (hmaterializer : InitialLayoutMaterializerConstruction M)
    (hlayout : LayoutCodeMachineConstruction M) :
    CodeMachineConstruction M :=
  codeMachineConstruction_of_materializer_layoutRunner_compose
    hcompose hmaterializer
    (layoutCodeRunnerConstruction_of_codeMachine hlayout)

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
