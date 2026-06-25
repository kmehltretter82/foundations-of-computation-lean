import FoC.Computability.Compiler.UniversalAndRanges.Basic

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

def CodePrefixDecodedBoundedSimulatorSemanticMachineSpec
    (simulator : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput simulator tokens <->
      exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        tokens = CodePrefixRecognizerStageCode encoded stage ∧
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input)

def CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction : Prop :=
  exists state : Type,
  exists simulator : TuringMachine MachineCodeSymbol state,
    CodePrefixDecodedBoundedSimulatorSemanticMachineSpec simulator

def CodePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction :
    Prop :=
  forall {stageState descriptionState : Type}
    (stageDecoder : TuringMachine MachineCodeSymbol stageState)
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState),
    (forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput stageDecoder tokens <->
        exists stage : Nat,
        exists encoded : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode encoded stage) ->
    (forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput descriptionDecoder encoded <->
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input)) ->
      CodePrefixDecodedBoundedSimulatorCodeMachineConstruction

def CodePrefixDecodedBoundedSimulatorStageDecoderConstruction : Prop :=
  exists state : Type,
  exists decoder : TuringMachine MachineCodeSymbol state,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput decoder tokens <->
        exists stage : Nat,
        exists encoded : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode encoded stage

def CodePrefixDecodedBoundedSimulatorDescriptionDecoderConstruction :
    Prop :=
  exists state : Type,
  exists decoder : TuringMachine MachineCodeSymbol state,
    forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput decoder encoded <->
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input)

theorem codePrefixDecodedBoundedSimulatorCodeMachineConstruction_of_components
    (hstage : CodePrefixDecodedBoundedSimulatorStageDecoderConstruction)
    (hdescription :
      CodePrefixDecodedBoundedSimulatorDescriptionDecoderConstruction)
    (hsequence :
      CodePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction) :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  rcases hstage with ⟨stageState, stageDecoder, hstage⟩
  rcases hdescription with
    ⟨descriptionState, descriptionDecoder, hdescription⟩
  exact
    hsequence stageDecoder descriptionDecoder hstage hdescription

theorem codePrefixDecodedBoundedSimulatorCodeMachineConstruction_of_semanticMachine
    (hsemantic :
      CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction) :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  rcases hsemantic with ⟨state, simulator, hsimulator⟩
  refine ⟨state, simulator, ?_⟩
  intro tokens
  rw [hsimulator tokens]
  constructor
  · intro h
    exact
      (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
        tokens ([] : Word MachineCodeSymbol)).mpr
        ⟨rfl, h⟩
  · intro h
    exact
      ((codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
        tokens ([] : Word MachineCodeSymbol)).mp h).right

theorem codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_of_codeMachine
    (hcode : CodePrefixDecodedBoundedSimulatorCodeMachineConstruction) :
    CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction := by
  rcases hcode with ⟨state, simulator, hsimulator⟩
  refine ⟨state, simulator, ?_⟩
  intro tokens
  rw [hsimulator tokens]
  constructor
  · intro h
    rcases
        (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
          tokens ([] : Word MachineCodeSymbol)).mp h with
      ⟨_hout, stage, encoded, D, input, htokens, hdecode, hhalts⟩
    exact ⟨stage, encoded, D, input, htokens, hdecode, hhalts⟩
  · intro h
    rcases h with
      ⟨stage, encoded, D, input, htokens, hdecode, hhalts⟩
    exact
      (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
        tokens ([] : Word MachineCodeSymbol)).mpr
        ⟨rfl, stage, encoded, D, input, htokens, hdecode, hhalts⟩

/-!
**Decoded simulator core.**  This is the real finite-machine leaf for the
uniform bounded simulator over encoded descriptions.  The decoder parameters
below are sequencing inputs; the core machine itself must parse a stage code,
decode one description prefix, simulate the decoded machine for the stage
bound, and halt exactly on hits.
-/

theorem codePrefixDecodedBoundedSimulatorStageDecoderConstruction_core :
    CodePrefixDecodedBoundedSimulatorStageDecoderConstruction := by
  sorry

theorem codePrefixDecodedBoundedSimulatorDescriptionDecoderConstruction_core :
    CodePrefixDecodedBoundedSimulatorDescriptionDecoderConstruction := by
  sorry

theorem codePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction_core :
    CodePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction := by
  sorry

theorem codePrefixDecodedBoundedSimulatorCodeMachineConstruction_core :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  exact
    codePrefixDecodedBoundedSimulatorCodeMachineConstruction_of_components
      codePrefixDecodedBoundedSimulatorStageDecoderConstruction_core
      codePrefixDecodedBoundedSimulatorDescriptionDecoderConstruction_core
      codePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction_core

theorem codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_core :
    CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction :=
  codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_of_codeMachine
    codePrefixDecodedBoundedSimulatorCodeMachineConstruction_core

end Computability
end FoC
