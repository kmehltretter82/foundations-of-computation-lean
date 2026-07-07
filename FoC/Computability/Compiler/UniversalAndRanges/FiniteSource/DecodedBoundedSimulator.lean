import FoC.Computability.Compiler.UniversalAndRanges.Basic
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.DescriptionPrefixDecoder
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.DecodedBoundedSimulator.NormRun
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageCodeDecoder

set_option doc.verso true

/-!
# Decoded Bounded Simulator

This module separates the finite-source decoded simulator into a stage-code
decoder, a description-prefix decoder, and a sequencing obligation that runs
the decoded machine for the requested bound.
-/

namespace FoC
namespace Computability

open Languages

/-- Semantic spec for a simulator that recognizes accepted stage-coded inputs. -/
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

theorem codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff
    (tokens : Word MachineCodeSymbol) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens =
        some ([] : Word MachineCodeSymbol) <->
      exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        tokens = CodePrefixRecognizerStageCode encoded stage ∧
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input) := by
  simpa using
    (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_iff
      tokens ([] : Word MachineCodeSymbol))

theorem codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff_decodeNat
    (tokens : Word MachineCodeSymbol) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens =
        some ([] : Word MachineCodeSymbol) <->
      exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens = some (stage, encoded) ∧
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input) := by
  constructor
  · intro h
    rcases
        (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff
          tokens).mp h with
      ⟨stage, encoded, D, input, htokens, hdecode, hhalts⟩
    subst tokens
    exact
      ⟨stage, encoded, D, input,
        codePrefixRecognizerStageCode_decodeNat encoded stage,
        hdecode, hhalts⟩
  · intro h
    rcases h with
      ⟨stage, encoded, D, input, hstage, hdecode, hhalts⟩
    exact
      (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff
        tokens).mpr
        ⟨stage, encoded, D, input,
          codePrefixRecognizerStageCode_eq_of_decodeNat hstage,
          hdecode, hhalts⟩

theorem codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff_decodeNat_encodeDescription
    (tokens : Word MachineCodeSymbol) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens =
        some ([] : Word MachineCodeSymbol) <->
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
    rcases
        (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff_decodeNat
          tokens).mp h with
      ⟨stage, encoded, D, input, hstage, hdecode, hhalts⟩
    have hencoded :
        encoded = List.append (MachineDescription.encodeDescription D)
          input :=
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        hdecode
    exact
      ⟨stage, D, input, by simpa [hencoded] using hstage, hhalts⟩
  · intro h
    rcases h with ⟨stage, D, input, hstage, hhalts⟩
    exact
      (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff_decodeNat
        tokens).mpr
        ⟨stage,
          List.append (MachineDescription.encodeDescription D) input,
          D, input, hstage,
          MachineDescription.decodeDescriptionPrefix_encodeDescription_append
            D input,
          hhalts⟩

theorem codePrefixDecodedBoundedSimulatorCode_transform_eq_none_of_decodeNat_none
    {tokens : Word MachineCodeSymbol}
    (hstage : MachineDescription.decodeNat tokens = none) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens = none := by
  classical
  simp [CodePrefixDecodedBoundedSimulatorCode, hstage]

theorem codePrefixDecodedBoundedSimulatorCode_transform_eq_none_of_decodeDescriptionPrefix_none
    {tokens encoded : Word MachineCodeSymbol} {stage : Nat}
    (hstage :
      MachineDescription.decodeNat tokens = some (stage, encoded))
    (hdecode :
      MachineDescription.decodeDescriptionPrefix encoded = none) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens = none := by
  classical
  simp [CodePrefixDecodedBoundedSimulatorCode, hstage, hdecode]

theorem codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff_of_decodeNat_decodeDescriptionPrefix
    {tokens encoded input : Word MachineCodeSymbol}
    {stage : Nat} {D : MachineDescription}
    (hstage :
      MachineDescription.decodeNat tokens = some (stage, encoded))
    (hdecode :
      MachineDescription.decodeDescriptionPrefix encoded =
        some (D, input)) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens =
        some ([] : Word MachineCodeSymbol) <->
      D.HaltsIn stage
        (MachineDescription.encodeCodeWordAsInput input) := by
  classical
  by_cases hhalts :
      D.HaltsIn stage
        (MachineDescription.encodeCodeWordAsInput input)
  · constructor
    · intro _h
      exact hhalts
    · intro _h
      simp [CodePrefixDecodedBoundedSimulatorCode,
        hstage, hdecode, hhalts]
      rfl
  · constructor
    · intro h
      have hfalse : False := by
        simp [CodePrefixDecodedBoundedSimulatorCode,
          hstage, hdecode, hhalts] at h
      exact False.elim hfalse
    · intro h
      exact False.elim (hhalts h)

theorem codePrefixDecodedBoundedSimulatorCode_transform_eq_none_of_decodeNat_decodeDescriptionPrefix_not_halts
    {tokens encoded input : Word MachineCodeSymbol}
    {stage : Nat} {D : MachineDescription}
    (hstage :
      MachineDescription.decodeNat tokens = some (stage, encoded))
    (hdecode :
      MachineDescription.decodeDescriptionPrefix encoded =
        some (D, input))
    (hhalts :
      ¬ D.HaltsIn stage
        (MachineDescription.encodeCodeWordAsInput input)) :
    CodePrefixDecodedBoundedSimulatorCode.transform tokens = none := by
  classical
  simp [CodePrefixDecodedBoundedSimulatorCode, hstage, hdecode, hhalts]

/--
Canonical source tape for the normalized decoded simulator leaf.  The finite
table should start from this generated stage-code input and then decode the
machine-description prefix in the payload.
-/
theorem codePrefixDecodedBoundedSimulatorNormalizedInputTape_cells
    (D : MachineDescription) (input : Word MachineCodeSymbol)
    (stage : Nat) :
    Tape.cells
        (Tape.input
          (CodePrefixRecognizerStageCode
            (List.append (MachineDescription.encodeDescription D) input)
            stage)) =
      match stage with
      | 0 =>
          some MachineCodeSymbol.done ::
            (List.append
              (MachineDescription.encodeDescription D) input).map some
      | stage + 1 =>
          some MachineCodeSymbol.tick ::
            (CodePrefixRecognizerStageCode
              (List.append (MachineDescription.encodeDescription D) input)
              stage).map some := by
  simpa using
    codePrefixRecognizerStageCode_input_cells
      (List.append (MachineDescription.encodeDescription D) input)
      stage

/--
Loading the normalized decoded-simulator input as a tape preserves exactly the
canonical stage-code word.
-/
theorem codePrefixDecodedBoundedSimulatorNormalizedInputTape_normalizedOutput
    (D : MachineDescription) (input : Word MachineCodeSymbol)
    (stage : Nat) :
    Tape.normalizedOutput
        (Tape.input
          (CodePrefixRecognizerStageCode
            (List.append (MachineDescription.encodeDescription D) input)
            stage)) =
      CodePrefixRecognizerStageCode
        (List.append (MachineDescription.encodeDescription D) input)
        stage := by
  simpa using
    codePrefixRecognizerStageCode_input_normalizedOutput
      (List.append (MachineDescription.encodeDescription D) input)
      stage

/--
The normalized decoded-simulator input decodes to the supplied stage and the
canonical encoded-description payload.
-/
theorem codePrefixDecodedBoundedSimulatorNormalizedInput_decodeNat
    (D : MachineDescription) (input : Word MachineCodeSymbol)
    (stage : Nat) :
    MachineDescription.decodeNat
        (CodePrefixRecognizerStageCode
          (List.append (MachineDescription.encodeDescription D) input)
          stage) =
      some (stage,
        List.append (MachineDescription.encodeDescription D) input) := by
  exact
    codePrefixRecognizerStageCode_decodeNat
      (List.append (MachineDescription.encodeDescription D) input)
      stage

/--
On canonical normalized inputs, the decoded-bounded-simulator code accepts
exactly when the encoded description halts at the requested stage.
-/
theorem codePrefixDecodedBoundedSimulatorCode_transform_normalizedInput_eq_some_nil_iff
    (D : MachineDescription) (input : Word MachineCodeSymbol)
    (stage : Nat) :
    CodePrefixDecodedBoundedSimulatorCode.transform
        (CodePrefixRecognizerStageCode
          (List.append (MachineDescription.encodeDescription D) input)
          stage) =
        some ([] : Word MachineCodeSymbol) <->
      D.HaltsIn stage
        (MachineDescription.encodeCodeWordAsInput input) := by
  exact
    codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff_of_decodeNat_decodeDescriptionPrefix
      (codePrefixDecodedBoundedSimulatorNormalizedInput_decodeNat
        D input stage)
      (MachineDescription.decodeDescriptionPrefix_encodeDescription_append
        D input)

def CodePrefixDecodedBoundedSimulatorParsedCodeMachineSpec
    (simulator : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput simulator tokens <->
      exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens = some (stage, encoded) ∧
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input) ∧
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input)

def CodePrefixDecodedBoundedSimulatorParsedCodeMachineConstruction : Prop :=
  exists state : Type,
  exists simulator : TuringMachine MachineCodeSymbol state,
    CodePrefixDecodedBoundedSimulatorParsedCodeMachineSpec simulator

def CodePrefixDecodedBoundedSimulatorNormalizedCodeMachineSpec
    (simulator : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput simulator tokens <->
      exists stage : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
            some (stage,
              List.append (MachineDescription.encodeDescription D) input) ∧
          D.HaltsIn stage
            (MachineDescription.encodeCodeWordAsInput input)

def CodePrefixDecodedBoundedSimulatorNormalizedCodeMachineConstruction :
    Prop :=
  exists state : Type,
  exists simulator : TuringMachine MachineCodeSymbol state,
    CodePrefixDecodedBoundedSimulatorNormalizedCodeMachineSpec simulator

theorem codePrefixDecodedBoundedSimulatorCodeMachineSpec_of_parsedCodeMachineSpec
    {simulator : TuringMachine MachineCodeSymbol state}
    (hsimulator :
      CodePrefixDecodedBoundedSimulatorParsedCodeMachineSpec simulator) :
    CodePrefixDecodedBoundedSimulatorCodeMachineSpec simulator := by
  intro tokens
  exact Iff.trans (hsimulator tokens)
    (Iff.symm
      (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff_decodeNat
        tokens))

theorem codePrefixDecodedBoundedSimulatorParsedCodeMachineSpec_of_codeMachineSpec
    {simulator : TuringMachine MachineCodeSymbol state}
    (hsimulator :
      CodePrefixDecodedBoundedSimulatorCodeMachineSpec simulator) :
    CodePrefixDecodedBoundedSimulatorParsedCodeMachineSpec simulator := by
  intro tokens
  exact Iff.trans (hsimulator tokens)
    (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff_decodeNat
      tokens)

theorem codePrefixDecodedBoundedSimulatorNormalizedCodeMachineSpec_of_codeMachineSpec
    {simulator : TuringMachine MachineCodeSymbol state}
    (hsimulator :
      CodePrefixDecodedBoundedSimulatorCodeMachineSpec simulator) :
    CodePrefixDecodedBoundedSimulatorNormalizedCodeMachineSpec simulator := by
  intro tokens
  exact Iff.trans (hsimulator tokens)
    (decodedBoundedSimulatorNormalizedCode_transform_eq_some_nil_iff
      tokens)

theorem codePrefixDecodedBoundedSimulatorCodeMachineSpec_of_normalizedCodeMachineSpec
    {simulator : TuringMachine MachineCodeSymbol state}
    (hsimulator :
      CodePrefixDecodedBoundedSimulatorNormalizedCodeMachineSpec simulator) :
    CodePrefixDecodedBoundedSimulatorCodeMachineSpec simulator := by
  intro tokens
  exact Iff.trans (hsimulator tokens)
    (Iff.symm
      (decodedBoundedSimulatorNormalizedCode_transform_eq_some_nil_iff
        tokens))

theorem codePrefixDecodedBoundedSimulatorParsedCodeMachineSpec_of_normalizedCodeMachineSpec
    {simulator : TuringMachine MachineCodeSymbol state}
    (hsimulator :
      CodePrefixDecodedBoundedSimulatorNormalizedCodeMachineSpec simulator) :
    CodePrefixDecodedBoundedSimulatorParsedCodeMachineSpec simulator := by
  exact
    codePrefixDecodedBoundedSimulatorParsedCodeMachineSpec_of_codeMachineSpec
      (codePrefixDecodedBoundedSimulatorCodeMachineSpec_of_normalizedCodeMachineSpec
        hsimulator)

theorem codePrefixDecodedBoundedSimulatorNormalizedCodeMachineSpec_of_parsedCodeMachineSpec
    {simulator : TuringMachine MachineCodeSymbol state}
    (hsimulator :
      CodePrefixDecodedBoundedSimulatorParsedCodeMachineSpec simulator) :
    CodePrefixDecodedBoundedSimulatorNormalizedCodeMachineSpec simulator := by
  exact
    codePrefixDecodedBoundedSimulatorNormalizedCodeMachineSpec_of_codeMachineSpec
      (codePrefixDecodedBoundedSimulatorCodeMachineSpec_of_parsedCodeMachineSpec
        hsimulator)

theorem codePrefixDecodedBoundedSimulatorCodeMachineConstruction_of_parsed
    (hparsed :
      CodePrefixDecodedBoundedSimulatorParsedCodeMachineConstruction) :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  rcases hparsed with ⟨state, simulator, hsimulator⟩
  exact
    ⟨state, simulator,
      codePrefixDecodedBoundedSimulatorCodeMachineSpec_of_parsedCodeMachineSpec
        hsimulator⟩

theorem codePrefixDecodedBoundedSimulatorParsedCodeMachineConstruction_of_codeMachine
    (hcode : CodePrefixDecodedBoundedSimulatorCodeMachineConstruction) :
    CodePrefixDecodedBoundedSimulatorParsedCodeMachineConstruction := by
  rcases hcode with ⟨state, simulator, hsimulator⟩
  exact
    ⟨state, simulator,
      codePrefixDecodedBoundedSimulatorParsedCodeMachineSpec_of_codeMachineSpec
        hsimulator⟩

theorem codePrefixDecodedBoundedSimulatorParsedCodeMachineConstruction_of_normalized
    (hnormalized :
      CodePrefixDecodedBoundedSimulatorNormalizedCodeMachineConstruction) :
    CodePrefixDecodedBoundedSimulatorParsedCodeMachineConstruction := by
  rcases hnormalized with ⟨state, simulator, hsimulator⟩
  exact
    ⟨state, simulator,
      codePrefixDecodedBoundedSimulatorParsedCodeMachineSpec_of_normalizedCodeMachineSpec
        hsimulator⟩

theorem codePrefixDecodedBoundedSimulatorNormalizedCodeMachineConstruction_of_parsed
    (hparsed :
      CodePrefixDecodedBoundedSimulatorParsedCodeMachineConstruction) :
    CodePrefixDecodedBoundedSimulatorNormalizedCodeMachineConstruction := by
  rcases hparsed with ⟨state, simulator, hsimulator⟩
  exact
    ⟨state, simulator,
      codePrefixDecodedBoundedSimulatorNormalizedCodeMachineSpec_of_parsedCodeMachineSpec
        hsimulator⟩

theorem codePrefixDecodedBoundedSimulatorCodeMachineSpec_iff_semanticMachineSpec
    (simulator : TuringMachine MachineCodeSymbol state) :
    CodePrefixDecodedBoundedSimulatorCodeMachineSpec simulator <->
      CodePrefixDecodedBoundedSimulatorSemanticMachineSpec simulator := by
  constructor
  · intro hsimulator tokens
    exact Iff.trans (hsimulator tokens)
      (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff
        tokens)
  · intro hsimulator tokens
    exact Iff.trans (hsimulator tokens)
      (Iff.symm
        (codePrefixDecodedBoundedSimulatorCode_transform_eq_some_nil_iff
          tokens))

/-!
**Decoded simulator core.**  This is the real finite-machine leaf for the
uniform bounded simulator over encoded descriptions.  The decoder parameters
below are sequencing inputs; the core machine itself must parse a stage code,
decode one description prefix, simulate the decoded machine for the stage
bound, and halt exactly on hits.
-/

theorem codePrefixDecodedBoundedSimulatorStageDecoderConstruction_core :
    CodePrefixDecodedBoundedSimulatorStageDecoderConstruction := by
  exact stageCodeDecoderConstruction_scaffold

/-- Description-prefix decoder supplied by the finite-source normalizer. -/
theorem codePrefixDecodedBoundedSimulatorDescriptionDecoderConstruction_core :
    CodePrefixDecodedBoundedSimulatorDescriptionDecoderConstruction := by
  exact codePrefixDescriptionPrefixDecoderConstruction_scaffold

/--
Normalized finite-machine leaf for the decoded bounded simulator primitive.
This is the operational transition-table obligation: parse the unary stage
prefix, parse a canonical encoded description prefix from the payload, and
accept exactly when the decoded table halts at that exact stage.
-/
theorem codePrefixDecodedBoundedSimulatorNormalizedCodeMachineFiniteLeaf :
    CodePrefixDecodedBoundedSimulatorNormalizedCodeMachineConstruction := by
  exact decodedBoundedSimulatorNormalizedRunnerConstruction

/--
Parsed finite-machine leaf for the decoded bounded simulator primitive.  The
decoder-prefix contract is now an adapter around the normalized encoded-shape
obligation.
-/
theorem codePrefixDecodedBoundedSimulatorParsedCodeMachineFiniteLeaf :
    CodePrefixDecodedBoundedSimulatorParsedCodeMachineConstruction := by
  exact
    codePrefixDecodedBoundedSimulatorParsedCodeMachineConstruction_of_normalized
      codePrefixDecodedBoundedSimulatorNormalizedCodeMachineFiniteLeaf

/--
Raw finite-machine leaf for the decoded bounded simulator primitive.  The
code-primitive contract is a thin adapter around the parsed operational leaf.
-/
theorem codePrefixDecodedBoundedSimulatorCodeMachineFiniteLeaf :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  exact
    codePrefixDecodedBoundedSimulatorCodeMachineConstruction_of_parsed
      codePrefixDecodedBoundedSimulatorParsedCodeMachineFiniteLeaf

/--
Semantic finite-machine leaf for the decoded bounded simulator primitive.  The
semantic contract is now only an adapter around the raw code-machine leaf above.
-/
theorem codePrefixDecodedBoundedSimulatorSemanticMachineFiniteLeaf :
    CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction := by
  exact
    codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_of_codeMachine
      codePrefixDecodedBoundedSimulatorCodeMachineFiniteLeaf

/--
Finite decoded-simulator construction after the stage-code and description
decoders have exposed their parser contracts.  The remaining transition-table
obligation is the semantic bounded simulator leaf above.
-/
theorem codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_of_decoders_finite
    {stageState descriptionState : Type}
    (stageDecoder : TuringMachine MachineCodeSymbol stageState)
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (_hstage :
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput stageDecoder tokens <->
          exists stage : Nat,
          exists encoded : Word MachineCodeSymbol,
            tokens = CodePrefixRecognizerStageCode encoded stage)
    (_hdescription :
      forall encoded : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput descriptionDecoder encoded <->
          exists D : MachineDescription,
          exists input : Word MachineCodeSymbol,
            MachineDescription.decodeDescriptionPrefix encoded =
              some (D, input)) :
    CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction := by
  exact codePrefixDecodedBoundedSimulatorSemanticMachineFiniteLeaf

/--
Adapter from the semantic decoded simulator leaf to the code-primitive
contract.
-/
theorem codePrefixDecodedBoundedSimulatorCodeMachineConstruction_core :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  exact codePrefixDecodedBoundedSimulatorCodeMachineFiniteLeaf

/--
Finite-machine leaf that sequences the stage decoder, description decoder, and
bounded simulation phase.
-/
theorem codePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction_core :
    CodePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction := by
  intro stageState descriptionState stageDecoder descriptionDecoder
    hstage hdescription
  exact codePrefixDecodedBoundedSimulatorCodeMachineFiniteLeaf

theorem codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_core :
    CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction :=
  codePrefixDecodedBoundedSimulatorSemanticMachineFiniteLeaf

end Computability
end FoC
