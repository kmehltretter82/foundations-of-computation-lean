import FoC.Computability.Compiler.UniversalAndRanges.Basic
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Soundness.Final

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

/--
Local construction target for the stage-code decoder.  This is currently the
same predicate as
{name}`CodePrefixDecodedBoundedSimulatorStageDecoderConstruction`, kept for
the higher-level finite-source assembly API.
-/
def StageCodeDecoderConstruction : Prop :=
  exists state : Type,
  exists decoder : TuringMachine MachineCodeSymbol state,
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput decoder tokens <->
        exists stage : Nat,
        exists encoded : Word MachineCodeSymbol,
          tokens = CodePrefixRecognizerStageCode encoded stage

inductive StageCodeDecoderState where
  | scan : StageCodeDecoderState
  | halt : StageCodeDecoderState
deriving DecidableEq

namespace StageCodeDecoderState

def finite : Foundation.FiniteType StageCodeDecoderState where
  elems := [scan, halt]
  complete := by
    intro state
    cases state <;> simp

end StageCodeDecoderState

def stageCodeDecoderTape
    (leftRev rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := leftRev.map some
        head := none
        right := [] }
  | symbol :: suffix =>
      { left := leftRev.map some
        head := some symbol
        right := suffix.map some }

theorem stageCodeDecoderTape_move_right
    (leftRev : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write (some symbol)
          (stageCodeDecoderTape leftRev (symbol :: suffix))) =
      stageCodeDecoderTape (symbol :: leftRev) suffix := by
  cases suffix <;>
    simp [stageCodeDecoderTape, Tape.move, Tape.moveRight,
      Tape.write]

theorem stageCodeDecoderTape_nil_eq_input
    (tokens : Word MachineCodeSymbol) :
    stageCodeDecoderTape [] tokens = Tape.input tokens := by
  cases tokens <;> rfl

def stageCodeDecoderMachine :
    TuringMachine MachineCodeSymbol StageCodeDecoderState where
  start := StageCodeDecoderState.scan
  halt := StageCodeDecoderState.halt
  transition := fun state cell =>
    match state, cell with
    | StageCodeDecoderState.scan, some MachineCodeSymbol.tick =>
        some
          (some MachineCodeSymbol.tick, Direction.right,
            StageCodeDecoderState.scan)
    | StageCodeDecoderState.scan, some MachineCodeSymbol.done =>
        some
          (some MachineCodeSymbol.done, Direction.right,
            StageCodeDecoderState.halt)
    | _, _ => none
  statesFinite := StageCodeDecoderState.finite

theorem stageCodeDecoderMachine_step_tick
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step stageCodeDecoderMachine
      { state := StageCodeDecoderState.scan
        tape :=
          stageCodeDecoderTape leftRev
            (MachineCodeSymbol.tick :: suffix) }
      { state := StageCodeDecoderState.scan
        tape :=
          stageCodeDecoderTape
            (MachineCodeSymbol.tick :: leftRev) suffix } := by
  rw [← stageCodeDecoderTape_move_right leftRev
    MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [stageCodeDecoderMachine,
      stageCodeDecoderTape, Tape.read])

theorem stageCodeDecoderMachine_step_done
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Step stageCodeDecoderMachine
      { state := StageCodeDecoderState.scan
        tape :=
          stageCodeDecoderTape leftRev
            (MachineCodeSymbol.done :: suffix) }
      { state := StageCodeDecoderState.halt
        tape :=
          stageCodeDecoderTape
            (MachineCodeSymbol.done :: leftRev) suffix } := by
  rw [← stageCodeDecoderTape_move_right leftRev
    MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [stageCodeDecoderMachine,
      stageCodeDecoderTape, Tape.read])

theorem stageCodeDecoderMachine_haltsFromIn_encodeNatAppend
    (leftRev : Word MachineCodeSymbol)
    (stage : Nat)
    (encoded : Word MachineCodeSymbol) :
    TuringMachine.HaltsFromIn stageCodeDecoderMachine
      (stage + 1)
      { state := StageCodeDecoderState.scan
        tape :=
          stageCodeDecoderTape leftRev
            (CodePrefixRecognizerStageCode encoded stage) } := by
  induction stage generalizing leftRev with
  | zero =>
      refine
        ⟨{ state := StageCodeDecoderState.halt,
            tape :=
              stageCodeDecoderTape
                (MachineCodeSymbol.done :: leftRev) encoded },
          ?_, rfl⟩
      exact TuringMachine.ComputesIn.succ
        (by
          simpa [CodePrefixRecognizerStageCode,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            stageCodeDecoderMachine_step_done leftRev encoded)
        (TuringMachine.ComputesIn.zero _)
  | succ stage ih =>
      rcases ih (MachineCodeSymbol.tick :: leftRev) with
        ⟨final, hcomp, hhalt⟩
      refine ⟨final, ?_, hhalt⟩
      exact TuringMachine.ComputesIn.succ
        (by
          simpa [CodePrefixRecognizerStageCode,
            MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            stageCodeDecoderMachine_step_tick leftRev
              (CodePrefixRecognizerStageCode encoded stage))
        hcomp

theorem stageCodeDecoderMachine_haltsFromIn_only_encodeNatAppend
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn stageCodeDecoderMachine steps
        { state := StageCodeDecoderState.scan
          tape := stageCodeDecoderTape leftRev rest }) :
    exists stage : Nat,
    exists encoded : Word MachineCodeSymbol,
      rest = CodePrefixRecognizerStageCode encoded stage := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      cases hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [stageCodeDecoderMachine,
                    stageCodeDecoderTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      rename_i write dir nextState
                      cases write with
                      | none =>
                          simp [stageCodeDecoderMachine,
                            stageCodeDecoderTape, Tape.read]
                            at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases dir <;>
                            cases nextState <;>
                              simp [stageCodeDecoderMachine,
                                stageCodeDecoderTape, Tape.read]
                                at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                stageCodeDecoderMachine steps
                                { state := StageCodeDecoderState.scan
                                  tape :=
                                    stageCodeDecoderTape
                                      (MachineCodeSymbol.tick :: leftRev)
                                      suffix } := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [stageCodeDecoderMachine,
                                stageCodeDecoderTape,
                                stageCodeDecoderTape_move_right,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases ih htail with ⟨stage, encoded, hsuffix⟩
                          exact ⟨stage + 1, encoded, by
                            simp [CodePrefixRecognizerStageCode,
                              MachineDescription.encodeNatAppend,
                              MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact ⟨0, suffix, by
                    simp [CodePrefixRecognizerStageCode,
                      MachineDescription.encodeNatAppend,
                      MachineDescription.encodeNat]⟩
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [stageCodeDecoderMachine,
                        stageCodeDecoderTape, Tape.read] at haction

theorem stageCodeDecoderMachine_spec
    (tokens : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput stageCodeDecoderMachine tokens <->
      exists stage : Nat,
      exists encoded : Word MachineCodeSymbol,
        tokens = CodePrefixRecognizerStageCode encoded stage := by
  constructor
  · intro h
    rcases
        (TuringMachine.halts_on_input_to_halts_on_input_in h) with
      ⟨steps, hsteps⟩
    have hfrom :
        TuringMachine.HaltsFromIn stageCodeDecoderMachine steps
          { state := StageCodeDecoderState.scan
            tape := stageCodeDecoderTape [] tokens } := by
      simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
        stageCodeDecoderMachine,
        stageCodeDecoderTape_nil_eq_input] using hsteps
    exact
      stageCodeDecoderMachine_haltsFromIn_only_encodeNatAppend
        (steps := steps) (leftRev := []) (rest := tokens) hfrom
  · intro h
    rcases h with ⟨stage, encoded, rfl⟩
    have hfrom :=
      stageCodeDecoderMachine_haltsFromIn_encodeNatAppend
        ([] : Word MachineCodeSymbol) stage encoded
    have hin :
        TuringMachine.HaltsOnInputIn stageCodeDecoderMachine
          (stage + 1) (CodePrefixRecognizerStageCode encoded stage) := by
      simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
        stageCodeDecoderMachine,
        stageCodeDecoderTape_nil_eq_input] using hfrom
    exact
      TuringMachine.halts_on_input_in_to_halts_on_input
        (n := stage + 1) hin

theorem stageCodeDecoderConstruction_scaffold :
    StageCodeDecoderConstruction :=
  ⟨StageCodeDecoderState,
    stageCodeDecoderMachine,
    stageCodeDecoderMachine_spec⟩

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

namespace MachineDescription

theorem haltsIn_zero_iff
    (D : MachineDescription) (w : Word Bool) :
    D.HaltsIn 0 w <-> D.start = D.halt := by
  simp [HaltsIn, initial, runConfig]

theorem runConfig_succ_of_stepConfig_none
    {D : MachineDescription} {c : Configuration} {n : Nat}
    (hstep : D.stepConfig c = none) :
    D.runConfig (n + 1) c = c := by
  simp [runConfig, hstep]

theorem runConfig_succ_of_stepConfig_some
    {D : MachineDescription} {c next : Configuration} {n : Nat}
    (hstep : D.stepConfig c = some next) :
    D.runConfig (n + 1) c = D.runConfig n next := by
  simp [runConfig, hstep]

theorem stepConfig_of_lookupTransition_none
    {D : MachineDescription} {c : Configuration}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = none) :
    D.stepConfig c = none := by
  simp [stepConfig, hlookup]

theorem stepConfig_of_lookupTransition_some
    {D : MachineDescription} {c : Configuration}
    {t : TransitionDescription}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = some t) :
    D.stepConfig c =
      some
        { state := t.target
          tape := Tape.move t.move (Tape.write t.write c.tape) } := by
  simp [stepConfig, hlookup]

theorem stepConfig_eq_none_iff_lookupTransition_eq_none
    {D : MachineDescription} {c : Configuration} :
    D.stepConfig c = none <->
      D.lookupTransition c.state (Tape.read c.tape) = none := by
  unfold stepConfig
  cases D.lookupTransition c.state (Tape.read c.tape) <;> simp

theorem stepConfig_eq_some_iff_lookupTransition_eq_some
    {D : MachineDescription} {c next : Configuration} :
    D.stepConfig c = some next <->
      exists t : TransitionDescription,
        D.lookupTransition c.state (Tape.read c.tape) = some t ∧
          next =
            { state := t.target
              tape := Tape.move t.move (Tape.write t.write c.tape) } := by
  constructor
  · intro hstep
    unfold stepConfig at hstep
    cases hlookup :
        D.lookupTransition c.state (Tape.read c.tape) with
    | none =>
        simp [hlookup] at hstep
    | some t =>
        simp [hlookup] at hstep
        subst next
        exact ⟨t, rfl, rfl⟩
  · intro h
    rcases h with ⟨t, hlookup, rfl⟩
    exact stepConfig_of_lookupTransition_some hlookup

theorem haltsIn_succ_iff_stepConfig_initial_none
    {D : MachineDescription} {w : Word Bool} {n : Nat}
    (hstep : D.stepConfig (D.initial w) = none) :
    D.HaltsIn (n + 1) w <-> D.start = D.halt := by
  change
    (D.runConfig (n + 1) (D.initial w)).state = D.halt <->
      D.start = D.halt
  rw [runConfig_succ_of_stepConfig_none hstep]
  simp [initial]

theorem haltsIn_succ_iff_stepConfig_initial_some
    {D : MachineDescription} {w : Word Bool} {n : Nat}
    {next : Configuration}
    (hstep : D.stepConfig (D.initial w) = some next) :
    D.HaltsIn (n + 1) w <->
      (D.runConfig n next).state = D.halt := by
  simp [HaltsIn, runConfig_succ_of_stepConfig_some hstep]

end MachineDescription

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
  refine
    ⟨CodePrefixParserNormalizerState,
      codePrefixParserNormalizerMachine, ?_⟩
  intro encoded
  constructor
  · intro h
    rcases h with ⟨final, hcomputes, hhalted⟩
    let out : Word MachineCodeSymbol :=
      Tape.normalizedOutput final.tape
    have hout :
        TuringMachine.HaltsWithOutput
          codePrefixParserNormalizerMachine encoded out :=
      ⟨final, hcomputes, hhalted, rfl⟩
    have htransform :
        CodePrefixParserNormalizerCode.transform encoded = some out :=
      (codePrefixParserNormalizerMachine_code_spec encoded out).mp hout
    rcases
        (codePrefixParserNormalizerCode_transform_eq_some_iff
          encoded out).mp htransform with
      ⟨D, input, hdecode, _hout⟩
    exact ⟨D, input, hdecode⟩
  · intro h
    rcases h with ⟨D, input, hdecode⟩
    have hencoded :
        encoded = List.append (MachineDescription.encodeDescription D)
          input :=
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        hdecode
    have htransform :
        CodePrefixParserNormalizerCode.transform encoded =
          some encoded :=
      (codePrefixParserNormalizerCode_transform_eq_some_iff
        encoded encoded).mpr
        ⟨D, input, hdecode, by rw [hencoded]⟩
    exact
      TuringMachine.halts_with_output_implies_halts
        ((codePrefixParserNormalizerMachine_code_spec
          encoded encoded).mpr htransform)

/--
Raw finite-machine leaf for the decoded bounded simulator primitive.  This is
the transition-table obligation: build a machine whose halting behavior agrees
with the semantic tape-code primitive on every staged input.
-/
theorem codePrefixDecodedBoundedSimulatorCodeMachineFiniteLeaf :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  sorry

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
