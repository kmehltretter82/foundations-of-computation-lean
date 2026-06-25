import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.DecodedBoundedSimulator
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.BranchSequencing

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

def CodePrefixParserNormalizerIdentityMachineSpec
    (normalizer : TuringMachine MachineCodeSymbol state) : Prop :=
  forall tokens out : Word MachineCodeSymbol,
    TuringMachine.HaltsWithOutput normalizer tokens out <->
      out = tokens ∧
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeDescriptionPrefix tokens =
            some (D, input)

def CodePrefixParserNormalizerIdentityMachineConstruction : Prop :=
  exists state : Type,
  exists normalizer : TuringMachine MachineCodeSymbol state,
    CodePrefixParserNormalizerIdentityMachineSpec normalizer

def CodePrefixParserNormalizerSequencingConstruction : Prop :=
  forall {headerState transitionState : Type}
    (header : TuringMachine MachineCodeSymbol headerState)
    (transitionParser : TuringMachine MachineCodeSymbol transitionState),
    (forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput header tokens <->
        exists stateCount start halt transitionCount : Nat,
        exists rest : Word MachineCodeSymbol,
          tokens =
            MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend stateCount
                (MachineDescription.encodeNatAppend start
                  (MachineDescription.encodeNatAppend halt
                    (MachineDescription.encodeNatAppend transitionCount
                      rest)))) ->
    (forall count : Nat,
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput transitionParser
            (MachineDescription.encodeNatAppend count tokens) <->
          exists parsed : List TransitionDescription,
          exists suffix : Word MachineCodeSymbol,
            MachineDescription.decodeTransitions count tokens =
              some (parsed, suffix)) ->
      CodePrefixParserNormalizerIdentityMachineConstruction

theorem turingMachine_haltsOnInput_iff_exists_haltsWithOutput
    (M : TuringMachine symbol state) (w : Word symbol) :
    TuringMachine.HaltsOnInput M w <->
      exists out : Word symbol,
        TuringMachine.HaltsWithOutput M w out := by
  constructor
  · intro h
    rcases h with ⟨final, hcomputes, hhalted⟩
    exact
      ⟨Tape.normalizedOutput final.tape,
        final, hcomputes, hhalted, rfl⟩
  · intro h
    rcases h with ⟨out, hout⟩
    exact TuringMachine.halts_with_output_implies_halts hout

theorem codePrefixParserNormalizerCodeMachineConstruction_of_identityMachine
    (hidentity : CodePrefixParserNormalizerIdentityMachineConstruction) :
    CodePrefixParserNormalizerCodeMachineConstruction := by
  rcases hidentity with ⟨state, normalizer, hnormalizer⟩
  refine ⟨state, normalizer, ?_⟩
  intro tokens out
  rw [hnormalizer tokens out]
  constructor
  · intro h
    rcases h with ⟨hout, D, input, hdecode⟩
    exact
      (codePrefixParserNormalizerCode_transform_eq_some_iff
        tokens out).mpr
        ⟨D, input, hdecode,
          by
            rw [hout]
            exact
              MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
                hdecode⟩
  · intro h
    rcases
        (codePrefixParserNormalizerCode_transform_eq_some_iff
          tokens out).mp h with
      ⟨D, input, hdecode, hout⟩
    have htokens :
        tokens = List.append (MachineDescription.encodeDescription D) input :=
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        hdecode
    exact ⟨by rw [htokens, hout], D, input, hdecode⟩



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

def CodePrefixStageDescriptionPrefixDecoderConstruction : Prop :=
  exists state : Type,
  exists decoder : TuringMachine MachineCodeSymbol state,
    forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput decoder encoded <->
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input)

theorem codePrefixStageDescriptionPrefixDecoderConstruction_of_normalizerIdentityMachine
    (hidentity : CodePrefixParserNormalizerIdentityMachineConstruction) :
    CodePrefixStageDescriptionPrefixDecoderConstruction := by
  rcases hidentity with ⟨state, normalizer, hnormalizer⟩
  refine ⟨state, normalizer, ?_⟩
  intro encoded
  rw [turingMachine_haltsOnInput_iff_exists_haltsWithOutput
    normalizer encoded]
  constructor
  · intro h
    rcases h with ⟨out, hout⟩
    rcases (hnormalizer encoded out).mp hout with
      ⟨_hout, D, input, hdecode⟩
    exact ⟨D, input, hdecode⟩
  · intro h
    rcases h with ⟨D, input, hdecode⟩
    exact
      ⟨encoded,
        (hnormalizer encoded encoded).mpr
          ⟨rfl, D, input, hdecode⟩⟩

/-!
**Prefix-runner proof frontier.**  The remaining universal-prefix placeholders
now separate finite parser machines from controller sequencing.  The
description-prefix decoder is no longer an independent leaf: it is derived from
the same {name}`CodePrefixParserNormalizerIdentityMachineConstruction` used by
the normalizer path.  The first sequencing scaffold is now backed by the
concrete {name}`codePrefixParserNormalizerMachine_code_spec`; the bounded
simulator leaf is the finite sequencing that connects the stage decoder, the
shared description decoder, and the pure
{name}`CodePrefixDecodedBoundedSimulatorCode` primitive.
-/

theorem codePrefixParserNormalizerSequencingConstruction_scaffold :
    CodePrefixParserNormalizerSequencingConstruction := by
  intro headerState transitionState header transitionParser
    hheader htransitions
  refine
    ⟨CodePrefixParserNormalizerState,
      codePrefixParserNormalizerMachine, ?_⟩
  intro tokens out
  rw [codePrefixParserNormalizerMachine_code_spec tokens out]
  constructor
  · intro h
    rcases
        (codePrefixParserNormalizerCode_transform_eq_some_iff
          tokens out).mp h with
      ⟨D, input, hdecode, hout⟩
    have htokens :
        tokens = List.append (MachineDescription.encodeDescription D) input :=
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        hdecode
    exact ⟨by rw [htokens, hout], D, input, hdecode⟩
  · intro h
    rcases h with ⟨hout, D, input, hdecode⟩
    exact
      (codePrefixParserNormalizerCode_transform_eq_some_iff
        tokens out).mpr
        ⟨D, input, hdecode,
          by
            have htokens :
                tokens =
                  List.append (MachineDescription.encodeDescription D)
                    input :=
              MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
                hdecode
            rw [hout, htokens]⟩

theorem headerFieldsParserConstruction_scaffold :
    HeaderFieldsParserConstruction := by
  refine
    ⟨HeaderFieldsParserState,
      headerFieldsParserMachine, ?_⟩
  intro tokens
  constructor
  · intro h
    rcases
        (TuringMachine.halts_on_input_to_halts_on_input_in h) with
      ⟨steps, hsteps⟩
    have hfrom :
        TuringMachine.HaltsFromIn
          headerFieldsParserMachine steps
          { state := HeaderFieldsParserState.needHeader
            tape :=
              headerFieldsParserTape [] tokens } := by
      simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
        headerFieldsParserMachine,
        headerFieldsParserTape_nil_eq_input] using hsteps
    exact
      headerFieldsParserMachine_haltsFromIn_only_header
        hfrom
  · intro h
    rcases h with
      ⟨stateCount, start, halt, transitionCount, rest, rfl⟩
    let suffixState :=
      MachineDescription.encodeNatAppend start
        (MachineDescription.encodeNatAppend halt
          (MachineDescription.encodeNatAppend transitionCount rest))
    let suffixStart :=
      MachineDescription.encodeNatAppend halt
        (MachineDescription.encodeNatAppend transitionCount rest)
    let suffixHalt :=
      MachineDescription.encodeNatAppend transitionCount rest
    let leftAfterHeader : Word MachineCodeSymbol :=
      [MachineCodeSymbol.header]
    let leftAfterState : Word MachineCodeSymbol :=
      List.append (MachineDescription.encodeNat stateCount).reverse
        leftAfterHeader
    let leftAfterStart : Word MachineCodeSymbol :=
      List.append (MachineDescription.encodeNat start).reverse
        leftAfterState
    let leftAfterHalt : Word MachineCodeSymbol :=
      List.append (MachineDescription.encodeNat halt).reverse
        leftAfterStart
    have hheader :
        TuringMachine.Step headerFieldsParserMachine
          { state := HeaderFieldsParserState.needHeader
            tape :=
              headerFieldsParserTape []
                (MachineCodeSymbol.header ::
                  MachineDescription.encodeNatAppend stateCount
                    suffixState) }
          { state := HeaderFieldsParserState.stateCount
            tape :=
              headerFieldsParserTape
                leftAfterHeader
                (MachineDescription.encodeNatAppend stateCount
                  suffixState) } := by
      simpa [leftAfterHeader] using
        headerFieldsParserMachine_step_header
          ([] : Word MachineCodeSymbol)
          (MachineDescription.encodeNatAppend stateCount suffixState)
    have hstateIn :
        TuringMachine.ComputesIn
          headerFieldsParserMachine
          (stateCount + 1)
          { state := HeaderFieldsParserState.stateCount
            tape :=
              headerFieldsParserTape
                leftAfterHeader
                (MachineDescription.encodeNatAppend stateCount
                  suffixState) }
          { state := HeaderFieldsParserState.startField
            tape :=
              headerFieldsParserTape
                leftAfterState suffixState } := by
      simpa [leftAfterState] using
        headerFieldsParserMachine_computesIn_nat
          headerFieldsParserMachine_step_tick_stateCount
          headerFieldsParserMachine_step_done_stateCount
          leftAfterHeader stateCount suffixState
    have hstartIn :
        TuringMachine.ComputesIn
          headerFieldsParserMachine
          (start + 1)
          { state := HeaderFieldsParserState.startField
            tape :=
              headerFieldsParserTape
                leftAfterState
                (MachineDescription.encodeNatAppend start suffixStart) }
          { state := HeaderFieldsParserState.haltField
            tape :=
              headerFieldsParserTape
                leftAfterStart suffixStart } := by
      simpa [leftAfterStart] using
        headerFieldsParserMachine_computesIn_nat
          headerFieldsParserMachine_step_tick_startField
          headerFieldsParserMachine_step_done_startField
          leftAfterState start suffixStart
    have hhaltIn :
        TuringMachine.ComputesIn
          headerFieldsParserMachine
          (halt + 1)
          { state := HeaderFieldsParserState.haltField
            tape :=
              headerFieldsParserTape
                leftAfterStart
                (MachineDescription.encodeNatAppend halt suffixHalt) }
          { state :=
              HeaderFieldsParserState.transitionCount
            tape :=
              headerFieldsParserTape
                leftAfterHalt suffixHalt } := by
      simpa [leftAfterHalt] using
        headerFieldsParserMachine_computesIn_nat
          headerFieldsParserMachine_step_tick_haltField
          headerFieldsParserMachine_step_done_haltField
          leftAfterStart halt suffixHalt
    have htransitionIn :
        TuringMachine.ComputesIn
          headerFieldsParserMachine
          (transitionCount + 1)
          { state :=
              HeaderFieldsParserState.transitionCount
            tape :=
              headerFieldsParserTape
                leftAfterHalt
                (MachineDescription.encodeNatAppend transitionCount rest) }
          { state := HeaderFieldsParserState.done
            tape :=
              headerFieldsParserTape
                (List.append
                  (MachineDescription.encodeNat transitionCount).reverse
                  leftAfterHalt)
                rest } := by
      exact
        headerFieldsParserMachine_computesIn_nat
          headerFieldsParserMachine_step_tick_transitionCount
          headerFieldsParserMachine_step_done_transitionCount
          leftAfterHalt transitionCount rest
    have hstate :
        TuringMachine.Computes headerFieldsParserMachine
          { state := HeaderFieldsParserState.stateCount
            tape :=
              headerFieldsParserTape
                leftAfterHeader
                (MachineDescription.encodeNatAppend stateCount
                  suffixState) }
          { state := HeaderFieldsParserState.startField
            tape :=
              headerFieldsParserTape
                leftAfterState suffixState } :=
      TuringMachine.computesIn_to_computes hstateIn
    have hstart :
        TuringMachine.Computes headerFieldsParserMachine
          { state := HeaderFieldsParserState.startField
            tape :=
              headerFieldsParserTape
                leftAfterState
                (MachineDescription.encodeNatAppend start suffixStart) }
          { state := HeaderFieldsParserState.haltField
            tape :=
              headerFieldsParserTape
                leftAfterStart suffixStart } :=
      TuringMachine.computesIn_to_computes hstartIn
    have hhalt :
        TuringMachine.Computes headerFieldsParserMachine
          { state := HeaderFieldsParserState.haltField
            tape :=
              headerFieldsParserTape
                leftAfterStart
                (MachineDescription.encodeNatAppend halt suffixHalt) }
          { state :=
              HeaderFieldsParserState.transitionCount
            tape :=
              headerFieldsParserTape
                leftAfterHalt suffixHalt } :=
      TuringMachine.computesIn_to_computes hhaltIn
    have htransition :
        TuringMachine.Computes headerFieldsParserMachine
          { state :=
              HeaderFieldsParserState.transitionCount
            tape :=
              headerFieldsParserTape
                leftAfterHalt
                (MachineDescription.encodeNatAppend transitionCount rest) }
          { state := HeaderFieldsParserState.done
            tape :=
              headerFieldsParserTape
                (List.append
                  (MachineDescription.encodeNat transitionCount).reverse
                  leftAfterHalt)
                rest } :=
      TuringMachine.computesIn_to_computes htransitionIn
    have hcompTail :
        TuringMachine.Computes headerFieldsParserMachine
          { state := HeaderFieldsParserState.stateCount
            tape :=
              headerFieldsParserTape
                leftAfterHeader
                (MachineDescription.encodeNatAppend stateCount
                  suffixState) }
          { state := HeaderFieldsParserState.done
            tape :=
              headerFieldsParserTape
                (List.append
                  (MachineDescription.encodeNat transitionCount).reverse
                  leftAfterHalt)
                rest } := by
      exact
        TuringMachine.computes_trans hstate
          (TuringMachine.computes_trans
            (by simpa [suffixState] using hstart)
            (TuringMachine.computes_trans
              (by simpa [suffixStart] using hhalt)
              (by simpa [suffixHalt] using htransition)))
    have hcomp :
        TuringMachine.Computes headerFieldsParserMachine
          { state := HeaderFieldsParserState.needHeader
            tape :=
              headerFieldsParserTape []
                (MachineCodeSymbol.header ::
                  MachineDescription.encodeNatAppend stateCount
                    suffixState) }
          { state := HeaderFieldsParserState.done
            tape :=
              headerFieldsParserTape
                (List.append
                  (MachineDescription.encodeNat transitionCount).reverse
                  leftAfterHalt)
                rest } :=
      TuringMachine.Computes.step hheader hcompTail
    have hhalts :
        TuringMachine.HaltsFrom
          headerFieldsParserMachine
          { state := HeaderFieldsParserState.needHeader
            tape :=
              headerFieldsParserTape []
                (MachineCodeSymbol.header ::
                  MachineDescription.encodeNatAppend stateCount
                    suffixState) } :=
      TuringMachine.halts_from_of_computes hcomp rfl
    simpa [TuringMachine.HaltsOnInput, TuringMachine.initial,
      headerFieldsParserMachine,
      headerFieldsParserTape_nil_eq_input,
      suffixState] using hhalts

theorem transitionListParserMachine_halts_decodeTransitions_succ
    (count : Nat) (tokens : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsOnInput transitionListParserMachine
        (MachineDescription.encodeNatAppend (Nat.succ count) tokens)) :
    exists transitions : List TransitionDescription,
    exists suffix : Word MachineCodeSymbol,
      MachineDescription.decodeTransitions (Nat.succ count) tokens =
        some (transitions, suffix) := by
  rcases
      transitionListParserMachine_halts_encodeNatAppend_only_encodeTransitionsAppend
        h with
    ⟨transitions, suffix, hcount, htokens⟩
  refine ⟨transitions, suffix, ?_⟩
  rw [hcount, htokens]
  exact
    MachineDescription.decodeTransitions_encodeTransitions_append
      transitions suffix

theorem transitionListParserMachine_halts_decodeTransitions
    (count : Nat) (tokens : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsOnInput transitionListParserMachine
        (MachineDescription.encodeNatAppend count tokens)) :
    exists transitions : List TransitionDescription,
    exists suffix : Word MachineCodeSymbol,
      MachineDescription.decodeTransitions count tokens =
        some (transitions, suffix) := by
  cases count with
  | zero =>
      exact ⟨[], tokens, rfl⟩
  | succ count =>
      exact
        transitionListParserMachine_halts_decodeTransitions_succ
          count tokens h

theorem transitionListParserMachine_accepts_decodeTransitions_succ
    (count : Nat) (tokens : Word MachineCodeSymbol)
    {transitions : List TransitionDescription}
    {suffix : Word MachineCodeSymbol}
    (hdecode :
      MachineDescription.decodeTransitions (Nat.succ count) tokens =
        some (transitions, suffix)) :
    TuringMachine.HaltsOnInput transitionListParserMachine
      (MachineDescription.encodeNatAppend (Nat.succ count) tokens) := by
  rcases
      MachineDescription.decodeTransitions_eq_some_encodeTransitionsAppend
        hdecode with
    ⟨hcount, htokens⟩
  have hhalts :=
    transitionListParserMachine_halts_encodeTransitionsAppend
      transitions suffix
  rw [hcount, htokens]
  exact hhalts

theorem transitionListParserMachine_accepts_decodeTransitions
    {count : Nat} {tokens : Word MachineCodeSymbol}
    {transitions : List TransitionDescription}
    {suffix : Word MachineCodeSymbol}
    (hdecode :
      MachineDescription.decodeTransitions count tokens =
        some (transitions, suffix)) :
    TuringMachine.HaltsOnInput transitionListParserMachine
      (MachineDescription.encodeNatAppend count tokens) := by
  cases count with
  | zero =>
      exact transitionListParserMachine_halts_count_zero tokens
  | succ count =>
      exact
        transitionListParserMachine_accepts_decodeTransitions_succ
          count tokens hdecode

theorem transitionListParserMachine_spec
    (count : Nat) (tokens : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput transitionListParserMachine
        (MachineDescription.encodeNatAppend count tokens) <->
      exists transitions : List TransitionDescription,
      exists suffix : Word MachineCodeSymbol,
        MachineDescription.decodeTransitions count tokens =
          some (transitions, suffix) := by
  constructor
  · intro h
    exact
      transitionListParserMachine_halts_decodeTransitions
        count tokens h
  · intro h
    rcases h with ⟨transitions, suffix, hdecode⟩
    exact
      transitionListParserMachine_accepts_decodeTransitions
        (count := count) (tokens := tokens)
        (transitions := transitions) (suffix := suffix)
        hdecode

theorem transitionListParserConstruction_scaffold :
    TransitionListParserConstruction := by
  refine
    ⟨TransitionListParserState,
      transitionListParserMachine, ?_⟩
  exact transitionListParserMachine_spec

theorem codePrefixParserNormalizerIdentityMachineConstruction_of_parserComponents
    (hheader : HeaderFieldsParserConstruction)
    (htransitions : TransitionListParserConstruction) :
    CodePrefixParserNormalizerIdentityMachineConstruction := by
  rcases hheader with ⟨headerState, header, hheader⟩
  rcases htransitions with
    ⟨transitionState, transitionParser, htransitions⟩
  exact
    codePrefixParserNormalizerSequencingConstruction_scaffold
      header transitionParser hheader htransitions

theorem codePrefixParserNormalizerCodeMachineConstruction_scaffold :
    CodePrefixParserNormalizerCodeMachineConstruction :=
  codePrefixParserNormalizerCodeMachineConstruction_of_identityMachine
    (codePrefixParserNormalizerIdentityMachineConstruction_of_parserComponents
      headerFieldsParserConstruction_scaffold
      transitionListParserConstruction_scaffold)

theorem codePrefixParserNormalizerMachineConstruction_scaffold :
    CodePrefixParserNormalizerMachineConstruction :=
  codePrefixParserNormalizerMachineConstruction_of_codeMachine
    codePrefixParserNormalizerCodeMachineConstruction_scaffold



theorem stageCodeDecoderConstruction_scaffold :
    StageCodeDecoderConstruction :=
  ⟨StageCodeDecoderState,
    stageCodeDecoderMachine,
    stageCodeDecoderMachine_spec⟩

theorem codePrefixStageDescriptionPrefixDecoderConstruction_scaffold :
    CodePrefixStageDescriptionPrefixDecoderConstruction :=
  codePrefixStageDescriptionPrefixDecoderConstruction_of_normalizerIdentityMachine
    (codePrefixParserNormalizerIdentityMachineConstruction_of_parserComponents
      headerFieldsParserConstruction_scaffold
      transitionListParserConstruction_scaffold)

theorem codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_of_decoders_finite
    {stageState descriptionState : Type}
    (_stageDecoder : TuringMachine MachineCodeSymbol stageState)
    (_descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
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
  exact codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_core

theorem codePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction_scaffold :
    CodePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction := by
  intro stageState descriptionState stageDecoder descriptionDecoder
    hstage hdescription
  exact
    codePrefixDecodedBoundedSimulatorCodeMachineConstruction_of_semanticMachine
      (codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_of_decoders_finite
        stageDecoder descriptionDecoder hstage hdescription)

theorem codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_of_decoders
    (hstage : StageCodeDecoderConstruction)
    (hdescription : CodePrefixStageDescriptionPrefixDecoderConstruction) :
    CodePrefixDecodedBoundedSimulatorSemanticMachineConstruction := by
  rcases hstage with ⟨stageState, stageDecoder, hstage⟩
  rcases hdescription with
    ⟨descriptionState, descriptionDecoder, hdescription⟩
  exact
    codePrefixDecodedBoundedSimulatorSemanticMachineConstruction_of_codeMachine
      (codePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction_scaffold
        stageDecoder descriptionDecoder hstage hdescription)

theorem codePrefixDecodedBoundedSimulatorCodeMachineConstruction_scaffold :
    CodePrefixDecodedBoundedSimulatorCodeMachineConstruction := by
  rcases stageCodeDecoderConstruction_scaffold with
    ⟨stageState, stageDecoder, hstage⟩
  rcases codePrefixStageDescriptionPrefixDecoderConstruction_scaffold with
    ⟨descriptionState, descriptionDecoder, hdescription⟩
  exact
    codePrefixDecodedBoundedSimulatorCodeMachineSequencingConstruction_scaffold
      stageDecoder descriptionDecoder hstage hdescription

theorem codePrefixDecodedBoundedSimulatorConstruction_scaffold :
    CodePrefixDecodedBoundedSimulatorConstruction :=
  codePrefixDecodedBoundedSimulatorConstruction_of_codeMachine
    codePrefixDecodedBoundedSimulatorCodeMachineConstruction_scaffold

theorem codePrefixStageSearchControllerCoreConstruction_finite :
    CodePrefixStageSearchControllerCoreConstruction := by
  exact codePrefixStageSearchControllerCoreConstruction_core

theorem codePrefixStageSearchControllerConstruction_scaffold :
    CodePrefixStageSearchControllerConstruction := by
  intro normalizerState branchState simulatorState
    normalizer branch simulator hnormalizer hbranch hsimulator
  exact
    codePrefixStageSearchControllerCoreConstruction_finite
      simulator hsimulator

theorem codePrefixStageSearchControllerCoreConstruction_of_finiteSource
    (hsearch : CodePrefixStageSearchControllerConstruction)
    (hnormalizer : CodePrefixParserNormalizerMachineConstruction)
    (hbranch : CodePrefixParserBranchMachineConstruction) :
    CodePrefixStageSearchControllerCoreConstruction := by
  intro simulatorState simulator hsimulator
  rcases hnormalizer with
    ⟨normalizerState, normalizer, hnormalizer⟩
  rcases hbranch with ⟨branchState, branch, hbranch⟩
  exact hsearch normalizer branch simulator
    hnormalizer hbranch hsimulator

theorem codePrefixStageSearchControllerCoreConstruction_scaffold :
    CodePrefixStageSearchControllerCoreConstruction :=
  codePrefixStageSearchControllerCoreConstruction_finite

theorem codePrefixStageSearchControllerConstruction_of_core
    (hcore : CodePrefixStageSearchControllerCoreConstruction) :
    CodePrefixStageSearchControllerConstruction := by
  intro normalizerState branchState simulatorState
    normalizer branch simulator hnormalizer hbranch hsimulator
  exact hcore simulator hsimulator

theorem codePrefixRecognizerMachineConstruction_scaffold :
    CodePrefixRecognizerMachineConstruction :=
  codePrefixRecognizerMachineConstruction_of_finiteSourceComponents
    codePrefixParserNormalizerMachineConstruction_scaffold
    codePrefixParserBranchMachineConstruction_scaffold
    codePrefixDecodedBoundedSimulatorConstruction_scaffold
    codePrefixStageSearchControllerConstruction_scaffold

def codeUniversalPrefixRunnerFiniteSourceCloseout_scaffold :
    CodeUniversalPrefixRunnerFiniteSourceCloseout where
  prefixRecognizerMachine :=
    codePrefixRecognizerMachineConstruction_scaffold

theorem codeUniversalPrefixRunnerConstruction_scaffold :
    CodeUniversalPrefixRunnerConstruction :=
  codeUniversalPrefixRunnerConstruction_of_runnerFiniteSourceCloseout
    codeUniversalPrefixRunnerFiniteSourceCloseout_scaffold

theorem encodedInputProgramCompiledByDescription_acceptsLanguage
    {P : StagedProgram MachineCodeSymbol Unit}
    {D : MachineDescription}
    {L : Language MachineCodeSymbol}
    (hP : ProgramAcceptsLanguage P L)
    (hcompile : EncodedInputProgramCompiledByDescription P D) :
    MachineDescriptionAcceptsEncodedInputLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w) (hP w)

theorem encodedInputProgramAcceptorCompilationPrinciple_of_descriptionProgramCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    EncodedInputProgramAcceptorCompilationPrinciple := by
  intro P
  rcases hcompile (EncodedInputBoolProgram P) with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  constructor
  · exact hD.left
  · intro w
    exact Iff.trans
      (hD.right (MachineDescription.encodeCodeWordAsInput w))
      (encodedInputBoolProgram_halts_encodeCodeWordAsInput_iff P w)

theorem encodedInputDescriptionCompilerPrinciple_of_programCompiler
    (hcompile : EncodedInputProgramAcceptorCompilationPrinciple) :
    EncodedInputDescriptionCompilerPrinciple := by
  intro L hL
  cases recursivelyEnumerable_has_acceptanceTrace hL with
  | intro trace htrace =>
      cases hcompile (TraceRecognizerProgram trace) with
      | intro D hD =>
          exists D
          exact encodedInputProgramCompiledByDescription_acceptsLanguage
            (traceRecognizerProgram_acceptsLanguage htrace) hD

theorem encodedInputDescriptionCompilerPrinciple_of_descriptionProgramCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    EncodedInputDescriptionCompilerPrinciple :=
  encodedInputDescriptionCompilerPrinciple_of_programCompiler
    (encodedInputProgramAcceptorCompilationPrinciple_of_descriptionProgramCompiler
      hcompile)

theorem codeUniversalPrefixRowsCoverConstruction_of_section53Closeout
    (hclose : CodeUniversalPrefixSection53Closeout) :
    CodeUniversalPrefixRowsCoverConstruction :=
  codeUniversalPrefixRowsCoverConstruction_of_constructions
    (encodedInputDescriptionCompilerPrinciple_of_programCompiler
      hclose.encodedInputProgramCompiler)
    hclose.universalRunner


end Computability
end FoC
