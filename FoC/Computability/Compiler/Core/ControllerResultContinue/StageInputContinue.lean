import FoC.Computability.Compiler.Core.ControllerResultContinue.GuardProjection
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.Assembly

set_option doc.verso true

/-!
# Controller result continuation stage-input leaf

This module isolates the final stage-input continuation leaf.  The pure
encoding lemmas here name the exact target word produced after the stage input
projection has removed the controller header and result suffix.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace ControllerResultContinueConstruction

def stageInputContinueNatTail : Nat -> Word MachineCodeSymbol
  | 0 => [MachineCodeSymbol.tick, MachineCodeSymbol.done, MachineCodeSymbol.done]
  | n + 1 => MachineCodeSymbol.tick :: stageInputContinueNatTail n

theorem encodeNatAppend_succ
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    encodeNatAppend (n + 1) suffix =
      MachineCodeSymbol.tick ::
        encodeNatAppend n suffix := by
  rfl

theorem encodeBoolWordAppend_nil_nil :
    encodeBoolWordAppend ([] : Word Bool) [] =
      [MachineCodeSymbol.done] := by
  rfl

theorem stageInputContinueNatTail_eq_encode
    (stage : Nat) :
    stageInputContinueNatTail stage =
      encodeNatAppend (stage + 1)
        (encodeBoolWordAppend ([] : Word Bool) []) := by
  induction stage with
  | zero =>
      rfl
  | succ stage ih =>
      change
        MachineCodeSymbol.tick :: stageInputContinueNatTail stage =
          encodeNatAppend (stage + 1 + 1)
            (encodeBoolWordAppend ([] : Word Bool) [])
      rw [ih]
      rfl

theorem stageInputContinue_output_eq_header_input_tail
    (input : Word Bool) (stage : Nat) :
    DovetailControllerLayout.encode
        { input := input, stage := stage + 1, result := [] } =
      MachineCodeSymbol.header ::
        encodeBoolWordAppend input
          (stageInputContinueNatTail stage) := by
  rw [stageInputContinueNatTail_eq_encode]
  rfl

theorem stageInputContinue_nextStage_eq_header_input_tail
    (C : DovetailControllerLayout) :
    DovetailControllerLayout.encode
        (DovetailControllerLayout.nextStage C) =
      MachineCodeSymbol.header ::
        encodeBoolWordAppend C.input
          (stageInputContinueNatTail C.stage) := by
  cases C
  exact stageInputContinue_output_eq_header_input_tail _ _

theorem stageInputContinue_stageInputCode_eq_input_stage
    (input : Word Bool) (stage : Nat) :
    DovetailLayout.stageInputCode input stage =
      encodeBoolWordAppend input
        (encodeNatAppend stage []) := by
  rfl

def stageInputContinueStagePrefix
    (input : Word Bool) (stage : Nat) : Word MachineCodeSymbol :=
  encodeBoolWordAppend input
    (List.replicate stage MachineCodeSymbol.tick)

theorem stageInputContinueNatTail_eq_replicate
    (stage : Nat) :
    stageInputContinueNatTail stage =
      List.append (List.replicate stage MachineCodeSymbol.tick)
        [MachineCodeSymbol.tick, MachineCodeSymbol.done,
          MachineCodeSymbol.done] := by
  induction stage with
  | zero =>
      rfl
  | succ stage ih =>
      change
        MachineCodeSymbol.tick :: stageInputContinueNatTail stage =
          MachineCodeSymbol.tick ::
            List.append (List.replicate stage MachineCodeSymbol.tick)
              [MachineCodeSymbol.tick, MachineCodeSymbol.done,
                MachineCodeSymbol.done]
      rw [ih]

theorem stageInputContinue_stageInputCode_eq_prefix_done
    (input : Word Bool) (stage : Nat) :
    DovetailLayout.stageInputCode input stage =
      List.append (stageInputContinueStagePrefix input stage)
        [MachineCodeSymbol.done] := by
  rw [stageInputContinue_stageInputCode_eq_input_stage]
  have hnat :
      encodeNatAppend stage [] =
        List.append (List.replicate stage MachineCodeSymbol.tick)
          [MachineCodeSymbol.done] := by
    simp [encodeNatAppend,
      ControllerStageInputProjection.encodeNat_eq_replicate_tick_done]
  rw [hnat]
  exact
    encodeBoolWordAppend_append input
      (List.replicate stage MachineCodeSymbol.tick)
      [MachineCodeSymbol.done]

theorem stageInputContinue_output_eq_header_prefix_tail
    (input : Word Bool) (stage : Nat) :
    DovetailControllerLayout.encode
        { input := input, stage := stage + 1, result := [] } =
      MachineCodeSymbol.header ::
        List.append (stageInputContinueStagePrefix input stage)
          [MachineCodeSymbol.tick, MachineCodeSymbol.done,
            MachineCodeSymbol.done] := by
  rw [stageInputContinue_output_eq_header_input_tail]
  rw [stageInputContinueNatTail_eq_replicate]
  exact congrArg (fun tail =>
      MachineCodeSymbol.header :: tail)
    (encodeBoolWordAppend_append input
      (List.replicate stage MachineCodeSymbol.tick)
      [MachineCodeSymbol.tick, MachineCodeSymbol.done,
        MachineCodeSymbol.done])

def stageInputContinueDoneDoneBits : Word Bool :=
  encodeCodeWordAsInput
    [MachineCodeSymbol.done, MachineCodeSymbol.done]

def stageInputContinueHeaderBits : Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.header

def stageInputContinueTickBits : Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.tick

def stageInputContinueDoneBits : Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.done

def stageInputContinueBitsOutputFromPrefix
    (prefixBits : Word Bool) : Word Bool :=
  List.append stageInputContinueHeaderBits
    (List.append prefixBits
      (List.append stageInputContinueTickBits
        stageInputContinueDoneDoneBits))

theorem stageInputContinue_stageInputBits_eq_prefix_done
    (input : Word Bool) (stage : Nat) :
    DovetailInitialLayoutInitializer.stageInputBits input stage =
      List.append
        (encodeCodeWordAsInput
          (stageInputContinueStagePrefix input stage))
        stageInputContinueDoneBits := by
  rw [DovetailInitialLayoutInitializer.stageInputBits]
  rw [PairedRecognizerDovetailStageInputCode]
  rw [stageInputContinue_stageInputCode_eq_prefix_done]
  rw [encodeCodeWordAsInput_append]
  simp [stageInputContinueDoneBits,
    encodeCodeWordAsInput]

theorem stageInputContinue_outputBits_eq_prefix
    (input : Word Bool) (stage : Nat) :
    encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          { input := input, stage := stage + 1, result := [] }) =
      stageInputContinueBitsOutputFromPrefix
        (encodeCodeWordAsInput
          (stageInputContinueStagePrefix input stage)) := by
  rw [stageInputContinue_output_eq_header_prefix_tail]
  change
    List.append stageInputContinueHeaderBits
        (encodeCodeWordAsInput
          (List.append (stageInputContinueStagePrefix input stage)
            [MachineCodeSymbol.tick, MachineCodeSymbol.done,
              MachineCodeSymbol.done])) =
      stageInputContinueBitsOutputFromPrefix
        (encodeCodeWordAsInput
          (stageInputContinueStagePrefix input stage))
  rw [encodeCodeWordAsInput_append]
  simp [stageInputContinueBitsOutputFromPrefix,
    stageInputContinueHeaderBits, stageInputContinueTickBits,
    stageInputContinueDoneDoneBits,
    encodeCodeWordAsInput,
    encodeCodeSymbolAsInput]

def StageInputContinueCheckedRewriterDescription : MachineDescription where
  stateCount := 16
  start := 0
  halt := 15
  transitions :=
    [ transition
        0 (some false) (some false) Direction.left 1
    , transition
        0 (some true) (some true) Direction.left 1
    , transition
        1 none (some false) Direction.left 2
    , transition
        2 none (some false) Direction.left 3
    , transition
        3 none (some false) Direction.left 4
    , transition
        4 none (some false) Direction.right 5
    , transition
        5 (some false) (some false) Direction.right 5
    , transition
        5 (some true) (some true) Direction.right 5
    , transition
        5 none none Direction.left 6
    , transition
        6 (some false) (some false) Direction.right 7
    , transition
        6 (some true) (some false) Direction.right 7
    , transition
        7 none (some false) Direction.right 8
    , transition
        8 none (some false) Direction.right 9
    , transition
        9 none (some true) Direction.right 10
    , transition
        10 none (some true) Direction.right 11
    , transition
        11 none (some false) Direction.right 12
    , transition
        12 none (some false) Direction.right 13
    , transition
        13 none (some true) Direction.right 14
    , transition
        14 none (some true) Direction.right 15
    ]

theorem stageInputContinueCheckedRewriterDescription_wellFormed :
    StageInputContinueCheckedRewriterDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := StageInputContinueCheckedRewriterDescription.transitions)
      (stateCount :=
        StageInputContinueCheckedRewriterDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := StageInputContinueCheckedRewriterDescription.transitions)
      (by native_decide)

theorem stageInputContinueCheckedRewriterDescription_haltTransitionFree :
    StageInputContinueCheckedRewriterDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := StageInputContinueCheckedRewriterDescription.transitions)
    (state := StageInputContinueCheckedRewriterDescription.halt)
    (by native_decide)

theorem stageInputContinueCheckedRewriterDescription_subroutineReady :
    StageInputContinueCheckedRewriterDescription.SubroutineReady :=
  ⟨stageInputContinueCheckedRewriterDescription_wellFormed,
    stageInputContinueCheckedRewriterDescription_haltTransitionFree⟩

def stageInputContinueHeaderPrefixedTape
    (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    [some false]
    (List.append
      [some false, some false, some false]
      (List.append (bits.map some) [none]))

theorem stageInputContinueCheckedRewriterDescription_run_header
    (b : Bool) (rest : List (Option Bool)) :
    StageInputContinueCheckedRewriterDescription.runConfig 5
        { state := StageInputContinueCheckedRewriterDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells []
              (some b :: rest) } =
      { state := 5
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            [some false]
            (List.append
              [some false, some false, some false]
              (some b :: rest)) } := by
  cases b <;>
    simp [StageInputContinueCheckedRewriterDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem stageInputContinueCheckedRewriterDescription_run_header_checked_cons
    (b : Bool) (bits : Word Bool) :
    StageInputContinueCheckedRewriterDescription.runConfig 5
        { state := StageInputContinueCheckedRewriterDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells []
              (List.append ((b :: bits).map some) [none]) } =
      { state := 5
        tape := stageInputContinueHeaderPrefixedTape (b :: bits) } := by
  simpa [stageInputContinueHeaderPrefixedTape,
    List.append_assoc] using
    stageInputContinueCheckedRewriterDescription_run_header
      b (List.append (bits.map some) [none])

theorem stageInputContinueCheckedRewriterDescription_run_scan_nonempty
    (leftRev : List (Option Bool)) (b : Bool)
    (rest : List (Option Bool)) :
    StageInputContinueCheckedRewriterDescription.runConfig 1
        { state := 5
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells leftRev
              (some b :: rest) } =
      { state := 5
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (some b :: leftRev) rest } := by
  cases b <;> cases rest <;>
    simp [StageInputContinueCheckedRewriterDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem stageInputContinueCheckedRewriterDescription_run_scan
    (leftRev : List (Option Bool)) (bits : Word Bool) :
    StageInputContinueCheckedRewriterDescription.runConfig bits.length
        { state := 5
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells leftRev
              (List.append (bits.map some) [none]) } =
      { state := 5
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (List.append (bits.reverse.map some) leftRev) [none] } := by
  induction bits generalizing leftRev with
  | nil =>
      simp [runConfig]
  | cons b rest ih =>
      rw [show (b :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        StageInputContinueCheckedRewriterDescription.runConfig rest.length
            (StageInputContinueCheckedRewriterDescription.runConfig 1
              { state := 5
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells leftRev
                    (some b :: List.append (rest.map some) [none]) }) =
          { state := 5
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (List.append ((b :: rest).reverse.map some) leftRev)
                [none] }
      rw [stageInputContinueCheckedRewriterDescription_run_scan_nonempty]
      rw [ih]
      simp [List.append_assoc]

theorem stageInputContinueCheckedRewriterDescription_run_to_last_bit
    (leftRev : List (Option Bool)) (lastBit : Bool) :
    StageInputContinueCheckedRewriterDescription.runConfig 1
        { state := 5
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (some lastBit :: leftRev) [none] } =
      { state := 6
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells leftRev
            [some lastBit, none] } := by
  cases lastBit <;>
    simp [StageInputContinueCheckedRewriterDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem stageInputContinueCheckedRewriterDescription_run_rewrite_last
    (leftRev : List (Option Bool)) (lastBit : Bool) :
    StageInputContinueCheckedRewriterDescription.runConfig 1
        { state := 6
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells leftRev
              [some lastBit, none] } =
      { state := 7
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (some false :: leftRev) [none] } := by
  cases lastBit <;>
    simp [StageInputContinueCheckedRewriterDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem stageInputContinueDoneDoneBits_eq :
    stageInputContinueDoneDoneBits =
      [false, false, true, true, false, false, true, true] := by
  rfl

def stageInputContinueCheckedTape (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    (List.append (bits.map some) [none])

def stageInputContinueOutputTape (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (bits.reverse.map some) [none]

theorem stageInputContinueOutputTape_normalizedOutput
    (bits : Word Bool) :
    Tape.normalizedOutput (stageInputContinueOutputTape bits) = bits := by
  have hfilter :
      forall xs : Word Bool,
        List.filterMap
            ((fun cell : Option Bool => cell) ∘
              (fun b : Bool => some b)) xs = xs := by
    intro xs
    induction xs with
    | nil =>
        rfl
    | cons b rest ih =>
        simp [Function.comp, ih]
  simp [stageInputContinueOutputTape,
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.normalizedOutput, Tape.cells, hfilter]

theorem stageInputContinueCheckedRewriterDescription_run_append_done_done
    (leftRev : List (Option Bool)) :
    StageInputContinueCheckedRewriterDescription.runConfig 8
        { state := 7
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells leftRev [none] } =
      { state := StageInputContinueCheckedRewriterDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (List.append
              (stageInputContinueDoneDoneBits.reverse.map some) leftRev)
            [none] } := by
  simp [StageInputContinueCheckedRewriterDescription,
    stageInputContinueDoneDoneBits,
    encodeCodeWordAsInput,
    encodeCodeSymbolAsInput,
    DovetailInitialLayoutInitializer.tapeAtCells,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write, Tape.move,
    Tape.moveRight]

theorem stageInputContinueCheckedRewriterDescription_haltsFromTape_prefixBits
    (prefixBits : Word Bool) :
    StageInputContinueCheckedRewriterDescription.HaltsFromTape
      (stageInputContinueCheckedTape
        (List.append prefixBits stageInputContinueDoneBits))
      (stageInputContinueOutputTape
        (stageInputContinueBitsOutputFromPrefix prefixBits)) := by
  let inputBits := List.append prefixBits stageInputContinueDoneBits
  let scanBits := List.append [false, false, false] inputBits
  let outputBits := stageInputContinueBitsOutputFromPrefix prefixBits
  let leftAfterLast : List (Option Bool) :=
    List.map some
      (List.append [true, false, false]
        (List.append prefixBits.reverse
          [false, false, false, false]))
  refine ⟨5 + scanBits.length + 10, ?_⟩
  have hrun :
      StageInputContinueCheckedRewriterDescription.runConfig
          (5 + scanBits.length + 10)
          { state := StageInputContinueCheckedRewriterDescription.start
            tape := stageInputContinueCheckedTape inputBits } =
        { state := StageInputContinueCheckedRewriterDescription.halt
          tape := stageInputContinueOutputTape outputBits } := by
    rw [show 5 + scanBits.length + 10 =
        5 + (scanBits.length + 10) by omega]
    rw [runConfig_add]
    have hheader :
        StageInputContinueCheckedRewriterDescription.runConfig 5
            { state := StageInputContinueCheckedRewriterDescription.start
              tape := stageInputContinueCheckedTape inputBits } =
          { state := 5
            tape := stageInputContinueHeaderPrefixedTape inputBits } := by
      unfold inputBits
      cases prefixBits with
      | nil =>
          simpa [stageInputContinueCheckedTape,
            stageInputContinueDoneBits,
            encodeCodeSymbolAsInput] using
            stageInputContinueCheckedRewriterDescription_run_header_checked_cons
              false [false, true, true]
      | cons b rest =>
          simpa [stageInputContinueCheckedTape,
            stageInputContinueDoneBits,
            encodeCodeSymbolAsInput,
            List.append_assoc] using
            stageInputContinueCheckedRewriterDescription_run_header_checked_cons
              b (List.append rest stageInputContinueDoneBits)
    rw [hheader]
    rw [show scanBits.length + 10 = scanBits.length + (1 + (1 + 8)) by
      omega]
    rw [runConfig_add]
    have hscan :
        StageInputContinueCheckedRewriterDescription.runConfig scanBits.length
            { state := 5
              tape := stageInputContinueHeaderPrefixedTape inputBits } =
          { state := 5
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (List.append (scanBits.reverse.map some) [some false])
                [none] } := by
      have htape :
          stageInputContinueHeaderPrefixedTape inputBits =
            DovetailInitialLayoutInitializer.tapeAtCells [some false]
              (List.append (scanBits.map some) [none]) := by
        simp [stageInputContinueHeaderPrefixedTape, scanBits]
      rw [htape]
      simpa [List.append_assoc] using
        stageInputContinueCheckedRewriterDescription_run_scan
          [some false] scanBits
    rw [hscan]
    have hleft :
        List.append (scanBits.reverse.map some) [some false] =
          some true :: leftAfterLast := by
      simp [scanBits, inputBits, leftAfterLast,
        stageInputContinueDoneBits,
        encodeCodeSymbolAsInput,
        List.reverse_append, List.map_append, List.append_assoc]
    rw [hleft]
    rw [runConfig_add]
    rw [stageInputContinueCheckedRewriterDescription_run_to_last_bit]
    rw [runConfig_add]
    rw [stageInputContinueCheckedRewriterDescription_run_rewrite_last]
    rw [stageInputContinueCheckedRewriterDescription_run_append_done_done]
    simp [stageInputContinueOutputTape, outputBits,
      stageInputContinueBitsOutputFromPrefix, leftAfterLast,
      stageInputContinueHeaderBits, stageInputContinueTickBits,
      stageInputContinueDoneDoneBits,
      encodeCodeSymbolAsInput,
      encodeCodeWordAsInput,
      List.reverse_append, List.map_append, List.append_assoc]
  constructor
  · exact
      (by
        simpa [inputBits] using
          congrArg Configuration.state hrun)
  · exact
      (by
        simpa [inputBits, outputBits] using
          congrArg Configuration.tape hrun)

theorem stageInputContinueCheckedRewriterDescription_haltsFromTape_stageInput
    (input : Word Bool) (stage : Nat) :
    StageInputContinueCheckedRewriterDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.stageInputCheckedInputTape
        input stage)
      (stageInputContinueOutputTape
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            { input := input, stage := stage + 1, result := [] }))) := by
  have h :=
    stageInputContinueCheckedRewriterDescription_haltsFromTape_prefixBits
      (encodeCodeWordAsInput
        (stageInputContinueStagePrefix input stage))
  have hinput :=
    stageInputContinue_stageInputBits_eq_prefix_done input stage
  have houtput :=
    stageInputContinue_outputBits_eq_prefix input stage
  simpa [DovetailInitialLayoutInitializer.stageInputCheckedInputTape,
    stageInputContinueCheckedTape, hinput, houtput] using h

def StageInputContinueDescription
    (validator : MachineDescription) : MachineDescription :=
  seqSubroutine validator
    StageInputContinueCheckedRewriterDescription Direction.left

theorem stageInputContinueDescription_subroutineReady
    {validator : MachineDescription}
    (hvalidator :
      DovetailInitialLayoutInitializer.StageInputValidatorSpec validator) :
    (StageInputContinueDescription validator).SubroutineReady :=
  seqSubroutine_subroutineReady
    hvalidator.left
    stageInputContinueCheckedRewriterDescription_subroutineReady

theorem stageInputContinueDescription_haltsWithOutput_stageInput
    {validator : MachineDescription}
    (hvalidator :
      DovetailInitialLayoutInitializer.StageInputValidatorSpec validator)
    (input : Word Bool) (stage : Nat) :
    (StageInputContinueDescription validator).HaltsWithOutput
      (DovetailInitialLayoutInitializer.stageInputBits input stage)
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          { input := input, stage := stage + 1, result := [] })) := by
  let A := validator
  let B := StageInputContinueCheckedRewriterDescription
  let Tout : Tape Bool :=
    stageInputContinueOutputTape
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          { input := input, stage := stage + 1, result := [] }))
  have hAready : A.SubroutineReady := hvalidator.left
  have hBready : B.SubroutineReady :=
    stageInputContinueCheckedRewriterDescription_subroutineReady
  rcases hvalidator.right.left input stage with ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              Tape.input
                (DovetailInitialLayoutInitializer.stageInputBits
                  input stage) } =
        { state := A.halt
          tape :=
            DovetailInitialLayoutInitializer.stageInputCheckedValidatorTape
              input stage } := by
    simpa [A, initial] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape :=
                Tape.move Direction.left
                  (DovetailInitialLayoutInitializer.stageInputCheckedValidatorTape
                    input stage) } =
          { state := B.halt, tape := Tout } := by
    have hBhalt :=
      stageInputContinueCheckedRewriterDescription_haltsFromTape_stageInput
        input stage
    rcases
        runConfig_eq_halt_of_haltsFromTape
          hBhalt with
      ⟨nB, hBRun⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tout,
      DovetailInitialLayoutInitializer.stageInputCheckedValidatorTape,
      DovetailInitialLayoutInitializer.stageInputCheckedInputTape_move_left_move_right]
      using hBRun
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  have hhalt :
      (StageInputContinueDescription validator).HaltsWithTape
        (DovetailInitialLayoutInitializer.stageInputBits input stage)
        Tout := by
    refine ⟨n, ?_⟩
    constructor
    · simpa [StageInputContinueDescription, A, B,
        initial] using
        congrArg Configuration.state hn
    · simpa [StageInputContinueDescription, A, B,
        initial, Tout] using
        congrArg Configuration.tape hn
  have houtput :=
    haltsWithOutput_of_haltsWithTape hhalt
  simpa [Tout, stageInputContinueOutputTape_normalizedOutput] using houtput

theorem stageInputContinueDescription_transform_of_haltsWithOutput
    {validator : MachineDescription}
    (hvalidator :
      DovetailInitialLayoutInitializer.StageInputValidatorSpec validator)
    (code out : Word MachineCodeSymbol)
    (hhalt :
      (StageInputContinueDescription validator).HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out)) :
    StageInputContinuePrimitive.transform code = some out := by
  let continuer := StageInputContinueDescription validator
  rcases hhalt with ⟨n, hn⟩
  let T : Tape Bool :=
    (continuer.runConfig n
      (continuer.initial
        (encodeCodeWordAsInput code))).tape
  have hTape :
      continuer.HaltsWithTape
        (encodeCodeWordAsInput code) T := by
    refine ⟨n, ?_⟩
    exact ⟨hn.left, rfl⟩
  have hnorm :
      Tape.normalizedOutput T =
        encodeCodeWordAsInput out := by
    simpa [T] using hn.right
  let A := validator
  let B := StageInputContinueCheckedRewriterDescription
  have hAready : A.SubroutineReady := hvalidator.left
  have hBready : B.SubroutineReady :=
    stageInputContinueCheckedRewriterDescription_subroutineReady
  rcases
      seqSubroutine_haltsWithTape_inv
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hTape with
    ⟨Tmid, hAhalt, hBReach⟩
  rcases hvalidator.right.right code Tmid hAhalt with
    ⟨input, stage, hcode, hhandoff⟩
  have hBFrom :
      B.HaltsFromTape
        (DovetailInitialLayoutInitializer.stageInputCheckedInputTape
          input stage)
        T := by
    rcases hBReach with ⟨nB, hBRun⟩
    refine ⟨nB, ?_⟩
    change
      (B.runConfig nB
        { state := B.start
          tape :=
            DovetailInitialLayoutInitializer.stageInputCheckedInputTape
              input stage }).state = B.halt ∧
      (B.runConfig nB
        { state := B.start
          tape :=
            DovetailInitialLayoutInitializer.stageInputCheckedInputTape
              input stage }).tape = T
    have hBRun' :
        B.runConfig nB
            { state := B.start
              tape :=
                DovetailInitialLayoutInitializer.stageInputCheckedInputTape
                  input stage } =
          { state := B.halt, tape := T } := by
      simpa [B, hhandoff] using hBRun
    constructor
    · simp [hBRun']
    · simp [hBRun']
  let targetCode : Word MachineCodeSymbol :=
    DovetailControllerLayout.encode
      { input := input, stage := stage + 1, result := [] }
  let targetTape : Tape Bool :=
    stageInputContinueOutputTape
      (encodeCodeWordAsInput targetCode)
  have hBGood :
      B.HaltsFromTape
        (DovetailInitialLayoutInitializer.stageInputCheckedInputTape
          input stage)
        targetTape := by
    simpa [B, targetTape, targetCode] using
      stageInputContinueCheckedRewriterDescription_haltsFromTape_stageInput
        input stage
  have hT : T = targetTape :=
    haltsFromTape_functional_of_haltTransitionFree
      stageInputContinueCheckedRewriterDescription_haltTransitionFree
      hBFrom hBGood
  have houtBits :
      encodeCodeWordAsInput out =
        encodeCodeWordAsInput targetCode := by
    rw [← hnorm, hT]
    simp [targetTape, stageInputContinueOutputTape_normalizedOutput]
  have hout : out = targetCode :=
    encodeCodeWordAsInput_injective houtBits
  exact
    (stageInputContinuePrimitive_transform_eq_some_iff code out).mpr
      ⟨input, stage, hcode, hout⟩

theorem stageInputContinueDescription_haltsWithOutput_iff
    {validator : MachineDescription}
    (hvalidator :
      DovetailInitialLayoutInitializer.StageInputValidatorSpec validator)
    (code out : Word MachineCodeSymbol) :
    (StageInputContinueDescription validator).HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
      StageInputContinuePrimitive.transform code = some out := by
  constructor
  · exact
      stageInputContinueDescription_transform_of_haltsWithOutput
        hvalidator code out
  · intro htransform
    rcases
        (stageInputContinuePrimitive_transform_eq_some_iff
          code out).mp htransform with
      ⟨input, stage, hcode, hout⟩
    have hforward :=
      stageInputContinueDescription_haltsWithOutput_stageInput
        hvalidator input stage
    simpa [DovetailInitialLayoutInitializer.stageInputBits,
      PairedRecognizerDovetailStageInputCode, hcode, hout] using hforward

theorem stageInputContinueDescription_outputCompiledSubroutine
    {validator : MachineDescription}
    (hvalidator :
      DovetailInitialLayoutInitializer.StageInputValidatorSpec validator) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      StageInputContinuePrimitive
      (StageInputContinueDescription validator) :=
  ⟨⟨(stageInputContinueDescription_subroutineReady hvalidator).left,
      stageInputContinueDescription_haltsWithOutput_iff hvalidator⟩,
    (stageInputContinueDescription_subroutineReady hvalidator).right⟩

theorem stageInputContinuePrimitive_outputCompiledSubroutineConstruction :
    exists continuer : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        StageInputContinuePrimitive continuer := by
  rcases
      DovetailInitialLayoutInitializer.stageInputValidatorSpec_realizer with
    ⟨validator, hvalidator⟩
  exact
    ⟨StageInputContinueDescription validator,
      stageInputContinueDescription_outputCompiledSubroutine hvalidator⟩

end ControllerResultContinueConstruction

end Computability
end FoC
