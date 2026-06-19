import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Emitter

set_option doc.verso true

/-!
# Bounded-layout runner assembly

The assembly leaf sequences the parser, configuration runner, and emitter
phases into the public
{name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.Spec)}`Spec`
for
{name (full := FoC.Computability.PairedRecognizerDovetailLayoutCode)}`PairedRecognizerDovetailLayoutCode`.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

theorem exactIdentityDescription_subroutineReady :
    MachineDescription.ExactIdentityDescription.SubroutineReady :=
  ⟨MachineDescription.exactIdentityDescription_wellFormed,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem exactIdentityDescription_reaches
    (T : Tape Bool) :
    exists n : Nat,
      MachineDescription.ExactIdentityDescription.runConfig n
          { state := MachineDescription.ExactIdentityDescription.start
            tape := T } =
        { state := MachineDescription.ExactIdentityDescription.halt
          tape := T } :=
  ⟨0, rfl⟩

theorem exactIdentityDescription_runConfig_from_start
    (n : Nat) (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.runConfig n
        { state := MachineDescription.ExactIdentityDescription.start
          tape := T } =
      { state := MachineDescription.ExactIdentityDescription.halt
        tape := T } := by
  cases n <;>
    simp [MachineDescription.ExactIdentityDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition]

theorem parsedLayoutTape_move_left_move_right
    (L : MachineDescription.DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right (ParsedLayoutTape L)) =
      ParsedLayoutTape L := by
  rcases EncodedRewriters.dovetailLayout_encode_cons L with
    ⟨tail, htail⟩
  unfold ParsedLayoutTape ParsedLayoutBits
  rw [htail]
  exact
    EncodedRewriters.tape_move_left_move_right_input_encodeCodeWordAsInput_cons
      MachineCodeSymbol.transition tail

theorem configRunnerOutputTape_move_left_move_right
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (ConfigRunnerOutputTape accept reject L)) =
      ConfigRunnerOutputTape accept reject L := by
  exact
    parsedLayoutTape_move_left_move_right
      (BoundedRunLayout accept reject L)

def PhaseAssemblyConstruction : Prop :=
  forall accept reject : MachineDescription,
    LayoutParserConstruction ->
      (exists configRunner : MachineDescription,
        AcceptRejectConfigRunnerSpec accept reject configRunner) ->
        (exists emitter : MachineDescription,
          OutputEmitterSpec accept reject emitter) ->
          exists runner : MachineDescription,
            Spec accept reject runner

theorem phaseAssemblyConstruction_scaffold :
    PhaseAssemblyConstruction := by
  intro accept reject hparser hconfig hem
  rcases hparser with ⟨parser, hparser⟩
  rcases hconfig with ⟨configRunner, hconfig⟩
  rcases hem with ⟨emitter, hem⟩
  let identity := MachineDescription.ExactIdentityDescription
  let parserId :=
    MachineDescription.seqSubroutine parser identity Direction.right
  let parsedRunner :=
    MachineDescription.seqSubroutine parserId configRunner Direction.left
  let parsedRunnerId :=
    MachineDescription.seqSubroutine parsedRunner identity Direction.right
  let runner :=
    MachineDescription.seqSubroutine parsedRunnerId emitter Direction.left
  refine ⟨runner, ?_⟩
  have hidReady : identity.SubroutineReady := by
    exact exactIdentityDescription_subroutineReady
  have hparserReady : parser.SubroutineReady := hparser.left
  have hconfigReady : configRunner.SubroutineReady := hconfig.left
  have hemReady : emitter.SubroutineReady := hem.left
  have hparserIdReady : parserId.SubroutineReady := by
    exact MachineDescription.seqSubroutine_subroutineReady
      hparserReady hidReady
  have hparsedRunnerReady : parsedRunner.SubroutineReady := by
    exact MachineDescription.seqSubroutine_subroutineReady
      hparserIdReady hconfigReady
  have hparsedRunnerIdReady : parsedRunnerId.SubroutineReady := by
    exact MachineDescription.seqSubroutine_subroutineReady
      hparsedRunnerReady hidReady
  have hrunnerReady : runner.SubroutineReady := by
    exact MachineDescription.seqSubroutine_subroutineReady
      hparsedRunnerIdReady hemReady
  constructor
  · exact hrunnerReady
  constructor
  · intro L
    have hparserId :
        parserId.HaltsWithTape
          (ParsedLayoutBits L)
          (Tape.move Direction.right (ParsedLayoutTape L)) := by
      exact
        MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
          (A := parser) (B := identity)
          (handoffMove := Direction.right)
          hparserReady hidReady
          (hparser.right.left L)
          (exactIdentityDescription_reaches
            (Tape.move Direction.right (ParsedLayoutTape L)))
    have hconfigReach :
        exists nB : Nat,
          configRunner.runConfig nB
              { state := configRunner.start
                tape :=
                  Tape.move Direction.left
                    (Tape.move Direction.right (ParsedLayoutTape L)) } =
            { state := configRunner.halt
              tape := ConfigRunnerOutputTape accept reject L } := by
      rcases
          MachineDescription.runConfig_eq_halt_of_haltsWithTape
            (hconfig.right.left L) with
        ⟨nB, hB⟩
      refine ⟨nB, ?_⟩
      simpa [ParsedLayoutTape,
        parsedLayoutTape_move_left_move_right L] using hB
    have hparsedRunner :
        parsedRunner.HaltsWithTape
          (ParsedLayoutBits L)
          (ConfigRunnerOutputTape accept reject L) := by
      exact
        MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
          (A := parserId) (B := configRunner)
          (handoffMove := Direction.left)
          hparserIdReady hconfigReady
          hparserId hconfigReach
    have hparsedRunnerId :
        parsedRunnerId.HaltsWithTape
          (ParsedLayoutBits L)
          (Tape.move Direction.right
            (ConfigRunnerOutputTape accept reject L)) := by
      exact
        MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
          (A := parsedRunner) (B := identity)
          (handoffMove := Direction.right)
          hparsedRunnerReady hidReady
          hparsedRunner
          (exactIdentityDescription_reaches
            (Tape.move Direction.right
              (ConfigRunnerOutputTape accept reject L)))
    have hemReach :
        exists nB : Nat,
          emitter.runConfig nB
              { state := emitter.start
                tape :=
                  Tape.move Direction.left
                    (Tape.move Direction.right
                      (ConfigRunnerOutputTape accept reject L)) } =
            { state := emitter.halt
              tape := OutputTape accept reject L } := by
      rcases
          MachineDescription.runConfig_eq_halt_of_haltsWithTape
            (hem.right.left L) with
        ⟨nB, hB⟩
      refine ⟨nB, ?_⟩
      simpa [ConfigRunnerOutputTape, ConfigRunnerOutputBits,
        ParsedLayoutTape,
        configRunnerOutputTape_move_left_move_right accept reject L] using hB
    simpa [runner] using
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := parsedRunnerId) (B := emitter)
        (handoffMove := Direction.left)
        hparsedRunnerIdReady hemReady
        hparsedRunnerId hemReach
  · intro code T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := parsedRunnerId) (B := emitter)
          (handoffMove := Direction.left)
          hparsedRunnerIdReady hemReady
          (by simpa [runner] using hhalt) with
      ⟨TemitInRight, hparsedRunnerIdHalt, hemReach⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := parsedRunner) (B := identity)
          (handoffMove := Direction.right)
          hparsedRunnerReady hidReady
          hparsedRunnerIdHalt with
      ⟨Tconfig, hparsedRunnerHalt, hidAfterConfig⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := parserId) (B := configRunner)
          (handoffMove := Direction.left)
          hparserIdReady hconfigReady
          hparsedRunnerHalt with
      ⟨TparserRight, hparserIdHalt, hconfigReach⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := parser) (B := identity)
          (handoffMove := Direction.right)
          hparserReady hidReady
          hparserIdHalt with
      ⟨Tparser, hparserHalt, hidAfterParser⟩
    rcases hparser.right.right code Tparser hparserHalt with
      ⟨L, hdecode, hTparser⟩
    have hcode :
        code = MachineDescription.DovetailLayout.encode L :=
      MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
        hdecode
    rcases hidAfterParser with ⟨nIdParser, hIdParser⟩
    have hTparserRight :
        TparserRight =
          Tape.move Direction.right (ParsedLayoutTape L) := by
      have hcfg :
          ({ state := identity.halt
             tape := Tape.move Direction.right Tparser } :
            MachineDescription.Configuration) =
          { state := identity.halt
            tape := TparserRight } := by
        simpa [identity] using
          ((exactIdentityDescription_runConfig_from_start
              nIdParser
              (Tape.move Direction.right Tparser)).symm.trans
            hIdParser)
      simpa [hTparser] using
        (congrArg MachineDescription.Configuration.tape hcfg).symm
    rcases hconfigReach with ⟨nConfig, hConfigRun⟩
    have hconfigHalt :
        configRunner.HaltsWithTape
          (ParsedLayoutBits L)
          Tconfig := by
      refine ⟨nConfig, ?_⟩
      have hConfigRunInput :
          configRunner.runConfig nConfig
              (configRunner.initial (ParsedLayoutBits L)) =
            { state := configRunner.halt, tape := Tconfig } := by
        change
          configRunner.runConfig nConfig
              { state := configRunner.start
                tape := ParsedLayoutTape L } =
            { state := configRunner.halt, tape := Tconfig }
        rw [← parsedLayoutTape_move_left_move_right L]
        simpa [hTparserRight] using hConfigRun
      constructor
      · exact congrArg MachineDescription.Configuration.state
          hConfigRunInput
      · exact congrArg MachineDescription.Configuration.tape
          hConfigRunInput
    have hTconfig :
        Tconfig = ConfigRunnerOutputTape accept reject L :=
      hconfig.right.right L Tconfig hconfigHalt
    rcases hidAfterConfig with ⟨nIdConfig, hIdConfig⟩
    have hTemitInRight :
        TemitInRight =
          Tape.move Direction.right
            (ConfigRunnerOutputTape accept reject L) := by
      have hcfg :
          ({ state := identity.halt
             tape := Tape.move Direction.right Tconfig } :
            MachineDescription.Configuration) =
          { state := identity.halt
            tape := TemitInRight } := by
        simpa [identity] using
          ((exactIdentityDescription_runConfig_from_start
              nIdConfig
              (Tape.move Direction.right Tconfig)).symm.trans
            hIdConfig)
      simpa [hTconfig] using
        (congrArg MachineDescription.Configuration.tape hcfg).symm
    rcases hemReach with ⟨nEmit, hEmitRun⟩
    have hemHalt :
        emitter.HaltsWithTape
          (ConfigRunnerOutputBits accept reject L)
          T := by
      refine ⟨nEmit, ?_⟩
      have hEmitRunInput :
          emitter.runConfig nEmit
              (emitter.initial
                (ConfigRunnerOutputBits accept reject L)) =
            { state := emitter.halt, tape := T } := by
        change
          emitter.runConfig nEmit
              { state := emitter.start
                tape := ConfigRunnerOutputTape accept reject L } =
            { state := emitter.halt, tape := T }
        rw [← configRunnerOutputTape_move_left_move_right
          accept reject L]
        simpa [hTemitInRight] using hEmitRun
      constructor
      · exact congrArg MachineDescription.Configuration.state
          hEmitRunInput
      · exact congrArg MachineDescription.Configuration.tape
          hEmitRunInput
    have hT :
        T = OutputTape accept reject L :=
      hem.right.right L T hemHalt
    exact ⟨L, hcode, hT⟩

theorem finiteDescriptionConstruction_scaffold :
    FiniteDescriptionConstruction := by
  intro accept reject
  exact
    phaseAssemblyConstruction_scaffold
      accept reject
      layoutParserConstruction_scaffold
      (acceptRejectConfigRunnerConstruction_scaffold accept reject)
      (outputEmitterConstruction_scaffold accept reject)

theorem rightShiftedOutputCompiledConstruction_scaffold :
    RightShiftedOutputCompiledConstruction := by
  intro accept reject
  rcases finiteDescriptionConstruction_scaffold accept reject with
    ⟨runner, hrunner⟩
  exact
    ⟨runner,
      rightShiftedOutputCompiled_of_spec hrunner⟩

theorem closedHandoffCompiledSubroutine
    (accept reject : MachineDescription) :
    exists runner : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner tapeCodePrimitiveCodeWordHandoffMove := by
  rcases
      rightShiftedOutputCompiledConstruction_scaffold accept reject with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    closedHandoffCompiled_of_rightShiftedOutputCompiled
      hrunner
      (by
        intro code out htransform
        rcases
            pairedRecognizerDovetailLayoutCode_transform_eq_some_cons
              htransform with
          ⟨tail, hout⟩
        exact ⟨MachineCodeSymbol.transition, tail, hout⟩)

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
