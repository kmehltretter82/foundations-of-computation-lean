import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.TapeCodePrimitiveSequencing
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner

set_option doc.verso true

/-!
# Bounded-layout runner assembly

The assembly leaf sequences the parser and configuration runner
phases into the public
{name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.Spec)}`Spec`
for
{name (full := FoC.Computability.PairedRecognizerDovetailLayoutCode)}`PairedRecognizerDovetailLayoutCode`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def PhaseAssemblyConstruction : Prop :=
  forall accept reject : MachineDescription,
    LayoutCheckedParserConstruction ->
      (exists configRunner : MachineDescription,
        AcceptRejectConfigRunnerSpec accept reject configRunner) ->
          exists runner : MachineDescription,
            Spec accept reject runner

theorem phaseAssemblyConstruction_scaffold :
    PhaseAssemblyConstruction := by
  intro accept reject hparser hconfig
  rcases hparser with ⟨parser, hparser⟩
  rcases hconfig with ⟨configRunner, hconfig⟩
  let identity := ExactIdentityDescription
  let parserId :=
    seqSubroutine parser identity Direction.right
  let runner :=
    seqSubroutine parserId configRunner Direction.left
  refine ⟨runner, ?_⟩
  have hparserReady : parser.SubroutineReady := hparser.left
  have hconfigReady : configRunner.SubroutineReady := hconfig.left
  have hidReady : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hparserIdReady : parserId.SubroutineReady :=
    seqSubroutine_subroutineReady
      hparserReady hidReady
  have hrunnerReady : runner.SubroutineReady :=
    seqSubroutine_subroutineReady
      hparserIdReady hconfigReady
  constructor
  · exact hrunnerReady
  constructor
  · intro L
    have hparserHalt :
        parser.HaltsWithTape
          (ParsedLayoutBits L)
          (ParsedLayoutCheckedTape L) :=
      hparser.right.left L
    have hparserId :
        parserId.HaltsWithTape
          (ParsedLayoutBits L)
          (Tape.move Direction.right (ParsedLayoutCheckedTape L)) := by
      exact
        seqSubroutine_haltsWithTape_of_haltsWithTape
          (A := parser) (B := identity)
          (handoffMove := Direction.right)
          hparserReady hidReady
          hparserHalt
          (CommonGround.Identity.exactIdentityDescription_run_from_start
            (Tape.move Direction.right (ParsedLayoutCheckedTape L)))
    have h_equiv := hconfig.right.left L
    rcases h_equiv with ⟨Tactual, h_halt, h_eq⟩
    have hconfigReach :
        exists nB : Nat,
          configRunner.runConfig nB
              { state := configRunner.start
                tape :=
                  Tape.move Direction.left
                    (Tape.move Direction.right (ParsedLayoutCheckedTape L)) } =
            { state := configRunner.halt
              tape := Tactual } := by
      rcases runConfig_eq_halt_of_haltsFromTape h_halt with ⟨nB, hB⟩
      refine ⟨nB, ?_⟩
      simpa [parsedLayoutCheckedTape_move_left_move_right L] using hB
    have h_runner_halts :
        runner.HaltsWithTape
          (ParsedLayoutBits L)
          Tactual := by
      exact
        seqSubroutine_haltsWithTape_of_haltsWithTape
          (A := parserId) (B := configRunner)
          (handoffMove := Direction.left)
          hparserIdReady hconfigReady
          hparserId hconfigReach
    exact ⟨Tactual, h_runner_halts, h_eq⟩
  · intro code T hhalt_equiv
    rcases hhalt_equiv with ⟨Tactual, hhalt, hT_equiv⟩
    rcases
        seqSubroutine_haltsWithTape_inv
          (A := parserId) (B := configRunner)
          (handoffMove := Direction.left)
          hparserIdReady hconfigReady
          (by simpa [runner] using hhalt) with
      ⟨TconfigInLeft, hparserIdHalt, hconfigHalt⟩
    rcases
        seqSubroutine_haltsWithTape_inv
          (A := parser) (B := identity)
          (handoffMove := Direction.right)
          hparserReady hidReady
          hparserIdHalt with
      ⟨Tparser, hparserHalt, hidAfterParser⟩
    rcases hparser.right.right code Tparser hparserHalt with
      ⟨L, hdecode, hTparser⟩
    have hcode :
        code = DovetailLayout.encode L :=
      DovetailLayout.decodeComplete_eq_some_encode
        hdecode
    rcases hidAfterParser with ⟨nIdParser, hIdParser⟩
    have hTconfigInLeft :
        TconfigInLeft =
          Tape.move Direction.right (ParsedLayoutCheckedTape L) := by
      have hcfg :
          ({ state := identity.halt
             tape := Tape.move Direction.right Tparser } :
            Configuration) =
          { state := identity.halt
            tape := TconfigInLeft } := by
        simpa [identity] using
          ((CommonGround.Identity.exactIdentityDescription_runConfig_from_start
              nIdParser
              (Tape.move Direction.right Tparser)).symm.trans
            hIdParser)
      simpa [hTparser] using
        (congrArg Configuration.tape hcfg).symm
    have hconfigRunStart :
        configRunner.HaltsFromTape
          (Tape.move Direction.left TconfigInLeft)
          Tactual := by
      rcases hconfigHalt with ⟨n, hn⟩
      exact ⟨n, ⟨congrArg Configuration.state hn, congrArg Configuration.tape hn⟩⟩
    have hconfigRunExact :
        configRunner.HaltsFromTape
          (ParsedLayoutCheckedTape L)
          Tactual := by
      have h_eq : Tape.move Direction.left TconfigInLeft = ParsedLayoutCheckedTape L := by
        rw [hTconfigInLeft]
        exact parsedLayoutCheckedTape_move_left_move_right L
      rw [← h_eq]
      exact hconfigRunStart
    have hTactual :
        Tape.Equiv Tactual (OutputTape accept reject L) :=
      hconfig.right.right L Tactual hconfigRunExact
    have hT :
        Tape.Equiv T (OutputTape accept reject L) :=
      Tape.Equiv.trans (Tape.Equiv.symm hT_equiv) hTactual
    exact ⟨L, hcode, hT⟩

theorem finiteDescriptionConstruction_scaffold :
    FiniteDescriptionConstruction := by
  intro accept reject
  exact
    phaseAssemblyConstruction_scaffold
      accept reject
      layoutCheckedParserConstruction_scaffold
      (acceptRejectConfigRunnerConstruction_scaffold accept reject)

theorem outputCompiledSubroutine
    (accept reject : MachineDescription) :
    exists runner : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner := by
  rcases finiteDescriptionConstruction_scaffold accept reject with
    ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    outputCompiledSubroutineByDescription_of_spec hrunner

def ClosedHandoffRightShiftedConstruction
    (accept reject : MachineDescription) : Prop :=
  exists runner : MachineDescription,
    FoC.Computability.EncodedRewriters.ExactRightShiftedOutputCompiledSubroutineByDescription
      (PairedRecognizerDovetailLayoutCode accept reject)
      runner

theorem closedHandoffCompiledSubroutine_of_rightShifted
    {accept reject : MachineDescription}
    (hright :
      ClosedHandoffRightShiftedConstruction accept reject) :
    exists runner : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner tapeCodePrimitiveCodeWordHandoffMove := by
  rcases hright with ⟨runner, hrunner⟩
  refine ⟨runner, ?_⟩
  exact
    FoC.Computability.EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled
      (FoC.Computability.EncodedRewriters.rightShiftedOutputCompiledSubroutineByDescription_of_exact
        hrunner)
      (fun htransform => by
        rcases
            pairedRecognizerDovetailLayoutCode_transform_eq_some_cons
              htransform with
          ⟨tail, htail⟩
        exact ⟨MachineCodeSymbol.transition, tail, htail⟩)

def PrimitivePipeline
    (accept reject : MachineDescription) :
    TapeCodePrimitive :=
  TapeCodePrimitive.compose
    (TapeCodePrimitive.compose
      (TapeCodePrimitive.compose
        (TapeCodePrimitive.compose
          (TapeCodePrimitive.compose
            AcceptProjectionPrimitive
            (FixedDescriptionBoundedSimulatorCode accept))
          AcceptMergePrimitive)
        RejectProjectionPrimitive)
      (FixedDescriptionBoundedSimulatorCode reject))
    RejectMergePrimitive

theorem primitivePipeline_transform_eq
    (accept reject : MachineDescription)
    (code : Word MachineCodeSymbol) :
    (PrimitivePipeline accept reject).transform code =
      (PairedRecognizerDovetailLayoutCode accept reject).transform code := by
  unfold PrimitivePipeline
  unfold TapeCodePrimitive.compose
  unfold PairedRecognizerDovetailLayoutCode
  unfold DovetailLayout.runCodePrimitive
  unfold DovetailLayout.runCode
  cases hdecode :
      DovetailLayout.decodeComplete code with
  | none =>
      simp [AcceptProjectionPrimitive, hdecode]
  | some L =>
      have hacceptMerge :
          AcceptMergePrimitive.transform
              (SimulatorLayout.encode
                (SimulatorLayout.run accept
                  (AcceptSimulatorLayout L).stage (AcceptSimulatorLayout L))) =
            some
              (DovetailLayout.encode
                (ConfigRunnerAfterAccept accept L)) := by
        simpa [AcceptSimulatorLayout] using
          AcceptMergePrimitive_encode_run accept L
      have hrejectMerge :
          RejectMergePrimitive.transform
              (SimulatorLayout.encode
                (SimulatorLayout.run reject
                  (RejectSimulatorLayout
                    (ConfigRunnerAfterAccept accept L)).stage
                  (RejectSimulatorLayout
                    (ConfigRunnerAfterAccept accept L)))) =
            some
              (DovetailLayout.encode
                (ConfigRunnerAfterReject reject
                  (ConfigRunnerAfterAccept accept L))) := by
        simpa [RejectSimulatorLayout] using
          RejectMergePrimitive_encode_run reject
            (ConfigRunnerAfterAccept accept L)
      simp [AcceptProjectionPrimitive, hdecode,
        fixedDescriptionBoundedSimulatorCode_encode, hacceptMerge,
        RejectProjectionPrimitive_encode, hrejectMerge,
        ConfigRunnerAfterReject_afterAccept, BoundedRunLayout]

/-!
The exact closed-handoff bounded-runner target is intentionally retired.
The padded/equivalence construction above proves {name}`outputCompiledSubroutine`,
which is the contract used by the high-level bounded-runner route.  Requiring
this runner to halt in the exact code-word handoff position is stronger than
normalized output and is not a valid construction target for shrinking layouts.
-/

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
