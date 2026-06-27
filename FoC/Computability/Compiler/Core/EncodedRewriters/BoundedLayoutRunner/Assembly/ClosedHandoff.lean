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
  let identity := MachineDescription.ExactIdentityDescription
  let parserId :=
    MachineDescription.seqSubroutine parser identity Direction.right
  let runner :=
    MachineDescription.seqSubroutine parserId configRunner Direction.left
  refine ⟨runner, ?_⟩
  have hparserReady : parser.SubroutineReady := hparser.left
  have hconfigReady : configRunner.SubroutineReady := hconfig.left
  have hidReady : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hparserIdReady : parserId.SubroutineReady :=
    MachineDescription.seqSubroutine_subroutineReady
      hparserReady hidReady
  have hrunnerReady : runner.SubroutineReady :=
    MachineDescription.seqSubroutine_subroutineReady
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
        MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
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
      rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape h_halt with ⟨nB, hB⟩
      refine ⟨nB, ?_⟩
      simpa [parsedLayoutCheckedTape_move_left_move_right L] using hB
    have h_runner_halts :
        runner.HaltsWithTape
          (ParsedLayoutBits L)
          Tactual := by
      exact
        MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
          (A := parserId) (B := configRunner)
          (handoffMove := Direction.left)
          hparserIdReady hconfigReady
          hparserId hconfigReach
    exact ⟨Tactual, h_runner_halts, h_eq⟩
  · intro code T hhalt_equiv
    rcases hhalt_equiv with ⟨Tactual, hhalt, hT_equiv⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := parserId) (B := configRunner)
          (handoffMove := Direction.left)
          hparserIdReady hconfigReady
          (by simpa [runner] using hhalt) with
      ⟨TconfigInLeft, hparserIdHalt, hconfigHalt⟩
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
    have hTconfigInLeft :
        TconfigInLeft =
          Tape.move Direction.right (ParsedLayoutCheckedTape L) := by
      have hcfg :
          ({ state := identity.halt
             tape := Tape.move Direction.right Tparser } :
            MachineDescription.Configuration) =
          { state := identity.halt
            tape := TconfigInLeft } := by
        simpa [identity] using
          ((CommonGround.Identity.exactIdentityDescription_runConfig_from_start
              nIdParser
              (Tape.move Direction.right Tparser)).symm.trans
            hIdParser)
      simpa [hTparser] using
        (congrArg MachineDescription.Configuration.tape hcfg).symm
    have hconfigRunStart :
        configRunner.HaltsFromTape
          (Tape.move Direction.left TconfigInLeft)
          Tactual := by
      rcases hconfigHalt with ⟨n, hn⟩
      exact ⟨n, ⟨congrArg MachineDescription.Configuration.state hn, congrArg MachineDescription.Configuration.tape hn⟩⟩
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

def PrimitivePipeline
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.TapeCodePrimitive.compose
    (MachineDescription.TapeCodePrimitive.compose
      (MachineDescription.TapeCodePrimitive.compose
        (MachineDescription.TapeCodePrimitive.compose
          (MachineDescription.TapeCodePrimitive.compose
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
  unfold MachineDescription.TapeCodePrimitive.compose
  unfold PairedRecognizerDovetailLayoutCode
  unfold MachineDescription.DovetailLayout.runCodePrimitive
  unfold MachineDescription.DovetailLayout.runCode
  cases hdecode :
      MachineDescription.DovetailLayout.decodeComplete code with
  | none =>
      simp [AcceptProjectionPrimitive, hdecode]
  | some L =>
      have hacceptMerge :
          AcceptMergePrimitive.transform
              (MachineDescription.SimulatorLayout.encode
                (MachineDescription.SimulatorLayout.run accept
                  (AcceptSimulatorLayout L).stage (AcceptSimulatorLayout L))) =
            some
              (MachineDescription.DovetailLayout.encode
                (ConfigRunnerAfterAccept accept L)) := by
        simpa [AcceptSimulatorLayout] using
          AcceptMergePrimitive_encode_run accept L
      have hrejectMerge :
          RejectMergePrimitive.transform
              (MachineDescription.SimulatorLayout.encode
                (MachineDescription.SimulatorLayout.run reject
                  (RejectSimulatorLayout
                    (ConfigRunnerAfterAccept accept L)).stage
                  (RejectSimulatorLayout
                    (ConfigRunnerAfterAccept accept L)))) =
            some
              (MachineDescription.DovetailLayout.encode
                (ConfigRunnerAfterReject reject
                  (ConfigRunnerAfterAccept accept L))) := by
        simpa [RejectSimulatorLayout] using
          RejectMergePrimitive_encode_run reject
            (ConfigRunnerAfterAccept accept L)
      simp [AcceptProjectionPrimitive, hdecode,
        fixedDescriptionBoundedSimulatorCode_encode, hacceptMerge,
        RejectProjectionPrimitive_encode, hrejectMerge,
        ConfigRunnerAfterReject_afterAccept, BoundedRunLayout]

/-- Direct finite-machine leaf for the closed-handoff bounded runner.

The older decomposition through {name}`PrimitivePipeline` required exact
closed-handoff merge primitives.  That split is too strong: the merge phases
return tapes equivalent to the parsed dovetail layout, while preserving
simulator-layout scratch structure.  The public closed-handoff theorem is
therefore kept as one finite-machine construction obligation.
-/
theorem closedHandoffCompiledSubroutine
    (accept reject : MachineDescription) :
    exists runner : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner tapeCodePrimitiveCodeWordHandoffMove := by
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
