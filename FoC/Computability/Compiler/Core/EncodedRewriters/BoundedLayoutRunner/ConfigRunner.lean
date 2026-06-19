import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser

set_option doc.verso true

/-!
# Bounded recognizer-configuration runner phase

The runner phase starts from a validated layout tape, simulates both stored
recognizer configurations for the layout stage, and preserves the exact updated
layout needed by the emitter phase.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def BoundedRunLayout
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    MachineDescription.DovetailLayout :=
  MachineDescription.DovetailLayout.run accept reject L.stage L

def ConfigRunnerOutputTape
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  ParsedLayoutTape (BoundedRunLayout accept reject L)

def ConfigRunnerOutputBits
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  ParsedLayoutBits (BoundedRunLayout accept reject L)

def AcceptRejectConfigRunnerForwardSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    runner.HaltsWithTape
      (ParsedLayoutBits L)
      (ConfigRunnerOutputTape accept reject L)

def AcceptRejectConfigRunnerClosedSpec
    (accept reject runner : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
  forall T : Tape Bool,
    runner.HaltsWithTape (ParsedLayoutBits L) T ->
      T = ConfigRunnerOutputTape accept reject L

def AcceptRejectConfigRunnerSpec
    (accept reject runner : MachineDescription) : Prop :=
  ReadySpec runner ∧
    AcceptRejectConfigRunnerForwardSpec accept reject runner ∧
      AcceptRejectConfigRunnerClosedSpec accept reject runner

def AcceptRejectConfigRunnerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      AcceptRejectConfigRunnerSpec accept reject runner

def ConfigRunnerFromClosedHandoff
    (closed : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine closed
    MachineDescription.ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem exactIdentityDescription_reaches_configRunner
    (T : Tape Bool) :
    exists n : Nat,
      MachineDescription.ExactIdentityDescription.runConfig n
          { state := MachineDescription.ExactIdentityDescription.start
            tape := T } =
        { state := MachineDescription.ExactIdentityDescription.halt
          tape := T } :=
  ⟨0, rfl⟩

theorem exactIdentityDescription_runConfig_from_start_configRunner
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

theorem configRunnerFromClosedHandoff_spec
    {accept reject closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    AcceptRejectConfigRunnerSpec accept reject
      (ConfigRunnerFromClosedHandoff closed) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hidentityReady : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        hclosedReady hidentityReady
  constructor
  · intro L
    have htransform :
        (PairedRecognizerDovetailLayoutCode accept reject).transform
            (MachineDescription.DovetailLayout.encode L) =
          some
            (MachineDescription.DovetailLayout.encode
              (BoundedRunLayout accept reject L)) := by
      simpa [PairedRecognizerDovetailLayoutCode,
        BoundedRunLayout] using
        MachineDescription.DovetailLayout.runCodePrimitive_encode
          accept reject L
    rcases
        (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
          hclosed).right
          (MachineDescription.DovetailLayout.encode L)
          (MachineDescription.DovetailLayout.encode
            (BoundedRunLayout accept reject L))
          htransform with
      ⟨Tmid, hclosedHalt, hhandoff⟩
    have hidentityReach :
        exists nB : Nat,
          identity.runConfig nB
              { state := identity.start
                tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } =
            { state := identity.halt
              tape := ConfigRunnerOutputTape accept reject L } := by
      refine ⟨0, ?_⟩
      have hinput :
          Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid =
            ConfigRunnerOutputTape accept reject L := by
        simpa [ConfigRunnerOutputTape, ParsedLayoutTape,
          ParsedLayoutBits, ConfigRunnerOutputBits] using hhandoff
      rw [hinput]
      rfl
    simpa [ConfigRunnerFromClosedHandoff, identity,
      tapeCodePrimitiveCodeWordHandoffMove] using
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := closed) (B := identity)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        hclosedReady hidentityReady hclosedHalt hidentityReach
  · intro L T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := closed) (B := identity)
          (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
          hclosedReady hidentityReady
          (by simpa [ConfigRunnerFromClosedHandoff, identity] using hhalt) with
      ⟨Tmid, hclosedHalt, hidentityReach⟩
    rcases
        hclosed.right
          (MachineDescription.DovetailLayout.encode L)
          Tmid hclosedHalt with
      ⟨out, htransform, _hnormalized, hhandoff⟩
    have htransformExpected :
        (PairedRecognizerDovetailLayoutCode accept reject).transform
            (MachineDescription.DovetailLayout.encode L) =
          some
            (MachineDescription.DovetailLayout.encode
              (BoundedRunLayout accept reject L)) := by
      simpa [PairedRecognizerDovetailLayoutCode,
        BoundedRunLayout] using
        MachineDescription.DovetailLayout.runCodePrimitive_encode
          accept reject L
    have hout :
        out =
          MachineDescription.DovetailLayout.encode
            (BoundedRunLayout accept reject L) := by
      rw [htransformExpected] at htransform
      cases htransform
      rfl
    rcases hidentityReach with ⟨nB, hidentityRun⟩
    have hT :
        T = Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid := by
      have hcfg :
          ({ state := identity.halt
             tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } :
            MachineDescription.Configuration) =
          { state := identity.halt, tape := T } := by
        simpa [identity] using
          ((exactIdentityDescription_runConfig_from_start_configRunner
              nB (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid)).symm.trans
            hidentityRun)
      exact (congrArg MachineDescription.Configuration.tape hcfg).symm
    rw [hT]
    simpa [hout, ConfigRunnerOutputTape, ParsedLayoutTape,
      ParsedLayoutBits, ConfigRunnerOutputBits] using hhandoff

theorem acceptRejectConfigRunnerConstruction_scaffold :
    AcceptRejectConfigRunnerConstruction := by
  intro accept reject
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
