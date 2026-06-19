import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Basic

set_option doc.verso true

/-!
# Bounded recognizer-configuration runner construction

The bridge below remains useful once a closed handoff implementation of
{name (full := FoC.Computability.PairedRecognizerDovetailLayoutCode)}`PairedRecognizerDovetailLayoutCode`
is available without importing this bounded-runner assembly.  The finite
construction leaf is kept here to avoid circular imports.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

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

theorem acceptRejectConfigRunnerConstruction_of_closedHandoffConstruction
    (h :
      PairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction) :
    AcceptRejectConfigRunnerConstruction := by
  intro accept reject
  rcases h accept reject with ⟨closed, hclosed⟩
  exact
    ⟨ConfigRunnerFromClosedHandoff closed,
      configRunnerFromClosedHandoff_spec hclosed⟩

theorem acceptRejectConfigRunnerConstruction_scaffold :
    AcceptRejectConfigRunnerConstruction := by
  intro accept reject
  sorry

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
