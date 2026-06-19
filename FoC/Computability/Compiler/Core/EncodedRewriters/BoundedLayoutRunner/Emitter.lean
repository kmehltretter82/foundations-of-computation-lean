import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner

set_option doc.verso true

/-!
# Bounded-layout output emitter phase

After the recognizer configurations have been advanced, the emitter phase
rewrites the preserved canonical layout tape into the right-shifted output tape
required by the encoded rewriter handoff contract.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def OutputEmitterForwardSpec
    (accept reject emitter : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    emitter.HaltsWithTape
      (ConfigRunnerOutputBits accept reject L)
      (OutputTape accept reject L)

def OutputEmitterClosedSpec
    (accept reject emitter : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
  forall T : Tape Bool,
    emitter.HaltsWithTape
        (ConfigRunnerOutputBits accept reject L) T ->
      T = OutputTape accept reject L

def OutputEmitterSpec
    (accept reject emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    OutputEmitterForwardSpec accept reject emitter ∧
      OutputEmitterClosedSpec accept reject emitter

def OutputEmitterConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists emitter : MachineDescription,
      OutputEmitterSpec accept reject emitter

def OutputEmitterDescription : MachineDescription :=
  (MachineDescription.Fragment.handoff Direction.right).toDescription

theorem outputEmitterDescription_ready :
    ReadySpec OutputEmitterDescription := by
  exact
    MachineDescription.Fragment.toDescription_subroutineReady
      (MachineDescription.Fragment.handoff_wellFormed Direction.right)

theorem outputEmitterDescription_haltsWithTape
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    OutputEmitterDescription.HaltsWithTape
      (ConfigRunnerOutputBits accept reject L)
      (OutputTape accept reject L) := by
  refine ⟨1, ?_⟩
  change
    (OutputEmitterDescription.runConfig 1
      { state := OutputEmitterDescription.start
        tape := Tape.input (ConfigRunnerOutputBits accept reject L) }).state =
        OutputEmitterDescription.halt ∧
      (OutputEmitterDescription.runConfig 1
        { state := OutputEmitterDescription.start
          tape := Tape.input (ConfigRunnerOutputBits accept reject L) }).tape =
        OutputTape accept reject L
  rw [show
      OutputEmitterDescription.runConfig 1
          { state := OutputEmitterDescription.start
            tape := Tape.input (ConfigRunnerOutputBits accept reject L) } =
        { state := OutputEmitterDescription.halt
          tape :=
            Tape.move Direction.right
              (Tape.input (ConfigRunnerOutputBits accept reject L)) } by
      exact
        MachineDescription.Fragment.handoff_runConfig_one Direction.right
          (Tape.input (ConfigRunnerOutputBits accept reject L))]
  constructor
  · rfl
  · rfl

theorem outputEmitterConstruction_scaffold :
    OutputEmitterConstruction := by
  intro accept reject
  refine ⟨OutputEmitterDescription, ?_⟩
  constructor
  · exact outputEmitterDescription_ready
  constructor
  · intro L
    exact outputEmitterDescription_haltsWithTape accept reject L
  · intro L T hhalt
    rcases hhalt with ⟨n, hn⟩
    have hfirst :=
      MachineDescription.firstReaches_halt_of_runConfig_eq
        outputEmitterDescription_ready.right
        (n := n)
        (c :=
          OutputEmitterDescription.initial
            (ConfigRunnerOutputBits accept reject L))
        (T := T)
        (by
          exact
            (show
              OutputEmitterDescription.runConfig n
                  (OutputEmitterDescription.initial
                    (ConfigRunnerOutputBits accept reject L)) =
                { state := OutputEmitterDescription.halt, tape := T } from
              by
                cases hn with
                | intro hstate htape =>
                    cases hcfg :
                      OutputEmitterDescription.runConfig n
                        (OutputEmitterDescription.initial
                          (ConfigRunnerOutputBits accept reject L))
                    case mk state tape =>
                      have hstate' : state = OutputEmitterDescription.halt := by
                        simpa [hcfg] using hstate
                      have htape' : tape = T := by
                        simpa [hcfg] using htape
                      simp [hstate', htape']))
    rcases hfirst with ⟨m, hmle, hmrun, hmfirst⟩
    have hm_ne_zero : m ≠ 0 := by
      intro hm0
      have hstartNotHalt :
          OutputEmitterDescription.start ≠ OutputEmitterDescription.halt := by
        change
          (MachineDescription.Fragment.handoff Direction.right).entry ≠
            (MachineDescription.Fragment.handoff Direction.right).exit
        decide
      have hstate :
          (OutputEmitterDescription.runConfig 0
            (OutputEmitterDescription.initial
              (ConfigRunnerOutputBits accept reject L))).state =
            OutputEmitterDescription.halt := by
        rw [hm0] at hmrun
        exact congrArg MachineDescription.Configuration.state hmrun
      exact hstartNotHalt (by simpa [MachineDescription.initial] using hstate)
    have hnotBefore : m = 1 := by
      have hm_le_one : m ≤ 1 := by
        cases m with
        | zero => omega
        | succ m' =>
            cases m' with
            | zero => omega
            | succ m'' =>
                have hbad :=
                  hmfirst 1 (by omega)
                have hone :
                    (OutputEmitterDescription.runConfig 1
                      (OutputEmitterDescription.initial
                        (ConfigRunnerOutputBits accept reject L))).state =
                      OutputEmitterDescription.halt := by
                  change
                    (OutputEmitterDescription.runConfig 1
                      { state := OutputEmitterDescription.start
                        tape :=
                          Tape.input
                            (ConfigRunnerOutputBits accept reject L) }).state =
                      OutputEmitterDescription.halt
                  exact
                    congrArg MachineDescription.Configuration.state
                      (show
                      OutputEmitterDescription.runConfig 1
                          { state := OutputEmitterDescription.start
                            tape :=
                              Tape.input
                                (ConfigRunnerOutputBits accept reject L) } =
                        { state := OutputEmitterDescription.halt
                          tape :=
                            Tape.move Direction.right
                              (Tape.input
                                (ConfigRunnerOutputBits accept reject L)) } by
                      exact
                        MachineDescription.Fragment.handoff_runConfig_one
                          Direction.right
                          (Tape.input
                            (ConfigRunnerOutputBits accept reject L)))
                exact False.elim (hbad hone)
      omega
    have hrun1 :
        OutputEmitterDescription.runConfig 1
            (OutputEmitterDescription.initial
              (ConfigRunnerOutputBits accept reject L)) =
          { state := OutputEmitterDescription.halt, tape := T } := by
      simpa [hnotBefore] using hmrun
    have hout :
        OutputEmitterDescription.runConfig 1
            (OutputEmitterDescription.initial
              (ConfigRunnerOutputBits accept reject L)) =
          { state := OutputEmitterDescription.halt
            tape := OutputTape accept reject L } := by
      change
        OutputEmitterDescription.runConfig 1
            { state := OutputEmitterDescription.start
              tape := Tape.input (ConfigRunnerOutputBits accept reject L) } =
          { state := OutputEmitterDescription.halt
            tape := OutputTape accept reject L }
      rw [show
          OutputEmitterDescription.runConfig 1
              { state := OutputEmitterDescription.start
                tape := Tape.input (ConfigRunnerOutputBits accept reject L) } =
            { state := OutputEmitterDescription.halt
              tape :=
                Tape.move Direction.right
                  (Tape.input (ConfigRunnerOutputBits accept reject L)) } by
          exact
            MachineDescription.Fragment.handoff_runConfig_one Direction.right
              (Tape.input (ConfigRunnerOutputBits accept reject L))]
      rfl
    exact congrArg MachineDescription.Configuration.tape (hrun1.symm.trans hout)

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
