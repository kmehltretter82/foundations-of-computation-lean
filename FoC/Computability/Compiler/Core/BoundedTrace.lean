import FoC.Computability.Compiler.Core.Language

set_option doc.verso true

/-!
# Bounded trace compiler targets
-/

namespace FoC
namespace Computability

open Languages

/-
The broad dovetail compiler above talks about arbitrary Lean traces.  The
paired-recognizer version below is the concrete Section 5.2 transition-level
handoff: both traces come from finite `MachineDescription` interpreters.
It is still a construction principle, but it names the exact uniform machine
description that a real dovetailing compiler must build.
-/

def PairedRecognizerDovetailDescriptionCompilerPrinciple : Prop :=
  forall accept reject : MachineDescription,
    exists D : MachineDescription,
      BoolProgramCompiledByDescription
        (DovetailProgram
          (fun w n => accept.HaltsIn n w)
          (fun w n => reject.HaltsIn n w)) D

def FiniteSourcePairedRecognizerDovetailCompilerConstruction : Prop :=
  PairedRecognizerDovetailDescriptionCompilerPrinciple

def PairedRecognizerBoundedDovetailTableRealizes
    (accept reject decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          MachineDescription.boundedDovetailOutput
            accept reject w limit = some [b]

def PairedRecognizerBoundedDovetailTableCompilerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerBoundedDovetailTableRealizes accept reject decider

def FiniteSourcePairedRecognizerBoundedDovetailTableCompilerConstruction :
    Prop :=
  PairedRecognizerBoundedDovetailTableCompilerConstruction

def FixedDescriptionBoundedSimulatorInput
    (L : MachineDescription.SimulatorLayout) : Word Bool :=
  MachineDescription.SimulatorLayout.asBoolInput L

def FixedDescriptionBoundedSimulatorOutput
    (D : MachineDescription)
    (L : MachineDescription.SimulatorLayout) : Word Bool :=
  MachineDescription.SimulatorLayout.asBoolInput
    (MachineDescription.SimulatorLayout.run D L.stage L)

def FixedDescriptionBoundedSimulatorTableRealizes
    (D simulator : MachineDescription) : Prop :=
  simulator.WellFormed ∧
    forall L : MachineDescription.SimulatorLayout,
      simulator.HaltsWithOutput
        (FixedDescriptionBoundedSimulatorInput L)
        (FixedDescriptionBoundedSimulatorOutput D L)

def FixedDescriptionBoundedSimulatorTableCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      FixedDescriptionBoundedSimulatorTableRealizes D simulator

structure MachineBoundedTraceSearchConstruction : Prop where
  haltsInBool_correct :
    forall D : MachineDescription, forall n : Nat, forall w : Word Bool,
      MachineDescription.haltsInBool D n w = true <-> D.HaltsIn n w
  hitsByBool_correct :
    forall D : MachineDescription, forall w : Word Bool, forall limit : Nat,
      MachineDescription.hitsByBool D w limit = true <->
        exists n : Nat, n ≤ limit ∧ D.HaltsIn n w
  boundedDovetailOutput_correct :
    forall accept reject : MachineDescription,
      forall w : Word Bool, forall limit : Nat,
        MachineDescription.boundedDovetailOutput accept reject w limit =
          (DovetailProgram
            (fun w n => accept.HaltsIn n w)
            (fun w n => reject.HaltsIn n w)).run w limit

structure EncodedConfigurationTraceSearchConstruction : Prop where
  checksEncodedRun_canonical :
    forall D : MachineDescription,
      forall c : MachineDescription.Configuration,
      forall steps : Nat,
        MachineDescription.checksEncodedRun D
          (MachineDescription.encodeConfiguration c)
          steps
          (MachineDescription.encodeConfiguration
            (D.runConfig steps c)) = true

structure BoundedTraceSearchConstruction : Prop where
  machine : MachineBoundedTraceSearchConstruction
  encodedConfiguration : EncodedConfigurationTraceSearchConstruction

theorem machineBoundedTraceSearchConstruction :
    MachineBoundedTraceSearchConstruction where
  haltsInBool_correct := MachineDescription.haltsInBool_eq_true_iff
  hitsByBool_correct := MachineDescription.hitsByBool_eq_true_iff
  boundedDovetailOutput_correct :=
    MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run

theorem encodedConfigurationTraceSearchConstruction :
    EncodedConfigurationTraceSearchConstruction where
  checksEncodedRun_canonical := by
    intro D c steps
    exact MachineDescription.checksEncodedRun_encodeConfiguration D steps c

theorem boundedTraceSearchConstruction :
    BoundedTraceSearchConstruction where
  machine := machineBoundedTraceSearchConstruction
  encodedConfiguration := encodedConfigurationTraceSearchConstruction

theorem fixedDescriptionBoundedSimulatorTableRealizes_wellFormed
    {D simulator : MachineDescription}
    (h : FixedDescriptionBoundedSimulatorTableRealizes D simulator) :
    simulator.WellFormed :=
  h.left

theorem fixedDescriptionBoundedSimulatorTableRealizes_output
    {D simulator : MachineDescription}
    (h : FixedDescriptionBoundedSimulatorTableRealizes D simulator)
    (L : MachineDescription.SimulatorLayout) :
    simulator.HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L) :=
  h.right L

theorem fixedDescriptionBoundedSimulatorOutput_run_hit
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    (MachineDescription.SimulatorLayout.run D L.stage L).hit = true <->
      L.hit = true ∨
        exists n : Nat, n ≤ L.stage ∧
          (D.runConfig n L.config).state = D.halt :=
  MachineDescription.SimulatorLayout.run_hit_eq_true_iff D L.stage L

def FixedDescriptionBoundedSimulatorCode
    (D : MachineDescription) : MachineDescription.TapeCodePrimitive :=
  MachineDescription.SimulatorLayout.runCodePrimitive D

def FixedDescriptionBoundedSimulatorCodeRealizes
    (D : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    P.transform (MachineDescription.SimulatorLayout.encode L) =
      some
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run D L.stage L))

theorem fixedDescriptionBoundedSimulatorCode_encode
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    (FixedDescriptionBoundedSimulatorCode D).transform
        (MachineDescription.SimulatorLayout.encode L) =
      some
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run D L.stage L)) :=
  MachineDescription.SimulatorLayout.runCodePrimitive_encode D L

theorem fixedDescriptionBoundedSimulatorCode_realizes
    (D : MachineDescription) :
    FixedDescriptionBoundedSimulatorCodeRealizes
      D (FixedDescriptionBoundedSimulatorCode D) := by
  intro L
  exact fixedDescriptionBoundedSimulatorCode_encode D L

theorem fixedDescriptionBoundedSimulatorCode_boolOutput
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    Option.map MachineDescription.encodeCodeWordAsInput
        ((FixedDescriptionBoundedSimulatorCode D).transform
          (MachineDescription.SimulatorLayout.encode L)) =
      some (FixedDescriptionBoundedSimulatorOutput D L) := by
  simp [fixedDescriptionBoundedSimulatorCode_encode,
    FixedDescriptionBoundedSimulatorOutput,
    MachineDescription.SimulatorLayout.asBoolInput]

def FixedDescriptionStepCode
    (D : MachineDescription) : MachineDescription.TapeCodePrimitive :=
  MachineDescription.stepConfigurationCodePrimitive D

def FixedDescriptionStepCodeRealizes
    (D : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall c : MachineDescription.Configuration,
    P.transform (MachineDescription.encodeConfiguration c) =
      some (MachineDescription.encodeConfiguration (D.runConfig 1 c))

theorem fixedDescriptionStepCode_encode
    (D : MachineDescription) (c : MachineDescription.Configuration) :
    (FixedDescriptionStepCode D).transform
        (MachineDescription.encodeConfiguration c) =
      some (MachineDescription.encodeConfiguration (D.runConfig 1 c)) :=
  MachineDescription.stepConfigurationCodePrimitive_encodeConfiguration D c

theorem fixedDescriptionStepCode_realizes
    (D : MachineDescription) :
    FixedDescriptionStepCodeRealizes D (FixedDescriptionStepCode D) := by
  intro c
  exact fixedDescriptionStepCode_encode D c


end Computability
end FoC
