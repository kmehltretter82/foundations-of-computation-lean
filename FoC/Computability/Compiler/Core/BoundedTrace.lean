import FoC.Computability.Compiler.Core.Language

set_option doc.verso true

/-!
# Bounded trace compiler targets
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-!
## Paired-Recognizer Dovetail Compilers

The broad dovetail compiler above talks about arbitrary Lean traces.  The
paired-recognizer version below is the concrete Section 5.2 transition-level
handoff: both traces come from finite {lit}`MachineDescription` interpreters.
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

def PairedRecognizerBoundedDovetailTableRealizes
    (accept reject decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          boundedDovetailOutput
            accept reject w limit = some [b]

def PairedRecognizerBoundedDovetailTableCompilerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerBoundedDovetailTableRealizes accept reject decider

theorem dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    DovetailDescriptionCompilerPrinciple :=
  fun accept reject => hcompile (DovetailProgram accept reject)

theorem pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile
    (fun w n => accept.HaltsIn n w)
    (fun w n => reject.HaltsIn n w)

theorem pairedRecognizerDovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler hcompile)

theorem pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (hcompile :
      PairedRecognizerBoundedDovetailTableCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  cases hcompile accept reject with
  | intro decider hdecider =>
      exists decider
      constructor
      · exact hdecider.left
      · intro w b
        constructor
        · intro hhalt
          cases (hdecider.right w b).mp hhalt with
          | intro limit hlimit =>
              exists limit
              rwa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
                at hlimit
        · intro hprog
          cases hprog with
          | intro limit hlimit =>
              apply (hdecider.right w b).mpr
              exists limit
              rwa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]

theorem pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler
    (hcompile : PairedRecognizerDovetailDescriptionCompilerPrinciple) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨decider, hdecider⟩
  refine ⟨decider, ?_⟩
  constructor
  · exact hdecider.left
  · intro w b
    constructor
    · intro hhalt
      rcases (hdecider.right w b).mp hhalt with ⟨limit, hlimit⟩
      exact
        ⟨limit, by
          simpa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
            using! hlimit⟩
    · intro hlimit
      rcases hlimit with ⟨limit, hlimit⟩
      apply (hdecider.right w b).mpr
      exact
        ⟨limit, by
          simpa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
            using! hlimit⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_iff_pairedRecognizerDovetailDescriptionCompiler :
    PairedRecognizerBoundedDovetailTableCompilerConstruction <->
      PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  ⟨pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler,
    pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler⟩

/-!
## Fixed-Description Bounded Simulation

The bounded simulator contracts expose the exact configuration input and
Boolean result expected from a finite table.
-/

def FixedDescriptionBoundedSimulatorInput
    (L : SimulatorLayout) : Word Bool :=
  SimulatorLayout.asBoolInput L

def FixedDescriptionBoundedSimulatorOutput
    (D : MachineDescription)
    (L : SimulatorLayout) : Word Bool :=
  SimulatorLayout.asBoolInput
    (SimulatorLayout.run D L.stage L)

def FixedDescriptionBoundedSimulatorTableRealizes
    (D simulator : MachineDescription) : Prop :=
  simulator.WellFormed ∧
    forall L : SimulatorLayout,
      simulator.HaltsWithOutput
        (FixedDescriptionBoundedSimulatorInput L)
        (FixedDescriptionBoundedSimulatorOutput D L)

def FixedDescriptionBoundedSimulatorTableCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      FixedDescriptionBoundedSimulatorTableRealizes D simulator

/-!
## Checked Trace-Search Bundles

These structures package executable bounded checks for machine runs, encoded
configuration traces, and their combined Section 5.2 search surface.
-/

structure MachineBoundedTraceSearchConstruction : Prop where
  haltsInBool_correct :
    forall D : MachineDescription, forall n : Nat, forall w : Word Bool,
      haltsInBool D n w = true <-> D.HaltsIn n w
  hitsByBool_correct :
    forall D : MachineDescription, forall w : Word Bool, forall limit : Nat,
      hitsByBool D w limit = true <->
        exists n : Nat, n ≤ limit ∧ D.HaltsIn n w
  boundedDovetailOutput_correct :
    forall accept reject : MachineDescription,
      forall w : Word Bool, forall limit : Nat,
        boundedDovetailOutput accept reject w limit =
          (DovetailProgram
            (fun w n => accept.HaltsIn n w)
            (fun w n => reject.HaltsIn n w)).run w limit

structure EncodedConfigurationTraceSearchConstruction : Prop where
  checksEncodedRun_canonical :
    forall D : MachineDescription,
      forall c : Configuration,
      forall steps : Nat,
        checksEncodedRun D
          (encodeConfiguration c)
          steps
          (encodeConfiguration
            (D.runConfig steps c)) = true

structure BoundedTraceSearchConstruction : Prop where
  machine : MachineBoundedTraceSearchConstruction
  encodedConfiguration : EncodedConfigurationTraceSearchConstruction

theorem machineBoundedTraceSearchConstruction :
    MachineBoundedTraceSearchConstruction where
  haltsInBool_correct := haltsInBool_eq_true_iff
  hitsByBool_correct := hitsByBool_eq_true_iff
  boundedDovetailOutput_correct :=
    boundedDovetailOutput_eq_dovetailProgram_run

theorem encodedConfigurationTraceSearchConstruction :
    EncodedConfigurationTraceSearchConstruction where
  checksEncodedRun_canonical :=
    fun D c steps =>
      checksEncodedRun_encodeConfiguration D steps c

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
    (L : SimulatorLayout) :
    simulator.HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L) :=
  h.right L

theorem fixedDescriptionBoundedSimulatorOutput_run_hit
    (D : MachineDescription) (L : SimulatorLayout) :
    (SimulatorLayout.run D L.stage L).hit = true <->
      L.hit = true ∨
        exists n : Nat, n ≤ L.stage ∧
          (D.runConfig n L.config).state = D.halt :=
  SimulatorLayout.run_hit_eq_true_iff D L.stage L

/-!
## Canonical Bounded-Simulator Code

The code primitive maps canonical encoded simulator inputs to their encoded
Boolean bounded-run result.
-/

def FixedDescriptionBoundedSimulatorCode
    (D : MachineDescription) : TapeCodePrimitive :=
  SimulatorLayout.runCodePrimitive D

def FixedDescriptionBoundedSimulatorCodeRealizes
    (D : MachineDescription)
    (P : TapeCodePrimitive) : Prop :=
  forall L : SimulatorLayout,
    P.transform (SimulatorLayout.encode L) =
      some
        (SimulatorLayout.encode
          (SimulatorLayout.run D L.stage L))

theorem fixedDescriptionBoundedSimulatorCode_encode
    (D : MachineDescription) (L : SimulatorLayout) :
    (FixedDescriptionBoundedSimulatorCode D).transform
        (SimulatorLayout.encode L) =
      some
        (SimulatorLayout.encode
          (SimulatorLayout.run D L.stage L)) :=
  SimulatorLayout.runCodePrimitive_encode D L

theorem fixedDescriptionBoundedSimulatorCode_realizes
    (D : MachineDescription) :
    FixedDescriptionBoundedSimulatorCodeRealizes
      D (FixedDescriptionBoundedSimulatorCode D) :=
  fixedDescriptionBoundedSimulatorCode_encode D

theorem fixedDescriptionBoundedSimulatorCode_boolOutput
    (D : MachineDescription) (L : SimulatorLayout) :
    Option.map encodeCodeWordAsInput
        ((FixedDescriptionBoundedSimulatorCode D).transform
          (SimulatorLayout.encode L)) =
      some (FixedDescriptionBoundedSimulatorOutput D L) := by
  simp [fixedDescriptionBoundedSimulatorCode_encode,
    FixedDescriptionBoundedSimulatorOutput,
    SimulatorLayout.asBoolInput]

/-!
## Canonical Fixed-Step Code

The fixed-step primitive exposes one decoded table step in the same code-word
currency used by the bounded simulator.
-/

def FixedDescriptionStepCode
    (D : MachineDescription) : TapeCodePrimitive :=
  stepConfigurationCodePrimitive D

def FixedDescriptionStepCodeRealizes
    (D : MachineDescription)
    (P : TapeCodePrimitive) : Prop :=
  forall c : Configuration,
    P.transform (encodeConfiguration c) =
      some (encodeConfiguration (D.runConfig 1 c))

theorem fixedDescriptionStepCode_encode
    (D : MachineDescription) (c : Configuration) :
    (FixedDescriptionStepCode D).transform
        (encodeConfiguration c) =
      some (encodeConfiguration (D.runConfig 1 c)) :=
  stepConfigurationCodePrimitive_encodeConfiguration D c

theorem fixedDescriptionStepCode_realizes
    (D : MachineDescription) :
    FixedDescriptionStepCodeRealizes D (FixedDescriptionStepCode D) :=
  fixedDescriptionStepCode_encode D


end Computability
end FoC
