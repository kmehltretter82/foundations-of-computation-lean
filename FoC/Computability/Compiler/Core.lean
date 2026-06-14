import FoC.Computability.Compiler.DescriptionExecution

set_option doc.verso true

/-!
# Description-backed compiler boundaries
-/

namespace FoC
namespace Computability

open Languages

/-!
## Description-backed language recognition and decision
-/

def MachineDescriptionAcceptsLanguage
    (D : MachineDescription) (L : Language Bool) : Prop :=
  D.WellFormed ∧ forall w : Word Bool, D.HaltsOnInput w <-> w ∈ L

def MachineDescriptionDecidesLanguage
    (D : MachineDescription) (L : Language Bool) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool,
      (w ∈ L -> D.HaltsWithOutput w [true]) ∧
        (¬ w ∈ L -> D.HaltsWithOutput w [false])

theorem machineDescriptionAcceptsLanguage_turingAcceptable
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionAcceptsLanguage D L) :
    TuringAcceptable L := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists fun b : Bool => b
  intro w
  rw [encodeWord_id]
  exact Iff.trans (MachineDescription.toTuringMachine_haltsOnInput_iff
    h.left w) (h.right w)

theorem machineDescriptionDecidesLanguage_turingDecidable
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionDecidesLanguage D L) :
    TuringDecidable L := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists fun b : Bool => b
  exists false
  exists true
  intro w
  constructor
  · intro hw
    rw [encodeWord_id]
    exact (MachineDescription.toTuringMachine_haltsWithOutput_iff
      h.left w [true]).mpr ((h.right w).left hw)
  · intro hw
    rw [encodeWord_id]
    exact (MachineDescription.toTuringMachine_haltsWithOutput_iff
      h.left w [false]).mpr ((h.right w).right hw)

/-!
## Staged-program compiler predicates
-/

def ProgramCompiledByDescription
    (P : StagedProgram Bool Unit) (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool,
      D.HaltsOnInput w <-> ProgramHaltsWithOutput P w []

theorem programCompiledByDescription_of_same_accepted_language
    {P Q : StagedProgram Bool Unit} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramAcceptsLanguage P L)
    (hQ : ProgramAcceptsLanguage Q L)
    (hcompile : ProgramCompiledByDescription P D) :
    ProgramCompiledByDescription Q D := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w)
      (Iff.trans (hP w) (Iff.symm (hQ w)))

def BoolProgramCompiledByDescription
    (P : StagedProgram Bool Bool) (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      D.HaltsWithOutput w [b] <-> ProgramHaltsWithOutput P w [b]

def ProgramAcceptableByDescription (L : Language Bool) : Prop :=
  exists P : StagedProgram Bool Unit, exists D : MachineDescription,
    ProgramAcceptsLanguage P L ∧ ProgramCompiledByDescription P D

def ProgramBoolDecidableByDescription (L : Language Bool) : Prop :=
  exists P : StagedProgram Bool Bool, exists D : MachineDescription,
    ProgramBoolDecides P L ∧ BoolProgramCompiledByDescription P D

theorem programCompiledByDescription_acceptsLanguage
    {P : StagedProgram Bool Unit} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramAcceptsLanguage P L)
    (hcompile : ProgramCompiledByDescription P D) :
    MachineDescriptionAcceptsLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w) (hP w)

theorem boolProgramCompiledByDescription_decidesLanguage
    {P : StagedProgram Bool Bool} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramBoolDecides P L)
    (hcompile : BoolProgramCompiledByDescription P D) :
    MachineDescriptionDecidesLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    constructor
    · intro hw
      exact (hcompile.right w true).mpr ((hP.left w).mpr hw)
    · intro hw
      exact (hcompile.right w false).mpr ((hP.right w).mpr hw)

theorem programAcceptableByDescription_turingAcceptable
    {L : Language Bool}
    (h : ProgramAcceptableByDescription L) :
    TuringAcceptable L := by
  cases h with
  | intro P hP =>
      cases hP with
      | intro D hD =>
          exact machineDescriptionAcceptsLanguage_turingAcceptable
            (programCompiledByDescription_acceptsLanguage hD.left hD.right)

theorem programBoolDecidableByDescription_turingDecidable
    {L : Language Bool}
    (h : ProgramBoolDecidableByDescription L) :
    TuringDecidable L := by
  cases h with
  | intro P hP =>
      cases hP with
      | intro D hD =>
          exact machineDescriptionDecidesLanguage_turingDecidable
            (boolProgramCompiledByDescription_decidesLanguage hD.left hD.right)

def DescriptionProgramAcceptorCompilationPrinciple : Prop :=
  forall P : StagedProgram Bool Unit,
    exists D : MachineDescription, ProgramCompiledByDescription P D

/-
The next aliases separate semantic compiler assumptions from finite-source
compiler targets.  A semantic assumption quantifies over arbitrary Lean staged
programs or traces.  A finite-source construction has concrete finite data as
input, such as a supplied {name}`MachineDescription`.
-/

def SemanticDescriptionAcceptorCompilerAssumption : Prop :=
  DescriptionProgramAcceptorCompilationPrinciple

theorem programAcceptableByDescription_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple)
    {L : Language Bool}
    (h : ProgramAcceptable L) :
    ProgramAcceptableByDescription L := by
  rcases h with ⟨P, hP⟩
  rcases hcompile P with ⟨D, hD⟩
  exact ⟨P, D, hP, hD⟩

theorem recursivelyEnumerable_programAcceptableByDescription_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple)
    {L : Language Bool}
    (h : RecursivelyEnumerable L) :
    ProgramAcceptableByDescription L :=
  programAcceptableByDescription_of_descriptionCompiler hcompile
    (recursivelyEnumerable_programAcceptable h)

def DescriptionProgramBoolDeciderCompilationPrinciple : Prop :=
  forall P : StagedProgram Bool Bool,
    exists D : MachineDescription, BoolProgramCompiledByDescription P D

def SemanticDescriptionBoolDeciderCompilerAssumption : Prop :=
  DescriptionProgramBoolDeciderCompilationPrinciple

def DovetailDescriptionCompilerPrinciple : Prop :=
  forall accept reject : Word Bool -> Nat -> Prop,
    exists D : MachineDescription,
      BoolProgramCompiledByDescription (DovetailProgram accept reject) D

def SemanticDovetailDescriptionCompilerAssumption : Prop :=
  DovetailDescriptionCompilerPrinciple

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

def PairedRecognizerDovetailLayoutCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.runCodePrimitive accept reject

def PairedRecognizerDovetailStageInputCode
    (w : Word Bool) (stage : Nat) : Word MachineCodeSymbol :=
  MachineDescription.DovetailLayout.stageInputCode w stage

def PairedRecognizerDovetailInitialLayoutCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.initialCodePrimitive accept reject

def PairedRecognizerDovetailOutputCode :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.outputCodePrimitive

def PairedRecognizerDovetailTotalOutputCode :
    MachineDescription.TapeCodePrimitive where
  transform := fun tokens =>
    match MachineDescription.DovetailLayout.decodeComplete tokens with
    | none => none
    | some L =>
        some
          (MachineDescription.encodeBoolWord
            (MachineDescription.DovetailLayout.outputWordFromHits L))

def PairedRecognizerDovetailStageAttemptCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.stageAttemptCodePrimitive accept reject

def PairedRecognizerDovetailTotalStageAttemptCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.totalStageAttemptCodePrimitive
    accept reject

def PairedRecognizerDovetailControllerLayoutCode
    (w : Word Bool) (stage : Nat) (result : Word Bool) :
    Word MachineCodeSymbol :=
  MachineDescription.DovetailControllerLayout.encode
    { input := w, stage := stage, result := result }

def PairedRecognizerDovetailControllerInitialCode
    (w : Word Bool) : Word MachineCodeSymbol :=
  MachineDescription.DovetailControllerLayout.encode
    (MachineDescription.DovetailControllerLayout.initial w)

def PairedRecognizerDovetailControllerStageInputCode
    (C : MachineDescription.DovetailControllerLayout) :
    Word MachineCodeSymbol :=
  MachineDescription.DovetailControllerLayout.stageInputCode C

def PairedRecognizerDovetailControllerStageInputCodePrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun tokens =>
    match MachineDescription.DovetailControllerLayout.decodeComplete tokens with
    | none => none
    | some C => some (PairedRecognizerDovetailControllerStageInputCode C)

def PairedRecognizerDovetailControllerRawOutput
    (result : Word Bool) : Option (Word Bool) :=
  MachineDescription.DovetailControllerLayout.rawOutput? result

def PairedRecognizerDovetailControllerRawOutputCode :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailControllerLayout.rawOutputCodePrimitive

def PairedRecognizerDovetailControllerResultEmitterCode :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailControllerLayout.emitResultCodePrimitive

def PairedRecognizerDovetailControllerResultContinueCode :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailControllerLayout.continueResultCodePrimitive

def PairedRecognizerDovetailControllerContinueCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailControllerLayout.continueCodePrimitive
    accept reject

def PairedRecognizerDovetailControllerEmitCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailControllerLayout.emitCodePrimitive
    accept reject

def PairedRecognizerDovetailTotalThenRawOutputCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.TapeCodePrimitive.compose
    (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
    PairedRecognizerDovetailControllerRawOutputCode

def PairedRecognizerDovetailTotalStageAttemptSourceCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.TapeCodePrimitive.compose
    (MachineDescription.TapeCodePrimitive.compose
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      (PairedRecognizerDovetailLayoutCode accept reject))
    PairedRecognizerDovetailTotalOutputCode

def PairedRecognizerDovetailControllerRawOutputCodeRealizes
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall result : Word Bool,
    P.transform (MachineDescription.encodeBoolWord result) =
      Option.map MachineDescription.encodeBoolWord
        (PairedRecognizerDovetailControllerRawOutput result)

def PairedRecognizerDovetailControllerContinueCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
    P.transform (MachineDescription.DovetailControllerLayout.encode C) =
      if MachineDescription.boundedDovetailOutput
          accept reject C.input C.stage = none then
        some
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C))
      else
        none

def PairedRecognizerDovetailControllerEmitCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
    P.transform (MachineDescription.DovetailControllerLayout.encode C) =
      Option.map MachineDescription.encodeBoolWord
        (MachineDescription.boundedDovetailOutput
          accept reject C.input C.stage)

def PairedRecognizerDovetailInitialLayoutCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    P.transform (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.initial
            accept reject w stage))

def PairedRecognizerDovetailLayoutCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    P.transform (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.run
            accept reject L.stage L))

def PairedRecognizerDovetailOutputCodeRealizes
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.DovetailLayout, forall out : Word Bool,
    MachineDescription.DovetailLayout.outputFromHits L = some out ->
      P.transform (MachineDescription.DovetailLayout.encode L) =
        some (MachineDescription.encodeBoolWord out)

def PairedRecognizerDovetailTotalOutputCodeRealizes
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    P.transform (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.encodeBoolWord
          (MachineDescription.DovetailLayout.outputWordFromHits L))

def PairedRecognizerDovetailControllerStageInputCodeRealizes
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall C : MachineDescription.DovetailControllerLayout,
    P.transform (MachineDescription.DovetailControllerLayout.encode C) =
      some (PairedRecognizerDovetailControllerStageInputCode C)

def PairedRecognizerDovetailStageAttemptCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    P.transform (PairedRecognizerDovetailStageInputCode w stage) =
      Option.map MachineDescription.encodeBoolWord
        (MachineDescription.boundedDovetailOutput
          accept reject w stage)

def PairedRecognizerDovetailTotalStageAttemptCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    P.transform (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (MachineDescription.encodeBoolWord
          (MachineDescription.DovetailLayout.outputWordFromOption
            (MachineDescription.boundedDovetailOutput
              accept reject w stage)))

def PairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall w : Word Bool, forall stage : Nat,
    exists result : Word Bool,
      P.transform (PairedRecognizerDovetailStageInputCode w stage) =
        some (MachineDescription.encodeBoolWord result) ∧
      PairedRecognizerDovetailControllerRawOutput result =
        MachineDescription.boundedDovetailOutput accept reject w stage

theorem pairedRecognizerDovetailInitialLayoutCode_encode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
        (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.initial
            accept reject w stage)) :=
  MachineDescription.DovetailLayout.initialCodePrimitive_stageInputCode
    accept reject w stage

theorem pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
    (accept reject : MachineDescription)
    (code out : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
        code = some out <->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          out =
            MachineDescription.DovetailLayout.encode
              (MachineDescription.DovetailLayout.initial
                accept reject w stage) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailInitialLayoutCode at h
    unfold MachineDescription.DovetailLayout.initialCodePrimitive at h
    unfold MachineDescription.DovetailLayout.initialCode at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            cases h
            exact
              ⟨w, stage,
                MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode,
                rfl⟩
  · intro h
    rcases h with ⟨w, stage, rfl, rfl⟩
    exact pairedRecognizerDovetailInitialLayoutCode_encode
      accept reject w stage

theorem pairedRecognizerDovetailInitialLayoutCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailInitialLayoutCodeRealizes
      accept reject
      (PairedRecognizerDovetailInitialLayoutCode accept reject) := by
  intro w stage
  exact pairedRecognizerDovetailInitialLayoutCode_encode
    accept reject w stage

theorem pairedRecognizerDovetailLayoutCode_encode
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    (PairedRecognizerDovetailLayoutCode accept reject).transform
        (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.run
            accept reject L.stage L)) :=
  MachineDescription.DovetailLayout.runCodePrimitive_encode
    accept reject L

theorem pairedRecognizerDovetailLayoutCode_transform_eq_some_iff
    (accept reject : MachineDescription)
    (code out : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailLayoutCode accept reject).transform code =
        some out <->
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.DovetailLayout.encode L ∧
          out =
            MachineDescription.DovetailLayout.encode
              (MachineDescription.DovetailLayout.run
                accept reject L.stage L) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailLayoutCode at h
    unfold MachineDescription.DovetailLayout.runCodePrimitive at h
    unfold MachineDescription.DovetailLayout.runCode at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some L =>
        simp [hdecode] at h
        cases h
        exact
          ⟨L,
            MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
              hdecode,
            rfl⟩
  · intro h
    rcases h with ⟨L, rfl, rfl⟩
    exact pairedRecognizerDovetailLayoutCode_encode accept reject L

theorem pairedRecognizerDovetailLayoutCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailLayoutCodeRealizes
      accept reject
      (PairedRecognizerDovetailLayoutCode accept reject) := by
  intro L
  exact pairedRecognizerDovetailLayoutCode_encode accept reject L

theorem pairedRecognizerDovetailOutputCode_encode
    {L : MachineDescription.DovetailLayout} {out : Word Bool}
    (h :
      MachineDescription.DovetailLayout.outputFromHits L = some out) :
    PairedRecognizerDovetailOutputCode.transform
        (MachineDescription.DovetailLayout.encode L) =
      some (MachineDescription.encodeBoolWord out) :=
  MachineDescription.DovetailLayout.outputCode_encode_of_outputFromHits_eq_some
    h

theorem pairedRecognizerDovetailOutputCode_realizes :
    PairedRecognizerDovetailOutputCodeRealizes
      PairedRecognizerDovetailOutputCode := by
  intro L out h
  exact pairedRecognizerDovetailOutputCode_encode h

theorem pairedRecognizerDovetailTotalOutputCode_encode
    (L : MachineDescription.DovetailLayout) :
    PairedRecognizerDovetailTotalOutputCode.transform
        (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.encodeBoolWord
          (MachineDescription.DovetailLayout.outputWordFromHits L)) := by
  simp [PairedRecognizerDovetailTotalOutputCode,
    MachineDescription.DovetailLayout.decodeComplete_encode]

theorem pairedRecognizerDovetailTotalOutputCode_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    PairedRecognizerDovetailTotalOutputCode.transform code = some out <->
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.DovetailLayout.encode L ∧
          out =
            MachineDescription.encodeBoolWord
              (MachineDescription.DovetailLayout.outputWordFromHits L) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailTotalOutputCode at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some L =>
        simp [hdecode] at h
        cases h
        exact
          ⟨L,
            MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
              hdecode,
            rfl⟩
  · intro h
    rcases h with ⟨L, rfl, rfl⟩
    exact pairedRecognizerDovetailTotalOutputCode_encode L

theorem pairedRecognizerDovetailTotalOutputCode_realizes :
    PairedRecognizerDovetailTotalOutputCodeRealizes
      PairedRecognizerDovetailTotalOutputCode := by
  intro L
  exact pairedRecognizerDovetailTotalOutputCode_encode L

theorem pairedRecognizerDovetailControllerStageInputCode_encode
    (C : MachineDescription.DovetailControllerLayout) :
    PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
      some (PairedRecognizerDovetailControllerStageInputCode C) := by
  simp [PairedRecognizerDovetailControllerStageInputCodePrimitive,
    MachineDescription.DovetailControllerLayout.decodeComplete_encode]

theorem pairedRecognizerDovetailControllerStageInputCode_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    PairedRecognizerDovetailControllerStageInputCodePrimitive.transform code =
        some out <->
      exists C : MachineDescription.DovetailControllerLayout,
        code = MachineDescription.DovetailControllerLayout.encode C ∧
          out = PairedRecognizerDovetailControllerStageInputCode C := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailControllerStageInputCodePrimitive at h
    cases hdecode :
        MachineDescription.DovetailControllerLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some C =>
        simp [hdecode] at h
        cases h
        exact
          ⟨C,
            MachineDescription.DovetailControllerLayout.decodeComplete_eq_some_encode
              hdecode,
            rfl⟩
  · intro h
    rcases h with ⟨C, rfl, rfl⟩
    exact pairedRecognizerDovetailControllerStageInputCode_encode C

theorem pairedRecognizerDovetailControllerStageInputCode_realizes :
    PairedRecognizerDovetailControllerStageInputCodeRealizes
      PairedRecognizerDovetailControllerStageInputCodePrimitive := by
  intro C
  exact pairedRecognizerDovetailControllerStageInputCode_encode C

theorem pairedRecognizerDovetailStageAttemptCode_encode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (PairedRecognizerDovetailStageAttemptCode accept reject).transform
        (PairedRecognizerDovetailStageInputCode w stage) =
      Option.map MachineDescription.encodeBoolWord
        (MachineDescription.boundedDovetailOutput
          accept reject w stage) :=
  MachineDescription.DovetailLayout.stageAttemptCodePrimitive_stageInputCode
    accept reject w stage

theorem pairedRecognizerDovetailStageAttemptCode_transform_eq_some_iff
    (accept reject : MachineDescription)
    (code out : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailStageAttemptCode accept reject).transform code =
        some out <->
      exists w : Word Bool,
      exists stage : Nat,
      exists result : Word Bool,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          MachineDescription.boundedDovetailOutput accept reject w stage =
            some result ∧
          out = MachineDescription.encodeBoolWord result := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailStageAttemptCode at h
    unfold MachineDescription.DovetailLayout.stageAttemptCodePrimitive at h
    unfold MachineDescription.DovetailLayout.stageAttemptCode at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            rw [MachineDescription.DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput]
              at h
            cases hbounded :
                MachineDescription.boundedDovetailOutput
                  accept reject w stage with
            | none =>
                simp [hbounded] at h
            | some result =>
                simp [hbounded] at h
                cases h
                exact
                  ⟨w, stage, result,
                    MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                      hdecode,
                    hbounded,
                    rfl⟩
  · intro h
    rcases h with ⟨w, stage, result, rfl, hbounded, rfl⟩
    rw [pairedRecognizerDovetailStageAttemptCode_encode, hbounded]
    rfl

theorem pairedRecognizerDovetailStageAttemptCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailStageAttemptCodeRealizes
      accept reject
      (PairedRecognizerDovetailStageAttemptCode accept reject) := by
  intro w stage
  exact pairedRecognizerDovetailStageAttemptCode_encode
    accept reject w stage

theorem pairedRecognizerDovetailTotalStageAttemptCode_encode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (PairedRecognizerDovetailTotalStageAttemptCode accept reject).transform
        (PairedRecognizerDovetailStageInputCode w stage) =
      some
        (MachineDescription.encodeBoolWord
          (MachineDescription.DovetailLayout.outputWordFromOption
            (MachineDescription.boundedDovetailOutput
              accept reject w stage))) :=
  MachineDescription.DovetailLayout.totalStageAttemptCodePrimitive_stageInputCode
    accept reject w stage

theorem pairedRecognizerDovetailTotalStageAttemptCode_transform_eq_some_iff
    (accept reject : MachineDescription)
    (code out : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailTotalStageAttemptCode accept reject).transform
        code = some out <->
      exists w : Word Bool,
      exists stage : Nat,
        code = PairedRecognizerDovetailStageInputCode w stage ∧
          out =
            MachineDescription.encodeBoolWord
              (MachineDescription.DovetailLayout.outputWordFromOption
                (MachineDescription.boundedDovetailOutput
                  accept reject w stage)) := by
  constructor
  · intro h
    unfold PairedRecognizerDovetailTotalStageAttemptCode at h
    unfold MachineDescription.DovetailLayout.totalStageAttemptCodePrimitive at h
    unfold MachineDescription.DovetailLayout.totalStageAttemptCode at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeStageInputComplete code with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        cases parsed with
        | mk w stage =>
            simp [hdecode] at h
            cases h
            exact
              ⟨w, stage,
                MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
                  hdecode,
                by
                  simp [MachineDescription.DovetailLayout.outputWordFromHits,
                    MachineDescription.DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput]⟩
  · intro h
    rcases h with ⟨w, stage, rfl, rfl⟩
    exact pairedRecognizerDovetailTotalStageAttemptCode_encode
      accept reject w stage

theorem pairedRecognizerDovetailTotalStageAttemptCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailTotalStageAttemptCodeRealizes
      accept reject
      (PairedRecognizerDovetailTotalStageAttemptCode accept reject) := by
  intro w stage
  exact pairedRecognizerDovetailTotalStageAttemptCode_encode
    accept reject w stage

theorem pairedRecognizerDovetailTotalStageAttemptSourceCode_transform_eq
    (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailTotalStageAttemptSourceCode
        accept reject).transform tokens =
      (PairedRecognizerDovetailTotalStageAttemptCode
        accept reject).transform tokens := by
  unfold PairedRecognizerDovetailTotalStageAttemptSourceCode
  unfold PairedRecognizerDovetailInitialLayoutCode
  unfold PairedRecognizerDovetailLayoutCode
  unfold PairedRecognizerDovetailTotalOutputCode
  unfold PairedRecognizerDovetailTotalStageAttemptCode
  unfold MachineDescription.TapeCodePrimitive.compose
  unfold MachineDescription.DovetailLayout.initialCodePrimitive
  unfold MachineDescription.DovetailLayout.runCodePrimitive
  unfold MachineDescription.DovetailLayout.totalStageAttemptCodePrimitive
  unfold MachineDescription.DovetailLayout.initialCode
  unfold MachineDescription.DovetailLayout.runCode
  unfold MachineDescription.DovetailLayout.totalStageAttemptCode
  cases h : MachineDescription.DovetailLayout.decodeStageInputComplete
      tokens with
  | none =>
      simp [h]
  | some parsed =>
      rcases parsed with ⟨w, stage⟩
      simp [h, MachineDescription.DovetailLayout.decodeComplete_encode,
        MachineDescription.DovetailLayout.initial]

theorem pairedRecognizerDovetailTotalStageAttemptCodeRealizes_controllerResult
    {accept reject : MachineDescription}
    {P : MachineDescription.TapeCodePrimitive}
    (hP :
      PairedRecognizerDovetailTotalStageAttemptCodeRealizes
        accept reject P) :
    PairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
      accept reject P := by
  intro w stage
  refine
    ⟨MachineDescription.DovetailLayout.outputWordFromOption
        (MachineDescription.boundedDovetailOutput
          accept reject w stage), ?_, ?_⟩
  · exact hP w stage
  · exact
      MachineDescription.DovetailControllerLayout.rawOutput_outputWordFromOption_boundedDovetailOutput
        accept reject w stage

theorem pairedRecognizerDovetailTotalStageAttemptCode_controllerResultRealizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
      accept reject
      (PairedRecognizerDovetailTotalStageAttemptCode accept reject) :=
  pairedRecognizerDovetailTotalStageAttemptCodeRealizes_controllerResult
    (pairedRecognizerDovetailTotalStageAttemptCode_realizes accept reject)

theorem pairedRecognizerDovetailControllerRawOutputCode_realizes :
    PairedRecognizerDovetailControllerRawOutputCodeRealizes
      PairedRecognizerDovetailControllerRawOutputCode := by
  intro result
  exact
    MachineDescription.DovetailControllerLayout.rawOutputCodePrimitive_encodeBoolWord
      result

theorem pairedRecognizerDovetailControllerRawOutputCode_eq_some_encodeBoolWord_singleton_iff
    {tokens : Word MachineCodeSymbol} {b : Bool} :
      PairedRecognizerDovetailControllerRawOutputCode.transform tokens =
        some (MachineDescription.encodeBoolWord [b]) <->
      MachineDescription.DovetailControllerLayout.decodeAttemptResultCode
        tokens = some [b] :=
  MachineDescription.DovetailControllerLayout.rawOutputCode_eq_some_encodeBoolWord_singleton_iff

theorem pairedRecognizerDovetailControllerRawOutputCode_transform_eq_some_iff
    (code outCode : Word MachineCodeSymbol) :
    PairedRecognizerDovetailControllerRawOutputCode.transform code =
        some outCode <->
      exists result out : Word Bool,
        code = MachineDescription.encodeBoolWord result ∧
          PairedRecognizerDovetailControllerRawOutput result = some out ∧
          outCode = MachineDescription.encodeBoolWord out := by
  constructor
  · intro h
    rcases
        MachineDescription.DovetailControllerLayout.rawOutputCode_eq_some_iff.mp
          h with
      ⟨result, out, hdecode, hraw, hout⟩
    exact
      ⟨result, out,
        MachineDescription.DovetailControllerLayout.decodeAttemptResultCode_eq_some_encodeBoolWord
          hdecode,
        hraw,
        hout⟩
  · intro h
    rcases h with ⟨result, out, rfl, hraw, rfl⟩
    exact
      MachineDescription.DovetailControllerLayout.rawOutputCode_eq_some_iff.mpr
        ⟨result, out,
          MachineDescription.DovetailControllerLayout.decodeAttemptResultCode_encodeBoolWord
            result,
          hraw,
          rfl⟩

theorem pairedRecognizerDovetailControllerRawOutputCode_eq_some_self
    {code out : Word MachineCodeSymbol}
    (h :
      PairedRecognizerDovetailControllerRawOutputCode.transform code =
        some out) :
    out = code := by
  rcases MachineDescription.DovetailControllerLayout.rawOutputCode_eq_some_iff.mp
      h with
    ⟨result, raw, hdecode, hraw, hout⟩
  cases result with
  | nil =>
      simp [MachineDescription.DovetailControllerLayout.rawOutput?] at hraw
  | cons b tail =>
      cases tail with
      | nil =>
          simp [MachineDescription.DovetailControllerLayout.rawOutput?] at hraw
          cases hraw
          have hcode : code = MachineDescription.encodeBoolWord [b] := by
            apply
              MachineDescription.DovetailControllerLayout.decodeAttemptResultCode_eq_some_encodeBoolWord
            exact hdecode
          rw [hout, hcode]
      | cons c rest =>
          simp [MachineDescription.DovetailControllerLayout.rawOutput?] at hraw

theorem pairedRecognizerDovetailControllerContinueCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailControllerContinueCodeRealizes
      accept reject
      (PairedRecognizerDovetailControllerContinueCode accept reject) := by
  intro C
  exact
    MachineDescription.DovetailControllerLayout.continueCodePrimitive_encode
      accept reject C

theorem pairedRecognizerDovetailControllerEmitCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailControllerEmitCodeRealizes
      accept reject
      (PairedRecognizerDovetailControllerEmitCode accept reject) := by
  intro C
  exact
    MachineDescription.DovetailControllerLayout.emitCodePrimitive_encode
      accept reject C

theorem pairedRecognizerDovetailControllerContinueCode_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {out : Word MachineCodeSymbol} :
    (PairedRecognizerDovetailControllerContinueCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some out <->
      MachineDescription.boundedDovetailOutput
          accept reject C.input C.stage = none ∧
        out =
          MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C) :=
  MachineDescription.DovetailControllerLayout.continueCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerEmitCode_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some outCode <->
      exists out : Word Bool,
        MachineDescription.boundedDovetailOutput
          accept reject C.input C.stage = some out ∧
          outCode = MachineDescription.encodeBoolWord out :=
  MachineDescription.DovetailControllerLayout.emitCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerEmitCode_encode_eq_encodeBoolWord_iff
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {out : Word Bool} :
    (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some (MachineDescription.encodeBoolWord out) <->
      MachineDescription.boundedDovetailOutput
        accept reject C.input C.stage = some out :=
  MachineDescription.DovetailControllerLayout.emitCodePrimitive_encode_eq_encodeBoolWord_iff

theorem pairedRecognizerDovetailControllerContinueEmitCode_exclusive
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {next out : Word MachineCodeSymbol}
    (hcontinue :
      (PairedRecognizerDovetailControllerContinueCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
          some next)
    (hemit :
      (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
          some out) :
    False :=
  MachineDescription.DovetailControllerLayout.continueCode_emitCode_encode_exclusive
    hcontinue hemit

theorem pairedRecognizerDovetailControllerContinueEmitCode_branch
    (accept reject : MachineDescription)
    (C : MachineDescription.DovetailControllerLayout) :
    ((PairedRecognizerDovetailControllerContinueCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)) ∧
      (PairedRecognizerDovetailControllerEmitCode accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) = none) ∨
      ((PairedRecognizerDovetailControllerContinueCode
          accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) = none ∧
        exists out : Word Bool,
          MachineDescription.boundedDovetailOutput
            accept reject C.input C.stage = some out ∧
            (PairedRecognizerDovetailControllerEmitCode
              accept reject).transform
              (MachineDescription.DovetailControllerLayout.encode C) =
                some (MachineDescription.encodeBoolWord out)) :=
  MachineDescription.DovetailControllerLayout.continue_emit_branch_encode
    accept reject C

theorem pairedRecognizerDovetailControllerResultEmitterCode_encode_eq_some_iff
    {C : MachineDescription.DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    PairedRecognizerDovetailControllerResultEmitterCode.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some outCode <->
      exists out : Word Bool,
        PairedRecognizerDovetailControllerRawOutput C.result = some out ∧
          outCode = MachineDescription.encodeBoolWord out :=
  MachineDescription.DovetailControllerLayout.emitResultCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerResultEmitterCode_encode_eq_encodeBoolWord_iff
    {C : MachineDescription.DovetailControllerLayout}
    {out : Word Bool} :
    PairedRecognizerDovetailControllerResultEmitterCode.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some (MachineDescription.encodeBoolWord out) <->
      PairedRecognizerDovetailControllerRawOutput C.result = some out :=
  MachineDescription.DovetailControllerLayout.emitResultCodePrimitive_encode_eq_encodeBoolWord_iff

theorem pairedRecognizerDovetailControllerResultContinueCode_encode_eq_some_iff
    {C : MachineDescription.DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    PairedRecognizerDovetailControllerResultContinueCode.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some outCode <->
      PairedRecognizerDovetailControllerRawOutput C.result = none ∧
        outCode =
          MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C) :=
  MachineDescription.DovetailControllerLayout.continueResultCodePrimitive_encode_eq_some_iff

theorem pairedRecognizerDovetailControllerResultContinueCode_encode_nextStage_iff
    {C : MachineDescription.DovetailControllerLayout} :
    PairedRecognizerDovetailControllerResultContinueCode.transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)) <->
      PairedRecognizerDovetailControllerRawOutput C.result = none := by
  constructor
  · intro h
    exact
      (pairedRecognizerDovetailControllerResultContinueCode_encode_eq_some_iff.mp
        h).left
  · intro h
    exact
      pairedRecognizerDovetailControllerResultContinueCode_encode_eq_some_iff.mpr
        ⟨h, rfl⟩

theorem pairedRecognizerDovetailTotalThenRawOutputCode_encode
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    (PairedRecognizerDovetailTotalThenRawOutputCode
      accept reject).transform
        (PairedRecognizerDovetailStageInputCode w stage) =
      Option.map MachineDescription.encodeBoolWord
        (MachineDescription.boundedDovetailOutput
          accept reject w stage) :=
  MachineDescription.DovetailControllerLayout.rawOutputCode_after_totalStageAttemptCode_stageInputCode
    accept reject w stage

theorem pairedRecognizerDovetailTotalThenRawOutputCode_eq_stageAttemptCode
    (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailTotalThenRawOutputCode
      accept reject).transform tokens =
      (PairedRecognizerDovetailStageAttemptCode
        accept reject).transform tokens :=
  MachineDescription.DovetailControllerLayout.rawOutputCode_after_totalStageAttemptCode
    accept reject tokens

theorem pairedRecognizerDovetailTotalThenRawOutputCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailStageAttemptCodeRealizes
      accept reject
      (PairedRecognizerDovetailTotalThenRawOutputCode accept reject) := by
  intro w stage
  exact pairedRecognizerDovetailTotalThenRawOutputCode_encode
    accept reject w stage

theorem pairedRecognizerDovetailLayout_initial_output
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    MachineDescription.DovetailLayout.outputFromHits
        (MachineDescription.DovetailLayout.run accept reject limit
          (MachineDescription.DovetailLayout.initial
            accept reject w limit)) =
      MachineDescription.boundedDovetailOutput accept reject w limit :=
  MachineDescription.DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput
    accept reject w limit

def TapeCodePrimitiveCompiledByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      D.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out

def TapeCodePrimitiveOutputRealizedByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      P.transform code = some out ->
        D.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out)

def TapeCodePrimitiveOutputCompiledByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out

def TapeCodePrimitiveOutputSubroutineRealizedByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  TapeCodePrimitiveOutputRealizedByDescription P D ∧
    D.HaltTransitionFree

def TapeCodePrimitiveOutputCompiledSubroutineByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  TapeCodePrimitiveOutputCompiledByDescription P D ∧
    D.HaltTransitionFree

theorem tapeCodePrimitiveOutputCompiledByDescription_wellFormed
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D) :
    D.WellFormed :=
  h.left

theorem tapeCodePrimitiveOutputCompiledByDescription_haltsWithOutput_iff
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  h.right code out

theorem tapeCodePrimitiveOutputCompiledByDescription_haltsWithOutput_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) :=
  (h.right code out).mpr hp

theorem tapeCodePrimitiveOutputCompiledByDescription_transform_eq_some_of_haltsWithOutput
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hD :
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)) :
    P.transform code = some out :=
  (h.right code out).mp hD

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_wellFormed
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    D.WellFormed :=
  h.left.left

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltTransitionFree
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    D.HaltTransitionFree :=
  h.right

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_iff
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D)
    (code out : Word MachineCodeSymbol) :
    D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      P.transform code = some out :=
  h.left.right code out

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hp : P.transform code = some out) :
    D.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) :=
  (h.left.right code out).mpr hp

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_transform_eq_some_of_haltsWithOutput
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D)
    {code out : Word MachineCodeSymbol}
    (hD :
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)) :
    P.transform code = some out :=
  (h.left.right code out).mp hD

theorem haltsWithEncodedCodeOutput_functional_of_haltTransitionFree
    {D : MachineDescription}
    {w : Word Bool}
    {out₁ out₂ : Word MachineCodeSymbol}
    (hD : D.HaltTransitionFree)
    (h₁ :
      D.HaltsWithOutput w
        (MachineDescription.encodeCodeWordAsInput out₁))
    (h₂ :
      D.HaltsWithOutput w
        (MachineDescription.encodeCodeWordAsInput out₂)) :
    out₁ = out₂ :=
  MachineDescription.encodeCodeWordAsInput_injective
    (MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
      hD h₁ h₂)

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_output_eq_of_haltsWithOutput
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D)
    {code expected actual : Word MachineCodeSymbol}
    (hp : P.transform code = some expected)
    (hD :
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput actual)) :
    expected = actual :=
  haltsWithEncodedCodeOutput_functional_of_haltTransitionFree h.right
    (h.left.right code expected hp) hD

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_congr
    {P Q : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hPQ : forall code : Word MachineCodeSymbol,
      P.transform code = Q.transform code)
    (hD : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription Q D := by
  constructor
  · constructor
    · exact hD.left.left
    · intro code out
      simpa [hPQ code] using hD.left.right code out
  · exact hD.right

theorem tapeCodePrimitiveOutputRealizedByDescription_of_outputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D := by
  constructor
  · exact h.left
  · intro code out hp
    exact (h.right code out).mpr hp

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_of_outputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription P D :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_of_outputCompiled h.left,
    h.right⟩

theorem tapeCodePrimitiveOutputRealizedByDescription_of_exact
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveCompiledByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D := by
  constructor
  · exact h.left
  · intro code out hp
    exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput
      ((h.right code out).mpr hp)

theorem tapeCodePrimitiveOutputRealizedByDescription_of_subroutine
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D) :
    TapeCodePrimitiveOutputRealizedByDescription P D :=
  h.left

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputSubroutineRealizedByDescription P D) :
    D.SubroutineReady :=
  ⟨h.left.left, h.right⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (h : TapeCodePrimitiveOutputCompiledSubroutineByDescription P D) :
    D.SubroutineReady :=
  ⟨h.left.left, h.right⟩

theorem tapeCodePrimitiveCompiledByDescription_identity :
    TapeCodePrimitiveCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact MachineDescription.exactIdentityDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hbool :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput code :=
        (MachineDescription.exactIdentityDescription_haltsWithExactOutput_iff
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out)).mp h
      have hout : out = code :=
        MachineDescription.encodeCodeWordAsInput_injective hbool
      simp [MachineDescription.TapeCodePrimitive.identity, hout]
    · intro h
      simp [MachineDescription.TapeCodePrimitive.identity] at h
      rw [← h]
      exact
        (MachineDescription.exactIdentityDescription_haltsWithExactOutput_iff
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

theorem tapeCodePrimitiveOutputRealizedByDescription_identity :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  tapeCodePrimitiveOutputRealizedByDescription_of_exact
    tapeCodePrimitiveCompiledByDescription_identity

theorem tapeCodePrimitiveOutputCompiledByDescription_identity :
    TapeCodePrimitiveOutputCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact MachineDescription.exactIdentityDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hbool :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput code :=
        (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out)).mp h
      have hout : out = code :=
        MachineDescription.encodeCodeWordAsInput_injective hbool
      simp [MachineDescription.TapeCodePrimitive.identity, hout]
    · intro h
      simp [MachineDescription.TapeCodePrimitive.identity] at h
      rw [← h]
      exact (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_identity :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_identity,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_identity :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  ⟨tapeCodePrimitiveOutputCompiledByDescription_identity,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

theorem pairedRecognizerDovetailControllerRawOutputCodeOutputRealizedByDescription :
    TapeCodePrimitiveOutputRealizedByDescription
      PairedRecognizerDovetailControllerRawOutputCode
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact MachineDescription.exactIdentityDescription_wellFormed
  · intro code out h
    have hout : out = code :=
      pairedRecognizerDovetailControllerRawOutputCode_eq_some_self h
    rw [hout]
    exact
      (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

theorem tapeCodePrimitiveOutputRealizedByDescription_erase :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription := by
  constructor
  · exact MachineDescription.eraseRightDescription_wellFormed
  · intro code out h
    simp [MachineDescription.TapeCodePrimitive.erase] at h
    rw [← h]
    exact MachineDescription.eraseRightDescription_haltsWithOutput_empty
      (MachineDescription.encodeCodeWordAsInput code)

theorem tapeCodePrimitiveOutputCompiledByDescription_erase :
    TapeCodePrimitiveOutputCompiledByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription := by
  constructor
  · exact MachineDescription.eraseRightDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hnil :
          MachineDescription.EraseRightDescription.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput
              ([] : Word MachineCodeSymbol)) := by
        simpa [MachineDescription.encodeCodeWordAsInput] using
          MachineDescription.eraseRightDescription_haltsWithOutput_empty
            (MachineDescription.encodeCodeWordAsInput code)
      have hbool :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput
              ([] : Word MachineCodeSymbol) :=
        MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
          MachineDescription.eraseRightDescription_haltTransitionFree h hnil
      have hout : out = [] :=
        MachineDescription.encodeCodeWordAsInput_injective hbool
      simp [MachineDescription.TapeCodePrimitive.erase, hout]
    · intro h
      exact (tapeCodePrimitiveOutputRealizedByDescription_erase.right
        code out) h

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_erase :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_erase,
    MachineDescription.eraseRightDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_erase :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription :=
  ⟨tapeCodePrimitiveOutputCompiledByDescription_erase,
    MachineDescription.eraseRightDescription_haltTransitionFree⟩

theorem tapeCodePrimitiveOutputRealizedByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputRealizedByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) := by
  constructor
  · exact MachineDescription.appendCodeSymbolRightDescription_wellFormed
      symbol
  · intro code out h
    simp [MachineDescription.TapeCodePrimitive.append] at h
    rw [← h]
    have hencoded :
        MachineDescription.encodeCodeWordAsInput
            (List.append code [symbol]) =
          List.append (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeSymbolAsInput symbol) := by
      rw [MachineDescription.encodeCodeWordAsInput_append,
        MachineDescription.encodeCodeWordAsInput_singleton]
    change
      (MachineDescription.AppendCodeSymbolRightDescription symbol).HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput
          (List.append code [symbol]))
    rw [hencoded]
    exact
      MachineDescription.appendCodeSymbolRightDescription_haltsWithOutput_append
        symbol (MachineDescription.encodeCodeWordAsInput code)

theorem tapeCodePrimitiveOutputCompiledByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputCompiledByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) := by
  constructor
  · exact MachineDescription.appendCodeSymbolRightDescription_wellFormed
      symbol
  · intro code out
    constructor
    · intro h
      have hencoded :
          MachineDescription.encodeCodeWordAsInput
              (List.append code [symbol]) =
            List.append (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeSymbolAsInput symbol) := by
        rw [MachineDescription.encodeCodeWordAsInput_append,
          MachineDescription.encodeCodeWordAsInput_singleton]
      have htarget :
          (MachineDescription.AppendCodeSymbolRightDescription
            symbol).HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput
              (List.append code [symbol])) := by
        rw [hencoded]
        exact
          MachineDescription.appendCodeSymbolRightDescription_haltsWithOutput_append
            symbol (MachineDescription.encodeCodeWordAsInput code)
      have hbool :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput
              (List.append code [symbol]) :=
        MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
          (MachineDescription.appendCodeSymbolRightDescription_haltTransitionFree
            symbol) h htarget
      have hout : out = List.append code [symbol] :=
        MachineDescription.encodeCodeWordAsInput_injective hbool
      simp [MachineDescription.TapeCodePrimitive.append, hout]
    · intro h
      exact
        (tapeCodePrimitiveOutputRealizedByDescription_append_singleton
          symbol).right code out h

theorem tapeCodePrimitiveOutputSubroutineRealizedByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) :=
  ⟨tapeCodePrimitiveOutputRealizedByDescription_append_singleton symbol,
    MachineDescription.appendCodeSymbolRightDescription_haltTransitionFree
      symbol⟩

theorem tapeCodePrimitiveOutputCompiledSubroutineByDescription_append_singleton
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) :=
  ⟨tapeCodePrimitiveOutputCompiledByDescription_append_singleton symbol,
    MachineDescription.appendCodeSymbolRightDescription_haltTransitionFree
      symbol⟩

theorem not_tapeCodePrimitiveCompiledByDescription_erase :
    ¬ exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        MachineDescription.TapeCodePrimitive.erase D := by
  intro h
  rcases h with ⟨D, hD⟩
  have herase :
      D.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput
          [MachineCodeSymbol.header])
        (MachineDescription.encodeCodeWordAsInput []) := by
    exact (hD.right [MachineCodeSymbol.header] []).mpr rfl
  have hctx :
      0 <
        Tape.contextLength
          (Tape.input
            (MachineDescription.encodeCodeWordAsInput
              [MachineCodeSymbol.header])) := by
    simp [MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput, Tape.input,
      Tape.contextLength]
  simpa [MachineDescription.encodeCodeWordAsInput] using
    MachineDescription.not_haltsWithExactOutput_empty_of_input_contextLength_pos
      (D := D)
      (w := MachineDescription.encodeCodeWordAsInput
        [MachineCodeSymbol.header])
      hctx herase

structure MachineDescriptionPrimitiveCompilerCore where
  identityCompiled :
    TapeCodePrimitiveCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription
  identityOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription
  identityOutputCompiled :
    TapeCodePrimitiveOutputCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription
  identityOutputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription
  eraseOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription
  eraseOutputCompiled :
    TapeCodePrimitiveOutputCompiledByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription
  eraseOutputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription
  eraseNotExactlyCompiled :
    ¬ exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        MachineDescription.TapeCodePrimitive.erase D
  appendSingletonOutputRealized :
    forall symbol : MachineCodeSymbol,
      TapeCodePrimitiveOutputRealizedByDescription
        (MachineDescription.TapeCodePrimitive.append [symbol])
        (MachineDescription.AppendCodeSymbolRightDescription symbol)
  appendSingletonOutputCompiled :
    forall symbol : MachineCodeSymbol,
      TapeCodePrimitiveOutputCompiledByDescription
        (MachineDescription.TapeCodePrimitive.append [symbol])
        (MachineDescription.AppendCodeSymbolRightDescription symbol)
  appendSingletonOutputCompiledSubroutine :
    forall symbol : MachineCodeSymbol,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (MachineDescription.TapeCodePrimitive.append [symbol])
        (MachineDescription.AppendCodeSymbolRightDescription symbol)
  controllerRawOutputOutputRealized :
    TapeCodePrimitiveOutputRealizedByDescription
      PairedRecognizerDovetailControllerRawOutputCode
      MachineDescription.ExactIdentityDescription

def machineDescriptionPrimitiveCompilerCore :
    MachineDescriptionPrimitiveCompilerCore where
  identityCompiled := tapeCodePrimitiveCompiledByDescription_identity
  identityOutputRealized :=
    tapeCodePrimitiveOutputRealizedByDescription_identity
  identityOutputCompiled :=
    tapeCodePrimitiveOutputCompiledByDescription_identity
  identityOutputCompiledSubroutine :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_identity
  eraseOutputRealized :=
    tapeCodePrimitiveOutputRealizedByDescription_erase
  eraseOutputCompiled :=
    tapeCodePrimitiveOutputCompiledByDescription_erase
  eraseOutputCompiledSubroutine :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_erase
  eraseNotExactlyCompiled :=
    not_tapeCodePrimitiveCompiledByDescription_erase
  appendSingletonOutputRealized :=
    tapeCodePrimitiveOutputRealizedByDescription_append_singleton
  appendSingletonOutputCompiled :=
    tapeCodePrimitiveOutputCompiledByDescription_append_singleton
  appendSingletonOutputCompiledSubroutine :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_append_singleton
  controllerRawOutputOutputRealized :=
    pairedRecognizerDovetailControllerRawOutputCodeOutputRealizedByDescription

structure MachineDescriptionPrimitiveSubroutineCore where
  identityReady :
    MachineDescription.SubroutineReady
      MachineDescription.ExactIdentityDescription
  eraseReady :
    MachineDescription.SubroutineReady
      MachineDescription.EraseRightDescription
  boolOutputReady :
    forall b : Bool,
      MachineDescription.SubroutineReady
        (MachineDescription.BoolOutputDescription b)
  boolOutputOnly :
    forall b : Bool,
      forall w out : Word Bool,
        (MachineDescription.BoolOutputDescription b).HaltsWithOutput w out <->
          out = [b]
  appendSingletonReady :
    forall symbol : MachineCodeSymbol,
      MachineDescription.SubroutineReady
        (MachineDescription.AppendCodeSymbolRightDescription symbol)

def machineDescriptionPrimitiveSubroutineCore :
    MachineDescriptionPrimitiveSubroutineCore where
  identityReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  eraseReady :=
    ⟨MachineDescription.eraseRightDescription_wellFormed,
      MachineDescription.eraseRightDescription_haltTransitionFree⟩
  boolOutputReady := by
    intro b
    exact
      ⟨MachineDescription.boolOutputDescription_wellFormed b,
        MachineDescription.boolOutputDescription_haltTransitionFree b⟩
  boolOutputOnly :=
    MachineDescription.boolOutputDescription_haltsWithOutput_iff
  appendSingletonReady := by
    intro symbol
    exact
      ⟨MachineDescription.appendCodeSymbolRightDescription_wellFormed symbol,
        MachineDescription.appendCodeSymbolRightDescription_haltTransitionFree
          symbol⟩

def MachineDescriptionTapeCodeExactCompilerConstruction : Prop :=
  forall P : MachineDescription.TapeCodePrimitive,
    exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription P D

def MachineDescriptionTapeCodeOutputCompilerConstruction : Prop :=
  forall P : MachineDescription.TapeCodePrimitive,
    exists D : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription P D

theorem not_machineDescriptionTapeCodeExactCompilerConstruction :
    ¬ MachineDescriptionTapeCodeExactCompilerConstruction := by
  intro hcompile
  rcases hcompile MachineDescription.TapeCodePrimitive.erase with
    ⟨D, hD⟩
  exact not_tapeCodePrimitiveCompiledByDescription_erase ⟨D, hD⟩

theorem machineDescriptionTapeCodeOutputCompiler_realizes
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction)
    (P : MachineDescription.TapeCodePrimitive) :
    exists D : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription P D :=
  hcompile P

def TapeCodePrimitiveCodeComposition
    (A B C : MachineDescription) : Prop :=
  C.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      C.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
        exists mid : Word MachineCodeSymbol,
          A.HaltsWithExactOutput
              (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeWordAsInput mid) ∧
            B.HaltsWithExactOutput
              (MachineDescription.encodeCodeWordAsInput mid)
              (MachineDescription.encodeCodeWordAsInput out)

theorem tapeCodePrimitiveCompiledByDescription_compose
    {P Q : MachineDescription.TapeCodePrimitive}
    {A B C : MachineDescription}
    (hcomp : TapeCodePrimitiveCodeComposition A B C)
    (hP : TapeCodePrimitiveCompiledByDescription P A)
    (hQ : TapeCodePrimitiveCompiledByDescription Q B) :
    TapeCodePrimitiveCompiledByDescription
      (MachineDescription.TapeCodePrimitive.compose P Q) C := by
  constructor
  · exact hcomp.left
  · intro code out
    constructor
    · intro h
      rcases (hcomp.right code out).mp h with
        ⟨mid, hA, hB⟩
      have hPmid : P.transform code = some mid :=
        (hP.right code mid).mp hA
      have hQout : Q.transform mid = some out :=
        (hQ.right mid out).mp hB
      exact
        MachineDescription.TapeCodePrimitive.compose_transform_some
          hPmid hQout
    · intro h
      unfold MachineDescription.TapeCodePrimitive.compose at h
      cases hPcode : P.transform code with
      | none =>
          simp [hPcode] at h
      | some mid =>
          have hQout : Q.transform mid = some out := by
            simpa [hPcode] using h
          apply (hcomp.right code out).mpr
          exists mid
          constructor
          · exact (hP.right code mid).mpr hPcode
          · exact (hQ.right mid out).mpr hQout

def FixedDescriptionBoundedSimulatorCodeCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (FixedDescriptionBoundedSimulatorCode D) simulator

def FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (FixedDescriptionBoundedSimulatorCode D) simulator

def FixedDescriptionStepCodeCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists stepper : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (FixedDescriptionStepCode D) stepper

def FixedDescriptionStepCodeOutputRealizerConstruction : Prop :=
  forall D : MachineDescription,
    exists stepper : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (FixedDescriptionStepCode D) stepper

def FixedDescriptionStepCodeConfigurationRealizes
    (D stepper : MachineDescription) : Prop :=
  stepper.WellFormed ∧
    forall c : MachineDescription.Configuration,
      stepper.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeConfiguration c))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeConfiguration (D.runConfig 1 c)))

def FixedDescriptionStepCodeConfigurationRealizerConstruction : Prop :=
  forall D : MachineDescription,
    exists stepper : MachineDescription,
      FixedDescriptionStepCodeConfigurationRealizes D stepper

def PairedRecognizerDovetailInitialLayoutCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists builder : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        builder

def PairedRecognizerDovetailOutputCodeOutputRealizerConstruction : Prop :=
  exists inspector : MachineDescription,
    TapeCodePrimitiveOutputRealizedByDescription
      PairedRecognizerDovetailOutputCode inspector

def PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailStageAttemptCode accept reject)
        attempt

def PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt

def PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailTotalThenRawOutputCode accept reject)
        attempt

def PairedRecognizerDovetailControllerContinueCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists branch : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailControllerContinueCode accept reject)
        branch

def PairedRecognizerDovetailControllerEmitCodeOutputRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists branch : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailControllerEmitCode accept reject)
        branch

def PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputSubroutineRealizedByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt

def PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt

def PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer

def PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner

def PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction :
    Prop :=
  exists emitter : MachineDescription,
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter

def PairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction :
    Prop :=
  forall accept reject initializer runner emitter : MachineDescription,
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      initializer ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      (PairedRecognizerDovetailLayoutCode accept reject)
      runner ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter ->
    exists attempt : MachineDescription,
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailTotalStageAttemptSourceCode accept reject)
        attempt

def PairedRecognizerDovetailLayoutCodeCompilerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner

def PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner

def PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveOutputSubroutineRealizedByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner

def PairedRecognizerDovetailSearchDriverCompilerConstruction : Prop :=
  forall accept reject runner : MachineDescription,
    TapeCodePrimitiveOutputRealizedByDescription
      (PairedRecognizerDovetailLayoutCode accept reject) runner ->
      exists decider : MachineDescription,
        PairedRecognizerBoundedDovetailTableRealizes accept reject decider

def PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction :
    Prop :=
  forall accept reject runner : MachineDescription,
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      (PairedRecognizerDovetailLayoutCode accept reject) runner ->
      exists decider : MachineDescription,
        PairedRecognizerBoundedDovetailTableRealizes accept reject decider

def PairedRecognizerDovetailRunnerSearchDriverRealizes
    (accept reject runner decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          runner.HaltsWithOutput
            (MachineDescription.DovetailLayout.asBoolInput
              (MachineDescription.DovetailLayout.initial
                accept reject w limit))
            (MachineDescription.DovetailLayout.asBoolInput
              (MachineDescription.DovetailLayout.run accept reject limit
                (MachineDescription.DovetailLayout.initial
                  accept reject w limit))) ∧
          MachineDescription.DovetailLayout.outputFromHits
              (MachineDescription.DovetailLayout.run accept reject limit
                (MachineDescription.DovetailLayout.initial
                  accept reject w limit)) =
            some [b]

def PairedRecognizerDovetailRunnerSearchDriverCompilerConstruction : Prop :=
  forall accept reject runner : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerDovetailRunnerSearchDriverRealizes
        accept reject runner decider

def PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction :
    Prop :=
  forall accept reject runner : MachineDescription,
    runner.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailRunnerSearchDriverRealizes
          accept reject runner decider

def PairedRecognizerDovetailStageAttemptSearchDriverRealizes
    (accept reject attempt decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord [b])) ∧
          MachineDescription.boundedDovetailOutput
            accept reject w limit = some [b]

def PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction :
    Prop :=
  forall accept reject attempt : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerDovetailStageAttemptSearchDriverRealizes
        accept reject attempt decider

def PairedRecognizerDovetailTotalStageAttemptSearchDriverRealizes
    (accept reject attempt decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord [b])) ∧
          MachineDescription.boundedDovetailOutput
            accept reject w limit = some [b]

def PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction :
    Prop :=
  forall accept reject attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptSearchDriverRealizes
          accept reject attempt decider

def PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
    (attempt decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]

def PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction :
    Prop :=
  forall _accept _reject attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
          attempt decider

def PairedRecognizerDovetailFiniteStageLoopControllerConstruction :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists decider : MachineDescription,
        PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
          attempt decider

def PairedRecognizerDovetailControllerInputInitializerRealizes
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall w : Word Bool,
      initializer.HaltsWithOutput w
        (MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerInitialCode w))

def PairedRecognizerDovetailControllerInputInitializerConstruction :
    Prop :=
  exists initializer : MachineDescription,
    PairedRecognizerDovetailControllerInputInitializerRealizes initializer

def PairedRecognizerDovetailControllerStageInputEncoderConstruction :
    Prop :=
  exists encoder : MachineDescription,
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder

def PairedRecognizerDovetailStageAttemptInvocationRealizes
    (attempt encoder invoker : MachineDescription) : Prop :=
  invoker.SubroutineReady ∧
    forall C : MachineDescription.DovetailControllerLayout,
    forall result : Word Bool,
      invoker.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode C))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode
              (MachineDescription.DovetailControllerLayout.withResult
                C result))) <->
        encoder.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode C))
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageInputCode C)) ∧
          attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageInputCode C))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord result))

def PairedRecognizerDovetailStageAttemptInvocationConstruction :
    Prop :=
  forall attempt encoder : MachineDescription,
    attempt.SubroutineReady ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder ->
    exists invoker : MachineDescription,
      PairedRecognizerDovetailStageAttemptInvocationRealizes
        attempt encoder invoker

def PairedRecognizerDovetailControllerResultEmitterRealizes
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall C : MachineDescription.DovetailControllerLayout,
    forall b : Bool,
      emitter.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode C))
          [b] <->
        PairedRecognizerDovetailControllerRawOutput C.result = some [b]

def PairedRecognizerDovetailControllerResultEmitterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    PairedRecognizerDovetailControllerResultEmitterRealizes emitter

def PairedRecognizerDovetailControllerContinueRealizes
    (continuer : MachineDescription) : Prop :=
  continuer.SubroutineReady ∧
    forall C : MachineDescription.DovetailControllerLayout,
      continuer.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode C))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode
              (MachineDescription.DovetailControllerLayout.nextStage C))) <->
        PairedRecognizerDovetailControllerRawOutput C.result = none

def PairedRecognizerDovetailControllerContinueConstruction :
    Prop :=
  exists continuer : MachineDescription,
    PairedRecognizerDovetailControllerContinueRealizes continuer

def PairedRecognizerDovetailFiniteStageLoopSequencingConstruction :
    Prop :=
  forall attempt initializer encoder invoker emitter continuer :
      MachineDescription,
    attempt.SubroutineReady ->
    PairedRecognizerDovetailControllerInputInitializerRealizes
      initializer ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder ->
    PairedRecognizerDovetailStageAttemptInvocationRealizes
      attempt encoder invoker ->
    PairedRecognizerDovetailControllerResultEmitterRealizes
      emitter ->
    PairedRecognizerDovetailControllerContinueRealizes
      continuer ->
    exists decider : MachineDescription,
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_finiteStageLoopController
    (hloop :
      PairedRecognizerDovetailFiniteStageLoopControllerConstruction) :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction := by
  intro _accept _reject attempt hattemptReady
  exact hloop attempt hattemptReady

/-!
The finite controller route for paired-recognizer dovetailing has two
machine-construction pieces: a total stage-attempt subroutine and a controller
that loops over stage bounds, inspecting the subroutine's normalized output.
Packaging them together gives downstream closeouts a finite-source target
without appealing to an arbitrary staged-program compiler.
-/

structure PairedRecognizerDovetailControllerCompilerCloseout where
  totalStageAttemptSubroutine :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction
  controllerSearchDriver :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction

def pairedRecognizerDovetailControllerCompilerCloseout_of_constructions
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailControllerCompilerCloseout where
  totalStageAttemptSubroutine := hattempt
  controllerSearchDriver := hdriver

structure PairedRecognizerDovetailFiniteControllerCompilerCloseout where
  totalStageAttemptSubroutine :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction
  finiteStageLoopController :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction

def pairedRecognizerDovetailControllerCompilerCloseout_of_finiteStageLoopController
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hloop :
      PairedRecognizerDovetailFiniteStageLoopControllerConstruction) :
    PairedRecognizerDovetailControllerCompilerCloseout :=
  pairedRecognizerDovetailControllerCompilerCloseout_of_constructions
    hattempt
    (pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_finiteStageLoopController
      hloop)

def pairedRecognizerDovetailControllerCompilerCloseout_of_finiteControllerCloseout
    (hclose : PairedRecognizerDovetailFiniteControllerCompilerCloseout) :
    PairedRecognizerDovetailControllerCompilerCloseout :=
  pairedRecognizerDovetailControllerCompilerCloseout_of_finiteStageLoopController
    hclose.totalStageAttemptSubroutine
    hclose.finiteStageLoopController

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_of_finiteSourceComponents
    (hinitializer :
      PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction)
    (hrunner :
      PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction)
    (hemitter :
      PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction)
    (hseq :
      PairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction := by
  intro accept reject
  rcases hinitializer accept reject with
    ⟨initializer, hinitializer⟩
  rcases hrunner accept reject with ⟨runner, hrunner⟩
  rcases hemitter with ⟨emitter, hemitter⟩
  rcases hseq accept reject initializer runner emitter
      hinitializer hrunner hemitter with
    ⟨attempt, hattempt⟩
  exact
    ⟨attempt,
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_congr
        (pairedRecognizerDovetailTotalStageAttemptSourceCode_transform_eq
          accept reject)
        hattempt⟩

theorem pairedRecognizerDovetailFiniteStageLoopControllerConstruction_of_components
    (hinit :
      PairedRecognizerDovetailControllerInputInitializerConstruction)
    (hencoder :
      PairedRecognizerDovetailControllerStageInputEncoderConstruction)
    (hinvoke :
      PairedRecognizerDovetailStageAttemptInvocationConstruction)
    (hemit :
      PairedRecognizerDovetailControllerResultEmitterConstruction)
    (hcontinue :
      PairedRecognizerDovetailControllerContinueConstruction)
    (hseq :
      PairedRecognizerDovetailFiniteStageLoopSequencingConstruction) :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction := by
  intro attempt hattempt
  rcases hinit with ⟨initializer, hinitializer⟩
  rcases hencoder with ⟨encoder, hencoder⟩
  rcases hinvoke attempt encoder hattempt hencoder with
    ⟨invoker, hinvoker⟩
  rcases hemit with ⟨emitter, hemitter⟩
  rcases hcontinue with ⟨continuer, hcontinuer⟩
  exact hseq attempt initializer encoder invoker emitter continuer
    hattempt hinitializer hencoder hinvoker hemitter hcontinuer

/-!
**Milestone 2 parser/rewriter leaves.**  The remaining finite-source work is
not a generic compiler for arbitrary {name}`MachineDescription.TapeCodePrimitive`
values.  It is a fixed family of code-word parsers and rewriters for the
canonical encodings used by the dovetail controller.  The declarations below
name those finite transition-table obligations explicitly.  Each one is a
single concrete machine family over the existing encodings, and the older
scaffold names are derived from them rather than carrying anonymous broad
holes.
-/

def EncodedCodeWordCanonicalRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    recognizer.SubroutineReady ∧
      forall bits : Word Bool,
      forall code : Word MachineCodeSymbol,
        recognizer.HaltsWithOutput bits
            (MachineDescription.encodeCodeWordAsInput code) <->
          MachineDescription.decodeCodeWordAsInput bits = some code

theorem encodedCodeWordCanonicalRecognizerConstruction_scaffold :
    EncodedCodeWordCanonicalRecognizerConstruction := by
  refine
    ⟨MachineDescription.ExactIdentityDescription,
      ⟨MachineDescription.exactIdentityDescription_wellFormed,
        MachineDescription.exactIdentityDescription_haltTransitionFree⟩,
      ?_⟩
  intro bits code
  constructor
  · intro h
    have hbits :
        MachineDescription.encodeCodeWordAsInput code = bits :=
      (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
        bits (MachineDescription.encodeCodeWordAsInput code)).mp h
    rw [← hbits]
    exact
      MachineDescription.decodeCodeWordAsInput_encodeCodeWordAsInput code
  · intro h
    have hbits :
        bits = MachineDescription.encodeCodeWordAsInput code :=
      MachineDescription.decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput h
    rw [hbits]
    exact
      (MachineDescription.exactIdentityDescription_haltsWithOutput_iff
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

def EncodedDovetailStageInputToInitialLayoutRewriterConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists initializer : MachineDescription,
      initializer.SubroutineReady ∧
        forall code out : Word MachineCodeSymbol,
          initializer.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeWordAsInput out) <->
            (PairedRecognizerDovetailInitialLayoutCode
              accept reject).transform code = some out

def EncodedDovetailLayoutBoundedRunnerRewriterConstruction :
    Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      runner.SubroutineReady ∧
        forall code out : Word MachineCodeSymbol,
          runner.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeWordAsInput out) <->
            (PairedRecognizerDovetailLayoutCode
              accept reject).transform code = some out

def EncodedDovetailTotalOutputEmitterRewriterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    emitter.SubroutineReady ∧
      forall code out : Word MachineCodeSymbol,
        emitter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          PairedRecognizerDovetailTotalOutputCode.transform code = some out

def EncodedControllerInputInitializerRewriterConstruction :
    Prop :=
  exists initializer : MachineDescription,
    initializer.SubroutineReady ∧
      forall w : Word Bool,
        initializer.HaltsWithOutput w
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerInitialCode w))

def EncodedControllerStageInputProjectionRewriterConstruction :
    Prop :=
  exists encoder : MachineDescription,
    encoder.SubroutineReady ∧
      forall code out : Word MachineCodeSymbol,
        encoder.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput code)
            (MachineDescription.encodeCodeWordAsInput out) <->
          PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
            code = some out

def EncodedControllerResultEmitterRewriterConstruction :
    Prop :=
  exists emitter : MachineDescription,
    emitter.SubroutineReady ∧
      forall C : MachineDescription.DovetailControllerLayout,
      forall b : Bool,
        emitter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode C))
            [b] <->
          PairedRecognizerDovetailControllerRawOutput C.result = some [b]

def EncodedControllerContinueRewriterConstruction :
    Prop :=
  exists continuer : MachineDescription,
    continuer.SubroutineReady ∧
      forall C : MachineDescription.DovetailControllerLayout,
        continuer.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode C))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                (MachineDescription.DovetailControllerLayout.nextStage C))) <->
          PairedRecognizerDovetailControllerRawOutput C.result = none

theorem encodedDovetailStageInputToInitialLayoutRewriterConstruction_scaffold :
    EncodedDovetailStageInputToInitialLayoutRewriterConstruction := by
  sorry

theorem encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold :
    EncodedDovetailLayoutBoundedRunnerRewriterConstruction := by
  sorry

theorem encodedDovetailTotalOutputEmitterRewriterConstruction_scaffold :
    EncodedDovetailTotalOutputEmitterRewriterConstruction := by
  sorry

theorem encodedControllerInputInitializerRewriterConstruction_scaffold :
    EncodedControllerInputInitializerRewriterConstruction := by
  sorry

theorem encodedControllerStageInputProjectionRewriterConstruction_scaffold :
    EncodedControllerStageInputProjectionRewriterConstruction := by
  sorry

theorem encodedControllerResultEmitterRewriterConstruction_scaffold :
    EncodedControllerResultEmitterRewriterConstruction := by
  sorry

theorem encodedControllerContinueRewriterConstruction_scaffold :
    EncodedControllerContinueRewriterConstruction := by
  sorry

theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailStageInputToInitialLayoutRewriterConstruction) :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction := by
  intro accept reject
  rcases h accept reject with ⟨initializer, hready, hspec⟩
  exact ⟨initializer, ⟨⟨hready.left, hspec⟩, hready.right⟩⟩

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailLayoutBoundedRunnerRewriterConstruction) :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction := by
  intro accept reject
  rcases h accept reject with ⟨runner, hready, hspec⟩
  exact ⟨runner, ⟨⟨hready.left, hspec⟩, hready.right⟩⟩

theorem pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_of_encodedRewriter
    (h :
      EncodedDovetailTotalOutputEmitterRewriterConstruction) :
    PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction := by
  rcases h with ⟨emitter, hready, hspec⟩
  exact ⟨emitter, ⟨⟨hready.left, hspec⟩, hready.right⟩⟩

theorem pairedRecognizerDovetailControllerInputInitializerConstruction_of_encodedRewriter
    (h : EncodedControllerInputInitializerRewriterConstruction) :
    PairedRecognizerDovetailControllerInputInitializerConstruction := by
  rcases h with ⟨initializer, hready, hspec⟩
  exact ⟨initializer, hready, hspec⟩

theorem pairedRecognizerDovetailControllerStageInputEncoderConstruction_of_encodedRewriter
    (h : EncodedControllerStageInputProjectionRewriterConstruction) :
    PairedRecognizerDovetailControllerStageInputEncoderConstruction := by
  rcases h with ⟨encoder, hready, hspec⟩
  exact ⟨encoder, ⟨⟨hready.left, hspec⟩, hready.right⟩⟩

theorem pairedRecognizerDovetailControllerResultEmitterConstruction_of_encodedRewriter
    (h : EncodedControllerResultEmitterRewriterConstruction) :
    PairedRecognizerDovetailControllerResultEmitterConstruction := by
  rcases h with ⟨emitter, hready, hspec⟩
  exact ⟨emitter, hready, hspec⟩

theorem pairedRecognizerDovetailControllerContinueConstruction_of_encodedRewriter
    (h : EncodedControllerContinueRewriterConstruction) :
    PairedRecognizerDovetailControllerContinueConstruction := by
  rcases h with ⟨continuer, hready, hspec⟩
  exact ⟨continuer, hready, hspec⟩

/-!
**Finite-source scaffold.**  These declarations are the remaining concrete
machine-construction leaves for the paired-recognizer dovetail controller
route. They are intentionally narrow: the source programs and controller layout
are the fixed finite targets above, not arbitrary staged programs or arbitrary
tape-code primitives.
-/

theorem pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction :=
  pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailStageInputToInitialLayoutRewriterConstruction_scaffold

theorem pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction :=
  pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailLayoutBoundedRunnerRewriterConstruction_scaffold

theorem pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction :=
  pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_of_encodedRewriter
    encodedDovetailTotalOutputEmitterRewriterConstruction_scaffold

theorem pairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction := by
  sorry

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction :=
  pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_of_finiteSourceComponents
    pairedRecognizerDovetailStageInputInitializerCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailBoundedLayoutRunnerCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailTotalOutputEmitterCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction_scaffold

theorem pairedRecognizerDovetailControllerInputInitializerConstruction_scaffold :
    PairedRecognizerDovetailControllerInputInitializerConstruction :=
  pairedRecognizerDovetailControllerInputInitializerConstruction_of_encodedRewriter
    encodedControllerInputInitializerRewriterConstruction_scaffold

theorem pairedRecognizerDovetailControllerStageInputEncoderConstruction_scaffold :
    PairedRecognizerDovetailControllerStageInputEncoderConstruction :=
  pairedRecognizerDovetailControllerStageInputEncoderConstruction_of_encodedRewriter
    encodedControllerStageInputProjectionRewriterConstruction_scaffold

theorem pairedRecognizerDovetailStageAttemptInvocationConstruction_scaffold :
    PairedRecognizerDovetailStageAttemptInvocationConstruction := by
  sorry

theorem pairedRecognizerDovetailControllerResultEmitterConstruction_scaffold :
    PairedRecognizerDovetailControllerResultEmitterConstruction :=
  pairedRecognizerDovetailControllerResultEmitterConstruction_of_encodedRewriter
    encodedControllerResultEmitterRewriterConstruction_scaffold

theorem pairedRecognizerDovetailControllerContinueConstruction_scaffold :
    PairedRecognizerDovetailControllerContinueConstruction :=
  pairedRecognizerDovetailControllerContinueConstruction_of_encodedRewriter
    encodedControllerContinueRewriterConstruction_scaffold

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstruction := by
  sorry

theorem pairedRecognizerDovetailFiniteStageLoopControllerConstruction_scaffold :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction :=
  pairedRecognizerDovetailFiniteStageLoopControllerConstruction_of_components
    pairedRecognizerDovetailControllerInputInitializerConstruction_scaffold
    pairedRecognizerDovetailControllerStageInputEncoderConstruction_scaffold
    pairedRecognizerDovetailStageAttemptInvocationConstruction_scaffold
    pairedRecognizerDovetailControllerResultEmitterConstruction_scaffold
    pairedRecognizerDovetailControllerContinueConstruction_scaffold
    pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold

def pairedRecognizerDovetailFiniteControllerCompilerCloseout_scaffold :
    PairedRecognizerDovetailFiniteControllerCompilerCloseout where
  totalStageAttemptSubroutine :=
    pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_scaffold
  finiteStageLoopController :=
    pairedRecognizerDovetailFiniteStageLoopControllerConstruction_scaffold

noncomputable def PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
    (attempt : MachineDescription) :
    StagedProgram Bool Bool :=
  by
    classical
    exact
      { run := fun w limit =>
          if attempt.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.encodeBoolWord [true])) then
            some [true]
          else if attempt.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.encodeBoolWord [false])) then
            some [false]
          else
            none }

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutput_iff
    (attempt : MachineDescription)
    (hattemptReady : attempt.SubroutineReady)
    (w : Word Bool) (b : Bool) :
    ProgramHaltsWithOutput
        (PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
          attempt) w [b] <->
      exists limit : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] := by
  classical
  constructor
  · intro h
    rcases h with ⟨limit, hrun⟩
    cases b
    · by_cases htrue :
        attempt.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeBoolWord [true]))
      · simp [PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram,
          htrue] at hrun
        cases hrun
      · by_cases hfalse :
          attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord [false]))
        · exact ⟨limit, [false], hfalse, by
            simp [PairedRecognizerDovetailControllerRawOutput,
              MachineDescription.DovetailControllerLayout.rawOutput_singleton]⟩
        · simp [PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram,
            htrue, hfalse] at hrun
    · by_cases htrue :
        attempt.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeBoolWord [true]))
      · exact ⟨limit, [true], htrue, by
          simp [PairedRecognizerDovetailControllerRawOutput,
            MachineDescription.DovetailControllerLayout.rawOutput_singleton]⟩
      · simp [PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram,
          htrue] at hrun
        cases hrun.right
  · intro h
    rcases h with ⟨limit, result, hattempt, hraw⟩
    have hresult : result = [b] :=
      (MachineDescription.DovetailControllerLayout.rawOutput_eq_some_singleton_iff
        result b).mp hraw
    subst result
    refine ⟨limit, ?_⟩
    cases b
    · have hnotTrue :
          ¬ attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord [true])) := by
        intro htrue
        have hencoded :
            MachineDescription.encodeBoolWord [false] =
              MachineDescription.encodeBoolWord [true] := by
          exact MachineDescription.encodeCodeWordAsInput_injective
            (MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
              hattemptReady.right
              hattempt htrue)
        have hbool : [false] = [true] :=
          MachineDescription.encodeBoolWord_injective hencoded
        cases hbool
      rw [show
          (PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
            attempt).run w limit =
            (if attempt.HaltsWithOutput
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w limit))
                (MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.encodeBoolWord [true])) then
              some [true]
            else if attempt.HaltsWithOutput
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w limit))
                (MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.encodeBoolWord [false])) then
              some [false]
            else
              none) by
          rfl]
      rw [if_neg hnotTrue, if_pos hattempt]
      rfl
    · simp [PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram,
        hattempt]

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction := by
  intro _accept _reject attempt _hattemptReady
  rcases hcompile
      (PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
        attempt) with
    ⟨decider, hdecider⟩
  refine ⟨decider, ?_⟩
  constructor
  · exact hdecider.left
  · intro w b
    exact Iff.trans (hdecider.right w b)
      (pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutput_iff
        attempt _hattemptReady w b)

noncomputable def PairedRecognizerDovetailStageAttemptSearchProgram
    (accept reject attempt : MachineDescription) :
    StagedProgram Bool Bool :=
  by
    classical
    exact
      { run := fun w limit =>
          if attempt.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.encodeBoolWord [true])) ∧
              MachineDescription.boundedDovetailOutput
                accept reject w limit = some [true] then
            some [true]
          else if attempt.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.encodeBoolWord [false])) ∧
              MachineDescription.boundedDovetailOutput
                accept reject w limit = some [false] then
            some [false]
          else
            none }

theorem pairedRecognizerDovetailStageAttemptSearchProgram_haltsWithOutput_iff
    (accept reject attempt : MachineDescription)
    (w : Word Bool) (b : Bool) :
    ProgramHaltsWithOutput
        (PairedRecognizerDovetailStageAttemptSearchProgram
          accept reject attempt) w [b] <->
      exists limit : Nat,
        attempt.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeBoolWord [b])) ∧
        MachineDescription.boundedDovetailOutput
          accept reject w limit = some [b] := by
  classical
  constructor
  · intro h
    rcases h with ⟨limit, hrun⟩
    cases b
    · by_cases htrue :
        attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord [true])) ∧
          MachineDescription.boundedDovetailOutput
            accept reject w limit = some [true]
      · simp [PairedRecognizerDovetailStageAttemptSearchProgram,
          htrue] at hrun
        cases hrun
      · by_cases hfalse :
          attempt.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord [false])) ∧
            MachineDescription.boundedDovetailOutput
              accept reject w limit = some [false]
        · exact ⟨limit, hfalse⟩
        · simp [PairedRecognizerDovetailStageAttemptSearchProgram,
            htrue, hfalse] at hrun
    · by_cases htrue :
        attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord [true])) ∧
          MachineDescription.boundedDovetailOutput
            accept reject w limit = some [true]
      · exact ⟨limit, htrue⟩
      · simp [PairedRecognizerDovetailStageAttemptSearchProgram,
          htrue] at hrun
        cases hrun.right
  · intro h
    rcases h with ⟨limit, hattempt, hout⟩
    refine ⟨limit, ?_⟩
    cases b
    · have hfalse :
          attempt.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.encodeBoolWord [false])) ∧
            MachineDescription.boundedDovetailOutput
              accept reject w limit = some [false] := by
        exact ⟨hattempt, hout⟩
      have hnotTrue :
          ¬ (attempt.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWord [true])) ∧
              MachineDescription.boundedDovetailOutput
              accept reject w limit = some [true]) := by
        intro htrue
        rw [hout] at htrue
        cases htrue.right
      rw [show
          (PairedRecognizerDovetailStageAttemptSearchProgram
            accept reject attempt).run w limit =
            (if
              attempt.HaltsWithOutput
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w limit))
                (MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.encodeBoolWord [true])) ∧
              MachineDescription.boundedDovetailOutput
                accept reject w limit = some [true] then
              some [true]
            else if
              attempt.HaltsWithOutput
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w limit))
                (MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.encodeBoolWord [false])) ∧
              MachineDescription.boundedDovetailOutput
                accept reject w limit = some [false] then
              some [false]
            else
              none) by
          rfl]
      rw [if_neg hnotTrue, if_pos hfalse]
      rfl
    · simp [PairedRecognizerDovetailStageAttemptSearchProgram,
        hattempt, hout]

theorem pairedRecognizerDovetailStageAttemptSearchDriverCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction := by
  intro accept reject attempt
  rcases hcompile
      (PairedRecognizerDovetailStageAttemptSearchProgram
        accept reject attempt) with
    ⟨decider, hdecider⟩
  refine ⟨decider, ?_⟩
  constructor
  · exact hdecider.left
  · intro w b
    exact Iff.trans (hdecider.right w b)
      (pairedRecognizerDovetailStageAttemptSearchProgram_haltsWithOutput_iff
        accept reject attempt w b)

theorem pairedRecognizerDovetailTotalStageAttemptSearchDriverCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction := by
  intro accept reject attempt _hattemptReady
  rcases hcompile
      (PairedRecognizerDovetailStageAttemptSearchProgram
        accept reject attempt) with
    ⟨decider, hdecider⟩
  refine ⟨decider, ?_⟩
  constructor
  · exact hdecider.left
  · intro w b
    exact Iff.trans (hdecider.right w b)
      (pairedRecognizerDovetailStageAttemptSearchProgram_haltsWithOutput_iff
        accept reject attempt w b)

theorem pairedRecognizerDovetailTotalStageAttemptControllerRawOutput_iff_of_outputCompiled
    {accept reject attempt : MachineDescription}
    (hattempt :
      TapeCodePrimitiveOutputCompiledByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt)
    (w : Word Bool) (limit : Nat) (b : Bool) :
    (exists result : Word Bool,
      attempt.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWord result)) ∧
      PairedRecognizerDovetailControllerRawOutput result = some [b]) <->
    MachineDescription.boundedDovetailOutput accept reject w limit =
      some [b] := by
  constructor
  · intro h
    rcases h with ⟨result, hattemptHalt, hraw⟩
    have htransform :
        (PairedRecognizerDovetailTotalStageAttemptCode
          accept reject).transform
            (PairedRecognizerDovetailStageInputCode w limit) =
          some (MachineDescription.encodeBoolWord result) :=
      (hattempt.right
        (PairedRecognizerDovetailStageInputCode w limit)
        (MachineDescription.encodeBoolWord result)).mp hattemptHalt
    have hcanonical :
        (PairedRecognizerDovetailTotalStageAttemptCode
          accept reject).transform
            (PairedRecognizerDovetailStageInputCode w limit) =
          some
            (MachineDescription.encodeBoolWord
              (MachineDescription.DovetailLayout.outputWordFromOption
                (MachineDescription.boundedDovetailOutput
                  accept reject w limit))) :=
      pairedRecognizerDovetailTotalStageAttemptCode_encode
        accept reject w limit
    have hencoded :
        MachineDescription.encodeBoolWord result =
          MachineDescription.encodeBoolWord
            (MachineDescription.DovetailLayout.outputWordFromOption
              (MachineDescription.boundedDovetailOutput
                accept reject w limit)) := by
      have hsome :
          some (MachineDescription.encodeBoolWord result) =
            some
              (MachineDescription.encodeBoolWord
                (MachineDescription.DovetailLayout.outputWordFromOption
                  (MachineDescription.boundedDovetailOutput
                    accept reject w limit))) := by
        rw [← htransform, hcanonical]
      exact Option.some.inj hsome
    have hresult :
        result =
          MachineDescription.DovetailLayout.outputWordFromOption
            (MachineDescription.boundedDovetailOutput
              accept reject w limit) :=
      MachineDescription.encodeBoolWord_injective hencoded
    rw [PairedRecognizerDovetailControllerRawOutput, hresult,
      MachineDescription.DovetailControllerLayout.rawOutput_outputWordFromOption_boundedDovetailOutput]
      at hraw
    exact hraw
  · intro hbounded
    refine ⟨[b], ?_, ?_⟩
    · exact
        (hattempt.right
          (PairedRecognizerDovetailStageInputCode w limit)
          (MachineDescription.encodeBoolWord [b])).mpr
          (by
            rw [pairedRecognizerDovetailTotalStageAttemptCode_encode,
              hbounded]
            rfl)
    · simp [PairedRecognizerDovetailControllerRawOutput,
        MachineDescription.DovetailControllerLayout.rawOutput_singleton]

theorem pairedRecognizerDovetailTotalStageAttemptSearchDriverRealizes_of_controllerSearchDriverRealizes
    {accept reject attempt decider : MachineDescription}
    (hattempt :
      TapeCodePrimitiveOutputCompiledByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider) :
    PairedRecognizerDovetailTotalStageAttemptSearchDriverRealizes
      accept reject attempt decider := by
  constructor
  · exact hdriver.left
  · intro w b
    constructor
    · intro hhalt
      rcases (hdriver.right w b).mp hhalt with
        ⟨limit, result, hattemptHalt, hraw⟩
      have hbounded :
          MachineDescription.boundedDovetailOutput
            accept reject w limit = some [b] := by
        exact
          (pairedRecognizerDovetailTotalStageAttemptControllerRawOutput_iff_of_outputCompiled
            hattempt w limit b).mp
            ⟨result, hattemptHalt, hraw⟩
      refine ⟨limit, ?_, hbounded⟩
      exact
        (hattempt.right
          (PairedRecognizerDovetailStageInputCode w limit)
          (MachineDescription.encodeBoolWord [b])).mpr
          (by
            rw [pairedRecognizerDovetailTotalStageAttemptCode_encode,
              hbounded]
            rfl)
    · intro hbounded
      rcases hbounded with ⟨limit, hattemptHalt, hout⟩
      apply (hdriver.right w b).mpr
      refine ⟨limit, [b], hattemptHalt, ?_⟩
      simp [PairedRecognizerDovetailControllerRawOutput,
        MachineDescription.DovetailControllerLayout.rawOutput_singleton]

theorem fixedDescriptionBoundedSimulatorCodeOutputRealizer_of_codeCompiler
    (hcompile :
      FixedDescriptionBoundedSimulatorCodeCompilerConstruction) :
    FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction := by
  intro D
  rcases hcompile D with ⟨simulator, hsimulator⟩
  exact ⟨simulator,
    tapeCodePrimitiveOutputRealizedByDescription_of_exact hsimulator⟩

theorem fixedDescriptionStepCodeOutputRealizer_of_codeCompiler
    (hcompile : FixedDescriptionStepCodeCompilerConstruction) :
    FixedDescriptionStepCodeOutputRealizerConstruction := by
  intro D
  rcases hcompile D with ⟨stepper, hstepper⟩
  exact ⟨stepper,
    tapeCodePrimitiveOutputRealizedByDescription_of_exact hstepper⟩

theorem fixedDescriptionStepCodeOutputRealizer_of_configurationRealizer
    {D stepper : MachineDescription}
    (hstepper :
      FixedDescriptionStepCodeConfigurationRealizes D stepper) :
    TapeCodePrimitiveOutputRealizedByDescription
      (FixedDescriptionStepCode D) stepper := by
  constructor
  · exact hstepper.left
  · intro code out hcode
    unfold FixedDescriptionStepCode at hcode
    simp [MachineDescription.stepConfigurationCodePrimitive,
      MachineDescription.stepConfigurationCode] at hcode
    cases hdecode : MachineDescription.decodeConfiguration code with
    | none =>
        simp [hdecode] at hcode
    | some parsed =>
        cases parsed with
        | mk c suffix =>
            cases suffix with
            | nil =>
                simp [hdecode] at hcode
                have hcanonical :
                    code = MachineDescription.encodeConfiguration c :=
                  MachineDescription.decodeConfiguration_eq_some_encodeConfiguration
                    hdecode
                rw [hcanonical, ← hcode]
                exact hstepper.right c
            | cons _ _ =>
                simp [hdecode] at hcode

theorem fixedDescriptionStepCodeOutputRealizerConstruction_of_configurationRealizerConstruction
    (hcompile :
      FixedDescriptionStepCodeConfigurationRealizerConstruction) :
    FixedDescriptionStepCodeOutputRealizerConstruction := by
  intro D
  rcases hcompile D with ⟨stepper, hstepper⟩
  exact ⟨stepper,
    fixedDescriptionStepCodeOutputRealizer_of_configurationRealizer
      hstepper⟩

theorem fixedDescriptionStepCodeConfigurationRealizer_of_outputRealizer
    {D stepper : MachineDescription}
    (hstepper :
      TapeCodePrimitiveOutputRealizedByDescription
        (FixedDescriptionStepCode D) stepper) :
    FixedDescriptionStepCodeConfigurationRealizes D stepper := by
  constructor
  · exact hstepper.left
  · intro c
    exact hstepper.right
      (MachineDescription.encodeConfiguration c)
      (MachineDescription.encodeConfiguration (D.runConfig 1 c))
      (fixedDescriptionStepCode_encode D c)

theorem fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction
    (hcompile :
      FixedDescriptionStepCodeOutputRealizerConstruction) :
    FixedDescriptionStepCodeConfigurationRealizerConstruction := by
  intro D
  rcases hcompile D with ⟨stepper, hstepper⟩
  exact ⟨stepper,
    fixedDescriptionStepCodeConfigurationRealizer_of_outputRealizer
      hstepper⟩

theorem fixedDescriptionStepCodeConfigurationRealizerConstruction_iff_outputRealizerConstruction :
    FixedDescriptionStepCodeConfigurationRealizerConstruction <->
      FixedDescriptionStepCodeOutputRealizerConstruction := by
  constructor
  · exact
      fixedDescriptionStepCodeOutputRealizerConstruction_of_configurationRealizerConstruction
  · exact
      fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction

theorem fixedDescriptionStepCodeConfigurationRealizes_of_runConfig_one_eq_id
    {D stepper : MachineDescription}
    (hstepper :
      TapeCodePrimitiveOutputRealizedByDescription
        MachineDescription.TapeCodePrimitive.identity stepper)
    (hD : forall c : MachineDescription.Configuration,
      D.runConfig 1 c = c) :
    FixedDescriptionStepCodeConfigurationRealizes D stepper := by
  constructor
  · exact hstepper.left
  · intro c
    rw [hD c]
    exact hstepper.right
      (MachineDescription.encodeConfiguration c)
      (MachineDescription.encodeConfiguration c)
      rfl

theorem runConfig_one_eq_id_of_transitions_nil
    {D : MachineDescription}
    (hD : D.transitions = []) :
    forall c : MachineDescription.Configuration, D.runConfig 1 c = c := by
  intro c
  cases c
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, hD]

theorem fixedDescriptionStepCodeConfigurationRealizes_transitionless
    {D : MachineDescription}
    (hD : D.transitions = []) :
    FixedDescriptionStepCodeConfigurationRealizes
      D MachineDescription.ExactIdentityDescription :=
  fixedDescriptionStepCodeConfigurationRealizes_of_runConfig_one_eq_id
    tapeCodePrimitiveOutputRealizedByDescription_identity
    (runConfig_one_eq_id_of_transitions_nil hD)

theorem fixedDescriptionStepCodeConfigurationRealizes_exactIdentityDescription :
    FixedDescriptionStepCodeConfigurationRealizes
      MachineDescription.ExactIdentityDescription
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact MachineDescription.exactIdentityDescription_wellFormed
  · intro c
    have hrun :
        MachineDescription.ExactIdentityDescription.runConfig 1 c = c := by
      cases c
      simp [MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition,
        MachineDescription.ExactIdentityDescription]
    rw [hrun]
    exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput
      ((MachineDescription.exactIdentityDescription_haltsWithExactOutput_iff
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeConfiguration c))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeConfiguration c))).mpr rfl)

theorem pairedRecognizerDovetailLayoutCodeOutputRealizer_of_codeCompiler
    (hcompile :
      PairedRecognizerDovetailLayoutCodeCompilerConstruction) :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨runner, hrunner⟩
  exact ⟨runner,
    tapeCodePrimitiveOutputRealizedByDescription_of_exact hrunner⟩

theorem pairedRecognizerDovetailInitialLayoutCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailInitialLayoutCodeOutputRealizerConstruction := by
  intro accept reject
  exact hcompile (PairedRecognizerDovetailInitialLayoutCode accept reject)

theorem pairedRecognizerDovetailOutputCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailOutputCodeOutputRealizerConstruction :=
  hcompile PairedRecognizerDovetailOutputCode

theorem pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction := by
  intro accept reject
  exact hcompile
    (PairedRecognizerDovetailStageAttemptCode accept reject)

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction := by
  intro accept reject
  exact hcompile
    (PairedRecognizerDovetailTotalStageAttemptCode accept reject)

theorem pairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction := by
  intro accept reject
  exact hcompile
    (PairedRecognizerDovetailTotalThenRawOutputCode accept reject)

theorem pairedRecognizerDovetailControllerContinueCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailControllerContinueCodeOutputRealizerConstruction := by
  intro accept reject
  exact hcompile
    (PairedRecognizerDovetailControllerContinueCode accept reject)

theorem pairedRecognizerDovetailControllerEmitCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailControllerEmitCodeOutputRealizerConstruction := by
  intro accept reject
  exact hcompile
    (PairedRecognizerDovetailControllerEmitCode accept reject)

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputRealizer_of_subroutineRealizer
    (hcompile :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨attempt, hattempt⟩
  exact ⟨attempt,
    tapeCodePrimitiveOutputRealizedByDescription_of_subroutine hattempt⟩

theorem pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_totalThenRawOutputCodeOutputRealizer
    {accept reject attempt : MachineDescription}
    (hattempt :
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailTotalThenRawOutputCode accept reject)
        attempt) :
    TapeCodePrimitiveOutputRealizedByDescription
      (PairedRecognizerDovetailStageAttemptCode accept reject)
      attempt := by
  constructor
  · exact hattempt.left
  · intro code out hcode
    apply hattempt.right code out
    rwa [pairedRecognizerDovetailTotalThenRawOutputCode_eq_stageAttemptCode]

theorem pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_totalThenRawOutputCodeOutputRealizerConstruction
    (hcompile :
      PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction) :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨attempt, hattempt⟩
  exact ⟨attempt,
    pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_totalThenRawOutputCodeOutputRealizer
      hattempt⟩

theorem pairedRecognizerDovetailTotalStageAttemptCode_transform_eq_of_stageAttemptCode_eq_some
    {accept reject : MachineDescription}
    {code out : Word MachineCodeSymbol}
    (hstage :
      (PairedRecognizerDovetailStageAttemptCode accept reject).transform
        code = some out) :
    (PairedRecognizerDovetailTotalStageAttemptCode accept reject).transform
      code = some out := by
  have hcompose :
      (PairedRecognizerDovetailTotalThenRawOutputCode accept reject).transform
        code = some out := by
    simpa [pairedRecognizerDovetailTotalThenRawOutputCode_eq_stageAttemptCode]
      using hstage
  unfold PairedRecognizerDovetailTotalThenRawOutputCode at hcompose
  unfold MachineDescription.TapeCodePrimitive.compose at hcompose
  cases htotal :
      (PairedRecognizerDovetailTotalStageAttemptCode accept reject).transform
        code with
  | none =>
      simp [htotal] at hcompose
  | some mid =>
      have hraw :
          PairedRecognizerDovetailControllerRawOutputCode.transform mid =
            some out := by
        simpa [htotal] using hcompose
      have hout : out = mid :=
        pairedRecognizerDovetailControllerRawOutputCode_eq_some_self hraw
      rw [hout]

theorem pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_totalStageAttemptCodeOutputRealizer
    {accept reject attempt : MachineDescription}
    (hattempt :
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt) :
    TapeCodePrimitiveOutputRealizedByDescription
      (PairedRecognizerDovetailStageAttemptCode accept reject)
      attempt := by
  constructor
  · exact hattempt.left
  · intro code out hstage
    exact hattempt.right code out
      (pairedRecognizerDovetailTotalStageAttemptCode_transform_eq_of_stageAttemptCode_eq_some
        hstage)

theorem pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_totalStageAttemptCodeOutputRealizerConstruction
    (hcompile :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction) :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨attempt, hattempt⟩
  exact ⟨attempt,
    pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_totalStageAttemptCodeOutputRealizer
      hattempt⟩

theorem pairedRecognizerDovetailLayoutCodeOutputRealizer_of_subroutineRealizer
    (hcompile :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction) :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨runner, hrunner⟩
  exact ⟨runner,
    tapeCodePrimitiveOutputRealizedByDescription_of_subroutine hrunner⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputRealizer_and_searchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hrunner accept reject with ⟨runner, hrunnerRealizes⟩
  exact hdriver accept reject runner hrunnerRealizes

theorem pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hrunner accept reject with ⟨runner, hrunnerRealizes⟩
  exact hdriver accept reject runner hrunnerRealizes

theorem pairedRecognizerBoundedDovetailTableRealizes_of_runnerSearchDriverRealizes
    {accept reject runner decider : MachineDescription}
    (hrunner :
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner)
    (hdecider :
      PairedRecognizerDovetailRunnerSearchDriverRealizes
        accept reject runner decider) :
    PairedRecognizerBoundedDovetailTableRealizes accept reject decider := by
  constructor
  · exact hdecider.left
  · intro w b
    constructor
    · intro hhalt
      rcases (hdecider.right w b).mp hhalt with
        ⟨limit, _hrunnerHalts, hout⟩
      exact ⟨limit, by
        simpa [pairedRecognizerDovetailLayout_initial_output] using hout⟩
    · intro hbounded
      rcases hbounded with ⟨limit, hout⟩
      apply (hdecider.right w b).mpr
      refine ⟨limit, ?_, ?_⟩
      · exact
          hrunner.right
            (MachineDescription.DovetailLayout.encode
              (MachineDescription.DovetailLayout.initial
                accept reject w limit))
            (MachineDescription.DovetailLayout.encode
              (MachineDescription.DovetailLayout.run accept reject limit
                (MachineDescription.DovetailLayout.initial
                  accept reject w limit)))
            (pairedRecognizerDovetailLayoutCode_encode
              accept reject
              (MachineDescription.DovetailLayout.initial
                accept reject w limit))
      · simpa [pairedRecognizerDovetailLayout_initial_output] using hout

theorem pairedRecognizerDovetailSearchDriverCompiler_of_runnerSearchDriverCompiler
    (hcompile :
      PairedRecognizerDovetailRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailSearchDriverCompilerConstruction := by
  intro accept reject runner hrunner
  rcases hcompile accept reject runner with ⟨decider, hdecider⟩
  exact ⟨decider,
    pairedRecognizerBoundedDovetailTableRealizes_of_runnerSearchDriverRealizes
      hrunner hdecider⟩

theorem pairedRecognizerDovetailSubroutineSearchDriverCompiler_of_subroutineRunnerSearchDriverCompiler
    (hcompile :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction := by
  intro accept reject runner hrunner
  rcases hcompile accept reject runner
      (tapeCodePrimitiveOutputSubroutineRealizedByDescription_subroutineReady
        hrunner) with
    ⟨decider, hdecider⟩
  exact ⟨decider,
    pairedRecognizerBoundedDovetailTableRealizes_of_runnerSearchDriverRealizes
      (tapeCodePrimitiveOutputRealizedByDescription_of_subroutine hrunner)
      hdecider⟩

theorem pairedRecognizerBoundedDovetailTableRealizes_of_stageAttemptSearchDriverRealizes
    {accept reject attempt decider : MachineDescription}
    (hattempt :
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailStageAttemptCode accept reject)
        attempt)
    (hdecider :
      PairedRecognizerDovetailStageAttemptSearchDriverRealizes
        accept reject attempt decider) :
    PairedRecognizerBoundedDovetailTableRealizes
      accept reject decider := by
  constructor
  · exact hdecider.left
  · intro w b
    constructor
    · intro hhalt
      rcases (hdecider.right w b).mp hhalt with
        ⟨limit, _hattemptHalts, hout⟩
      exact ⟨limit, hout⟩
    · intro hbounded
      rcases hbounded with ⟨limit, hout⟩
      apply (hdecider.right w b).mpr
      refine ⟨limit, ?_, hout⟩
      exact
        hattempt.right
          (PairedRecognizerDovetailStageInputCode w limit)
          (MachineDescription.encodeBoolWord [b])
          (by
            rw [pairedRecognizerDovetailStageAttemptCode_encode, hout]
            rfl)

theorem pairedRecognizerBoundedDovetailTableRealizes_of_totalStageAttemptSearchDriverRealizes
    {accept reject attempt decider : MachineDescription}
    (hattempt :
      TapeCodePrimitiveOutputRealizedByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt)
    (hdecider :
      PairedRecognizerDovetailTotalStageAttemptSearchDriverRealizes
        accept reject attempt decider) :
    PairedRecognizerBoundedDovetailTableRealizes
      accept reject decider := by
  constructor
  · exact hdecider.left
  · intro w b
    constructor
    · intro hhalt
      rcases (hdecider.right w b).mp hhalt with
        ⟨limit, _hattemptHalts, hout⟩
      exact ⟨limit, hout⟩
    · intro hbounded
      rcases hbounded with ⟨limit, hout⟩
      apply (hdecider.right w b).mpr
      refine ⟨limit, ?_, hout⟩
      exact
        hattempt.right
          (PairedRecognizerDovetailStageInputCode w limit)
          (MachineDescription.encodeBoolWord [b])
          (by
            rw [pairedRecognizerDovetailTotalStageAttemptCode_encode, hout]
            rfl)

theorem pairedRecognizerBoundedDovetailTableCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
    (hattempt :
      PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hattempt accept reject with ⟨attempt, hattemptRealizes⟩
  rcases hdriver accept reject attempt with ⟨decider, hdecider⟩
  exact ⟨decider,
    pairedRecognizerBoundedDovetailTableRealizes_of_stageAttemptSearchDriverRealizes
      hattemptRealizes hdecider⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_of_totalThenRawOutputCodeOutputRealizer_and_stageAttemptSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  pairedRecognizerBoundedDovetailTableCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
    (pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_totalThenRawOutputCodeOutputRealizerConstruction
      hattempt)
    hdriver

theorem pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  pairedRecognizerBoundedDovetailTableCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
    (pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_totalStageAttemptCodeOutputRealizerConstruction
      hattempt)
    hdriver

theorem pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputSubroutineRealizer_and_totalStageAttemptSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hattempt accept reject with ⟨attempt, hattemptRealizes⟩
  rcases hdriver accept reject attempt
      (tapeCodePrimitiveOutputSubroutineRealizedByDescription_subroutineReady
        hattemptRealizes) with
    ⟨decider, hdecider⟩
  exact ⟨decider,
    pairedRecognizerBoundedDovetailTableRealizes_of_totalStageAttemptSearchDriverRealizes
      (tapeCodePrimitiveOutputRealizedByDescription_of_subroutine
        hattemptRealizes)
      hdecider⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_controllerSearchDriver
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hattempt accept reject with ⟨attempt, hattemptCompiled⟩
  rcases hdriver accept reject attempt
      (tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
        hattemptCompiled) with
    ⟨decider, hdecider⟩
  exact ⟨decider,
    pairedRecognizerBoundedDovetailTableRealizes_of_totalStageAttemptSearchDriverRealizes
      (tapeCodePrimitiveOutputRealizedByDescription_of_outputCompiled
        hattemptCompiled.left)
      (pairedRecognizerDovetailTotalStageAttemptSearchDriverRealizes_of_controllerSearchDriverRealizes
        hattemptCompiled.left hdecider)⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_descriptionBoolDeciderCompiler
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_controllerSearchDriver
    hattempt
    (pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompiler_of_descriptionBoolDeciderCompiler
      hcompile)

theorem pairedRecognizerBoundedDovetailTableCompiler_of_controllerCompilerCloseout
    (hclose : PairedRecognizerDovetailControllerCompilerCloseout) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  pairedRecognizerBoundedDovetailTableCompiler_of_totalStageAttemptCodeOutputCompiledSubroutine_and_controllerSearchDriver
    hclose.totalStageAttemptSubroutine
    hclose.controllerSearchDriver

theorem pairedRecognizerBoundedDovetailTableCompiler_of_finiteControllerCompilerCloseout
    (hclose : PairedRecognizerDovetailFiniteControllerCompilerCloseout) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  pairedRecognizerBoundedDovetailTableCompiler_of_controllerCompilerCloseout
    (pairedRecognizerDovetailControllerCompilerCloseout_of_finiteControllerCloseout
      hclose)

theorem pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineRunnerSearchDriver
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
    hrunner
    (pairedRecognizerDovetailSubroutineSearchDriverCompiler_of_subroutineRunnerSearchDriverCompiler
      hdriver)

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_codeCompiler
    {D simulator : MachineDescription}
    (hcompile : TapeCodePrimitiveCompiledByDescription
      (FixedDescriptionBoundedSimulatorCode D) simulator) :
    FixedDescriptionBoundedSimulatorTableRealizes D simulator := by
  constructor
  · exact hcompile.left
  · intro L
    have hExact :
        simulator.HaltsWithExactOutput
          (FixedDescriptionBoundedSimulatorInput L)
          (FixedDescriptionBoundedSimulatorOutput D L) := by
      have hcode := (hcompile.right
        (MachineDescription.SimulatorLayout.encode L)
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run D L.stage L))).mpr
          (fixedDescriptionBoundedSimulatorCode_encode D L)
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorOutput,
        MachineDescription.SimulatorLayout.asBoolInput] using hcode
    exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput hExact

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_codeCompiler
    (hcompile :
      FixedDescriptionBoundedSimulatorCodeCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨simulator, hsimulator⟩
  exact ⟨simulator,
    fixedDescriptionBoundedSimulatorTableRealizes_of_codeCompiler
      hsimulator⟩

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_codeOutputRealizer
    {D simulator : MachineDescription}
    (hcompile : TapeCodePrimitiveOutputRealizedByDescription
      (FixedDescriptionBoundedSimulatorCode D) simulator) :
    FixedDescriptionBoundedSimulatorTableRealizes D simulator := by
  constructor
  · exact hcompile.left
  · intro L
    exact hcompile.right
      (MachineDescription.SimulatorLayout.encode L)
      (MachineDescription.SimulatorLayout.encode
        (MachineDescription.SimulatorLayout.run D L.stage L))
      (fixedDescriptionBoundedSimulatorCode_encode D L)

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_codeOutputRealizer
    (hcompile :
      FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨simulator, hsimulator⟩
  exact ⟨simulator,
    fixedDescriptionBoundedSimulatorTableRealizes_of_codeOutputRealizer
      hsimulator⟩

structure MachineDescriptionCompilerCloseout where
  stepCodeOutput :
    FixedDescriptionStepCodeOutputRealizerConstruction
  stepConfiguration :
    FixedDescriptionStepCodeConfigurationRealizerConstruction
  boundedSimulatorCodeOutput :
    FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction
  boundedSimulatorTable :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction
  dovetailInitialLayoutCodeOutput :
    PairedRecognizerDovetailInitialLayoutCodeOutputRealizerConstruction
  dovetailLayoutCodeOutput :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction
  dovetailOutputCodeOutput :
    PairedRecognizerDovetailOutputCodeOutputRealizerConstruction
  dovetailStageAttemptCodeOutput :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction
  dovetailTotalStageAttemptCodeOutput :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction
  dovetailControllerContinueCodeOutput :
    PairedRecognizerDovetailControllerContinueCodeOutputRealizerConstruction
  dovetailControllerEmitCodeOutput :
    PairedRecognizerDovetailControllerEmitCodeOutputRealizerConstruction

def machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    MachineDescriptionCompilerCloseout where
  stepCodeOutput := by
    intro D
    exact hcompile (FixedDescriptionStepCode D)
  stepConfiguration :=
    fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction
      (by
        intro D
        exact hcompile (FixedDescriptionStepCode D))
  boundedSimulatorCodeOutput := by
    intro D
    exact hcompile (FixedDescriptionBoundedSimulatorCode D)
  boundedSimulatorTable :=
    fixedDescriptionBoundedSimulatorTableCompiler_of_codeOutputRealizer
      (by
        intro D
        exact hcompile (FixedDescriptionBoundedSimulatorCode D))
  dovetailLayoutCodeOutput := by
    intro accept reject
    exact hcompile (PairedRecognizerDovetailLayoutCode accept reject)
  dovetailInitialLayoutCodeOutput := by
    intro accept reject
    exact hcompile
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
  dovetailOutputCodeOutput :=
    hcompile PairedRecognizerDovetailOutputCode
  dovetailStageAttemptCodeOutput := by
    intro accept reject
    exact hcompile
      (PairedRecognizerDovetailStageAttemptCode accept reject)
  dovetailTotalStageAttemptCodeOutput := by
    intro accept reject
    exact hcompile
      (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
  dovetailControllerContinueCodeOutput := by
    intro accept reject
    exact hcompile
      (PairedRecognizerDovetailControllerContinueCode accept reject)
  dovetailControllerEmitCodeOutput := by
    intro accept reject
    exact hcompile
      (PairedRecognizerDovetailControllerEmitCode accept reject)

theorem fixedDescriptionStepCodeConfigurationRealizerConstruction_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    FixedDescriptionStepCodeConfigurationRealizerConstruction :=
  (machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile).stepConfiguration

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  (machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile).boundedSimulatorTable

theorem pairedRecognizerDovetailLayoutCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction :=
  (machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile).dovetailLayoutCodeOutput


end Computability
end FoC
