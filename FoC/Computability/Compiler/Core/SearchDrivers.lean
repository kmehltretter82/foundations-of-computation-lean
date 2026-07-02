import FoC.Computability.Compiler.Core.FiniteScaffolds

set_option doc.verso true

/-!
# Search-driver compiler bridges
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

noncomputable def PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
    (attempt : MachineDescription) :
    StagedProgram Bool Bool :=
  by
    classical
    exact
      { run := fun w limit =>
          if attempt.HaltsWithOutput
              (encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (encodeCodeWordAsInput
                (encodeBoolWord [true])) then
            some [true]
          else if attempt.HaltsWithOutput
              (encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (encodeCodeWordAsInput
                (encodeBoolWord [false])) then
            some [false]
          else
            none }

def PairedRecognizerDovetailStageAttemptOutputFunctional
    (attempt : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall limit : Nat,
  forall result1 result2 : Word Bool,
    attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (encodeCodeWordAsInput
          (encodeBoolWord result1)) ->
    attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (encodeCodeWordAsInput
          (encodeBoolWord result2)) ->
      result1 = result2

theorem pairedRecognizerDovetailStageAttemptOutputFunctional_of_subroutineReady
    {attempt : MachineDescription}
    (hattemptReady : attempt.SubroutineReady) :
    PairedRecognizerDovetailStageAttemptOutputFunctional attempt := by
  intro w limit result1 result2 h1 h2
  exact
    haltsWithOutput_encodedBoolWord_functional
      hattemptReady h1 h2

theorem pairedRecognizerDovetailStageAttemptOutputFunctional_of_protectedInvocation
    {attempt invoker : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker) :
    PairedRecognizerDovetailStageAttemptOutputFunctional attempt := by
  intro w limit result1 result2 h1 h2
  exact
    pairedRecognizerDovetailStageAttemptProtectedInvocation_attempt_output_functional
      hinvoker
      ({ input := w, stage := limit, result := [] } :
        DovetailControllerLayout)
      (by
        simpa [PairedRecognizerDovetailControllerStageInputCode,
          PairedRecognizerDovetailStageInputCode] using h1)
      (by
        simpa [PairedRecognizerDovetailControllerStageInputCode,
          PairedRecognizerDovetailStageInputCode] using h2)

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutput_iff_of_functional
    (attempt : MachineDescription)
    (hfunctional :
      PairedRecognizerDovetailStageAttemptOutputFunctional attempt)
    (w : Word Bool) (b : Bool) :
    ProgramHaltsWithOutput
        (PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
          attempt) w [b] <->
      exists limit : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput
            (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] := by
  classical
  constructor
  · intro h
    rcases h with ⟨limit, hrun⟩
    cases b
    · by_cases htrue :
        attempt.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput
            (encodeBoolWord [true]))
      · simp [PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram,
          htrue] at hrun
        cases hrun
      · by_cases hfalse :
          attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord [false]))
        · exact ⟨limit, [false], hfalse, by
            simp [PairedRecognizerDovetailControllerRawOutput,
              DovetailControllerLayout.rawOutput_singleton]⟩
        · simp [PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram,
            htrue, hfalse] at hrun
    · by_cases htrue :
        attempt.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput
            (encodeBoolWord [true]))
      · exact ⟨limit, [true], htrue, by
          simp [PairedRecognizerDovetailControllerRawOutput,
            DovetailControllerLayout.rawOutput_singleton]⟩
      · simp [PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram,
          htrue] at hrun
        cases hrun.right
  · intro h
    rcases h with ⟨limit, result, hattempt, hraw⟩
    have hresult : result = [b] :=
      (DovetailControllerLayout.rawOutput_eq_some_singleton_iff
        result b).mp hraw
    subst result
    refine ⟨limit, ?_⟩
    cases b
    · have hnotTrue :
          ¬ attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord [true])) := by
        intro htrue
        have hbool : [false] = [true] :=
          hfunctional w limit [false] [true] hattempt htrue
        cases hbool
      rw [show
          (PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
            attempt).run w limit =
            (if attempt.HaltsWithOutput
                (encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w limit))
                (encodeCodeWordAsInput
                  (encodeBoolWord [true])) then
              some [true]
            else if attempt.HaltsWithOutput
                (encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w limit))
                (encodeCodeWordAsInput
                  (encodeBoolWord [false])) then
              some [false]
            else
              none) by
          rfl]
      rw [if_neg hnotTrue, if_pos hattempt]
      rfl
    · simp [PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram,
        hattempt]

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
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput
            (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] :=
  pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutput_iff_of_functional
    attempt
    (pairedRecognizerDovetailStageAttemptOutputFunctional_of_subroutineReady
      hattemptReady)
    w b

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutput_iff_of_protectedInvocation
    {attempt invoker : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (w : Word Bool) (b : Bool) :
    ProgramHaltsWithOutput
        (PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
          attempt) w [b] <->
      exists limit : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput
            (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] :=
  pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutput_iff_of_functional
    attempt
    (pairedRecognizerDovetailStageAttemptOutputFunctional_of_protectedInvocation
      hinvoker)
    w b

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutputIn_iff_of_functional
    (attempt : MachineDescription)
    (hfunctional :
      PairedRecognizerDovetailStageAttemptOutputFunctional attempt)
    (w : Word Bool) (b : Bool) :
    ProgramHaltsWithOutput
        (PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
          attempt) w [b] <->
      exists limit : Nat,
      exists fuel : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutputIn fuel
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput
            (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] := by
  constructor
  · intro h
    rcases
        (pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutput_iff_of_functional
          attempt hfunctional w b).mp h with
      ⟨limit, result, hattempt, hraw⟩
    rcases
        MachineDescription.haltsWithOutput_iff_exists_haltsWithOutputIn.mp
          hattempt with
      ⟨fuel, hfuel⟩
    exact ⟨limit, fuel, result, hfuel, hraw⟩
  · intro h
    rcases h with ⟨limit, fuel, result, hattempt, hraw⟩
    exact
      (pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutput_iff_of_functional
        attempt hfunctional w b).mpr
        ⟨limit, result,
          MachineDescription.haltsWithOutput_iff_exists_haltsWithOutputIn.mpr
            ⟨fuel, hattempt⟩,
          hraw⟩

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutputIn_iff
    (attempt : MachineDescription)
    (hattemptReady : attempt.SubroutineReady)
    (w : Word Bool) (b : Bool) :
    ProgramHaltsWithOutput
        (PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
          attempt) w [b] <->
      exists limit : Nat,
      exists fuel : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutputIn fuel
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput
            (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] :=
  pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutputIn_iff_of_functional
    attempt
    (pairedRecognizerDovetailStageAttemptOutputFunctional_of_subroutineReady
      hattemptReady)
    w b

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutputIn_iff_of_protectedInvocation
    {attempt invoker : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (w : Word Bool) (b : Bool) :
    ProgramHaltsWithOutput
        (PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
          attempt) w [b] <->
      exists limit : Nat,
      exists fuel : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutputIn fuel
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput
            (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] :=
  pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutputIn_iff_of_functional
    attempt
    (pairedRecognizerDovetailStageAttemptOutputFunctional_of_protectedInvocation
      hinvoker)
    w b

theorem Search.controllerCompilerOfDeciderOfFunctional
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple)
    (attempt : MachineDescription)
    (hfunctional :
      PairedRecognizerDovetailStageAttemptOutputFunctional attempt) :
    exists decider : MachineDescription,
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider := by
  rcases hcompile
      (PairedRecognizerDovetailTotalStageAttemptControllerSearchProgram
        attempt) with
    ⟨decider, hdecider⟩
  refine ⟨decider, ?_⟩
  constructor
  · exact hdecider.left
  · intro w b
    exact Iff.trans (hdecider.right w b)
      (pairedRecognizerDovetailTotalStageAttemptControllerSearchProgram_haltsWithOutput_iff_of_functional
        attempt hfunctional w b)

theorem Search.controllerCompilerOfDeciderOfProtectedInvocation
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple)
    {attempt invoker : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker) :
    exists decider : MachineDescription,
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider :=
  Search.controllerCompilerOfDeciderOfFunctional
    hcompile attempt
    (pairedRecognizerDovetailStageAttemptOutputFunctional_of_protectedInvocation
      hinvoker)

theorem Search.protectedControllerSearchDriverConstructionOfDecider
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction := by
  intro attempt invoker hinvoker
  exact
    Search.controllerCompilerOfDeciderOfProtectedInvocation
      hcompile hinvoker

theorem Search.controllerCompilerOfDecider
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction := by
  intro _accept _reject attempt hattemptReady
  exact
    Search.controllerCompilerOfDeciderOfFunctional
      hcompile attempt
      (pairedRecognizerDovetailStageAttemptOutputFunctional_of_subroutineReady
        hattemptReady)

noncomputable def PairedRecognizerDovetailStageAttemptSearchProgram
    (accept reject attempt : MachineDescription) :
    StagedProgram Bool Bool :=
  by
    classical
    exact
      { run := fun w limit =>
          if attempt.HaltsWithOutput
              (encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (encodeCodeWordAsInput
                (encodeBoolWord [true])) ∧
              boundedDovetailOutput
                accept reject w limit = some [true] then
            some [true]
          else if attempt.HaltsWithOutput
              (encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (encodeCodeWordAsInput
                (encodeBoolWord [false])) ∧
              boundedDovetailOutput
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
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w limit))
          (encodeCodeWordAsInput
            (encodeBoolWord [b])) ∧
        boundedDovetailOutput
          accept reject w limit = some [b] := by
  classical
  constructor
  · intro h
    rcases h with ⟨limit, hrun⟩
    cases b
    · by_cases htrue :
        attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord [true])) ∧
          boundedDovetailOutput
            accept reject w limit = some [true]
      · simp [PairedRecognizerDovetailStageAttemptSearchProgram,
          htrue] at hrun
        cases hrun
      · by_cases hfalse :
          attempt.HaltsWithOutput
              (encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (encodeCodeWordAsInput
              (encodeBoolWord [false])) ∧
            boundedDovetailOutput
              accept reject w limit = some [false]
        · exact ⟨limit, hfalse⟩
        · simp [PairedRecognizerDovetailStageAttemptSearchProgram,
            htrue, hfalse] at hrun
    · by_cases htrue :
        attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord [true])) ∧
          boundedDovetailOutput
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
              (encodeCodeWordAsInput
                (PairedRecognizerDovetailStageInputCode w limit))
              (encodeCodeWordAsInput
                (encodeBoolWord [false])) ∧
            boundedDovetailOutput
              accept reject w limit = some [false] := by
        exact ⟨hattempt, hout⟩
      have hnotTrue :
          ¬ (attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord [true])) ∧
              boundedDovetailOutput
              accept reject w limit = some [true]) := by
        intro htrue
        rw [hout] at htrue
        cases htrue.right
      rw [show
          (PairedRecognizerDovetailStageAttemptSearchProgram
            accept reject attempt).run w limit =
            (if
              attempt.HaltsWithOutput
                (encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w limit))
                (encodeCodeWordAsInput
                  (encodeBoolWord [true])) ∧
              boundedDovetailOutput
                accept reject w limit = some [true] then
              some [true]
            else if
              attempt.HaltsWithOutput
                (encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w limit))
                (encodeCodeWordAsInput
                  (encodeBoolWord [false])) ∧
              boundedDovetailOutput
                accept reject w limit = some [false] then
              some [false]
            else
              none) by
          rfl]
      rw [if_neg hnotTrue, if_pos hfalse]
      rfl
    · simp [PairedRecognizerDovetailStageAttemptSearchProgram,
        hattempt, hout]

theorem Search.stageCompilerOfDecider
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

theorem Search.totalStageCompilerOfDecider
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
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (encodeCodeWordAsInput
          (encodeBoolWord result)) ∧
      PairedRecognizerDovetailControllerRawOutput result = some [b]) <->
    boundedDovetailOutput accept reject w limit =
      some [b] := by
  constructor
  · intro h
    rcases h with ⟨result, hattemptHalt, hraw⟩
    have htransform :
        (PairedRecognizerDovetailTotalStageAttemptCode
          accept reject).transform
            (PairedRecognizerDovetailStageInputCode w limit) =
          some (encodeBoolWord result) :=
      (hattempt.right
        (PairedRecognizerDovetailStageInputCode w limit)
        (encodeBoolWord result)).mp hattemptHalt
    have hcanonical :
        (PairedRecognizerDovetailTotalStageAttemptCode
          accept reject).transform
            (PairedRecognizerDovetailStageInputCode w limit) =
          some
            (encodeBoolWord
              (DovetailLayout.outputWordFromOption
                (boundedDovetailOutput
                  accept reject w limit))) :=
      pairedRecognizerDovetailTotalStageAttemptCode_encode
        accept reject w limit
    have hencoded :
        encodeBoolWord result =
          encodeBoolWord
            (DovetailLayout.outputWordFromOption
              (boundedDovetailOutput
                accept reject w limit)) := by
      have hsome :
          some (encodeBoolWord result) =
            some
              (encodeBoolWord
                (DovetailLayout.outputWordFromOption
                  (boundedDovetailOutput
                    accept reject w limit))) := by
        rw [← htransform, hcanonical]
      exact Option.some.inj hsome
    have hresult :
        result =
          DovetailLayout.outputWordFromOption
            (boundedDovetailOutput
              accept reject w limit) :=
      encodeBoolWord_injective hencoded
    rw [PairedRecognizerDovetailControllerRawOutput, hresult,
      DovetailControllerLayout.rawOutput_outputWordFromOption_boundedDovetailOutput]
      at hraw
    exact hraw
  · intro hbounded
    refine ⟨[b], ?_, ?_⟩
    · exact
        (hattempt.right
          (PairedRecognizerDovetailStageInputCode w limit)
          (encodeBoolWord [b])).mpr
          (by
            rw [pairedRecognizerDovetailTotalStageAttemptCode_encode,
              hbounded]
            rfl)
    · simp [PairedRecognizerDovetailControllerRawOutput,
        DovetailControllerLayout.rawOutput_singleton]

theorem Search.realizesOfControllerRealizes
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
          boundedDovetailOutput
            accept reject w limit = some [b] := by
        exact
          (pairedRecognizerDovetailTotalStageAttemptControllerRawOutput_iff_of_outputCompiled
            hattempt w limit b).mp
            ⟨result, hattemptHalt, hraw⟩
      refine ⟨limit, ?_, hbounded⟩
      exact
        (hattempt.right
          (PairedRecognizerDovetailStageInputCode w limit)
          (encodeBoolWord [b])).mpr
          (by
            rw [pairedRecognizerDovetailTotalStageAttemptCode_encode,
              hbounded]
            rfl)
    · intro hbounded
      rcases hbounded with ⟨limit, hattemptHalt, hout⟩
      apply (hdriver.right w b).mpr
      refine ⟨limit, [b], hattemptHalt, ?_⟩
      simp [PairedRecognizerDovetailControllerRawOutput,
        DovetailControllerLayout.rawOutput_singleton]

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
    simp [stepConfigurationCodePrimitive,
      stepConfigurationCode] at hcode
    cases hdecode : decodeConfiguration code with
    | none =>
        simp [hdecode] at hcode
    | some parsed =>
        cases parsed with
        | mk c suffix =>
            cases suffix with
            | nil =>
                simp [hdecode] at hcode
                have hcanonical :
                    code = encodeConfiguration c :=
                  decodeConfiguration_eq_some_encodeConfiguration
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
      (encodeConfiguration c)
      (encodeConfiguration (D.runConfig 1 c))
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
        TapeCodePrimitive.identity stepper)
    (hD : forall c : Configuration,
      D.runConfig 1 c = c) :
    FixedDescriptionStepCodeConfigurationRealizes D stepper := by
  constructor
  · exact hstepper.left
  · intro c
    rw [hD c]
    exact hstepper.right
      (encodeConfiguration c)
      (encodeConfiguration c)
      rfl

theorem runConfig_one_eq_id_of_transitions_nil
    {D : MachineDescription}
    (hD : D.transitions = []) :
    forall c : Configuration, D.runConfig 1 c = c := by
  intro c
  cases c
  simp [runConfig, stepConfig,
    lookupTransition, hD]

theorem fixedDescriptionStepCodeConfigurationRealizes_transitionless
    {D : MachineDescription}
    (hD : D.transitions = []) :
    FixedDescriptionStepCodeConfigurationRealizes
      D ExactIdentityDescription :=
  fixedDescriptionStepCodeConfigurationRealizes_of_runConfig_one_eq_id
    tapeCodePrimitiveOutputRealizedByDescription_identity
    (runConfig_one_eq_id_of_transitions_nil hD)

theorem fixedDescriptionStepCodeConfigurationRealizes_exactIdentityDescription :
    FixedDescriptionStepCodeConfigurationRealizes
      ExactIdentityDescription
      ExactIdentityDescription := by
  constructor
  · exact exactIdentityDescription_wellFormed
  · intro c
    have hrun :
        ExactIdentityDescription.runConfig 1 c = c := by
      cases c
      simp [runConfig,
        stepConfig,
        lookupTransition,
        ExactIdentityDescription]
    rw [hrun]
    exact haltsWithOutput_of_haltsWithExactOutput
      ((exactIdentityDescription_haltsWithExactOutput_iff
        (encodeCodeWordAsInput
          (encodeConfiguration c))
        (encodeCodeWordAsInput
          (encodeConfiguration c))).mpr rfl)

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
    PairedRecognizerDovetailInitialLayoutCodeOutputRealizerConstruction :=
  fun accept reject =>
    hcompile (PairedRecognizerDovetailInitialLayoutCode accept reject)

theorem pairedRecognizerDovetailOutputCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailOutputCodeOutputRealizerConstruction :=
  hcompile PairedRecognizerDovetailOutputCode

theorem pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction :=
  fun accept reject =>
    hcompile (PairedRecognizerDovetailStageAttemptCode accept reject)

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction :=
  fun accept reject =>
    hcompile (PairedRecognizerDovetailTotalStageAttemptCode accept reject)

theorem pairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction :=
  fun accept reject =>
    hcompile (PairedRecognizerDovetailTotalThenRawOutputCode accept reject)

theorem pairedRecognizerDovetailControllerContinueCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailControllerContinueCodeOutputRealizerConstruction :=
  fun accept reject =>
    hcompile (PairedRecognizerDovetailControllerContinueCode accept reject)

theorem pairedRecognizerDovetailControllerEmitCodeOutputRealizer_of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailControllerEmitCodeOutputRealizerConstruction :=
  fun accept reject =>
    hcompile (PairedRecognizerDovetailControllerEmitCode accept reject)

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

namespace PairedRecognizerDovetail

namespace StageAttemptCodeOutputRealizer

theorem of_totalThenRawOutputConstruction
    (hcompile :
      PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction) :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨attempt, hattempt⟩
  exact ⟨attempt,
    pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_totalThenRawOutputCodeOutputRealizer
      hattempt⟩

end StageAttemptCodeOutputRealizer

end PairedRecognizerDovetail

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
  unfold TapeCodePrimitive.compose at hcompose
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

theorem Search.stageOutputOfTotal
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

theorem Search.stageOutputConstructionOfTotal
    (hcompile :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction) :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨attempt, hattempt⟩
  exact ⟨attempt,
    Search.stageOutputOfTotal
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

namespace PairedRecognizerBoundedDovetailTableCompiler

theorem of_layoutSubroutine_and_subroutineSearch
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction := by
  intro accept reject
  rcases hrunner accept reject with ⟨runner, hrunnerRealizes⟩
  exact hdriver accept reject runner hrunnerRealizes

end PairedRecognizerBoundedDovetailTableCompiler

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
            (DovetailLayout.encode
              (DovetailLayout.initial
                accept reject w limit))
            (DovetailLayout.encode
              (DovetailLayout.run accept reject limit
                (DovetailLayout.initial
                  accept reject w limit)))
            (pairedRecognizerDovetailLayoutCode_encode
              accept reject
              (DovetailLayout.initial
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
          (encodeBoolWord [b])
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
          (encodeBoolWord [b])
          (by
            rw [pairedRecognizerDovetailTotalStageAttemptCode_encode, hout]
            rfl)

namespace PairedRecognizerBoundedDovetailTableCompiler

theorem of_stageAttemptOutput_and_search
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

theorem of_totalThenRawOutput_and_search
    (hattempt :
      PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  of_stageAttemptOutput_and_search
    (PairedRecognizerDovetail.StageAttemptCodeOutputRealizer.of_totalThenRawOutputConstruction
      hattempt)
    hdriver

theorem of_totalStageAttemptOutput_and_search
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  of_stageAttemptOutput_and_search
    (Search.stageOutputConstructionOfTotal
      hattempt)
    hdriver

end PairedRecognizerBoundedDovetailTableCompiler

theorem Search.boundedCompilerOfSubroutineAndTotalSearch
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

theorem Search.boundedCompilerOfCompiledSubroutineAndController
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
      (Search.realizesOfControllerRealizes
        hattemptCompiled.left hdecider)⟩

theorem Search.boundedCompilerOfCompiledSubroutineAndDecider
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Search.boundedCompilerOfCompiledSubroutineAndController
    hattempt
    (Search.controllerCompilerOfDecider
      hcompile)

theorem pairedRecognizerBoundedDovetailTableCompiler_of_controllerCompilerCloseout
    (hclose : PairedRecognizerDovetailControllerCompilerCloseout) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  Search.boundedCompilerOfCompiledSubroutineAndController
    hclose.totalStageAttemptSubroutine
    hclose.controllerSearchDriver

theorem pairedRecognizerBoundedDovetailTableCompiler_of_finiteControllerCompilerCloseout
    (hclose : PairedRecognizerDovetailFiniteControllerCompilerCloseout) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  pairedRecognizerBoundedDovetailTableCompiler_of_controllerCompilerCloseout
    (pairedRecognizerDovetailControllerCompilerCloseout_of_finiteControllerCloseout
      hclose)

namespace PairedRecognizerBoundedDovetailTableCompiler

theorem of_layoutSubroutine_and_runnerSearch
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerBoundedDovetailTableCompilerConstruction :=
  of_layoutSubroutine_and_subroutineSearch
    hrunner
    (pairedRecognizerDovetailSubroutineSearchDriverCompiler_of_subroutineRunnerSearchDriverCompiler
      hdriver)

end PairedRecognizerBoundedDovetailTableCompiler

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
        (SimulatorLayout.encode L)
        (SimulatorLayout.encode
          (SimulatorLayout.run D L.stage L))).mpr
          (fixedDescriptionBoundedSimulatorCode_encode D L)
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorOutput,
        SimulatorLayout.asBoolInput] using hcode
    exact haltsWithOutput_of_haltsWithExactOutput hExact

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
      (SimulatorLayout.encode L)
      (SimulatorLayout.encode
        (SimulatorLayout.run D L.stage L))
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

end Computability
end FoC
