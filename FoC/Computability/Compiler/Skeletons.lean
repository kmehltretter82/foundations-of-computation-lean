import FoC.Computability.Compiler.FixedSimulatorSkeletons
import FoC.Computability.Compiler.Core.TapeCodePrimitiveSequencing
import FoC.Computability.Compiler.Core.FiniteScaffolds
import FoC.Computability.Compiler.Core.SearchDrivers
import FoC.Computability.Compiler.Core.Closeout

set_option doc.verso true

/-!
# Fixed-simulator skeleton compiler bridges
-/

namespace FoC
namespace Computability

open Languages

theorem pairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction := by
  intro accept reject initializer runner emitter
    hinitializer hrunner hemitter
  let initRunner :=
    MachineDescription.seqSubroutine initializer runner
      tapeCodePrimitiveCodeWordHandoffMove
  let attempt :=
    MachineDescription.seqSubroutine initRunner emitter
      tapeCodePrimitiveCodeWordHandoffMove
  refine ⟨attempt, ?_⟩
  have hfirst :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (MachineDescription.TapeCodePrimitive.compose
          (PairedRecognizerDovetailInitialLayoutCode accept reject)
          (PairedRecognizerDovetailLayoutCode accept reject))
        initRunner tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_compose
      hinitializer hrunner
  have hsecond :
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        (MachineDescription.TapeCodePrimitive.compose
          (MachineDescription.TapeCodePrimitive.compose
            (PairedRecognizerDovetailInitialLayoutCode accept reject)
            (PairedRecognizerDovetailLayoutCode accept reject))
          PairedRecognizerDovetailTotalOutputCode)
        attempt :=
    by
      let firstCode :=
        MachineDescription.TapeCodePrimitive.compose
          (PairedRecognizerDovetailInitialLayoutCode accept reject)
          (PairedRecognizerDovetailLayoutCode accept reject)
      let totalCode :=
        MachineDescription.TapeCodePrimitive.compose firstCode
          PairedRecognizerDovetailTotalOutputCode
      have hrealized :
          TapeCodePrimitiveOutputSubroutineRealizedByDescription
            totalCode attempt :=
        tapeCodePrimitiveHandoffSubroutineRealizedByDescription_compose_output
          (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
            hfirst)
          hemitter
      have hAready : initRunner.SubroutineReady :=
        tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
          hfirst
      have hBready : emitter.SubroutineReady :=
        tapeCodePrimitiveOutputSubroutineRealizedByDescription_subroutineReady
          hemitter
      constructor
      · constructor
        · exact hrealized.left.left
        · intro code out
          constructor
          · intro hhalt
            rcases hhalt with ⟨n, hn⟩
            let Tout : Tape Bool :=
              (attempt.runConfig n
                (attempt.initial
                  (MachineDescription.encodeCodeWordAsInput code))).tape
            have hSeqTape :
                attempt.HaltsWithTape
                  (MachineDescription.encodeCodeWordAsInput code) Tout := by
              refine ⟨n, ?_⟩
              exact ⟨hn.left, rfl⟩
            have hToutNorm :
                Tape.normalizedOutput Tout =
                  MachineDescription.encodeCodeWordAsInput out :=
              hn.right
            rcases MachineDescription.seqSubroutine_haltsWithTape_inv
                hAready hBready hSeqTape with
              ⟨Tmid, hFirstTape, hEmitterReach⟩
            rcases hfirst.right code Tmid hFirstTape with
              ⟨mid, hFirstCode, _hmidNorm, hTmidMove⟩
            have hmidLayout :
                exists L : MachineDescription.DovetailLayout,
                  mid = MachineDescription.DovetailLayout.encode L := by
              unfold MachineDescription.TapeCodePrimitive.compose at hFirstCode
              cases hinit :
                  (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
                    code with
              | none =>
                  simp [hinit] at hFirstCode
              | some initOut =>
                  have hrunnerMid :
                      (PairedRecognizerDovetailLayoutCode accept reject).transform
                          initOut =
                        some mid := by
                    simpa [hinit] using hFirstCode
                  rcases
                      (pairedRecognizerDovetailLayoutCode_transform_eq_some_iff
                        accept reject initOut mid).mp hrunnerMid with
                    ⟨L, _hinitOut, hmid⟩
                  exact ⟨MachineDescription.DovetailLayout.run
                    accept reject L.stage L, hmid⟩
            rcases hmidLayout with ⟨Lmid, hmid⟩
            subst mid
            let expected : Word MachineCodeSymbol :=
              MachineDescription.encodeBoolWord
                (MachineDescription.DovetailLayout.outputWordFromHits Lmid)
            have hExpected :
                PairedRecognizerDovetailTotalOutputCode.transform
                    (MachineDescription.DovetailLayout.encode Lmid) =
                  some expected := by
              exact pairedRecognizerDovetailTotalOutputCode_encode Lmid
            rcases hEmitterReach with ⟨nB, hBRun⟩
            have hBRunInput :
                emitter.runConfig nB
                    (emitter.initial
                      (MachineDescription.encodeCodeWordAsInput
                        (MachineDescription.DovetailLayout.encode Lmid))) =
                  { state := emitter.halt, tape := Tout } := by
              change
                emitter.runConfig nB
                    { state := emitter.start,
                      tape := Tape.input
                        (MachineDescription.encodeCodeWordAsInput
                          (MachineDescription.DovetailLayout.encode Lmid)) } =
                  { state := emitter.halt, tape := Tout }
              simpa [hTmidMove] using hBRun
            have hBOut :
                emitter.HaltsWithOutput
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.DovetailLayout.encode Lmid))
                  (MachineDescription.encodeCodeWordAsInput out) := by
              refine ⟨nB, ?_⟩
              constructor
              · exact congrArg MachineDescription.Configuration.state
                  hBRunInput
              · change
                  Tape.normalizedOutput
                      (emitter.runConfig nB
                        (emitter.initial
                          (MachineDescription.encodeCodeWordAsInput
                            (MachineDescription.DovetailLayout.encode Lmid)))).tape =
                    MachineDescription.encodeCodeWordAsInput out
                rw [hBRunInput]
                exact hToutNorm
            have hBExpected :
                emitter.HaltsWithOutput
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.DovetailLayout.encode Lmid))
                  (MachineDescription.encodeCodeWordAsInput expected) :=
              hemitter.left.right
                (MachineDescription.DovetailLayout.encode Lmid)
                expected hExpected
            have hout : out = expected :=
              haltsWithEncodedCodeOutput_functional_of_haltTransitionFree
                hemitter.right hBOut hBExpected
            exact
              MachineDescription.TapeCodePrimitive.compose_transform_some
                hFirstCode
                (by simpa [hout] using hExpected)
          · intro htransform
            exact hrealized.left.right code out htransform
      · exact hrealized.right
  simpa [PairedRecognizerDovetailTotalStageAttemptSourceCode,
    initRunner, attempt] using hsecond

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction :=
  pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_of_finiteSourceComponents
    pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailBoundedLayoutRunnerClosedHandoffCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction_scaffold
    pairedRecognizerDovetailTotalStageAttemptSubroutineSequencingConstruction_scaffold

def pairedRecognizerDovetailFiniteControllerCompilerCloseout_scaffold :
    PairedRecognizerDovetailFiniteControllerCompilerCloseout where
  totalStageAttemptSubroutine :=
    pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_scaffold
  finiteStageLoopController :=
    pairedRecognizerDovetailFiniteStageLoopControllerConstruction_scaffold

theorem pairedRecognizerDovetailTotalStageAttemptHandoffSubroutineRealizerSequencingConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptHandoffSubroutineRealizerSequencingConstruction := by
  intro accept reject initializer runner emitter
    hinitializer hrunner hemitter
  let initRunner :=
    MachineDescription.seqSubroutine initializer runner
      tapeCodePrimitiveCodeWordHandoffMove
  let attempt :=
    MachineDescription.seqSubroutine initRunner emitter
      tapeCodePrimitiveCodeWordHandoffMove
  refine ⟨attempt, ?_⟩
  have hinitRealized :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_of_handoffCompiled
      hinitializer
  have hrunnerRealized :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (PairedRecognizerDovetailLayoutCode accept reject)
        runner tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_of_handoffCompiled
      hrunner
  have hemitterRealized :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        PairedRecognizerDovetailTotalOutputCode
        emitter tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_of_handoffCompiled
      hemitter
  have hfirst :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (MachineDescription.TapeCodePrimitive.compose
          (PairedRecognizerDovetailInitialLayoutCode accept reject)
          (PairedRecognizerDovetailLayoutCode accept reject))
        initRunner tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_compose
      hinitRealized hrunnerRealized
  have hsecond :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (MachineDescription.TapeCodePrimitive.compose
          (MachineDescription.TapeCodePrimitive.compose
            (PairedRecognizerDovetailInitialLayoutCode accept reject)
            (PairedRecognizerDovetailLayoutCode accept reject))
          PairedRecognizerDovetailTotalOutputCode)
        attempt tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_compose
      hfirst hemitterRealized
  simpa [PairedRecognizerDovetailTotalStageAttemptSourceCode,
    initRunner, attempt] using hsecond

theorem pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile
    (fun w n => accept.HaltsIn n w)
    (fun w n => reject.HaltsIn n w)

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
            using hlimit⟩
    · intro hlimit
      rcases hlimit with ⟨limit, hlimit⟩
      apply (hdecider.right w b).mpr
      exact
        ⟨limit, by
          simpa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
            using hlimit⟩

theorem pairedRecognizerBoundedDovetailTableCompiler_iff_pairedRecognizerDovetailDescriptionCompiler :
    PairedRecognizerBoundedDovetailTableCompilerConstruction <->
      PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  ⟨pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler,
    pairedRecognizerBoundedDovetailTableCompiler_of_pairedRecognizerDovetailDescriptionCompiler⟩

theorem DescriptionCompiler.ofLayoutAndSearch
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputRealizer_and_searchDriver
      hrunner hdriver)

theorem DescriptionCompiler.ofStageAttemptAndSearch
    (hattempt :
      PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_stageAttemptCodeOutputRealizer_and_stageAttemptSearchDriver
      hattempt hdriver)

theorem DescriptionCompiler.ofTapeCodeAndDecider
    (htape : MachineDescriptionTapeCodeOutputCompilerConstruction)
    (hbool : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  DescriptionCompiler.ofStageAttemptAndSearch
    (pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
      htape)
    (Search.stageCompilerOfDecider
      hbool)

theorem DescriptionCompiler.ofTotalStageSubroutineAndSearch
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (Search.boundedCompilerOfSubroutineAndTotalSearch
      hattempt hdriver)

theorem DescriptionCompiler.ofCompiledSubroutineAndController
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (Search.boundedCompilerOfCompiledSubroutineAndController
      hattempt hdriver)

theorem pairedRecognizerDovetailDescriptionCompiler_of_controllerCompilerCloseout
    (hclose : PairedRecognizerDovetailControllerCompilerCloseout) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_controllerCompilerCloseout
      hclose)

theorem pairedRecognizerDovetailDescriptionCompiler_of_finiteControllerCompilerCloseout
    (hclose : PairedRecognizerDovetailFiniteControllerCompilerCloseout) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_finiteControllerCompilerCloseout
      hclose)

theorem finiteSourcePairedRecognizerDovetailCompilerConstruction_scaffold :
    FiniteSourcePairedRecognizerDovetailCompilerConstruction :=
  pairedRecognizerDovetailDescriptionCompiler_of_finiteControllerCompilerCloseout
    pairedRecognizerDovetailFiniteControllerCompilerCloseout_scaffold

theorem DescriptionCompiler.ofCompiledSubroutineAndDecider
    (hattempt :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction)
    (hbool : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  DescriptionCompiler.ofCompiledSubroutineAndController
    hattempt
    (Search.controllerCompilerOfDecider
      hbool)

theorem DescriptionCompiler.ofLayoutSubroutineAndSearch
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineSearchDriver
      hrunner hdriver)

theorem DescriptionCompiler.ofLayoutSubroutineAndRunner
    (hrunner :
      PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction)
    (hdriver :
      PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (pairedRecognizerBoundedDovetailTableCompiler_of_layoutCodeOutputSubroutineRealizer_and_subroutineRunnerSearchDriver
      hrunner hdriver)

theorem dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    DovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile (DovetailProgram accept reject)

theorem pairedRecognizerDovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler hcompile)

theorem programAcceptorCompilationPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    ProgramAcceptorCompilationPrinciple Bool := by
  intro L hL
  cases hL with
  | intro P hP =>
      cases hcompile P with
      | intro D hD =>
          exact programAcceptableByDescription_turingAcceptable
            (Exists.intro P (Exists.intro D (And.intro hP hD)))

theorem programBoolDeciderCompilationPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    ProgramBoolDeciderCompilationPrinciple Bool := by
  intro L hL
  cases hL with
  | intro P hP =>
      cases hcompile P with
      | intro D hD =>
          exact programBoolDecidableByDescription_turingDecidable
            (Exists.intro P (Exists.intro D (And.intro hP hD)))

theorem complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    {accept reject : Word Bool -> Nat -> Prop}
    (htraces : ComplementaryAcceptanceTraces accept reject L) :
    TuringDecidable L := by
  cases hcompile accept reject with
  | intro D hD =>
      exact programBoolDecidableByDescription_turingDecidable
        (Exists.intro (DovetailProgram accept reject)
          (Exists.intro D (And.intro (dovetailProgram_decides htraces) hD)))

theorem reCoRe_turingDecidable_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : RecursivelyEnumerableWithComplement L) :
    TuringDecidable L := by
  cases recursivelyEnumerable_with_complement_has_complementaryTraces h with
  | intro accept haccept =>
      cases haccept with
      | intro reject htraces =>
          exact complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
            hcompile htraces

theorem reCoReToDecidablePrinciple_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    ReCoReToDecidablePrinciple Bool := by
  intro L h
  exact reCoRe_turingDecidable_of_dovetailDescriptionCompiler hcompile h

end Computability
end FoC
