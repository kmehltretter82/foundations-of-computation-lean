import FoC.Computability.Compiler.FixedSimulatorSkeletons
import FoC.Computability.Compiler.Core.TapeCodePrimitiveSequencing
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.PhaseAdapters
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
open MachineDescription

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

theorem pairedRecognizerDovetailTotalStageAttemptOutputSubroutineSequencingConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptOutputSubroutineSequencingConstruction := by
  intro accept reject initializer runner emitter
    hinitializer hrunner hemitter
  let initRunner :=
    MachineDescription.seqSubroutine initializer runner
      tapeCodePrimitiveCodeWordHandoffMove
  let attempt :=
    EncodedRewriters.BoundedLayoutRunner.SeqViaCanonical initRunner emitter
  refine ⟨attempt, ?_⟩
  let firstCode :=
    MachineDescription.TapeCodePrimitive.compose
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      (PairedRecognizerDovetailLayoutCode accept reject)
  let totalCode :=
    MachineDescription.TapeCodePrimitive.compose firstCode
      PairedRecognizerDovetailTotalOutputCode
  have hinitReady : initializer.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hinitializer
  have hrunnerReady : runner.SubroutineReady :=
    hrunner.left
  have hinitRunnerReady : initRunner.SubroutineReady := by
    exact
      MachineDescription.seqSubroutine_subroutineReady
        hinitReady hrunnerReady
  have hemitterReady : emitter.SubroutineReady :=
    tapeCodePrimitiveOutputSubroutineRealizedByDescription_subroutineReady
      hemitter
  have hattemptReady : attempt.SubroutineReady := by
    exact
      EncodedRewriters.BoundedLayoutRunner.SeqViaCanonical_subroutineReady
        hinitRunnerReady hemitterReady
  have hinitHandoff :
      TapeCodePrimitiveHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer tapeCodePrimitiveCodeWordHandoffMove :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
      hinitializer
  have hinitRunnerForward :
      forall {code mid : Word MachineCodeSymbol},
        firstCode.transform code = some mid ->
          initRunner.HaltsFromTapeEquiv
            (Tape.input (MachineDescription.encodeCodeWordAsInput code))
            (Tape.input (MachineDescription.encodeCodeWordAsInput mid)) := by
    intro code mid hfirst
    unfold firstCode at hfirst
    unfold MachineDescription.TapeCodePrimitive.compose at hfirst
    cases hinit :
        (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
          code with
    | none =>
        simp [hinit] at hfirst
    | some initOut =>
        have hrun :
            (PairedRecognizerDovetailLayoutCode accept reject).transform
                initOut = some mid := by
          simpa [hinit] using hfirst
        rcases
            (pairedRecognizerDovetailLayoutCode_transform_eq_some_iff
              accept reject initOut mid).mp hrun with
          ⟨L, hinitOut, hmid⟩
        subst initOut
        subst mid
        rcases
            tapeCodePrimitiveHandoffCompiledSubroutineByDescription_haltsWithTape_of_transform_eq_some
              hinitHandoff hinit with
          ⟨Tinit, hInitTape, hInitMove⟩
        rcases hrunner.right.left L with
          ⟨Trunner, hRunnerTape, hRunnerEquiv⟩
        have hRunnerReach :
            exists nB : Nat,
              runner.runConfig nB
                  { state := runner.start,
                    tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove
                      Tinit } =
                { state := runner.halt, tape := Trunner } := by
          rcases runConfig_eq_halt_of_haltsWithTape hRunnerTape with
            ⟨nB, hBRun⟩
          refine ⟨nB, ?_⟩
          simpa [hInitMove] using hBRun
        have hSeqTape :
            initRunner.HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code)
              Trunner :=
          MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
            hinitReady hrunnerReady hInitTape hRunnerReach
        refine ⟨Trunner, ?_, ?_⟩
        · rcases hSeqTape with ⟨n, hn⟩
          exact
            ⟨n, by
              simpa [MachineDescription.HaltsWithTapeIn,
                MachineDescription.HaltsFromTapeIn,
                MachineDescription.initial] using hn⟩
        · simpa [EncodedRewriters.BoundedLayoutRunner.OutputTape,
            EncodedRewriters.BoundedLayoutRunner.OutputCode,
            Tape.output] using hRunnerEquiv
  have hinitRunnerClosed :
      forall {code : Word MachineCodeSymbol} {T : Tape Bool},
        initRunner.HaltsFromTape
            (Tape.input (MachineDescription.encodeCodeWordAsInput code)) T ->
          exists mid : Word MachineCodeSymbol,
            firstCode.transform code = some mid ∧
              Tape.Equiv T
                (Tape.input (MachineDescription.encodeCodeWordAsInput mid)) := by
    intro code T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsFromTape_inv
          hinitReady hrunnerReady hhalt with
      ⟨Tinit, hInitFrom, hRunnerReach⟩
    have hInitTape :
        initializer.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) Tinit := by
      rcases hInitFrom with ⟨nA, hnA⟩
      exact
        ⟨nA, by
          simpa [MachineDescription.HaltsWithTapeIn,
            MachineDescription.HaltsFromTapeIn,
            MachineDescription.initial] using hnA⟩
    rcases
        tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_haltsWithTape_output
          hinitializer hInitTape with
      ⟨initOut, hinitTransform, _hinitNorm, hinitMove⟩
    rcases hRunnerReach with ⟨nB, hBRun⟩
    have hRunnerTape :
        runner.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput initOut) T := by
      have hBRunInput :
          runner.runConfig nB
              (runner.initial
                (MachineDescription.encodeCodeWordAsInput initOut)) =
            { state := runner.halt, tape := T } := by
        change
          runner.runConfig nB
              { state := runner.start,
                tape := Tape.input
                  (MachineDescription.encodeCodeWordAsInput initOut) } =
            { state := runner.halt, tape := T }
        simpa [hinitMove] using hBRun
      exact
        ⟨nB,
          ⟨congrArg MachineDescription.Configuration.state hBRunInput,
            congrArg MachineDescription.Configuration.tape hBRunInput⟩⟩
    have hRunnerTapeEquiv :
        runner.HaltsWithTapeEquiv
          (MachineDescription.encodeCodeWordAsInput initOut) T :=
      ⟨T, hRunnerTape, Tape.Equiv.refl T⟩
    rcases hrunner.right.right initOut T hRunnerTapeEquiv with
      ⟨L, hinitOut, hTEquiv⟩
    let mid : Word MachineCodeSymbol :=
      MachineDescription.DovetailLayout.encode
        (MachineDescription.DovetailLayout.run
          accept reject L.stage L)
    have hrunnerTransform :
        (PairedRecognizerDovetailLayoutCode accept reject).transform
            initOut = some mid := by
      simpa [mid, hinitOut] using
        pairedRecognizerDovetailLayoutCode_encode accept reject L
    refine ⟨mid, ?_, ?_⟩
    · unfold firstCode
      exact
        MachineDescription.TapeCodePrimitive.compose_transform_some
          hinitTransform hrunnerTransform
    · simpa [mid, EncodedRewriters.BoundedLayoutRunner.OutputTape,
        EncodedRewriters.BoundedLayoutRunner.OutputCode,
        Tape.output] using hTEquiv
  have hcompiled :
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        totalCode attempt := by
    refine
      tapeCodePrimitiveOutputCompiledSubroutineByDescription_of_forward_closed
        hattemptReady ?_ ?_
    · intro code out htransform
      cases hfirst : firstCode.transform code with
      | none =>
          simp [totalCode, MachineDescription.TapeCodePrimitive.compose,
            hfirst] at htransform
      | some mid =>
          have hout :
              PairedRecognizerDovetailTotalOutputCode.transform mid =
                some out := by
            simpa [totalCode, MachineDescription.TapeCodePrimitive.compose,
              hfirst] using htransform
          have hA :=
            hinitRunnerForward (code := code) (mid := mid) hfirst
          have hBOut :
              emitter.HaltsWithOutput
                (MachineDescription.encodeCodeWordAsInput mid)
                (MachineDescription.encodeCodeWordAsInput out) :=
            hemitter.left.right mid out hout
          rcases hBOut with ⟨nB, hnB⟩
          let Tout : Tape Bool :=
            (emitter.runConfig nB
              (emitter.initial
                (MachineDescription.encodeCodeWordAsInput mid))).tape
          have hBTape :
              emitter.HaltsWithTape
                (MachineDescription.encodeCodeWordAsInput mid) Tout :=
            ⟨nB, ⟨hnB.left, rfl⟩⟩
          have hBFrom :
              emitter.HaltsFromTape
                (Tape.input
                  (MachineDescription.encodeCodeWordAsInput mid)) Tout := by
            rcases hBTape with ⟨n, hn⟩
            exact
              ⟨n, by
                simpa [MachineDescription.HaltsWithTapeIn,
                  MachineDescription.HaltsFromTapeIn,
                  MachineDescription.initial] using hn⟩
          have hBEq :
              emitter.HaltsFromTapeEquiv
                (Tape.input
                  (MachineDescription.encodeCodeWordAsInput mid)) Tout :=
            MachineDescription.HaltsFromTape.toEquiv hBFrom
          have hbridge :
              Tape.Equiv
                (Tape.move Direction.left
                  (Tape.move Direction.right
                    (Tape.input
                      (MachineDescription.encodeCodeWordAsInput mid))))
                (Tape.input
                  (MachineDescription.encodeCodeWordAsInput mid)) :=
            EncodedRewriters.BoundedLayoutRunner.moveLeft_moveRight_equiv_self
              (Tape.input (MachineDescription.encodeCodeWordAsInput mid))
          have hAttemptFrom :
              attempt.HaltsFromTapeEquiv
                (Tape.input
                  (MachineDescription.encodeCodeWordAsInput code)) Tout :=
            EncodedRewriters.BoundedLayoutRunner.SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
              hinitRunnerReady hemitterReady hA hbridge hBEq
          have hAttemptWith :
              attempt.HaltsWithTapeEquiv
                (MachineDescription.encodeCodeWordAsInput code) Tout := by
            rcases hAttemptFrom with ⟨Tactual, hActual, hEquiv⟩
            refine ⟨Tactual, ?_, hEquiv⟩
            rcases hActual with ⟨n, hn⟩
            exact
              ⟨n, by
                simpa [MachineDescription.HaltsWithTapeIn,
                  MachineDescription.HaltsFromTapeIn,
                  MachineDescription.initial] using hn⟩
          have hAttemptOut :=
            MachineDescription.haltsWithOutput_of_haltsWithTapeEquiv
              hAttemptWith
          have hToutNorm :
              Tape.normalizedOutput Tout =
                MachineDescription.encodeCodeWordAsInput out := by
            simpa [Tout] using hnB.right
          simpa [hToutNorm] using hAttemptOut
    · intro code out hhalt
      rcases hhalt with ⟨n, hn⟩
      let Tout : Tape Bool :=
        (attempt.runConfig n
          (attempt.initial
            (MachineDescription.encodeCodeWordAsInput code))).tape
      have hSeqFrom :
          attempt.HaltsFromTape
            (Tape.input (MachineDescription.encodeCodeWordAsInput code))
            Tout := by
        refine ⟨n, ?_⟩
        exact
          ⟨hn.left, by
            change
              (attempt.runConfig n
                (attempt.initial
                  (MachineDescription.encodeCodeWordAsInput code))).tape =
                Tout
            rfl⟩
      have hToutNorm :
          Tape.normalizedOutput Tout =
            MachineDescription.encodeCodeWordAsInput out :=
        hn.right
      rcases
          EncodedRewriters.BoundedLayoutRunner.SeqViaCanonical_haltsFromTape_inv
            hinitRunnerReady hemitterReady hSeqFrom with
        ⟨Tmid, hFirstFrom, hEmitterFrom⟩
      rcases hinitRunnerClosed hFirstFrom with
        ⟨mid, hFirstCode, hTmid⟩
      have hbridge :
          Tape.Equiv
            (Tape.move Direction.left (Tape.move Direction.right Tmid))
            (Tape.input (MachineDescription.encodeCodeWordAsInput mid)) :=
        Tape.Equiv.trans
          (EncodedRewriters.BoundedLayoutRunner.moveLeft_moveRight_equiv_self
            Tmid)
          hTmid
      have hEmitterEquiv :
          emitter.HaltsFromTapeEquiv
            (Tape.input (MachineDescription.encodeCodeWordAsInput mid))
            Tout :=
        MachineDescription.HaltsFromTapeEquiv_of_input_equiv
          hbridge hEmitterFrom
      have hEmitterWith :
          emitter.HaltsWithTapeEquiv
            (MachineDescription.encodeCodeWordAsInput mid) Tout := by
        rcases hEmitterEquiv with ⟨Tactual, hActual, hEquiv⟩
        refine ⟨Tactual, ?_, hEquiv⟩
        rcases hActual with ⟨nB, hnB⟩
        exact
          ⟨nB, by
            simpa [MachineDescription.HaltsWithTapeIn,
              MachineDescription.HaltsFromTapeIn,
              MachineDescription.initial] using hnB⟩
      have hEmitterOut :=
        MachineDescription.haltsWithOutput_of_haltsWithTapeEquiv
          hEmitterWith
      have hEmitterActual :
          emitter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput mid)
            (MachineDescription.encodeCodeWordAsInput out) := by
        simpa [hToutNorm] using hEmitterOut
      have hmidLayout :
          exists L : MachineDescription.DovetailLayout,
            mid = MachineDescription.DovetailLayout.encode L := by
        unfold firstCode at hFirstCode
        unfold MachineDescription.TapeCodePrimitive.compose at hFirstCode
        cases hinit :
            (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
              code with
        | none =>
            simp [hinit] at hFirstCode
        | some initOut =>
            have hrunnerMid :
                (PairedRecognizerDovetailLayoutCode accept reject).transform
                    initOut = some mid := by
              simpa [hinit] using hFirstCode
            rcases
                (pairedRecognizerDovetailLayoutCode_transform_eq_some_iff
                  accept reject initOut mid).mp hrunnerMid with
              ⟨L, _hinitOut, hmid⟩
            exact
              ⟨MachineDescription.DovetailLayout.run
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
      have hEmitterExpected :
          emitter.HaltsWithOutput
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailLayout.encode Lmid))
            (MachineDescription.encodeCodeWordAsInput expected) :=
        hemitter.left.right
          (MachineDescription.DovetailLayout.encode Lmid)
          expected hExpected
      have hout : out = expected :=
        haltsWithEncodedCodeOutput_functional_of_haltTransitionFree
          hemitter.right hEmitterActual hEmitterExpected
      exact
        MachineDescription.TapeCodePrimitive.compose_transform_some
          hFirstCode
          (by simpa [hout] using hExpected)
  simpa [PairedRecognizerDovetailTotalStageAttemptSourceCode,
    initRunner, attempt, firstCode, totalCode] using hcompiled

theorem pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_scaffold :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction :=
  pairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction_of_outputFiniteSourceComponents
    pairedRecognizerDovetailStageInputInitializerClosedHandoffCompiledSubroutineConstruction_scaffold
    pairedRecognizerDovetailBoundedLayoutRunnerSpecConstruction_scaffold
    pairedRecognizerDovetailTotalOutputEmitterOutputSubroutineRealizerConstruction_scaffold
    pairedRecognizerDovetailTotalStageAttemptOutputSubroutineSequencingConstruction_scaffold

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
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  fun accept reject =>
    hcompile
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
    DovetailDescriptionCompilerPrinciple :=
  fun accept reject => hcompile (DovetailProgram accept reject)

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
