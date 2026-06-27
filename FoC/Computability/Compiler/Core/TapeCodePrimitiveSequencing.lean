import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.TapeCodePrimitives

set_option doc.verso true

/-!
# Sequencing for tape-code primitive subroutines

Composition lemmas for compiled tape-code primitives, separated from the
high-level skeleton closeouts so Core constructions can reuse them directly.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_compose
    {P Q : TapeCodePrimitive}
    {A B : MachineDescription} {handoffMove : Direction}
    (hP : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P A handoffMove)
    (hQ : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      Q B handoffMove) :
    TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      (TapeCodePrimitive.compose P Q)
      (seqSubroutine A B handoffMove)
      handoffMove := by
  have hAready : A.SubroutineReady :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_subroutineReady
      hP
  have hBready : B.SubroutineReady :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_subroutineReady
      hQ
  have hseqTape :
      forall {code out : Word MachineCodeSymbol},
        (TapeCodePrimitive.compose P Q).transform code =
            some out ->
          exists Tout : Tape Bool,
            (seqSubroutine A B handoffMove).HaltsWithTape
              (encodeCodeWordAsInput code) Tout ∧
            Tape.move handoffMove Tout =
              Tape.input (encodeCodeWordAsInput out) ∧
            Tape.normalizedOutput Tout =
              encodeCodeWordAsInput out := by
    intro code out hcompose
    unfold TapeCodePrimitive.compose at hcompose
    cases hPcode : P.transform code with
    | none =>
        simp [hPcode] at hcompose
    | some mid =>
        have hQout : Q.transform mid = some out := by
          simpa [hPcode] using hcompose
        rcases
            tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltsWithTape_of_transform_eq_some
              hP hPcode with
          ⟨Tmid, hAhalt, hPmove⟩
        rcases
            tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltsWithTape_of_transform_eq_some
              hQ hQout with
          ⟨Tout, hBhalt, hQmove⟩
        rcases runConfig_eq_halt_of_haltsWithTape
            hBhalt with
          ⟨nB, hBRunInput⟩
        have hBReach :
            exists nB : Nat,
              B.runConfig nB
                  { state := B.start,
                    tape := Tape.move handoffMove Tmid } =
                { state := B.halt, tape := Tout } := by
          exact ⟨nB, by simpa [hPmove] using hBRunInput⟩
        have hSeqTape :
            (seqSubroutine A B handoffMove).HaltsWithTape
              (encodeCodeWordAsInput code) Tout :=
          seqSubroutine_haltsWithTape_of_haltsWithTape
            hAready hBready hAhalt hBReach
        have hQOutCanonical :
            B.HaltsWithOutput
              (encodeCodeWordAsInput mid)
              (encodeCodeWordAsInput out) :=
          tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltsWithOutput_of_transform_eq_some
            hQ hQout
        have hQOutTape :
            B.HaltsWithOutput
              (encodeCodeWordAsInput mid)
              (Tape.normalizedOutput Tout) :=
          haltsWithOutput_of_haltsWithTape hBhalt
        have hToutNorm :
            Tape.normalizedOutput Tout =
              encodeCodeWordAsInput out :=
          haltsWithOutput_functional_of_haltTransitionFree
            (tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltTransitionFree
              hQ)
            hQOutTape hQOutCanonical
        exact ⟨Tout, hSeqTape, hQmove, hToutNorm⟩
  constructor
  · constructor
    · constructor
      · exact seqSubroutine_wellFormed hAready hBready
      · intro code out hcompose
        rcases hseqTape hcompose with
          ⟨Tout, hSeqTape, _hmove, hToutNorm⟩
        simpa [hToutNorm] using
          haltsWithOutput_of_haltsWithTape hSeqTape
    · exact seqSubroutine_haltTransitionFree
        hAready hBready
  · intro code out hcompose
    rcases hseqTape hcompose with
      ⟨Tout, hSeqTape, hmove, _hToutNorm⟩
    exact ⟨Tout, hSeqTape, hmove⟩

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_compose_output
    {P Q : TapeCodePrimitive}
    {A B : MachineDescription} {handoffMove : Direction}
    (hP : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P A handoffMove)
    (hQ : TapeCodePrimitiveOutputSubroutineRealizedByDescription Q B) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      (TapeCodePrimitive.compose P Q)
      (seqSubroutine A B handoffMove) := by
  have hAready : A.SubroutineReady :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_subroutineReady
      hP
  have hBready : B.SubroutineReady :=
    tapeCodePrimitiveOutputSubroutineRealizedByDescription_subroutineReady
      hQ
  constructor
  · constructor
    · exact seqSubroutine_wellFormed hAready hBready
    · intro code out hcompose
      unfold TapeCodePrimitive.compose at hcompose
      cases hPcode : P.transform code with
      | none =>
          simp [hPcode] at hcompose
      | some mid =>
          have hQout : Q.transform mid = some out := by
            simpa [hPcode] using hcompose
          rcases
              tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltsWithTape_of_transform_eq_some
                hP hPcode with
            ⟨Tmid, hAhalt, hPmove⟩
          have hBOut :
              B.HaltsWithOutput
                (encodeCodeWordAsInput mid)
                (encodeCodeWordAsInput out) :=
            hQ.left.right mid out hQout
          rcases hBOut with ⟨nB, hBOutIn⟩
          let Tout : Tape Bool :=
            (B.runConfig nB
              (B.initial
                (encodeCodeWordAsInput mid))).tape
          have hBRunInput :
              B.runConfig nB
                  (B.initial
                    (encodeCodeWordAsInput mid)) =
                { state := B.halt, tape := Tout } := by
            cases hfinal :
                B.runConfig nB
                  (B.initial
                    (encodeCodeWordAsInput mid)) with
            | mk state tape =>
                have hstate : state = B.halt := by
                  simpa [HaltsWithOutputIn,
                    hfinal] using hBOutIn.left
                simp [Tout, hfinal, hstate]
          have hBReach :
              exists nB : Nat,
                B.runConfig nB
                    { state := B.start,
                      tape := Tape.move handoffMove Tmid } =
                  { state := B.halt, tape := Tout } := by
            refine ⟨nB, ?_⟩
            change
              B.runConfig nB
                  { state := B.start,
                    tape := Tape.move handoffMove Tmid } =
                { state := B.halt, tape := Tout }
            simpa [hPmove] using hBRunInput
          have hSeqTape :
              (seqSubroutine A B handoffMove).HaltsWithTape
                (encodeCodeWordAsInput code) Tout :=
            seqSubroutine_haltsWithTape_of_haltsWithTape
              hAready hBready hAhalt hBReach
          have hToutNorm :
              Tape.normalizedOutput Tout =
                encodeCodeWordAsInput out := by
            change
              Tape.normalizedOutput
                  (B.runConfig nB
                    (B.initial
                      (encodeCodeWordAsInput mid))).tape =
                encodeCodeWordAsInput out
            simpa [Tout] using hBOutIn.right
          simpa [hToutNorm] using
            haltsWithOutput_of_haltsWithTape hSeqTape
  · exact seqSubroutine_haltTransitionFree hAready hBready

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_compose_outputCompiled
    {P Q : TapeCodePrimitive}
    {A B : MachineDescription} {handoffMove : Direction}
    (hP : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P A handoffMove)
    (hQ : TapeCodePrimitiveOutputCompiledSubroutineByDescription Q B) :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      (TapeCodePrimitive.compose P Q)
      (seqSubroutine A B handoffMove) := by
  have hAready : A.SubroutineReady :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
      hP.left
  have hBready : B.SubroutineReady :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
      hQ
  constructor
  · constructor
    · exact seqSubroutine_wellFormed hAready hBready
    · intro code out
      constructor
      · intro hseqOut
        rcases hseqOut with ⟨n, hn⟩
        let seq :=
          seqSubroutine A B handoffMove
        let Tout : Tape Bool :=
          (seq.runConfig n
            (seq.initial
              (encodeCodeWordAsInput code))).tape
        have hSeqTape :
            seq.HaltsWithTape
              (encodeCodeWordAsInput code) Tout := by
          refine ⟨n, ?_⟩
          exact ⟨hn.left, rfl⟩
        have hToutNorm :
            Tape.normalizedOutput Tout =
              encodeCodeWordAsInput out :=
          hn.right
        rcases seqSubroutine_haltsWithTape_inv
            hAready hBready hSeqTape with
          ⟨Tmid, hAhalt, hBReach⟩
        rcases hP.right code Tmid hAhalt with
          ⟨mid, hPmid, _hTmidNorm, hTmidMove⟩
        rcases hBReach with ⟨nB, hBRun⟩
        have hBRunInput :
            B.runConfig nB
                (B.initial
                  (encodeCodeWordAsInput mid)) =
              { state := B.halt, tape := Tout } := by
          change
            B.runConfig nB
                { state := B.start,
                  tape := Tape.input
                    (encodeCodeWordAsInput mid) } =
              { state := B.halt, tape := Tout }
          simpa [hTmidMove] using hBRun
        have hBhalt :
            B.HaltsWithOutput
              (encodeCodeWordAsInput mid)
              (encodeCodeWordAsInput out) := by
          refine ⟨nB, ?_⟩
          constructor
          · exact congrArg Configuration.state
              hBRunInput
          · change
              Tape.normalizedOutput
                  (B.runConfig nB
                    (B.initial
                      (encodeCodeWordAsInput mid))).tape =
                encodeCodeWordAsInput out
            rw [hBRunInput]
            exact hToutNorm
        have hQout : Q.transform mid = some out :=
          (hQ.left.right mid out).mp hBhalt
        exact
          TapeCodePrimitive.compose_transform_some
            hPmid hQout
      · intro hcompose
        unfold TapeCodePrimitive.compose at hcompose
        cases hPcode : P.transform code with
        | none =>
            simp [hPcode] at hcompose
        | some mid =>
            have hQout : Q.transform mid = some out := by
              simpa [hPcode] using hcompose
            rcases
                tapeCodePrimitiveHandoffCompiledSubroutineByDescription_haltsWithTape_of_transform_eq_some
                  (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffCompiled
                    hP)
                  hPcode with
              ⟨Tmid, hAhalt, hTmidMove⟩
            rcases
                (hQ.left.right mid out).mpr hQout with
              ⟨nB, hBOut⟩
            let Tout : Tape Bool :=
              (B.runConfig nB
                (B.initial
                  (encodeCodeWordAsInput mid))).tape
            have hBReach :
                exists nB : Nat,
                  B.runConfig nB
                      { state := B.start,
                        tape := Tape.move handoffMove Tmid } =
                    { state := B.halt, tape := Tout } := by
              refine ⟨nB, ?_⟩
              change
                B.runConfig nB
                    { state := B.start,
                      tape := Tape.move handoffMove Tmid } =
                  { state := B.halt, tape := Tout }
              have hBRun :
                  B.runConfig nB
                      (B.initial
                        (encodeCodeWordAsInput mid)) =
                    { state := B.halt, tape := Tout } := by
                cases hfinal :
                    B.runConfig nB
                      (B.initial
                        (encodeCodeWordAsInput mid)) with
                | mk state tape =>
                    have hstate : state = B.halt := by
                      simpa [HaltsWithOutputIn,
                        hfinal] using hBOut.left
                    simp [Tout, hfinal, hstate]
              simpa [hTmidMove] using hBRun
            have hseqTape :
                (seqSubroutine A B handoffMove).HaltsWithTape
                  (encodeCodeWordAsInput code) Tout :=
              seqSubroutine_haltsWithTape_of_haltsWithTape
                hAready hBready hAhalt hBReach
            have hToutNorm :
                Tape.normalizedOutput Tout =
                  encodeCodeWordAsInput out := by
              simpa [Tout] using hBOut.right
            simpa [hToutNorm] using
              haltsWithOutput_of_haltsWithTape hseqTape
  · exact seqSubroutine_haltTransitionFree hAready hBready

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_compose
    {P Q : TapeCodePrimitive}
    {A B : MachineDescription} {handoffMove : Direction}
    (hP : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P A handoffMove)
    (hQ : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      Q B handoffMove) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      (TapeCodePrimitive.compose P Q)
      (seqSubroutine A B handoffMove)
      handoffMove := by
  have hAready : A.SubroutineReady :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
      hP.left
  have hBready : B.SubroutineReady :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
      hQ.left
  have hrealized :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (TapeCodePrimitive.compose P Q)
        (seqSubroutine A B handoffMove)
        handoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_compose
      (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
        hP)
      (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
        hQ)
  constructor
  · constructor
    · constructor
      · exact seqSubroutine_wellFormed hAready hBready
      · intro code out
        constructor
        · intro hseqOut
          rcases hseqOut with ⟨n, hn⟩
          let seq :=
            seqSubroutine A B handoffMove
          let Tout : Tape Bool :=
            (seq.runConfig n
              (seq.initial
                (encodeCodeWordAsInput code))).tape
          have hSeqTape :
              seq.HaltsWithTape
                (encodeCodeWordAsInput code) Tout := by
            refine ⟨n, ?_⟩
            exact ⟨hn.left, rfl⟩
          have hToutNorm :
              Tape.normalizedOutput Tout =
                encodeCodeWordAsInput out :=
            hn.right
          rcases seqSubroutine_haltsWithTape_inv
              hAready hBready hSeqTape with
            ⟨Tmid, hAhalt, hBReach⟩
          rcases hP.right code Tmid hAhalt with
            ⟨mid, hPmid, _hTmidNorm, hTmidMove⟩
          rcases hBReach with ⟨nB, hBRun⟩
          have hBRunInput :
              B.runConfig nB
                  (B.initial
                    (encodeCodeWordAsInput mid)) =
                { state := B.halt, tape := Tout } := by
            change
              B.runConfig nB
                  { state := B.start,
                    tape := Tape.input
                      (encodeCodeWordAsInput mid) } =
                { state := B.halt, tape := Tout }
            simpa [hTmidMove] using hBRun
          have hBhalt :
              B.HaltsWithTape
                (encodeCodeWordAsInput mid) Tout := by
            refine ⟨nB, ?_⟩
            constructor
            · exact congrArg Configuration.state
                  hBRunInput
            · exact
                (congrArg Configuration.tape
                  hBRunInput).trans (show
                    Tout =
                      (seq.runConfig n
                        (seq.initial
                          (encodeCodeWordAsInput code))).tape
                    from rfl)
          have hBout :
              B.HaltsWithOutput
                (encodeCodeWordAsInput mid)
                (encodeCodeWordAsInput out) := by
            simpa [hToutNorm] using
              haltsWithOutput_of_haltsWithTape hBhalt
          have hQout : Q.transform mid = some out :=
            (hQ.left.left.right mid out).mp hBout
          exact
            TapeCodePrimitive.compose_transform_some
              hPmid hQout
        · intro hcompose
          exact hrealized.left.left.right code out hcompose
    · exact seqSubroutine_haltTransitionFree
        hAready hBready
  · intro code Tout hSeqTape
    rcases seqSubroutine_haltsWithTape_inv
        hAready hBready hSeqTape with
      ⟨Tmid, hAhalt, hBReach⟩
    rcases hP.right code Tmid hAhalt with
      ⟨mid, hPmid, _hTmidNorm, hTmidMove⟩
    rcases hBReach with ⟨nB, hBRun⟩
    have hBRunInput :
        B.runConfig nB
            (B.initial
              (encodeCodeWordAsInput mid)) =
          { state := B.halt, tape := Tout } := by
      change
        B.runConfig nB
            { state := B.start,
              tape := Tape.input
                (encodeCodeWordAsInput mid) } =
          { state := B.halt, tape := Tout }
      simpa [hTmidMove] using hBRun
    have hBhalt :
        B.HaltsWithTape
          (encodeCodeWordAsInput mid) Tout := by
      refine ⟨nB, ?_⟩
      constructor
      · exact congrArg Configuration.state
          hBRunInput
      · change
          (B.runConfig nB
            (B.initial
              (encodeCodeWordAsInput mid))).tape =
              Tout
        exact congrArg Configuration.tape
          hBRunInput
    rcases hQ.right mid Tout hBhalt with
      ⟨out, hQout, hToutNorm, hToutMove⟩
    exact
      ⟨out,
        TapeCodePrimitive.compose_transform_some
          hPmid hQout,
        hToutNorm,
        hToutMove⟩


end Computability
end FoC
