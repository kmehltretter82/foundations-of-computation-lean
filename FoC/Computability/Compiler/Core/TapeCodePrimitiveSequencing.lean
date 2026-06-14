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

theorem tapeCodePrimitiveHandoffSubroutineRealizedByDescription_compose
    {P Q : MachineDescription.TapeCodePrimitive}
    {A B : MachineDescription} {handoffMove : Direction}
    (hP : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      P A handoffMove)
    (hQ : TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      Q B handoffMove) :
    TapeCodePrimitiveHandoffSubroutineRealizedByDescription
      (MachineDescription.TapeCodePrimitive.compose P Q)
      (MachineDescription.seqSubroutine A B handoffMove)
      handoffMove := by
  have hAready : A.SubroutineReady :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_subroutineReady
      hP
  have hBready : B.SubroutineReady :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_subroutineReady
      hQ
  have hseqTape :
      forall {code out : Word MachineCodeSymbol},
        (MachineDescription.TapeCodePrimitive.compose P Q).transform code =
            some out ->
          exists Tout : Tape Bool,
            (MachineDescription.seqSubroutine A B handoffMove).HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) Tout ∧
            Tape.move handoffMove Tout =
              Tape.input (MachineDescription.encodeCodeWordAsInput out) ∧
            Tape.normalizedOutput Tout =
              MachineDescription.encodeCodeWordAsInput out := by
    intro code out hcompose
    unfold MachineDescription.TapeCodePrimitive.compose at hcompose
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
        rcases MachineDescription.runConfig_eq_halt_of_haltsWithTape
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
            (MachineDescription.seqSubroutine A B handoffMove).HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) Tout :=
          MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
            hAready hBready hAhalt hBReach
        have hQOutCanonical :
            B.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput mid)
              (MachineDescription.encodeCodeWordAsInput out) :=
          tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltsWithOutput_of_transform_eq_some
            hQ hQout
        have hQOutTape :
            B.HaltsWithOutput
              (MachineDescription.encodeCodeWordAsInput mid)
              (Tape.normalizedOutput Tout) :=
          MachineDescription.haltsWithOutput_of_haltsWithTape hBhalt
        have hToutNorm :
            Tape.normalizedOutput Tout =
              MachineDescription.encodeCodeWordAsInput out :=
          MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
            (tapeCodePrimitiveHandoffSubroutineRealizedByDescription_haltTransitionFree
              hQ)
            hQOutTape hQOutCanonical
        exact ⟨Tout, hSeqTape, hQmove, hToutNorm⟩
  constructor
  · constructor
    · constructor
      · exact MachineDescription.seqSubroutine_wellFormed hAready hBready
      · intro code out hcompose
        rcases hseqTape hcompose with
          ⟨Tout, hSeqTape, _hmove, hToutNorm⟩
        simpa [hToutNorm] using
          MachineDescription.haltsWithOutput_of_haltsWithTape hSeqTape
    · exact MachineDescription.seqSubroutine_haltTransitionFree
        hAready hBready
  · intro code out hcompose
    rcases hseqTape hcompose with
      ⟨Tout, hSeqTape, hmove, _hToutNorm⟩
    exact ⟨Tout, hSeqTape, hmove⟩

theorem tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_compose
    {P Q : MachineDescription.TapeCodePrimitive}
    {A B : MachineDescription} {handoffMove : Direction}
    (hP : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P A handoffMove)
    (hQ : TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      Q B handoffMove) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      (MachineDescription.TapeCodePrimitive.compose P Q)
      (MachineDescription.seqSubroutine A B handoffMove)
      handoffMove := by
  have hAready : A.SubroutineReady :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
      hP.left
  have hBready : B.SubroutineReady :=
    tapeCodePrimitiveOutputCompiledSubroutineByDescription_subroutineReady
      hQ.left
  have hrealized :
      TapeCodePrimitiveHandoffSubroutineRealizedByDescription
        (MachineDescription.TapeCodePrimitive.compose P Q)
        (MachineDescription.seqSubroutine A B handoffMove)
        handoffMove :=
    tapeCodePrimitiveHandoffSubroutineRealizedByDescription_compose
      (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
        hP)
      (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
        hQ)
  constructor
  · constructor
    · constructor
      · exact MachineDescription.seqSubroutine_wellFormed hAready hBready
      · intro code out
        constructor
        · intro hseqOut
          rcases hseqOut with ⟨n, hn⟩
          let seq :=
            MachineDescription.seqSubroutine A B handoffMove
          let Tout : Tape Bool :=
            (seq.runConfig n
              (seq.initial
                (MachineDescription.encodeCodeWordAsInput code))).tape
          have hSeqTape :
              seq.HaltsWithTape
                (MachineDescription.encodeCodeWordAsInput code) Tout := by
            refine ⟨n, ?_⟩
            exact ⟨hn.left, rfl⟩
          have hToutNorm :
              Tape.normalizedOutput Tout =
                MachineDescription.encodeCodeWordAsInput out :=
            hn.right
          rcases MachineDescription.seqSubroutine_haltsWithTape_inv
              hAready hBready hSeqTape with
            ⟨Tmid, hAhalt, hBReach⟩
          rcases hP.right code Tmid hAhalt with
            ⟨mid, hPmid, _hTmidNorm, hTmidMove⟩
          rcases hBReach with ⟨nB, hBRun⟩
          have hBRunInput :
              B.runConfig nB
                  (B.initial
                    (MachineDescription.encodeCodeWordAsInput mid)) =
                { state := B.halt, tape := Tout } := by
            change
              B.runConfig nB
                  { state := B.start,
                    tape := Tape.input
                      (MachineDescription.encodeCodeWordAsInput mid) } =
                { state := B.halt, tape := Tout }
            simpa [hTmidMove] using hBRun
          have hBhalt :
              B.HaltsWithTape
                (MachineDescription.encodeCodeWordAsInput mid) Tout := by
            refine ⟨nB, ?_⟩
            constructor
            · exact congrArg MachineDescription.Configuration.state
                  hBRunInput
            · exact
                (congrArg MachineDescription.Configuration.tape
                  hBRunInput).trans (show
                    Tout =
                      (seq.runConfig n
                        (seq.initial
                          (MachineDescription.encodeCodeWordAsInput code))).tape
                    from rfl)
          have hBout :
              B.HaltsWithOutput
                (MachineDescription.encodeCodeWordAsInput mid)
                (MachineDescription.encodeCodeWordAsInput out) := by
            simpa [hToutNorm] using
              MachineDescription.haltsWithOutput_of_haltsWithTape hBhalt
          have hQout : Q.transform mid = some out :=
            (hQ.left.left.right mid out).mp hBout
          exact
            MachineDescription.TapeCodePrimitive.compose_transform_some
              hPmid hQout
        · intro hcompose
          exact hrealized.left.left.right code out hcompose
    · exact MachineDescription.seqSubroutine_haltTransitionFree
        hAready hBready
  · intro code Tout hSeqTape
    rcases MachineDescription.seqSubroutine_haltsWithTape_inv
        hAready hBready hSeqTape with
      ⟨Tmid, hAhalt, hBReach⟩
    rcases hP.right code Tmid hAhalt with
      ⟨mid, hPmid, _hTmidNorm, hTmidMove⟩
    rcases hBReach with ⟨nB, hBRun⟩
    have hBRunInput :
        B.runConfig nB
            (B.initial
              (MachineDescription.encodeCodeWordAsInput mid)) =
          { state := B.halt, tape := Tout } := by
      change
        B.runConfig nB
            { state := B.start,
              tape := Tape.input
                (MachineDescription.encodeCodeWordAsInput mid) } =
          { state := B.halt, tape := Tout }
      simpa [hTmidMove] using hBRun
    have hBhalt :
        B.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput mid) Tout := by
      refine ⟨nB, ?_⟩
      constructor
      · exact congrArg MachineDescription.Configuration.state
          hBRunInput
      · change
          (B.runConfig nB
            (B.initial
              (MachineDescription.encodeCodeWordAsInput mid))).tape =
              Tout
        exact congrArg MachineDescription.Configuration.tape
          hBRunInput
    rcases hQ.right mid Tout hBhalt with
      ⟨out, hQout, hToutNorm, hToutMove⟩
    exact
      ⟨out,
        MachineDescription.TapeCodePrimitive.compose_transform_some
          hPmid hQout,
        hToutNorm,
        hToutMove⟩


end Computability
end FoC
