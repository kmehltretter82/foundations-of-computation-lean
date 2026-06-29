import FoC.Computability.Compiler.Core.ControllerResultContinue.GuardProjection.Rewind

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace ControllerResultContinueConstruction
def ResultNoneGuardStageInputProjectionDescription : MachineDescription :=
  seqSubroutine
    ResultNoneGuardScanRewindDescription
    ControllerStageInputProjection.Description
    Direction.left

theorem resultNoneGuardStageInputProjectionDescription_subroutineReady :
    ResultNoneGuardStageInputProjectionDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    resultNoneGuardScanRewindDescription_subroutineReady
    ⟨ControllerStageInputProjection.wellFormed,
      ControllerStageInputProjection.haltTransitionFree⟩

theorem resultNoneGuardStageInputProjectionDescription_haltsWithOutput_controllerEncode
    (C : DovetailControllerLayout)
    (hraw : PairedRecognizerDovetailControllerRawOutput C.result = none) :
    ResultNoneGuardStageInputProjectionDescription.HaltsWithOutput
      (encodeCodeWordAsInput
        (DovetailControllerLayout.encode C))
      (encodeCodeWordAsInput
        (DovetailControllerLayout.stageInputCode C)) := by
  let code := DovetailControllerLayout.encode C
  let inputBits := encodeCodeWordAsInput code
  let stageBits :=
    encodeCodeWordAsInput
      (DovetailControllerLayout.stageInputCode C)
  have haccept : (resultNoneGuardScanBoundary code).accepts :=
    (resultNoneGuardScanBoundary_controllerEncode_accepts_iff C).mpr hraw
  rcases
      resultNoneGuardScanRewindDescription_handoff_equiv_code_of_accepts
        code haccept with
    ⟨Tguard, hguard, hguardMove⟩
  have hprojReady : ControllerStageInputProjection.Description.SubroutineReady :=
    ⟨ControllerStageInputProjection.wellFormed,
      ControllerStageInputProjection.haltTransitionFree⟩
  have hprojOut :
      ControllerStageInputProjection.Description.HaltsWithOutput
        inputBits stageBits := by
    simpa [code, inputBits, stageBits] using
      ControllerStageInputProjection.haltsWithOutput_encode C
  rcases hprojOut with ⟨nProj, hnProj⟩
  let Tproj : Tape Bool :=
    (ControllerStageInputProjection.Description.runConfig nProj
      (ControllerStageInputProjection.Description.initial inputBits)).tape
  have hprojTape :
      ControllerStageInputProjection.Description.HaltsFromTape
        (Tape.input inputBits) Tproj := by
    refine ⟨nProj, ?_⟩
    change
      (ControllerStageInputProjection.Description.runConfig nProj
        { state := ControllerStageInputProjection.Description.start
          tape := Tape.input inputBits }).state =
          ControllerStageInputProjection.Description.halt ∧
        (ControllerStageInputProjection.Description.runConfig nProj
          { state := ControllerStageInputProjection.Description.start
            tape := Tape.input inputBits }).tape = Tproj
    constructor
    · simpa [Tproj, HaltsWithOutputIn] using hnProj.left
    · rfl
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm hguardMove) hprojTape with
    ⟨Tactual, hprojActual, hactualEquiv⟩
  have hprojReach :
      exists nB : Nat,
        ControllerStageInputProjection.Description.runConfig nB
            { state := ControllerStageInputProjection.Description.start
              tape := Tape.move Direction.left Tguard } =
          { state := ControllerStageInputProjection.Description.halt
            tape := Tactual } :=
    runConfig_eq_halt_of_haltsFromTape hprojActual
  have hseqTape :
      ResultNoneGuardStageInputProjectionDescription.HaltsWithTape
        inputBits Tactual := by
    simpa [ResultNoneGuardStageInputProjectionDescription, inputBits] using
      seqSubroutine_haltsWithTape_of_haltsWithTape
        resultNoneGuardScanRewindDescription_subroutineReady
        hprojReady hguard hprojReach
  have hTprojNorm : Tape.normalizedOutput Tproj = stageBits := by
    change
      Tape.normalizedOutput
          (ControllerStageInputProjection.Description.runConfig nProj
            (ControllerStageInputProjection.Description.initial inputBits)).tape =
        stageBits
    exact hnProj.right
  have hTactualNorm : Tape.normalizedOutput Tactual = stageBits :=
    (Tape.Equiv.normalizedOutput_eq hactualEquiv).trans hTprojNorm
  simpa [hTactualNorm, code, inputBits, stageBits] using
    haltsWithOutput_of_haltsWithTape hseqTape

theorem resultNoneGuardStageInputProjectionDescription_haltsWithOutput_of_transform
    {code out : Word MachineCodeSymbol}
    (htransform :
      GuardProjectionPrimitive.transform code = some out) :
    ResultNoneGuardStageInputProjectionDescription.HaltsWithOutput
      (encodeCodeWordAsInput code)
      (encodeCodeWordAsInput out) := by
  rcases
      (guardProjectionPrimitive_transform_eq_some_iff code out).mp
        htransform with
    ⟨C, rfl, hraw, rfl⟩
  exact
    resultNoneGuardStageInputProjectionDescription_haltsWithOutput_controllerEncode
      C hraw

theorem resultNoneGuardStageInputProjectionDescription_transform_of_haltsWithOutput
    {code out : Word MachineCodeSymbol}
    (hhalt :
      ResultNoneGuardStageInputProjectionDescription.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out)) :
    GuardProjectionPrimitive.transform code = some out := by
  rcases hhalt with ⟨n, hn⟩
  let inputBits := encodeCodeWordAsInput code
  let seq := ResultNoneGuardStageInputProjectionDescription
  let Tout : Tape Bool :=
    (seq.runConfig n (seq.initial inputBits)).tape
  have hseqTape :
      seq.HaltsWithTape inputBits Tout := by
    refine ⟨n, ?_⟩
    exact ⟨hn.left, rfl⟩
  have hToutNorm :
      Tape.normalizedOutput Tout =
        encodeCodeWordAsInput out :=
    hn.right
  have hguardReady : ResultNoneGuardScanRewindDescription.SubroutineReady :=
    resultNoneGuardScanRewindDescription_subroutineReady
  have hprojReady : ControllerStageInputProjection.Description.SubroutineReady :=
    ⟨ControllerStageInputProjection.wellFormed,
      ControllerStageInputProjection.haltTransitionFree⟩
  rcases
      seqSubroutine_haltsWithTape_inv
        hguardReady hprojReady hseqTape with
    ⟨Tguard, hguard, hprojReach⟩
  have hguardEquiv :
      Tape.Equiv
        (Tape.move Direction.left Tguard)
        (Tape.input inputBits) := by
    simpa [inputBits] using
      resultNoneGuardScanRewindDescription_handoff_equiv_of_haltsWithTape_code
        hguard
  rcases hprojReach with ⟨nProj, hprojRun⟩
  have hprojActual :
      ControllerStageInputProjection.Description.HaltsFromTape
        (Tape.move Direction.left Tguard) Tout := by
    refine ⟨nProj, ?_⟩
    change
      (ControllerStageInputProjection.Description.runConfig nProj
        { state := ControllerStageInputProjection.Description.start
          tape := Tape.move Direction.left Tguard }).state =
          ControllerStageInputProjection.Description.halt ∧
        (ControllerStageInputProjection.Description.runConfig nProj
          { state := ControllerStageInputProjection.Description.start
            tape := Tape.move Direction.left Tguard }).tape =
          Tout
    rw [hprojRun]
    exact ⟨rfl, rfl⟩
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        hguardEquiv hprojActual with
    ⟨Tclean, hprojClean, hcleanEquiv⟩
  have hprojCleanWith :
      ControllerStageInputProjection.Description.HaltsWithTape
        inputBits Tclean := by
    rcases hprojClean with ⟨nClean, hnClean⟩
    refine ⟨nClean, ?_⟩
    simpa [initial] using hnClean
  have hprojOut :
      ControllerStageInputProjection.Description.HaltsWithOutput
        inputBits (encodeCodeWordAsInput out) := by
    have hprojEquiv :
        ControllerStageInputProjection.Description.HaltsWithTapeEquiv
          inputBits Tout :=
      ⟨Tclean, hprojCleanWith, hcleanEquiv⟩
    have hnormOut :
        ControllerStageInputProjection.Description.HaltsWithOutput
          inputBits (Tape.normalizedOutput Tout) :=
      haltsWithOutput_of_haltsWithTapeEquiv
        hprojEquiv
    simpa [hToutNorm] using hnormOut
  have hstage :
      PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        code = some out := by
    exact
      (tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_iff
        ControllerStageInputProjection.outputCompiledSubroutine
        code out).mp
        (by simpa [inputBits] using hprojOut)
  rcases
      (pairedRecognizerDovetailControllerStageInputCode_transform_eq_some_iff
        code out).mp hstage with
    ⟨C, hcode, hout⟩
  have haccept :
      (resultNoneGuardScanBoundary code).accepts :=
    resultNoneGuardScanRewindDescription_accepts_of_haltsWithTape_code
      hguard
  have hraw :
      PairedRecognizerDovetailControllerRawOutput C.result = none := by
    rw [hcode] at haccept
    exact
      (resultNoneGuardScanBoundary_controllerEncode_accepts_iff C).mp
        haccept
  exact
    (guardProjectionPrimitive_transform_eq_some_iff code out).mpr
      ⟨C, hcode, hraw, hout⟩

theorem resultNoneGuardStageInputProjectionDescription_haltsWithOutput_iff
    (code out : Word MachineCodeSymbol) :
    ResultNoneGuardStageInputProjectionDescription.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
      GuardProjectionPrimitive.transform code = some out := by
  constructor
  · exact resultNoneGuardStageInputProjectionDescription_transform_of_haltsWithOutput
  · exact resultNoneGuardStageInputProjectionDescription_haltsWithOutput_of_transform

theorem resultNoneGuardStageInputProjectionDescription_outputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      GuardProjectionPrimitive
      ResultNoneGuardStageInputProjectionDescription :=
  ⟨⟨resultNoneGuardStageInputProjectionDescription_subroutineReady.left,
      resultNoneGuardStageInputProjectionDescription_haltsWithOutput_iff⟩,
    resultNoneGuardStageInputProjectionDescription_subroutineReady.right⟩


end ControllerResultContinueConstruction

end Computability
end FoC
