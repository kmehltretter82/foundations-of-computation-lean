import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.Assembly

set_option doc.verso true

/-!
# Compiled

Supporting declarations and helper lemmas for Computability Compiler Core DovetailInitialLayoutInitializer Compiled.
-/


namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

def DescriptionWithValidatorCopier
    (accept reject validator copier : MachineDescription) :
    MachineDescription :=
  MachineDescription.seqSubroutine
    validator
    (DescriptionWithCopier
      accept reject copier)
    Direction.left
     /-- {name}`descriptionWithValidatorCopier_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    descriptionWithValidatorCopier_subroutineReady
    {accept reject validator copier : MachineDescription}
    (hvalidator : StageInputValidatorSpec validator)
    (hcopier : AppendInputTapeReturnSpec copier) :
    (DescriptionWithValidatorCopier
      accept reject validator copier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hvalidator.left
    (descriptionWithCopier_subroutineReady
      hcopier)
     /-- {name}`descriptionWithValidatorCopier_run_bits` states the corresponding theorem run form. -/

theorem
    descriptionWithValidatorCopier_run_bits
    {accept reject validator copier : MachineDescription}
    (hvalidator : StageInputValidatorSpec validator)
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (DescriptionWithValidatorCopier
        accept reject validator copier).runConfig steps
          ((DescriptionWithValidatorCopier
            accept reject validator copier).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (DescriptionWithValidatorCopier
              accept reject validator copier).halt
          tape :=
            OutputTape
              accept reject w stage } := by
  let A := validator
  let B :=
    DescriptionWithCopier
      accept reject copier
  let Tmid :=
    stageInputCheckedValidatorTape w stage
  have hAready : A.SubroutineReady := hvalidator.left
  have hBready : B.SubroutineReady :=
    descriptionWithCopier_subroutineReady
      hcopier
  rcases hvalidator.right.left w stage with ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              Tape.input
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w stage)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, stageInputBits,
      MachineDescription.initial] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              OutputTape
                accept reject w stage } := by
    rcases
        descriptionWithCopier_run_bits_checked
          (accept := accept) (reject := reject) hcopier w stage with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    have hBout :
        B.runConfig nB
            { state := B.start
              tape := stageInputCheckedInputTape w stage } =
          { state := B.halt
            tape :=
              OutputTape
                accept reject w stage } := by
      exact hB.trans (by
        simp [B, outputTape_eq_bits])
    have hstart :
        MachineDescription.Configuration.mk
            B.start (Tape.move Direction.left Tmid) =
          MachineDescription.Configuration.mk
            B.start (stageInputCheckedInputTape w stage) := by
      simp [Tmid, stageInputCheckedValidatorTape,
        stageInputCheckedInputTape_move_left_move_right]
    rw [hstart]
    exact hBout
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [DescriptionWithValidatorCopier,
    A, B, MachineDescription.initial, stageInputBits] using hn
     /-- {name}`descriptionWithValidatorCopier_forward` captures the core lemma for this local construction. -/

theorem
    descriptionWithValidatorCopier_forward
    {accept reject validator copier : MachineDescription}
    (hvalidator : StageInputValidatorSpec validator)
    (hcopier : AppendInputTapeReturnSpec copier) :
    ForwardSpec
      accept reject
      (DescriptionWithValidatorCopier
        accept reject validator copier) := by
  intro w stage
  rcases
      descriptionWithValidatorCopier_run_bits
        (accept := accept) (reject := reject)
        hvalidator hcopier w stage with
    ⟨n, hn⟩
  exact ⟨n, by
    constructor
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.state hn
    · simpa [MachineDescription.HaltsWithTapeIn] using
        congrArg MachineDescription.Configuration.tape hn⟩
     /-- {name}`descriptionWithValidatorCopier_closed` captures the core lemma for this local construction. -/

theorem
    descriptionWithValidatorCopier_closed
    {accept reject validator copier : MachineDescription}
    (hvalidator : StageInputValidatorSpec validator)
    (hcopier : AppendInputTapeReturnSpec copier) :
    ClosedSpec
      accept reject
      (DescriptionWithValidatorCopier
        accept reject validator copier) := by
  intro code T hhalt
  let A := validator
  let B :=
    DescriptionWithCopier
      accept reject copier
  have hAready : A.SubroutineReady := hvalidator.left
  have hBready : B.SubroutineReady :=
    descriptionWithCopier_subroutineReady
      hcopier
  rcases
      MachineDescription.seqSubroutine_haltsWithTape_inv
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hhalt with
    ⟨Tmid, hAhalt, nB, hBrun⟩
  rcases hvalidator.right.right code Tmid hAhalt with
    ⟨w, stage, hcode, hhandoff⟩
  subst code
  have hBrun' :
      B.runConfig nB
          { state := B.start
            tape := stageInputCheckedInputTape w stage } =
        { state := B.halt, tape := T } := by
    simpa [hhandoff] using hBrun
  rcases
      descriptionWithCopier_run_bits_checked
        (accept := accept) (reject := reject)
        hcopier w stage with
    ⟨nExpected, hExpectedRaw⟩
  have hBexpected :
      B.runConfig nExpected
          { state := B.start
            tape := stageInputCheckedInputTape w stage } =
        { state := B.halt
          tape :=
            OutputTape
              accept reject w stage } := by
    exact hExpectedRaw.trans (by
      simp [B, outputTape_eq_bits])
  have hT :
      T =
        OutputTape accept reject w stage :=
    runConfig_halt_tape_functional_of_haltTransitionFree
      hBready.right hBrun' hBexpected
  exact ⟨w, stage, rfl, hT⟩

 /-- {name}`rightShiftedSpec_of_rightShiftedOutputCompiled` states the finite-machine specification. -/
theorem rightShiftedSpec_of_rightShiftedOutputCompiled
    {accept reject initializer : MachineDescription}
    (hinit :
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer) :
    RightShiftedSpec
      accept reject initializer := by
  constructor
  · exact ⟨hinit.left, hinit.right.left⟩
  constructor
  · intro w stage
    let code := PairedRecognizerDovetailStageInputCode w stage
    let out := OutputCode
      accept reject w stage
    have htransform :
        (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
            code = some out := by
      simpa [code, out, OutputCode] using
        pairedRecognizerDovetailInitialLayoutCode_encode
          accept reject w stage
    have houtput :
        initializer.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out) :=
      (hinit.right.right.left code out).mpr htransform
    rcases houtput with ⟨n, hn⟩
    let T :=
      (initializer.runConfig n
        (initializer.initial
          (MachineDescription.encodeCodeWordAsInput code))).tape
    have hTape :
        initializer.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T := by
      exact ⟨n, ⟨hn.left, rfl⟩⟩
    rcases hinit.right.right.right code T hTape with
      ⟨actualOut, hactual, hT⟩
    have hactualEq : actualOut = out := by
      rw [htransform] at hactual
      cases hactual
      rfl
    subst actualOut
    refine ⟨n, ?_⟩
    constructor
    · exact hn.left
    · change T =
        OutputTape accept reject w stage
      rw [hT]
      simp [out, OutputTape]
  · intro code T hhalt
    rcases hinit.right.right.right code T hhalt with
      ⟨out, htransform, hT⟩
    rcases
        (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
          accept reject code out).mp htransform with
      ⟨w, stage, hcode, hout⟩
    refine ⟨w, stage, hcode, ?_⟩
    rw [hT, hout]
    rfl

 /-- {name}`concreteMachineConstruction_of_rightShiftedOutputCompiled` captures the core lemma for this local construction. -/
theorem concreteMachineConstruction_of_rightShiftedOutputCompiled
    (hcompile :
      RightShiftedOutputCompiledConstruction) :
    ConcreteMachineConstruction := by
  intro accept reject
  rcases hcompile accept reject with ⟨initializer, hinit⟩
  exact
    ⟨initializer,
      rightShiftedSpec_of_rightShiftedOutputCompiled
        hinit⟩

 /-- {name}`rightShiftedSpec_haltsWithOutput_iff` states the finite-machine specification. -/
theorem rightShiftedSpec_haltsWithOutput_iff
    {accept reject initializer : MachineDescription}
    (hinit :
      RightShiftedSpec
        accept reject initializer)
    (code out : Word MachineCodeSymbol) :
    initializer.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
        code = some out := by
  constructor
  · intro hhalt
    rcases hhalt with ⟨n, hn⟩
    let T :=
      (initializer.runConfig n
        (initializer.initial
          (MachineDescription.encodeCodeWordAsInput code))).tape
    have hTape :
        initializer.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) T := by
      exact ⟨n, ⟨hn.left, rfl⟩⟩
    rcases hinit.right.right code T hTape with
      ⟨w, stage, hcode, hT⟩
    let expected :=
      MachineDescription.DovetailLayout.encode
        (MachineDescription.DovetailLayout.initial accept reject w stage)
    have hactual :
        Tape.normalizedOutput T =
          MachineDescription.encodeCodeWordAsInput out := by
      simpa [T] using hn.right
    have hexpected :
        Tape.normalizedOutput T =
          MachineDescription.encodeCodeWordAsInput expected := by
      rw [hT]
      exact
        tape_normalizedOutput_move_right_input
          (MachineDescription.encodeCodeWordAsInput expected)
    have houtBits :
        MachineDescription.encodeCodeWordAsInput out =
          MachineDescription.encodeCodeWordAsInput expected := by
      rw [← hactual]
      exact hexpected
    have hout : out = expected :=
      MachineDescription.encodeCodeWordAsInput_injective houtBits
    exact
      (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
        accept reject code out).mpr
        ⟨w, stage, hcode, hout⟩
  · intro htransform
    rcases
        (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
          accept reject code out).mp htransform with
      ⟨w, stage, hcode, hout⟩
    subst code
    subst out
    simpa [OutputTape,
      OutputCode,
      tape_normalizedOutput_move_right_input] using
      MachineDescription.haltsWithOutput_of_haltsWithTape
        (hinit.right.left w stage)

 /-- {name}`tapeCodePrimitiveRightShiftedOutputCompiled_of_dovetailInitialLayoutSpec` states the finite-machine specification. -/
theorem tapeCodePrimitiveRightShiftedOutputCompiled_of_dovetailInitialLayoutSpec
    {accept reject initializer : MachineDescription}
    (hinit :
      RightShiftedSpec
        accept reject initializer) :
    TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
      (PairedRecognizerDovetailInitialLayoutCode accept reject)
      initializer := by
  constructor
  · exact hinit.left.left
  · constructor
    · exact hinit.left.right
    · constructor
      · exact
          rightShiftedSpec_haltsWithOutput_iff
            hinit
      · intro code T hhalt
        rcases hinit.right.right code T hhalt with
          ⟨w, stage, hcode, hT⟩
        refine
          ⟨MachineDescription.DovetailLayout.encode
            (MachineDescription.DovetailLayout.initial
              accept reject w stage), ?_, hT⟩
        exact
          (pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_iff
            accept reject code
              (MachineDescription.DovetailLayout.encode
                (MachineDescription.DovetailLayout.initial
                  accept reject w stage))).mpr
            ⟨w, stage, hcode, rfl⟩

 /-- {name}`tapeCodePrimitiveClosedHandoffCompiled_of_rightShiftedOutputCompiled` captures the core lemma for this local construction. -/
theorem tapeCodePrimitiveClosedHandoffCompiled_of_rightShiftedOutputCompiled
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hD :
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        P D)
    (houtCons :
      forall {code out : Word MachineCodeSymbol},
        P.transform code = some out ->
          exists symbol : MachineCodeSymbol,
          exists tail : Word MachineCodeSymbol,
            out = symbol :: tail) :
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      P D tapeCodePrimitiveCodeWordHandoffMove :=
  tapeCodePrimitiveClosedHandoffCompiled_of_halt_tape_move_right
    hD.left hD.right.left hD.right.right.left houtCons
    hD.right.right.right

 /-- {name}`finiteDescription_realizer` captures the core lemma for this local construction. -/
theorem finiteDescription_realizer
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      RightShiftedSpec
        accept reject initializer := by
  rcases stageInputValidatorSpec_realizer with
    ⟨validator, hvalidator⟩
  rcases appendInputTapeReturnSpec_realizer with
    ⟨copier, hcopier⟩
  refine
    ⟨DescriptionWithValidatorCopier
      accept reject validator copier, ?_⟩
  constructor
  · exact
      descriptionWithValidatorCopier_subroutineReady
        hvalidator hcopier
  constructor
  · exact
      descriptionWithValidatorCopier_forward
        hvalidator hcopier
  · exact
      descriptionWithValidatorCopier_closed
        hvalidator hcopier

 /-- {name}`finiteDescriptionConstruction_scaffold` describes append/fold behavior used by later composition. -/
theorem finiteDescriptionConstruction_scaffold :
    FiniteDescriptionConstruction := by
  intro accept reject
  exact
    finiteDescription_realizer
      accept reject

 /-- {name}`rightShiftedOutputCompiledConstruction` captures the core lemma for this local construction. -/
theorem rightShiftedOutputCompiledConstruction :
    RightShiftedOutputCompiledConstruction := by
  intro accept reject
  rcases
      finiteDescriptionConstruction_scaffold
        accept reject with
    ⟨initializer, hinit⟩
  exact
    ⟨initializer,
      tapeCodePrimitiveRightShiftedOutputCompiled_of_dovetailInitialLayoutSpec
        hinit⟩

 /-- {name}`concreteMachineConstruction` captures the core lemma for this local construction. -/
theorem concreteMachineConstruction :
    ConcreteMachineConstruction :=
  concreteMachineConstruction_of_rightShiftedOutputCompiled
    rightShiftedOutputCompiledConstruction

 /-- {name}`machineConstruction` captures the core lemma for this local construction. -/
theorem machineConstruction :
    MachineConstruction := by
  intro accept reject
  exact
    concreteMachineConstruction
      accept reject

 /-- {name}`pairedRecognizerDovetailInitialLayoutCode_rightShiftedSpecConstruction` states the finite-machine specification. -/
theorem pairedRecognizerDovetailInitialLayoutCode_rightShiftedSpecConstruction :
    PairedRecognizerDovetailInitialLayoutCodeRightShiftedSpecConstruction := by
  intro accept reject
  exact
    finiteDescriptionConstruction_scaffold
      accept reject

 /-- {name}`pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine` captures the core lemma for this local construction. -/
theorem pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      TapeCodePrimitiveRightShiftedOutputCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer :=
  rightShiftedOutputCompiledConstruction
    accept reject

 /-- {name}`pairedRecognizerDovetailInitialLayoutCode_closedHandoffCompiledSubroutine` captures the core lemma for this local construction. -/
theorem pairedRecognizerDovetailInitialLayoutCode_closedHandoffCompiledSubroutine
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer tapeCodePrimitiveCodeWordHandoffMove := by
  rcases
      pairedRecognizerDovetailInitialLayoutCode_rightShiftedOutputCompiledSubroutine
        accept reject with
    ⟨initializer, hinitializer⟩
  refine ⟨initializer, ?_⟩
  have houtCons :
      forall {code out : Word MachineCodeSymbol},
        (PairedRecognizerDovetailInitialLayoutCode accept reject).transform
            code = some out ->
          exists symbol : MachineCodeSymbol,
          exists tail : Word MachineCodeSymbol,
            out = symbol :: tail := by
    intro code out hp
    rcases
        pairedRecognizerDovetailInitialLayoutCode_transform_eq_some_cons hp with
      ⟨tail, hout⟩
    exact ⟨MachineCodeSymbol.transition, tail, hout⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiled_of_rightShiftedOutputCompiled
      hinitializer houtCons

end DovetailInitialLayoutInitializer

end Computability
end FoC
