import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions.Main

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedMergeCounterexample

def blankConfig : MachineDescription.Configuration :=
  { state := 0, tape := Tape.blank }

def layout : MachineDescription.DovetailLayout :=
  { input := []
    stage := 0
    acceptConfig := blankConfig
    rejectConfig := blankConfig
    acceptHit := false
    rejectHit := false }

def simulator : MachineDescription.SimulatorLayout :=
  { input := MachineDescription.encodeCodeWordAsInput
      (MachineDescription.DovetailLayout.encode layout)
    stage := 0
    config := blankConfig
    hit := false }

theorem simulator_input :
    MachineDescription.decodeCodeWordAsInput simulator.input =
      some (MachineDescription.DovetailLayout.encode layout) := by
  simp [simulator,
    MachineDescription.decodeCodeWordAsInput_encodeCodeWordAsInput]

def payload : SelectedMergeEmitterPayload :=
  { S := simulator
    L := layout
    input := simulator_input }

theorem output_contextLength_lt_input :
    Tape.contextLength (SelectedMergeOutputTape true simulator layout) <
      Tape.contextLength
        (Tape.input
          (MachineDescription.SimulatorLayout.asBoolInput simulator)) := by
  native_decide

theorem exactOutput_contextLength_lt_input :
    Tape.contextLength
        (CanonicalLayouts.ExactOutputTape
          (SelectedMergeEmitterOutputCode true) payload) <
      Tape.contextLength
        (Tape.input
          (MachineDescription.SimulatorLayout.asBoolInput simulator)) := by
  native_decide

theorem paddedOutput_contextLength_not_lt_input :
    ¬ Tape.contextLength
        (SelectedMergeEquivEmitterPaddedOutputTape true payload) <
      Tape.contextLength
        (Tape.input
          (MachineDescription.SimulatorLayout.asBoolInput simulator)) := by
  simpa [MachineDescription.SimulatorLayout.tape, payload] using
    Nat.not_lt_of_ge
      (SelectedMergeEquivEmitterPaddedOutputTape_contextLength_ge_input
        true payload)

theorem contextLength_eq_of_move_left_eq_input
    {w : Word Bool} {T : Tape Bool}
    (h : Tape.move Direction.left T = Tape.input w) :
    Tape.contextLength T = Tape.contextLength (Tape.input w) := by
  cases T with
  | mk left head right =>
      cases w with
      | nil =>
          cases left with
          | nil =>
              simp [Tape.move, Tape.moveLeft, Tape.input, Tape.blank] at h
          | cons first leftRest =>
              cases leftRest with
              | nil =>
                  simp [Tape.move, Tape.moveLeft, Tape.input, Tape.blank] at h
              | cons second more =>
                  simp [Tape.move, Tape.moveLeft, Tape.input, Tape.blank] at h
      | cons a rest =>
          cases left with
          | nil =>
              simp [Tape.move, Tape.moveLeft, Tape.input] at h
          | cons first leftRest =>
              cases leftRest with
              | nil =>
                  cases rest with
                  | nil =>
                      simp [Tape.move, Tape.moveLeft, Tape.input] at h
                  | cons b restTail =>
                      simp [Tape.move, Tape.moveLeft, Tape.input,
                        Tape.contextLength] at h ⊢
                      rw [h.right.right]
                      simp
                      omega
              | cons second more =>
                  simp [Tape.move, Tape.moveLeft, Tape.input] at h

theorem not_selectedMergeCanonicalExactEmitterConstruction :
    ¬ SelectedMergeCanonicalExactEmitterConstruction := by
  intro hconstruction
  rcases hconstruction true with ⟨emitter, hemits⟩
  have hhalt := hemits.right.left payload
  rcases hhalt with ⟨n, hn⟩
  have hmono :=
    MachineDescription.runConfig_contextLength_mono emitter n
      (emitter.initial (SelectedMergeEmitterInputBits payload))
  have hfinal :
      Tape.contextLength
          (emitter.runConfig n
            (emitter.initial
              (SelectedMergeEmitterInputBits payload))).tape =
        Tape.contextLength
          (CanonicalLayouts.ExactOutputTape
            (SelectedMergeEmitterOutputCode true) payload) := by
    exact congrArg Tape.contextLength hn.right
  rw [hfinal] at hmono
  have hinput :
      Tape.contextLength
          (emitter.initial
            (SelectedMergeEmitterInputBits payload)).tape =
        Tape.contextLength
          (Tape.input
            (MachineDescription.SimulatorLayout.asBoolInput simulator)) := by
    rfl
  rw [hinput] at hmono
  exact (Nat.not_lt_of_ge hmono) exactOutput_contextLength_lt_input

theorem not_selectedMergeEmitterConstruction :
    ¬ SelectedMergeEmitterConstruction := by
  intro hconstruction
  rcases hconstruction true with ⟨emitter, hemits⟩
  have hhalt := hemits.right.left simulator layout simulator_input
  rcases hhalt with ⟨n, hn⟩
  have hmono :=
    MachineDescription.runConfig_contextLength_mono emitter n
      (emitter.initial
        (MachineDescription.SimulatorLayout.asBoolInput simulator))
  have hfinal :
      Tape.contextLength
          (emitter.runConfig n
            (emitter.initial
              (MachineDescription.SimulatorLayout.asBoolInput simulator))).tape =
        Tape.contextLength (SelectedMergeOutputTape true simulator layout) := by
    exact congrArg Tape.contextLength hn.right
  rw [hfinal] at hmono
  have hinput :
      Tape.contextLength
          (emitter.initial
            (MachineDescription.SimulatorLayout.asBoolInput simulator)).tape =
        Tape.contextLength
          (Tape.input
            (MachineDescription.SimulatorLayout.asBoolInput simulator)) :=
    rfl
  rw [hinput] at hmono
  exact (Nat.not_lt_of_ge hmono) output_contextLength_lt_input

theorem not_selectedMergeCanonicalEmitterConstruction :
    ¬ SelectedMergeCanonicalEmitterConstruction := by
  intro hconstruction
  exact not_selectedMergeEmitterConstruction
    (by
      intro useAccept
      rcases hconstruction useAccept with ⟨emitter, hemits⟩
      exact
        ⟨emitter,
          (selectedMergeEmitterSpec_iff_canonical useAccept emitter).mpr
            hemits⟩)

theorem not_selectedMergePrimitiveRightShiftedConstruction :
    ¬ SelectedMergePrimitiveRightShiftedConstruction := by
  intro hconstruction
  rcases hconstruction true with ⟨runner, hrunner⟩
  have htransform :
      (SelectedMergePrimitive true).transform
          (MachineDescription.SimulatorLayout.encode simulator) =
        some (SelectedMergeOutputCode true simulator layout) :=
    (SelectedMergePrimitive_transform_eq_some_iff true
      (MachineDescription.SimulatorLayout.encode simulator)
      (SelectedMergeOutputCode true simulator layout)).mpr
      ⟨simulator, layout, rfl, simulator_input, rfl⟩
  have hhalt :=
    rightShiftedOutputCompiled_haltsWithTape_of_transform
      hrunner htransform
  rcases hhalt with ⟨n, hn⟩
  have hmono :=
    MachineDescription.runConfig_contextLength_mono runner n
      (runner.initial
        (MachineDescription.SimulatorLayout.asBoolInput simulator))
  have hfinal :
      Tape.contextLength
          (runner.runConfig n
            (runner.initial
              (MachineDescription.SimulatorLayout.asBoolInput simulator))).tape =
        Tape.contextLength (SelectedMergeOutputTape true simulator layout) := by
    exact congrArg Tape.contextLength hn.right
  rw [hfinal] at hmono
  have hinput :
      Tape.contextLength
          (runner.initial
            (MachineDescription.SimulatorLayout.asBoolInput simulator)).tape =
        Tape.contextLength
          (Tape.input
            (MachineDescription.SimulatorLayout.asBoolInput simulator)) :=
    rfl
  rw [hinput] at hmono
  exact (Nat.not_lt_of_ge hmono) output_contextLength_lt_input

theorem not_selectedMergePrimitiveClosedHandoffDescription
    (closed : MachineDescription) :
    ¬ TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedMergePrimitive true) closed
        tapeCodePrimitiveCodeWordHandoffMove := by
  intro hclosed
  have htransform :
      (SelectedMergePrimitive true).transform
          (MachineDescription.SimulatorLayout.encode simulator) =
        some (SelectedMergeOutputCode true simulator layout) :=
    (SelectedMergePrimitive_transform_eq_some_iff true
      (MachineDescription.SimulatorLayout.encode simulator)
      (SelectedMergeOutputCode true simulator layout)).mpr
      ⟨simulator, layout, rfl, simulator_input, rfl⟩
  have houtput :
      closed.HaltsWithOutput
        (MachineDescription.SimulatorLayout.asBoolInput simulator)
        (MachineDescription.encodeCodeWordAsInput
          (SelectedMergeOutputCode true simulator layout)) :=
    (hclosed.left.left.right
      (MachineDescription.SimulatorLayout.encode simulator)
      (SelectedMergeOutputCode true simulator layout)).mpr htransform
  rcases houtput with ⟨n, hn⟩
  let T : Tape Bool :=
    (closed.runConfig n
      (closed.initial
        (MachineDescription.SimulatorLayout.asBoolInput simulator))).tape
  have hhalt :
      closed.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput simulator) T := by
    exact ⟨n, hn.left, rfl⟩
  rcases hclosed.right
      (MachineDescription.SimulatorLayout.encode simulator) T hhalt with
    ⟨out, hout, _hnormalized, hhandoff⟩
  have hout_eq : out = SelectedMergeOutputCode true simulator layout := by
    rw [htransform] at hout
    cases hout
    rfl
  have hctxT :
      Tape.contextLength T =
        Tape.contextLength
          (CanonicalLayouts.ExactOutputTape
            (SelectedMergeEmitterOutputCode true) payload) := by
    have hctxOut :=
      contextLength_eq_of_move_left_eq_input hhandoff
    rw [hout_eq] at hctxOut
    simpa [CanonicalLayouts.ExactOutputTape,
      SelectedMergeEmitterOutputCode, payload,
      tapeCodePrimitiveCodeWordHandoffMove] using hctxOut
  have hmono :=
    MachineDescription.runConfig_contextLength_mono closed n
      (closed.initial
        (MachineDescription.SimulatorLayout.asBoolInput simulator))
  have hinput :
      Tape.contextLength
          (closed.initial
            (MachineDescription.SimulatorLayout.asBoolInput simulator)).tape =
        Tape.contextLength
          (Tape.input
            (MachineDescription.SimulatorLayout.asBoolInput simulator)) :=
    rfl
  rw [hinput] at hmono
  have hfinal :
      Tape.contextLength
          (closed.runConfig n
            (closed.initial
              (MachineDescription.SimulatorLayout.asBoolInput simulator))).tape =
        Tape.contextLength
          (CanonicalLayouts.ExactOutputTape
            (SelectedMergeEmitterOutputCode true) payload) := by
    simpa [T] using hctxT
  rw [hfinal] at hmono
  exact (Nat.not_lt_of_ge hmono) exactOutput_contextLength_lt_input

theorem not_selectedMergePrimitiveClosedHandoffConstruction :
    ¬ SelectedMergePrimitiveClosedHandoffConstruction := by
  intro hconstruction
  rcases hconstruction true with ⟨closed, hclosed⟩
  exact not_selectedMergePrimitiveClosedHandoffDescription closed hclosed

theorem not_acceptMergePrimitiveClosedHandoffConstruction :
    ¬ AcceptMergePrimitiveClosedHandoffConstruction := by
  intro hconstruction
  rcases hconstruction with ⟨closed, hclosed⟩
  exact
    not_selectedMergePrimitiveClosedHandoffDescription closed
      (by
        simpa [SelectedMergePrimitive, AcceptMergePrimitive,
          SelectedMergeSimulatorResult] using hclosed)

theorem not_configRunnerPrimitiveClosedHandoffConstruction :
    ¬ ConfigRunnerPrimitiveClosedHandoffConstruction := by
  intro hconstruction
  rcases hconstruction with
    ⟨_acceptProject, acceptMerge, _rejectProject, _rejectMerge,
      _hacceptProject, hacceptMerge, _hrejectProject, _hrejectMerge⟩
  exact not_acceptMergePrimitiveClosedHandoffConstruction
    ⟨acceptMerge, hacceptMerge⟩

theorem not_selectedMergeFiniteDescriptionConstruction :
    ¬ SelectedMergeFiniteDescriptionConstruction := by
  intro hconstruction
  exact not_selectedMergePrimitiveRightShiftedConstruction
    (selectedMergePrimitiveRightShiftedConstruction_of_finiteDescription
      hconstruction)

end SelectedMergeCounterexample

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
