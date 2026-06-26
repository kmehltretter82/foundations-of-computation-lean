import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Emitters
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Simulator

set_option doc.verso true

/-!
# Right-shifted fixed-description simulator code construction target

This module keeps the finite-machine leaf for compiling
{name}`FoC.Computability.FixedDescriptionBoundedSimulatorCode` with the other
fixed-description simulator construction targets.  Downstream config-runner
modules should consume this target as an input and remain adapter glue.

The bounded-layout config runner imports this file while assembling its
closed-handoff construction, so the construction here must remain independent
of that downstream assembly.
-/

namespace FoC
namespace Computability

open Languages

/-- The fixed-description simulator layout update computed by the code leaf. -/
def FixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout
    (D : MachineDescription)
    (L : MachineDescription.SimulatorLayout) :
    MachineDescription.SimulatorLayout :=
  { L with
    config := D.runConfig L.stage L.config
    hit :=
      L.hit ||
        MachineDescription.SimulatorLayout.hitsFromConfigByBool
          D L.config L.stage }

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout_eq_run
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout D L =
      MachineDescription.SimulatorLayout.run D L.stage L := by
  rfl

/-- Code word emitted by the right-shifted fixed-description simulator leaf. -/
def FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode
    (D : MachineDescription)
    (L : MachineDescription.SimulatorLayout) :
    Word MachineCodeSymbol :=
  MachineDescription.SimulatorLayout.encode
    (FixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout D L)

/-- Tape emitted by the right-shifted fixed-description simulator leaf. -/
def FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape
    (D : MachineDescription)
    (L : MachineDescription.SimulatorLayout) :
    Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (MachineDescription.encodeCodeWordAsInput
        (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L)))

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape_normalizedOutput
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape D L) =
      MachineDescription.encodeCodeWordAsInput
        (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L) := by
  simpa [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape] using
    EncodedRewriters.tape_normalizedOutput_move_right_input
      (MachineDescription.encodeCodeWordAsInput
        (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L))

/--
Forward half of the finite simulator-layout runner: on a complete canonical
layout it halts just to the right of the updated layout code.
-/
def FixedDescriptionBoundedSimulatorCodeRightShiftedForwardSpec
    (D runner : MachineDescription) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    runner.HaltsWithTape
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape D L)

/--
Closed half of the finite simulator-layout runner: every halting canonical
code-word input came from a complete simulator layout and emits the
corresponding updated layout.
-/
def FixedDescriptionBoundedSimulatorCodeRightShiftedClosedSpec
    (D runner : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    runner.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists L : MachineDescription.SimulatorLayout,
        MachineDescription.SimulatorLayout.decodeComplete code = some L ∧
          T = FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape D L

/--
Concrete finite-machine contract for the right-shifted fixed-description
simulator code leaf.  This names the complete simulator-layout parser, the
fixed-{lean}`D` bounded run, and the right-shifted emitter shape.
-/
def FixedDescriptionBoundedSimulatorCodeRightShiftedSpec
    (D runner : MachineDescription) : Prop :=
  runner.SubroutineReady ∧
    FixedDescriptionBoundedSimulatorCodeRightShiftedForwardSpec D runner ∧
      FixedDescriptionBoundedSimulatorCodeRightShiftedClosedSpec D runner

/-- Narrow finite construction target for the fixed-description simulator leaf. -/
def FixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction : Prop :=
  forall D : MachineDescription,
    exists runner : MachineDescription,
      FixedDescriptionBoundedSimulatorCodeRightShiftedSpec D runner

/-- Closed complete simulator-layout parser needed by the right-shifted code leaf. -/
abbrev FixedDescriptionBoundedSimulatorCodeRightShiftedParserConstruction :
    Prop :=
  EncodedRewriters.CanonicalLayouts.Simulator.ClosedRecognizerConstruction

/--
Emitter half of the right-shifted code leaf: after the complete simulator
layout has been parsed, emit the fixed-{lean}`D` bounded run/update-hit layout
one cell to the right of the canonical code word.
-/
def FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterSpec
    (D emitter : MachineDescription) : Prop :=
  EncodedRewriters.CanonicalLayouts.EmitterSpec
    MachineDescription.SimulatorLayout.asBoolInput
    (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D)
    emitter

/-- Finite construction target for the fixed description's right-shifted emitter. -/
def FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterConstruction :
    Prop :=
  forall D : MachineDescription,
    exists emitter : MachineDescription,
      FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterSpec D emitter

/--
Separated parser/emitter construction target for the concrete leaf.  This is
strictly narrower than {lean}`FixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction`:
it names the complete simulator-layout parser independently of the fixed
bounded-run emitter.
-/
def FixedDescriptionBoundedSimulatorCodeRightShiftedParserEmitterConstruction :
    Prop :=
  FixedDescriptionBoundedSimulatorCodeRightShiftedParserConstruction ∧
    FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterConstruction

def FixedDescriptionBoundedSimulatorCodeRightShiftedRunner
    (parser emitter : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine parser emitter Direction.left

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedParser_handoff
    (L : MachineDescription.SimulatorLayout) :
    Tape.move Direction.left
        (EncodedRewriters.CanonicalLayouts.Simulator.handoffTape L) =
      Tape.input (MachineDescription.SimulatorLayout.asBoolInput L) := by
  simpa [EncodedRewriters.CanonicalLayouts.Simulator.handoffTape,
    EncodedRewriters.CanonicalLayouts.Simulator.inputTape,
    EncodedRewriters.CanonicalLayouts.Simulator.encode,
    EncodedRewriters.CanonicalLayouts.HandoffTape,
    EncodedRewriters.CanonicalLayouts.InputTape,
    MachineDescription.SimulatorLayout.asBoolInput,
    tapeCodePrimitiveCodeWordHandoffMove] using
    EncodedRewriters.CanonicalLayouts.handoffTape_handoff
      EncodedRewriters.CanonicalLayouts.Simulator.encode_cons L

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedSpec_of_parser_emitter
    {D parser emitter : MachineDescription}
    (hparser :
      EncodedRewriters.CanonicalLayouts.Simulator.ClosedRecognizerSpec
        parser)
    (hemitter :
      FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterSpec
        D emitter) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedSpec D
      (FixedDescriptionBoundedSimulatorCodeRightShiftedRunner
        parser emitter) := by
  have hrunnerReady :
      (FixedDescriptionBoundedSimulatorCodeRightShiftedRunner
        parser emitter).SubroutineReady := by
    exact MachineDescription.seqSubroutine_subroutineReady
      hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro L
    have hparserRun :
        parser.HaltsWithTape
          (FixedDescriptionBoundedSimulatorInput L)
          (EncodedRewriters.CanonicalLayouts.Simulator.handoffTape L) := by
      simpa [FixedDescriptionBoundedSimulatorInput,
        EncodedRewriters.CanonicalLayouts.Simulator.bits,
        EncodedRewriters.CanonicalLayouts.Bits,
        EncodedRewriters.CanonicalLayouts.Simulator.encode] using
        hparser.right.left L
    have hemitterRun :
        emitter.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput L)
          (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape D L) := by
      simpa [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape,
        EncodedRewriters.CanonicalLayouts.OutputTape] using
        hemitter.right.left L
    rcases MachineDescription.runConfig_eq_halt_of_haltsWithTape
      hemitterRun with ⟨n, hn⟩
    exact
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left hparserRun
        ⟨n, by
          simpa [
            fixedDescriptionBoundedSimulatorCodeRightShiftedParser_handoff
              L] using hn⟩
  · intro code T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          hparser.left hemitter.left hhalt with
      ⟨Tmid, hparserRun, hemitterReach⟩
    rcases hparser.right.right code Tmid hparserRun with
      ⟨L, hdecode, hTmid⟩
    refine ⟨L, hdecode, ?_⟩
    rcases hemitterReach with ⟨n, hn⟩
    have hemitterRun :
        emitter.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput L) T := by
      refine ⟨n, ?_⟩
      constructor
      · simpa [MachineDescription.HaltsWithTapeIn,
          MachineDescription.initial, hTmid,
          fixedDescriptionBoundedSimulatorCodeRightShiftedParser_handoff
            L] using congrArg MachineDescription.Configuration.state hn
      · simpa [MachineDescription.HaltsWithTapeIn,
          MachineDescription.initial, hTmid,
          fixedDescriptionBoundedSimulatorCodeRightShiftedParser_handoff
            L] using congrArg MachineDescription.Configuration.tape hn
    exact
      hemitter.right.right L T hemitterRun

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction_of_parserEmitter
    (h :
      FixedDescriptionBoundedSimulatorCodeRightShiftedParserEmitterConstruction) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction := by
  intro D
  rcases h.left with ⟨parser, hparser⟩
  rcases h.right D with ⟨emitter, hemits⟩
  exact
    ⟨FixedDescriptionBoundedSimulatorCodeRightShiftedRunner parser emitter,
      fixedDescriptionBoundedSimulatorCodeRightShiftedSpec_of_parser_emitter
        hparser hemits⟩

theorem fixedDescriptionBoundedSimulatorCode_transform_eq_some_iff
    (D : MachineDescription)
    (code out : Word MachineCodeSymbol) :
    (FixedDescriptionBoundedSimulatorCode D).transform code = some out ↔
      exists L : MachineDescription.SimulatorLayout,
        MachineDescription.SimulatorLayout.decodeComplete code = some L ∧
          out =
            FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L := by
  constructor
  · intro h
    unfold FixedDescriptionBoundedSimulatorCode at h
    unfold MachineDescription.SimulatorLayout.runCodePrimitive at h
    unfold MachineDescription.SimulatorLayout.runCode at h
    cases hdecode :
        MachineDescription.SimulatorLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some L =>
        simp [hdecode] at h
        refine ⟨L, ?_, ?_⟩
        · rfl
        · simpa [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode,
            fixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout_eq_run]
            using h.symm
  · intro h
    rcases h with ⟨L, hdecode, hout⟩
    unfold FixedDescriptionBoundedSimulatorCode
    unfold MachineDescription.SimulatorLayout.runCodePrimitive
    unfold MachineDescription.SimulatorLayout.runCode
    simp [hdecode, hout,
      FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode,
      fixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout_eq_run]

theorem fixedDescriptionBoundedSimulatorCodeRightShifted_of_spec
    {D runner : MachineDescription}
    (hrunner :
      FixedDescriptionBoundedSimulatorCodeRightShiftedSpec D runner) :
    EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
      (FixedDescriptionBoundedSimulatorCode D) runner := by
  constructor
  · exact hrunner.left.left
  constructor
  · exact hrunner.left.right
  constructor
  · intro code out
    constructor
    · intro hhalt
      rcases hhalt with ⟨n, hn⟩
      let T : Tape Bool :=
        (runner.runConfig n
          (runner.initial
            (MachineDescription.encodeCodeWordAsInput code))).tape
      have hTape :
          runner.HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) T := by
        exact ⟨n, ⟨hn.left, rfl⟩⟩
      rcases hrunner.right.right code T hTape with
        ⟨L, hdecode, hT⟩
      have hactual :
          Tape.normalizedOutput T =
            MachineDescription.encodeCodeWordAsInput out := by
        simpa [T] using hn.right
      have hexpected :
          Tape.normalizedOutput T =
            MachineDescription.encodeCodeWordAsInput
              (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode
                D L) := by
        rw [hT]
        exact
          fixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape_normalizedOutput
            D L
      have houtBits :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput
              (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode
                D L) :=
        hactual.symm.trans hexpected
      have hout :
          out =
            FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L :=
        MachineDescription.encodeCodeWordAsInput_injective houtBits
      exact
        (fixedDescriptionBoundedSimulatorCode_transform_eq_some_iff
          D code out).mpr
          ⟨L, hdecode, hout⟩
    · intro htransform
      rcases
          (fixedDescriptionBoundedSimulatorCode_transform_eq_some_iff
            D code out).mp htransform with
        ⟨L, hdecode, hout⟩
      have hcode :
          code = MachineDescription.SimulatorLayout.encode L :=
        MachineDescription.SimulatorLayout.decodeComplete_eq_some_encode
          hdecode
      subst code
      subst out
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape,
        FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode,
        fixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout_eq_run,
        EncodedRewriters.tape_normalizedOutput_move_right_input,
        MachineDescription.SimulatorLayout.asBoolInput] using
        MachineDescription.haltsWithOutput_of_haltsWithTape
          (hrunner.right.left L)
  · intro code T hhalt
    rcases hrunner.right.right code T hhalt with
      ⟨L, hdecode, hT⟩
    refine
      ⟨FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L,
        ?_, ?_⟩
    · exact
        (fixedDescriptionBoundedSimulatorCode_transform_eq_some_iff
          D code
          (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode
            D L)).mpr
          ⟨L, hdecode, rfl⟩
    · simpa [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape]
        using hT

/--
Finite-machine leaf for the simulator-layout parser, fixed-description bounded
config runner, and right-shifted simulator-layout emitter.
-/
theorem fixedDescriptionBoundedSimulatorCodeRightShiftedParserEmitterConstruction_scaffold :
    FixedDescriptionBoundedSimulatorCodeRightShiftedParserEmitterConstruction := by
  sorry

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction_scaffold :
    FixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction := by
  exact
    fixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction_of_parserEmitter
      fixedDescriptionBoundedSimulatorCodeRightShiftedParserEmitterConstruction_scaffold

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_of_specConstruction
    (h :
      FixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction := by
  intro D
  rcases h D with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      fixedDescriptionBoundedSimulatorCodeRightShifted_of_spec hrunner⟩

/-- Finite-machine leaf for the right-shifted fixed-description simulator. -/
theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold :
    FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction := by
  exact
    fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_of_specConstruction
      fixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction_scaffold

end Computability
end FoC
