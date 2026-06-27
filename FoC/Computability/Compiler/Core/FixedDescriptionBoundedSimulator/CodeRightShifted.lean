import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.CommonGround
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator.Skeleton

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
    CommonGround.CodeWordEmitters.tape_normalizedOutput_move_right_input
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
  CommonGround.SimulatorLayouts.ClosedRecognizerConstruction

/--
Concrete parser leaf in the standard right-shifted code-word form: normalize a
complete simulator-layout code word and reject malformed code words.
-/
def FixedDescriptionBoundedSimulatorCodeRightShiftedParserPrimitiveConstruction :
    Prop :=
  exists parser : MachineDescription,
    EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
      MachineDescription.SimulatorLayout.normalizeCodePrimitive parser

theorem fixedDescriptionBoundedSimulatorCodeRightShifted_haltsWithTape_of_transform
    {P : MachineDescription.TapeCodePrimitive}
    {D : MachineDescription}
    (hD :
      EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
        P D)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out) :
    D.HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput code)
      (Tape.move Direction.right
        (Tape.input
          (MachineDescription.encodeCodeWordAsInput out))) := by
  have houtput :
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) :=
    (hD.right.right.left code out).mpr htransform
  rcases houtput with ⟨n, hn⟩
  let T : Tape Bool :=
    (D.runConfig n
      (D.initial
        (MachineDescription.encodeCodeWordAsInput code))).tape
  have hhalt :
      D.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T := by
    exact ⟨n, ⟨hn.left, rfl⟩⟩
  rcases hD.right.right.right code T hhalt with
    ⟨actual, hactual, hT⟩
  have hactualOut : actual = out := by
    rw [htransform] at hactual
    cases hactual
    rfl
  rw [hT] at hhalt
  simpa [hactualOut] using hhalt

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedParserConstruction_of_primitive
    (h :
      FixedDescriptionBoundedSimulatorCodeRightShiftedParserPrimitiveConstruction) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedParserConstruction := by
  rcases h with ⟨parser, hparser⟩
  refine ⟨parser, ?_⟩
  constructor
  · exact ⟨hparser.left, hparser.right.left⟩
  constructor
  · intro L
    have htransform :
        MachineDescription.SimulatorLayout.normalizeCodePrimitive.transform
            (MachineDescription.SimulatorLayout.encode L) =
          some (MachineDescription.SimulatorLayout.encode L) :=
      CommonGround.SimulatorLayouts.normalizeCodePrimitive_encode L
    simpa [CommonGround.SimulatorLayouts.bits,
      CommonGround.SimulatorLayouts.handoffTape,
      CommonGround.SimulatorLayouts.encode,
      CommonGround.LayoutTapes.Bits,
      CommonGround.LayoutTapes.HandoffTape,
      CommonGround.LayoutTapes.InputTape] using
      fixedDescriptionBoundedSimulatorCodeRightShifted_haltsWithTape_of_transform
        hparser htransform
  · intro code T hhalt
    rcases hparser.right.right.right code T hhalt with
      ⟨out, htransform, hT⟩
    unfold MachineDescription.SimulatorLayout.normalizeCodePrimitive at htransform
    unfold MachineDescription.SimulatorLayout.normalizeCode at htransform
    cases hdecode :
        MachineDescription.SimulatorLayout.decodeComplete code with
    | none =>
        simp [hdecode] at htransform
    | some L =>
        simp [hdecode] at htransform
        cases htransform
        refine ⟨L, hdecode, ?_⟩
        simpa [CommonGround.SimulatorLayouts.handoffTape,
          CommonGround.SimulatorLayouts.encode,
          CommonGround.LayoutTapes.HandoffTape,
          CommonGround.LayoutTapes.InputTape,
          CommonGround.LayoutTapes.Bits] using hT

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedParserPrimitiveConstruction_of_closedRecognizer
    (h :
      FixedDescriptionBoundedSimulatorCodeRightShiftedParserConstruction) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedParserPrimitiveConstruction := by
  rcases h with ⟨recognizer, hrecognizer⟩
  refine ⟨recognizer, ?_⟩
  constructor
  · exact hrecognizer.left.left
  constructor
  · exact hrecognizer.left.right
  constructor
  · intro code out
    constructor
    · intro hhalt
      rcases hhalt with ⟨n, hn⟩
      let T : Tape Bool :=
        (recognizer.runConfig n
          (recognizer.initial
            (MachineDescription.encodeCodeWordAsInput code))).tape
      have hTape :
          recognizer.HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) T := by
        exact ⟨n, ⟨hn.left, rfl⟩⟩
      rcases hrecognizer.right.right code T hTape with
        ⟨L, hdecode, hT⟩
      have houtBits :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput
              (MachineDescription.SimulatorLayout.encode L) := by
        calc
          MachineDescription.encodeCodeWordAsInput out =
              Tape.normalizedOutput T := by
                simpa [T] using hn.right.symm
          _ =
              MachineDescription.encodeCodeWordAsInput
                (MachineDescription.SimulatorLayout.encode L) := by
                rw [hT]
                simpa [CommonGround.SimulatorLayouts.encode] using
                  CommonGround.SimulatorLayouts.handoffTape_normalizedOutput L
      have hout :
          out = MachineDescription.SimulatorLayout.encode L :=
        MachineDescription.encodeCodeWordAsInput_injective houtBits
      have hdecode' :
          MachineDescription.SimulatorLayout.decodeComplete code = some L := by
        simpa [CommonGround.SimulatorLayouts.decode] using
          hdecode
      simp [MachineDescription.SimulatorLayout.normalizeCodePrimitive,
        MachineDescription.SimulatorLayout.normalizeCode,
        hout, hdecode']
    · intro htransform
      unfold MachineDescription.SimulatorLayout.normalizeCodePrimitive at htransform
      unfold MachineDescription.SimulatorLayout.normalizeCode at htransform
      cases hdecode :
          MachineDescription.SimulatorLayout.decodeComplete code with
      | none =>
          simp [hdecode] at htransform
      | some L =>
          simp [hdecode] at htransform
          cases htransform
          have hcode :
              code = MachineDescription.SimulatorLayout.encode L :=
            CommonGround.SimulatorLayouts.decodeComplete_eq_some_encode
              hdecode
          subst code
          have hhaltTape :
              recognizer.HaltsWithTape
                (CommonGround.SimulatorLayouts.bits L)
                (CommonGround.SimulatorLayouts.handoffTape L) :=
            hrecognizer.right.left L
          have houtput :=
            MachineDescription.haltsWithOutput_of_haltsWithTape hhaltTape
          have hnormalized :
              Tape.normalizedOutput
                  (CommonGround.SimulatorLayouts.handoffTape L) =
                MachineDescription.encodeCodeWordAsInput
                  (MachineDescription.SimulatorLayout.encode L) := by
            simpa [CommonGround.SimulatorLayouts.encode,
              CommonGround.SimulatorLayouts.bits,
              CommonGround.LayoutTapes.Bits] using
              CommonGround.SimulatorLayouts.handoffTape_normalizedOutput L
          rw [hnormalized] at houtput
          simpa [CommonGround.SimulatorLayouts.bits,
            CommonGround.SimulatorLayouts.encode,
            CommonGround.LayoutTapes.Bits] using houtput
  · intro code T hhalt
    rcases hrecognizer.right.right code T hhalt with
      ⟨L, hdecode, hT⟩
    refine ⟨MachineDescription.SimulatorLayout.encode L, ?_, ?_⟩
    · have hdecode' :
          MachineDescription.SimulatorLayout.decodeComplete code = some L := by
        simpa [CommonGround.SimulatorLayouts.decode] using
          hdecode
      simp [MachineDescription.SimulatorLayout.normalizeCodePrimitive,
        MachineDescription.SimulatorLayout.normalizeCode, hdecode']
    · rw [hT]
      simp [CommonGround.SimulatorLayouts.encode,
        CommonGround.LayoutTapes.HandoffTape,
        CommonGround.LayoutTapes.InputTape,
        CommonGround.LayoutTapes.Bits]

/--
Emitter half of the right-shifted code leaf: after the complete simulator
layout has been parsed, emit the fixed-{lean}`D` bounded run/update-hit layout
one cell to the right of the canonical code word.
-/
def FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterSpec
    (D emitter : MachineDescription) : Prop :=
  CommonGround.CodeWordEmitters.EmitterSpec
    MachineDescription.SimulatorLayout.asBoolInput
    (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D)
    emitter

/-- Finite construction target for the fixed description's right-shifted emitter. -/
def FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterConstruction :
    Prop :=
  forall D : MachineDescription,
    exists emitter : MachineDescription,
      FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterSpec D emitter

def FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterRunner
    (sim : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    sim MachineDescription.ExactIdentityDescription Direction.right

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedEmitterSpec_of_canonical
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorCanonicalSpec D sim) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterSpec D
      (FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterRunner sim) := by
  have hidentityReady :
      MachineDescription.ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        hsim.left hidentityReady
  constructor
  · intro L
    have hsimRun :
        sim.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput L)
          (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L) := by
      simpa [FixedDescriptionBoundedSimulatorInput] using
        hsim.right.left L
    exact
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        hsim.left hidentityReady hsimRun
        ⟨0, by
          simp [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode,
            CommonGround.CodeWordEmitters.OutputTape,
            FixedDescriptionBoundedSimulatorCanonicalOutputTape,
            fixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout_eq_run,
            MachineDescription.SimulatorLayout.tape,
            MachineDescription.SimulatorLayout.asBoolInput,
            MachineDescription.runConfig,
            MachineDescription.ExactIdentityDescription]⟩
  · intro L T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          hsim.left hidentityReady hhalt with
      ⟨Tmid, hsimRun, hidentityRun⟩
    have hTmid :
        Tmid = FixedDescriptionBoundedSimulatorCanonicalOutputTape D L := by
      exact
        hsim.right.right L Tmid
          (by
            simpa [FixedDescriptionBoundedSimulatorInput] using hsimRun)
    subst Tmid
    rcases hidentityRun with ⟨n, hn⟩
    have hrun :=
      CommonGround.Identity.exactIdentityDescription_runConfig_from_start
        n
        (Tape.move Direction.right
          (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L))
    rw [hrun] at hn
    have hT :
        Tape.move Direction.right
            (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L) =
          T := by
      simpa using congrArg MachineDescription.Configuration.tape hn
    simpa [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape,
      FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode,
      CommonGround.CodeWordEmitters.OutputTape,
      FixedDescriptionBoundedSimulatorCanonicalOutputTape,
      fixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout_eq_run,
      MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using hT.symm

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedEmitterConstruction_of_canonical
    (hcanonical : FixedDescriptionBoundedSimulatorCanonicalConstruction) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterConstruction := by
  intro D
  rcases hcanonical D with ⟨sim, hsim⟩
  exact
    ⟨FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterRunner sim,
      fixedDescriptionBoundedSimulatorCodeRightShiftedEmitterSpec_of_canonical
        hsim⟩

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
        (CommonGround.SimulatorLayouts.handoffTape L) =
      Tape.input (MachineDescription.SimulatorLayout.asBoolInput L) := by
  exact CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape L

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedSpec_of_parser_emitter
    {D parser emitter : MachineDescription}
    (hparser :
      CommonGround.SimulatorLayouts.ClosedRecognizerSpec
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
          (CommonGround.SimulatorLayouts.handoffTape L) := by
      simpa [FixedDescriptionBoundedSimulatorInput,
        CommonGround.SimulatorLayouts.bits,
        CommonGround.LayoutTapes.Bits,
        CommonGround.SimulatorLayouts.encode] using
        hparser.right.left L
    have hemitterRun :
        emitter.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput L)
          (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape D L) := by
      simpa [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape,
        CommonGround.CodeWordEmitters.OutputTape] using
        hemitter.right.left L
    rcases MachineDescription.runConfig_eq_halt_of_haltsWithTape
      hemitterRun with ⟨n, hn⟩
    exact
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left hparserRun
        ⟨n, by
          simpa [
            CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
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
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            L] using congrArg MachineDescription.Configuration.state hn
      · simpa [MachineDescription.HaltsWithTapeIn,
          MachineDescription.initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
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
  exact
    CommonGround.CodeWordEmitters.rightShiftedOutputCompiled_of_indexed_tape_spec
      hrunner.left.left
      hrunner.left.right
      MachineDescription.SimulatorLayout.encode
      (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D)
      (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape D)
      (by
        intro L
        rfl)
      (by
        intro L
        simpa [FixedDescriptionBoundedSimulatorInput,
          MachineDescription.SimulatorLayout.asBoolInput] using
          hrunner.right.left L)
      (by
        intro code T hhalt
        rcases hrunner.right.right code T hhalt with
          ⟨L, hdecode, hT⟩
        exact
          ⟨L,
            CommonGround.SimulatorLayouts.decode_eq_some_encode hdecode,
            hT⟩)
      (by
        intro code out
        constructor
        · intro htransform
          rcases
              (fixedDescriptionBoundedSimulatorCode_transform_eq_some_iff
                D code out).mp htransform with
            ⟨L, hdecode, hout⟩
          exact
            ⟨L,
              CommonGround.SimulatorLayouts.decode_eq_some_encode
                hdecode,
              hout⟩
        · intro h
          rcases h with ⟨L, hcode, hout⟩
          exact
            (fixedDescriptionBoundedSimulatorCode_transform_eq_some_iff
              D code out).mpr
              ⟨L,
                by
                  rw [hcode]
                  exact CommonGround.SimulatorLayouts.decode_encode L,
                hout⟩)

/--
Narrow finite-machine leaf for the canonical fixed-description simulator: after
the skeleton handoff has moved one cell right from a canonical simulator-layout
tape, one fragment performs the fixed-description bounded run and returns to the
canonical layout tape.
-/
def FixedDescriptionBoundedSimulatorRightHandoffStepPhaseConstruction :
    Prop :=
  forall D : MachineDescription,
    exists simulateStep : MachineDescription.Fragment,
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => MachineDescription.SimulatorLayout.run D L.stage L)
        simulateStep

namespace FixedDescriptionBoundedSimulatorRightHandoffCounterexample

def shrinkTransition : TransitionDescription :=
  { source := 100
    read := none
    write := none
    move := Direction.right
    target := 0 }

def shrinkDescription : MachineDescription :=
  { stateCount := 101
    start := 100
    halt := 0
    transitions := [shrinkTransition] }

def shrinkConfig : MachineDescription.Configuration :=
  { state := 100
    tape := Tape.blank }

def shrinkLayout : MachineDescription.SimulatorLayout :=
  { input := []
    stage := 1
    config := shrinkConfig
    hit := false }

theorem shrinkTarget_contextLength_lt_source :
    Tape.contextLength
        (FixedDescriptionBoundedSimulatorLayoutTape
          (MachineDescription.SimulatorLayout.run shrinkDescription
            shrinkLayout.stage shrinkLayout)) <
      Tape.contextLength
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right
          shrinkLayout) := by
  native_decide

theorem not_rightHandoffStepPhaseRealizes
    (fragment : MachineDescription.Fragment) :
    ¬ FixedDescriptionBoundedSimulatorPhaseRealizes
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L =>
          MachineDescription.SimulatorLayout.run shrinkDescription
            L.stage L)
        fragment := by
  intro h
  rcases h.right shrinkLayout with ⟨steps, hsteps, _hminimal⟩
  have hmono :=
    MachineDescription.runConfig_contextLength_mono
      fragment.toDescription steps
      { state := fragment.entry
        tape :=
          FixedDescriptionBoundedSimulatorHandoffTape Direction.right
            shrinkLayout }
  have hfinal :
      Tape.contextLength
          ((fragment.toDescription.runConfig steps
            { state := fragment.entry
              tape :=
                FixedDescriptionBoundedSimulatorHandoffTape Direction.right
                  shrinkLayout }).tape) =
        Tape.contextLength
          (FixedDescriptionBoundedSimulatorLayoutTape
            (MachineDescription.SimulatorLayout.run shrinkDescription
              shrinkLayout.stage shrinkLayout)) := by
    simpa using
      congrArg (fun c : MachineDescription.Configuration =>
        Tape.contextLength c.tape) hsteps
  rw [hfinal] at hmono
  exact (Nat.not_lt_of_ge hmono) shrinkTarget_contextLength_lt_source

end FixedDescriptionBoundedSimulatorRightHandoffCounterexample

theorem fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_codeRightShifted :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
      FixedDescriptionBoundedSimulatorLayoutTape
      id
      (MachineDescription.Fragment.handoff Direction.left) :=
  fixedDescriptionBoundedSimulatorReturnFromRightHandoffPhaseRealizes

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_rightHandoffStepPhase
    (hstep :
      FixedDescriptionBoundedSimulatorRightHandoffStepPhaseConstruction) :
    FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction := by
  intro D
  rcases hstep D with ⟨simulateStep, hsimulateStep⟩
  let S : MachineDescription.FixedSimulatorTableSkeleton :=
    { decodeLayout := MachineDescription.Fragment.halt
      simulateStep := simulateStep
      repeatControl := MachineDescription.Fragment.handoff Direction.left
      emitLayout := MachineDescription.Fragment.handoff Direction.left
      decodeLayout_wellFormed :=
        MachineDescription.Fragment.halt_wellFormed
      simulateStep_wellFormed := hsimulateStep.left
      repeatControl_wellFormed :=
        MachineDescription.Fragment.handoff_wellFormed Direction.left
      emitLayout_wellFormed :=
        MachineDescription.Fragment.handoff_wellFormed Direction.left }
  refine
    ⟨S, Direction.right,
      FixedDescriptionBoundedSimulatorPhaseTargets.canonical D, ?_⟩
  refine
    { decodeLayout := ?_
      simulateStep := ?_
      repeatControl := ?_
      emitLayout := ?_ }
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorHaltPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      hsimulateStep
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_codeRightShifted
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_codeRightShifted

/--
Finite-machine leaf for the one real phase in the canonical simulator skeleton.
-/
theorem fixedDescriptionBoundedSimulatorRightHandoffStepPhaseConstruction_scaffold :
    FixedDescriptionBoundedSimulatorRightHandoffStepPhaseConstruction := by
  sorry

/--
Finite-machine leaf for the canonical fixed-description simulator used by the
right-shifted emitter adapter.
-/
theorem fixedDescriptionBoundedSimulatorCodeRightShiftedEmitterCanonicalConstruction_scaffold :
    FixedDescriptionBoundedSimulatorCanonicalConstruction := by
  exact
    fixedDescriptionBoundedSimulatorCanonicalConstruction_of_phaseConstruction
      (fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_rightHandoffStepPhase
        fixedDescriptionBoundedSimulatorRightHandoffStepPhaseConstruction_scaffold)

/--
Finite-machine leaf for the fixed-description bounded config runner and
right-shifted simulator-layout emitter.
-/
theorem fixedDescriptionBoundedSimulatorCodeRightShiftedEmitterConstruction_scaffold :
    FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterConstruction := by
  exact
    fixedDescriptionBoundedSimulatorCodeRightShiftedEmitterConstruction_of_canonical
      fixedDescriptionBoundedSimulatorCodeRightShiftedEmitterCanonicalConstruction_scaffold

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_of_specConstruction
    (h :
      FixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction := by
  intro D
  rcases h D with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      fixedDescriptionBoundedSimulatorCodeRightShifted_of_spec hrunner⟩

end Computability
end FoC
