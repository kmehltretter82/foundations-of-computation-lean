import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.Layouts
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
open MachineDescription

/-- The fixed-description simulator layout update computed by the code leaf. -/
def FixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout
    (D : MachineDescription)
    (L : SimulatorLayout) :
    SimulatorLayout :=
  { L with
    config := D.runConfig L.stage L.config
    hit :=
      L.hit ||
        SimulatorLayout.hitsFromConfigByBool
          D L.config L.stage }

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout_eq_run
    (D : MachineDescription) (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout D L =
      SimulatorLayout.run D L.stage L := by
  rfl

/-- Code word emitted by the right-shifted fixed-description simulator leaf. -/
def FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode
    (D : MachineDescription)
    (L : SimulatorLayout) :
    Word MachineCodeSymbol :=
  SimulatorLayout.encode
    (FixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout D L)

/-- Tape emitted by the right-shifted fixed-description simulator leaf. -/
def FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape
    (D : MachineDescription)
    (L : SimulatorLayout) :
    Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (encodeCodeWordAsInput
        (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L)))

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape_normalizedOutput
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.normalizedOutput
        (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape D L) =
      encodeCodeWordAsInput
        (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L) := by
  simpa [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape] using
    CommonGround.CodeWordEmitters.tape_normalizedOutput_move_right_input
      (encodeCodeWordAsInput
        (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L))

/--
Forward half of the finite simulator-layout runner: on a complete canonical
layout it halts just to the right of the updated layout code.
-/
def FixedDescriptionBoundedSimulatorCodeRightShiftedForwardSpec
    (D runner : MachineDescription) : Prop :=
  forall L : SimulatorLayout,
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
        (encodeCodeWordAsInput code) T ->
      exists L : SimulatorLayout,
        SimulatorLayout.decodeComplete code = some L ∧
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
      SimulatorLayout.normalizeCodePrimitive parser

theorem fixedDescriptionBoundedSimulatorCodeRightShifted_haltsWithTape_of_transform
    {P : TapeCodePrimitive}
    {D : MachineDescription}
    (hD :
      EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
        P D)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out) :
    D.HaltsWithTape
      (encodeCodeWordAsInput code)
      (Tape.move Direction.right
        (Tape.input
          (encodeCodeWordAsInput out))) := by
  have houtput :
      D.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) :=
    (hD.right.right.left code out).mpr htransform
  rcases houtput with ⟨n, hn⟩
  let T : Tape Bool :=
    (D.runConfig n
      (D.initial
        (encodeCodeWordAsInput code))).tape
  have hhalt :
      D.HaltsWithTape
        (encodeCodeWordAsInput code) T := by
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
        SimulatorLayout.normalizeCodePrimitive.transform
            (SimulatorLayout.encode L) =
          some (SimulatorLayout.encode L) :=
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
    unfold SimulatorLayout.normalizeCodePrimitive at htransform
    unfold SimulatorLayout.normalizeCode at htransform
    cases hdecode :
        SimulatorLayout.decodeComplete code with
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
            (encodeCodeWordAsInput code))).tape
      have hTape :
          recognizer.HaltsWithTape
              (encodeCodeWordAsInput code) T := by
        exact ⟨n, ⟨hn.left, rfl⟩⟩
      rcases hrecognizer.right.right code T hTape with
        ⟨L, hdecode, hT⟩
      have houtBits :
          encodeCodeWordAsInput out =
            encodeCodeWordAsInput
              (SimulatorLayout.encode L) := by
        calc
          encodeCodeWordAsInput out =
              Tape.normalizedOutput T := by
                simpa [T] using hn.right.symm
          _ =
              encodeCodeWordAsInput
                (SimulatorLayout.encode L) := by
                rw [hT]
                simpa [CommonGround.SimulatorLayouts.encode] using
                  CommonGround.SimulatorLayouts.handoffTape_normalizedOutput L
      have hout :
          out = SimulatorLayout.encode L :=
        encodeCodeWordAsInput_injective houtBits
      have hdecode' :
          SimulatorLayout.decodeComplete code = some L := by
        simpa [CommonGround.SimulatorLayouts.decode] using
          hdecode
      simp [SimulatorLayout.normalizeCodePrimitive,
        SimulatorLayout.normalizeCode,
        hout, hdecode']
    · intro htransform
      unfold SimulatorLayout.normalizeCodePrimitive at htransform
      unfold SimulatorLayout.normalizeCode at htransform
      cases hdecode :
          SimulatorLayout.decodeComplete code with
      | none =>
          simp [hdecode] at htransform
      | some L =>
          simp [hdecode] at htransform
          cases htransform
          have hcode :
              code = SimulatorLayout.encode L :=
            CommonGround.SimulatorLayouts.decodeComplete_eq_some_encode
              hdecode
          subst code
          have hhaltTape :
              recognizer.HaltsWithTape
                (CommonGround.SimulatorLayouts.bits L)
                (CommonGround.SimulatorLayouts.handoffTape L) :=
            hrecognizer.right.left L
          have houtput :=
            haltsWithOutput_of_haltsWithTape hhaltTape
          have hnormalized :
              Tape.normalizedOutput
                  (CommonGround.SimulatorLayouts.handoffTape L) =
                encodeCodeWordAsInput
                  (SimulatorLayout.encode L) := by
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
    refine ⟨SimulatorLayout.encode L, ?_, ?_⟩
    · have hdecode' :
          SimulatorLayout.decodeComplete code = some L := by
        simpa [CommonGround.SimulatorLayouts.decode] using
          hdecode
      simp [SimulatorLayout.normalizeCodePrimitive,
        SimulatorLayout.normalizeCode, hdecode']
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
    SimulatorLayout.asBoolInput
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
  seqSubroutine
    sim ExactIdentityDescription Direction.right

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedEmitterSpec_of_canonical
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorCanonicalSpec D sim) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterSpec D
      (FixedDescriptionBoundedSimulatorCodeRightShiftedEmitterRunner sim) := by
  have hidentityReady :
      ExactIdentityDescription.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      seqSubroutine_subroutineReady
        hsim.left hidentityReady
  constructor
  · intro L
    have hsimRun :
        sim.HaltsWithTape
          (SimulatorLayout.asBoolInput L)
          (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L) := by
      simpa [FixedDescriptionBoundedSimulatorInput] using
        hsim.right.left L
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        hsim.left hidentityReady hsimRun
        ⟨0, by
          simp [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode,
            CommonGround.CodeWordEmitters.OutputTape,
            FixedDescriptionBoundedSimulatorCanonicalOutputTape,
            fixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout_eq_run,
            SimulatorLayout.tape,
            SimulatorLayout.asBoolInput,
            runConfig,
            ExactIdentityDescription]⟩
  · intro L T hhalt
    rcases
        seqSubroutine_haltsWithTape_inv
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
      simpa using congrArg Configuration.tape hn
    simpa [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape,
      FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode,
      CommonGround.CodeWordEmitters.OutputTape,
      FixedDescriptionBoundedSimulatorCanonicalOutputTape,
      fixedDescriptionBoundedSimulatorCodeRightShiftedRunLayout_eq_run,
      SimulatorLayout.tape,
      SimulatorLayout.asBoolInput] using hT.symm

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
  seqSubroutine parser emitter Direction.left

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedParser_handoff
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (CommonGround.SimulatorLayouts.handoffTape L) =
      Tape.input (SimulatorLayout.asBoolInput L) := by
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
    exact seqSubroutine_subroutineReady
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
          (SimulatorLayout.asBoolInput L)
          (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape D L) := by
      simpa [FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape,
        CommonGround.CodeWordEmitters.OutputTape] using
        hemitter.right.left L
    rcases runConfig_eq_halt_of_haltsWithTape
      hemitterRun with ⟨n, hn⟩
    exact
      seqSubroutine_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left hparserRun
        ⟨n, by
          simpa [
            CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
              L] using hn⟩
  · intro code T hhalt
    rcases
        seqSubroutine_haltsWithTape_inv
          hparser.left hemitter.left hhalt with
      ⟨Tmid, hparserRun, hemitterReach⟩
    rcases hparser.right.right code Tmid hparserRun with
      ⟨L, hdecode, hTmid⟩
    refine ⟨L, hdecode, ?_⟩
    rcases hemitterReach with ⟨n, hn⟩
    have hemitterRun :
        emitter.HaltsWithTape
          (SimulatorLayout.asBoolInput L) T := by
      refine ⟨n, ?_⟩
      constructor
      · simpa [HaltsWithTapeIn,
          initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            L] using congrArg Configuration.state hn
      · simpa [HaltsWithTapeIn,
          initial, hTmid,
          CommonGround.SimulatorLayouts.handoffTape_move_left_eq_tape
            L] using congrArg Configuration.tape hn
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
      exists L : SimulatorLayout,
        SimulatorLayout.decodeComplete code = some L ∧
          out =
            FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D L := by
  constructor
  · intro h
    unfold FixedDescriptionBoundedSimulatorCode at h
    unfold SimulatorLayout.runCodePrimitive at h
    unfold SimulatorLayout.runCode at h
    cases hdecode :
        SimulatorLayout.decodeComplete code with
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
    unfold SimulatorLayout.runCodePrimitive
    unfold SimulatorLayout.runCode
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
      SimulatorLayout.encode
      (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputCode D)
      (FixedDescriptionBoundedSimulatorCodeRightShiftedOutputTape D)
      (by
        intro L
        rfl)
      (by
        intro L
        simpa [FixedDescriptionBoundedSimulatorInput,
          SimulatorLayout.asBoolInput] using
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
    exists simulateStep : Fragment,
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => SimulatorLayout.run D L.stage L)
        simulateStep

theorem fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_codeRightShifted :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
      FixedDescriptionBoundedSimulatorLayoutTape
      id
      (Fragment.handoff Direction.left) :=
  fixedDescriptionBoundedSimulatorReturnFromRightHandoffPhaseRealizes

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_rightHandoffStepPhase
    (hstep :
      FixedDescriptionBoundedSimulatorRightHandoffStepPhaseConstruction) :
    FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction := by
  intro D
  rcases hstep D with ⟨simulateStep, hsimulateStep⟩
  let S : FixedSimulatorTableSkeleton :=
    { decodeLayout := Fragment.halt
      simulateStep := simulateStep
      repeatControl := Fragment.handoff Direction.left
      emitLayout := Fragment.handoff Direction.left
      decodeLayout_wellFormed :=
        Fragment.halt_wellFormed
      simulateStep_wellFormed := hsimulateStep.left
      repeatControl_wellFormed :=
        Fragment.handoff_wellFormed Direction.left
      emitLayout_wellFormed :=
        Fragment.handoff_wellFormed Direction.left }
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

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_of_specConstruction
    (h :
      FixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction := by
  intro D
  rcases h D with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      fixedDescriptionBoundedSimulatorCodeRightShifted_of_spec hrunner⟩

theorem fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_of_parser_rightHandoffStep
    (hparser : FixedDescriptionBoundedSimulatorCodeRightShiftedParserConstruction)
    (hstep :
      FixedDescriptionBoundedSimulatorRightHandoffStepPhaseConstruction) :
    FixedDescriptionBoundedSimulatorCodeRightShiftedConstruction := by
  exact
    fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_of_specConstruction
      (fixedDescriptionBoundedSimulatorCodeRightShiftedSpecConstruction_of_parserEmitter
        ⟨hparser,
          fixedDescriptionBoundedSimulatorCodeRightShiftedEmitterConstruction_of_canonical
            (fixedDescriptionBoundedSimulatorCanonicalConstruction_of_phaseConstruction
              (fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_rightHandoffStepPhase
                hstep))⟩)

end Computability
end FoC
