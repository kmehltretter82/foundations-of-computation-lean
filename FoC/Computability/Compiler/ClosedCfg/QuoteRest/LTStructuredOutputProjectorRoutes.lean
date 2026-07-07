import FoC.Computability.Compiler.Structured.Lowering.Projection
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.PhaseOutputAdapters
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTStructuredLowererReadiness

set_option doc.verso true

/-!
# Live-tail structured output projector routes

The static table checks and structured runs are now proved for the live-tail
emitter and joiner.  This module isolates the remaining output-projector
boundary for the lowered one-tape route.

The emitter final structured endpoint still contains meaningful data on two
logical tapes: tape 2 has the emitted quoted prefix, while tape 0 still carries
the live raw tail.  The emitter therefore needs a real assembly-local merge
projector; a plain tape-2 extractor is too weak.

The joiner restore endpoint is simpler.  Its tape 0 already carries the joined
public output up to the intended normalized-output contract.  The generic
structured tape-0 projector is therefore enough to build a joiner lowered
output endpoint.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

/-! ## Output composition for canonical primitive sequences -/

theorem haltsFromTapeWithOutput_of_input_equiv
    {D : MachineDescription} {Tin Tin' : Tape Bool} {out : Word Bool}
    (hin : Tape.Equiv Tin Tin')
    (h : D.HaltsFromTapeWithOutput Tin out) :
    D.HaltsFromTapeWithOutput Tin' out := by
  rcases h with ⟨n, hn⟩
  have hrun :=
    MachineDescription.runConfig_equiv
      D n
      (c := { state := D.start, tape := Tin })
      (d := { state := D.start, tape := Tin' })
      rfl hin
  refine ⟨n, ?_⟩
  constructor
  · change
      (D.runConfig n { state := D.start, tape := Tin' }).state =
        D.halt
    rw [← hrun.left]
    exact hn.left
  · change
      Tape.normalizedOutput
          (D.runConfig n { state := D.start, tape := Tin' }).tape =
        out
    rw [← Tape.Equiv.normalizedOutput_eq hrun.right]
    exact hn.right

theorem canonicalPrimitiveSeqDescription_haltsFromTapeWithOutput_of_haltsFromTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid : Tape Bool} {out : Word Bool}
    (hAmid : A.HaltsFromTape Tin Tmid)
    (hBout :
      B.HaltsFromTapeWithOutput
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        out) :
    (Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription
      A B).HaltsFromTapeWithOutput Tin out := by
  simpa [Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription,
    SeqViaCanonical] using
    SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape
      hA hB hAmid hBout

private theorem moveLeft_moveRight_equiv_self
    (T : Tape Bool) :
    Tape.Equiv
      (Tape.move Direction.left (Tape.move Direction.right T)) T := by
  cases T with
  | mk left head right =>
      simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight]
      cases right <;> simp [Tape.dropTrailingNone]

theorem canonicalPrimitiveSeqDescription_haltsFromTapeWithOutput_of_haltsFromTapeEquiv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid : Tape Bool} {out : Word Bool}
    (hAmid : A.HaltsFromTapeEquiv Tin Tmid)
    (hBout :
      B.HaltsFromTapeWithOutput
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        out) :
    (Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription
      A B).HaltsFromTapeWithOutput Tin out := by
  rcases hAmid with ⟨TmidActual, hAactual, hTmidActual⟩
  have hbounce :
      Tape.Equiv
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        (Tape.move Direction.left (Tape.move Direction.right TmidActual)) :=
    Tape.Equiv.move
      (Tape.Equiv.move (Tape.Equiv.symm hTmidActual) Direction.right)
      Direction.left
  have hBoutActual :
      B.HaltsFromTapeWithOutput
        (Tape.move Direction.left (Tape.move Direction.right TmidActual))
        out :=
    haltsFromTapeWithOutput_of_input_equiv hbounce hBout
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeWithOutput_of_haltsFromTape
      hA hB hAactual hBoutActual

theorem canonicalPrimitiveSeqDescription_haltsFromTapeWithOutput_of_haltsFromTapeEquiv_at
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {Tin Tmid TprojectorIn : Tape Bool} {out : Word Bool}
    (hAmid : A.HaltsFromTapeEquiv Tin Tmid)
    (hbridge :
      Tape.move Direction.left (Tape.move Direction.right Tmid) =
        TprojectorIn)
    (hBout : B.HaltsFromTapeWithOutput TprojectorIn out) :
    (Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription
      A B).HaltsFromTapeWithOutput Tin out := by
  subst TprojectorIn
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeWithOutput_of_haltsFromTapeEquiv
      hA hB hAmid hBout

/-! ## Emitter lowered output endpoint -/

def StructuredLiveTailEmitterOutputProjectorSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      projector.HaltsFromTapeWithOutput
        (Tape.move Direction.left
          (Tape.move Direction.right
            (structuredLiveTailEmitterAssemblyEncodedFinalTape p)))
        (structuredLiveTailEmitterAssemblyTargetOutput p)

def StructuredLiveTailEmitterOutputProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    StructuredLiveTailEmitterOutputProjectorSpec projector

theorem StructuredLiveTailEmitterOutputProjectorSpec.subroutineReady
    {projector : MachineDescription}
    (h : StructuredLiveTailEmitterOutputProjectorSpec projector) :
    projector.SubroutineReady :=
  h.left

theorem StructuredLiveTailEmitterOutputProjectorSpec.run
    {projector : MachineDescription}
    (h : StructuredLiveTailEmitterOutputProjectorSpec projector)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    projector.HaltsFromTapeWithOutput
      (Tape.move Direction.left
        (Tape.move Direction.right
          (structuredLiveTailEmitterAssemblyEncodedFinalTape p)))
      (structuredLiveTailEmitterAssemblyTargetOutput p) :=
  h.right p

def structuredLiveTailEmitterLoweredOutputEndpointDescription
    (projector : MachineDescription) : MachineDescription :=
  Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription
    loweredStructuredLiveTailEmitterDescription projector

def StructuredLiveTailEmitterLoweredOutputEndpointSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      finish.HaltsFromTapeWithOutput
        (structuredLiveTailEmitterAssemblyEncodedInitialTape p)
        (structuredLiveTailEmitterAssemblyTargetOutput p)

def StructuredLiveTailEmitterLoweredOutputEndpointConstruction : Prop :=
  exists finish : MachineDescription,
    StructuredLiveTailEmitterLoweredOutputEndpointSpec finish

theorem StructuredLiveTailEmitterLoweredOutputEndpointSpec.subroutineReady
    {finish : MachineDescription}
    (h : StructuredLiveTailEmitterLoweredOutputEndpointSpec finish) :
    finish.SubroutineReady :=
  h.left

theorem StructuredLiveTailEmitterLoweredOutputEndpointSpec.run
    {finish : MachineDescription}
    (h : StructuredLiveTailEmitterLoweredOutputEndpointSpec finish)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    finish.HaltsFromTapeWithOutput
      (structuredLiveTailEmitterAssemblyEncodedInitialTape p)
      (structuredLiveTailEmitterAssemblyTargetOutput p) :=
  h.right p

theorem structuredLiveTailEmitterLoweredOutputEndpointDescription_subroutineReady
    {projector : MachineDescription}
    (hprojector :
      StructuredLiveTailEmitterOutputProjectorSpec projector) :
    (structuredLiveTailEmitterLoweredOutputEndpointDescription
      projector).SubroutineReady :=
  Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_subroutineReady
    loweredStructuredLiveTailEmitterDescription_subroutineReady_static
    hprojector.subroutineReady

theorem structuredLiveTailEmitterLoweredOutputEndpointDescription_spec
    {projector : MachineDescription}
    (hprojector :
      StructuredLiveTailEmitterOutputProjectorSpec projector) :
    StructuredLiveTailEmitterLoweredOutputEndpointSpec
      (structuredLiveTailEmitterLoweredOutputEndpointDescription
        projector) := by
  constructor
  · exact
      structuredLiveTailEmitterLoweredOutputEndpointDescription_subroutineReady
        hprojector
  · intro p
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeWithOutput_of_haltsFromTapeEquiv
        loweredStructuredLiveTailEmitterDescription_subroutineReady_static
        hprojector.subroutineReady
        (loweredStructuredLiveTailEmitterDescription_haltsFromAssemblyEncoded_static
          p)
        (hprojector.run p)

theorem structuredLiveTailEmitterLoweredOutputEndpointConstruction_of_projector
    (hprojector : StructuredLiveTailEmitterOutputProjectorConstruction) :
    StructuredLiveTailEmitterLoweredOutputEndpointConstruction := by
  rcases hprojector with ⟨projector, hprojector⟩
  exact
    ⟨structuredLiveTailEmitterLoweredOutputEndpointDescription projector,
      structuredLiveTailEmitterLoweredOutputEndpointDescription_spec
        hprojector⟩

/-! ## Joiner restore endpoint shape -/

def structuredLiveTailJoinerAssemblyRestoreSourceTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffSourceTape
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredLiveTailJoinerAssemblyRestoreScratchTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalScratchTape
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredLiveTailJoinerAssemblyRestoreWorkTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalWorkTape
    (assemblySourceRestLiveTailEmitterRawTail p)

theorem structuredLiveTailJoinerAssemblyEncodedRestoreTape_eq_encoded3
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyEncodedRestoreTape p =
      Structured.MultiTapeLowering.encodedGuardedStructured3Tapes
        (structuredLiveTailJoinerAssemblyRestoreSourceTape p)
        (structuredLiveTailJoinerAssemblyRestoreScratchTape p)
        (structuredLiveTailJoinerAssemblyRestoreWorkTape p) := by
  rfl

theorem structuredLiveTailJoinerAssemblyRestoreSourceTape_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyRestoreSourceTape p =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffSourceTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  rfl

theorem structuredLiveTailJoinerAssemblyRestoreScratchTape_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyRestoreScratchTape p =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalScratchTape
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  rfl

theorem structuredLiveTailJoinerAssemblyRestoreWorkTape_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyRestoreWorkTape p =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalWorkTape
        (assemblySourceRestLiveTailEmitterRawTail p) := by
  rfl

theorem structuredLiveTailJoinerAssemblyRestoreSourceTape_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyRestoreSourceTape p) =
      structuredLiveTailJoinerAssemblyTargetOutput p := by
  have hnorm :=
    structuredRawTailInsertionJoinerRestoreHandoff_source_normalizedOutput_eq_joined
      p
  simpa [structuredLiveTailJoinerAssemblyRestoreSourceTape,
    structuredLiveTailJoinerAssemblyTargetTape,
    structuredLiveTailJoinerAssemblyTargetOutput,
    mixedOptionCellQuoteLiveTailJoinedTape_normalizedOutput,
    Structured.Description.tapeAt,
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig,
    Structured.MultiTapeLowering.ThreeTape.config] using hnorm

theorem structuredLiveTailJoinerAssemblyRestoreScratchTape_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyRestoreScratchTape p) =
      assemblySourceRestLiveTailEmitterQuoteRest p := by
  simpa [structuredLiveTailJoinerAssemblyRestoreScratchTape] using
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalScratchTape_normalizedOutput
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredLiveTailJoinerAssemblyRestoreWorkTape_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyRestoreWorkTape p) =
      [] := by
  simpa [structuredLiveTailJoinerAssemblyRestoreWorkTape] using
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalWorkTape_normalizedOutput
      (assemblySourceRestLiveTailEmitterRawTail p)

/-! ## Joiner output projector from the generic tape-0 projector -/

def StructuredLiveTailJoinerOutputProjectorSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      projector.HaltsFromTapeWithOutput
        (Tape.move Direction.left
          (Tape.move Direction.right
            (structuredLiveTailJoinerAssemblyEncodedRestoreTape p)))
        (structuredLiveTailJoinerAssemblyTargetOutput p)

def StructuredLiveTailJoinerOutputProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    StructuredLiveTailJoinerOutputProjectorSpec projector

theorem StructuredLiveTailJoinerOutputProjectorSpec.subroutineReady
    {projector : MachineDescription}
    (h : StructuredLiveTailJoinerOutputProjectorSpec projector) :
    projector.SubroutineReady :=
  h.left

theorem StructuredLiveTailJoinerOutputProjectorSpec.run
    {projector : MachineDescription}
    (h : StructuredLiveTailJoinerOutputProjectorSpec projector)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    projector.HaltsFromTapeWithOutput
      (Tape.move Direction.left
        (Tape.move Direction.right
          (structuredLiveTailJoinerAssemblyEncodedRestoreTape p)))
      (structuredLiveTailJoinerAssemblyTargetOutput p) :=
  h.right p

theorem StructuredLiveTailJoinerOutputProjectorSpec_of_tape0ProjectorSpec
    {projector : MachineDescription}
    (hprojector :
      Structured.MultiTapeLowering.StructuredTape0ProjectorSpec
        projector) :
    StructuredLiveTailJoinerOutputProjectorSpec projector := by
  constructor
  · exact hprojector.left
  · intro p
    let T0 := structuredLiveTailJoinerAssemblyRestoreSourceTape p
    let T1 := structuredLiveTailJoinerAssemblyRestoreScratchTape p
    let T2 := structuredLiveTailJoinerAssemblyRestoreWorkTape p
    have hrun :
        projector.HaltsFromTapeEquiv
          (structuredLiveTailJoinerAssemblyEncodedRestoreTape p)
          T0 := by
      simpa [T0, T1, T2,
        structuredLiveTailJoinerAssemblyEncodedRestoreTape_eq_encoded3 p]
        using hprojector.right T0 T1 T2
    have hout :
        projector.HaltsFromTapeWithOutput
          (structuredLiveTailJoinerAssemblyEncodedRestoreTape p)
          (Tape.normalizedOutput T0) :=
      MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
        hrun
    have hnorm :
        Tape.normalizedOutput T0 =
          structuredLiveTailJoinerAssemblyTargetOutput p := by
      simpa [T0] using
        structuredLiveTailJoinerAssemblyRestoreSourceTape_normalizedOutput p
    have houtTarget :
        projector.HaltsFromTapeWithOutput
          (structuredLiveTailJoinerAssemblyEncodedRestoreTape p)
          (structuredLiveTailJoinerAssemblyTargetOutput p) := by
      rwa [hnorm] at hout
    exact
      haltsFromTapeWithOutput_of_input_equiv
        (Tape.Equiv.symm
          (moveLeft_moveRight_equiv_self
            (structuredLiveTailJoinerAssemblyEncodedRestoreTape p)))
        houtTarget

theorem StructuredLiveTailJoinerOutputProjectorConstruction_of_tape0Projector
    (hprojector :
      Structured.MultiTapeLowering.StructuredTape0ProjectorConstruction) :
    StructuredLiveTailJoinerOutputProjectorConstruction := by
  rcases hprojector with ⟨projector, hprojector⟩
  exact
    ⟨projector,
      StructuredLiveTailJoinerOutputProjectorSpec_of_tape0ProjectorSpec
        hprojector⟩

theorem StructuredLiveTailJoinerOutputProjectorConstruction_of_tape0SegmentNormalizer
    (hnormalizer :
      Structured.MultiTapeLowering.StructuredTape0SegmentNormalizerConstruction) :
    StructuredLiveTailJoinerOutputProjectorConstruction :=
  StructuredLiveTailJoinerOutputProjectorConstruction_of_tape0Projector
    (Structured.MultiTapeLowering.structuredTape0ProjectorConstruction_of_segmentNormalizerConstruction
      hnormalizer)

/-! ## Joiner lowered output endpoint -/

def structuredLiveTailJoinerLoweredOutputEndpointDescription
    (projector : MachineDescription) : MachineDescription :=
  Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription
    loweredStructuredLiveTailJoinerDescription projector

def StructuredLiveTailJoinerLoweredOutputEndpointSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      finish.HaltsFromTapeWithOutput
        (structuredLiveTailJoinerAssemblyEncodedInitialTape p)
        (structuredLiveTailJoinerAssemblyTargetOutput p)

def StructuredLiveTailJoinerLoweredOutputEndpointConstruction : Prop :=
  exists finish : MachineDescription,
    StructuredLiveTailJoinerLoweredOutputEndpointSpec finish

theorem StructuredLiveTailJoinerLoweredOutputEndpointSpec.subroutineReady
    {finish : MachineDescription}
    (h : StructuredLiveTailJoinerLoweredOutputEndpointSpec finish) :
    finish.SubroutineReady :=
  h.left

theorem StructuredLiveTailJoinerLoweredOutputEndpointSpec.run
    {finish : MachineDescription}
    (h : StructuredLiveTailJoinerLoweredOutputEndpointSpec finish)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    finish.HaltsFromTapeWithOutput
      (structuredLiveTailJoinerAssemblyEncodedInitialTape p)
      (structuredLiveTailJoinerAssemblyTargetOutput p) :=
  h.right p

theorem structuredLiveTailJoinerLoweredOutputEndpointDescription_subroutineReady
    {projector : MachineDescription}
    (hprojector :
      StructuredLiveTailJoinerOutputProjectorSpec projector) :
    (structuredLiveTailJoinerLoweredOutputEndpointDescription
      projector).SubroutineReady :=
  Structured.MultiTapeLowering.canonicalPrimitiveSeqDescription_subroutineReady
    loweredStructuredLiveTailJoinerDescription_subroutineReady_static
    hprojector.subroutineReady

theorem structuredLiveTailJoinerLoweredOutputEndpointDescription_spec
    {projector : MachineDescription}
    (hprojector :
      StructuredLiveTailJoinerOutputProjectorSpec projector) :
    StructuredLiveTailJoinerLoweredOutputEndpointSpec
      (structuredLiveTailJoinerLoweredOutputEndpointDescription
        projector) := by
  constructor
  · exact
      structuredLiveTailJoinerLoweredOutputEndpointDescription_subroutineReady
        hprojector
  · intro p
    exact
      canonicalPrimitiveSeqDescription_haltsFromTapeWithOutput_of_haltsFromTapeEquiv
        loweredStructuredLiveTailJoinerDescription_subroutineReady_static
        hprojector.subroutineReady
        (loweredStructuredLiveTailJoinerDescription_haltsFromAssemblyEncoded_static
          p)
        (hprojector.run p)

theorem structuredLiveTailJoinerLoweredOutputEndpointConstruction_of_projector
    (hprojector : StructuredLiveTailJoinerOutputProjectorConstruction) :
    StructuredLiveTailJoinerLoweredOutputEndpointConstruction := by
  rcases hprojector with ⟨projector, hprojector⟩
  exact
    ⟨structuredLiveTailJoinerLoweredOutputEndpointDescription projector,
      structuredLiveTailJoinerLoweredOutputEndpointDescription_spec
        hprojector⟩

theorem structuredLiveTailJoinerLoweredOutputEndpointConstruction_of_tape0Projector
    (hprojector :
      Structured.MultiTapeLowering.StructuredTape0ProjectorConstruction) :
    StructuredLiveTailJoinerLoweredOutputEndpointConstruction :=
  structuredLiveTailJoinerLoweredOutputEndpointConstruction_of_projector
    (StructuredLiveTailJoinerOutputProjectorConstruction_of_tape0Projector
      hprojector)

theorem structuredLiveTailJoinerLoweredOutputEndpointConstruction_of_tape0SegmentNormalizer
    (hnormalizer :
      Structured.MultiTapeLowering.StructuredTape0SegmentNormalizerConstruction) :
    StructuredLiveTailJoinerLoweredOutputEndpointConstruction :=
  structuredLiveTailJoinerLoweredOutputEndpointConstruction_of_projector
    (StructuredLiveTailJoinerOutputProjectorConstruction_of_tape0SegmentNormalizer
      hnormalizer)

/-! ## Combined lowered-output route -/

def StructuredLiveTailLoweredOutputEndpointSpec
    (emitterFinish joinerFinish : MachineDescription) : Prop :=
  StructuredLiveTailEmitterLoweredOutputEndpointSpec emitterFinish ∧
    StructuredLiveTailJoinerLoweredOutputEndpointSpec joinerFinish

def StructuredLiveTailLoweredOutputEndpointConstruction : Prop :=
  exists emitterFinish joinerFinish : MachineDescription,
    StructuredLiveTailLoweredOutputEndpointSpec emitterFinish joinerFinish

theorem StructuredLiveTailLoweredOutputEndpointSpec.emitter
    {emitterFinish joinerFinish : MachineDescription}
    (h :
      StructuredLiveTailLoweredOutputEndpointSpec
        emitterFinish joinerFinish) :
    StructuredLiveTailEmitterLoweredOutputEndpointSpec emitterFinish :=
  h.left

theorem StructuredLiveTailLoweredOutputEndpointSpec.joiner
    {emitterFinish joinerFinish : MachineDescription}
    (h :
      StructuredLiveTailLoweredOutputEndpointSpec
        emitterFinish joinerFinish) :
    StructuredLiveTailJoinerLoweredOutputEndpointSpec joinerFinish :=
  h.right

theorem StructuredLiveTailLoweredOutputEndpointSpec.emitterRun
    {emitterFinish joinerFinish : MachineDescription}
    (h :
      StructuredLiveTailLoweredOutputEndpointSpec
        emitterFinish joinerFinish)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    emitterFinish.HaltsFromTapeWithOutput
      (structuredLiveTailEmitterAssemblyEncodedInitialTape p)
      (structuredLiveTailEmitterAssemblyTargetOutput p) :=
  h.emitter.run p

theorem StructuredLiveTailLoweredOutputEndpointSpec.joinerRun
    {emitterFinish joinerFinish : MachineDescription}
    (h :
      StructuredLiveTailLoweredOutputEndpointSpec
        emitterFinish joinerFinish)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    joinerFinish.HaltsFromTapeWithOutput
      (structuredLiveTailJoinerAssemblyEncodedInitialTape p)
      (structuredLiveTailJoinerAssemblyTargetOutput p) :=
  h.joiner.run p

theorem StructuredLiveTailLoweredOutputEndpointConstruction_of_parts
    (hemitter :
      StructuredLiveTailEmitterLoweredOutputEndpointConstruction)
    (hjoiner :
      StructuredLiveTailJoinerLoweredOutputEndpointConstruction) :
    StructuredLiveTailLoweredOutputEndpointConstruction := by
  rcases hemitter with ⟨emitterFinish, hemitter⟩
  rcases hjoiner with ⟨joinerFinish, hjoiner⟩
  exact ⟨emitterFinish, joinerFinish, hemitter, hjoiner⟩

def StructuredLiveTailOutputProjectorComponentsSpec
    (emitterProjector joinerProjector : MachineDescription) : Prop :=
  StructuredLiveTailEmitterOutputProjectorSpec emitterProjector ∧
    StructuredLiveTailJoinerOutputProjectorSpec joinerProjector

def StructuredLiveTailOutputProjectorComponentsConstruction : Prop :=
  exists emitterProjector joinerProjector : MachineDescription,
    StructuredLiveTailOutputProjectorComponentsSpec
      emitterProjector joinerProjector

theorem StructuredLiveTailOutputProjectorComponentsSpec.emitter
    {emitterProjector joinerProjector : MachineDescription}
    (h :
      StructuredLiveTailOutputProjectorComponentsSpec
        emitterProjector joinerProjector) :
    StructuredLiveTailEmitterOutputProjectorSpec emitterProjector :=
  h.left

theorem StructuredLiveTailOutputProjectorComponentsSpec.joiner
    {emitterProjector joinerProjector : MachineDescription}
    (h :
      StructuredLiveTailOutputProjectorComponentsSpec
        emitterProjector joinerProjector) :
    StructuredLiveTailJoinerOutputProjectorSpec joinerProjector :=
  h.right

theorem StructuredLiveTailLoweredOutputEndpointConstruction_of_projectorComponents
    (hcomponents :
      StructuredLiveTailOutputProjectorComponentsConstruction) :
    StructuredLiveTailLoweredOutputEndpointConstruction := by
  rcases hcomponents with
    ⟨emitterProjector, joinerProjector, hcomponents⟩
  exact
    StructuredLiveTailLoweredOutputEndpointConstruction_of_parts
      (structuredLiveTailEmitterLoweredOutputEndpointConstruction_of_projector
        ⟨emitterProjector, hcomponents.emitter⟩)
      (structuredLiveTailJoinerLoweredOutputEndpointConstruction_of_projector
        ⟨joinerProjector, hcomponents.joiner⟩)

theorem StructuredLiveTailOutputProjectorComponentsConstruction_of_emitterAndTape0
    (hemitter : StructuredLiveTailEmitterOutputProjectorConstruction)
    (hjoiner :
      Structured.MultiTapeLowering.StructuredTape0ProjectorConstruction) :
    StructuredLiveTailOutputProjectorComponentsConstruction := by
  rcases hemitter with ⟨emitterProjector, hemitter⟩
  rcases
    StructuredLiveTailJoinerOutputProjectorConstruction_of_tape0Projector
      hjoiner with
    ⟨joinerProjector, hjoiner⟩
  exact ⟨emitterProjector, joinerProjector, hemitter, hjoiner⟩

theorem StructuredLiveTailLoweredOutputEndpointConstruction_of_emitterAndTape0
    (hemitter : StructuredLiveTailEmitterOutputProjectorConstruction)
    (hjoiner :
      Structured.MultiTapeLowering.StructuredTape0ProjectorConstruction) :
    StructuredLiveTailLoweredOutputEndpointConstruction :=
  StructuredLiveTailLoweredOutputEndpointConstruction_of_projectorComponents
    (StructuredLiveTailOutputProjectorComponentsConstruction_of_emitterAndTape0
      hemitter hjoiner)

theorem StructuredLiveTailLoweredOutputEndpointConstruction_of_emitterAndTape0SegmentNormalizer
    (hemitter : StructuredLiveTailEmitterOutputProjectorConstruction)
    (hjoiner :
      Structured.MultiTapeLowering.StructuredTape0SegmentNormalizerConstruction) :
    StructuredLiveTailLoweredOutputEndpointConstruction :=
  StructuredLiveTailLoweredOutputEndpointConstruction_of_emitterAndTape0
    hemitter
    (Structured.MultiTapeLowering.structuredTape0ProjectorConstruction_of_segmentNormalizerConstruction
      hjoiner)

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
