import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTJoinerOutput

set_option doc.verso true

/-!
# Live-tail gap-scan output contracts

The source-rest live-tail route has a small exact middle phase between the
emitter and joiner: the right-blank gap payload scanner moves the raw-tail
payload across the blank gap so the joiner can restore the final source-rest
layout.  This module records that phase as its own output-facing contract.

The contract intentionally keeps the exact tape handoff visible.  The scanner
can produce a normalized-output fact, but its input is still the exact
prefix-quoted-separated tape parked at the right cursor position.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

/-! ## Parameterized gap-scan shape -/

structure AssemblySourceRestLiveTailGapParam where
  w : Word Bool
  sourceRestBits : Word Bool
  stage : Nat
  head : Bool
  rawTailRest : Word Bool
  rawTail_eq :
    assemblySourceRestFinishRawTailBits sourceRestBits stage =
      head :: rawTailRest

def AssemblySourceRestLiveTailGapParam.ofRawTailCons
    (w sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (rawTailRest : Word Bool)
    (hraw :
      assemblySourceRestFinishRawTailBits sourceRestBits stage =
        head :: rawTailRest) :
    AssemblySourceRestLiveTailGapParam where
  w := w
  sourceRestBits := sourceRestBits
  stage := stage
  head := head
  rawTailRest := rawTailRest
  rawTail_eq := hraw

theorem AssemblySourceRestLiveTailGapParam.rawTailBits_eq_cons
    (p : AssemblySourceRestLiveTailGapParam) :
    assemblySourceRestFinishRawTailBits p.sourceRestBits p.stage =
      p.head :: p.rawTailRest :=
  p.rawTail_eq

theorem exists_assemblySourceRestLiveTailGapParam
    (w sourceRestBits : Word Bool) (stage : Nat) :
    exists p : AssemblySourceRestLiveTailGapParam,
      p.w = w ∧ p.sourceRestBits = sourceRestBits ∧ p.stage = stage := by
  rcases assemblySourceRestFinishRawTailBits_cons_exists
      sourceRestBits stage with
    ⟨head, rawTailRest, hraw⟩
  exact
    ⟨AssemblySourceRestLiveTailGapParam.ofRawTailCons
        w sourceRestBits stage head rawTailRest hraw,
      rfl, rfl, rfl⟩

def assemblySourceRestLiveTailGapBaseLeft
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List (Option Bool) :=
  ((List.append
    (MixedParserStackRewriterLengthHeader
      (assemblySourceRestFinishParserPrefixCells w)
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage)
      sourceRestBits)
    (MixedParserStackRewriterPrefixQuote
      (assemblySourceRestFinishParserPrefixCells w)
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage))).reverse.map some)

def assemblySourceRestLiveTailGapPadding
    (sourceRestBits : Word Bool) : List (Option Bool) :=
  List.append ((preservingCellPassCellBits sourceRestBits).map some) [none]

def assemblySourceRestLiveTailGapSourceTape
    (p : AssemblySourceRestLiveTailGapParam) : Tape Bool :=
  CommonGround.FiniteTransducers.rightBlankGapPayloadScanSourceTape
    (assemblySourceRestLiveTailGapBaseLeft
      p.w p.sourceRestBits p.stage)
    0 p.head p.rawTailRest
    (assemblySourceRestLiveTailGapPadding p.sourceRestBits)

def assemblySourceRestLiveTailGapTargetTape
    (p : AssemblySourceRestLiveTailGapParam) : Tape Bool :=
  CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
    (assemblySourceRestLiveTailGapBaseLeft
      p.w p.sourceRestBits p.stage)
    0 p.head p.rawTailRest
    (assemblySourceRestLiveTailGapPadding p.sourceRestBits)

def assemblySourceRestLiveTailGapAssemblySourceTape
    (p : AssemblySourceRestLiveTailGapParam) : Tape Bool :=
  MixedParserStackWholeSourcePrefixQuotedSeparatedTape
    p.w p.sourceRestBits p.stage

def assemblySourceRestLiveTailGapAssemblyTargetTape
    (p : AssemblySourceRestLiveTailGapParam) : Tape Bool :=
  MixedParserStackWholeSourceAfterRawTailScanTape
    p.w p.sourceRestBits p.stage

def assemblySourceRestLiveTailGapSourceOutput
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  assemblySourceRestFinishPrefixQuotedSeparatedOutput
    w sourceRestBits stage

def assemblySourceRestLiveTailGapTargetOutput
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  assemblySourceRestFinishSeparatedOutput
    w sourceRestBits stage

theorem assemblySourceRestLiveTailGapBaseLeft_eq
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestLiveTailGapBaseLeft w sourceRestBits stage =
      ((List.append
        (MixedParserStackRewriterLengthHeader
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits)
        (MixedParserStackRewriterPrefixQuote
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage))).reverse.map some) := by
  rfl

theorem assemblySourceRestLiveTailGapPadding_eq
    (sourceRestBits : Word Bool) :
    assemblySourceRestLiveTailGapPadding sourceRestBits =
      List.append ((preservingCellPassCellBits sourceRestBits).map some)
        [none] := by
  rfl

theorem assemblySourceRestLiveTailGapSourceTape_eq
    (p : AssemblySourceRestLiveTailGapParam) :
    assemblySourceRestLiveTailGapSourceTape p =
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanSourceTape
        (assemblySourceRestLiveTailGapBaseLeft
          p.w p.sourceRestBits p.stage)
        0 p.head p.rawTailRest
        (assemblySourceRestLiveTailGapPadding p.sourceRestBits) := by
  rfl

theorem assemblySourceRestLiveTailGapTargetTape_eq
    (p : AssemblySourceRestLiveTailGapParam) :
    assemblySourceRestLiveTailGapTargetTape p =
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
        (assemblySourceRestLiveTailGapBaseLeft
          p.w p.sourceRestBits p.stage)
        0 p.head p.rawTailRest
        (assemblySourceRestLiveTailGapPadding p.sourceRestBits) := by
  rfl

theorem assemblySourceRestLiveTailGapAssemblySourceTape_eq_gapSource
    (p : AssemblySourceRestLiveTailGapParam) :
    assemblySourceRestLiveTailGapAssemblySourceTape p =
      assemblySourceRestLiveTailGapSourceTape p := by
  rw [assemblySourceRestLiveTailGapAssemblySourceTape,
    assemblySourceRestLiveTailGapSourceTape,
    assemblySourceRestLiveTailGapBaseLeft,
    assemblySourceRestLiveTailGapPadding]
  exact
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_gapPayloadScanSource
      p.w p.sourceRestBits p.stage p.head p.rawTailRest p.rawTail_eq

theorem assemblySourceRestLiveTailGapAssemblyTargetTape_eq_gapTarget
    (p : AssemblySourceRestLiveTailGapParam) :
    assemblySourceRestLiveTailGapAssemblyTargetTape p =
      assemblySourceRestLiveTailGapTargetTape p := by
  rw [assemblySourceRestLiveTailGapAssemblyTargetTape,
    MixedParserStackWholeSourceAfterRawTailScanTape,
    p.rawTail_eq,
    assemblySourceRestLiveTailGapTargetTape,
    assemblySourceRestLiveTailGapBaseLeft,
    assemblySourceRestLiveTailGapPadding]

theorem assemblySourceRestLiveTailGapSourceTape_eq_assemblySource
    (p : AssemblySourceRestLiveTailGapParam) :
    assemblySourceRestLiveTailGapSourceTape p =
      assemblySourceRestLiveTailGapAssemblySourceTape p :=
  (assemblySourceRestLiveTailGapAssemblySourceTape_eq_gapSource p).symm

theorem assemblySourceRestLiveTailGapTargetTape_eq_assemblyTarget
    (p : AssemblySourceRestLiveTailGapParam) :
    assemblySourceRestLiveTailGapTargetTape p =
      assemblySourceRestLiveTailGapAssemblyTargetTape p :=
  (assemblySourceRestLiveTailGapAssemblyTargetTape_eq_gapTarget p).symm

theorem assemblySourceRestLiveTailGapAssemblySourceTape_normalizedOutput
    (p : AssemblySourceRestLiveTailGapParam) :
    Tape.normalizedOutput
        (assemblySourceRestLiveTailGapAssemblySourceTape p) =
      assemblySourceRestLiveTailGapSourceOutput
        p.w p.sourceRestBits p.stage := by
  rw [assemblySourceRestLiveTailGapAssemblySourceTape,
    assemblySourceRestLiveTailGapSourceOutput]
  exact
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_normalizedOutput
      p.w p.sourceRestBits p.stage

theorem assemblySourceRestLiveTailGapAssemblyTargetTape_normalizedOutput
    (p : AssemblySourceRestLiveTailGapParam) :
    Tape.normalizedOutput
        (assemblySourceRestLiveTailGapAssemblyTargetTape p) =
      assemblySourceRestLiveTailGapTargetOutput
        p.w p.sourceRestBits p.stage := by
  rw [assemblySourceRestLiveTailGapAssemblyTargetTape,
    assemblySourceRestLiveTailGapTargetOutput]
  exact
    MixedParserStackWholeSourceAfterRawTailScanTape_normalizedOutput
      p.w p.sourceRestBits p.stage

theorem assemblySourceRestLiveTailGapSourceTape_normalizedOutput
    (p : AssemblySourceRestLiveTailGapParam) :
    Tape.normalizedOutput
        (assemblySourceRestLiveTailGapSourceTape p) =
      assemblySourceRestLiveTailGapSourceOutput
        p.w p.sourceRestBits p.stage := by
  rw [assemblySourceRestLiveTailGapSourceTape_eq_assemblySource]
  exact assemblySourceRestLiveTailGapAssemblySourceTape_normalizedOutput p

theorem assemblySourceRestLiveTailGapTargetTape_normalizedOutput
    (p : AssemblySourceRestLiveTailGapParam) :
    Tape.normalizedOutput
        (assemblySourceRestLiveTailGapTargetTape p) =
      assemblySourceRestLiveTailGapTargetOutput
        p.w p.sourceRestBits p.stage := by
  rw [assemblySourceRestLiveTailGapTargetTape_eq_assemblyTarget]
  exact assemblySourceRestLiveTailGapAssemblyTargetTape_normalizedOutput p

theorem assemblySourceRestLiveTailGapTargetTape_normalizedOutput_eq_generic
    (p : AssemblySourceRestLiveTailGapParam) :
    Tape.normalizedOutput
        (assemblySourceRestLiveTailGapTargetTape p) =
      rightBlankGapPayloadScanTargetNormalizedOutput
        (assemblySourceRestLiveTailGapBaseLeft
          p.w p.sourceRestBits p.stage)
        0 p.head p.rawTailRest
        (assemblySourceRestLiveTailGapPadding p.sourceRestBits) := by
  rw [assemblySourceRestLiveTailGapTargetTape]
  exact
    rightBlankGapPayloadScanTargetTape_normalizedOutput
      (assemblySourceRestLiveTailGapBaseLeft
        p.w p.sourceRestBits p.stage)
      0 p.head p.rawTailRest
      (assemblySourceRestLiveTailGapPadding p.sourceRestBits)

theorem assemblySourceRestLiveTailGapSourceOutput_eq_targetOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestLiveTailGapSourceOutput w sourceRestBits stage =
      assemblySourceRestLiveTailGapTargetOutput w sourceRestBits stage := by
  rfl

theorem assemblySourceRestLiveTailGapTargetOutput_eq_sourceOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestLiveTailGapTargetOutput w sourceRestBits stage =
      assemblySourceRestLiveTailGapSourceOutput w sourceRestBits stage := by
  rfl

theorem assemblySourceRestLiveTailGapTargetOutput_eq_joinerSource
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestLiveTailGapTargetOutput w sourceRestBits stage =
      mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) := by
  rfl

theorem assemblySourceRestLiveTailGapSourceOutput_eq_emitterTarget
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestLiveTailGapSourceOutput w sourceRestBits stage =
      mixedOptionCellQuoteLiveTailEmitterTargetNormalizedOutput
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) := by
  rfl

theorem assemblySourceRestLiveTailGapTargetTape_normalizedOutput_eq_joinerSource
    (p : AssemblySourceRestLiveTailGapParam) :
    Tape.normalizedOutput
        (assemblySourceRestLiveTailGapTargetTape p) =
      mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput
        (assemblySourceRestFinishPrefixQuoteOutputBits
          p.w p.sourceRestBits p.stage)
        (assemblySourceRestFinishRawTailBits p.sourceRestBits p.stage)
        (preservingCellPassCellBits p.sourceRestBits) := by
  rw [assemblySourceRestLiveTailGapTargetTape_normalizedOutput,
    assemblySourceRestLiveTailGapTargetOutput_eq_joinerSource]

/-! ## Exact and output contracts for the gap scanner -/

def RightBlankGapPayloadScanParamTapeSpec
    (D : MachineDescription) : Prop :=
  D.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailGapParam,
      D.HaltsFromTape
        (assemblySourceRestLiveTailGapSourceTape p)
        (assemblySourceRestLiveTailGapTargetTape p)

def RightBlankGapPayloadScanAssemblyTapeSpec
    (D : MachineDescription) : Prop :=
  D.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      D.HaltsFromTape
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage)
        (MixedParserStackWholeSourceAfterRawTailScanTape
          w sourceRestBits stage)

def RightBlankGapPayloadScanParamOutputSpec
    (D : MachineDescription) : Prop :=
  D.SubroutineReady ∧
    forall p : AssemblySourceRestLiveTailGapParam,
      D.HaltsFromTapeWithOutput
        (assemblySourceRestLiveTailGapSourceTape p)
        (assemblySourceRestLiveTailGapTargetOutput
          p.w p.sourceRestBits p.stage)

def RightBlankGapPayloadScanAssemblyOutputSpec
    (D : MachineDescription) : Prop :=
  D.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      D.HaltsFromTapeWithOutput
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage)
        (assemblySourceRestLiveTailGapTargetOutput
          w sourceRestBits stage)

def RightBlankGapPayloadScanAssemblyOutputConstruction : Prop :=
  exists finish : MachineDescription,
    RightBlankGapPayloadScanAssemblyOutputSpec finish

theorem RightBlankGapPayloadScanParamTapeSpec.subroutineReady
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanParamTapeSpec D) :
    D.SubroutineReady :=
  hD.left

theorem RightBlankGapPayloadScanParamTapeSpec.haltsFromTape
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanParamTapeSpec D)
    (p : AssemblySourceRestLiveTailGapParam) :
    D.HaltsFromTape
      (assemblySourceRestLiveTailGapSourceTape p)
      (assemblySourceRestLiveTailGapTargetTape p) :=
  hD.right p

theorem RightBlankGapPayloadScanAssemblyTapeSpec.subroutineReady
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanAssemblyTapeSpec D) :
    D.SubroutineReady :=
  hD.left

theorem RightBlankGapPayloadScanAssemblyTapeSpec.haltsFromTape
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanAssemblyTapeSpec D)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    D.HaltsFromTape
      (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage)
      (MixedParserStackWholeSourceAfterRawTailScanTape
        w sourceRestBits stage) :=
  hD.right w sourceRestBits stage

theorem RightBlankGapPayloadScanParamOutputSpec.subroutineReady
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanParamOutputSpec D) :
    D.SubroutineReady :=
  hD.left

theorem RightBlankGapPayloadScanParamOutputSpec.haltsFromTapeWithOutput
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanParamOutputSpec D)
    (p : AssemblySourceRestLiveTailGapParam) :
    D.HaltsFromTapeWithOutput
      (assemblySourceRestLiveTailGapSourceTape p)
      (assemblySourceRestLiveTailGapTargetOutput
        p.w p.sourceRestBits p.stage) :=
  hD.right p

theorem RightBlankGapPayloadScanAssemblyOutputSpec.subroutineReady
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanAssemblyOutputSpec D) :
    D.SubroutineReady :=
  hD.left

theorem RightBlankGapPayloadScanAssemblyOutputSpec.haltsFromTapeWithOutput
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanAssemblyOutputSpec D)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    D.HaltsFromTapeWithOutput
      (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage)
      (assemblySourceRestLiveTailGapTargetOutput
        w sourceRestBits stage) :=
  hD.right w sourceRestBits stage

theorem RightBlankGapPayloadScanParamTapeSpec.toAssemblyTapeSpec
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanParamTapeSpec D) :
    RightBlankGapPayloadScanAssemblyTapeSpec D := by
  refine ⟨hD.subroutineReady, ?_⟩
  intro w sourceRestBits stage
  rcases exists_assemblySourceRestLiveTailGapParam
      w sourceRestBits stage with
    ⟨p, hpw, hpsource, hpstage⟩
  subst hpw
  subst hpsource
  subst hpstage
  change
    D.HaltsFromTape
      (assemblySourceRestLiveTailGapAssemblySourceTape p)
      (assemblySourceRestLiveTailGapAssemblyTargetTape p)
  rw [assemblySourceRestLiveTailGapAssemblySourceTape_eq_gapSource,
    assemblySourceRestLiveTailGapAssemblyTargetTape_eq_gapTarget]
  exact hD.haltsFromTape p

theorem RightBlankGapPayloadScanAssemblyTapeSpec.toOutputSpec
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanAssemblyTapeSpec D) :
    RightBlankGapPayloadScanAssemblyOutputSpec D := by
  refine ⟨hD.subroutineReady, ?_⟩
  intro w sourceRestBits stage
  have hhalt :
      D.HaltsFromTapeWithOutput
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage)
        (Tape.normalizedOutput
          (MixedParserStackWholeSourceAfterRawTailScanTape
            w sourceRestBits stage)) :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape
      (hD.haltsFromTape w sourceRestBits stage)
  simpa [
    MixedParserStackWholeSourceAfterRawTailScanTape_normalizedOutput,
    assemblySourceRestLiveTailGapTargetOutput]
    using hhalt

theorem RightBlankGapPayloadScanParamTapeSpec.toParamOutputSpec
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanParamTapeSpec D) :
    RightBlankGapPayloadScanParamOutputSpec D := by
  refine ⟨hD.subroutineReady, ?_⟩
  intro p
  have hhalt :
      D.HaltsFromTapeWithOutput
        (assemblySourceRestLiveTailGapSourceTape p)
        (Tape.normalizedOutput
          (assemblySourceRestLiveTailGapTargetTape p)) :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape
      (hD.haltsFromTape p)
  simpa [
    assemblySourceRestLiveTailGapTargetTape_normalizedOutput]
    using hhalt

theorem RightBlankGapPayloadScanParamOutputSpec.toAssemblyOutputSpec
    {D : MachineDescription}
    (hD : RightBlankGapPayloadScanParamOutputSpec D) :
    RightBlankGapPayloadScanAssemblyOutputSpec D := by
  refine ⟨hD.subroutineReady, ?_⟩
  intro w sourceRestBits stage
  rcases exists_assemblySourceRestLiveTailGapParam
      w sourceRestBits stage with
    ⟨p, hpw, hpsource, hpstage⟩
  subst hpw
  subst hpsource
  subst hpstage
  change
    D.HaltsFromTapeWithOutput
      (assemblySourceRestLiveTailGapAssemblySourceTape p)
      (assemblySourceRestLiveTailGapTargetOutput
        p.w p.sourceRestBits p.stage)
  rw [assemblySourceRestLiveTailGapAssemblySourceTape_eq_gapSource]
  exact hD.haltsFromTapeWithOutput p

theorem rightBlankGapPayloadScanDescription_paramTapeSpec :
    RightBlankGapPayloadScanParamTapeSpec
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription := by
  refine
    ⟨CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription_subroutineReady,
      ?_⟩
  intro p
  simpa [
    assemblySourceRestLiveTailGapSourceTape,
    assemblySourceRestLiveTailGapTargetTape,
    assemblySourceRestLiveTailGapBaseLeft,
    assemblySourceRestLiveTailGapPadding,
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_gapPayloadScanSource
      p.w p.sourceRestBits p.stage p.head p.rawTailRest p.rawTail_eq]
    using
      rightBlankGapPayloadScanDescription_haltsFrom_prefixQuotedSeparatedTape
        p.w p.sourceRestBits p.stage p.head p.rawTailRest p.rawTail_eq

theorem rightBlankGapPayloadScanDescription_assemblyTapeSpec :
    RightBlankGapPayloadScanAssemblyTapeSpec
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription :=
  rightBlankGapPayloadScanDescription_paramTapeSpec.toAssemblyTapeSpec

theorem rightBlankGapPayloadScanDescription_paramOutputSpec :
    RightBlankGapPayloadScanParamOutputSpec
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription :=
  rightBlankGapPayloadScanDescription_paramTapeSpec.toParamOutputSpec

theorem rightBlankGapPayloadScanDescription_assemblyOutputSpec :
    RightBlankGapPayloadScanAssemblyOutputSpec
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription :=
  rightBlankGapPayloadScanDescription_assemblyTapeSpec.toOutputSpec

theorem rightBlankGapPayloadScanAssemblyOutputConstruction :
    RightBlankGapPayloadScanAssemblyOutputConstruction :=
  ⟨CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription,
    rightBlankGapPayloadScanDescription_assemblyOutputSpec⟩

/-! ## Source-rest output component bundles -/

def MixedParserStackSourceRestFinishOutputComponentsSpec
    (prefixFinish gapFinish joinFinish : MachineDescription) : Prop :=
  MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec
    prefixFinish ∧
  RightBlankGapPayloadScanAssemblyOutputSpec gapFinish ∧
  MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
    joinFinish

def MixedParserStackSourceRestFinishExactGapOutputComponentsSpec
    (prefixFinish gapFinish joinFinish : MachineDescription) : Prop :=
  MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec
    prefixFinish ∧
  RightBlankGapPayloadScanAssemblyTapeSpec gapFinish ∧
  MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
    joinFinish

theorem MixedParserStackSourceRestFinishOutputComponentsSpec.prefix
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec
      prefixFinish :=
  h.left

theorem MixedParserStackSourceRestFinishOutputComponentsSpec.gap
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    RightBlankGapPayloadScanAssemblyOutputSpec gapFinish :=
  h.right.left

theorem MixedParserStackSourceRestFinishOutputComponentsSpec.join
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
      joinFinish :=
  h.right.right

theorem MixedParserStackSourceRestFinishExactGapOutputComponentsSpec.prefix
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec
      prefixFinish :=
  h.left

theorem MixedParserStackSourceRestFinishExactGapOutputComponentsSpec.gap
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    RightBlankGapPayloadScanAssemblyTapeSpec gapFinish :=
  h.right.left

theorem MixedParserStackSourceRestFinishExactGapOutputComponentsSpec.join
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
      joinFinish :=
  h.right.right

theorem MixedParserStackSourceRestFinishExactGapOutputComponentsSpec.toOutputComponents
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    MixedParserStackSourceRestFinishOutputComponentsSpec
      prefixFinish gapFinish joinFinish :=
  ⟨h.prefix, h.gap.toOutputSpec, h.join⟩

theorem MixedParserStackSourceRestFinishOutputComponentsSpec.prefix_subroutineReady
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    prefixFinish.SubroutineReady :=
  MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec_subroutineReady
    h.prefix

theorem MixedParserStackSourceRestFinishOutputComponentsSpec.gap_subroutineReady
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    gapFinish.SubroutineReady :=
  h.gap.subroutineReady

theorem MixedParserStackSourceRestFinishOutputComponentsSpec.join_subroutineReady
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    joinFinish.SubroutineReady :=
  MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec_subroutineReady
    h.join

theorem MixedParserStackSourceRestFinishOutputComponentsSpec.prefix_output
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishOutputComponentsSpec
        prefixFinish gapFinish joinFinish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    prefixFinish.HaltsFromTapeWithOutput
      (MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits
        (preservingCellPassCellBits sourceRestBits)
        stage)
      (assemblySourceRestLiveTailGapSourceOutput
        w sourceRestBits stage) := by
  simpa [assemblySourceRestLiveTailGapSourceOutput,
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_normalizedOutput]
    using
    MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestOutputSpec_haltsFromTapeWithOutput
      h.prefix w sourceRestBits stage

theorem MixedParserStackSourceRestFinishOutputComponentsSpec.gap_output
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishOutputComponentsSpec
        prefixFinish gapFinish joinFinish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    gapFinish.HaltsFromTapeWithOutput
      (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage)
      (assemblySourceRestLiveTailGapTargetOutput
        w sourceRestBits stage) :=
  h.gap.haltsFromTapeWithOutput w sourceRestBits stage

theorem MixedParserStackSourceRestFinishOutputComponentsSpec.join_output
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishOutputComponentsSpec
        prefixFinish gapFinish joinFinish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    joinFinish.HaltsFromTapeWithOutput
      (MixedParserStackWholeSourceAfterRawTailScanTape
        w sourceRestBits stage)
      (assemblySourceRestFinishJoinedOutput
        w sourceRestBits stage) :=
  MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec_haltsFromTapeWithJoinedOutput
    h.join w sourceRestBits stage

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
