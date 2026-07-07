import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInner

set_option doc.verso true

/-!
# Parsed-inner route contracts

This module packages the parsed-inner post-prefix route for padded merge.  The
fixed prefix cleanup and post-prefix gap close phases are already concrete
finite transducers; the branch-parametric field transport remains the finite
machine leaf in
{module}`FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInner`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

private theorem haltsFromTapeWithOutput_of_haltsFromTape_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape h

/-!
## Output-level parsed-inner specs
-/

def SelectedMergePaddedEmitterParsedInnerPrefixCleanupOutputSpec
    (cleaner : MachineDescription) : Prop :=
  cleaner.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      cleaner.HaltsFromTapeWithOutput
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
        (Tape.normalizedOutput
          (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p))

def SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseOutputSpec
    (closer : MachineDescription) : Prop :=
  closer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      closer.HaltsFromTapeWithOutput
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p)
        (Tape.normalizedOutput
          (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p))

def SelectedMergePaddedEmitterParsedInnerPrefixCloserOutputSpec
    (closer : MachineDescription) : Prop :=
  closer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      closer.HaltsFromTapeWithOutput
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
        (Tape.normalizedOutput
          (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p))

def SelectedMergePaddedEmitterParsedInnerPrefixCloserSpec
    (closer : MachineDescription) : Prop :=
  closer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      closer.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)

def SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputSpec
    (useAccept : Bool) (transport : MachineDescription) : Prop :=
  transport.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      transport.HaltsFromTapeWithOutput
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (Tape.normalizedOutput
          (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p))

def SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputSpec
    (useAccept : Bool) (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      emitter.HaltsFromTapeWithOutput
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
        (Tape.normalizedOutput
          (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p))

def SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputConstruction
    (useAccept : Bool) : Prop :=
  exists transport : MachineDescription,
    SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputSpec
      useAccept transport

def SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputConstruction
    (useAccept : Bool) : Prop :=
  exists emitter : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputSpec
      useAccept emitter

theorem SelectedMergePaddedEmitterParsedInnerPrefixCleanupOutputSpec_of_exact
    {cleaner : MachineDescription}
    (hcleaner :
      cleaner.SubroutineReady ∧
        forall p : SelectedMergeEmitterPayload,
          cleaner.HaltsFromTape
            (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
            (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape
              p)) :
    SelectedMergePaddedEmitterParsedInnerPrefixCleanupOutputSpec cleaner := by
  refine ⟨hcleaner.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hcleaner.right p)

theorem SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseOutputSpec_of_exact
    {closer : MachineDescription}
    (hcloser :
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseSpec closer) :
    SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseOutputSpec
      closer := by
  refine ⟨hcloser.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hcloser.right p)

theorem SelectedMergePaddedEmitterParsedInnerPrefixCloserOutputSpec_of_exact
    {closer : MachineDescription}
    (hcloser :
      SelectedMergePaddedEmitterParsedInnerPrefixCloserSpec closer) :
    SelectedMergePaddedEmitterParsedInnerPrefixCloserOutputSpec closer := by
  refine ⟨hcloser.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hcloser.right p)

theorem SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputSpec_of_exact
    {useAccept : Bool} {transport : MachineDescription}
    (htransport :
      SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportSpec
        useAccept transport) :
    SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputSpec
      useAccept transport := by
  refine ⟨htransport.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (htransport.right p)

theorem SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputSpec_of_exact
    {useAccept : Bool} {emitter : MachineDescription}
    (hemitting :
      SelectedMergePaddedEmitterAfterHitPaddedParsedInnerSpec
        useAccept emitter) :
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputSpec
      useAccept emitter := by
  refine ⟨hemitting.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hemitting.right p)

theorem SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputConstruction_of_exact
    {useAccept : Bool}
    (htransport :
      exists transport : MachineDescription,
        SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportSpec
          useAccept transport) :
    SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputConstruction
      useAccept := by
  rcases htransport with ⟨transport, hspec⟩
  exact
    ⟨transport,
      SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputSpec_of_exact
        hspec⟩

theorem SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputConstruction_of_exact
    {useAccept : Bool}
    (hemitting :
      SelectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction
        useAccept) :
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputConstruction
      useAccept := by
  rcases hemitting with ⟨emitter, hspec⟩
  exact
    ⟨emitter,
      SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputSpec_of_exact
        hspec⟩

/-!
## Fixed prefix route
-/

def SelectedMergePaddedEmitterParsedInnerPrefixCloserDescription :
    MachineDescription :=
  CommonGround.FiniteTransducers.canonicalSeqDescription
    SelectedMergePaddedEmitterParsedInnerPrefixCleanupDescription
    SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription

def SelectedMergePaddedEmitterParsedInnerRouteEmitterDescription
    (transport : MachineDescription) : MachineDescription :=
  CommonGround.FiniteTransducers.canonicalSeqDescription
    SelectedMergePaddedEmitterParsedInnerPrefixCloserDescription
    transport

theorem selectedMergePaddedEmitterParsedInnerPrefixCloserSpec :
    SelectedMergePaddedEmitterParsedInnerPrefixCloserSpec
      SelectedMergePaddedEmitterParsedInnerPrefixCloserDescription := by
  constructor
  · exact
      CommonGround.FiniteTransducers.canonicalSeqDescription_subroutineReady
        selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_subroutineReady
        selectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription_subroutineReady
  · intro p
    exact
      CommonGround.FiniteTransducers.canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_subroutineReady
        selectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription_subroutineReady
        (selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_haltsFromParsedTape
          p)
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_move_left_move_right
          p)
        (selectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription_haltsFromTape
          p)

theorem selectedMergePaddedEmitterParsedInnerPrefixCloserOutputSpec :
    SelectedMergePaddedEmitterParsedInnerPrefixCloserOutputSpec
      SelectedMergePaddedEmitterParsedInnerPrefixCloserDescription := by
  exact
    SelectedMergePaddedEmitterParsedInnerPrefixCloserOutputSpec_of_exact
      selectedMergePaddedEmitterParsedInnerPrefixCloserSpec

/-!
## Parsed-inner tape shape
-/

structure SelectedMergePaddedEmitterParsedInnerRouteShape
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) : Prop where
  sourceTapeCellsEqSourceWindow :
    Tape.cells
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceCells p
  sourceCellsFilterMapEqSourceBits :
    (SelectedMergePaddedEmitterParsedInnerSourceCells p).filterMap
        (fun cell => cell) =
      SelectedMergePaddedEmitterParsedInnerSourceBits p
  sourceTailBitsNeNil :
    SelectedMergePaddedEmitterParsedInnerSourceTailBits p ≠ []
  sourceBitsNeNil :
    SelectedMergePaddedEmitterParsedInnerSourceBits p ≠ []
  sourceTailCurrentRestReverse :
    (SelectedMergePaddedEmitterParsedInnerSourceTailCurrent p ::
        SelectedMergePaddedEmitterParsedInnerSourceTailLeftRest p).reverse =
      SelectedMergePaddedEmitterParsedInnerSourceTailBits p
  sourceCellsEqSplit :
    SelectedMergePaddedEmitterParsedInnerSourceCells p =
      SelectedMergePaddedEmitterParsedInnerSourceSplitCells p
  sourceLeftCellsEqGapLeft :
    SelectedMergePaddedEmitterParsedInnerSourceLeftCells p =
      List.append
        ((SelectedMergePaddedEmitterParsedInnerSourceTailBits p).reverse.map
          some)
        (none :: SelectedMergePaddedEmitterParsedInnerGapBaseLeft)
  sourceBitsEqMarkedPrefixFieldTail :
    SelectedMergePaddedEmitterParsedInnerSourceBits p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerMarkedPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits p)
  sourceTailBitsEqMarkedBodyOuterSuffix :
    SelectedMergePaddedEmitterParsedInnerSourceTailBits p =
      List.append
        CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
            p.L.input
            (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              p.L.stage))
          (SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits p))
  sourceBitsEqRemainderDeleteSplit :
    SelectedMergePaddedEmitterParsedInnerSourceBits p =
      List.append
        SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits
        (List.append
          SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits
          (SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits p))
  targetFieldTailExpandedEqTargetFieldTail :
    SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits
        useAccept p =
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
        useAccept p
  postPrefixTargetBitsEqDecoded :
    SelectedMergePaddedEmitterDecodedHandoffBits useAccept p =
      SelectedMergePaddedEmitterParsedInnerPostPrefixTargetBits
        useAccept p
  decodedHandoffBitsEqOutputPrefixFieldTail :
    SelectedMergePaddedEmitterDecodedHandoffBits useAccept p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
          useAccept p)
  decodedHandoffBitsEqOutputPrefixExpandedTarget :
    SelectedMergePaddedEmitterDecodedHandoffBits useAccept p =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits
          useAccept p)
  targetTailBitsEqOutputPrefixTail :
    SelectedMergePaddedEmitterParsedInnerTargetTailBits useAccept p =
      List.append
        (CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits
          p.L.input
          (FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.L.stage))
        (SelectedMergePaddedEmitterParsedInnerTargetFieldTailBits
          useAccept p)
  decodedHandoffTapeEqOutputTape :
    SelectedMergePaddedEmitterDecodedHandoffTape useAccept p =
      SelectedMergeEquivEmitterPaddedOutputTape useAccept p
  decodedHandoffTapeNormalizedOutputEqBits :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p) =
      SelectedMergePaddedEmitterDecodedHandoffBits useAccept p
  decodedHandoffTapeCellsEqBits :
    Tape.cells (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p) =
      List.append
        ((SelectedMergePaddedEmitterDecodedHandoffBits useAccept p).map some)
        (List.replicate (SimulatorLayout.asBoolInput p.S).length none)
  decodedHandoffTapeCellsEqTargetWindow :
    Tape.cells (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p) =
      SelectedMergePaddedEmitterParsedInnerTargetCells useAccept p
  decodedHandoffTapeCellsEqSplit :
    Tape.cells (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p) =
      SelectedMergePaddedEmitterParsedInnerTargetSplitCells useAccept p
  targetCellsFilterMapEqBits :
    (SelectedMergePaddedEmitterParsedInnerTargetCells useAccept p).filterMap
        (fun cell => cell) =
      SelectedMergePaddedEmitterDecodedHandoffBits useAccept p
  targetCellsEqSplit :
    SelectedMergePaddedEmitterParsedInnerTargetCells useAccept p =
      SelectedMergePaddedEmitterParsedInnerTargetSplitCells useAccept p
  parsedTapeCellsEqSplit :
    Tape.cells
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceSplitCells p
  gapCompactorSourceTapeCellsEqSplit :
    Tape.cells
        (SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceSplitCells p
  parsedTapeCellsEqGapCompactorSource :
    Tape.cells
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p) =
      Tape.cells (SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape
        p)
  parsedTapeEqGapCompactorSource :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p =
      SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape p
  gapCompactorTargetTapeNormalizedOutput :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceBits p
  gapCompactorHalts :
    CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape p)
      (SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape p)
  gapCompactorTargetMoveLeftMoveLeftEqRewindSource :
    Tape.move Direction.left
        (Tape.move Direction.left
          (SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape p)) =
      SelectedMergePaddedEmitterParsedInnerPostGapRewindSourceTape p
  postGapRewindTargetEqDeleteSource :
    CommonGround.FiniteTransducers.rightEdgeRewindTargetTapeWithBase
        []
        (SelectedMergePaddedEmitterParsedInnerSourceBits p)
        [none, none] =
      SelectedMergePaddedEmitterParsedInnerDeleteSourceTape p
  rightEdgeRewindHaltsFromPostGap :
    CommonGround.FiniteTransducers.rightEdgeRewindDescription.HaltsFromTape
      (Tape.move Direction.left
        (Tape.move Direction.left
          (SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape p)))
      (SelectedMergePaddedEmitterParsedInnerDeleteSourceTape p)
  gapThenLeftHalts :
    SelectedMergePaddedEmitterParsedInnerGapThenLeftDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape p)
      (SelectedMergePaddedEmitterParsedInnerPostGapRewindSourceTape p)
  postGapRewindMoveLeftMoveRight :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterParsedInnerPostGapRewindSourceTape p)) =
      SelectedMergePaddedEmitterParsedInnerPostGapRewindSourceTape p
  rightEdgeRewindHaltsFromRewindSource :
    CommonGround.FiniteTransducers.rightEdgeRewindDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerPostGapRewindSourceTape p)
      (SelectedMergePaddedEmitterParsedInnerDeleteSourceTape p)
  prefixRewindHalts :
    SelectedMergePaddedEmitterParsedInnerPrefixRewindDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape p)
      (SelectedMergePaddedEmitterParsedInnerDeleteSourceTape p)
  deleteSourceMoveLeftMoveRight :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterParsedInnerDeleteSourceTape p)) =
      SelectedMergePaddedEmitterParsedInnerDeleteSourceTape p
  remainderDeleteHalts :
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerDeleteSourceTape p)
      (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p)
  prefixCleanupHaltsFromTape :
    SelectedMergePaddedEmitterParsedInnerPrefixCleanupDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape p)
      (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p)
  prefixCleanupHaltsFromParsedTape :
    SelectedMergePaddedEmitterParsedInnerPrefixCleanupDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
      (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p)
  remainderDeleteTargetMoveLeftMoveRight :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p)) =
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p
  remainderDeleteTargetEqPostPrefixGapCloseSource :
    SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p =
      CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (CommonGround.FiniteTransducers.rightBlankLocalGapBaseLeft 2
          (some true ::
            SelectedMergePaddedEmitterParsedInnerPostPrefixGapBaseTail))
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixCurrent
          p)
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixLeftRest
          p)
        1
        [none]
  remainderDeleteTargetCells :
    Tape.cells
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) =
      List.append
        [none]
        (List.append
          (SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits.map
            some)
          (List.append
            (List.replicate
              SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits.length
              (none : Option Bool))
            (List.append
              ((SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits
                p).map some)
              [none, none, none])))
  remainderDeleteTargetNormalizedOutputSplit :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) =
      List.append
        SelectedMergePaddedEmitterParsedInnerRemainderDeletePrefixBits
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits p)
  remainderDeleteTargetNormalizedOutput :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerSourceFieldTailBits p)
  remainderDeleteTargetNormalizedOutputExpandedSource :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) =
      List.append
        (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
        (SelectedMergePaddedEmitterParsedInnerSourceFieldTailExpandedBits p)
  remainderDeleteTargetNormalizedOutputPostPrefixSource :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) =
      SelectedMergePaddedEmitterParsedInnerPostPrefixSourceBits p
  postPrefixGapClosedTapeCells :
    Tape.cells
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p) =
      CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetCellsWithPadding
        [none]
        (SelectedMergePaddedEmitterParsedInnerPostPrefixSourceBits p)
        (List.replicate
          (SelectedMergePaddedEmitterParsedInnerRemainderDeleteBits.length + 1)
          (none : Option Bool))
  postPrefixGapClosedTapeNormalizedOutput :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p) =
      SelectedMergePaddedEmitterParsedInnerPostPrefixSourceBits p
  postPrefixGapClosedTapeMoveLeftMoveRight :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)) =
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p
  postPrefixGapClosedTapeEqGapCloseTarget :
    SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p =
      CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding
        (some true ::
          SelectedMergePaddedEmitterParsedInnerPostPrefixGapBaseTail)
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteSuffixBits p)
        (CommonGround.FiniteTransducers.sentinelGapCompactorFinalPadding
          2 1 [none])
  postPrefixGapCloseHalts :
    SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription.HaltsFromTape
      (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p)
      (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)

theorem selectedMergePaddedEmitterParsedInnerRouteShape
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerRouteShape useAccept p :=
  { sourceTapeCellsEqSourceWindow :=
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_cells_eq_sourceWindow
        p
    sourceCellsFilterMapEqSourceBits :=
      SelectedMergePaddedEmitterParsedInnerSourceCells_filterMap_eq_sourceBits
        p
    sourceTailBitsNeNil :=
      SelectedMergePaddedEmitterParsedInnerSourceTailBits_ne_nil p
    sourceBitsNeNil :=
      SelectedMergePaddedEmitterParsedInnerSourceBits_ne_nil p
    sourceTailCurrentRestReverse :=
      SelectedMergePaddedEmitterParsedInnerSourceTailCurrentRest_reverse p
    sourceCellsEqSplit :=
      SelectedMergePaddedEmitterParsedInnerSourceCells_eq_split p
    sourceLeftCellsEqGapLeft :=
      SelectedMergePaddedEmitterParsedInnerSourceLeftCells_eq_gapLeft p
    sourceBitsEqMarkedPrefixFieldTail :=
      SelectedMergePaddedEmitterParsedInnerSourceBits_eq_markedPrefix_fieldTail
        p
    sourceTailBitsEqMarkedBodyOuterSuffix :=
      SelectedMergePaddedEmitterParsedInnerSourceTailBits_eq_markedBody_outerSuffix
        p
    sourceBitsEqRemainderDeleteSplit :=
      SelectedMergePaddedEmitterParsedInnerSourceBits_eq_remainderDeleteSplit
        p
    targetFieldTailExpandedEqTargetFieldTail :=
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits_eq_targetFieldTailBits
        useAccept p
    postPrefixTargetBitsEqDecoded :=
      SelectedMergePaddedEmitterDecodedHandoffBits_eq_postPrefixTargetBits
        useAccept p
    decodedHandoffBitsEqOutputPrefixFieldTail :=
      SelectedMergePaddedEmitterDecodedHandoffBits_eq_outputPrefix_fieldTail
        useAccept p
    decodedHandoffBitsEqOutputPrefixExpandedTarget :=
      SelectedMergePaddedEmitterDecodedHandoffBits_eq_outputPrefix_expandedTarget
        useAccept p
    targetTailBitsEqOutputPrefixTail :=
      SelectedMergePaddedEmitterParsedInnerTargetTailBits_eq_outputPrefixTail
        useAccept p
    decodedHandoffTapeEqOutputTape :=
      SelectedMergePaddedEmitterDecodedHandoffTape_eq_outputTape useAccept p
    decodedHandoffTapeNormalizedOutputEqBits :=
      SelectedMergePaddedEmitterDecodedHandoffTape_normalizedOutput_eq_bits
        useAccept p
    decodedHandoffTapeCellsEqBits :=
      SelectedMergePaddedEmitterDecodedHandoffTape_cells_eq_bits useAccept p
    decodedHandoffTapeCellsEqTargetWindow :=
      SelectedMergePaddedEmitterDecodedHandoffTape_cells_eq_targetWindow
        useAccept p
    decodedHandoffTapeCellsEqSplit :=
      SelectedMergePaddedEmitterDecodedHandoffTape_cells_eq_split
        useAccept p
    targetCellsFilterMapEqBits :=
      SelectedMergePaddedEmitterParsedInnerTargetCells_filterMap_eq_bits
        useAccept p
    targetCellsEqSplit :=
      SelectedMergePaddedEmitterParsedInnerTargetCells_eq_split useAccept p
    parsedTapeCellsEqSplit :=
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_cells_eq_split
        p
    gapCompactorSourceTapeCellsEqSplit :=
      SelectedMergePaddedEmitterParsedInnerGapCompactorSourceTape_cells_eq_split
        p
    parsedTapeCellsEqGapCompactorSource :=
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_cells_eq_gapCompactorSource
        p
    parsedTapeEqGapCompactorSource :=
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_eq_gapCompactorSource
        p
    gapCompactorTargetTapeNormalizedOutput :=
      SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape_normalizedOutput
        p
    gapCompactorHalts :=
      selectedMergePaddedEmitterParsedInnerGapCompactorDescription_haltsFromTape
        p
    gapCompactorTargetMoveLeftMoveLeftEqRewindSource :=
      SelectedMergePaddedEmitterParsedInnerGapCompactorTargetTape_moveLeft_moveLeft_eq_rewindSource
        p
    postGapRewindTargetEqDeleteSource :=
      SelectedMergePaddedEmitterParsedInnerPostGapRewindTargetTape_eq_deleteSourceTape
        p
    rightEdgeRewindHaltsFromPostGap :=
      selectedMergePaddedEmitterParsedInnerRightEdgeRewindDescription_haltsFromPostGap
        p
    gapThenLeftHalts :=
      selectedMergePaddedEmitterParsedInnerGapThenLeftDescription_haltsFromTape
        p
    postGapRewindMoveLeftMoveRight :=
      SelectedMergePaddedEmitterParsedInnerPostGapRewindSourceTape_move_left_move_right
        p
    rightEdgeRewindHaltsFromRewindSource :=
      selectedMergePaddedEmitterParsedInnerRightEdgeRewindDescription_haltsFromRewindSource
        p
    prefixRewindHalts :=
      selectedMergePaddedEmitterParsedInnerPrefixRewindDescription_haltsFromTape
        p
    deleteSourceMoveLeftMoveRight :=
      SelectedMergePaddedEmitterParsedInnerDeleteSourceTape_move_left_move_right
        p
    remainderDeleteHalts :=
      selectedMergePaddedEmitterParsedInnerRemainderDeleteDescription_haltsFromDeleteSource
        p
    prefixCleanupHaltsFromTape :=
      selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_haltsFromTape
        p
    prefixCleanupHaltsFromParsedTape :=
      selectedMergePaddedEmitterParsedInnerPrefixCleanupDescription_haltsFromParsedTape
        p
    remainderDeleteTargetMoveLeftMoveRight :=
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_move_left_move_right
        p
    remainderDeleteTargetEqPostPrefixGapCloseSource :=
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_eq_postPrefixGapCloseSource
        p
    remainderDeleteTargetCells :=
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_cells p
    remainderDeleteTargetNormalizedOutputSplit :=
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_normalizedOutput_split
        p
    remainderDeleteTargetNormalizedOutput :=
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_normalizedOutput
        p
    remainderDeleteTargetNormalizedOutputExpandedSource :=
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_normalizedOutput_expandedSource
        p
    remainderDeleteTargetNormalizedOutputPostPrefixSource :=
      SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape_normalizedOutput_postPrefixSource
        p
    postPrefixGapClosedTapeCells :=
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape_cells p
    postPrefixGapClosedTapeNormalizedOutput :=
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape_normalizedOutput
        p
    postPrefixGapClosedTapeMoveLeftMoveRight :=
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape_move_left_move_right
        p
    postPrefixGapClosedTapeEqGapCloseTarget :=
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape_eq_postPrefixGapCloseTarget
        p
    postPrefixGapCloseHalts :=
      selectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription_haltsFromTape
        p }

/-!
## Exact and output parsed-inner routes
-/

structure SelectedMergePaddedEmitterParsedInnerRouteSpec
    (useAccept : Bool) (transport : MachineDescription) : Prop where
  prefixCloser :
    SelectedMergePaddedEmitterParsedInnerPrefixCloserSpec
      SelectedMergePaddedEmitterParsedInnerPrefixCloserDescription
  gapClose :
    SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseSpec
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription
  transportExact :
    SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportSpec
      useAccept transport
  prefixCloserOutput :
    SelectedMergePaddedEmitterParsedInnerPrefixCloserOutputSpec
      SelectedMergePaddedEmitterParsedInnerPrefixCloserDescription
  gapCloseOutput :
    SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseOutputSpec
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription
  transportOutput :
    SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputSpec
      useAccept transport
  emitterExact :
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerSpec
      useAccept
      (SelectedMergePaddedEmitterParsedInnerRouteEmitterDescription
        transport)
  emitterOutput :
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputSpec
      useAccept
      (SelectedMergePaddedEmitterParsedInnerRouteEmitterDescription
        transport)
  shape :
    forall p : SelectedMergeEmitterPayload,
      SelectedMergePaddedEmitterParsedInnerRouteShape useAccept p

def SelectedMergePaddedEmitterParsedInnerRouteConstruction
    (useAccept : Bool) : Prop :=
  exists transport : MachineDescription,
    SelectedMergePaddedEmitterParsedInnerRouteSpec useAccept transport

structure SelectedMergePaddedEmitterParsedInnerOutputRouteSpec
    (useAccept : Bool) (transport : MachineDescription) : Prop where
  prefixCloserOutput :
    SelectedMergePaddedEmitterParsedInnerPrefixCloserOutputSpec
      SelectedMergePaddedEmitterParsedInnerPrefixCloserDescription
  gapCloseOutput :
    SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseOutputSpec
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription
  transportOutput :
    SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputSpec
      useAccept transport
  emitterOutput :
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputSpec
      useAccept
      (SelectedMergePaddedEmitterParsedInnerRouteEmitterDescription
        transport)
  shape :
    forall p : SelectedMergeEmitterPayload,
      SelectedMergePaddedEmitterParsedInnerRouteShape useAccept p

def SelectedMergePaddedEmitterParsedInnerOutputRouteConstruction
    (useAccept : Bool) : Prop :=
  exists transport : MachineDescription,
    SelectedMergePaddedEmitterParsedInnerOutputRouteSpec useAccept transport

theorem selectedMergePaddedEmitterParsedInnerRouteSpec_of_transport
    {useAccept : Bool} {transport : MachineDescription}
    (htransport :
      SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportSpec
        useAccept transport) :
    SelectedMergePaddedEmitterParsedInnerRouteSpec useAccept transport := by
  have hprefix :
      SelectedMergePaddedEmitterParsedInnerPrefixCloserSpec
        SelectedMergePaddedEmitterParsedInnerPrefixCloserDescription :=
    selectedMergePaddedEmitterParsedInnerPrefixCloserSpec
  have hgap :
      SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseSpec
        SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseDescription :=
    selectedMergePaddedEmitterParsedInnerPostPrefixGapCloseSpec
  have hemitting :
      SelectedMergePaddedEmitterAfterHitPaddedParsedInnerSpec
        useAccept
        (SelectedMergePaddedEmitterParsedInnerRouteEmitterDescription
          transport) := by
    constructor
    · exact
        CommonGround.FiniteTransducers.canonicalSeqDescription_subroutineReady
          hprefix.left
          htransport.left
    · intro p
      exact
        CommonGround.FiniteTransducers.canonicalSeqDescription_haltsFromTape_of_haltsFromTape
          hprefix.left
          htransport.left
          (hprefix.right p)
          (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape_move_left_move_right
            p)
          (htransport.right p)
  exact
    { prefixCloser := hprefix
      gapClose := hgap
      transportExact := htransport
      prefixCloserOutput :=
        selectedMergePaddedEmitterParsedInnerPrefixCloserOutputSpec
      gapCloseOutput :=
        SelectedMergePaddedEmitterParsedInnerPostPrefixGapCloseOutputSpec_of_exact
          hgap
      transportOutput :=
        SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportOutputSpec_of_exact
          htransport
      emitterExact := hemitting
      emitterOutput :=
        SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputSpec_of_exact
          hemitting
      shape := selectedMergePaddedEmitterParsedInnerRouteShape useAccept }

theorem selectedMergePaddedEmitterParsedInnerRouteConstruction_of_transport
    {useAccept : Bool}
    (htransport :
      exists transport : MachineDescription,
        SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportSpec
          useAccept transport) :
    SelectedMergePaddedEmitterParsedInnerRouteConstruction useAccept := by
  rcases htransport with ⟨transport, hspec⟩
  exact
    ⟨transport,
      selectedMergePaddedEmitterParsedInnerRouteSpec_of_transport hspec⟩

theorem selectedMergePaddedEmitterParsedInnerRouteConstruction_core
    (useAccept : Bool) :
    SelectedMergePaddedEmitterParsedInnerRouteConstruction useAccept :=
  selectedMergePaddedEmitterParsedInnerRouteConstruction_of_transport
    (selectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportConstruction
      useAccept)

theorem selectedMergePaddedEmitterParsedInnerOutputRouteSpec_of_exact
    {useAccept : Bool} {transport : MachineDescription}
    (hroute :
      SelectedMergePaddedEmitterParsedInnerRouteSpec useAccept transport) :
    SelectedMergePaddedEmitterParsedInnerOutputRouteSpec
      useAccept transport :=
  { prefixCloserOutput := hroute.prefixCloserOutput
    gapCloseOutput := hroute.gapCloseOutput
    transportOutput := hroute.transportOutput
    emitterOutput := hroute.emitterOutput
    shape := hroute.shape }

theorem selectedMergePaddedEmitterParsedInnerOutputRouteConstruction_of_exact
    {useAccept : Bool}
    (hroute :
      SelectedMergePaddedEmitterParsedInnerRouteConstruction useAccept) :
    SelectedMergePaddedEmitterParsedInnerOutputRouteConstruction
      useAccept := by
  rcases hroute with ⟨transport, hspec⟩
  exact
    ⟨transport,
      selectedMergePaddedEmitterParsedInnerOutputRouteSpec_of_exact hspec⟩

theorem selectedMergePaddedEmitterParsedInnerOutputRouteConstruction_core
    (useAccept : Bool) :
    SelectedMergePaddedEmitterParsedInnerOutputRouteConstruction
      useAccept :=
  selectedMergePaddedEmitterParsedInnerOutputRouteConstruction_of_exact
    (selectedMergePaddedEmitterParsedInnerRouteConstruction_core useAccept)

theorem selectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction_of_route
    {useAccept : Bool}
    (hroute :
      SelectedMergePaddedEmitterParsedInnerRouteConstruction useAccept) :
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerConstruction
      useAccept := by
  rcases hroute with ⟨transport, hspec⟩
  exact
    ⟨SelectedMergePaddedEmitterParsedInnerRouteEmitterDescription
        transport,
      hspec.emitterExact⟩

theorem selectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputConstruction_of_route
    {useAccept : Bool}
    (hroute :
      SelectedMergePaddedEmitterParsedInnerOutputRouteConstruction
        useAccept) :
    SelectedMergePaddedEmitterAfterHitPaddedParsedInnerOutputConstruction
      useAccept := by
  rcases hroute with ⟨transport, hspec⟩
  exact
    ⟨SelectedMergePaddedEmitterParsedInnerRouteEmitterDescription
        transport,
      hspec.emitterOutput⟩

/-!
## Field projections
-/

theorem selectedMergePaddedEmitterParsedInnerRouteShape_of_route
    {useAccept : Bool}
    (hroute :
      SelectedMergePaddedEmitterParsedInnerRouteConstruction useAccept)
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerRouteShape useAccept p := by
  rcases hroute with ⟨_transport, hspec⟩
  exact hspec.shape p

theorem selectedMergePaddedEmitterParsedInnerRouteShape_of_outputRoute
    {useAccept : Bool}
    (hroute :
      SelectedMergePaddedEmitterParsedInnerOutputRouteConstruction
        useAccept)
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerRouteShape useAccept p := by
  rcases hroute with ⟨_transport, hspec⟩
  exact hspec.shape p

theorem selectedMergePaddedEmitterParsedInnerPostPrefixTargetBits_core
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterDecodedHandoffBits useAccept p =
      SelectedMergePaddedEmitterParsedInnerPostPrefixTargetBits
        useAccept p :=
  (selectedMergePaddedEmitterParsedInnerRouteShape_of_route
    (selectedMergePaddedEmitterParsedInnerRouteConstruction_core useAccept)
    p)
      |>.postPrefixTargetBitsEqDecoded

theorem selectedMergePaddedEmitterParsedInnerPostPrefixGapClosed_normalizedOutput_core
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p) =
      SelectedMergePaddedEmitterParsedInnerPostPrefixSourceBits p :=
  (selectedMergePaddedEmitterParsedInnerRouteShape_of_route
    (selectedMergePaddedEmitterParsedInnerRouteConstruction_core useAccept)
    p)
      |>.postPrefixGapClosedTapeNormalizedOutput

theorem selectedMergePaddedEmitterParsedInnerDecodedHandoff_cells_split_core
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterDecodedHandoffTape useAccept p) =
      SelectedMergePaddedEmitterParsedInnerTargetSplitCells useAccept p :=
  (selectedMergePaddedEmitterParsedInnerRouteShape_of_route
    (selectedMergePaddedEmitterParsedInnerRouteConstruction_core useAccept)
    p)
      |>.decodedHandoffTapeCellsEqSplit

theorem selectedMergePaddedEmitterParsedInnerRemainderDeleteTarget_normalizedOutput_core
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) =
      SelectedMergePaddedEmitterParsedInnerPostPrefixSourceBits p :=
  (selectedMergePaddedEmitterParsedInnerRouteShape_of_route
    (selectedMergePaddedEmitterParsedInnerRouteConstruction_core useAccept)
    p)
      |>.remainderDeleteTargetNormalizedOutputPostPrefixSource

theorem selectedMergePaddedEmitterParsedInnerPrefixCleanup_halts_core
    (useAccept : Bool) (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterParsedInnerPrefixCleanupDescription.HaltsFromTape
      (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)
      (SelectedMergePaddedEmitterParsedInnerRemainderDeleteTargetTape p) :=
  (selectedMergePaddedEmitterParsedInnerRouteShape_of_route
    (selectedMergePaddedEmitterParsedInnerRouteConstruction_core useAccept)
    p)
      |>.prefixCleanupHaltsFromParsedTape

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
