import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorBoundaryGapCreator
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorPipelines

set_option doc.verso true

/-!
# Structured refresh composition

This module contains the proof-side bridge from a one-segment head refresh to
the three-segment structured singleton refresh target.  The remaining machine
work is to build concrete selected-segment refreshers for interior segments;
the theorem here records exactly the contracts those machines must satisfy.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

theorem encodedStructuredTapes_cons_eq_cons_of_singleton_eq
    {actual expected : Tape Bool} {rest : List (Tape Bool)}
    (h :
      encodedStructuredTapes [actual] =
        encodedStructuredTapes [expected]) :
    encodedStructuredTapes (actual :: rest) =
      encodedStructuredTapes (expected :: rest) := by
  unfold encodedStructuredTapes at h
  simp [encodedStructuredTapeCells] at h
  injection h with _ _ hcode
  simp at hcode
  simp [encodedStructuredTapes, encodedStructuredTapeCells, hcode]

theorem encodedStructuredTapes_cons_eq_guarded_cons_of_singleton_eq
    {actual target : Tape Bool} {rest : List (Tape Bool)}
    (h :
      encodedStructuredTapes [actual] =
        encodedGuardedStructuredTapes [target]) :
    encodedStructuredTapes (actual :: rest) =
      encodedStructuredTapes (guardLogicalTape target :: rest) :=
  encodedStructuredTapes_cons_eq_cons_of_singleton_eq
    (by simpa [encodedGuardedStructuredTapes, guardLogicalTapes] using h)

namespace SingletonHeadGuardSlackRefreshCaseContract

theorem toContract
    {refresh : MachineDescription}
    (hrefresh : SingletonHeadGuardSlackRefreshCaseContract refresh) :
    SingletonHeadGuardSlackRefreshContract refresh where
  subroutineReady := hrefresh.subroutineReady
  realizes := by
    intro target actual rest hshape
    suffices hrealizes :
        forall {physical : Tape Bool},
          SingletonGuardSlackEndpointShape [target] physical ->
          encodedStructuredTapes [actual] = physical ->
          refresh.HaltsFromTapeEquiv
            (encodedStructuredTapes (actual :: rest))
            (encodedStructuredTapes
              (guardLogicalTape target :: rest)) by
      exact hrealizes hshape rfl
    intro physical hshape hactualPhysical
    cases hshape with
    | canonical htargetPhysical =>
        have hsource :
            encodedStructuredTapes (actual :: rest) =
              encodedStructuredTapes
                (guardLogicalTape target :: rest) :=
          encodedStructuredTapes_cons_eq_guarded_cons_of_singleton_eq
            (by rw [hactualPhysical, htargetPhysical])
        rw [hsource]
        exact hrefresh.canonical target rest
    | leftBoundary head right =>
        have hsource :
            encodedStructuredTapes (actual :: rest) =
              encodedStructuredTapes
                (({ left := [], head := head, right := right ++ [none] } :
                  Tape Bool) :: rest) :=
          encodedStructuredTapes_cons_eq_cons_of_singleton_eq
            hactualPhysical
        rw [hsource]
        exact hrefresh.leftBoundary head right rest
    | rightBoundary left head =>
        have hsource :
            encodedStructuredTapes (actual :: rest) =
              encodedStructuredTapes
                (({ left := left ++ [none], head := head, right := [] } :
                  Tape Bool) :: rest) :=
          encodedStructuredTapes_cons_eq_cons_of_singleton_eq
            hactualPhysical
        rw [hsource]
        exact hrefresh.rightBoundary left head rest

end SingletonHeadGuardSlackRefreshCaseContract

/--
Contract for refreshing one selected segment of a structured singleton
endpoint.

The contract is stated over the exact segment list rather than over an
existential physical shape.  That keeps later three-segment composition
syntactic: after segment 0 is refreshed, segment 1 runs on the literal
{lit}`replaceTapeAt 0 ... actual` list, and so on.
-/
structure StructuredSegmentGuardSlackRefreshContract
    (refresh : MachineDescription) (tapeIndex : Nat) : Prop where
  subroutineReady : refresh.SubroutineReady
  realizes :
    forall {target actual : List (Tape Bool)}
      {targetTape : Tape Bool} {targetRest : List (Tape Bool)},
      SingletonGuardSlackEndpointShapeList target actual ->
      target.drop tapeIndex = targetTape :: targetRest ->
      refresh.HaltsFromTapeEquiv
        (encodedStructuredTapes actual)
        (encodedStructuredTapes
          (replaceTapeAt tapeIndex (guardLogicalTape targetTape) actual))

namespace StructuredSegmentGuardSlackRefreshContract

theorem ofHead
    {refresh : MachineDescription}
    (hrefresh : SingletonHeadGuardSlackRefreshContract refresh) :
    StructuredSegmentGuardSlackRefreshContract refresh 0 where
  subroutineReady := hrefresh.subroutineReady
  realizes := by
    intro target actual targetTape targetRest hlist hdrop
    cases target with
    | nil =>
        simp at hdrop
    | cons targetHead targetTail =>
        simp at hdrop
        rcases hdrop with ⟨rfl, rfl⟩
        cases actual with
        | nil =>
            simp [SingletonGuardSlackEndpointShapeList] at hlist
        | cons actualHead actualTail =>
            simp [SingletonGuardSlackEndpointShapeList] at hlist
            exact hrefresh.realizes hlist.left

end StructuredSegmentGuardSlackRefreshContract

theorem concreteSingletonHeadRefreshDescription_contract :
    SingletonHeadGuardSlackRefreshContract
      concreteSingletonHeadRefreshDescription :=
  concreteSingletonHeadRefreshDescription_caseContract.toContract

theorem concreteSingletonHeadRefreshDescription_segment0Contract :
    StructuredSegmentGuardSlackRefreshContract
      concreteSingletonHeadRefreshDescription 0 :=
  StructuredSegmentGuardSlackRefreshContract.ofHead
    concreteSingletonHeadRefreshDescription_contract

/--
Contract for a local selected-separator refresh routine.

The machine starts with the physical head on the selected segment separator
inside the full structured encoding and halts on the corresponding separator
for the list where that segment has been re-guarded.
-/
structure SelectedSeparatorGuardSlackRefreshContract
    (refresh : MachineDescription) (tapeIndex : Nat) : Prop where
  subroutineReady : refresh.SubroutineReady
  realizes :
    forall {target actual : List (Tape Bool)}
      {targetTape : Tape Bool} {targetRest : List (Tape Bool)},
      SingletonGuardSlackEndpointShapeList target actual ->
      target.drop tapeIndex = targetTape :: targetRest ->
      refresh.HaltsFromTapeEquiv
        (tapeAtEncodedSplit
          (encodedPrefixBeforeTape actual tapeIndex)
          (encodedSuffixFromTape actual tapeIndex))
        (tapeAtEncodedSplit
          (encodedPrefixBeforeTape
            (replaceTapeAt tapeIndex (guardLogicalTape targetTape) actual)
            tapeIndex)
          (encodedSuffixFromTape
            (replaceTapeAt tapeIndex (guardLogicalTape targetTape) actual)
            tapeIndex))

theorem atTapeSeparator_zero_eq_encodedStructuredTapes
    (logical : List (Tape Bool)) {physical : Tape Bool}
    (h : AtTapeSeparator logical 0 physical) :
    physical = encodedStructuredTapes logical := by
  rcases h with ⟨_hle, hphysical⟩
  simpa [encodedStructuredTapes, tapeAtEncodedSplit,
    encodedPrefixBeforeTape, encodedSuffixFromTape] using hphysical

/--
Seek to segment 1, run a local selected-separator refresh there, and return to
the block-start separator.
-/
def structuredSegment1RefreshDescription
    (localRefresh : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription seekTape1Description localRefresh)
    returnFromTape1SeparatorToBlockStartDescription

theorem structuredSegment1RefreshDescription_contract
    {localRefresh : MachineDescription}
    (hlocal : SelectedSeparatorGuardSlackRefreshContract localRefresh 1) :
    StructuredSegmentGuardSlackRefreshContract
      (structuredSegment1RefreshDescription localRefresh) 1 where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      (canonicalPrimitiveSeqDescription_subroutineReady
        seekTape1Description_contract.subroutineReady
        hlocal.subroutineReady)
      returnFromTape1SeparatorToBlockStartDescription_contract.subroutineReady
  realizes := by
    intro target actual targetTape targetRest hlist hdrop
    rcases singletonGuardSlackEndpointShapeList_drop_eq_cons
        hlist hdrop with
      ⟨_actualTape, _actualRest, hactualDrop, _hsegment, _hrest⟩
    cases actual with
    | nil =>
        simp at hactualDrop
    | cons actual0 actualTail =>
        cases actualTail with
        | nil =>
            simp at hactualDrop
        | cons actual1 actualTailRest =>
            simp at hactualDrop
            cases hactualDrop
            let modified : List (Tape Bool) :=
              replaceTapeAt 1 (guardLogicalTape targetTape)
                (actual0 :: actual1 :: actualTailRest)
            let selectedSeparator : Tape Bool :=
              tapeAtEncodedSplit
                (encodedPrefixBeforeTape
                  (actual0 :: actual1 :: actualTailRest) 1)
                (encodedSuffixFromTape
                  (actual0 :: actual1 :: actualTailRest) 1)
            let modifiedSeparator : Tape Bool :=
              tapeAtEncodedSplit
                (encodedPrefixBeforeTape modified 1)
                (encodedSuffixFromTape modified 1)
            have hstart :
                AtExistingTapeSeparator
                  (actual0 :: actual1 :: actualTailRest) 0
                  (encodedStructuredTapes
                    (actual0 :: actual1 :: actualTailRest)) := by
              exact
                ⟨atTapeSeparator_zero_self
                    (actual0 :: actual1 :: actualTailRest),
                  ⟨actual0, actual1 :: actualTailRest, rfl⟩⟩
            rcases seekTape1Description_contract.realizes
                (actual0 :: actual1 :: actualTailRest)
                (encodedStructuredTapes
                  (actual0 :: actual1 :: actualTailRest)) hstart with
              ⟨seekOut, hseek, hseekSep⟩
            have hseekEquiv :
                seekTape1Description.HaltsFromTapeEquiv
                  (encodedStructuredTapes
                    (actual0 :: actual1 :: actualTailRest))
                  selectedSeparator := by
              refine ⟨seekOut, hseek, ?_⟩
              rcases hseekSep with ⟨_hle, hseekOut⟩
              rw [hseekOut]
              exact Tape.Equiv.refl _
            have hlocalRun :
                localRefresh.HaltsFromTapeEquiv selectedSeparator
                  modifiedSeparator := by
              simpa [selectedSeparator, modified] using
                hlocal.realizes
                  (target := target)
                  (actual := actual0 :: actual1 :: actualTailRest)
                  (targetTape := targetTape)
                  (targetRest := targetRest)
                  hlist hdrop
            have hfirst :=
              canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
                seekTape1Description_contract.subroutineReady
                hlocal.subroutineReady hseekEquiv hlocalRun
            have hmodifiedSep :
                AtTapeSeparator modified 1 modifiedSeparator := by
              subst modified
              subst modifiedSeparator
              constructor
              · simp
              · rfl
            rcases
                returnFromTape1SeparatorToBlockStartDescription_contract.realizes
                  modified modifiedSeparator hmodifiedSep with
              ⟨returnOut, hreturn, hreturnSep⟩
            have hreturnEquiv :
                returnFromTape1SeparatorToBlockStartDescription.HaltsFromTapeEquiv
                  modifiedSeparator
                  (encodedStructuredTapes modified) := by
              refine ⟨returnOut, hreturn, ?_⟩
              have hout :=
                atTapeSeparator_zero_eq_encodedStructuredTapes
                  modified hreturnSep
              rw [hout]
              exact Tape.Equiv.refl _
            have hwhole :=
              canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
                (canonicalPrimitiveSeqDescription_subroutineReady
                  seekTape1Description_contract.subroutineReady
                  hlocal.subroutineReady)
                returnFromTape1SeparatorToBlockStartDescription_contract.subroutineReady
                hfirst hreturnEquiv
            simpa [structuredSegment1RefreshDescription, modified] using
              hwhole

/--
Seek to segment 2, run a local selected-separator refresh there, return to the
segment-1 separator, and then return to the block-start separator.
-/
def structuredSegment2RefreshDescription
    (localRefresh : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (canonicalPrimitiveSeqDescription seekTape2Description localRefresh)
      returnFromNextSeparatorToCurrentSeparatorDescription)
    returnFromTape1SeparatorToBlockStartDescription

theorem structuredSegment2RefreshDescription_contract
    {localRefresh : MachineDescription}
    (hlocal : SelectedSeparatorGuardSlackRefreshContract localRefresh 2) :
    StructuredSegmentGuardSlackRefreshContract
      (structuredSegment2RefreshDescription localRefresh) 2 where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      (canonicalPrimitiveSeqDescription_subroutineReady
        (canonicalPrimitiveSeqDescription_subroutineReady
          seekTape2Description_contract.subroutineReady
          hlocal.subroutineReady)
        (returnFromNextSeparatorToCurrentSeparatorDescription_contract
          1).subroutineReady)
      returnFromTape1SeparatorToBlockStartDescription_contract.subroutineReady
  realizes := by
    intro target actual targetTape targetRest hlist hdrop
    rcases singletonGuardSlackEndpointShapeList_drop_eq_cons
        hlist hdrop with
      ⟨_actualTape, _actualRest, hactualDrop, _hsegment, _hrest⟩
    cases actual with
    | nil =>
        simp at hactualDrop
    | cons actual0 actualTail =>
        cases actualTail with
        | nil =>
            simp at hactualDrop
        | cons actual1 actualTailRest =>
            cases actualTailRest with
            | nil =>
                simp at hactualDrop
            | cons actual2 actualRestTail =>
                simp at hactualDrop
                cases hactualDrop
                let modified : List (Tape Bool) :=
                  replaceTapeAt 2 (guardLogicalTape targetTape)
                    (actual0 :: actual1 :: actual2 :: actualRestTail)
                let selectedSeparator : Tape Bool :=
                  tapeAtEncodedSplit
                    (encodedPrefixBeforeTape
                      (actual0 :: actual1 :: actual2 :: actualRestTail) 2)
                    (encodedSuffixFromTape
                      (actual0 :: actual1 :: actual2 :: actualRestTail) 2)
                let modifiedSeparator : Tape Bool :=
                  tapeAtEncodedSplit
                    (encodedPrefixBeforeTape modified 2)
                    (encodedSuffixFromTape modified 2)
                let modifiedSeparator1 : Tape Bool :=
                  tapeAtEncodedSplit
                    (encodedPrefixBeforeTape modified 1)
                    (encodedSuffixFromTape modified 1)
                have hstart :
                    exists T : Tape Bool, exists U : Tape Bool,
                    exists rest : List (Tape Bool),
                      (actual0 :: actual1 :: actual2 :: actualRestTail) =
                        T :: U :: rest ∧
                        AtEncodedBlockStart
                          (actual0 :: actual1 :: actual2 :: actualRestTail)
                          (encodedStructuredTapes
                            (actual0 :: actual1 :: actual2 ::
                              actualRestTail)) := by
                  exact
                    ⟨actual0, actual1, actual2 :: actualRestTail,
                      rfl,
                      atEncodedBlockStart_self
                        (actual0 :: actual1 :: actual2 ::
                          actualRestTail)⟩
                rcases seekTape2Description_contract.realizes
                    (actual0 :: actual1 :: actual2 :: actualRestTail)
                    (encodedStructuredTapes
                      (actual0 :: actual1 :: actual2 :: actualRestTail))
                    hstart with
                  ⟨seekOut, hseek, hseekSep⟩
                have hseekEquiv :
                    seekTape2Description.HaltsFromTapeEquiv
                      (encodedStructuredTapes
                        (actual0 :: actual1 :: actual2 ::
                          actualRestTail))
                      selectedSeparator := by
                  refine ⟨seekOut, hseek, ?_⟩
                  rcases hseekSep with ⟨_hle, hseekOut⟩
                  rw [hseekOut]
                  exact Tape.Equiv.refl _
                have hlocalRun :
                    localRefresh.HaltsFromTapeEquiv selectedSeparator
                      modifiedSeparator := by
                  simpa [selectedSeparator, modified] using
                    hlocal.realizes
                      (target := target)
                      (actual := actual0 :: actual1 :: actual2 ::
                        actualRestTail)
                      (targetTape := targetTape)
                      (targetRest := targetRest)
                      hlist hdrop
                have hfirst :=
                  canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
                    seekTape2Description_contract.subroutineReady
                    hlocal.subroutineReady hseekEquiv hlocalRun
                have hmodifiedSep2 :
                    AtTapeSeparator modified 2 modifiedSeparator := by
                  subst modified
                  subst modifiedSeparator
                  constructor
                  · simp
                  · rfl
                have hmodifiedDropOne :
                    exists T : Tape Bool, exists rest : List (Tape Bool),
                      modified.drop 1 = T :: rest := by
                  subst modified
                  exact
                    ⟨actual1,
                      guardLogicalTape targetTape :: actualRestTail,
                      rfl⟩
                rcases
                    (returnFromNextSeparatorToCurrentSeparatorDescription_contract
                      1).realizes modified modifiedSeparator
                      ⟨hmodifiedSep2, hmodifiedDropOne⟩ with
                  ⟨returnOneOut, hreturnOne, hreturnOneSep⟩
                have hreturnOneEquiv :
                    returnFromNextSeparatorToCurrentSeparatorDescription.HaltsFromTapeEquiv
                      modifiedSeparator modifiedSeparator1 := by
                  refine ⟨returnOneOut, hreturnOne, ?_⟩
                  rcases hreturnOneSep with ⟨_hle, hsep⟩
                  rw [hsep]
                  exact Tape.Equiv.refl _
                have hfirstReturn :=
                  canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
                    (canonicalPrimitiveSeqDescription_subroutineReady
                      seekTape2Description_contract.subroutineReady
                      hlocal.subroutineReady)
                    (returnFromNextSeparatorToCurrentSeparatorDescription_contract
                      1).subroutineReady
                    hfirst hreturnOneEquiv
                have hmodifiedSep1 :
                    AtTapeSeparator modified 1 modifiedSeparator1 := by
                  subst modifiedSeparator1
                  constructor
                  · subst modified
                    simp
                  · rfl
                rcases
                    returnFromTape1SeparatorToBlockStartDescription_contract.realizes
                      modified modifiedSeparator1 hmodifiedSep1 with
                  ⟨returnOut, hreturn, hreturnSep⟩
                have hreturnEquiv :
                    returnFromTape1SeparatorToBlockStartDescription.HaltsFromTapeEquiv
                      modifiedSeparator1
                      (encodedStructuredTapes modified) := by
                  refine ⟨returnOut, hreturn, ?_⟩
                  have hout :=
                    atTapeSeparator_zero_eq_encodedStructuredTapes
                      modified hreturnSep
                  rw [hout]
                  exact Tape.Equiv.refl _
                have hwhole :=
                  canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
                    (canonicalPrimitiveSeqDescription_subroutineReady
                      (canonicalPrimitiveSeqDescription_subroutineReady
                        seekTape2Description_contract.subroutineReady
                        hlocal.subroutineReady)
                      (returnFromNextSeparatorToCurrentSeparatorDescription_contract
                        1).subroutineReady)
                    returnFromTape1SeparatorToBlockStartDescription_contract.subroutineReady
                    hfirstReturn hreturnEquiv
                simpa [structuredSegment2RefreshDescription, modified] using
                  hwhole

/--
Canonical composition of selected-segment refreshers for the three-tape
structured singleton endpoint used by the current lowerer.
-/
def structuredSegmentRefresh3Description
    (refresh0 refresh1 refresh2 : MachineDescription) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription refresh0 refresh1)
    refresh2

theorem structuredSegmentRefresh3Description_contract
    {refresh0 refresh1 refresh2 : MachineDescription}
    (h0 : StructuredSegmentGuardSlackRefreshContract refresh0 0)
    (h1 : StructuredSegmentGuardSlackRefreshContract refresh1 1)
    (h2 : StructuredSegmentGuardSlackRefreshContract refresh2 2) :
    StructuredSingletonGuardSlackRefresh3Contract
      (structuredSegmentRefresh3Description refresh0 refresh1 refresh2) where
  subroutineReady :=
    canonicalPrimitiveSeqDescription_subroutineReady
      (canonicalPrimitiveSeqDescription_subroutineReady
        h0.subroutineReady h1.subroutineReady)
      h2.subroutineReady
  realizes := by
    intro target0 target1 target2 physical hshape
    rcases hshape with ⟨actual, hlist, hphysical⟩
    rcases singletonGuardSlackEndpointShapeList_three hlist with
      ⟨actual0, actual1, actual2, hactual, _hseg0, _hseg1, _hseg2⟩
    subst actual
    have hrun0 :=
      h0.realizes
        (target := [target0, target1, target2])
        (actual := [actual0, actual1, actual2])
        (targetTape := target0)
        (targetRest := [target1, target2])
        hlist rfl
    have hlist0 :
        SingletonGuardSlackEndpointShapeList [target0, target1, target2]
          (replaceTapeAt 0 (guardLogicalTape target0)
            [actual0, actual1, actual2]) :=
      singletonGuardSlackEndpointShapeList_replaceTapeAt_guarded
        hlist rfl
    have hrun1 :=
      h1.realizes
        (target := [target0, target1, target2])
        (actual := replaceTapeAt 0 (guardLogicalTape target0)
          [actual0, actual1, actual2])
        (targetTape := target1)
        (targetRest := [target2])
        hlist0 rfl
    have hlist1 :
        SingletonGuardSlackEndpointShapeList [target0, target1, target2]
          (replaceTapeAt 1 (guardLogicalTape target1)
            (replaceTapeAt 0 (guardLogicalTape target0)
              [actual0, actual1, actual2])) :=
      singletonGuardSlackEndpointShapeList_replaceTapeAt_guarded
        hlist0 rfl
    have hrun2 :=
      h2.realizes
        (target := [target0, target1, target2])
        (actual := replaceTapeAt 1 (guardLogicalTape target1)
          (replaceTapeAt 0 (guardLogicalTape target0)
            [actual0, actual1, actual2]))
        (targetTape := target2)
        (targetRest := [])
        hlist1 rfl
    have hrun01 :=
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        h0.subroutineReady h1.subroutineReady hrun0 hrun1
    have hrun012 :=
      canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
        (canonicalPrimitiveSeqDescription_subroutineReady
          h0.subroutineReady h1.subroutineReady)
        h2.subroutineReady hrun01 hrun2
    rw [hphysical]
    simpa [structuredSegmentRefresh3Description,
      encodedGuardedStructuredTapes, guardLogicalTapes] using hrun012

/--
Three-segment refresh composition with the concrete head refresher fixed for
segment 0.

The remaining parameters are exactly the local selected-separator refreshers
needed for the interior segment boundaries.
-/
def concreteHeadStructuredSegmentRefresh3Description
    (localRefresh1 localRefresh2 : MachineDescription) :
    MachineDescription :=
  structuredSegmentRefresh3Description
    concreteSingletonHeadRefreshDescription
    (structuredSegment1RefreshDescription localRefresh1)
    (structuredSegment2RefreshDescription localRefresh2)

theorem concreteHeadStructuredSegmentRefresh3Description_contract
    {localRefresh1 localRefresh2 : MachineDescription}
    (hlocal1 :
      SelectedSeparatorGuardSlackRefreshContract localRefresh1 1)
    (hlocal2 :
      SelectedSeparatorGuardSlackRefreshContract localRefresh2 2) :
    StructuredSingletonGuardSlackRefresh3Contract
      (concreteHeadStructuredSegmentRefresh3Description
        localRefresh1 localRefresh2) :=
  structuredSegmentRefresh3Description_contract
    concreteSingletonHeadRefreshDescription_segment0Contract
    (structuredSegment1RefreshDescription_contract hlocal1)
    (structuredSegment2RefreshDescription_contract hlocal2)

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC
