import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompactionShape
import FoC.Computability.Compiler.Structured.Lowering.PairEncodedOptionCellCompactor.Base

set_option doc.verso true

/-!
# Selected-footprint compaction contract guardrails

The former payload-wide ingress and arbitrary-bit compactor constructions are
inconsistent with {lit}`Tape.Equiv`.  This module records the concrete
collisions and the source-family functionality of the narrower live
count-window frontier.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner
open PairEncodedOptionCellCompactor

/-!
## Retired payload-wide ingress contract

These three declarations keep the rejected contract visible at the guardrail
that disproves it.  They used to anchor a large endpoint-bridge lattice; no
live construction may depend on them.
-/

def selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape
    (payload : List (Option Bool)) : Tape Bool :=
  PairEncodedOptionCellCompactor.payloadIngressTargetTape payload

def SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall payload : List (Option Bool),
      initializer.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          payload)
        (selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape
          payload)

def SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction :
    Prop :=
  exists initializer : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec
      initializer

theorem selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_eq_pairEncodedIngressSource
    (payload : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        payload =
      PairEncodedOptionCellCompactor.fixedPrefixPayloadIngressSourceTape
        selectedSegmentLogicalTapeDecoderGuardPrefixCells payload := by
  simp [
    selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload,
    selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload,
    selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload,
    PairEncodedOptionCellCompactor.fixedPrefixPayloadIngressSourceTape,
    PairEncodedOptionCellCompactor.encodedCells]

private theorem concreteGuardPrefix_payloadSource_collision :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload [])
      (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
        [none]) := by
  simp [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload,
    selectedSegmentLogicalTapeDecoderFootprintLeftCellsFromPayload,
    selectedSegmentLogicalTapeDecoderFootprintCellsFromPayload,
    selectedSegmentLogicalTapeDecoderGuardPrefixCells,
    selectedSegmentLogicalTapeDecoderCellCells,
    rightEndCompactionSourceTape, tapeAtCells,
    Tape.Equiv, Tape.dropTrailingNone]

private theorem concreteGuardPrefix_payloadTarget_separation :
    ¬ Tape.Equiv
      (selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape [])
      (selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape
        [none]) := by
  simp [selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape,
    payloadIngressTargetTape, encodedGuardedStructured3Tapes,
    encodedGuardedStructuredTapes, encodedStructuredTapes,
    guardLogicalTapes, guardLogicalTape,
    sourceTape, sourceTapeAt, markerTape, markerTapeAt, outputTape,
    encodedCells, logicalTapeCode, logicalCellListCode, headMarkerCells,
    logicalCellCode, logicalCellListBits, logicalCellBits,
    encodedStructuredTapeCells, tapeSeparatorCells, markerCell, tapeAtCells,
    Tape.Equiv, Tape.dropTrailingNone]

/--
The concrete six-blank-prefix payload family cannot have one deterministic
structured input materializer: payloads {lit}`[]` and {lit}`[none]` are
equivalent sources but demand non-equivalent guarded targets.
-/
theorem selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction_impossible :
    ¬ SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction := by
  rintro ⟨initializer, hready, hrun⟩
  rcases hrun [] with ⟨actualNil, hhaltNil, hequivNil⟩
  rcases hrun [none] with ⟨actualOne, hhaltOne, hequivOne⟩
  rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      concreteGuardPrefix_payloadSource_collision hhaltNil with
    ⟨actualNil', hhaltNil', hequivNil'⟩
  have hactual : actualNil' = actualOne :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hready.right hhaltNil' hhaltOne
  subst actualNil'
  have htargets :=
    Tape.Equiv.trans (Tape.Equiv.symm hequivNil)
      (Tape.Equiv.trans (Tape.Equiv.symm hequivNil') hequivOne)
  exact concreteGuardPrefix_payloadTarget_separation htargets

private theorem genericCompactor_nilPadding_source_collision :
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [some true])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        [] [none, some true]) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
    selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells,
    selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
    selectedSegmentLogicalTapeDecoderCellCells,
    rightEndCompactionSourceTape, tapeAtCells,
    Tape.Equiv, Tape.dropTrailingNone]

private theorem genericCompactor_nilPadding_target_separation :
    ¬ Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] [some true])
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        [] [none, some true]) := by
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape,
    rightEdgeRewindSourceTape, tapeAtCells,
    Tape.Equiv, Tape.dropTrailingNone]

/--
The old arbitrary-bit compactor frontier is inconsistent.  With no selected
bits, inserting one leading blank before a later nonblank padding cell does not
change the source equivalence class, but it does change the requested head
layout at the target.
-/
theorem selectedSegmentLogicalTapeDecoderFootprintCompactorConstruction_impossible :
    ¬ SelectedSegmentLogicalTapeDecoderFootprintCompactorConstruction := by
  rintro ⟨compactor, hready, hrun⟩
  rcases hrun [] [some true] with
    ⟨actualShort, hhaltShort, hequivShort⟩
  rcases hrun [] [none, some true] with
    ⟨actualLong, hhaltLong, hequivLong⟩
  rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      genericCompactor_nilPadding_source_collision hhaltShort with
    ⟨actualShort', hhaltShort', hequivShort'⟩
  have hactual : actualShort' = actualLong :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hready.right hhaltShort' hhaltLong
  subst actualShort'
  have htargets :=
    Tape.Equiv.trans (Tape.Equiv.symm hequivShort)
      (Tape.Equiv.trans (Tape.Equiv.symm hequivShort') hequivLong)
  exact genericCompactor_nilPadding_target_separation htargets

private theorem dropTrailingNone_append_some
    (xs : List (Option Bool)) (bit : Bool) :
    Tape.dropTrailingNone (xs ++ [some bit]) = xs ++ [some bit] := by
  induction xs with
  | nil =>
      rfl
  | cons cell rest ih =>
      rw [List.cons_append, Tape.dropTrailingNone_cons, ih]
      simp

private theorem dropTrailingNone_append_some_replicate_none
    (xs : List (Option Bool)) (bit : Bool) (n : Nat) :
    Tape.dropTrailingNone
        ((xs ++ [some bit]) ++ List.replicate n none) =
      xs ++ [some bit] := by
  rw [dropTrailingNone_append_replicate_none]
  exact dropTrailingNone_append_some xs bit

private theorem dropTrailingNone_append_some_eight_none
    (xs : List (Option Bool)) (bit : Bool) :
    Tape.dropTrailingNone
        (xs ++ [some bit, none, none, none, none, none, none, none, none]) =
      xs ++ [some bit] := by
  simpa [List.append_assoc] using
    dropTrailingNone_append_some_replicate_none xs bit 8

private theorem concreteGuardPrefix_sourceLeftTrim_cons_some
    (bit : Bool) (rest : List (Option Bool)) :
    Tape.dropTrailingNone
        (fixedPrefixPayloadIngressSourceTape
          selectedSegmentLogicalTapeDecoderGuardPrefixCells
          (some bit :: rest)).left =
      none :: (encodedCells rest).reverse ++ [some bit] := by
  simp [fixedPrefixPayloadIngressSourceTape,
    selectedSegmentLogicalTapeDecoderGuardPrefixCells,
    encodedCells, rightEndCompactionSourceTape, tapeAtCells,
    Tape.dropTrailingNone, List.reverse_append,
    dropTrailingNone_append_some_eight_none]

private theorem mapSome_append_none_cons_inj :
    forall (xs ys : List Bool) (u v : List (Option Bool)),
      xs.map some ++ none :: u = ys.map some ++ none :: v ->
        xs = ys ∧ u = v
  | [], [], _u, _v, h => by
      injection h with _ huv
      exact ⟨rfl, huv⟩
  | [], _y :: _ys, _u, _v, h => by
      injection h with hcontra _
      cases hcontra
  | _x :: _xs, [], _u, _v, h => by
      injection h with hcontra _
      cases hcontra
  | x :: xs, y :: ys, u, v, h => by
      injection h with hhead htail
      injection hhead with hxy
      rcases mapSome_append_none_cons_inj xs ys u v htail with
        ⟨hxs, huv⟩
      exact ⟨by rw [hxy, hxs], huv⟩

/--
The live count-window target is functional on source equivalence classes.
Unlike the retired arbitrary-bit family, every live parsed-layout word begins
with two nonblank encoded bits, so the pair encoding retains the complete
payload and padding split.
-/
theorem countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTarget_functional_of_source_equiv
    (useAcceptA useAcceptB : Bool) (L K : DovetailLayout)
    (hsource :
      Tape.Equiv
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAcceptA L)
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAcceptB K)) :
    Tape.Equiv
      (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
        useAcceptA L)
      (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorTargetTape
        useAcceptB K) := by
  change
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAcceptA L))
      (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        (ParsedLayoutBits K)
        (postFieldDecodedPrefixScanPadding useAcceptB K)) at hsource
  change
    Tape.Equiv
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (ParsedLayoutBits L)
        (postFieldDecodedPrefixScanPadding useAcceptA L))
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (ParsedLayoutBits K)
        (postFieldDecodedPrefixScanPadding useAcceptB K))
  rcases parsedLayoutBits_eq_false_false_tail L with ⟨tailL, hbitsL⟩
  rcases parsedLayoutBits_eq_false_false_tail K with ⟨tailK, hbitsK⟩
  rw [hbitsL, hbitsK] at hsource ⊢
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
    selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload,
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape,
    selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload] at hsource
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_eq_pairEncodedIngressSource,
    selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload_eq_pairEncodedIngressSource] at hsource
  have hleft := hsource.left
  simp [selectedSegmentLogicalTapeDecoderPayloadCells,
    concreteGuardPrefix_sourceLeftTrim_cons_some] at hleft
  have hpayload := encodedCells_inj hleft
  rcases mapSome_append_none_cons_inj _ _ _ _ hpayload with
    ⟨htail, hpaddingEnd⟩
  have hpadding :
      postFieldDecodedPrefixScanPadding useAcceptA L =
        postFieldDecodedPrefixScanPadding useAcceptB K := by
    simpa using hpaddingEnd
  simpa [htail, hpadding] using
    Tape.Equiv.refl
      (selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape
        (false :: false :: tailL)
        (postFieldDecodedPrefixScanPadding useAcceptA L))

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
