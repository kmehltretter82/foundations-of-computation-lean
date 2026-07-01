import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingScratchCounter

set_option doc.verso true

/-!
# Post-padding scratch window

This module isolates the arithmetic and encoded-layout split used to expose the
scratch-count suffix of a parsed selected-projection layout.  The closeout
module consumes these facts when packaging the post-padding source materializer.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

theorem selectedProjectionPaddedTailCleanupSentinelExtraScratch_pos_true
    (L : DovetailLayout) :
    0 < selectedProjectionPaddedTailCleanupSentinelExtraScratch true L := by
  have hsource :=
    SelectedProjectionTailProjector.sourceFieldBits_length_le_parsedLayoutBits
      L
  have hbools :
      8 <=
        (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    cases L.acceptHit <;> cases L.rejectHit <;>
      simp [boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  have hsplit :
      (SelectedProjectionTailProjector.sourceFieldBits L).length =
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage).length +
          (configurationFieldBits L.acceptConfig []).length +
          (configurationFieldBits L.rejectConfig []).length +
          (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    rw [SelectedProjectionTailProjector.sourceFieldBits]
    rw [←
      configurationFieldBits_append_nil L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.acceptHit
            (boolFieldBits L.rejectHit [])))]
    rw [←
      configurationFieldBits_append_nil L.rejectConfig
        (boolFieldBits L.acceptHit
          (boolFieldBits L.rejectHit []))]
    rw [show
        boolFieldBits L.acceptHit (boolFieldBits L.rejectHit []) =
          List.append (boolFieldBits L.acceptHit [])
            (boolFieldBits L.rejectHit []) by
      simpa [boolFieldBits] using
        (cellFieldBits_append_nil (some L.acceptHit)
          (boolFieldBits L.rejectHit [])).symm]
    simp [List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  have hreject_pos :
      0 < (configurationFieldBits L.rejectConfig []).length := by
    simpa [selectedProjectionPaddedTailCleanupUnselectedConfigBits] using
      selectedProjectionPaddedTailCleanupUnselectedConfigBits_length_pos
        true L
  have hlt :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch true L <
        (SelectedProjectionTailProjector.sourceFieldBits L).length := by
    rw [hsplit]
    simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits]
    omega
  have hbase_lt_parsed :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch true L <
        (ParsedLayoutBits L).length := Nat.lt_of_lt_of_le hlt hsource
  rw [selectedProjectionPaddedTailCleanupSentinelExtraScratch]
  omega

theorem selectedProjectionPaddedTailCleanupSentinelExtraScratch_pos_false
    (L : DovetailLayout) :
    0 < selectedProjectionPaddedTailCleanupSentinelExtraScratch false L := by
  have hsource :=
    SelectedProjectionTailProjector.sourceFieldBits_length_le_parsedLayoutBits
      L
  have hbools :
      8 <=
        (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    cases L.acceptHit <;> cases L.rejectHit <;>
      simp [boolFieldBits, cellFieldBits, cellCodeBits,
        encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  have hsplit :
      (SelectedProjectionTailProjector.sourceFieldBits L).length =
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage).length +
          (configurationFieldBits L.acceptConfig []).length +
          (configurationFieldBits L.rejectConfig []).length +
          (boolFieldBits L.acceptHit []).length +
          (boolFieldBits L.rejectHit []).length := by
    rw [SelectedProjectionTailProjector.sourceFieldBits]
    rw [←
      configurationFieldBits_append_nil L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.acceptHit
            (boolFieldBits L.rejectHit [])))]
    rw [←
      configurationFieldBits_append_nil L.rejectConfig
        (boolFieldBits L.acceptHit
          (boolFieldBits L.rejectHit []))]
    rw [show
        boolFieldBits L.acceptHit (boolFieldBits L.rejectHit []) =
          List.append (boolFieldBits L.acceptHit [])
            (boolFieldBits L.rejectHit []) by
      simpa [boolFieldBits] using
        (cellFieldBits_append_nil (some L.acceptHit)
          (boolFieldBits L.rejectHit [])).symm]
    simp [List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  have haccept_pos :
      0 < (configurationFieldBits L.acceptConfig []).length := by
    simpa [selectedProjectionPaddedTailCleanupUnselectedConfigBits] using
      selectedProjectionPaddedTailCleanupUnselectedConfigBits_length_pos
        false L
  have hlt :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch false L <
        (SelectedProjectionTailProjector.sourceFieldBits L).length := by
    rw [hsplit]
    simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits]
    omega
  have hbase_lt_parsed :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch false L <
        (ParsedLayoutBits L).length := Nat.lt_of_lt_of_le hlt hsource
  rw [selectedProjectionPaddedTailCleanupSentinelExtraScratch]
  omega

theorem selectedProjectionPaddedTailCleanupSentinelBaseScratch_eq_unselected_length_add_seven
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupSentinelBaseScratch useAccept L =
      (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        useAccept L).length + 7 := by
  have hpos :=
    selectedProjectionPaddedTailCleanupUnselectedConfigBits_length_pos
      useAccept L
  simp [selectedProjectionPaddedTailCleanupSentinelBaseScratch]
  omega

theorem selectedProjectionPaddedTailCleanupUnselectedLength_add_seven_add_extraScratch
    (useAccept : Bool) (L : DovetailLayout)
    (hle :
      selectedProjectionPaddedTailCleanupSentinelBaseScratch useAccept L <=
        (ParsedLayoutBits L).length) :
    (selectedProjectionPaddedTailCleanupUnselectedConfigBits
        useAccept L).length + 7 +
        selectedProjectionPaddedTailCleanupSentinelExtraScratch useAccept L =
      (ParsedLayoutBits L).length := by
  rw [←
    selectedProjectionPaddedTailCleanupSentinelBaseScratch_eq_unselected_length_add_seven
      useAccept L]
  exact
    selectedProjectionPaddedTailCleanupSentinelBaseScratch_add_extraScratch
      useAccept L hle

theorem selectedProjectionPaddedTailCleanupUnselectedLength_add_seven_add_extraScratch_true
    (L : DovetailLayout) :
    (selectedProjectionPaddedTailCleanupUnselectedConfigBits true L).length +
        7 +
        selectedProjectionPaddedTailCleanupSentinelExtraScratch true L =
      (ParsedLayoutBits L).length :=
  selectedProjectionPaddedTailCleanupUnselectedLength_add_seven_add_extraScratch
    true L
    (selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_true L)

theorem selectedProjectionPaddedTailCleanupUnselectedLength_add_seven_add_extraScratch_false
    (L : DovetailLayout) :
    (selectedProjectionPaddedTailCleanupUnselectedConfigBits false L).length +
        7 +
        selectedProjectionPaddedTailCleanupSentinelExtraScratch false L =
      (ParsedLayoutBits L).length :=
  selectedProjectionPaddedTailCleanupUnselectedLength_add_seven_add_extraScratch
    false L
    (selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_false L)

theorem selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed
    (useAccept : Bool) (L : DovetailLayout) :
    selectedProjectionPaddedTailCleanupSentinelBaseScratch useAccept L <=
      (ParsedLayoutBits L).length := by
  cases useAccept
  · exact
      selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_false
        L
  · exact
      selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed_true
        L

def selectedProjectionPaddedTailCleanupScratchCountBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  (ParsedLayoutBits L).drop
    (selectedProjectionPaddedTailCleanupSentinelBaseScratch useAccept L)

def selectedProjectionPaddedTailCleanupScratchSkippedBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  (ParsedLayoutBits L).take
    (selectedProjectionPaddedTailCleanupSentinelBaseScratch useAccept L)

theorem selectedProjectionPaddedTailCleanupScratchSkippedBits_length
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedProjectionPaddedTailCleanupScratchSkippedBits
        useAccept L).length =
      selectedProjectionPaddedTailCleanupSentinelBaseScratch useAccept L := by
  simp [selectedProjectionPaddedTailCleanupScratchSkippedBits,
    selectedProjectionPaddedTailCleanupSentinelBaseScratch_le_parsed
      useAccept L]

theorem selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
    (useAccept : Bool) (L : DovetailLayout) :
    ParsedLayoutBits L =
      List.append
        (selectedProjectionPaddedTailCleanupScratchSkippedBits useAccept L)
        (selectedProjectionPaddedTailCleanupScratchCountBits
          useAccept L) := by
  simp [selectedProjectionPaddedTailCleanupScratchSkippedBits,
    selectedProjectionPaddedTailCleanupScratchCountBits,
    List.take_append_drop]

theorem selectedProjectionPaddedTailCleanupParsedLayoutBoolWordBits_split
    (useAccept : Bool) (L : DovetailLayout)
    (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeBoolWordAppend (ParsedLayoutBits L) suffix) =
      List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (ParsedLayoutBits L).length)
        (List.append
          (cellsCodeBits
            ((selectedProjectionPaddedTailCleanupScratchSkippedBits
              useAccept L).map some))
          (List.append
            (cellsCodeBits
              ((selectedProjectionPaddedTailCleanupScratchCountBits
                useAccept L).map some))
            (encodeCodeWordAsInput suffix))) := by
  have hsplit :=
    selectedProjectionPaddedTailCleanupParsedLayoutBits_eq_skipped_append_count
      useAccept L
  have hmap :
      (ParsedLayoutBits L).map some =
        List.append
          ((selectedProjectionPaddedTailCleanupScratchSkippedBits
            useAccept L).map some)
          ((selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).map some) := by
    rw [hsplit]
    simp [List.map_append]
  rw [boolWordBits_eq_encodeBoolWordAppend]
  rw [hmap]
  rw [cellsCodeBits_append]
  exact
    congrArg
      (fun tail =>
        List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (ParsedLayoutBits L).length)
          tail)
      (List.append_assoc
        (cellsCodeBits
          ((selectedProjectionPaddedTailCleanupScratchSkippedBits
            useAccept L).map some))
        (cellsCodeBits
          ((selectedProjectionPaddedTailCleanupScratchCountBits
            useAccept L).map some))
        (encodeCodeWordAsInput suffix))

theorem selectedProjectionPaddedTailCleanupScratchCountBits_length
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).length =
      selectedProjectionPaddedTailCleanupSentinelExtraScratch
        useAccept L := by
  simp [selectedProjectionPaddedTailCleanupScratchCountBits,
    selectedProjectionPaddedTailCleanupSentinelExtraScratch]

theorem selectedProjectionPaddedTailCleanupScratchCountBits_length_true
    (L : DovetailLayout) :
    (selectedProjectionPaddedTailCleanupScratchCountBits true L).length =
      selectedProjectionPaddedTailCleanupSentinelExtraScratch true L :=
  selectedProjectionPaddedTailCleanupScratchCountBits_length true L

theorem selectedProjectionPaddedTailCleanupScratchCountBits_length_false
    (L : DovetailLayout) :
    (selectedProjectionPaddedTailCleanupScratchCountBits false L).length =
      selectedProjectionPaddedTailCleanupSentinelExtraScratch false L :=
  selectedProjectionPaddedTailCleanupScratchCountBits_length false L

theorem selectedProjectionPaddedTailCleanupScratchCountBits_length_pos
    (useAccept : Bool) (L : DovetailLayout) :
    0 <
      (selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).length := by
  cases useAccept
  · rw [selectedProjectionPaddedTailCleanupScratchCountBits_length_false]
    exact selectedProjectionPaddedTailCleanupSentinelExtraScratch_pos_false
      L
  · rw [selectedProjectionPaddedTailCleanupScratchCountBits_length_true]
    exact selectedProjectionPaddedTailCleanupSentinelExtraScratch_pos_true
      L

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
