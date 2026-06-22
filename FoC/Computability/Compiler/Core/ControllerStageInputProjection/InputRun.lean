import FoC.Computability.Compiler.Core.ControllerStageInputProjection.ScanInput

set_option doc.verso true

/-!
# InputRun

Supporting declarations and helper lemmas for Computability Compiler Core ControllerStageInputProjection InputRun.
-/


namespace FoC
namespace Computability

open Languages

namespace ControllerStageInputProjection


def projectionInputBoolWordCost (w : Word Bool) : Nat :=
  12 * w.length * w.length + 42 * w.length + 24

def projectionResultBoolWordCost (w : Word Bool) : Nat :=
  12 * w.length * w.length + 34 * w.length + 16

def projectionInputMarkStepCost
    (marked rest : Word Bool) : Nat :=
  16 * marked.length + 8 * rest.length + 30

def projectionInputRemainingCost
    (marked rest : Word Bool) : Nat :=
  12 * rest.length * rest.length +
    16 * marked.length * rest.length +
    42 * rest.length + 24 * marked.length + 24

 /-- {name}`run_input_mark_one` states the corresponding theorem run form. -/
theorem run_input_mark_one
    (marked rest : Word Bool) (b : Bool)
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionInputMarkStepCost marked rest)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked (b :: rest) suffix)) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix) := by
  have hcost :
      projectionInputMarkStepCost marked rest =
        4 * marked.length +
          (4 + (4 * rest.length +
            (4 + (4 * marked.length +
              (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
                7)))))) := by
    rw [projectionInputMarkScanBackCellsRev_length]
    simp [projectionInputMarkStepCost]
    omega
  rw [hcost, MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + (4 * rest.length +
          (4 + (4 * marked.length +
            (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
              7))))))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 100
            (List.append [none, none, none, none] baseLeftRev)
            (projectionBoolWordWorkCells marked (b :: rest) suffix))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  simp only [projectionBoolWordWorkCells]
  rw [run_state100_marked_ticks]
  have htickCells :
      projectionCodeCells
          (List.replicate (b :: rest).length MachineCodeSymbol.tick) =
        List.append projectionTickCodeCells
          (projectionCodeCells
            (List.replicate rest.length MachineCodeSymbol.tick)) := by
    change
      projectionCodeCells
          (List.replicate (rest.length + 1) MachineCodeSymbol.tick) =
        List.append projectionTickCodeCells
          (projectionCodeCells
            (List.replicate rest.length MachineCodeSymbol.tick))
    rw [show rest.length + 1 = Nat.succ rest.length by omega]
    rfl
  rw [MachineDescription.runConfig_add]
  rw [htickCells]
  change
    Description.runConfig
        (4 * rest.length +
          (4 + (4 * marked.length +
            (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
              7)))))
        (Description.runConfig 4
          (projectionConfig 100
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionTickCodeCells
              (List.append
                (projectionCodeCells
                  (List.replicate rest.length MachineCodeSymbol.tick))
                (List.append projectionDoneCodeCells
                  (List.append (projectionMarkedBoolPayloadCells marked)
                    (List.append (projectionBoolPayloadCells (b :: rest))
                      (projectionCodeCells suffix)))))))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  rw [run_state100_mark_tick]
  rw [MachineDescription.runConfig_add]
  rw [projectionCodeCells_replicate_tick]
  change
    Description.runConfig
        (4 + (4 * marked.length +
          (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
            7))))
        (Description.runConfig
          (4 * rest.length)
          (projectionConfig 120
            (List.append projectionMarkedTickCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  marked.length).reverse
                (List.append [none, none, none, none] baseLeftRev)))
            (List.append
              (projectionRepeatedCells projectionTickCodeCells rest.length)
              (List.append projectionDoneCodeCells
                (List.append (projectionMarkedBoolPayloadCells marked)
                  (List.append (projectionBoolPayloadCells (b :: rest))
                    (projectionCodeCells suffix))))))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  rw [run_state120_ticks]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 * marked.length +
          (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length +
            7)))
        (Description.runConfig 4
          (projectionConfig 120
            (List.append
              (projectionRepeatedCells projectionTickCodeCells
                rest.length).reverse
              (List.append projectionMarkedTickCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells
                    marked.length).reverse
                  (List.append [none, none, none, none] baseLeftRev))))
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells marked)
                (List.append (projectionBoolPayloadCells (b :: rest))
                  (projectionCodeCells suffix)))))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  rw [run_state120_done]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + ((projectionInputMarkScanBackCellsRev marked rest b).length + 7))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 130
            (List.append projectionDoneCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionTickCodeCells
                  rest.length).reverse
                (List.append projectionMarkedTickCodeCells.reverse
                  (List.append
                    (projectionRepeatedCells projectionMarkedTickCodeCells
                      marked.length).reverse
                    (List.append [none, none, none, none] baseLeftRev)))))
            (List.append (projectionMarkedBoolPayloadCells marked)
              (List.append (projectionBoolPayloadCells (b :: rest))
                (projectionCodeCells suffix))))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  rw [run_state130_marked_payload]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        ((projectionInputMarkScanBackCellsRev marked rest b).length + 7)
        (Description.runConfig 4
          (projectionConfig 130
            (List.append (projectionMarkedBoolPayloadCells marked).reverse
              (List.append projectionDoneCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionTickCodeCells
                    rest.length).reverse
                  (List.append projectionMarkedTickCodeCells.reverse
                    (List.append
                      (projectionRepeatedCells projectionMarkedTickCodeCells
                        marked.length).reverse
                      (List.append [none, none, none, none] baseLeftRev))))))
            (List.append (projectionBoolPayloadCells (b :: rest))
              (projectionCodeCells suffix)))) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix)
  rw [show projectionBoolPayloadCells (b :: rest) =
      List.append (projectionBoolCellCodeCells b)
        (projectionBoolPayloadCells rest) by
    rfl]
  rw [show
      List.append
          (List.append (projectionBoolCellCodeCells b)
            (projectionBoolPayloadCells rest))
          (projectionCodeCells suffix) =
        List.append (projectionBoolCellCodeCells b)
          (List.append (projectionBoolPayloadCells rest)
            (projectionCodeCells suffix)) by
    simp [List.append_assoc]]
  rw [run_state130_mark_payload_cell]
  cases b
  · simp only [projectionBoolWordWorkCells,
      projectionMarkedBoolPayloadCells_append_false,
      projectionCodeCells_replicate_tick]
    simpa [projectionScanLeftConfig, projectionInputMarkScanBackCellsRev,
      projectionInputMarkPreviousCells, projectionInputMarkScanTail,
      projectionMarkedBoolCellScanPrefixRev,
      projectionMarkedBoolCellScanTailHead, projectionBoolWordWorkCells,
      projectionMarkedBoolPayloadCells_append,
      projectionMarkedBoolPayloadCells, projectionBoolPayloadCells,
      projectionCodeCells_replicate_tick, projectionRepeatedCells_succ_right,
      List.reverse_append, List.append_assoc] using
        (run_scan140_cells_to_boundary
          (cellsRev := projectionInputMarkScanBackCellsRev marked rest false)
          (hsafe := projectionInputMarkScanBackCellsRev_scanSafe marked rest false)
          (hcount := projectionInputMarkScanBackCellsRev_scanCountFold marked rest false)
          (base := baseLeftRev)
          (tail := projectionInputMarkScanTail rest false suffix))
  · simp only [projectionBoolWordWorkCells,
      projectionMarkedBoolPayloadCells_append_true,
      projectionCodeCells_replicate_tick]
    simpa [projectionScanLeftConfig, projectionInputMarkScanBackCellsRev,
      projectionInputMarkPreviousCells, projectionInputMarkScanTail,
      projectionMarkedBoolCellScanPrefixRev,
      projectionMarkedBoolCellScanTailHead, projectionBoolWordWorkCells,
      projectionMarkedBoolPayloadCells_append,
      projectionMarkedBoolPayloadCells, projectionBoolPayloadCells,
      projectionCodeCells_replicate_tick, projectionRepeatedCells_succ_right,
      List.reverse_append, List.append_assoc] using
        (run_scan140_cells_to_boundary
          (cellsRev := projectionInputMarkScanBackCellsRev marked rest true)
          (hsafe := projectionInputMarkScanBackCellsRev_scanSafe marked rest true)
          (hcount := projectionInputMarkScanBackCellsRev_scanCountFold marked rest true)
          (base := baseLeftRev)
            (tail := projectionInputMarkScanTail rest true suffix))

def projectionResultTailWorkCells
    (marked : Word Bool) (restCount : Nat)
    (tail : List (Option Bool)) : List (Option Bool) :=
  List.append
    (projectionRepeatedCells projectionMarkedTickCodeCells marked.length)
    (List.append
      (projectionCodeCells
        (List.replicate restCount MachineCodeSymbol.tick))
      (List.append projectionDoneCodeCells
        (List.append (projectionMarkedBoolPayloadCells marked) tail)))

def projectionResultMarkTailStepCost
    (marked : Word Bool) (restCount : Nat) : Nat :=
  16 * marked.length + 8 * restCount + 30

def projectionResultTailPayloadLeftRev
    (marked : Word Bool) (restCount : Nat)
    (baseLeftRev : List (Option Bool)) : List (Option Bool) :=
  List.append (projectionMarkedBoolPayloadCells marked).reverse
    (List.append projectionDoneCodeCells.reverse
      (List.append
        (projectionRepeatedCells projectionTickCodeCells restCount).reverse
        (List.append projectionMarkedTickCodeCells.reverse
          (List.append
            (projectionRepeatedCells projectionMarkedTickCodeCells
              marked.length).reverse
            (List.append [none, none, none, none] baseLeftRev)))))

 /-- {name}`run_input_finish_marked_suffix` states the corresponding theorem run form. -/
theorem run_input_finish_marked_suffix
    (marked : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (24 * marked.length + 24)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked []
            (MachineDescription.encodeNatAppend stage suffix))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells
          (MachineDescription.encodeNatAppend stage suffix)) := by
  have hcost :
      24 * marked.length + 24 =
        4 * marked.length +
          (4 + (4 * marked.length +
            (2 + ((projectionInputFinishScanBackCellsRev marked).length + 7 +
              (4 * marked.length + (4 + (4 * marked.length + 2))))))) := by
    rw [projectionInputFinishScanBackCellsRev_length]
    omega
  have hnil :
      projectionCodeCells ([] : Word MachineCodeSymbol) = [] := rfl
  rw [hcost, MachineDescription.runConfig_add]
  simp only [projectionBoolWordWorkCells]
  rw [projectionCodeCells_encodeNatAppend_cons_cons_suffix]
  rw [run_state100_marked_ticks]
  simp [List.length_nil, hnil, projectionBoolPayloadCells]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 * marked.length +
          (2 + ((projectionInputFinishScanBackCellsRev marked).length + 7 +
            (4 * marked.length + (4 + (4 * marked.length + 2))))))
        (Description.runConfig 4
          (projectionConfig 100
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells marked)
                (some false :: some false ::
                  projectionInputFinishSuffixTailFor stage suffix))))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (some false :: some false ::
          projectionInputFinishSuffixTailFor stage suffix)
  rw [run_state100_done]
  rw [MachineDescription.runConfig_add]
  rw [run_state150_marked_payload]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        ((projectionInputFinishScanBackCellsRev marked).length + 7 +
          (4 * marked.length + (4 + (4 * marked.length + 2))))
        (Description.runConfig 2
          (projectionConfig 150
            (List.append (projectionMarkedBoolPayloadCells marked).reverse
              (List.append projectionDoneCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells
                    marked.length).reverse
                  (List.append [none, none, none, none] baseLeftRev))))
            (some false :: some false ::
              projectionInputFinishSuffixTailFor stage suffix))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (some false :: some false ::
          projectionInputFinishSuffixTailFor stage suffix)
  rw [run_state150_to_scan160]
  rw [show
      (projectionInputFinishScanBackCellsRev marked).length + 7 +
          (4 * marked.length + (4 + (4 * marked.length + 2))) =
        ((projectionInputFinishScanBackCellsRev marked).length + 7) +
          (4 * marked.length + (4 + (4 * marked.length + 2))) by
    omega,
    MachineDescription.runConfig_add]
  rw [show
      projectionConfig 160
          (List.append (projectionMarkedBoolPayloadCells marked).reverse
            (List.append projectionDoneCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  marked.length).reverse
                (List.append [none, none, none, none] baseLeftRev))))
          (some false :: some false ::
            projectionInputFinishSuffixTailFor stage suffix) =
        projectionScanLeftConfig 160
          (List.append ([none, none, none] : List (Option Bool)) baseLeftRev)
          none (projectionInputFinishScanBackCellsRev marked)
          (some false :: projectionInputFinishSuffixTailFor stage suffix) by
    simp [projectionScanLeftConfig, projectionInputFinishScanBackCellsRev,
      List.append_assoc]]
  rw [run_scan160_cells_to_boundary
    (hsafe := projectionInputFinishScanBackCellsRev_scanSafe marked)
    (hcount := projectionInputFinishScanBackCellsRev_scanCountFold marked)]
  simp [projectionInputFinishScanBackCellsRev, List.reverse_append,
    List.append_assoc]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + (4 * marked.length + 2))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 170
            (List.append [none, none, none, none] baseLeftRev)
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length)
              (List.append projectionDoneCodeCells
                (List.append (projectionMarkedBoolPayloadCells marked)
                  (some false :: some false ::
                    projectionInputFinishSuffixTailFor stage suffix)))))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (some false :: some false ::
          projectionInputFinishSuffixTailFor stage suffix)
  rw [run_state170_marked_ticks]
  rw [MachineDescription.runConfig_add]
  rw [run_state170_done]
  rw [MachineDescription.runConfig_add]
  rw [run_state180_marked_payload]
  rw [run_state180_to_200]
  simp [projectionCodeCells_encodeBoolWord, List.reverse_append,
    List.append_assoc]

 /-- {name}`run_input_finish_marked` states the corresponding theorem run form. -/
theorem run_input_finish_marked
    (marked : Word Bool) (stage : Nat) (result : Word Bool)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (24 * marked.length + 24)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked []
            (MachineDescription.encodeNatAppend stage
              (MachineDescription.encodeBoolWord result)))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeBoolWord result))) := by
  have hcost :
      24 * marked.length + 24 =
        4 * marked.length +
          (4 + (4 * marked.length +
            (2 + ((projectionInputFinishScanBackCellsRev marked).length + 7 +
              (4 * marked.length + (4 + (4 * marked.length + 2))))))) := by
    rw [projectionInputFinishScanBackCellsRev_length]
    omega
  have hnil :
      projectionCodeCells ([] : Word MachineCodeSymbol) = [] := rfl
  rw [hcost, MachineDescription.runConfig_add]
  simp only [projectionBoolWordWorkCells]
  rw [projectionCodeCells_encodeNatAppend_cons_cons]
  rw [run_state100_marked_ticks]
  simp [List.length_nil, hnil, projectionBoolPayloadCells]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 * marked.length +
          (2 + ((projectionInputFinishScanBackCellsRev marked).length + 7 +
            (4 * marked.length + (4 + (4 * marked.length + 2))))))
        (Description.runConfig 4
          (projectionConfig 100
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells marked)
                (some false :: some false ::
                  projectionInputFinishSuffixTail stage result))))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (some false :: some false ::
          projectionInputFinishSuffixTail stage result)
  rw [run_state100_done]
  rw [MachineDescription.runConfig_add]
  rw [run_state150_marked_payload]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        ((projectionInputFinishScanBackCellsRev marked).length + 7 +
          (4 * marked.length + (4 + (4 * marked.length + 2))))
        (Description.runConfig 2
          (projectionConfig 150
            (List.append (projectionMarkedBoolPayloadCells marked).reverse
              (List.append projectionDoneCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells
                    marked.length).reverse
                  (List.append [none, none, none, none] baseLeftRev))))
            (some false :: some false ::
              projectionInputFinishSuffixTail stage result))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (some false :: some false ::
          projectionInputFinishSuffixTail stage result)
  rw [run_state150_to_scan160]
  rw [show
      (projectionInputFinishScanBackCellsRev marked).length + 7 +
          (4 * marked.length + (4 + (4 * marked.length + 2))) =
        ((projectionInputFinishScanBackCellsRev marked).length + 7) +
          (4 * marked.length + (4 + (4 * marked.length + 2))) by
    omega,
    MachineDescription.runConfig_add]
  rw [show
      projectionConfig 160
          (List.append (projectionMarkedBoolPayloadCells marked).reverse
            (List.append projectionDoneCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  marked.length).reverse
                (List.append [none, none, none, none] baseLeftRev))))
          (some false :: some false ::
            projectionInputFinishSuffixTail stage result) =
        projectionScanLeftConfig 160
          (List.append ([none, none, none] : List (Option Bool)) baseLeftRev)
          none (projectionInputFinishScanBackCellsRev marked)
          (some false :: projectionInputFinishSuffixTail stage result) by
    simp [projectionScanLeftConfig, projectionInputFinishScanBackCellsRev,
      List.append_assoc]]
  rw [run_scan160_cells_to_boundary
    (hsafe := projectionInputFinishScanBackCellsRev_scanSafe marked)
    (hcount := projectionInputFinishScanBackCellsRev_scanCountFold marked)]
  simp [projectionInputFinishScanBackCellsRev, List.reverse_append,
    List.append_assoc]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + (4 * marked.length + 2))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 170
            (List.append [none, none, none, none] baseLeftRev)
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length)
              (List.append projectionDoneCodeCells
                (List.append (projectionMarkedBoolPayloadCells marked)
                  (some false :: some false ::
                    projectionInputFinishSuffixTail stage result)))))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (some false :: some false ::
          projectionInputFinishSuffixTail stage result)
  rw [run_state170_marked_ticks]
  rw [MachineDescription.runConfig_add]
  rw [run_state170_done]
  rw [MachineDescription.runConfig_add]
  rw [run_state180_marked_payload]
  rw [run_state180_to_200]
  simp [projectionCodeCells_encodeBoolWord, List.reverse_append,
    List.append_assoc]

 /-- {name}`run_input_finish_marked_false_false_tail` states the corresponding theorem run form. -/
theorem run_input_finish_marked_false_false_tail
    (marked : Word Bool) (tail : List (Option Bool))
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (24 * marked.length + 24)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionResultTailWorkCells marked 0
            (some false :: some false :: tail))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (some false :: some false :: tail) := by
  have hcost :
      24 * marked.length + 24 =
        4 * marked.length +
          (4 + (4 * marked.length +
            (2 + ((projectionInputFinishScanBackCellsRev marked).length + 7 +
              (4 * marked.length + (4 + (4 * marked.length + 2))))))) := by
    rw [projectionInputFinishScanBackCellsRev_length]
    omega
  rw [hcost, MachineDescription.runConfig_add]
  simp only [projectionResultTailWorkCells]
  rw [run_state100_marked_ticks]
  simp
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 * marked.length +
          (2 + ((projectionInputFinishScanBackCellsRev marked).length + 7 +
            (4 * marked.length + (4 + (4 * marked.length + 2))))))
        (Description.runConfig 4
          (projectionConfig 100
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells marked)
                (some false :: some false :: tail))))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (some false :: some false :: tail)
  rw [run_state100_done]
  rw [MachineDescription.runConfig_add]
  rw [run_state150_marked_payload]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        ((projectionInputFinishScanBackCellsRev marked).length + 7 +
          (4 * marked.length + (4 + (4 * marked.length + 2))))
        (Description.runConfig 2
          (projectionConfig 150
            (List.append (projectionMarkedBoolPayloadCells marked).reverse
              (List.append projectionDoneCodeCells.reverse
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells
                    marked.length).reverse
                  (List.append [none, none, none, none] baseLeftRev))))
            (some false :: some false :: tail))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (some false :: some false :: tail)
  rw [run_state150_to_scan160]
  rw [show
      (projectionInputFinishScanBackCellsRev marked).length + 7 +
          (4 * marked.length + (4 + (4 * marked.length + 2))) =
        ((projectionInputFinishScanBackCellsRev marked).length + 7) +
          (4 * marked.length + (4 + (4 * marked.length + 2))) by
    omega,
    MachineDescription.runConfig_add]
  rw [show
      projectionConfig 160
          (List.append (projectionMarkedBoolPayloadCells marked).reverse
            (List.append projectionDoneCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  marked.length).reverse
                (List.append [none, none, none, none] baseLeftRev))))
          (some false :: some false :: tail) =
        projectionScanLeftConfig 160
          (List.append ([none, none, none] : List (Option Bool)) baseLeftRev)
          none (projectionInputFinishScanBackCellsRev marked)
          (some false :: tail) by
    simp [projectionScanLeftConfig, projectionInputFinishScanBackCellsRev,
      List.append_assoc]]
  rw [run_scan160_cells_to_boundary
    (hsafe := projectionInputFinishScanBackCellsRev_scanSafe marked)
    (hcount := projectionInputFinishScanBackCellsRev_scanCountFold marked)]
  simp [projectionInputFinishScanBackCellsRev, List.reverse_append,
    List.append_assoc]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 + (4 * marked.length + 2))
        (Description.runConfig
          (4 * marked.length)
          (projectionConfig 170
            (List.append [none, none, none, none] baseLeftRev)
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length)
              (List.append projectionDoneCodeCells
                (List.append (projectionMarkedBoolPayloadCells marked)
                  (some false :: some false :: tail)))))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (some false :: some false :: tail)
  rw [run_state170_marked_ticks]
  rw [MachineDescription.runConfig_add]
  rw [run_state170_done]
  rw [MachineDescription.runConfig_add]
  rw [run_state180_marked_payload]
  rw [run_state180_to_200]
  simp [projectionCodeCells_encodeBoolWord, List.reverse_append,
    List.append_assoc]

 /-- {name}`run_input_finish_marked_to_state150_tail` states the corresponding theorem run form. -/
theorem run_input_finish_marked_to_state150_tail
    (marked : Word Bool) (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (8 * marked.length + 4)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked [] suffix)) =
      projectionConfig 150
        (List.append (projectionMarkedBoolPayloadCells marked).reverse
          (List.append projectionDoneCodeCells.reverse
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))))
        (projectionCodeCells suffix) := by
  rw [show 8 * marked.length + 4 =
      4 * marked.length + (4 + 4 * marked.length) by
    omega,
    MachineDescription.runConfig_add]
  simp only [projectionBoolWordWorkCells]
  rw [run_state100_marked_ticks]
  simp [List.length_nil, projectionBoolPayloadCells]
  rw [MachineDescription.runConfig_add]
  change
    Description.runConfig
        (4 * marked.length)
        (Description.runConfig 4
          (projectionConfig 100
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells marked)
                (projectionCodeCells suffix))))) =
      projectionConfig 150
        (List.append (projectionMarkedBoolPayloadCells marked).reverse
          (List.append projectionDoneCodeCells.reverse
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))))
        (projectionCodeCells suffix)
  rw [run_state100_done]
  rw [run_state150_marked_payload]

 /-- {name}`run_input_bool_word_acc` states the corresponding theorem run form. -/
theorem run_input_bool_word_acc
    (marked rest : Word Bool) (stage : Nat) (result : Word Bool)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionInputRemainingCost marked rest)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked rest
            (MachineDescription.encodeNatAppend stage
              (MachineDescription.encodeBoolWord result)))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells
            (MachineDescription.encodeBoolWord
              (List.append marked rest))).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeBoolWord result))) := by
  induction rest generalizing marked baseLeftRev with
  | nil =>
      simp [projectionInputRemainingCost]
      exact
        run_input_finish_marked
          marked stage result baseLeftRev
  | cons b rest ih =>
      have hcost :
          projectionInputRemainingCost marked (b :: rest) =
            projectionInputMarkStepCost marked rest +
              projectionInputRemainingCost (List.append marked [b]) rest := by
        simp [projectionInputRemainingCost, projectionInputMarkStepCost,
          Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
        omega
      rw [hcost, MachineDescription.runConfig_add]
      rw [run_input_mark_one]
      rw [ih]
      have hword :
          List.append (List.append marked [b]) rest =
            List.append marked (b :: rest) := by
        simp [List.append_assoc]
      rw [hword]

 /-- {name}`run_input_bool_word` states the corresponding theorem run form. -/
theorem run_input_bool_word
    (w : Word Bool) (stage : Nat) (result : Word Bool)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionInputBoolWordCost w)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionCodeCells
            (MachineDescription.encodeBoolWordAppend w
              (MachineDescription.encodeNatAppend stage
                (MachineDescription.encodeBoolWord result))))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord w)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeBoolWord result))) := by
  have h :=
    run_input_bool_word_acc
      ([] : Word Bool) w stage result baseLeftRev
  simpa [projectionInputRemainingCost, projectionInputBoolWordCost,
    projectionBoolWordWorkCells_nil_eq_encodeBoolWordAppend] using h

 /-- {name}`run_input_bool_word_acc_suffix` states the corresponding theorem run form. -/
theorem run_input_bool_word_acc_suffix
    (marked rest : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionInputRemainingCost marked rest)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked rest
            (MachineDescription.encodeNatAppend stage suffix))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells
            (MachineDescription.encodeBoolWord
              (List.append marked rest))).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells
          (MachineDescription.encodeNatAppend stage suffix)) := by
  induction rest generalizing marked baseLeftRev with
  | nil =>
      simp [projectionInputRemainingCost]
      exact
        run_input_finish_marked_suffix
          marked stage suffix baseLeftRev
  | cons b rest ih =>
      have hcost :
          projectionInputRemainingCost marked (b :: rest) =
            projectionInputMarkStepCost marked rest +
              projectionInputRemainingCost (List.append marked [b]) rest := by
        simp [projectionInputRemainingCost, projectionInputMarkStepCost,
          Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
        omega
      rw [hcost, MachineDescription.runConfig_add]
      rw [run_input_mark_one]
      rw [ih]
      have hword :
          List.append (List.append marked [b]) rest =
            List.append marked (b :: rest) := by
        simp [List.append_assoc]
      rw [hword]

 /-- {name}`run_input_bool_word_suffix` states the corresponding theorem run form. -/
theorem run_input_bool_word_suffix
    (w : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionInputBoolWordCost w)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionCodeCells
            (MachineDescription.encodeBoolWordAppend w
              (MachineDescription.encodeNatAppend stage suffix)))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord w)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells
          (MachineDescription.encodeNatAppend stage suffix)) := by
  have h :=
    run_input_bool_word_acc_suffix
      ([] : Word Bool) w stage suffix baseLeftRev
  simpa [projectionInputRemainingCost, projectionInputBoolWordCost,
    projectionBoolWordWorkCells_nil_eq_encodeBoolWordAppend] using h

 /-- {name}`run_input_bool_word_acc_false_false_suffix` states the corresponding theorem run form. -/
theorem run_input_bool_word_acc_false_false_suffix
    (marked rest : Word Bool) (suffix : Word MachineCodeSymbol)
    (tail : List (Option Bool))
    (baseLeftRev : List (Option Bool))
    (hsuffix :
      projectionCodeCells suffix = some false :: some false :: tail) :
    Description.runConfig
        (projectionInputRemainingCost marked rest)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked rest suffix)) =
      projectionConfig 200
        (List.append
          (projectionCodeCells
            (MachineDescription.encodeBoolWord
              (List.append marked rest))).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells suffix) := by
  induction rest generalizing marked baseLeftRev with
  | nil =>
      simpa [projectionInputRemainingCost, projectionBoolWordWorkCells,
        projectionResultTailWorkCells, projectionRepeatedCells, hsuffix] using
        run_input_finish_marked_false_false_tail
          marked tail baseLeftRev
  | cons b rest ih =>
      have hcost :
          projectionInputRemainingCost marked (b :: rest) =
            projectionInputMarkStepCost marked rest +
              projectionInputRemainingCost (List.append marked [b]) rest := by
        simp [projectionInputRemainingCost, projectionInputMarkStepCost,
          Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
        omega
      rw [hcost, MachineDescription.runConfig_add]
      rw [run_input_mark_one]
      rw [ih (List.append marked [b]) baseLeftRev]
      have hword :
          List.append (List.append marked [b]) rest =
            List.append marked (b :: rest) := by
        simp [List.append_assoc]
      rw [hword]

 /-- {name}`run_input_bool_word_false_false_suffix` states the corresponding theorem run form. -/
theorem run_input_bool_word_false_false_suffix
    (w : Word Bool) (suffix : Word MachineCodeSymbol)
    (tail : List (Option Bool))
    (baseLeftRev : List (Option Bool))
    (hsuffix :
      projectionCodeCells suffix = some false :: some false :: tail) :
    Description.runConfig
        (projectionInputBoolWordCost w)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionCodeCells
            (MachineDescription.encodeBoolWordAppend w suffix))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord w)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells suffix) := by
  have h :=
    run_input_bool_word_acc_false_false_suffix
      ([] : Word Bool) w suffix tail baseLeftRev hsuffix
  simpa [projectionInputRemainingCost, projectionInputBoolWordCost,
    projectionBoolWordWorkCells_nil_eq_encodeBoolWordAppend] using h

end ControllerStageInputProjection
end Computability
end FoC
