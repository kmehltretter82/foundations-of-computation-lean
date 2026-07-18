import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockMachineInversion
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsRuns

set_option doc.verso true
set_option maxRecDepth 100000

/-!
# Exact-code validator: counted-row field failures

This module records the two arithmetic rejection paths inside a selected
transition row.  Exhausting the state-count field before the source or target
field reaches a missing logical row; the resulting witness is already in the
generated Boolean leaf currency used by closedness.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorCountedRows

open Languages
open MachineDescription

private theorem corridor_mem_leftCorridor
    {middle : Word ValidatorBlockSymbol}
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols)
    (initial final : Word ValidatorBlockSymbol)
    (hinitial : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from initial) ->
        symbol ∈ corridorSymbols)
    (hfinal : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from final) ->
        symbol ∈ corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.append initial
          (.done :: List.append middle (.marker001 :: final)))) :
    symbol ∈ leftCorridorSymbols := by
  rcases List.mem_append.mp hmem with hp | htail
  · exact List.mem_append_left [.marker001] (hinitial symbol hp)
  · rcases List.mem_cons.mp htail with rfl | htail
    · simp [leftCorridorSymbols, corridorSymbols,
        canonicalCorridorSymbols]
    · rcases List.mem_append.mp htail with hm | htail
      · exact List.mem_append_left [.marker001] (hmiddle symbol hm)
      · rcases List.mem_cons.mp htail with rfl | hs
        · simp [leftCorridorSymbols]
        · exact List.mem_append_left [.marker001] (hfinal symbol hs)

private theorem replicate_marker_mem_corridor
    (count : Nat) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.replicate count .marker010)) :
    symbol ∈ corridorSymbols := by
  have heq : symbol = .marker010 := (List.mem_replicate.mp hmem).2
  subst symbol
  simp [corridorSymbols]

private def sourceExhaustedCorridor
    (count : Nat) (middle : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate count .marker010)
    (.done ::
      List.append middle
        (.marker001 :: List.replicate count .marker010))

private theorem sourceExhaustedCorridor_mem_left
    (count : Nat) (middle : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        sourceExhaustedCorridor count middle)) :
    symbol ∈ leftCorridorSymbols := by
  exact corridor_mem_leftCorridor hmiddle
    (List.replicate count .marker010)
    (List.replicate count .marker010)
    (replicate_marker_mem_corridor count)
    (replicate_marker_mem_corridor count) symbol
    (by simpa [sourceExhaustedCorridor] using hmem)

/-- Once all state-count ticks are paired, one additional source tick reaches
the fixed missing row at state 10. -/
def sourceExtraTickStuckWitness
    (stateCount : Nat) (middle remaining : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 8
        (sourcePairLeft 0 stateCount middle) (.tick :: remaining)) := by
  let corridor := sourceExhaustedCorridor stateCount middle
  let tail : Word ValidatorBlockSymbol :=
    List.append middle
      (.marker001 ::
        List.append (List.replicate stateCount .marker010)
          (.marker010 :: remaining))
  have hback := reaches_to_header
    (entry := 8) (scan := 9)
    (entryRead := .tick) (entryWrite := .marker010)
    (Or.inr (Or.inl rfl)) (by decide)
    corridor remaining
    (sourceExhaustedCorridor_mem_left stateCount middle hmiddle)
  have hback' :
      blockDescription.Reaches
        (configuration 8
          (sourcePairLeft 0 stateCount middle) (.tick :: remaining))
        (configuration 9 []
          (.header :: List.append corridor (.marker010 :: remaining))) := by
    simpa [corridor, sourceExhaustedCorridor, sourcePairLeft,
      markedTicks, configuration, List.append_assoc] using hback
  have hheader := reaches_one_right
    (state := 9) (target := 10)
    (read := .header) (write := .header)
    (by decide) []
    (List.append corridor (.marker010 :: remaining))
  have hmarkers := reaches_scan_right_markers
    (state := 10) (by decide) stateCount [.header]
    (.done :: tail)
  have hmarkers' :
      blockDescription.Reaches
        (configuration 10 [.header]
          (List.append corridor (.marker010 :: remaining)))
        (configuration 10
          (List.append [.header]
            (List.replicate stateCount .marker010))
          (.done :: tail)) := by
    simpa [corridor, sourceExhaustedCorridor, tail,
      configuration, List.append_assoc] using hmarkers
  have hrun := hback'.trans (hheader.trans hmarkers')
  exact .leaf
    { logical := 10
      left := List.append [.header]
        (List.replicate stateCount .marker010)
      right := tail
      read := .done
      reaches := by simpa [configuration] using hrun
      logical_lt := by decide
      logical_ne_halt := by decide
      leaf_none := by decide
      leaf_ne_halt := by decide }

/-- A parsed source field at least as large as the state count reaches a
missing generated leaf. -/
def sourceBoundStuckWitness
    (stateCount source : Nat)
    (middle after : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols)
    (hnotBound : ¬ source < stateCount) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 8
        (sourcePairLeft stateCount 0 middle)
        (List.append (List.replicate source .tick) (.done :: after))) := by
  have hle : stateCount ≤ source := by lia
  by_cases heq : source = stateCount
  · subst source
    let corridor := sourceExhaustedCorridor stateCount middle
    let tail : Word ValidatorBlockSymbol :=
      List.append middle
        (.marker001 ::
          List.append (List.replicate stateCount .marker010)
            (.done :: after))
    have hpairs := reaches_pair_all_source_ticks
      0 stateCount 0 middle (.done :: after) hmiddle
    have hpairs' :
        blockDescription.Reaches
          (configuration 8
            (sourcePairLeft stateCount 0 middle)
            (List.append (List.replicate stateCount .tick)
              (.done :: after)))
          (configuration 8 (.header :: corridor) (.done :: after)) := by
      simpa [corridor, sourceExhaustedCorridor, sourcePairLeft,
        markedTicks, configuration, List.append_assoc] using hpairs
    have hback := reaches_to_header
      (entry := 8) (scan := 12)
      (entryRead := .done) (entryWrite := .done)
      (Or.inr (Or.inr (Or.inl rfl))) (by decide)
      corridor after
      (sourceExhaustedCorridor_mem_left stateCount middle hmiddle)
    have hheader := reaches_one_right
      (state := 12) (target := 13)
      (read := .header) (write := .header)
      (by decide) []
      (List.append corridor (.done :: after))
    have hmarkers := reaches_scan_right_markers
      (state := 13) (by decide) stateCount [.header]
      (.done :: tail)
    have hmarkers' :
        blockDescription.Reaches
          (configuration 13 [.header]
            (List.append corridor (.done :: after)))
          (configuration 13
            (List.append [.header]
              (List.replicate stateCount .marker010))
            (.done :: tail)) := by
      simpa [corridor, sourceExhaustedCorridor, tail,
        configuration, List.append_assoc] using hmarkers
    have hrun := hpairs'.trans
      (hback.trans (hheader.trans hmarkers'))
    exact .leaf
      { logical := 13
        left := List.append [.header]
          (List.replicate stateCount .marker010)
        right := tail
        read := .done
        reaches := by
          simpa [configuration, corridor, sourceExhaustedCorridor,
            tail, List.append_assoc] using hrun
        logical_lt := by decide
        logical_ne_halt := by decide
        leaf_none := by decide
        leaf_ne_halt := by decide }
  · let extra := source - (stateCount + 1)
    have hdecomp : source = stateCount + (extra + 1) := by
      dsimp [extra]
      lia
    let corridor := sourceExhaustedCorridor stateCount middle
    let remaining : Word ValidatorBlockSymbol :=
      List.append (List.replicate extra .tick) (.done :: after)
    let tail : Word ValidatorBlockSymbol :=
      List.append middle
        (.marker001 ::
          List.append (List.replicate stateCount .marker010)
            (.marker010 :: remaining))
    have hpairs := reaches_pair_all_source_ticks
      0 stateCount 0 middle
      (List.append (List.replicate (extra + 1) .tick) (.done :: after))
      hmiddle
    have hpairs' :
        blockDescription.Reaches
          (configuration 8
            (sourcePairLeft stateCount 0 middle)
            (List.append (List.replicate source .tick) (.done :: after)))
          (configuration 8 (.header :: corridor) (.tick :: remaining)) := by
      simpa [hdecomp, corridor, sourceExhaustedCorridor, remaining,
        sourcePairLeft, markedTicks, configuration,
        List.replicate_succ, list_replicate_add_append,
        List.append_assoc] using hpairs
    have hback := reaches_to_header
      (entry := 8) (scan := 9)
      (entryRead := .tick) (entryWrite := .marker010)
      (Or.inr (Or.inl rfl)) (by decide)
      corridor remaining
      (sourceExhaustedCorridor_mem_left stateCount middle hmiddle)
    have hheader := reaches_one_right
      (state := 9) (target := 10)
      (read := .header) (write := .header)
      (by decide) []
      (List.append corridor (.marker010 :: remaining))
    have hmarkers := reaches_scan_right_markers
      (state := 10) (by decide) stateCount [.header]
      (.done :: tail)
    have hmarkers' :
        blockDescription.Reaches
          (configuration 10 [.header]
            (List.append corridor (.marker010 :: remaining)))
          (configuration 10
            (List.append [.header]
              (List.replicate stateCount .marker010))
            (.done :: tail)) := by
      simpa [corridor, sourceExhaustedCorridor, remaining, tail,
        configuration, List.append_assoc] using hmarkers
    have hrun := hpairs'.trans
      (hback.trans (hheader.trans hmarkers'))
    exact .leaf
      { logical := 10
        left := List.append [.header]
          (List.replicate stateCount .marker010)
        right := tail
        read := .done
        reaches := by
          simpa [configuration, corridor, sourceExhaustedCorridor,
            remaining, tail, List.replicate_succ, List.append_assoc]
            using hrun
        logical_lt := by decide
        logical_ne_halt := by decide
        leaf_none := by decide
        leaf_ne_halt := by decide }

private def targetExhaustedCorridor
    (count : Nat) (row : TransitionDescription)
    (middle : Word ValidatorBlockSymbol) : Word ValidatorBlockSymbol :=
  List.append (List.replicate count .marker010)
    (.done ::
      List.append middle
        (.marker001 ::
          List.append (List.replicate row.source .tick)
            (.done ::
              cellBlock row.read :: cellBlock row.write ::
                directionBlock row.move ::
                  List.replicate count .marker010)))

private theorem targetExhaustedCorridor_mem_left
    (count : Nat) (row : TransitionDescription)
    (middle : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        targetExhaustedCorridor count row middle)) :
    symbol ∈ leftCorridorSymbols := by
  unfold targetExhaustedCorridor at hmem
  rcases List.mem_append.mp hmem with hstate | htail
  · exact List.mem_append_left [.marker001]
      (replicate_marker_mem_corridor count symbol hstate)
  · rcases List.mem_cons.mp htail with rfl | htail
    · simp [leftCorridorSymbols, corridorSymbols,
        canonicalCorridorSymbols]
    · rcases List.mem_append.mp htail with hm | htail
      · exact List.mem_append_left [.marker001] (hmiddle symbol hm)
      · rcases List.mem_cons.mp htail with rfl | htail
        · simp [leftCorridorSymbols]
        · rcases List.mem_append.mp htail with hsource | htail
          · have heq : symbol = .tick :=
              (List.mem_replicate.mp hsource).2
            subst symbol
            simp [leftCorridorSymbols, corridorSymbols,
              canonicalCorridorSymbols]
          · rcases List.mem_cons.mp htail with rfl | htail
            · simp [leftCorridorSymbols, corridorSymbols,
                canonicalCorridorSymbols]
            · rcases List.mem_cons.mp htail with hread | htail
              · subst symbol
                cases row.read with
                | none =>
                    simp [cellBlock, leftCorridorSymbols, corridorSymbols,
                      canonicalCorridorSymbols]
                | some bit =>
                    cases bit <;>
                      simp [cellBlock, leftCorridorSymbols, corridorSymbols,
                        canonicalCorridorSymbols]
              · rcases List.mem_cons.mp htail with hwrite | htail
                · subst symbol
                  cases row.write with
                  | none =>
                      simp [cellBlock, leftCorridorSymbols, corridorSymbols,
                        canonicalCorridorSymbols]
                  | some bit =>
                      cases bit <;>
                        simp [cellBlock, leftCorridorSymbols, corridorSymbols,
                          canonicalCorridorSymbols]
                · rcases List.mem_cons.mp htail with hmove | hmarkers
                  · subst symbol
                    cases row.move <;>
                      simp [directionBlock, leftCorridorSymbols,
                        corridorSymbols, canonicalCorridorSymbols]
                  · exact List.mem_append_left [.marker001]
                      (replicate_marker_mem_corridor count symbol hmarkers)

/-- Once all state-count ticks are paired, one additional target tick reaches
the fixed missing row at state 22. -/
def targetExtraTickStuckWitness
    (stateCount : Nat) (row : TransitionDescription)
    (middle remaining : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 20
        (targetPairLeft 0 stateCount row middle) (.tick :: remaining)) := by
  let corridor := targetExhaustedCorridor stateCount row middle
  let tail : Word ValidatorBlockSymbol :=
    List.append middle
      (.marker001 ::
        List.append (List.replicate row.source .tick)
          (.done ::
            cellBlock row.read :: cellBlock row.write ::
              directionBlock row.move ::
                List.append (List.replicate stateCount .marker010)
                  (.marker010 :: remaining)))
  have hback := reaches_to_header
    (entry := 20) (scan := 21)
    (entryRead := .tick) (entryWrite := .marker010)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide)
    corridor remaining
    (targetExhaustedCorridor_mem_left stateCount row middle hmiddle)
  have hback' :
      blockDescription.Reaches
        (configuration 20
          (targetPairLeft 0 stateCount row middle) (.tick :: remaining))
        (configuration 21 []
          (.header :: List.append corridor (.marker010 :: remaining))) := by
    simpa [corridor, targetExhaustedCorridor, targetPairLeft,
      markedTicks, configuration, List.append_assoc] using hback
  have hheader := reaches_one_right
    (state := 21) (target := 22)
    (read := .header) (write := .header)
    (by decide) []
    (List.append corridor (.marker010 :: remaining))
  have hmarkers := reaches_scan_right_markers
    (state := 22) (by decide) stateCount [.header]
    (.done :: tail)
  have hmarkers' :
      blockDescription.Reaches
        (configuration 22 [.header]
          (List.append corridor (.marker010 :: remaining)))
        (configuration 22
          (List.append [.header]
            (List.replicate stateCount .marker010))
          (.done :: tail)) := by
    simpa [corridor, targetExhaustedCorridor, tail,
      configuration, List.append_assoc] using hmarkers
  have hrun := hback'.trans (hheader.trans hmarkers')
  exact .leaf
    { logical := 22
      left := List.append [.header]
        (List.replicate stateCount .marker010)
      right := tail
      read := .done
      reaches := by simpa [configuration] using hrun
      logical_lt := by decide
      logical_ne_halt := by decide
      leaf_none := by decide
      leaf_ne_halt := by decide }

/-- A parsed target field at least as large as the state count reaches a
missing generated leaf. -/
def targetBoundStuckWitness
    (stateCount : Nat) (row : TransitionDescription)
    (middle after : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols)
    (hnotBound : ¬ row.target < stateCount) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 20
        (targetPairLeft stateCount 0 row middle)
        (List.append (List.replicate row.target .tick) (.done :: after))) := by
  have hle : stateCount ≤ row.target := by lia
  by_cases heq : row.target = stateCount
  · have htarget : row.target = stateCount := heq
    rw [htarget]
    let corridor := targetExhaustedCorridor stateCount row middle
    let tail : Word ValidatorBlockSymbol :=
      List.append middle
        (.marker001 ::
          List.append (List.replicate row.source .tick)
            (.done ::
              cellBlock row.read :: cellBlock row.write ::
                directionBlock row.move ::
                  List.append (List.replicate stateCount .marker010)
                    (.done :: after)))
    have hpairs := reaches_pair_all_target_ticks
      0 stateCount 0 row middle (.done :: after) hmiddle
    have hpairs' :
        blockDescription.Reaches
          (configuration 20
            (targetPairLeft stateCount 0 row middle)
            (List.append (List.replicate stateCount .tick)
              (.done :: after)))
          (configuration 20 (.header :: corridor) (.done :: after)) := by
      simpa [corridor, targetExhaustedCorridor, targetPairLeft,
        markedTicks, configuration, List.append_assoc] using hpairs
    have hback := reaches_to_header
      (entry := 20) (scan := 28)
      (entryRead := .done) (entryWrite := .done)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by decide)
      corridor after
      (targetExhaustedCorridor_mem_left
        stateCount row middle hmiddle)
    have hheader := reaches_one_right
      (state := 28) (target := 29)
      (read := .header) (write := .header)
      (by decide) []
      (List.append corridor (.done :: after))
    have hmarkers := reaches_scan_right_markers
      (state := 29) (by decide) stateCount [.header]
      (.done :: tail)
    have hmarkers' :
        blockDescription.Reaches
          (configuration 29 [.header]
            (List.append corridor (.done :: after)))
          (configuration 29
            (List.append [.header]
              (List.replicate stateCount .marker010))
            (.done :: tail)) := by
      simpa [corridor, targetExhaustedCorridor, tail,
        configuration, List.append_assoc] using hmarkers
    have hrun := hpairs'.trans
      (hback.trans (hheader.trans hmarkers'))
    exact .leaf
      { logical := 29
        left := List.append [.header]
          (List.replicate stateCount .marker010)
        right := tail
        read := .done
        reaches := by
          simpa [configuration, corridor, targetExhaustedCorridor,
            tail, List.append_assoc] using hrun
        logical_lt := by decide
        logical_ne_halt := by decide
        leaf_none := by decide
        leaf_ne_halt := by decide }
  · let extra := row.target - (stateCount + 1)
    have hdecomp : row.target = stateCount + (extra + 1) := by
      dsimp [extra]
      lia
    let corridor := targetExhaustedCorridor stateCount row middle
    let remaining : Word ValidatorBlockSymbol :=
      List.append (List.replicate extra .tick) (.done :: after)
    let tail : Word ValidatorBlockSymbol :=
      List.append middle
        (.marker001 ::
          List.append (List.replicate row.source .tick)
            (.done ::
              cellBlock row.read :: cellBlock row.write ::
                directionBlock row.move ::
                  List.append (List.replicate stateCount .marker010)
                    (.marker010 :: remaining)))
    have hpairs := reaches_pair_all_target_ticks
      0 stateCount 0 row middle
      (List.append (List.replicate (extra + 1) .tick) (.done :: after))
      hmiddle
    have hpairs' :
        blockDescription.Reaches
          (configuration 20
            (targetPairLeft stateCount 0 row middle)
            (List.append (List.replicate row.target .tick)
              (.done :: after)))
          (configuration 20 (.header :: corridor) (.tick :: remaining)) := by
      simpa [hdecomp, corridor, targetExhaustedCorridor, remaining,
        targetPairLeft, markedTicks, configuration,
        List.replicate_succ, list_replicate_add_append,
        List.append_assoc] using hpairs
    have hback := reaches_to_header
      (entry := 20) (scan := 21)
      (entryRead := .tick) (entryWrite := .marker010)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide)
      corridor remaining
      (targetExhaustedCorridor_mem_left
        stateCount row middle hmiddle)
    have hheader := reaches_one_right
      (state := 21) (target := 22)
      (read := .header) (write := .header)
      (by decide) []
      (List.append corridor (.marker010 :: remaining))
    have hmarkers := reaches_scan_right_markers
      (state := 22) (by decide) stateCount [.header]
      (.done :: tail)
    have hmarkers' :
        blockDescription.Reaches
          (configuration 22 [.header]
            (List.append corridor (.marker010 :: remaining)))
          (configuration 22
            (List.append [.header]
              (List.replicate stateCount .marker010))
            (.done :: tail)) := by
      simpa [corridor, targetExhaustedCorridor, remaining, tail,
        configuration, List.append_assoc] using hmarkers
    have hrun := hpairs'.trans
      (hback.trans (hheader.trans hmarkers'))
    exact .leaf
      { logical := 22
        left := List.append [.header]
          (List.replicate stateCount .marker010)
        right := tail
        read := .done
        reaches := by
          simpa [configuration, corridor, targetExhaustedCorridor,
            remaining, tail, List.replicate_succ, List.append_assoc]
            using hrun
        logical_lt := by decide
        logical_ne_halt := by decide
        leaf_none := by decide
        leaf_ne_halt := by decide }

end ValidatorCountedRows
end SelfHaltingRecognizer
end Computability
end FoC
