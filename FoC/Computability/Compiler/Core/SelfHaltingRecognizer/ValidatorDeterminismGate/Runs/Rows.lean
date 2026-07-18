import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.Pair

set_option doc.verso true
set_option maxRecDepth 10000

/-!
# Exact-code validator: nested row scans

This module lifts the complete selected-pair theorem through the inner and
outer triangular row scans.  The last row is kept separate because state 0
replaces its final {lit}`done` with {lit}`marker011`.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

private def rowCorridorSymbols : List ValidatorBlockSymbol :=
  [.tick, .done, .blank, .zero, .one, .moveLeft, .moveRight]

private def outerCorridorSymbols : List ValidatorBlockSymbol :=
  .marker001 :: rowCorridorSymbols

private def backCorridorSymbols : List ValidatorBlockSymbol :=
  .transition :: outerCorridorSymbols

private def initialCorridorSymbols : List ValidatorBlockSymbol :=
  .transition :: rowCorridorSymbols

/-- Final row after state 0 has marked the description boundary. -/
def finalRowBlocks (row : TransitionDescription) :
    Word ValidatorBlockSymbol :=
  .transition :: List.append (rowInteriorBlocks row) [.marker011]

private theorem lookup_state2_outer
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ outerCorridorSymbols) :
    blockDescription.lookup 2 symbol =
      some
        { source := 2, read := symbol, write := symbol
          move := Direction.right, target := 2 } := by
  cases symbol <;>
    simp [outerCorridorSymbols, rowCorridorSymbols] at hmem <;> decide

private theorem lookup_state1_initial
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ initialCorridorSymbols) :
    blockDescription.lookup 1 symbol =
      some
        { source := 1, read := symbol, write := symbol
          move := Direction.left, target := 1 } := by
  cases symbol <;>
    simp [initialCorridorSymbols, rowCorridorSymbols] at hmem <;> decide

private theorem lookup_state3_outer
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ rowCorridorSymbols) :
    blockDescription.lookup 3 symbol =
      some
        { source := 3, read := symbol, write := symbol
          move := Direction.right, target := 3 } := by
  cases symbol <;> simp [rowCorridorSymbols] at hmem <;> decide

private theorem lookup_state4_canonical
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols) :
    blockDescription.lookup 4 symbol =
      some
        { source := 4, read := symbol, write := symbol
          move := Direction.left, target := 4 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;> decide

private theorem lookup_state97_back
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ backCorridorSymbols) :
    blockDescription.lookup 97 symbol =
      some
        { source := 97, read := symbol, write := symbol
          move := Direction.left, target := 97 } := by
  cases symbol <;>
    simp [backCorridorSymbols, outerCorridorSymbols,
      rowCorridorSymbols] at hmem <;> decide

private theorem rowInterior_mem_outer
    (row : TransitionDescription) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from rowInteriorBlocks row)) :
    symbol ∈ rowCorridorSymbols := by
  unfold rowInteriorBlocks at hmem
  rcases List.mem_append.mp hmem with hsource | htail
  · have heq : symbol = .tick := (List.mem_replicate.mp hsource).2
    subst symbol
    simp [rowCorridorSymbols]
  · rcases List.mem_cons.mp htail with rfl | htail
    · simp [rowCorridorSymbols]
    · rcases List.mem_cons.mp htail with rfl | htail
      · cases row.read with
        | none => simp [ValidatorCountedRows.cellBlock, rowCorridorSymbols]
        | some bit =>
            cases bit <;>
              simp [ValidatorCountedRows.cellBlock, rowCorridorSymbols]
      · rcases List.mem_cons.mp htail with rfl | htail
        · cases row.write with
          | none => simp [ValidatorCountedRows.cellBlock, rowCorridorSymbols]
          | some bit =>
              cases bit <;>
                simp [ValidatorCountedRows.cellBlock, rowCorridorSymbols]
        · rcases List.mem_cons.mp htail with rfl | htarget
          · cases row.move <;>
              simp [ValidatorCountedRows.directionBlock,
                rowCorridorSymbols]
          · have heq : symbol = .tick :=
              (List.mem_replicate.mp htarget).2
            subst symbol
            simp [rowCorridorSymbols]

private theorem selectedRowBlocks_mem_outer
    (row : TransitionDescription) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from selectedRowBlocks row)) :
    symbol ∈ outerCorridorSymbols := by
  unfold selectedRowBlocks at hmem
  rcases List.mem_cons.mp hmem with rfl | htail
  · simp [outerCorridorSymbols]
  · rcases List.mem_append.mp htail with hrow | hdone
    · exact List.mem_cons_of_mem .marker001
        (rowInterior_mem_outer row symbol hrow)
    · have heq : symbol = .done := List.mem_singleton.mp hdone
      subst symbol
      simp [outerCorridorSymbols, rowCorridorSymbols]

private theorem selectedRowsBlocks_mem_outer
    (rows : List TransitionDescription) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from selectedRowsBlocks rows)) :
    symbol ∈ outerCorridorSymbols := by
  induction rows with
  | nil => simp [selectedRowsBlocks] at hmem
  | cons row rows ih =>
      unfold selectedRowsBlocks at hmem
      rcases List.mem_append.mp hmem with hrow | hrows
      · exact selectedRowBlocks_mem_outer row symbol hrow
      · exact ih hrows

private theorem rowBlocks_mem_back
    (row : TransitionDescription) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from ValidatorCountedRows.rowBlocks row)) :
    symbol ∈ backCorridorSymbols := by
  rw [rowBlocks_eq_transition_cons_interior_append_done] at hmem
  rcases List.mem_cons.mp hmem with rfl | htail
  · simp [backCorridorSymbols]
  · rcases List.mem_append.mp htail with hrow | hdone
    · exact List.mem_cons_of_mem .transition
        (List.mem_cons_of_mem .marker001
          (rowInterior_mem_outer row symbol hrow))
    · have heq : symbol = .done := List.mem_singleton.mp hdone
      subst symbol
      simp [backCorridorSymbols, outerCorridorSymbols, rowCorridorSymbols]

private theorem rowBlocks_mem_initial
    (row : TransitionDescription) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from ValidatorCountedRows.rowBlocks row)) :
    symbol ∈ initialCorridorSymbols := by
  rw [rowBlocks_eq_transition_cons_interior_append_done] at hmem
  rcases List.mem_cons.mp hmem with rfl | htail
  · simp [initialCorridorSymbols]
  · rcases List.mem_append.mp htail with hrow | hdone
    · exact List.mem_cons_of_mem .transition
        (rowInterior_mem_outer row symbol hrow)
    · have heq : symbol = .done := List.mem_singleton.mp hdone
      subst symbol
      simp [initialCorridorSymbols, rowCorridorSymbols]

private theorem rowsBlocks_mem_initial
    (rows : List TransitionDescription) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from ValidatorCountedRows.rowsBlocks rows)) :
    symbol ∈ initialCorridorSymbols := by
  induction rows with
  | nil => simp [ValidatorCountedRows.rowsBlocks] at hmem
  | cons row rows ih =>
      unfold ValidatorCountedRows.rowsBlocks at hmem
      rcases List.mem_append.mp hmem with hrow | hrows
      · exact rowBlocks_mem_initial row symbol hrow
      · exact ih hrows

/-- Select the next inner row and return to the outer source field. -/
theorem reaches_select_inner
    (outer inner : TransitionDescription)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols) :
    blockDescription.Reaches
        (configuration 3
          (List.append
            (List.append
              (List.append before [.marker001]) (rowInteriorBlocks outer))
            (.done :: between))
          (.transition :: List.append (rowInteriorBlocks inner)
            (innerEnd :: rest)))
        (pairStartConfig outer inner before between innerEnd rest) := by
  let corridor : Word ValidatorBlockSymbol :=
    List.append (rowInteriorBlocks outer) (.done :: between)
  have hcorridor : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from corridor) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols := by
    intro symbol hsymbol
    rcases List.mem_append.mp hsymbol with houter | htail
    · exact rowInteriorBlocks_mem_canonicalCorridor outer symbol houter
    · rcases List.mem_cons.mp htail with rfl | hbetween'
      · simp [ValidatorCountedRows.canonicalCorridorSymbols]
      · exact hbetween symbol hbetween'
  have hleft := reaches_cross_scan_left_word corridor
    (entry := 3) (scan := 4)
    (entryRead := .transition) (entryWrite := .marker001)
    (boundary := .marker001) (by decide)
    (fun symbol hsymbol => lookup_state4_canonical symbol
      (hcorridor symbol hsymbol))
    before (List.append (rowInteriorBlocks inner) (innerEnd :: rest))
  have hright := reaches_one_right
    (state := 4) (target := 5)
    (read := .marker001) (write := .marker001) (by decide)
    before
    (List.append corridor
      (.marker001 :: List.append (rowInteriorBlocks inner)
        (innerEnd :: rest)))
  have hrun := hleft.trans hright
  simpa [pairStartConfig, sourcePairRight, corridor, rowInteriorBlocks,
    rowAfterSourceBlocks, rowAfterReadBlocks, rowAfterWriteBlocks,
    rowTargetAndEndBlocks, List.append_assoc] using hrun

/-- After the final inner comparison, scan back to the header and resume the
outer selector with the current outer row still selected. -/
theorem reaches_finish_outer
    (outer last : TransitionDescription)
    (beforeHeader scanPrefix between rest : Word ValidatorBlockSymbol)
    (hprefix : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ backCorridorSymbols) :
    blockDescription.Reaches
        (pairFinalConfig outer last
          (List.append (List.append beforeHeader [.header]) scanPrefix)
          between rest)
        (configuration 2 (List.append beforeHeader [.header])
          (List.append scanPrefix
            (List.append (selectedRowBlocks outer)
              (List.append between
                (List.append (finalRowBlocks last) rest))))) := by
  let corridor : Word ValidatorBlockSymbol :=
    List.append scanPrefix
      (List.append (selectedRowBlocks outer)
        (List.append between
          (.transition :: rowInteriorBlocks last)))
  have hcorridor : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from corridor) ->
        symbol ∈ backCorridorSymbols := by
    intro symbol hsymbol
    rcases List.mem_append.mp hsymbol with hscan | htail
    · exact List.mem_cons_of_mem .transition (hprefix symbol hscan)
    · rcases List.mem_append.mp htail with houter | htail
      · exact List.mem_cons_of_mem .transition
          (selectedRowBlocks_mem_outer outer symbol houter)
      · rcases List.mem_append.mp htail with hmiddle | hlast
        · exact hbetween symbol hmiddle
        · rcases List.mem_cons.mp hlast with rfl | hrow
          · simp [backCorridorSymbols]
          · exact List.mem_cons_of_mem .transition
              (List.mem_cons_of_mem .marker001
                (rowInterior_mem_outer last symbol hrow))
  have hleft := reaches_cross_scan_left_word corridor
    (entry := 3) (scan := 97)
    (entryRead := .marker011) (entryWrite := .marker011)
    (boundary := .header) (by decide)
    (fun symbol hsymbol => lookup_state97_back symbol
      (hcorridor symbol hsymbol))
    beforeHeader rest
  have hright := reaches_one_right
    (state := 97) (target := 2)
    (read := .header) (write := .header) (by decide)
    beforeHeader (List.append corridor (.marker011 :: rest))
  have hrun := hleft.trans hright
  simpa [pairFinalConfig, finalRowBlocks, selectedRowBlocks, corridor,
    List.append_assoc] using hrun

/-- State-3 source with some inner rows already compared and restored. -/
def innerRowsConfig
    (outer : TransitionDescription)
    (beforeHeader scanPrefix between : Word ValidatorBlockSymbol)
    (ordinary : List TransitionDescription)
    (last : TransitionDescription)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration 3
    (List.append
      (List.append
        (List.append
          (List.append (List.append beforeHeader [.header]) scanPrefix)
          [.marker001])
        (rowInteriorBlocks outer))
      (.done :: between))
    (List.append (ValidatorCountedRows.rowsBlocks ordinary)
      (List.append (finalRowBlocks last) rest))

/-- Compare one outer row against an ordinary tail and its distinguished final
row, restoring every successful inner row before continuing. -/
theorem reaches_inner_rows_of_all
    (outer : TransitionDescription)
    (ordinary : List TransitionDescription)
    (last : TransitionDescription)
    (beforeHeader scanPrefix between rest : Word ValidatorBlockSymbol)
    (hprefix : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hbetweenCanonical : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols)
    (hbetweenBack : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ backCorridorSymbols)
    (hall : (ordinary ++ [last]).all
      (fun inner => transitionDeterministicPairBool outer inner) = true) :
    blockDescription.Reaches
        (innerRowsConfig outer beforeHeader scanPrefix between
          ordinary last rest)
        (configuration 2 (List.append beforeHeader [.header])
          (List.append scanPrefix
            (List.append (selectedRowBlocks outer)
              (List.append between
                (List.append (ValidatorCountedRows.rowsBlocks ordinary)
                  (List.append (finalRowBlocks last) rest)))))) := by
  induction ordinary generalizing between with
  | nil =>
      have hlast := List.all_eq_true.mp hall last (by simp)
      have hselect := reaches_select_inner outer last
        (List.append (List.append beforeHeader [.header]) scanPrefix)
        between .marker011 rest hbetweenCanonical
      have hpair := reaches_selected_pair_of_true outer last
        (List.append (List.append beforeHeader [.header]) scanPrefix)
        between .marker011 rest hbetweenCanonical (Or.inr rfl) hlast
      rcases hpair with hdone | hfinal
      · simp at hdone
      · have hfinish := reaches_finish_outer outer last beforeHeader
          scanPrefix between rest hprefix hbetweenBack
        have hrun := hselect.trans (hfinal.2.trans hfinish)
        simpa [innerRowsConfig, finalRowBlocks,
          ValidatorCountedRows.rowsBlocks, List.append_assoc] using hrun
  | cons inner ordinary ih =>
      have hinner := List.all_eq_true.mp hall inner (by simp)
      have htail : (ordinary ++ [last]).all
          (fun row => transitionDeterministicPairBool outer row) = true := by
        apply List.all_eq_true.mpr
        intro row hrow
        exact List.all_eq_true.mp hall row (by simp [hrow])
      let remaining : Word ValidatorBlockSymbol :=
        List.append (ValidatorCountedRows.rowsBlocks ordinary)
          (List.append (finalRowBlocks last) rest)
      have hselect := reaches_select_inner outer inner
        (List.append (List.append beforeHeader [.header]) scanPrefix)
        between .done remaining hbetweenCanonical
      have hpair := reaches_selected_pair_of_true outer inner
        (List.append (List.append beforeHeader [.header]) scanPrefix)
        between .done remaining hbetweenCanonical (Or.inl rfl) hinner
      rcases hpair with hdone | hfinal
      · let between' : Word ValidatorBlockSymbol :=
          List.append between (ValidatorCountedRows.rowBlocks inner)
        have hbetweenCanonical' : forall symbol : ValidatorBlockSymbol,
            symbol ∈ (show List ValidatorBlockSymbol from between') ->
              symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols := by
          intro symbol hsymbol
          rcases List.mem_append.mp hsymbol with hbefore | hrow
          · exact hbetweenCanonical symbol hbefore
          · exact ValidatorCountedRows.canonicalCorridor_rowBlocks
              inner symbol hrow
        have hbetweenBack' : forall symbol : ValidatorBlockSymbol,
            symbol ∈ (show List ValidatorBlockSymbol from between') ->
              symbol ∈ backCorridorSymbols := by
          intro symbol hsymbol
          rcases List.mem_append.mp hsymbol with hbefore | hrow
          · exact hbetweenBack symbol hbefore
          · exact rowBlocks_mem_back inner symbol hrow
        have htailRun := ih between' hbetweenCanonical'
          hbetweenBack' htail
        have hpairRun : blockDescription.Reaches
            (pairStartConfig outer inner
              (List.append (List.append beforeHeader [.header]) scanPrefix)
              between .done remaining)
            (innerRowsConfig outer beforeHeader scanPrefix between'
              ordinary last rest) := by
          simpa [pairDoneConfig, innerRowsConfig, between', remaining,
            rowBlocks_eq_transition_cons_interior_append_done,
            List.append_assoc] using hdone.2
        have hrun := hselect.trans (hpairRun.trans htailRun)
        simpa [innerRowsConfig, between', remaining,
          rowBlocks_eq_transition_cons_interior_append_done,
          ValidatorCountedRows.rowsBlocks, List.append_assoc] using hrun
      · simp at hfinal

/-- If some remaining inner row is incompatible with the selected outer row,
the inner scan reaches the explicit conflict state. -/
theorem reaches_inner_rows_conflict_of_all_false
    (outer : TransitionDescription)
    (ordinary : List TransitionDescription)
    (last : TransitionDescription)
    (beforeHeader scanPrefix between rest : Word ValidatorBlockSymbol)
    (hbetweenCanonical : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols)
    (hall : (ordinary ++ [last]).all
      (fun inner => transitionDeterministicPairBool outer inner) = false) :
    ReachesConflict
      (innerRowsConfig outer beforeHeader scanPrefix between
        ordinary last rest) := by
  induction ordinary generalizing between with
  | nil =>
      have hlast :
          transitionDeterministicPairBool outer last = false := by
        simpa using hall
      have hselect := reaches_select_inner outer last
        (List.append (List.append beforeHeader [.header]) scanPrefix)
        between .marker011 rest hbetweenCanonical
      have hconflict := reaches_selected_pair_of_false outer last
        (List.append (List.append beforeHeader [.header]) scanPrefix)
        between .marker011 rest hbetweenCanonical (Or.inr rfl) hlast
      apply ReachesConflict.of_reaches _ hconflict
      simpa [innerRowsConfig, finalRowBlocks,
        ValidatorCountedRows.rowsBlocks, List.append_assoc] using hselect
  | cons inner ordinary ih =>
      let remaining : Word ValidatorBlockSymbol :=
        List.append (ValidatorCountedRows.rowsBlocks ordinary)
          (List.append (finalRowBlocks last) rest)
      have hselect := reaches_select_inner outer inner
        (List.append (List.append beforeHeader [.header]) scanPrefix)
        between .done remaining hbetweenCanonical
      cases hinner : transitionDeterministicPairBool outer inner with
      | false =>
          have hconflict := reaches_selected_pair_of_false outer inner
            (List.append (List.append beforeHeader [.header]) scanPrefix)
            between .done remaining hbetweenCanonical (Or.inl rfl) hinner
          apply ReachesConflict.of_reaches _ hconflict
          simpa [innerRowsConfig, remaining,
            rowBlocks_eq_transition_cons_interior_append_done,
            ValidatorCountedRows.rowsBlocks, List.append_assoc] using hselect
      | true =>
          have htail : (ordinary ++ [last]).all
              (fun row => transitionDeterministicPairBool outer row) = false := by
            simpa [hinner] using hall
          have hpair := reaches_selected_pair_of_true outer inner
            (List.append (List.append beforeHeader [.header]) scanPrefix)
            between .done remaining hbetweenCanonical (Or.inl rfl) hinner
          rcases hpair with hdone | hfinal
          · let between' : Word ValidatorBlockSymbol :=
              List.append between (ValidatorCountedRows.rowBlocks inner)
            have hbetweenCanonical' : forall symbol : ValidatorBlockSymbol,
                symbol ∈ (show List ValidatorBlockSymbol from between') ->
                  symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols := by
              intro symbol hsymbol
              rcases List.mem_append.mp hsymbol with hbefore | hrow
              · exact hbetweenCanonical symbol hbefore
              · exact ValidatorCountedRows.canonicalCorridor_rowBlocks
                  inner symbol hrow
            have htailConflict := ih between' hbetweenCanonical' htail
            have hpairRun : blockDescription.Reaches
                (pairStartConfig outer inner
                  (List.append (List.append beforeHeader [.header]) scanPrefix)
                  between .done remaining)
                (innerRowsConfig outer beforeHeader scanPrefix between'
                  ordinary last rest) := by
              simpa [pairDoneConfig, innerRowsConfig, between', remaining,
                rowBlocks_eq_transition_cons_interior_append_done,
                List.append_assoc] using hdone.2
            have hfront : blockDescription.Reaches
                (innerRowsConfig outer beforeHeader scanPrefix between
                  (inner :: ordinary) last rest)
                (innerRowsConfig outer beforeHeader scanPrefix between'
                  ordinary last rest) := by
              have hrun := hselect.trans hpairRun
              simpa [innerRowsConfig, remaining,
                rowBlocks_eq_transition_cons_interior_append_done,
                ValidatorCountedRows.rowsBlocks, List.append_assoc] using hrun
            exact ReachesConflict.of_reaches hfront htailConflict
          · simp at hfinal

/-- Select one outer row and position the head at its first inner row. -/
theorem reaches_begin_outer_row
    (outer : TransitionDescription)
    (ordinary : List TransitionDescription)
    (last : TransitionDescription)
    (beforeHeader scanPrefix rest : Word ValidatorBlockSymbol)
    (hprefix : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols) :
    blockDescription.Reaches
        (configuration 2 (List.append beforeHeader [.header])
          (List.append scanPrefix
            (List.append (ValidatorCountedRows.rowBlocks outer)
              (List.append (ValidatorCountedRows.rowsBlocks ordinary)
                (List.append (finalRowBlocks last) rest)))))
        (innerRowsConfig outer beforeHeader scanPrefix []
          ordinary last rest) := by
  have hscan := reaches_scan_right_list scanPrefix
    (fun symbol hsymbol => lookup_state2_outer symbol
      (hprefix symbol hsymbol))
    (List.append beforeHeader [.header])
    (.transition :: List.append (rowInteriorBlocks outer)
      (.done :: List.append (ValidatorCountedRows.rowsBlocks ordinary)
        (List.append (finalRowBlocks last) rest)))
  have hmark := reaches_one_right
    (state := 2) (target := 3)
    (read := .transition) (write := .marker001) (by decide)
    (List.append (List.append beforeHeader [.header]) scanPrefix)
    (List.append (rowInteriorBlocks outer)
      (.done :: List.append (ValidatorCountedRows.rowsBlocks ordinary)
        (List.append (finalRowBlocks last) rest)))
  have houter := reaches_scan_right_list
    (List.append (rowInteriorBlocks outer) [.done])
    (by
      intro symbol hsymbol
      rcases List.mem_append.mp hsymbol with hrow | hdone
      · exact lookup_state3_outer symbol
          (rowInterior_mem_outer outer symbol hrow)
      · have heq : symbol = .done := List.mem_singleton.mp hdone
        subst symbol
        decide)
    (List.append
      (List.append (List.append beforeHeader [.header]) scanPrefix)
      [.marker001])
    (List.append (ValidatorCountedRows.rowsBlocks ordinary)
      (List.append (finalRowBlocks last) rest))
  simp [List.append_assoc] at hscan hmark houter
  have hrun := hscan.trans (hmark.trans houter)
  simpa [innerRowsConfig,
    rowBlocks_eq_transition_cons_interior_append_done,
    List.append_assoc] using hrun

/-- Select one nonfinal outer row, compare it with every later row, and return
to the header-side outer selector. -/
theorem reaches_outer_row_of_all
    (outer : TransitionDescription)
    (ordinary : List TransitionDescription)
    (last : TransitionDescription)
    (beforeHeader scanPrefix rest : Word ValidatorBlockSymbol)
    (hprefix : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hall : (ordinary ++ [last]).all
      (fun inner => transitionDeterministicPairBool outer inner) = true) :
    blockDescription.Reaches
        (configuration 2 (List.append beforeHeader [.header])
          (List.append scanPrefix
            (List.append (ValidatorCountedRows.rowBlocks outer)
              (List.append (ValidatorCountedRows.rowsBlocks ordinary)
                (List.append (finalRowBlocks last) rest)))))
        (configuration 2 (List.append beforeHeader [.header])
          (List.append scanPrefix
            (List.append (selectedRowBlocks outer)
              (List.append (ValidatorCountedRows.rowsBlocks ordinary)
                (List.append (finalRowBlocks last) rest))))) := by
  have hbegin := reaches_begin_outer_row outer ordinary last beforeHeader
    scanPrefix rest hprefix
  have hinner := reaches_inner_rows_of_all outer ordinary last beforeHeader
    scanPrefix [] rest hprefix (by simp) (by simp) hall
  have hrun := hbegin.trans hinner
  simpa [innerRowsConfig, selectedRowBlocks,
    rowBlocks_eq_transition_cons_interior_append_done,
    List.append_assoc] using hrun

/-- If the selected outer row has an incompatible later row, its inner scan
reaches the explicit conflict state. -/
theorem reaches_outer_row_conflict_of_all_false
    (outer : TransitionDescription)
    (ordinary : List TransitionDescription)
    (last : TransitionDescription)
    (beforeHeader scanPrefix rest : Word ValidatorBlockSymbol)
    (hprefix : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hall : (ordinary ++ [last]).all
      (fun inner => transitionDeterministicPairBool outer inner) = false) :
    ReachesConflict
      (configuration 2 (List.append beforeHeader [.header])
        (List.append scanPrefix
          (List.append (ValidatorCountedRows.rowBlocks outer)
            (List.append (ValidatorCountedRows.rowsBlocks ordinary)
              (List.append (finalRowBlocks last) rest))))) := by
  have hbegin := reaches_begin_outer_row outer ordinary last beforeHeader
    scanPrefix rest hprefix
  have hconflict := reaches_inner_rows_conflict_of_all_false outer ordinary
    last beforeHeader scanPrefix [] rest (by simp) hall
  exact ReachesConflict.of_reaches hbegin hconflict

/-- Process every nonfinal outer row of a compatible triangular table. -/
theorem reaches_outer_front_of_upper
    (front : List TransitionDescription)
    (last : TransitionDescription)
    (beforeHeader scanPrefix rest : Word ValidatorBlockSymbol)
    (hprefix : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hupper : transitionUpperPairsBool (front ++ [last]) = true) :
    blockDescription.Reaches
        (configuration 2 (List.append beforeHeader [.header])
          (List.append scanPrefix
            (List.append (ValidatorCountedRows.rowsBlocks front)
              (List.append (finalRowBlocks last) rest))))
        (configuration 2 (List.append beforeHeader [.header])
          (List.append scanPrefix
            (List.append (selectedRowsBlocks front)
              (List.append (finalRowBlocks last) rest)))) := by
  induction front generalizing scanPrefix with
  | nil =>
      simpa [ValidatorCountedRows.rowsBlocks, selectedRowsBlocks] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration 2 (List.append beforeHeader [.header])
            (List.append scanPrefix (List.append (finalRowBlocks last) rest)))
  | cons outer front ih =>
      have hparts :
          (front ++ [last]).all
              (fun inner => transitionDeterministicPairBool outer inner) = true ∧
            transitionUpperPairsBool (front ++ [last]) = true := by
        simpa [transitionUpperPairsBool] using hupper
      have houter := reaches_outer_row_of_all outer front last beforeHeader
        scanPrefix rest hprefix hparts.1
      let scanPrefix' : Word ValidatorBlockSymbol :=
        List.append scanPrefix (selectedRowBlocks outer)
      have hprefix' : forall symbol : ValidatorBlockSymbol,
          symbol ∈ (show List ValidatorBlockSymbol from scanPrefix') ->
            symbol ∈ outerCorridorSymbols := by
        intro symbol hsymbol
        rcases List.mem_append.mp hsymbol with hbefore | hrow
        · exact hprefix symbol hbefore
        · exact selectedRowBlocks_mem_outer outer symbol hrow
      have htail := ih scanPrefix' hprefix' hparts.2
      simp [scanPrefix', List.append_assoc] at houter htail
      have hrun := houter.trans htail
      simpa [scanPrefix', ValidatorCountedRows.rowsBlocks,
        selectedRowsBlocks, List.append_assoc] using hrun

/-- A failed triangular table check reaches conflict while scanning the first
incompatible unordered pair. -/
theorem reaches_outer_front_conflict_of_upper_false
    (front : List TransitionDescription)
    (last : TransitionDescription)
    (beforeHeader scanPrefix rest : Word ValidatorBlockSymbol)
    (hprefix : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hupper : transitionUpperPairsBool (front ++ [last]) = false) :
    ReachesConflict
      (configuration 2 (List.append beforeHeader [.header])
        (List.append scanPrefix
          (List.append (ValidatorCountedRows.rowsBlocks front)
            (List.append (finalRowBlocks last) rest)))) := by
  induction front generalizing scanPrefix with
  | nil =>
      simp [transitionUpperPairsBool] at hupper
  | cons outer front ih =>
      cases hall : (front ++ [last]).all
          (fun inner => transitionDeterministicPairBool outer inner) with
      | false =>
          have hconflict := reaches_outer_row_conflict_of_all_false
            outer front last beforeHeader scanPrefix rest hprefix hall
          simpa [ValidatorCountedRows.rowsBlocks, List.append_assoc] using
            hconflict
      | true =>
          have htail :
              transitionUpperPairsBool (front ++ [last]) = false := by
            simpa [transitionUpperPairsBool, hall] using hupper
          have houter := reaches_outer_row_of_all outer front last beforeHeader
            scanPrefix rest hprefix hall
          let scanPrefix' : Word ValidatorBlockSymbol :=
            List.append scanPrefix (selectedRowBlocks outer)
          have hprefix' : forall symbol : ValidatorBlockSymbol,
              symbol ∈ (show List ValidatorBlockSymbol from scanPrefix') ->
                symbol ∈ outerCorridorSymbols := by
            intro symbol hsymbol
            rcases List.mem_append.mp hsymbol with hbefore | hrow
            · exact hprefix symbol hbefore
            · exact selectedRowBlocks_mem_outer outer symbol hrow
          have htailConflict := ih scanPrefix' hprefix' htail
          have htailConflict' : ReachesConflict
              (configuration 2 (List.append beforeHeader [.header])
                (List.append scanPrefix
                  (List.append (selectedRowBlocks outer)
                    (List.append (ValidatorCountedRows.rowsBlocks front)
                      (List.append (finalRowBlocks last) rest))))) := by
            simpa [scanPrefix', List.append_assoc] using htailConflict
          have hconflict :=
            ReachesConflict.of_reaches houter htailConflict'
          simpa [scanPrefix', ValidatorCountedRows.rowsBlocks,
            List.append_assoc] using hconflict

private def restoreOuterBoundary : ValidatorBlockSymbol -> ValidatorBlockSymbol
  | .marker001 => .transition
  | symbol => symbol

@[simp] private theorem restoreOuterBoundary_marker001 :
    restoreOuterBoundary .marker001 = .transition := rfl

@[simp] private theorem restoreOuterBoundary_tick :
    restoreOuterBoundary .tick = .tick := rfl

@[simp] private theorem restoreOuterBoundary_done :
    restoreOuterBoundary .done = .done := rfl

@[simp] private theorem restoreOuterBoundary_cell
    (cell : Option Bool) :
    restoreOuterBoundary (ValidatorCountedRows.cellBlock cell) =
      ValidatorCountedRows.cellBlock cell := by
  cases cell with
  | none => rfl
  | some bit => cases bit <;> rfl

@[simp] private theorem restoreOuterBoundary_move
    (move : Direction) :
    restoreOuterBoundary (ValidatorCountedRows.directionBlock move) =
      ValidatorCountedRows.directionBlock move := by
  cases move <;> rfl

private theorem map_restoreOuterBoundary_rowInterior
    (row : TransitionDescription) :
    List.map restoreOuterBoundary (rowInteriorBlocks row) =
      rowInteriorBlocks row := by
  simp [rowInteriorBlocks]

private theorem map_restoreOuterBoundary_selectedRows
    (rows : List TransitionDescription) :
    List.map restoreOuterBoundary (selectedRowsBlocks rows) =
      ValidatorCountedRows.rowsBlocks rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [selectedRowsBlocks, selectedRowBlocks,
        ValidatorCountedRows.rowsBlocks,
        rowBlocks_eq_transition_cons_interior_append_done,
        map_restoreOuterBoundary_rowInterior, ih, restoreOuterBoundary,
        List.map_append, List.append_assoc]

private theorem lookup_state98_back
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ backCorridorSymbols) :
    blockDescription.lookup 98 symbol =
      some
        { source := 98, read := symbol, write := symbol
          move := Direction.left, target := 98 } := by
  cases symbol <;>
    simp [backCorridorSymbols, outerCorridorSymbols,
      rowCorridorSymbols] at hmem <;> decide

private theorem lookup_state99_outer
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ outerCorridorSymbols) :
    blockDescription.lookup 99 symbol =
      some
        { source := 99, read := symbol
          write := restoreOuterBoundary symbol
          move := Direction.right, target := 99 } := by
  cases symbol <;>
    simp [outerCorridorSymbols, rowCorridorSymbols] at hmem <;> decide

private theorem reaches_rewrite_right_word
    (symbols : Word ValidatorBlockSymbol)
    (left rest : Word ValidatorBlockSymbol)
    (hlookup : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from symbols) ->
        blockDescription.lookup 99 symbol =
          some
            { source := 99, read := symbol
              write := restoreOuterBoundary symbol
              move := Direction.right, target := 99 }) :
    blockDescription.Reaches
        (configuration 99 left (List.append symbols rest))
        (configuration 99
          (List.append left (List.map restoreOuterBoundary symbols)) rest) := by
  induction symbols generalizing left with
  | nil =>
      simpa using ValidatorBlockDescription.reaches_refl blockDescription
        (configuration 99 left rest)
  | cons symbol symbols ih =>
      have hstep := reaches_one_right
        (hlookup symbol List.mem_cons_self) left
        (List.append symbols rest)
      have htail := ih (List.append left [restoreOuterBoundary symbol])
        (fun item hitem => hlookup item
          (List.mem_cons_of_mem symbol hitem))
      simpa [List.append_assoc] using hstep.trans htail

/-- Restore every selected outer boundary in a corridor and consume the final
description marker into the successful halt state. -/
theorem reaches_restore_outer_corridor_and_halt
    (corridor beforeHeader rest : Word ValidatorBlockSymbol)
    (hcorridor : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from corridor) ->
        symbol ∈ outerCorridorSymbols) :
    blockDescription.Reaches
        (configuration 2 (List.append beforeHeader [.header])
          (List.append corridor (.marker011 :: rest)))
        (configuration 101
          (List.append
            (List.append beforeHeader [.header])
            (List.append (List.map restoreOuterBoundary corridor) [.done]))
          rest) := by
  have hscan := reaches_scan_right_list corridor
    (fun symbol hsymbol => lookup_state2_outer symbol
      (hcorridor symbol hsymbol))
    (List.append beforeHeader [.header]) (.marker011 :: rest)
  have hleft := reaches_cross_scan_left_word corridor
    (entry := 2) (scan := 98)
    (entryRead := .marker011) (entryWrite := .marker011)
    (boundary := .header) (by decide)
    (fun symbol hsymbol => lookup_state98_back symbol
      (by
        simpa [backCorridorSymbols] using
          List.mem_cons_of_mem .transition (hcorridor symbol hsymbol)))
    beforeHeader rest
  have hstart := reaches_one_right
    (state := 98) (target := 99)
    (read := .header) (write := .header) (by decide)
    beforeHeader (List.append corridor (.marker011 :: rest))
  have hrestore := reaches_rewrite_right_word corridor
    (List.append beforeHeader [.header]) (.marker011 :: rest)
    (fun symbol hsymbol => lookup_state99_outer symbol
      (hcorridor symbol hsymbol))
  have hhalt := reaches_one_right
    (state := 99) (target := 101)
    (read := .marker011) (write := .done) (by decide)
    (List.append (List.append beforeHeader [.header])
      (List.map restoreOuterBoundary corridor)) rest
  simpa [List.append_assoc] using
    hscan.trans (hleft.trans (hstart.trans (hrestore.trans hhalt)))

/-- Select the final outer row, restore every outer marker, and halt with the
original canonical row table. -/
theorem reaches_final_outer_and_halt
    (front : List TransitionDescription)
    (last : TransitionDescription)
    (beforeHeader scanPrefix rest : Word ValidatorBlockSymbol)
    (hprefix : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hrestorePrefix :
      List.map restoreOuterBoundary scanPrefix = scanPrefix) :
    blockDescription.Reaches
        (configuration 2 (List.append beforeHeader [.header])
          (List.append scanPrefix
            (List.append (selectedRowsBlocks front)
              (List.append (finalRowBlocks last) rest))))
        (configuration 101
          (List.append
            (List.append (List.append beforeHeader [.header]) scanPrefix)
            (List.append (ValidatorCountedRows.rowsBlocks front)
              (ValidatorCountedRows.rowBlocks last)))
          rest) := by
  let selectedPrefix : Word ValidatorBlockSymbol :=
    List.append scanPrefix (selectedRowsBlocks front)
  let corridor : Word ValidatorBlockSymbol :=
    List.append selectedPrefix
      (.marker001 :: rowInteriorBlocks last)
  have hselected : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from selectedPrefix) ->
        symbol ∈ outerCorridorSymbols := by
    intro symbol hsymbol
    rcases List.mem_append.mp hsymbol with hscan | hrows
    · exact hprefix symbol hscan
    · exact selectedRowsBlocks_mem_outer front symbol hrows
  have hcorridor : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from corridor) ->
        symbol ∈ outerCorridorSymbols := by
    intro symbol hsymbol
    rcases List.mem_append.mp hsymbol with hselected' | htail
    · exact hselected symbol hselected'
    · rcases List.mem_cons.mp htail with rfl | hrow
      · simp [outerCorridorSymbols]
      · exact List.mem_cons_of_mem .marker001
          (rowInterior_mem_outer last symbol hrow)
  have hscan := reaches_scan_right_list selectedPrefix
    (fun symbol hsymbol => lookup_state2_outer symbol
      (hselected symbol hsymbol))
    (List.append beforeHeader [.header])
    (.transition :: List.append (rowInteriorBlocks last)
      (.marker011 :: rest))
  have hmark := reaches_one_right
    (state := 2) (target := 3)
    (read := .transition) (write := .marker001) (by decide)
    (List.append (List.append beforeHeader [.header]) selectedPrefix)
    (List.append (rowInteriorBlocks last) (.marker011 :: rest))
  have hrow := reaches_scan_right_list (rowInteriorBlocks last)
    (fun symbol hsymbol => lookup_state3_outer symbol
      (rowInterior_mem_outer last symbol hsymbol))
    (List.append
      (List.append (List.append beforeHeader [.header]) selectedPrefix)
      [.marker001])
    (.marker011 :: rest)
  have hback := reaches_cross_scan_left_word corridor
    (entry := 3) (scan := 97)
    (entryRead := .marker011) (entryWrite := .marker011)
    (boundary := .header) (by decide)
    (fun symbol hsymbol => lookup_state97_back symbol
      (by
        simpa [backCorridorSymbols] using
          List.mem_cons_of_mem .transition (hcorridor symbol hsymbol)))
    beforeHeader rest
  have hresume := reaches_one_right
    (state := 97) (target := 2)
    (read := .header) (write := .header) (by decide)
    beforeHeader (List.append corridor (.marker011 :: rest))
  have hcleanup := reaches_restore_outer_corridor_and_halt corridor
    beforeHeader rest hcorridor
  simp [corridor, selectedPrefix, List.append_assoc] at hscan hmark hrow hback
  simp [corridor, selectedPrefix, List.append_assoc] at hresume hcleanup
  have hrun := hscan.trans (hmark.trans (hrow.trans
    (hback.trans (hresume.trans hcleanup))))
  simpa [selectedPrefix, corridor, finalRowBlocks, hrestorePrefix,
    map_restoreOuterBoundary_selectedRows,
    map_restoreOuterBoundary_rowInterior,
    rowBlocks_eq_transition_cons_interior_append_done,
    List.map_append, List.append_assoc] using hrun

/-- Complete a compatible nonempty table from the header-side outer selector. -/
theorem reaches_nonempty_table_of_upper
    (front : List TransitionDescription)
    (last : TransitionDescription)
    (beforeHeader scanPrefix rest : Word ValidatorBlockSymbol)
    (hprefix : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hrestorePrefix :
      List.map restoreOuterBoundary scanPrefix = scanPrefix)
    (hupper : transitionUpperPairsBool (front ++ [last]) = true) :
    blockDescription.Reaches
        (configuration 2 (List.append beforeHeader [.header])
          (List.append scanPrefix
            (List.append (ValidatorCountedRows.rowsBlocks front)
              (List.append (finalRowBlocks last) rest))))
        (configuration 101
          (List.append
            (List.append (List.append beforeHeader [.header]) scanPrefix)
            (List.append (ValidatorCountedRows.rowsBlocks front)
              (ValidatorCountedRows.rowBlocks last)))
          rest) := by
  exact (reaches_outer_front_of_upper front last beforeHeader scanPrefix rest
    hprefix hupper).trans
      (reaches_final_outer_and_halt front last beforeHeader scanPrefix rest
        hprefix hrestorePrefix)

/-- An empty transition table restores the marked final header terminator and
halts without entering the pair loop. -/
theorem reaches_empty_table
    (beforeHeader scanPrefix rest : Word ValidatorBlockSymbol)
    (hprefix : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hrestorePrefix :
      List.map restoreOuterBoundary scanPrefix = scanPrefix) :
    blockDescription.Reaches
        (configuration 2 (List.append beforeHeader [.header])
          (List.append scanPrefix (.marker011 :: rest)))
        (configuration 101
          (List.append
            (List.append beforeHeader [.header])
            (List.append scanPrefix [.done]))
          rest) := by
  simpa [hrestorePrefix] using
    reaches_restore_outer_corridor_and_halt scanPrefix beforeHeader rest hprefix

/-- State 0 marks the final terminator and returns to the first block after the
header token. -/
theorem reaches_mark_final_boundary
    (beforeHeader corridor rest : Word ValidatorBlockSymbol)
    (hcorridor : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from corridor) ->
        symbol ∈ initialCorridorSymbols) :
    blockDescription.Reaches
        (configuration 0
          (List.append (List.append beforeHeader [.header]) corridor)
          (.done :: rest))
        (configuration 2 (List.append beforeHeader [.header])
          (List.append corridor (.marker011 :: rest))) := by
  have hleft := reaches_cross_scan_left_word corridor
    (entry := 0) (scan := 1)
    (entryRead := .done) (entryWrite := .marker011)
    (boundary := .header) (by decide)
    (fun symbol hsymbol => lookup_state1_initial symbol
      (hcorridor symbol hsymbol))
    beforeHeader rest
  have hright := reaches_one_right
    (state := 1) (target := 2)
    (read := .header) (write := .header) (by decide)
    beforeHeader (List.append corridor (.marker011 :: rest))
  simpa [List.append_assoc] using hleft.trans hright

/-- Complete a nonempty compatible table from state 0. -/
theorem reaches_nonempty_table_from_start
    (front : List TransitionDescription)
    (last : TransitionDescription)
    (beforeHeader scanPrefix rest : Word ValidatorBlockSymbol)
    (hprefixOuter : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hprefixInitial : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ initialCorridorSymbols)
    (hrestorePrefix :
      List.map restoreOuterBoundary scanPrefix = scanPrefix)
    (hupper : transitionUpperPairsBool (front ++ [last]) = true) :
    blockDescription.Reaches
        (configuration 0
          (List.append
            (List.append (List.append beforeHeader [.header]) scanPrefix)
            (List.append (ValidatorCountedRows.rowsBlocks front)
              (.transition :: rowInteriorBlocks last)))
          (.done :: rest))
        (configuration 101
          (List.append
            (List.append (List.append beforeHeader [.header]) scanPrefix)
            (List.append (ValidatorCountedRows.rowsBlocks front)
              (ValidatorCountedRows.rowBlocks last)))
          rest) := by
  let corridor : Word ValidatorBlockSymbol :=
    List.append scanPrefix
      (List.append (ValidatorCountedRows.rowsBlocks front)
        (.transition :: rowInteriorBlocks last))
  have hcorridor : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from corridor) ->
        symbol ∈ initialCorridorSymbols := by
    intro symbol hsymbol
    rcases List.mem_append.mp hsymbol with hscan | htail
    · exact hprefixInitial symbol hscan
    · rcases List.mem_append.mp htail with hrows | hlast
      · exact rowsBlocks_mem_initial front symbol hrows
      · rcases List.mem_cons.mp hlast with rfl | hrow
        · simp [initialCorridorSymbols]
        · exact List.mem_cons_of_mem .transition
            (rowInterior_mem_outer last symbol hrow)
  have hmark := reaches_mark_final_boundary beforeHeader corridor rest hcorridor
  have htable := reaches_nonempty_table_of_upper front last beforeHeader
    scanPrefix rest hprefixOuter hrestorePrefix hupper
  simp [corridor, finalRowBlocks, List.append_assoc] at hmark htable
  simpa [corridor, finalRowBlocks, List.append_assoc] using hmark.trans htable

/-- Complete the empty-table case from state 0. -/
theorem reaches_empty_table_from_start
    (beforeHeader scanPrefix rest : Word ValidatorBlockSymbol)
    (hprefixOuter : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ outerCorridorSymbols)
    (hprefixInitial : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from scanPrefix) ->
        symbol ∈ initialCorridorSymbols)
    (hrestorePrefix :
      List.map restoreOuterBoundary scanPrefix = scanPrefix) :
    blockDescription.Reaches
        (configuration 0
          (List.append (List.append beforeHeader [.header]) scanPrefix)
          (.done :: rest))
        (configuration 101
          (List.append
            (List.append beforeHeader [.header])
            (List.append scanPrefix [.done]))
          rest) := by
  exact (reaches_mark_final_boundary beforeHeader scanPrefix rest
    hprefixInitial).trans
      (reaches_empty_table beforeHeader scanPrefix rest
        hprefixOuter hrestorePrefix)

/-!
## Canonical encoded-description specializations

The physical proof consumes these wrappers, which discharge the private
corridor invariants for the actual header layouts.
-/

private def completeHeaderTailBlocks
    (stateCount start halt transitionCount : Nat) :
    Word ValidatorBlockSymbol :=
  List.append (ValidatorHeaderBounds.natBlocks stateCount)
    (List.append (ValidatorHeaderBounds.natBlocks start)
      (List.append (ValidatorHeaderBounds.natBlocks halt)
        (ValidatorHeaderBounds.natBlocks transitionCount)))

private def openHeaderTailBlocks
    (stateCount start halt transitionCount : Nat) :
    Word ValidatorBlockSymbol :=
  List.append (ValidatorHeaderBounds.natBlocks stateCount)
    (List.append (ValidatorHeaderBounds.natBlocks start)
      (List.append (ValidatorHeaderBounds.natBlocks halt)
        (List.replicate transitionCount .tick)))

private theorem completeHeaderTailBlocks_mem_corridors
    (stateCount start halt transitionCount : Nat)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ (show List ValidatorBlockSymbol from
      completeHeaderTailBlocks stateCount start halt transitionCount)) :
    symbol ∈ outerCorridorSymbols ∧
      symbol ∈ initialCorridorSymbols := by
  simp [completeHeaderTailBlocks, ValidatorHeaderBounds.natBlocks] at hmem
  rcases hmem with
    ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl |
    ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl <;>
    simp [outerCorridorSymbols, initialCorridorSymbols,
      rowCorridorSymbols]

private theorem openHeaderTailBlocks_mem_corridors
    (stateCount start halt transitionCount : Nat)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ (show List ValidatorBlockSymbol from
      openHeaderTailBlocks stateCount start halt transitionCount)) :
    symbol ∈ outerCorridorSymbols ∧
      symbol ∈ initialCorridorSymbols := by
  simp [openHeaderTailBlocks, ValidatorHeaderBounds.natBlocks] at hmem
  rcases hmem with
    ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl |
    ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ <;>
    simp [outerCorridorSymbols, initialCorridorSymbols,
      rowCorridorSymbols]

private theorem map_restoreOuterBoundary_completeHeaderTailBlocks
    (stateCount start halt transitionCount : Nat) :
    List.map restoreOuterBoundary
        (completeHeaderTailBlocks stateCount start halt transitionCount) =
      completeHeaderTailBlocks stateCount start halt transitionCount := by
  simp [completeHeaderTailBlocks, ValidatorHeaderBounds.natBlocks,
    restoreOuterBoundary, List.map_append]

private theorem map_restoreOuterBoundary_openHeaderTailBlocks
    (stateCount start halt transitionCount : Nat) :
    List.map restoreOuterBoundary
        (openHeaderTailBlocks stateCount start halt transitionCount) =
      openHeaderTailBlocks stateCount start halt transitionCount := by
  simp [openHeaderTailBlocks, ValidatorHeaderBounds.natBlocks,
    restoreOuterBoundary, List.map_append]

/-- A compatible nonempty encoded table reaches the successful logical halt
and restores the complete canonical block sequence. -/
theorem reaches_encoded_nonempty_table_from_start
    (stateCount start halt transitionCount : Nat)
    (front : List TransitionDescription)
    (last : TransitionDescription)
    (rest : Word ValidatorBlockSymbol)
    (hupper : transitionUpperPairsBool (front ++ [last]) = true) :
    blockDescription.Reaches
        (configuration 0
          (List.append
            (ValidatorHeaderBounds.prefixBlocks
              stateCount start halt transitionCount)
            (List.append (ValidatorCountedRows.rowsBlocks front)
              (.transition :: rowInteriorBlocks last)))
          (.done :: rest))
        (configuration 101
          (List.append
            (ValidatorHeaderBounds.prefixBlocks
              stateCount start halt transitionCount)
            (ValidatorCountedRows.rowsBlocks (front ++ [last])))
          rest) := by
  let scanPrefix := completeHeaderTailBlocks
    stateCount start halt transitionCount
  have hrun := reaches_nonempty_table_from_start front last []
    scanPrefix rest
    (fun symbol hsymbol =>
      (completeHeaderTailBlocks_mem_corridors
        stateCount start halt transitionCount symbol hsymbol).1)
    (fun symbol hsymbol =>
      (completeHeaderTailBlocks_mem_corridors
        stateCount start halt transitionCount symbol hsymbol).2)
    (map_restoreOuterBoundary_completeHeaderTailBlocks
      stateCount start halt transitionCount)
    hupper
  rw [ValidatorCountedRows.rowsBlocks_append]
  simpa [scanPrefix, completeHeaderTailBlocks,
    ValidatorHeaderBounds.prefixBlocks,
    ValidatorCountedRows.rowsBlocks,
    rowBlocks_eq_transition_cons_interior_append_done,
    List.append_assoc] using hrun

/-- A failed compatibility check on a nonempty encoded table reaches the
explicit logical conflict state. -/
theorem reaches_encoded_nonempty_table_conflict
    (stateCount start halt transitionCount : Nat)
    (front : List TransitionDescription)
    (last : TransitionDescription)
    (rest : Word ValidatorBlockSymbol)
    (hupper : transitionUpperPairsBool (front ++ [last]) = false) :
    ReachesConflict
      (configuration 0
        (List.append
          (ValidatorHeaderBounds.prefixBlocks
            stateCount start halt transitionCount)
          (List.append (ValidatorCountedRows.rowsBlocks front)
            (.transition :: rowInteriorBlocks last)))
        (.done :: rest)) := by
  let scanPrefix := completeHeaderTailBlocks
    stateCount start halt transitionCount
  let corridor : Word ValidatorBlockSymbol :=
    List.append scanPrefix
      (List.append (ValidatorCountedRows.rowsBlocks front)
        (.transition :: rowInteriorBlocks last))
  have hcorridor : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from corridor) ->
        symbol ∈ initialCorridorSymbols := by
    intro symbol hsymbol
    rcases List.mem_append.mp hsymbol with hscan | htail
    · exact (completeHeaderTailBlocks_mem_corridors
        stateCount start halt transitionCount symbol hscan).2
    · rcases List.mem_append.mp htail with hrows | hlast
      · exact rowsBlocks_mem_initial front symbol hrows
      · rcases List.mem_cons.mp hlast with rfl | hrow
        · simp [initialCorridorSymbols]
        · exact List.mem_cons_of_mem .transition
            (rowInterior_mem_outer last symbol hrow)
  have hmark := reaches_mark_final_boundary [] corridor rest hcorridor
  have hconflict := reaches_outer_front_conflict_of_upper_false
    front last [] scanPrefix rest
    (fun symbol hsymbol =>
      (completeHeaderTailBlocks_mem_corridors
        stateCount start halt transitionCount symbol hsymbol).1)
    hupper
  have hmark' : blockDescription.Reaches
      (configuration 0
        (List.append [.header] corridor) (.done :: rest))
      (configuration 2 [.header]
        (List.append scanPrefix
          (List.append (ValidatorCountedRows.rowsBlocks front)
            (List.append (finalRowBlocks last) rest)))) := by
    simpa [corridor, finalRowBlocks, List.append_assoc] using hmark
  have hrun := ReachesConflict.of_reaches hmark' hconflict
  simpa [scanPrefix, corridor, completeHeaderTailBlocks,
    ValidatorHeaderBounds.prefixBlocks, List.append_assoc] using hrun

/-- The encoded empty table reaches the successful logical halt and restores
the final transition-count terminator. -/
theorem reaches_encoded_empty_table_from_start
    (stateCount start halt transitionCount : Nat)
    (rest : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 0
          (ValidatorHeaderBounds.startLeftBlocks
            stateCount start halt transitionCount)
          (.done :: rest))
        (configuration 101
          (ValidatorHeaderBounds.prefixBlocks
            stateCount start halt transitionCount)
          rest) := by
  let scanPrefix := openHeaderTailBlocks
    stateCount start halt transitionCount
  have hrun := reaches_empty_table_from_start [] scanPrefix rest
    (fun symbol hsymbol =>
      (openHeaderTailBlocks_mem_corridors
        stateCount start halt transitionCount symbol hsymbol).1)
    (fun symbol hsymbol =>
      (openHeaderTailBlocks_mem_corridors
        stateCount start halt transitionCount symbol hsymbol).2)
    (map_restoreOuterBoundary_openHeaderTailBlocks
      stateCount start halt transitionCount)
  simpa [scanPrefix, openHeaderTailBlocks,
    ValidatorHeaderBounds.startLeftBlocks,
    ValidatorHeaderBounds.prefixBlocks,
    ValidatorHeaderBounds.natBlocks,
    List.append_assoc] using hrun

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
