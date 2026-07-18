import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.PairTarget

set_option doc.verso true
set_option maxRecDepth 10000

/-!
# Exact-code validator: selected-pair restoration

Every successful pair comparison uses the same cleanup.  It rewrites temporary
source/target markers back to unary ticks, restores the inner transition token,
and leaves the outer row selected for the next comparison.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

/-- Restore the only temporary unary marker used by pair comparison. -/
def restorePairMarker : ValidatorBlockSymbol -> ValidatorBlockSymbol
  | .marker010 => .tick
  | symbol => symbol

@[simp] private theorem restorePairMarker_marker010 :
    restorePairMarker .marker010 = .tick := rfl

@[simp] private theorem restorePairMarker_tick :
    restorePairMarker .tick = .tick := rfl

@[simp] private theorem restorePairMarker_done :
    restorePairMarker .done = .done := rfl

/-- A row interior during comparison, with independently marked source and
target prefixes. -/
def comparisonRowInterior
    (row : TransitionDescription)
    (sourcePaired sourceRemaining targetPaired targetRemaining : Nat) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate sourcePaired .marker010)
    (List.append (List.replicate sourceRemaining .tick)
      (.done :: ValidatorCountedRows.cellBlock row.read ::
        ValidatorCountedRows.cellBlock row.write ::
        ValidatorCountedRows.directionBlock row.move ::
        List.append (List.replicate targetPaired .marker010)
          (List.replicate targetRemaining .tick)))

/-- Every symbol in a mutable row interior is accepted by cleanup scans. -/
theorem comparisonRowInterior_mem_corridor
    (row : TransitionDescription)
    (sourcePaired sourceRemaining targetPaired targetRemaining : Nat)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        comparisonRowInterior row sourcePaired sourceRemaining
          targetPaired targetRemaining)) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  unfold comparisonRowInterior at hmem
  rcases List.mem_append.mp hmem with hsourceMarked | htail
  · have heq : symbol = .marker010 :=
      (List.mem_replicate.mp hsourceMarked).2
    subst symbol
    exact ValidatorCountedRows.marker010_mem_corridor
  · rcases List.mem_append.mp htail with hsource | hfixed
    · have heq : symbol = .tick := (List.mem_replicate.mp hsource).2
      subst symbol
      exact ValidatorCountedRows.tick_mem_corridor
    · rcases List.mem_cons.mp hfixed with hdone | hfixed
      · subst symbol
        exact ValidatorCountedRows.done_mem_corridor
      · rcases List.mem_cons.mp hfixed with hread | hfixed
        · subst symbol
          exact ValidatorCountedRows.mem_corridor_of_canonical
            (ValidatorCountedRows.cellBlock_mem_canonicalCorridor row.read)
        · rcases List.mem_cons.mp hfixed with hwrite | hfixed
          · subst symbol
            exact ValidatorCountedRows.mem_corridor_of_canonical
              (ValidatorCountedRows.cellBlock_mem_canonicalCorridor row.write)
          · rcases List.mem_cons.mp hfixed with hmove | htarget
            · subst symbol
              exact ValidatorCountedRows.mem_corridor_of_canonical
                (ValidatorCountedRows.directionBlock_mem_canonicalCorridor
                  row.move)
            · rcases List.mem_append.mp htarget with
                htargetMarked | htarget
              · have heq : symbol = .marker010 :=
                  (List.mem_replicate.mp htargetMarked).2
                subst symbol
                exact ValidatorCountedRows.marker010_mem_corridor
              · have heq : symbol = .tick :=
                  (List.mem_replicate.mp htarget).2
                subst symbol
                exact ValidatorCountedRows.tick_mem_corridor

@[simp] private theorem restorePairMarker_cellBlock
    (cell : Option Bool) :
    restorePairMarker (ValidatorCountedRows.cellBlock cell) =
      ValidatorCountedRows.cellBlock cell := by
  cases cell with
  | none => rfl
  | some bit => cases bit <;> rfl

@[simp] private theorem restorePairMarker_directionBlock
    (move : Direction) :
    restorePairMarker (ValidatorCountedRows.directionBlock move) =
      ValidatorCountedRows.directionBlock move := by
  cases move <;> rfl

/-- Cleanup maps a mutable row interior back to its canonical row interior. -/
theorem map_restore_comparisonRowInterior
    (row : TransitionDescription)
    (sourcePaired sourceRemaining targetPaired targetRemaining : Nat)
    (hsource : row.source = sourcePaired + sourceRemaining)
    (htarget : row.target = targetPaired + targetRemaining) :
    List.map restorePairMarker
        (comparisonRowInterior row sourcePaired sourceRemaining
          targetPaired targetRemaining) =
      rowInteriorBlocks row := by
  simp only [comparisonRowInterior]
  simp [rowInteriorBlocks, hsource, htarget]
  rw [← List.append_assoc, List.replicate_append_replicate]

/-- Marker restoration fixes words consisting only of canonical corridor
symbols. -/
theorem map_restore_eq_self_of_canonical
    (word : Word ValidatorBlockSymbol)
    (hword : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from word) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols) :
    List.map restorePairMarker word = word := by
  induction word with
  | nil => rfl
  | cons first rest ih =>
      have hfirst := hword first List.mem_cons_self
      have hrest : forall symbol : ValidatorBlockSymbol,
          symbol ∈ (show List ValidatorBlockSymbol from rest) ->
            symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols := by
        intro symbol hsymbol
        exact hword symbol (List.mem_cons_of_mem first hsymbol)
      have hfirstEq : restorePairMarker first = first := by
        cases first <;>
          simp [restorePairMarker,
            ValidatorCountedRows.canonicalCorridorSymbols] at hfirst ⊢
      simp only [List.map_cons]
      rw [hfirstEq, ih hrest]

private theorem restorePairMarker_mem_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    restorePairMarker symbol ∈ ValidatorCountedRows.corridorSymbols := by
  cases symbol <;>
    simp [restorePairMarker, ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem ⊢

private theorem lookup_state88_restore
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 88 symbol =
      some
        { source := 88, read := symbol, write := restorePairMarker symbol
          move := Direction.left, target := 88 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem lookup_state89_restore
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 89 symbol =
      some
        { source := 89, read := symbol, write := restorePairMarker symbol
          move := Direction.left, target := 89 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem lookup_state90_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 90 symbol =
      some
        { source := 90, read := symbol, write := symbol
          move := Direction.right, target := 90 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

/-- Restore both selected row interiors and the inner transition boundary,
stopping at the first symbol of the restored inner row. -/
theorem reaches_restore_pair_prefix
    {entry : Nat}
    (outerMarked between innerMarked : Word ValidatorBlockSymbol)
    (before rest : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (hentry :
      blockDescription.lookup entry innerEnd =
        some
          { source := entry, read := innerEnd, write := innerEnd
            move := Direction.left, target := 88 })
    (houter : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from
        List.append outerMarked between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (hinner : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from innerMarked) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration entry
          (List.append
            (List.append
              (List.append
                (List.append before [.marker001]) outerMarked) between)
            (List.append [.marker001] innerMarked))
          (innerEnd :: rest))
        (configuration 91
          (List.append
            (List.append
              (List.append before [.marker001])
              (List.map restorePairMarker
                (List.append outerMarked between))) [.transition])
          (List.append (List.map restorePairMarker innerMarked)
            (innerEnd :: rest))) := by
  let outerBetween : Word ValidatorBlockSymbol :=
    List.append outerMarked between
  let restoredOuter : Word ValidatorBlockSymbol :=
    List.map restorePairMarker outerBetween
  let restoredInner : Word ValidatorBlockSymbol :=
    List.map restorePairMarker innerMarked
  let innerBase : Word ValidatorBlockSymbol :=
    List.append (List.append before [.marker001]) outerBetween

  have hinnerRun := reaches_cross_rewrite_left_word
    (boundary := .marker001) innerMarked restorePairMarker hentry
    (fun symbol hsymbol => lookup_state88_restore symbol
      (hinner symbol hsymbol))
    innerBase rest
  have houterRun := reaches_cross_rewrite_left_word outerBetween
    restorePairMarker (entry := 88) (scan := 89)
    (entryRead := .marker001) (entryWrite := .marker001)
    (boundary := .marker001) (by decide)
    (fun symbol hsymbol => lookup_state89_restore symbol
      (houter symbol (by simpa [outerBetween] using hsymbol)))
    before (List.append restoredInner (innerEnd :: rest))
  have houterMarker := reaches_one_right
    (state := 89) (target := 90)
    (read := .marker001) (write := .marker001) (by decide)
    before
    (List.append restoredOuter
      (.marker001 :: List.append restoredInner (innerEnd :: rest)))
  have hreturn := reaches_scan_right_list restoredOuter
    (fun symbol hsymbol => lookup_state90_corridor symbol
      (by
        unfold restoredOuter at hsymbol
        rcases List.mem_map.mp hsymbol with ⟨original, horiginal, rfl⟩
        exact restorePairMarker_mem_corridor original
          (houter original (by simpa [outerBetween] using horiginal))))
    (List.append before [.marker001])
    (.marker001 :: List.append restoredInner (innerEnd :: rest))
  have hinnerMarker := reaches_one_right
    (state := 90) (target := 91)
    (read := .marker001) (write := .transition) (by decide)
    (List.append (List.append before [.marker001]) restoredOuter)
    (List.append restoredInner (innerEnd :: rest))

  have hinnerRun' : blockDescription.Reaches
      (configuration entry
        (List.append innerBase (List.append [.marker001] innerMarked))
        (innerEnd :: rest))
      (configuration 88 innerBase
        (.marker001 :: List.append restoredInner (innerEnd :: rest))) := by
    simpa [restoredInner, List.append_assoc] using hinnerRun
  have houterRun' : blockDescription.Reaches
      (configuration 88 innerBase
        (.marker001 :: List.append restoredInner (innerEnd :: rest)))
      (configuration 89 before
        (.marker001 :: List.append restoredOuter
          (.marker001 :: List.append restoredInner (innerEnd :: rest)))) := by
    simpa [innerBase, outerBetween, restoredOuter, List.append_assoc] using
      houterRun
  have hrun := hinnerRun'.trans (houterRun'.trans
    (houterMarker.trans (hreturn.trans hinnerMarker)))
  simpa [innerBase, outerBetween, restoredOuter, restoredInner,
    List.append_assoc] using hrun

private theorem reaches_scan_right_ticks
    {state : Nat}
    (hlookup :
      blockDescription.lookup state .tick =
        some
          { source := state, read := .tick, write := .tick
            move := Direction.right, target := state })
    (count : Nat) (left rest : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state left
          (List.append (List.replicate count .tick) rest))
        (configuration state
          (List.append left (List.replicate count .tick)) rest) := by
  apply reaches_scan_right_list
  intro symbol hsymbol
  have heq : symbol = .tick := (List.mem_replicate.mp hsymbol).2
  subst symbol
  exact hlookup

/-- Cross a restored inner row and stop on its terminator. -/
theorem reaches_restored_inner_end
    (inner : TransitionDescription)
    (left rest : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 91 left
          (List.append (rowInteriorBlocks inner) (innerEnd :: rest)))
        (configuration 95
          (List.append left (rowInteriorBlocks inner))
          (innerEnd :: rest)) := by
  let sourceTicks : Word ValidatorBlockSymbol :=
    List.replicate inner.source .tick
  let targetTicks : Word ValidatorBlockSymbol :=
    List.replicate inner.target .tick
  have hsource := reaches_scan_right_ticks
    (state := 91) (by decide) inner.source left
    (.done :: ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append targetTicks (innerEnd :: rest))
  have hdone := reaches_one_right
    (state := 91) (target := 92)
    (read := .done) (write := .done) (by decide)
    (List.append left sourceTicks)
    (ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append targetTicks (innerEnd :: rest))
  have hread := reaches_one_right
    (state := 92) (target := 93)
    (read := ValidatorCountedRows.cellBlock inner.read)
    (write := ValidatorCountedRows.cellBlock inner.read)
    (by cases inner.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append (List.append left sourceTicks) [.done])
    (ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append targetTicks (innerEnd :: rest))
  have hwrite := reaches_one_right
    (state := 93) (target := 94)
    (read := ValidatorCountedRows.cellBlock inner.write)
    (write := ValidatorCountedRows.cellBlock inner.write)
    (by cases inner.write with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append (List.append left sourceTicks) [.done])
      [ValidatorCountedRows.cellBlock inner.read])
    (ValidatorCountedRows.directionBlock inner.move ::
      List.append targetTicks (innerEnd :: rest))
  have hmove := reaches_one_right
    (state := 94) (target := 95)
    (read := ValidatorCountedRows.directionBlock inner.move)
    (write := ValidatorCountedRows.directionBlock inner.move)
    (by cases inner.move <;> decide)
    (List.append
      (List.append
        (List.append (List.append left sourceTicks) [.done])
        [ValidatorCountedRows.cellBlock inner.read])
      [ValidatorCountedRows.cellBlock inner.write])
    (List.append targetTicks (innerEnd :: rest))
  have htarget := reaches_scan_right_ticks
    (state := 95) (by decide) inner.target
    (List.append
      (List.append
        (List.append
          (List.append (List.append left sourceTicks) [.done])
          [ValidatorCountedRows.cellBlock inner.read])
        [ValidatorCountedRows.cellBlock inner.write])
      [ValidatorCountedRows.directionBlock inner.move])
    (innerEnd :: rest)
  have hrun := hsource.trans (hdone.trans
    (hread.trans (hwrite.trans (hmove.trans htarget))))
  simpa [rowInteriorBlocks, sourceTicks, targetTicks,
    List.append_assoc] using hrun

/-- A restored ordinary row terminator advances to the next inner row. -/
theorem reaches_restored_inner_done
    (inner : TransitionDescription)
    (left rest : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 91 left
          (List.append (rowInteriorBlocks inner) (.done :: rest)))
        (configuration 3
          (List.append
            (List.append left (rowInteriorBlocks inner)) [.done]) rest) := by
  have hprefix := reaches_restored_inner_end inner left rest .done
  have hdone := reaches_one_right
    (state := 95) (target := 3)
    (read := .done) (write := .done) (by decide)
    (List.append left (rowInteriorBlocks inner)) rest
  exact hprefix.trans hdone

/-- Restoring the final row leaves the sentinel under the state-3 head. -/
theorem reaches_restored_inner_final
    (inner : TransitionDescription)
    (left rest : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 91 left
          (List.append (rowInteriorBlocks inner) (.marker011 :: rest)))
        (configuration 3
          (List.append left (rowInteriorBlocks inner))
          (.marker011 :: rest)) := by
  have hprefix := reaches_restored_inner_end inner left rest .marker011
  cases htarget : inner.target with
  | zero =>
      let beforeLast : Word ValidatorBlockSymbol :=
        List.append left
          (List.append (List.replicate inner.source .tick)
            [.done, ValidatorCountedRows.cellBlock inner.read,
              ValidatorCountedRows.cellBlock inner.write])
      have hleft := reaches_one_left
        (state := 95) (target := 96)
        (read := .marker011) (write := .marker011) (by decide)
        beforeLast rest (ValidatorCountedRows.directionBlock inner.move)
      have hright := reaches_one_right
        (state := 96) (target := 3)
        (read := ValidatorCountedRows.directionBlock inner.move)
        (write := ValidatorCountedRows.directionBlock inner.move)
        (by cases inner.move <;> decide)
        beforeLast (.marker011 :: rest)
      have hfinish := hleft.trans hright
      have hfinish' : blockDescription.Reaches
          (configuration 95 (List.append left (rowInteriorBlocks inner))
            (.marker011 :: rest))
          (configuration 3 (List.append left (rowInteriorBlocks inner))
            (.marker011 :: rest)) := by
        simpa [rowInteriorBlocks, beforeLast, htarget,
          List.append_assoc] using hfinish
      exact hprefix.trans hfinish'
  | succ target =>
      let beforeLast : Word ValidatorBlockSymbol :=
        List.append left
          (List.append
            (List.append (List.replicate inner.source .tick)
              (.done :: ValidatorCountedRows.cellBlock inner.read ::
                ValidatorCountedRows.cellBlock inner.write ::
                ValidatorCountedRows.directionBlock inner.move :: []))
            (List.replicate target .tick))
      have hleft := reaches_one_left
        (state := 95) (target := 96)
        (read := .marker011) (write := .marker011) (by decide)
        beforeLast rest .tick
      have hright := reaches_one_right
        (state := 96) (target := 3)
        (read := .tick) (write := .tick) (by decide)
        beforeLast (.marker011 :: rest)
      have hfinish := hleft.trans hright
      have hfinish' : blockDescription.Reaches
          (configuration 95 (List.append left (rowInteriorBlocks inner))
            (.marker011 :: rest))
          (configuration 3 (List.append left (rowInteriorBlocks inner))
            (.marker011 :: rest)) := by
        simpa [rowInteriorBlocks, beforeLast, htarget,
          List.replicate_succ', List.append_assoc] using hfinish
      exact hprefix.trans hfinish'

/-- Row-level cleanup for an inner row with an ordinary terminator. -/
theorem reaches_restore_selected_pair_done
    {entry : Nat}
    (outer inner : TransitionDescription)
    (outerMarked middle innerMarked : Word ValidatorBlockSymbol)
    (before rest : Word ValidatorBlockSymbol)
    (hentry :
      blockDescription.lookup entry .done =
        some
          { source := entry, read := .done, write := .done
            move := Direction.left, target := 88 })
    (houter : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from
        List.append outerMarked middle) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (hinner : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from innerMarked) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (hrestoreOuter :
      List.map restorePairMarker outerMarked = rowInteriorBlocks outer)
    (hrestoreMiddle : List.map restorePairMarker middle = middle)
    (hrestoreInner :
      List.map restorePairMarker innerMarked = rowInteriorBlocks inner) :
    blockDescription.Reaches
        (configuration entry
          (List.append
            (List.append
              (List.append
                (List.append before [.marker001]) outerMarked) middle)
            (List.append [.marker001] innerMarked))
          (.done :: rest))
        (configuration 3
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append before [.marker001])
                  (rowInteriorBlocks outer)) middle) [.transition])
            (List.append (rowInteriorBlocks inner) [.done]))
          rest) := by
  have hprefix := reaches_restore_pair_prefix outerMarked middle innerMarked
    before rest .done hentry houter hinner
  let restoredLeft : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (List.append
          (List.append before [.marker001]) (rowInteriorBlocks outer)) middle)
      [.transition]
  have hprefix' : blockDescription.Reaches
      (configuration entry
        (List.append
          (List.append
            (List.append
              (List.append before [.marker001]) outerMarked) middle)
          (List.append [.marker001] innerMarked))
        (.done :: rest))
      (configuration 91 restoredLeft
        (List.append (rowInteriorBlocks inner) (.done :: rest))) := by
    simpa [restoredLeft, List.map_append, hrestoreOuter,
      hrestoreMiddle, hrestoreInner, List.append_assoc] using hprefix
  have hfinish := reaches_restored_inner_done inner restoredLeft rest
  simpa [restoredLeft, List.append_assoc] using hprefix'.trans hfinish

/-- Row-level cleanup for the final inner row, retaining its sentinel under
the state-3 head. -/
theorem reaches_restore_selected_pair_final
    {entry : Nat}
    (outer inner : TransitionDescription)
    (outerMarked middle innerMarked : Word ValidatorBlockSymbol)
    (before rest : Word ValidatorBlockSymbol)
    (hentry :
      blockDescription.lookup entry .marker011 =
        some
          { source := entry, read := .marker011, write := .marker011
            move := Direction.left, target := 88 })
    (houter : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from
        List.append outerMarked middle) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (hinner : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from innerMarked) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (hrestoreOuter :
      List.map restorePairMarker outerMarked = rowInteriorBlocks outer)
    (hrestoreMiddle : List.map restorePairMarker middle = middle)
    (hrestoreInner :
      List.map restorePairMarker innerMarked = rowInteriorBlocks inner) :
    blockDescription.Reaches
        (configuration entry
          (List.append
            (List.append
              (List.append
                (List.append before [.marker001]) outerMarked) middle)
            (List.append [.marker001] innerMarked))
          (.marker011 :: rest))
        (configuration 3
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append before [.marker001])
                  (rowInteriorBlocks outer)) middle) [.transition])
            (rowInteriorBlocks inner))
          (.marker011 :: rest)) := by
  have hprefix := reaches_restore_pair_prefix outerMarked middle innerMarked
    before rest .marker011 hentry houter hinner
  let restoredLeft : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (List.append
          (List.append before [.marker001]) (rowInteriorBlocks outer)) middle)
      [.transition]
  have hprefix' : blockDescription.Reaches
      (configuration entry
        (List.append
          (List.append
            (List.append
              (List.append before [.marker001]) outerMarked) middle)
          (List.append [.marker001] innerMarked))
        (.marker011 :: rest))
      (configuration 91 restoredLeft
        (List.append (rowInteriorBlocks inner) (.marker011 :: rest))) := by
    simpa [restoredLeft, List.map_append, hrestoreOuter,
      hrestoreMiddle, hrestoreInner, List.append_assoc] using hprefix
  have hfinish := reaches_restored_inner_final inner restoredLeft rest
  simpa [restoredLeft, List.append_assoc] using hprefix'.trans hfinish

/-- Skip the inner write, move, and target fields after a successful key
mismatch, stopping on the row terminator for shared cleanup. -/
theorem reaches_skip_inner_write_to_end
    (inner : TransitionDescription)
    (left rest : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 85 left
          (ValidatorCountedRows.cellBlock inner.write ::
            ValidatorCountedRows.directionBlock inner.move ::
            List.append (List.replicate inner.target .tick)
              (innerEnd :: rest)))
        (configuration 87
          (List.append
            (List.append left
              [ValidatorCountedRows.cellBlock inner.write,
                ValidatorCountedRows.directionBlock inner.move])
            (List.replicate inner.target .tick))
          (innerEnd :: rest)) := by
  have hwrite := reaches_one_right
    (state := 85) (target := 86)
    (read := ValidatorCountedRows.cellBlock inner.write)
    (write := ValidatorCountedRows.cellBlock inner.write)
    (by cases inner.write with
      | none => decide
      | some bit => cases bit <;> decide)
    left
    (ValidatorCountedRows.directionBlock inner.move ::
      List.append (List.replicate inner.target .tick) (innerEnd :: rest))
  have hmove := reaches_one_right
    (state := 86) (target := 87)
    (read := ValidatorCountedRows.directionBlock inner.move)
    (write := ValidatorCountedRows.directionBlock inner.move)
    (by cases inner.move <;> decide)
    (List.append left [ValidatorCountedRows.cellBlock inner.write])
    (List.append (List.replicate inner.target .tick) (innerEnd :: rest))
  have htarget := reaches_scan_right_ticks
    (state := 87) (by decide) inner.target
    (List.append
      (List.append left [ValidatorCountedRows.cellBlock inner.write])
      [ValidatorCountedRows.directionBlock inner.move])
    (innerEnd :: rest)
  simpa [List.append_assoc] using hwrite.trans (hmove.trans htarget)

/-- Include the inner read field in the successful mismatch skip. -/
theorem reaches_skip_inner_read_to_end
    (inner : TransitionDescription)
    (left rest : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 84 left
          (ValidatorCountedRows.cellBlock inner.read ::
            ValidatorCountedRows.cellBlock inner.write ::
            ValidatorCountedRows.directionBlock inner.move ::
            List.append (List.replicate inner.target .tick)
              (innerEnd :: rest)))
        (configuration 87
          (List.append
            (List.append left
              [ValidatorCountedRows.cellBlock inner.read,
                ValidatorCountedRows.cellBlock inner.write,
                ValidatorCountedRows.directionBlock inner.move])
            (List.replicate inner.target .tick))
          (innerEnd :: rest)) := by
  have hread := reaches_one_right
    (state := 84) (target := 85)
    (read := ValidatorCountedRows.cellBlock inner.read)
    (write := ValidatorCountedRows.cellBlock inner.read)
    (by cases inner.read with
      | none => decide
      | some bit => cases bit <;> decide)
    left
    (ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append (List.replicate inner.target .tick) (innerEnd :: rest))
  have htail := reaches_skip_inner_write_to_end inner
    (List.append left [ValidatorCountedRows.cellBlock inner.read])
    rest innerEnd
  simpa [List.append_assoc] using hread.trans htail

/-- Skip a remaining inner-source suffix before the common action-field skip. -/
theorem reaches_skip_inner_source_to_end
    (inner : TransitionDescription) (remaining : Nat)
    (left rest : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 83 left
          (List.append (List.replicate remaining .tick)
            (.done :: List.append
              (rowAfterSourceBlocks inner innerEnd) rest)))
        (configuration 87
          (List.append
            (List.append left (List.replicate remaining .tick))
            (rowInteriorBlocks { inner with source := 0 }))
          (innerEnd :: rest)) := by
  have hsource := reaches_scan_right_ticks
    (state := 83) (by decide) remaining left
    (.done :: ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append (List.replicate inner.target .tick) (innerEnd :: rest))
  have hdone := reaches_one_right
    (state := 83) (target := 84)
    (read := .done) (write := .done) (by decide)
    (List.append left (List.replicate remaining .tick))
    (ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append (List.replicate inner.target .tick) (innerEnd :: rest))
  have htail := reaches_skip_inner_read_to_end inner
    (List.append
      (List.append left (List.replicate remaining .tick)) [.done])
    rest innerEnd
  simpa [rowAfterSourceBlocks, rowAfterReadBlocks, rowAfterWriteBlocks,
    rowTargetAndEndBlocks, rowInteriorBlocks, List.append_assoc] using
      hsource.trans (hdone.trans htail)

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
