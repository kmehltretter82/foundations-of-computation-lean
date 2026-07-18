import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.Restore

set_option doc.verso true
set_option maxRecDepth 10000

/-!
# Exact-code validator: complete selected-pair run

This module joins source-key comparison, action comparison, conflict, and the
shared restoration pass into one selected-pair contract.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

private theorem lookup_compare_read_ne
    (expected actual : Option Bool) (hne : expected ≠ actual) :
    blockDescription.lookup (compareInnerReadState expected)
        (ValidatorCountedRows.cellBlock actual) =
      some
        { source := compareInnerReadState expected
          read := ValidatorCountedRows.cellBlock actual
          write := ValidatorCountedRows.cellBlock actual
          move := Direction.right
          target := 85 } := by
  cases expected with
  | none =>
      cases actual with
      | none => simp at hne
      | some bit => cases bit <;> decide
  | some expectedBit =>
      cases expectedBit with
      | false =>
          cases actual with
          | none => decide
          | some actualBit =>
              cases actualBit with
              | false => simp at hne
              | true => decide
      | true =>
          cases actual with
          | none => decide
          | some actualBit =>
              cases actualBit with
              | false => decide
              | true => simp at hne

private def sourceComparisonMiddle
    (outer : TransitionDescription)
    (between : Word ValidatorBlockSymbol) : Word ValidatorBlockSymbol :=
  List.append (rowAfterSourceBlocks outer .done) between

private def sourceComparisonAfter
    (inner : TransitionDescription) (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) : Word ValidatorBlockSymbol :=
  List.append (rowAfterSourceBlocks inner innerEnd) rest

private theorem sourceComparisonMiddle_mem_corridor
    (outer : TransitionDescription)
    (between : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        sourceComparisonMiddle outer between)) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  unfold sourceComparisonMiddle at hmem
  rcases List.mem_append.mp hmem with hrow | hbetween'
  · unfold rowAfterSourceBlocks rowAfterReadBlocks rowAfterWriteBlocks
      rowTargetAndEndBlocks at hrow
    simp only [List.mem_cons] at hrow
    rcases hrow with hread | hwrite | hmove | htarget
    · subst symbol
      exact ValidatorCountedRows.mem_corridor_of_canonical
        (ValidatorCountedRows.cellBlock_mem_canonicalCorridor outer.read)
    · subst symbol
      exact ValidatorCountedRows.mem_corridor_of_canonical
        (ValidatorCountedRows.cellBlock_mem_canonicalCorridor outer.write)
    · subst symbol
      exact ValidatorCountedRows.mem_corridor_of_canonical
        (ValidatorCountedRows.directionBlock_mem_canonicalCorridor outer.move)
    · rcases List.mem_append.mp htarget with htick | hdone
      · have heq : symbol = .tick := (List.mem_replicate.mp htick).2
        subst symbol
        exact ValidatorCountedRows.tick_mem_corridor
      · have heq : symbol = .done := List.mem_singleton.mp hdone
        subst symbol
        exact ValidatorCountedRows.done_mem_corridor
  · exact hbetween symbol hbetween'

/-- Common restoration layout after a selected pair has been fully traversed. -/
def pairCleanupConfig
    (entry : Nat)
    (outer inner : TransitionDescription)
    (outerSourcePaired outerSourceRemaining
      outerTargetPaired outerTargetRemaining : Nat)
    (innerSourcePaired innerSourceRemaining
      innerTargetPaired innerTargetRemaining : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration entry
    (List.append
      (List.append
        (List.append
          (List.append before [.marker001])
          (comparisonRowInterior outer outerSourcePaired outerSourceRemaining
            outerTargetPaired outerTargetRemaining))
        (.done :: between))
      (List.append [.marker001]
        (comparisonRowInterior inner innerSourcePaired innerSourceRemaining
          innerTargetPaired innerTargetRemaining)))
    (innerEnd :: rest)

/-- State-87 layout after a source-length mismatch has skipped the remaining
inner row fields. -/
def sourceMismatchEndConfig
    (outer inner : TransitionDescription)
    (outerPaired outerRemaining innerPaired innerRemaining : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  pairCleanupConfig 87 outer inner
    outerPaired outerRemaining 0 outer.target
    innerPaired innerRemaining 0 inner.target
    before between innerEnd rest

/-- With no inner source tick left, marking one more outer tick and probing the
inner source terminator reaches the common cleanup entry. -/
theorem reaches_outer_longer_source_to_end
    (outer inner : TransitionDescription)
    (paired outerRemaining : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 5 (List.append before [.marker001])
          (sourcePairRight (outerRemaining + 1) 0 paired
            (sourceComparisonMiddle outer between)
            (sourceComparisonAfter inner innerEnd rest)))
        (sourceMismatchEndConfig outer inner (paired + 1) outerRemaining
          paired 0 before between innerEnd rest) := by
  let markers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let outerRest : Word ValidatorBlockSymbol :=
    List.append (List.replicate outerRemaining .tick)
      (.done :: sourceComparisonMiddle outer between)
  let innerAfter := sourceComparisonAfter inner innerEnd rest
  let base : Word ValidatorBlockSymbol := List.append before [.marker001]
  have hmarkers := reaches_scan_right_markers
    (state := 5) (by decide) paired base
    (.tick :: List.append outerRest
      (.marker001 :: List.append markers (.done :: innerAfter)))
  have houterTick := reaches_one_right
    (state := 5) (target := 6)
    (read := .tick) (write := .marker010) (by decide)
    (List.append base markers)
    (List.append outerRest
      (.marker001 :: List.append markers (.done :: innerAfter)))
  have houterRest := reaches_scan_right_list outerRest
    (fun symbol hsymbol => lookup_state6_corridor symbol
      (sourcePairCorridor_mem outerRemaining 0
        (sourceComparisonMiddle outer between)
        (sourceComparisonMiddle_mem_corridor outer between hbetween)
        symbol (by simpa [outerRest] using hsymbol)))
    (List.append (List.append base markers) [.marker010])
    (.marker001 :: List.append markers (.done :: innerAfter))
  have hinnerMarker := reaches_one_right
    (state := 6) (target := 7)
    (read := .marker001) (write := .marker001) (by decide)
    (List.append
      (List.append (List.append base markers) [.marker010]) outerRest)
    (List.append markers (.done :: innerAfter))
  have hinnerMarkers := reaches_scan_right_markers
    (state := 7) (by decide) paired
    (List.append
      (List.append
        (List.append (List.append base markers) [.marker010]) outerRest)
      [.marker001])
    (.done :: innerAfter)
  have hinnerDone := reaches_one_right
    (state := 7) (target := 84)
    (read := .done) (write := .done) (by decide)
    (List.append
      (List.append
        (List.append
          (List.append (List.append base markers) [.marker010]) outerRest)
        [.marker001]) markers)
    (sourceComparisonAfter inner innerEnd rest)
  have hskip := reaches_skip_inner_read_to_end inner
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append (List.append base markers) [.marker010]) outerRest)
          [.marker001]) markers) [.done])
    rest innerEnd
  have hskip' : blockDescription.Reaches
      (configuration 84
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append (List.append base markers) [.marker010]) outerRest)
              [.marker001]) markers) [.done])
        (sourceComparisonAfter inner innerEnd rest))
      (sourceMismatchEndConfig outer inner (paired + 1) outerRemaining
        paired 0 before between innerEnd rest) := by
    simpa [sourceMismatchEndConfig, pairCleanupConfig, sourceComparisonMiddle,
      sourceComparisonAfter, comparisonRowInterior, markers, outerRest, base,
      rowAfterSourceBlocks, rowAfterReadBlocks, rowAfterWriteBlocks,
      rowTargetAndEndBlocks,
      List.replicate_succ', List.append_assoc] using hskip
  have hrun := hmarkers.trans (houterTick.trans
    (houterRest.trans (hinnerMarker.trans
      (hinnerMarkers.trans (hinnerDone.trans hskip')))))
  simpa [sourcePairRight, sourceMismatchEndConfig, pairCleanupConfig,
    sourceComparisonMiddle, sourceComparisonAfter,
    comparisonRowInterior, markers, outerRest, innerAfter, base,
    List.replicate_succ, List.replicate_succ', List.append_assoc] using hrun

/-- With the outer source exhausted, the first remaining inner tick selects the
successful key-mismatch skip and reaches the common cleanup entry. -/
theorem reaches_inner_longer_source_to_end
    (outer inner : TransitionDescription)
    (paired innerRemaining : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 5 (List.append before [.marker001])
          (sourcePairRight 0 (innerRemaining + 1) paired
            (sourceComparisonMiddle outer between)
            (sourceComparisonAfter inner innerEnd rest)))
        (sourceMismatchEndConfig outer inner paired 0 paired
          (innerRemaining + 1) before between innerEnd rest) := by
  let markers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let middle := sourceComparisonMiddle outer between
  let innerAfter := sourceComparisonAfter inner innerEnd rest
  let base : Word ValidatorBlockSymbol := List.append before [.marker001]
  have hmarkers := reaches_scan_right_markers
    (state := 5) (by decide) paired base
    (.done :: List.append middle
      (.marker001 :: List.append markers
        (.tick :: List.append (List.replicate innerRemaining .tick)
          (.done :: innerAfter))))
  have houterDone := reaches_one_right
    (state := 5) (target := 10)
    (read := .done) (write := .done) (by decide)
    (List.append base markers)
    (List.append middle
      (.marker001 :: List.append markers
        (.tick :: List.append (List.replicate innerRemaining .tick)
          (.done :: innerAfter))))
  have hmiddle := reaches_scan_right_list middle
    (fun symbol hsymbol => lookup_state10_corridor symbol
      (sourceComparisonMiddle_mem_corridor outer between hbetween symbol
        (by simpa [middle] using hsymbol)))
    (List.append (List.append base markers) [.done])
    (.marker001 :: List.append markers
      (.tick :: List.append (List.replicate innerRemaining .tick)
        (.done :: innerAfter)))
  have hinnerMarker := reaches_one_right
    (state := 10) (target := 11)
    (read := .marker001) (write := .marker001) (by decide)
    (List.append (List.append (List.append base markers) [.done]) middle)
    (List.append markers
      (.tick :: List.append (List.replicate innerRemaining .tick)
        (.done :: innerAfter)))
  have hinnerMarkers := reaches_scan_right_markers
    (state := 11) (by decide) paired
    (List.append
      (List.append (List.append (List.append base markers) [.done]) middle)
      [.marker001])
    (.tick :: List.append (List.replicate innerRemaining .tick)
      (.done :: innerAfter))
  have hinnerTick := reaches_one_right
    (state := 11) (target := 83)
    (read := .tick) (write := .tick) (by decide)
    (List.append
      (List.append
        (List.append (List.append (List.append base markers) [.done]) middle)
        [.marker001]) markers)
    (List.append (List.replicate innerRemaining .tick)
      (.done :: innerAfter))
  have hskip := reaches_skip_inner_source_to_end inner innerRemaining
    (List.append
      (List.append
        (List.append
          (List.append (List.append (List.append base markers) [.done]) middle)
          [.marker001]) markers) [.tick])
    rest innerEnd
  have hskip' : blockDescription.Reaches
      (configuration 83
        (List.append
          (List.append
            (List.append
              (List.append (List.append (List.append base markers) [.done])
                middle) [.marker001]) markers) [.tick])
        (List.append (List.replicate innerRemaining .tick)
          (.done :: innerAfter)))
      (sourceMismatchEndConfig outer inner paired 0 paired
        (innerRemaining + 1) before between innerEnd rest) := by
    simpa [sourceMismatchEndConfig, pairCleanupConfig, sourceComparisonMiddle,
      sourceComparisonAfter, comparisonRowInterior, markers, middle,
      innerAfter, base, rowAfterSourceBlocks, rowAfterReadBlocks,
      rowAfterWriteBlocks, rowTargetAndEndBlocks, rowInteriorBlocks,
      List.replicate_succ, List.append_assoc] using hskip
  have hrun := hmarkers.trans (houterDone.trans
    (hmiddle.trans (hinnerMarker.trans
      (hinnerMarkers.trans (hinnerTick.trans hskip')))))
  simpa [sourcePairRight, markers, middle, innerAfter, base,
    List.replicate_succ, List.append_assoc] using hrun

/-- State-3 target after an ordinary inner row has been restored. -/
def pairDoneConfig
    (outer inner : TransitionDescription)
    (before between rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration 3
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append before [.marker001]) (rowInteriorBlocks outer))
          (.done :: between)) [.transition])
      (List.append (rowInteriorBlocks inner) [.done]))
    rest

/-- State-3 target after the final inner row has been restored. -/
def pairFinalConfig
    (outer inner : TransitionDescription)
    (before between rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration 3
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append before [.marker001]) (rowInteriorBlocks outer))
          (.done :: between)) [.transition])
      (rowInteriorBlocks inner))
    (.marker011 :: rest)

/-- A successful pair comparison advances either to the next row or to the
final-row sentinel, according to the inner terminator. -/
def ReachesPairAdvance
    (source : ValidatorBlockDescription.Configuration)
    (outer inner : TransitionDescription)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) : Prop :=
  (innerEnd = .done ∧
    blockDescription.Reaches source
      (pairDoneConfig outer inner before between rest)) ∨
  (innerEnd = .marker011 ∧
    blockDescription.Reaches source
      (pairFinalConfig outer inner before between rest))

theorem ReachesPairAdvance.of_reaches
    {source middle : ValidatorBlockDescription.Configuration}
    {outer inner : TransitionDescription}
    {before between : Word ValidatorBlockSymbol}
    {innerEnd : ValidatorBlockSymbol}
    {rest : Word ValidatorBlockSymbol}
    (hsource : blockDescription.Reaches source middle)
    (hmiddle : ReachesPairAdvance middle outer inner
      before between innerEnd rest) :
    ReachesPairAdvance source outer inner before between innerEnd rest := by
  rcases hmiddle with ⟨hend, hrun⟩ | ⟨hend, hrun⟩
  · exact Or.inl ⟨hend, hsource.trans hrun⟩
  · exact Or.inr ⟨hend, hsource.trans hrun⟩

/-- A selected pair either advances compatibly or reaches the explicit
determinism conflict, with the branch synchronized to the semantic Boolean. -/
def PairOutcome
    (source : ValidatorBlockDescription.Configuration)
    (outer inner : TransitionDescription)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) : Prop :=
  (transitionDeterministicPairBool outer inner = true ∧
    ReachesPairAdvance source outer inner before between innerEnd rest) ∨
  (transitionDeterministicPairBool outer inner = false ∧
    ReachesConflict source)

theorem PairOutcome.of_reaches
    {source middle : ValidatorBlockDescription.Configuration}
    {outer inner : TransitionDescription}
    {before between : Word ValidatorBlockSymbol}
    {innerEnd : ValidatorBlockSymbol}
    {rest : Word ValidatorBlockSymbol}
    (hsource : blockDescription.Reaches source middle)
    (hmiddle : PairOutcome middle outer inner
      before between innerEnd rest) :
    PairOutcome source outer inner before between innerEnd rest := by
  rcases hmiddle with ⟨hbool, hadvance⟩ | ⟨hbool, hconflict⟩
  · exact Or.inl ⟨hbool,
      ReachesPairAdvance.of_reaches hsource hadvance⟩
  · exact Or.inr ⟨hbool, ReachesConflict.of_reaches hsource hconflict⟩

/-- Restore any fully traversed selected-pair layout and advance it. -/
theorem reaches_cleanup_pair
    (entry : Nat)
    (outer inner : TransitionDescription)
    (outerSourcePaired outerSourceRemaining
      outerTargetPaired outerTargetRemaining : Nat)
    (innerSourcePaired innerSourceRemaining
      innerTargetPaired innerTargetRemaining : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (houterSource :
      outer.source = outerSourcePaired + outerSourceRemaining)
    (houterTarget :
      outer.target = outerTargetPaired + outerTargetRemaining)
    (hinnerSource :
      inner.source = innerSourcePaired + innerSourceRemaining)
    (hinnerTarget :
      inner.target = innerTargetPaired + innerTargetRemaining)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols)
    (hinnerEnd : innerEnd = .done ∨ innerEnd = .marker011)
    (hdone :
      blockDescription.lookup entry .done =
        some
          { source := entry, read := .done, write := .done
            move := Direction.left, target := 88 })
    (hfinal :
      blockDescription.lookup entry .marker011 =
        some
          { source := entry, read := .marker011, write := .marker011
            move := Direction.left, target := 88 }) :
    ReachesPairAdvance
      (pairCleanupConfig entry outer inner
        outerSourcePaired outerSourceRemaining
        outerTargetPaired outerTargetRemaining
        innerSourcePaired innerSourceRemaining
        innerTargetPaired innerTargetRemaining
        before between innerEnd rest)
      outer inner before between innerEnd rest := by
  let outerMarked := comparisonRowInterior outer
    outerSourcePaired outerSourceRemaining
    outerTargetPaired outerTargetRemaining
  let innerMarked := comparisonRowInterior inner
    innerSourcePaired innerSourceRemaining
    innerTargetPaired innerTargetRemaining
  let middle : Word ValidatorBlockSymbol := .done :: between
  have houter : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from
        List.append outerMarked middle) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols := by
    intro symbol hsymbol
    rcases List.mem_append.mp hsymbol with hmarked | hmiddle
    · exact comparisonRowInterior_mem_corridor outer
        outerSourcePaired outerSourceRemaining
        outerTargetPaired outerTargetRemaining symbol hmarked
    · rcases List.mem_cons.mp hmiddle with rfl | hbetween'
      · exact ValidatorCountedRows.done_mem_corridor
      · exact ValidatorCountedRows.mem_corridor_of_canonical
          (hbetween symbol hbetween')
  have hinner : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from innerMarked) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols := by
    exact comparisonRowInterior_mem_corridor inner
      innerSourcePaired innerSourceRemaining
      innerTargetPaired innerTargetRemaining
  have hrestoreOuter := map_restore_comparisonRowInterior outer
    outerSourcePaired outerSourceRemaining
    outerTargetPaired outerTargetRemaining houterSource houterTarget
  have hrestoreInner := map_restore_comparisonRowInterior inner
    innerSourcePaired innerSourceRemaining
    innerTargetPaired innerTargetRemaining hinnerSource hinnerTarget
  have hrestoreMiddle : List.map restorePairMarker middle = middle := by
    apply map_restore_eq_self_of_canonical
    intro symbol hsymbol
    rcases List.mem_cons.mp hsymbol with rfl | hbetween'
    · simp [ValidatorCountedRows.canonicalCorridorSymbols]
    · exact hbetween symbol hbetween'
  rcases hinnerEnd with rfl | rfl
  · apply Or.inl
    refine ⟨rfl, ?_⟩
    have hrun := reaches_restore_selected_pair_done (entry := entry) outer inner
      outerMarked middle innerMarked before rest hdone houter hinner
      hrestoreOuter hrestoreMiddle hrestoreInner
    simpa [pairCleanupConfig, pairDoneConfig, outerMarked,
      innerMarked, middle, List.append_assoc] using hrun
  · apply Or.inr
    refine ⟨rfl, ?_⟩
    have hrun := reaches_restore_selected_pair_final (entry := entry) outer inner
      outerMarked middle innerMarked before rest hfinal houter hinner
      hrestoreOuter hrestoreMiddle hrestoreInner
    simpa [pairCleanupConfig, pairFinalConfig, outerMarked,
      innerMarked, middle, List.append_assoc] using hrun

/-- Restore a source-mismatch layout and advance the selected pair. -/
theorem reaches_cleanup_source_mismatch
    (outer inner : TransitionDescription)
    (outerPaired outerRemaining innerPaired innerRemaining : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (houterSource : outer.source = outerPaired + outerRemaining)
    (hinnerSource : inner.source = innerPaired + innerRemaining)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols)
    (hinnerEnd : innerEnd = .done ∨ innerEnd = .marker011) :
    ReachesPairAdvance
      (sourceMismatchEndConfig outer inner outerPaired outerRemaining
        innerPaired innerRemaining before between innerEnd rest)
      outer inner before between innerEnd rest := by
  simpa [sourceMismatchEndConfig, pairCleanupConfig] using
    reaches_cleanup_pair 87 outer inner
      outerPaired outerRemaining 0 outer.target
      innerPaired innerRemaining 0 inner.target
      before between innerEnd rest houterSource (by simp)
      hinnerSource (by simp) hbetween hinnerEnd (by decide) (by decide)

/-- State-15 target after equal source fields have been paired. -/
def pairReadConfig
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration 15
    (List.append
      (List.append (List.append before [.marker001])
        (List.replicate paired .marker010)) [.done])
    (selectedPairReadRight outer inner paired between innerEnd rest)

/-- State-5 source before any source ticks of the selected pair are marked. -/
def pairStartConfig
    (outer inner : TransitionDescription)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration 5 (List.append before [.marker001])
    (sourcePairRight outer.source inner.source 0
      (List.append (rowAfterSourceBlocks outer .done) between)
      (List.append (rowAfterSourceBlocks inner innerEnd) rest))

/-- Unequal read symbols skip the remaining inner action fields and reach the
shared successful cleanup entry. -/
theorem reaches_read_mismatch_to_end
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hread : outer.read ≠ inner.read) :
    blockDescription.Reaches
        (readComparisonConfig outer inner paired before
          between innerEnd rest)
        (sourceMismatchEndConfig outer inner paired 0 paired 0
          before between innerEnd rest) := by
  let left : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append before [.marker001])
                (List.replicate paired .marker010)) [.done])
              [ValidatorCountedRows.cellBlock outer.read])
            (List.append (rowAfterReadBlocks outer .done) between))
          [.marker001])
        (List.append (List.replicate paired .marker010) [.done])
  let innerAfterRead : Word ValidatorBlockSymbol :=
    List.append (rowAfterReadBlocks inner innerEnd) rest
  have hcompare := reaches_one_right
    (state := compareInnerReadState outer.read) (target := 85)
    (read := ValidatorCountedRows.cellBlock inner.read)
    (write := ValidatorCountedRows.cellBlock inner.read)
    (lookup_compare_read_ne outer.read inner.read hread)
    left innerAfterRead
  have hskip := reaches_skip_inner_write_to_end inner
    (List.append left [ValidatorCountedRows.cellBlock inner.read])
    rest innerEnd
  have hskip' : blockDescription.Reaches
      (configuration 85
        (List.append left [ValidatorCountedRows.cellBlock inner.read])
        innerAfterRead)
      (configuration 87
        (List.append
          (List.append
            (List.append left [ValidatorCountedRows.cellBlock inner.read])
            [ValidatorCountedRows.cellBlock inner.write,
              ValidatorCountedRows.directionBlock inner.move])
          (List.replicate inner.target .tick))
        (innerEnd :: rest)) := by
    simpa [innerAfterRead, rowAfterReadBlocks, rowAfterWriteBlocks,
      rowTargetAndEndBlocks] using hskip
  have hrun := hcompare.trans hskip'
  simpa [readComparisonConfig, sourceMismatchEndConfig, pairCleanupConfig,
    comparisonRowInterior, left, innerAfterRead, rowAfterReadBlocks,
    rowAfterWriteBlocks, rowTargetAndEndBlocks, List.append_assoc] using hrun

/-- Equal target fields use state 82 as the same successful cleanup entry. -/
theorem reaches_cleanup_equal_target
    (outer inner : TransitionDescription)
    (sourcePaired targetPaired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (houterSource : outer.source = sourcePaired)
    (houterTarget : outer.target = targetPaired)
    (hinnerSource : inner.source = sourcePaired)
    (hinnerTarget : inner.target = targetPaired)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols)
    (hinnerEnd : innerEnd = .done ∨ innerEnd = .marker011) :
    ReachesPairAdvance
      (targetEndCheckConfig outer inner sourcePaired targetPaired
        before between innerEnd rest)
      outer inner before between innerEnd rest := by
  have hrun := reaches_cleanup_pair 82 outer inner
    sourcePaired 0 targetPaired 0 sourcePaired 0 targetPaired 0
    before between innerEnd rest (by simpa using houterSource)
    (by simpa using houterTarget) (by simpa using hinnerSource)
    (by simpa using hinnerTarget) hbetween hinnerEnd (by decide) (by decide)
  simpa [targetEndCheckConfig, targetEndProbeConfig, targetPairLeft,
    pairCleanupConfig, comparisonRowInterior, List.append_assoc] using hrun

/-- Once source fields agree, compare the read/action/target fields and return
the Boolean-synchronized pair outcome. -/
theorem reaches_equal_source_outcome
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (houterSource : outer.source = paired)
    (hinnerSource : inner.source = paired)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols)
    (hinnerEnd : innerEnd = .done ∨ innerEnd = .marker011) :
    PairOutcome (pairReadConfig outer inner paired before between innerEnd rest)
      outer inner before between innerEnd rest := by
  have hsource : outer.source = inner.source :=
    houterSource.trans hinnerSource.symm
  have hcorridor : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols := by
    intro symbol hsymbol
    exact ValidatorCountedRows.mem_corridor_of_canonical
      (hbetween symbol hsymbol)
  by_cases hread : outer.read = inner.read
  · have hreadRun := reaches_equal_read_to_write outer inner paired before
      between innerEnd rest hcorridor hread
    have hwriteProbe := reaches_write_comparison outer inner paired before
      between innerEnd rest hcorridor
    have htoWrite := hreadRun.trans hwriteProbe
    by_cases hwrite : outer.write = inner.write
    · have hwriteRun := reaches_equal_write_to_move outer inner paired before
        between innerEnd rest hcorridor hwrite
      have hmoveProbe := reaches_move_comparison outer inner paired before
        between innerEnd rest hcorridor
      have htoMove := htoWrite.trans (hwriteRun.trans hmoveProbe)
      by_cases hmove : outer.move = inner.move
      · have hmoveRun := reaches_equal_move_to_target outer inner paired before
          between innerEnd rest hcorridor hmove
        have htoTargetRaw := htoMove.trans hmoveRun
        have htoTarget : blockDescription.Reaches
            (pairReadConfig outer inner paired before between innerEnd rest)
            (configuration 64 (targetPairLeft outer paired before)
              (targetPairRight outer inner paired outer.target inner.target 0
                between innerEnd rest)) := by
          simpa [pairReadConfig, targetPairLeft,
            selectedPairTargetRight_eq_targetPairRight] using htoTargetRaw
        rcases reaches_target_comparison outer inner paired outer.target
            inner.target 0 before between innerEnd rest hcorridor hinnerEnd with
          htarget | htarget
        · apply Or.inl
          refine ⟨?_, ?_⟩
          · simp [transitionDeterministicPairBool, transitionSameKeyBool,
              transitionSameActionBool, hsource, hread, hwrite, hmove,
              htarget.1]
          · have hcleanup := reaches_cleanup_equal_target outer inner paired
              outer.target before between innerEnd rest houterSource rfl
              hinnerSource htarget.1.symm hbetween hinnerEnd
            have htoEnd := htoTarget.trans htarget.2
            have htoEnd' : blockDescription.Reaches
                (pairReadConfig outer inner paired before between innerEnd rest)
                (targetEndCheckConfig outer inner paired outer.target
                  before between innerEnd rest) := by
              simpa using htoEnd
            exact ReachesPairAdvance.of_reaches htoEnd' hcleanup
        · apply Or.inr
          refine ⟨?_, ReachesConflict.of_reaches htoTarget htarget.2⟩
          simp [transitionDeterministicPairBool, transitionSameKeyBool,
            transitionSameActionBool, hsource, hread, hwrite, hmove,
            htarget.1]
      · apply Or.inr
        refine ⟨?_, ReachesConflict.of_reaches htoMove
          (reaches_move_conflict outer inner paired before between
            innerEnd rest hmove)⟩
        simp [transitionDeterministicPairBool, transitionSameKeyBool,
          transitionSameActionBool, hsource, hread, hwrite, hmove]
    · apply Or.inr
      refine ⟨?_, ReachesConflict.of_reaches htoWrite
        (reaches_write_conflict outer inner paired before between
          innerEnd rest hwrite)⟩
      simp [transitionDeterministicPairBool, transitionSameKeyBool,
        transitionSameActionBool, hsource, hread, hwrite]
  · apply Or.inl
    refine ⟨?_, ?_⟩
    · simp [transitionDeterministicPairBool, transitionSameKeyBool,
        hsource, hread]
    · have hprobe := reaches_read_comparison outer inner paired before between
        innerEnd rest hcorridor
      have hend := reaches_read_mismatch_to_end outer inner paired before
        between innerEnd rest hread
      apply ReachesPairAdvance.of_reaches (hprobe.trans hend)
      exact reaches_cleanup_source_mismatch outer inner paired 0 paired 0
        before between innerEnd rest (by simpa using houterSource)
        (by simpa using hinnerSource) hbetween hinnerEnd

/-- Complete source-key comparison: equality reaches the read comparison;
inequality restores the pair and advances successfully. -/
theorem reaches_source_comparison
    (outer inner : TransitionDescription)
    (outerRemaining innerRemaining paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (houterSource : outer.source = paired + outerRemaining)
    (hinnerSource : inner.source = paired + innerRemaining)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols)
    (hinnerEnd : innerEnd = .done ∨ innerEnd = .marker011) :
    (outerRemaining = innerRemaining ∧
      blockDescription.Reaches
        (configuration 5 (List.append before [.marker001])
          (sourcePairRight outerRemaining innerRemaining paired
            (sourceComparisonMiddle outer between)
            (sourceComparisonAfter inner innerEnd rest)))
        (pairReadConfig outer inner (paired + outerRemaining)
          before between innerEnd rest)) ∨
    (outerRemaining ≠ innerRemaining ∧
      ReachesPairAdvance
        (configuration 5 (List.append before [.marker001])
          (sourcePairRight outerRemaining innerRemaining paired
            (sourceComparisonMiddle outer between)
            (sourceComparisonAfter inner innerEnd rest)))
        outer inner before between innerEnd rest) := by
  have hbetweenCorridor : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols := by
    intro symbol hsymbol
    exact ValidatorCountedRows.mem_corridor_of_canonical
      (hbetween symbol hsymbol)
  induction outerRemaining generalizing innerRemaining paired with
  | zero =>
      cases innerRemaining with
      | zero =>
          apply Or.inl
          refine ⟨rfl, ?_⟩
          have hrun := reaches_equal_source_to_read paired before
            (sourceComparisonMiddle outer between)
            (sourceComparisonAfter inner innerEnd rest)
            (sourceComparisonMiddle_mem_corridor outer between
              hbetweenCorridor)
          simpa [pairReadConfig, sourceComparisonMiddle,
            sourceComparisonAfter, selectedPairReadRight,
            markedSourceInterior, List.append_assoc] using hrun
      | succ innerRemaining =>
          apply Or.inr
          refine ⟨by simp, ?_⟩
          have hrun := reaches_inner_longer_source_to_end outer inner paired
            innerRemaining before between innerEnd rest hbetweenCorridor
          apply ReachesPairAdvance.of_reaches hrun
          exact reaches_cleanup_source_mismatch outer inner paired 0 paired
            (innerRemaining + 1) before between innerEnd rest
            (by simpa using houterSource) (by simpa using hinnerSource)
            hbetween hinnerEnd
  | succ outerRemaining ih =>
      cases innerRemaining with
      | zero =>
          apply Or.inr
          refine ⟨by simp, ?_⟩
          have hrun := reaches_outer_longer_source_to_end outer inner paired
            outerRemaining before between innerEnd rest hbetweenCorridor
          apply ReachesPairAdvance.of_reaches hrun
          exact reaches_cleanup_source_mismatch outer inner (paired + 1)
            outerRemaining paired 0 before between innerEnd rest
            (by lia) (by simpa using hinnerSource) hbetween hinnerEnd
      | succ innerRemaining =>
          have hpair := reaches_pair_source_tick outerRemaining innerRemaining
            paired before (sourceComparisonMiddle outer between)
            (sourceComparisonAfter inner innerEnd rest)
            (sourceComparisonMiddle_mem_corridor outer between
              hbetweenCorridor)
          rcases ih (innerRemaining := innerRemaining)
              (paired := paired + 1) (by lia) (by lia) with hequal | hne
          · apply Or.inl
            refine ⟨congrArg Nat.succ hequal.1, ?_⟩
            have hrun := hpair.trans hequal.2
            have hpaired : paired + (outerRemaining + 1) =
                (paired + 1) + outerRemaining := by lia
            simpa [hpaired] using hrun
          · exact Or.inr ⟨fun heq => hne.1 (Nat.succ.inj heq),
              ReachesPairAdvance.of_reaches hpair hne.2⟩

/-- Complete one selected-row pair, synchronized with the semantic
determinism Boolean. -/
theorem reaches_selected_pair_outcome
    (outer inner : TransitionDescription)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols)
    (hinnerEnd : innerEnd = .done ∨ innerEnd = .marker011) :
    PairOutcome
      (pairStartConfig outer inner before between innerEnd rest)
      outer inner before between innerEnd rest := by
  rcases reaches_source_comparison outer inner outer.source inner.source 0
      before between innerEnd rest (by simp) (by simp) hbetween hinnerEnd with
    hequal | hne
  · have hfront : blockDescription.Reaches
        (pairStartConfig outer inner before between innerEnd rest)
        (pairReadConfig outer inner outer.source before between innerEnd rest) := by
      simpa [pairStartConfig, sourceComparisonMiddle,
        sourceComparisonAfter] using hequal.2
    have htail := reaches_equal_source_outcome outer inner outer.source before
      between innerEnd rest rfl hequal.1.symm hbetween hinnerEnd
    exact PairOutcome.of_reaches hfront htail
  · apply Or.inl
    refine ⟨?_, ?_⟩
    · simp [transitionDeterministicPairBool, transitionSameKeyBool, hne.1]
    · simpa [pairStartConfig, sourceComparisonMiddle,
        sourceComparisonAfter] using hne.2

/-- A semantically compatible selected pair follows the successful branch. -/
theorem reaches_selected_pair_of_true
    (outer inner : TransitionDescription)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols)
    (hinnerEnd : innerEnd = .done ∨ innerEnd = .marker011)
    (hpair : transitionDeterministicPairBool outer inner = true) :
    ReachesPairAdvance
      (pairStartConfig outer inner before between innerEnd rest)
      outer inner before between innerEnd rest := by
  rcases reaches_selected_pair_outcome outer inner before between innerEnd rest
    hbetween hinnerEnd with hsuccess | hconflict
  · exact hsuccess.2
  · simp [hpair] at hconflict

/-- A semantically incompatible selected pair reaches conflict. -/
theorem reaches_selected_pair_of_false
    (outer inner : TransitionDescription)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.canonicalCorridorSymbols)
    (hinnerEnd : innerEnd = .done ∨ innerEnd = .marker011)
    (hpair : transitionDeterministicPairBool outer inner = false) :
    ReachesConflict
      (pairStartConfig outer inner before between innerEnd rest) := by
  rcases reaches_selected_pair_outcome outer inner before between innerEnd rest
    hbetween hinnerEnd with hsuccess | hconflict
  · simp [hpair] at hsuccess
  · exact hconflict.2

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
