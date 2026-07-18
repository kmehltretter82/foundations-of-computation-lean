import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.PairWrite

set_option doc.verso true
set_option maxRecDepth 10000

/-!
# Exact-code validator: move-field comparison

The move field is the second action component.  A mismatch reaches conflict;
equality returns to the first outer target tick or target terminator.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

private theorem lookup_moveSeekMarker_corridor
    (expected : Direction) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup (moveSeekMarkerState expected) symbol =
      some
        { source := moveSeekMarkerState expected
          read := symbol
          write := symbol
          move := Direction.right
          target := moveSeekMarkerState expected } := by
  cases expected <;>
    cases symbol <;>
      simp [ValidatorCountedRows.corridorSymbols,
        ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
      decide

private theorem lookup_state59_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 59 symbol =
      some
        { source := 59
          read := symbol
          write := symbol
          move := Direction.left
          target := 59 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem lookup_compare_move_ne
    (expected actual : Direction) (hne : expected ≠ actual) :
    blockDescription.lookup (compareInnerMoveState expected)
        (ValidatorCountedRows.directionBlock actual) =
      some
        { source := compareInnerMoveState expected
          read := ValidatorCountedRows.directionBlock actual
          write := ValidatorCountedRows.directionBlock actual
          move := Direction.right
          target := 100 } := by
  cases expected <;> cases actual <;> simp at hne <;> decide

private theorem lookup_compare_move_eq
    (expected actual : Direction) (heq : expected = actual) :
    blockDescription.lookup (compareInnerMoveState expected)
        (ValidatorCountedRows.directionBlock actual) =
      some
        { source := compareInnerMoveState expected
          read := ValidatorCountedRows.directionBlock actual
          write := ValidatorCountedRows.directionBlock actual
          move := Direction.left
          target := 58 } := by
  subst actual
  cases expected <;> decide

private theorem moveMiddle_mem_corridor
    (outer : TransitionDescription)
    (between : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.append (rowTargetAndEndBlocks outer .done) between)) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  rcases List.mem_append.mp hmem with houter | hbetween'
  · unfold rowTargetAndEndBlocks at houter
    rcases List.mem_append.mp houter with htick | hdone
    · have heq : symbol = .tick := (List.mem_replicate.mp htick).2
      subst symbol
      exact ValidatorCountedRows.tick_mem_corridor
    · have heq : symbol = .done := List.mem_singleton.mp hdone
      subst symbol
      exact ValidatorCountedRows.done_mem_corridor
  · exact hbetween symbol hbetween'

private theorem moveReturnCorridor_mem
    (outer : TransitionDescription) (paired : Nat)
    (between : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.append (List.replicate paired .marker010)
          (.done ::
            ValidatorCountedRows.cellBlock outer.read ::
            ValidatorCountedRows.cellBlock outer.write ::
            ValidatorCountedRows.directionBlock outer.move ::
            List.append (rowTargetAndEndBlocks outer .done) between))) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  rcases List.mem_append.mp hmem with hmarkers | htail
  · have heq : symbol = .marker010 :=
      (List.mem_replicate.mp hmarkers).2
    subst symbol
    exact ValidatorCountedRows.marker010_mem_corridor
  · rcases List.mem_cons.mp htail with hdone | htail
    · subst symbol
      exact ValidatorCountedRows.done_mem_corridor
    · rcases List.mem_cons.mp htail with hread | htail
      · subst symbol
        exact ValidatorCountedRows.mem_corridor_of_canonical
          (ValidatorCountedRows.cellBlock_mem_canonicalCorridor outer.read)
      · rcases List.mem_cons.mp htail with hwrite | htail
        · subst symbol
          exact ValidatorCountedRows.mem_corridor_of_canonical
            (ValidatorCountedRows.cellBlock_mem_canonicalCorridor outer.write)
        · rcases List.mem_cons.mp htail with hmove | hmiddle
          · subst symbol
            exact ValidatorCountedRows.mem_corridor_of_canonical
              (ValidatorCountedRows.directionBlock_mem_canonicalCorridor
                outer.move)
          · exact moveMiddle_mem_corridor outer between hbetween symbol hmiddle

/-- Configuration at the inner move symbol. -/
def moveComparisonConfig
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration (compareInnerMoveState outer.move)
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append
                    (List.append
                      (List.append
                        (List.append before [.marker001])
                        (List.replicate paired .marker010)) [.done])
                    [ValidatorCountedRows.cellBlock outer.read])
                  [ValidatorCountedRows.cellBlock outer.write])
                [ValidatorCountedRows.directionBlock outer.move])
              (List.append (rowTargetAndEndBlocks outer .done) between))
            [.marker001])
          (List.replicate paired .marker010)) [.done])
      [ValidatorCountedRows.cellBlock inner.read,
        ValidatorCountedRows.cellBlock inner.write])
    (ValidatorCountedRows.directionBlock inner.move ::
      List.append (rowTargetAndEndBlocks inner innerEnd) rest)

/-- Shuttle from the outer move symbol to the inner move symbol. -/
theorem reaches_move_comparison
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 47
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append before [.marker001])
                  (List.replicate paired .marker010)) [.done])
              [ValidatorCountedRows.cellBlock outer.read])
            [ValidatorCountedRows.cellBlock outer.write])
          (selectedPairMoveRight outer inner paired
            between innerEnd rest))
        (moveComparisonConfig outer inner paired before
          between innerEnd rest) := by
  let markers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let middle : Word ValidatorBlockSymbol :=
    List.append (rowTargetAndEndBlocks outer .done) between
  let innerAfterMove : Word ValidatorBlockSymbol :=
    List.append (rowTargetAndEndBlocks inner innerEnd) rest
  let base : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (List.append
          (List.append (List.append before [.marker001]) markers) [.done])
        [ValidatorCountedRows.cellBlock outer.read])
      [ValidatorCountedRows.cellBlock outer.write]
  have houterMove := reaches_one_right
    (state := 47) (target := moveSeekMarkerState outer.move)
    (read := ValidatorCountedRows.directionBlock outer.move)
    (write := ValidatorCountedRows.directionBlock outer.move)
    (by cases outer.move <;> decide)
    base
    (List.append middle
      (.marker001 ::
        List.append markers
          (.done :: ValidatorCountedRows.cellBlock inner.read ::
            ValidatorCountedRows.cellBlock inner.write ::
            ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)))
  have hmiddleRun := reaches_scan_right_list middle
    (fun symbol hsymbol => lookup_moveSeekMarker_corridor outer.move symbol
      (moveMiddle_mem_corridor outer between hbetween symbol
        (by simpa [middle] using hsymbol)))
    (List.append base [ValidatorCountedRows.directionBlock outer.move])
    (.marker001 ::
      List.append markers
        (.done :: ValidatorCountedRows.cellBlock inner.read ::
          ValidatorCountedRows.cellBlock inner.write ::
          ValidatorCountedRows.directionBlock inner.move :: innerAfterMove))
  have hinnerMarker := reaches_one_right
    (state := moveSeekMarkerState outer.move)
    (target := moveSeekSourceState outer.move)
    (read := .marker001) (write := .marker001)
    (by cases outer.move <;> decide)
    (List.append
      (List.append base [ValidatorCountedRows.directionBlock outer.move]) middle)
    (List.append markers
      (.done :: ValidatorCountedRows.cellBlock inner.read ::
        ValidatorCountedRows.cellBlock inner.write ::
        ValidatorCountedRows.directionBlock inner.move :: innerAfterMove))
  have hmarkers := reaches_scan_right_markers
    (state := moveSeekSourceState outer.move)
    (by cases outer.move <;> decide)
    paired
    (List.append
      (List.append
        (List.append base [ValidatorCountedRows.directionBlock outer.move])
        middle) [.marker001])
    (.done :: ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)
  have hdone := reaches_one_right
    (state := moveSeekSourceState outer.move)
    (target := moveSkipReadState outer.move)
    (read := .done) (write := .done)
    (by cases outer.move <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append base [ValidatorCountedRows.directionBlock outer.move])
          middle) [.marker001]) markers)
    (ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)
  have hread := reaches_one_right
    (state := moveSkipReadState outer.move)
    (target := moveSkipWriteState outer.move)
    (read := ValidatorCountedRows.cellBlock inner.read)
    (write := ValidatorCountedRows.cellBlock inner.read)
    (by
      cases outer.move <;> cases inner.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append base [ValidatorCountedRows.directionBlock outer.move])
            middle) [.marker001]) markers) [.done])
    (ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)
  have hwrite := reaches_one_right
    (state := moveSkipWriteState outer.move)
    (target := compareInnerMoveState outer.move)
    (read := ValidatorCountedRows.cellBlock inner.write)
    (write := ValidatorCountedRows.cellBlock inner.write)
    (by
      cases outer.move <;> cases inner.write with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append base
                [ValidatorCountedRows.directionBlock outer.move])
              middle) [.marker001]) markers) [.done])
      [ValidatorCountedRows.cellBlock inner.read])
    (ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)
  have hrun := houterMove.trans
    (hmiddleRun.trans (hinnerMarker.trans
      (hmarkers.trans (hdone.trans (hread.trans hwrite)))))
  simpa [moveComparisonConfig, selectedPairMoveRight, markedSourceInterior,
    rowAfterSourceBlocks, rowAfterReadBlocks, rowAfterWriteBlocks,
    base, middle, innerAfterMove, markers, List.append_assoc] using hrun

/-- Unequal moves reach the explicit conflict state. -/
theorem reaches_move_conflict
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hmove : outer.move ≠ inner.move) :
    ReachesConflict
      (moveComparisonConfig outer inner paired before
        between innerEnd rest) := by
  let explicitLeft : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append
                    (List.append
                      (List.append
                        (List.append before [.marker001])
                        (List.replicate paired .marker010)) [.done])
                    [ValidatorCountedRows.cellBlock outer.read])
                  [ValidatorCountedRows.cellBlock outer.write])
                [ValidatorCountedRows.directionBlock outer.move])
              (List.append (rowTargetAndEndBlocks outer .done) between))
            [.marker001])
          (List.replicate paired .marker010)) [.done])
      [ValidatorCountedRows.cellBlock inner.read,
        ValidatorCountedRows.cellBlock inner.write]
  let innerAfterMove : Word ValidatorBlockSymbol :=
    List.append (rowTargetAndEndBlocks inner innerEnd) rest
  have hstep := reaches_one_right
    (state := compareInnerMoveState outer.move) (target := 100)
    (read := ValidatorCountedRows.directionBlock inner.move)
    (write := ValidatorCountedRows.directionBlock inner.move)
    (lookup_compare_move_ne outer.move inner.move hmove)
    explicitLeft innerAfterMove
  refine ⟨List.append explicitLeft
      [ValidatorCountedRows.directionBlock inner.move], innerAfterMove, ?_⟩
  simpa [moveComparisonConfig, explicitLeft, innerAfterMove,
    configuration, ValidatorBlockDescription.blockConfiguration,
    List.append_assoc] using hstep

/-- Equal moves return to the outer target field. -/
theorem reaches_equal_move_to_target
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (hmove : outer.move = inner.move) :
    blockDescription.Reaches
        (moveComparisonConfig outer inner paired before
          between innerEnd rest)
        (configuration 64
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append
                    (List.append before [.marker001])
                    (List.replicate paired .marker010)) [.done])
                [ValidatorCountedRows.cellBlock outer.read])
              [ValidatorCountedRows.cellBlock outer.write])
            [ValidatorCountedRows.directionBlock outer.move])
          (selectedPairTargetRight outer inner paired
            between innerEnd rest)) := by
  let markers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let middle : Word ValidatorBlockSymbol :=
    List.append (rowTargetAndEndBlocks outer .done) between
  let innerAfterMove : Word ValidatorBlockSymbol :=
    List.append (rowTargetAndEndBlocks inner innerEnd) rest
  let innerPrefix : Word ValidatorBlockSymbol :=
    List.append markers
      [.done, ValidatorCountedRows.cellBlock inner.read,
        ValidatorCountedRows.cellBlock inner.write]
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append markers
      (.done :: ValidatorCountedRows.cellBlock outer.read ::
        ValidatorCountedRows.cellBlock outer.write ::
        ValidatorCountedRows.directionBlock outer.move :: middle)
  have hcompare := reaches_cross_scan_left_word innerPrefix
    (entry := compareInnerMoveState outer.move) (scan := 58)
    (entryRead := ValidatorCountedRows.directionBlock inner.move)
    (entryWrite := ValidatorCountedRows.directionBlock inner.move)
    (boundary := .marker001)
    (lookup_compare_move_eq outer.move inner.move hmove)
    (by
      intro symbol hsymbol
      unfold innerPrefix at hsymbol
      rcases List.mem_append.mp hsymbol with hmarkers | hfixed
      · have heq : symbol = .marker010 :=
          (List.mem_replicate.mp hmarkers).2
        subst symbol
        decide
      · rcases List.mem_cons.mp hfixed with hdone | hfixed
        · subst symbol
          decide
        · rcases List.mem_cons.mp hfixed with hread | hwrite
          · subst symbol
            cases inner.read with
            | none => decide
            | some bit => cases bit <;> decide
          · have heq : symbol = ValidatorCountedRows.cellBlock inner.write :=
              List.mem_singleton.mp hwrite
            subst symbol
            cases inner.write with
            | none => decide
            | some bit => cases bit <;> decide)
    (List.append (List.append before [.marker001]) returnCorridor)
    innerAfterMove
  have hreturn := reaches_cross_scan_left_word returnCorridor
    (entry := 58) (scan := 59)
    (entryRead := .marker001) (entryWrite := .marker001)
    (boundary := .marker001)
    (by decide)
    (fun symbol hsymbol => lookup_state59_corridor symbol
      (moveReturnCorridor_mem outer paired between hbetween symbol
        (by simpa [returnCorridor, middle, markers] using hsymbol)))
    before
    (List.append innerPrefix
      (ValidatorCountedRows.directionBlock inner.move :: innerAfterMove))
  have houterMarker := reaches_one_right
    (state := 59) (target := 60)
    (read := .marker001) (write := .marker001)
    (by decide) before
    (List.append returnCorridor
      (.marker001 :: List.append innerPrefix
        (ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)))
  have hmarkers := reaches_scan_right_markers
    (state := 60) (by decide) paired
    (List.append before [.marker001])
    (.done :: ValidatorCountedRows.cellBlock outer.read ::
      ValidatorCountedRows.cellBlock outer.write ::
      ValidatorCountedRows.directionBlock outer.move ::
      List.append middle
        (.marker001 :: List.append innerPrefix
          (ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)))
  have hdone := reaches_one_right
    (state := 60) (target := 61)
    (read := .done) (write := .done) (by decide)
    (List.append (List.append before [.marker001]) markers)
    (ValidatorCountedRows.cellBlock outer.read ::
      ValidatorCountedRows.cellBlock outer.write ::
      ValidatorCountedRows.directionBlock outer.move ::
      List.append middle
        (.marker001 :: List.append innerPrefix
          (ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)))
  have hread := reaches_one_right
    (state := 61) (target := 62)
    (read := ValidatorCountedRows.cellBlock outer.read)
    (write := ValidatorCountedRows.cellBlock outer.read)
    (by cases outer.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append (List.append before [.marker001]) markers) [.done])
    (ValidatorCountedRows.cellBlock outer.write ::
      ValidatorCountedRows.directionBlock outer.move ::
      List.append middle
        (.marker001 :: List.append innerPrefix
          (ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)))
  have hwrite := reaches_one_right
    (state := 62) (target := 63)
    (read := ValidatorCountedRows.cellBlock outer.write)
    (write := ValidatorCountedRows.cellBlock outer.write)
    (by cases outer.write with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append (List.append before [.marker001]) markers) [.done])
      [ValidatorCountedRows.cellBlock outer.read])
    (ValidatorCountedRows.directionBlock outer.move ::
      List.append middle
        (.marker001 :: List.append innerPrefix
          (ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)))
  have hmoveOuter := reaches_one_right
    (state := 63) (target := 64)
    (read := ValidatorCountedRows.directionBlock outer.move)
    (write := ValidatorCountedRows.directionBlock outer.move)
    (by cases outer.move <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append (List.append before [.marker001]) markers) [.done])
        [ValidatorCountedRows.cellBlock outer.read])
      [ValidatorCountedRows.cellBlock outer.write])
    (List.append middle
      (.marker001 :: List.append innerPrefix
        (ValidatorCountedRows.directionBlock inner.move :: innerAfterMove)))
  have hmarkers' : blockDescription.Reaches
      (configuration 60 (List.append before [.marker001])
        (List.append returnCorridor
          (.marker001 :: List.append innerPrefix
            (ValidatorCountedRows.directionBlock inner.move :: innerAfterMove))))
      (configuration 60
        (List.append (List.append before [.marker001]) markers)
        (.done :: ValidatorCountedRows.cellBlock outer.read ::
          ValidatorCountedRows.cellBlock outer.write ::
          ValidatorCountedRows.directionBlock outer.move ::
          List.append middle
            (.marker001 :: List.append innerPrefix
              (ValidatorCountedRows.directionBlock inner.move ::
                innerAfterMove)))) := by
    simpa [returnCorridor, List.append_assoc] using hmarkers
  have hrun := hcompare.trans
    (hreturn.trans (houterMarker.trans
      (hmarkers'.trans
        (hdone.trans (hread.trans (hwrite.trans hmoveOuter))))))
  simpa [moveComparisonConfig, selectedPairTargetRight,
    markedSourceInterior, rowAfterSourceBlocks, rowAfterReadBlocks,
    rowAfterWriteBlocks, innerPrefix, returnCorridor, middle,
    innerAfterMove, markers, List.append_assoc] using hrun

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
