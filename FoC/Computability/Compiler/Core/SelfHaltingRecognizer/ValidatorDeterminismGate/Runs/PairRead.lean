import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.PairLayout

set_option doc.verso true

/-!
# Exact-code validator: read-field comparison

For equal source fields, equal read symbols complete the transition-key test.
This module proves the return shuttle from the inner read symbol to the outer
write symbol.  The unequal-read branch is routed to the shared successful
cleanup in a later module.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

private theorem lookup_readSeekMarker_corridor
    (expected : Option Bool) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup (readSeekMarkerState expected) symbol =
      some
        { source := readSeekMarkerState expected
          read := symbol
          write := symbol
          move := Direction.right
          target := readSeekMarkerState expected } := by
  cases expected with
  | none =>
      cases symbol <;>
        simp [ValidatorCountedRows.corridorSymbols,
          ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
        decide
  | some bit =>
      cases bit <;>
        cases symbol <;>
          simp [ValidatorCountedRows.corridorSymbols,
            ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
          decide

private theorem lookup_state26_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 26 symbol =
      some
        { source := 26
          read := symbol
          write := symbol
          move := Direction.left
          target := 26 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem readMiddle_mem_corridor
    (outer : TransitionDescription)
    (between : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.append (rowAfterReadBlocks outer .done) between)) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  rcases List.mem_append.mp hmem with houter | hbetween'
  · unfold rowAfterReadBlocks rowAfterWriteBlocks rowTargetAndEndBlocks at houter
    simp only [List.mem_cons] at houter
    rcases houter with hwrite | houter
    · subst symbol
      exact ValidatorCountedRows.mem_corridor_of_canonical
        (ValidatorCountedRows.cellBlock_mem_canonicalCorridor outer.write)
    · rcases houter with hmove | htarget
      · subst symbol
        exact ValidatorCountedRows.mem_corridor_of_canonical
          (ValidatorCountedRows.directionBlock_mem_canonicalCorridor
            outer.move)
      · rcases List.mem_append.mp htarget with htick | hdone
        · have heq : symbol = .tick :=
            (List.mem_replicate.mp htick).2
          subst symbol
          exact ValidatorCountedRows.tick_mem_corridor
        · have heq : symbol = .done := List.mem_singleton.mp hdone
          subst symbol
          exact ValidatorCountedRows.done_mem_corridor
  · exact hbetween symbol hbetween'

private theorem readReturnCorridor_mem
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
            List.append (rowAfterReadBlocks outer .done) between))) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  rcases List.mem_append.mp hmem with hmarkers | htail
  · have heq : symbol = .marker010 :=
      (List.mem_replicate.mp hmarkers).2
    subst symbol
    exact ValidatorCountedRows.marker010_mem_corridor
  · rcases List.mem_cons.mp htail with hdone | htail
    · subst symbol
      exact ValidatorCountedRows.done_mem_corridor
    · rcases List.mem_cons.mp htail with hread | hmiddle
      · subst symbol
        exact ValidatorCountedRows.mem_corridor_of_canonical
          (ValidatorCountedRows.cellBlock_mem_canonicalCorridor outer.read)
      · exact readMiddle_mem_corridor outer between hbetween symbol hmiddle

/-- Configuration at the inner read symbol. -/
def readComparisonConfig
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration (compareInnerReadState outer.read)
    (List.append
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
        (List.append (List.replicate paired .marker010) [.done]))
    (ValidatorCountedRows.cellBlock inner.read ::
      List.append (rowAfterReadBlocks inner innerEnd) rest)

/-- Shuttle from the outer read symbol to the inner read symbol. -/
theorem reaches_read_comparison
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 15
          (List.append
            (List.append (List.append before [.marker001])
              (List.replicate paired .marker010)) [.done])
          (selectedPairReadRight outer inner paired
            between innerEnd rest))
        (readComparisonConfig outer inner paired before
          between innerEnd rest) := by
  let markers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let middle : Word ValidatorBlockSymbol :=
    List.append (rowAfterReadBlocks outer .done) between
  let innerAfterRead : Word ValidatorBlockSymbol :=
    List.append (rowAfterReadBlocks inner innerEnd) rest
  let base : Word ValidatorBlockSymbol :=
    List.append
      (List.append (List.append before [.marker001]) markers) [.done]
  have houterRead := reaches_one_right
    (state := 15) (target := readSeekMarkerState outer.read)
    (read := ValidatorCountedRows.cellBlock outer.read)
    (write := ValidatorCountedRows.cellBlock outer.read)
    (by cases outer.read with
      | none => decide
      | some bit => cases bit <;> decide)
    base
    (List.append middle
      (.marker001 :: List.append markers
        (.done :: ValidatorCountedRows.cellBlock inner.read ::
          innerAfterRead)))
  have hmiddle := reaches_scan_right_list middle
    (fun symbol hsymbol => lookup_readSeekMarker_corridor outer.read symbol
      (readMiddle_mem_corridor outer between hbetween symbol
        (by simpa [middle] using hsymbol)))
    (List.append base [ValidatorCountedRows.cellBlock outer.read])
    (.marker001 :: List.append markers
      (.done :: ValidatorCountedRows.cellBlock inner.read :: innerAfterRead))
  have hmarker := reaches_one_right
    (state := readSeekMarkerState outer.read)
    (target := readSeekSourceState outer.read)
    (read := .marker001) (write := .marker001)
    (by cases outer.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append base [ValidatorCountedRows.cellBlock outer.read]) middle)
    (List.append markers
      (.done :: ValidatorCountedRows.cellBlock inner.read :: innerAfterRead))
  have hmarkers := reaches_scan_right_markers
    (state := readSeekSourceState outer.read)
    (by cases outer.read with
      | none => decide
      | some bit => cases bit <;> decide)
    paired
    (List.append
      (List.append
        (List.append base [ValidatorCountedRows.cellBlock outer.read]) middle)
      [.marker001])
    (.done :: ValidatorCountedRows.cellBlock inner.read :: innerAfterRead)
  have hdone := reaches_one_right
    (state := readSeekSourceState outer.read)
    (target := compareInnerReadState outer.read)
    (read := .done) (write := .done)
    (by cases outer.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append base [ValidatorCountedRows.cellBlock outer.read]) middle)
        [.marker001]) markers)
    (ValidatorCountedRows.cellBlock inner.read :: innerAfterRead)
  have hrun := houterRead.trans
    (hmiddle.trans (hmarker.trans (hmarkers.trans hdone)))
  simpa [readComparisonConfig, selectedPairReadRight,
    markedSourceInterior, rowAfterSourceBlocks, base, middle,
    innerAfterRead, markers, List.append_assoc] using hrun

/-- Equal read symbols return to the selected outer write field. -/
theorem reaches_equal_read_to_write
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (hread : outer.read = inner.read) :
    blockDescription.Reaches
        (configuration 15
          (List.append
            (List.append (List.append before [.marker001])
              (List.replicate paired .marker010)) [.done])
          (selectedPairReadRight outer inner paired
            between innerEnd rest))
        (configuration 29
          (List.append
            (List.append
              (List.append
                (List.append before [.marker001])
                (List.replicate paired .marker010)) [.done])
            [ValidatorCountedRows.cellBlock outer.read])
          (selectedPairWriteRight outer inner paired
            between innerEnd rest)) := by
  let markers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let middle : Word ValidatorBlockSymbol :=
    List.append (rowAfterReadBlocks outer .done) between
  let innerAfterRead : Word ValidatorBlockSymbol :=
    List.append (rowAfterReadBlocks inner innerEnd) rest
  let innerSource : Word ValidatorBlockSymbol :=
    List.append markers [.done]
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append markers
      (.done :: ValidatorCountedRows.cellBlock outer.read :: middle)
  let base : Word ValidatorBlockSymbol :=
    List.append before [.marker001]

  let c6 := configuration 25
    (List.append (List.append before [.marker001]) returnCorridor)
    (.marker001 :: List.append innerSource
      (ValidatorCountedRows.cellBlock inner.read :: innerAfterRead))
  let c8 := configuration 27 base
    (List.append returnCorridor
      (.marker001 :: List.append innerSource
        (ValidatorCountedRows.cellBlock inner.read :: innerAfterRead)))
  let c9 := configuration 27 (List.append base markers)
    (.done :: ValidatorCountedRows.cellBlock outer.read ::
      List.append middle
        (.marker001 :: List.append innerSource
          (ValidatorCountedRows.cellBlock inner.read :: innerAfterRead)))
  have hcompareReturn := reaches_cross_scan_left_word innerSource
    (entry := compareInnerReadState outer.read) (scan := 25)
    (entryRead := ValidatorCountedRows.cellBlock inner.read)
    (entryWrite := ValidatorCountedRows.cellBlock inner.read)
    (boundary := .marker001)
    (by
      rw [← hread]
      cases outer.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (by
      intro symbol hsymbol
      rcases List.mem_append.mp hsymbol with hmarkers | hdone
      · have heq : symbol = .marker010 :=
          (List.mem_replicate.mp hmarkers).2
        subst symbol
        decide
      · have heq : symbol = .done := List.mem_singleton.mp hdone
        subst symbol
        decide)
    (List.append (List.append before [.marker001]) returnCorridor)
    innerAfterRead
  have hreturn := reaches_cross_scan_left_word returnCorridor
    (entry := 25) (scan := 26)
    (entryRead := .marker001) (entryWrite := .marker001)
    (boundary := .marker001)
    (by decide)
    (fun symbol hsymbol => lookup_state26_corridor symbol
      (readReturnCorridor_mem outer paired between hbetween symbol
        (by simpa [returnCorridor, middle, markers] using hsymbol)))
    before
    (List.append innerSource
      (ValidatorCountedRows.cellBlock inner.read :: innerAfterRead))
  have houterMarker := reaches_one_right
    (state := 26) (target := 27)
    (read := .marker001) (write := .marker001)
    (by decide) before
    (List.append returnCorridor
      (.marker001 :: List.append innerSource
        (ValidatorCountedRows.cellBlock inner.read :: innerAfterRead)))
  have houterMarkers := reaches_scan_right_markers
    (state := 27) (by decide) paired base
    (.done :: ValidatorCountedRows.cellBlock outer.read ::
      List.append middle
        (.marker001 :: List.append innerSource
          (ValidatorCountedRows.cellBlock inner.read :: innerAfterRead)))
  have houterDone := reaches_one_right
    (state := 27) (target := 28)
    (read := .done) (write := .done)
    (by decide) (List.append base markers)
    (ValidatorCountedRows.cellBlock outer.read ::
      List.append middle
        (.marker001 :: List.append innerSource
          (ValidatorCountedRows.cellBlock inner.read :: innerAfterRead)))
  have houterRead := reaches_one_right
    (state := 28) (target := 29)
    (read := ValidatorCountedRows.cellBlock outer.read)
    (write := ValidatorCountedRows.cellBlock outer.read)
    (by cases outer.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append (List.append base markers) [.done])
    (List.append middle
      (.marker001 :: List.append innerSource
        (ValidatorCountedRows.cellBlock inner.read :: innerAfterRead)))

  have hstart := reaches_read_comparison outer inner paired before between
    innerEnd rest hbetween
  have h56 : blockDescription.Reaches
      (readComparisonConfig outer inner paired before between innerEnd rest)
      c6 := by
    simpa [readComparisonConfig, c6, returnCorridor, middle, base,
      innerSource, innerAfterRead, markers, List.append_assoc] using
      hcompareReturn
  have h68 : blockDescription.Reaches c6 c8 := by
    simpa [c6, c8, base] using hreturn.trans houterMarker
  have h89 : blockDescription.Reaches c8 c9 := by
    simpa [c8, c9, returnCorridor, middle, base, List.append_assoc] using
      houterMarkers
  have hend : blockDescription.Reaches c9
      (configuration 29
        (List.append
          (List.append
            (List.append
              (List.append before [.marker001])
              (List.replicate paired .marker010)) [.done])
          [ValidatorCountedRows.cellBlock outer.read])
        (selectedPairWriteRight outer inner paired
          between innerEnd rest)) := by
    have hrun := houterDone.trans houterRead
    simpa [c9, base, middle, innerSource, innerAfterRead,
      selectedPairWriteRight, markedSourceInterior,
      rowAfterSourceBlocks, markers, List.append_assoc] using hrun
  exact hstart.trans (h56.trans (h68.trans (h89.trans hend)))

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
