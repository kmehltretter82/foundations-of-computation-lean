import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.PairRead

set_option doc.verso true
set_option maxRecDepth 10000

/-!
# Exact-code validator: write-field comparison

The write field is the first action component.  A mismatch reaches the explicit
conflict state; equality returns to the outer move field.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

private theorem lookup_writeSeekMarker_corridor
    (expected : Option Bool) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup (writeSeekMarkerState expected) symbol =
      some
        { source := writeSeekMarkerState expected
          read := symbol
          write := symbol
          move := Direction.right
          target := writeSeekMarkerState expected } := by
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

private theorem lookup_state43_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 43 symbol =
      some
        { source := 43
          read := symbol
          write := symbol
          move := Direction.left
          target := 43 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem lookup_compare_write_ne
    (expected actual : Option Bool) (hne : expected ≠ actual) :
    blockDescription.lookup (compareInnerWriteState expected)
        (ValidatorCountedRows.cellBlock actual) =
      some
        { source := compareInnerWriteState expected
          read := ValidatorCountedRows.cellBlock actual
          write := ValidatorCountedRows.cellBlock actual
          move := Direction.right
          target := 100 } := by
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

private theorem lookup_compare_write_eq
    (expected actual : Option Bool) (heq : expected = actual) :
    blockDescription.lookup (compareInnerWriteState expected)
        (ValidatorCountedRows.cellBlock actual) =
      some
        { source := compareInnerWriteState expected
          read := ValidatorCountedRows.cellBlock actual
          write := ValidatorCountedRows.cellBlock actual
          move := Direction.left
          target := 42 } := by
  subst actual
  cases expected with
  | none => decide
  | some bit => cases bit <;> decide

private theorem writeMiddle_mem_corridor
    (outer : TransitionDescription)
    (between : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.append (rowAfterWriteBlocks outer .done) between)) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  rcases List.mem_append.mp hmem with houter | hbetween'
  · unfold rowAfterWriteBlocks rowTargetAndEndBlocks at houter
    simp only [List.mem_cons] at houter
    rcases houter with hmove | htarget
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

private theorem writeReturnCorridor_mem
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
            List.append (rowAfterWriteBlocks outer .done) between))) :
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
      · rcases List.mem_cons.mp htail with hwrite | hmiddle
        · subst symbol
          exact ValidatorCountedRows.mem_corridor_of_canonical
            (ValidatorCountedRows.cellBlock_mem_canonicalCorridor outer.write)
        · exact writeMiddle_mem_corridor outer between hbetween symbol hmiddle

/-- Configuration at the inner write symbol. -/
def writeComparisonConfig
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration (compareInnerWriteState outer.write)
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
            (List.append (rowAfterWriteBlocks outer .done) between))
          [.marker001])
        (List.replicate paired .marker010))
      [.done, ValidatorCountedRows.cellBlock inner.read])
    (ValidatorCountedRows.cellBlock inner.write ::
      List.append (rowAfterWriteBlocks inner innerEnd) rest)

/-- Shuttle from the outer write symbol to the inner write symbol. -/
theorem reaches_write_comparison
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 29
          (List.append
            (List.append
              (List.append
                (List.append before [.marker001])
                (List.replicate paired .marker010)) [.done])
            [ValidatorCountedRows.cellBlock outer.read])
          (selectedPairWriteRight outer inner paired
            between innerEnd rest))
        (writeComparisonConfig outer inner paired before
          between innerEnd rest) := by
  let markers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let middle : Word ValidatorBlockSymbol :=
    List.append (rowAfterWriteBlocks outer .done) between
  let innerAfterWrite : Word ValidatorBlockSymbol :=
    List.append (rowAfterWriteBlocks inner innerEnd) rest
  let base : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (List.append (List.append before [.marker001]) markers) [.done])
      [ValidatorCountedRows.cellBlock outer.read]

  have houterWrite := reaches_one_right
    (state := 29) (target := writeSeekMarkerState outer.write)
    (read := ValidatorCountedRows.cellBlock outer.write)
    (write := ValidatorCountedRows.cellBlock outer.write)
    (by cases outer.write with
      | none => decide
      | some bit => cases bit <;> decide)
    base
    (List.append middle
      (.marker001 ::
        List.append markers
          (.done :: ValidatorCountedRows.cellBlock inner.read ::
            ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite)))
  have hmiddleRun := reaches_scan_right_list middle
    (fun symbol hsymbol => lookup_writeSeekMarker_corridor outer.write symbol
      (writeMiddle_mem_corridor outer between hbetween symbol
        (by simpa [middle] using hsymbol)))
    (List.append base [ValidatorCountedRows.cellBlock outer.write])
    (.marker001 ::
      List.append markers
        (.done :: ValidatorCountedRows.cellBlock inner.read ::
          ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite))
  have hinnerMarker := reaches_one_right
    (state := writeSeekMarkerState outer.write)
    (target := writeSeekSourceState outer.write)
    (read := .marker001) (write := .marker001)
    (by cases outer.write with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append base [ValidatorCountedRows.cellBlock outer.write]) middle)
    (List.append markers
      (.done :: ValidatorCountedRows.cellBlock inner.read ::
        ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite))
  have hmarkers := reaches_scan_right_markers
    (state := writeSeekSourceState outer.write)
    (by cases outer.write with
      | none => decide
      | some bit => cases bit <;> decide)
    paired
    (List.append
      (List.append
        (List.append base [ValidatorCountedRows.cellBlock outer.write]) middle)
      [.marker001])
    (.done :: ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite)
  have hdone := reaches_one_right
    (state := writeSeekSourceState outer.write)
    (target := writeSkipReadState outer.write)
    (read := .done) (write := .done)
    (by cases outer.write with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append base [ValidatorCountedRows.cellBlock outer.write]) middle)
        [.marker001]) markers)
    (ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite)
  have hread := reaches_one_right
    (state := writeSkipReadState outer.write)
    (target := compareInnerWriteState outer.write)
    (read := ValidatorCountedRows.cellBlock inner.read)
    (write := ValidatorCountedRows.cellBlock inner.read)
    (by
      cases outer.write with
      | none => cases inner.read with
        | none => decide
        | some bit => cases bit <;> decide
      | some outerBit =>
          cases outerBit <;>
            cases inner.read with
            | none => decide
            | some innerBit => cases innerBit <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append base [ValidatorCountedRows.cellBlock outer.write]) middle)
          [.marker001]) markers) [.done])
    (ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite)
  have hrun := houterWrite.trans
    (hmiddleRun.trans (hinnerMarker.trans (hmarkers.trans (hdone.trans hread))))
  simpa [writeComparisonConfig, selectedPairWriteRight,
    markedSourceInterior, rowAfterSourceBlocks, rowAfterReadBlocks,
    base, middle, innerAfterWrite, markers, List.append_assoc] using hrun

/-- Unequal writes reach the explicit conflict state. -/
theorem reaches_write_conflict
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hwrite : outer.write ≠ inner.write) :
    ReachesConflict
      (writeComparisonConfig outer inner paired before
        between innerEnd rest) := by
  let logicalLeft : Word ValidatorBlockSymbol :=
    List.append
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
            (List.append (rowAfterWriteBlocks outer .done) between))
          [.marker001])
        (List.replicate paired .marker010))
      [.done, ValidatorCountedRows.cellBlock inner.read]
  let innerAfterWrite : Word ValidatorBlockSymbol :=
    List.append (rowAfterWriteBlocks inner innerEnd) rest
  have hstep := reaches_one_right
    (state := compareInnerWriteState outer.write) (target := 100)
    (read := ValidatorCountedRows.cellBlock inner.write)
    (write := ValidatorCountedRows.cellBlock inner.write)
    (lookup_compare_write_ne outer.write inner.write hwrite)
    logicalLeft innerAfterWrite
  refine ⟨List.append logicalLeft
      [ValidatorCountedRows.cellBlock inner.write], innerAfterWrite, ?_⟩
  simpa [writeComparisonConfig, logicalLeft, innerAfterWrite,
    configuration, ValidatorBlockDescription.blockConfiguration,
    List.append_assoc] using hstep

/-- Equal writes return to the outer move field. -/
theorem reaches_equal_write_to_move
    (outer inner : TransitionDescription) (paired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (hwrite : outer.write = inner.write) :
    blockDescription.Reaches
        (writeComparisonConfig outer inner paired before
          between innerEnd rest)
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
            between innerEnd rest)) := by
  let markers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let middle : Word ValidatorBlockSymbol :=
    List.append (rowAfterWriteBlocks outer .done) between
  let innerAfterWrite : Word ValidatorBlockSymbol :=
    List.append (rowAfterWriteBlocks inner innerEnd) rest
  let innerPrefix : Word ValidatorBlockSymbol :=
    List.append markers
      [.done, ValidatorCountedRows.cellBlock inner.read]
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append markers
      (.done :: ValidatorCountedRows.cellBlock outer.read ::
        ValidatorCountedRows.cellBlock outer.write :: middle)

  have hcompare := reaches_cross_scan_left_word innerPrefix
    (entry := compareInnerWriteState outer.write) (scan := 42)
    (entryRead := ValidatorCountedRows.cellBlock inner.write)
    (entryWrite := ValidatorCountedRows.cellBlock inner.write)
    (boundary := .marker001)
    (lookup_compare_write_eq outer.write inner.write hwrite)
    (by
      intro symbol hsymbol
      unfold innerPrefix at hsymbol
      rcases List.mem_append.mp hsymbol with hmarkers | hfixed
      · have heq : symbol = .marker010 :=
          (List.mem_replicate.mp hmarkers).2
        subst symbol
        decide
      · rcases List.mem_cons.mp hfixed with hdone | hread
        · subst symbol
          decide
        · have heq : symbol = ValidatorCountedRows.cellBlock inner.read :=
            List.mem_singleton.mp hread
          subst symbol
          cases inner.read with
          | none => decide
          | some bit => cases bit <;> decide)
    (List.append (List.append before [.marker001]) returnCorridor)
    innerAfterWrite
  have hreturn := reaches_cross_scan_left_word returnCorridor
    (entry := 42) (scan := 43)
    (entryRead := .marker001) (entryWrite := .marker001)
    (boundary := .marker001)
    (by decide)
    (fun symbol hsymbol => lookup_state43_corridor symbol
      (writeReturnCorridor_mem outer paired between hbetween symbol
        (by simpa [returnCorridor, middle, markers] using hsymbol)))
    before
    (List.append innerPrefix
      (ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite))
  have houterMarker := reaches_one_right
    (state := 43) (target := 44)
    (read := .marker001) (write := .marker001)
    (by decide) before
    (List.append returnCorridor
      (.marker001 :: List.append innerPrefix
        (ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite)))
  have hmarkers := reaches_scan_right_markers
    (state := 44) (by decide) paired
    (List.append before [.marker001])
    (.done :: ValidatorCountedRows.cellBlock outer.read ::
      ValidatorCountedRows.cellBlock outer.write ::
      List.append middle
        (.marker001 :: List.append innerPrefix
          (ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite)))
  have hdone := reaches_one_right
    (state := 44) (target := 45)
    (read := .done) (write := .done) (by decide)
    (List.append
      (List.append before [.marker001]) markers)
    (ValidatorCountedRows.cellBlock outer.read ::
      ValidatorCountedRows.cellBlock outer.write ::
      List.append middle
        (.marker001 :: List.append innerPrefix
          (ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite)))
  have hread := reaches_one_right
    (state := 45) (target := 46)
    (read := ValidatorCountedRows.cellBlock outer.read)
    (write := ValidatorCountedRows.cellBlock outer.read)
    (by cases outer.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append (List.append before [.marker001]) markers) [.done])
    (ValidatorCountedRows.cellBlock outer.write ::
      List.append middle
        (.marker001 :: List.append innerPrefix
          (ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite)))
  have hwriteOuter := reaches_one_right
    (state := 46) (target := 47)
    (read := ValidatorCountedRows.cellBlock outer.write)
    (write := ValidatorCountedRows.cellBlock outer.write)
    (by cases outer.write with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append (List.append before [.marker001]) markers) [.done])
      [ValidatorCountedRows.cellBlock outer.read])
    (List.append middle
      (.marker001 :: List.append innerPrefix
        (ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite)))
  have hmarkers' : blockDescription.Reaches
      (configuration 44 (List.append before [.marker001])
        (List.append returnCorridor
          (.marker001 :: List.append innerPrefix
            (ValidatorCountedRows.cellBlock inner.write :: innerAfterWrite))))
      (configuration 44
        (List.append (List.append before [.marker001]) markers)
        (.done :: ValidatorCountedRows.cellBlock outer.read ::
          ValidatorCountedRows.cellBlock outer.write ::
          List.append middle
            (.marker001 :: List.append innerPrefix
              (ValidatorCountedRows.cellBlock inner.write ::
                innerAfterWrite)))) := by
    simpa [returnCorridor, List.append_assoc] using hmarkers
  have hrun := hcompare.trans
    (hreturn.trans (houterMarker.trans
      (hmarkers'.trans (hdone.trans (hread.trans hwriteOuter)))))
  simpa [writeComparisonConfig, selectedPairMoveRight,
    markedSourceInterior, rowAfterSourceBlocks, rowAfterReadBlocks,
    innerPrefix, returnCorridor, middle, innerAfterWrite, markers,
    List.append_assoc] using hrun

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
