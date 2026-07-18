import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.SourcePair

set_option doc.verso true

/-!
# Exact-code validator: equal-source handoff

After both unary source fields are exhausted, the machine verifies the second
terminator, returns to the selected outer row, and positions the head on its
read symbol.  The paired source ticks intentionally remain marked until the
common pair-cleanup pass.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

theorem lookup_state10_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 10 symbol =
      some
        { source := 10
          read := symbol
          write := symbol
          move := Direction.right
          target := 10 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem lookup_state13_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 13 symbol =
      some
        { source := 13
          read := symbol
          write := symbol
          move := Direction.left
          target := 13 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem outerReturnCorridor_mem
    (paired : Nat) (middle : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.append (List.replicate paired .marker010)
          (.done :: middle))) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  rcases List.mem_append.mp hmem with hmarkers | htail
  · have heq : symbol = .marker010 :=
      (List.mem_replicate.mp hmarkers).2
    subst symbol
    exact ValidatorCountedRows.marker010_mem_corridor
  · rcases List.mem_cons.mp htail with hdone | hmiddle'
    · subst symbol
      exact ValidatorCountedRows.done_mem_corridor
    · exact hmiddle symbol hmiddle'

/-- Equal marked source fields hand off at the outer read symbol. -/
theorem reaches_equal_source_to_read
    (paired : Nat)
    (before middle after : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 5 (List.append before [.marker001])
          (sourcePairRight 0 0 paired middle after))
        (configuration 15
          (List.append
            (List.append (List.append before [.marker001])
              (List.replicate paired .marker010)) [.done])
          (List.append middle
            (.marker001 ::
              List.append (List.replicate paired .marker010)
                (.done :: after)))) := by
  let markers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append markers (.done :: middle)

  let c5 := configuration 11
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append (List.append before [.marker001]) markers) [.done])
          middle) [.marker001]) markers)
    (.done :: after)
  let c6 := configuration 12
    (List.append (List.append before [.marker001]) returnCorridor)
    (.marker001 :: List.append markers (.done :: after))
  let c8 := configuration 14 (List.append before [.marker001])
    (List.append returnCorridor
      (.marker001 :: List.append markers (.done :: after)))
  let c9 := configuration 14
    (List.append (List.append before [.marker001]) markers)
    (.done :: List.append middle
      (.marker001 :: List.append markers (.done :: after)))

  have houterMarkers := reaches_scan_right_markers
    (state := 5) (by decide) paired
    (List.append before [.marker001])
    (.done :: List.append middle
      (.marker001 :: List.append markers (.done :: after)))
  have houterDone := reaches_one_right
    (state := 5) (target := 10)
    (read := .done) (write := .done)
    (by decide)
    (List.append (List.append before [.marker001]) markers)
    (List.append middle
      (.marker001 :: List.append markers (.done :: after)))
  have hmiddleRun := reaches_scan_right_list middle
    (fun symbol hsymbol =>
      lookup_state10_corridor symbol (hmiddle symbol hsymbol))
    (List.append
      (List.append (List.append before [.marker001]) markers) [.done])
    (.marker001 :: List.append markers (.done :: after))
  have hinnerMarker := reaches_one_right
    (state := 10) (target := 11)
    (read := .marker001) (write := .marker001)
    (by decide)
    (List.append
      (List.append
        (List.append (List.append before [.marker001]) markers) [.done])
      middle)
    (List.append markers (.done :: after))
  have hinnerMarkers := reaches_scan_right_markers
    (state := 11) (by decide) paired
    (List.append
      (List.append
        (List.append
          (List.append (List.append before [.marker001]) markers) [.done])
        middle) [.marker001])
    (.done :: after)
  have hinnerDone := reaches_cross_scan_left_word markers
    (entry := 11) (scan := 12)
    (entryRead := .done) (entryWrite := .done)
    (boundary := .marker001)
    (by decide)
    (by
      intro symbol hsymbol
      have heq : symbol = .marker010 :=
        (List.mem_replicate.mp hsymbol).2
      subst symbol
      decide)
    (List.append (List.append before [.marker001]) returnCorridor)
    after
  have hreturn := reaches_cross_scan_left_word returnCorridor
    (entry := 12) (scan := 13)
    (entryRead := .marker001) (entryWrite := .marker001)
    (boundary := .marker001)
    (by decide)
    (fun symbol hsymbol =>
      lookup_state13_corridor symbol
        (outerReturnCorridor_mem paired middle hmiddle
          symbol hsymbol))
    before
    (List.append markers (.done :: after))
  have houterMarker := reaches_one_right
    (state := 13) (target := 14)
    (read := .marker001) (write := .marker001)
    (by decide) before
    (List.append returnCorridor
      (.marker001 :: List.append markers (.done :: after)))
  have hreturnMarkers := reaches_scan_right_markers
    (state := 14) (by decide) paired
    (List.append before [.marker001])
    (.done :: List.append middle
      (.marker001 :: List.append markers (.done :: after)))
  have hreturnDone := reaches_one_right
    (state := 14) (target := 15)
    (read := .done) (write := .done)
    (by decide)
    (List.append (List.append before [.marker001]) markers)
    (List.append middle
      (.marker001 :: List.append markers (.done :: after)))

  have hstart : blockDescription.Reaches
      (configuration 5 (List.append before [.marker001])
        (sourcePairRight 0 0 paired middle after)) c5 := by
    have hrun := houterMarkers.trans (houterDone.trans
      (hmiddleRun.trans (hinnerMarker.trans hinnerMarkers)))
    simpa [c5, sourcePairRight, markers, List.append_assoc] using hrun
  have h56 : blockDescription.Reaches c5 c6 := by
    simpa [c5, c6, returnCorridor, List.append_assoc] using hinnerDone
  have h68 : blockDescription.Reaches c6 c8 := by
    simpa [c6, c8] using hreturn.trans houterMarker
  have h89 : blockDescription.Reaches c8 c9 := by
    simpa [c8, c9, returnCorridor, List.append_assoc] using hreturnMarkers
  have hend : blockDescription.Reaches c9
      (configuration 15
        (List.append
          (List.append (List.append before [.marker001]) markers) [.done])
        (List.append middle
          (.marker001 :: List.append markers (.done :: after)))) := by
    simpa [c9] using hreturnDone
  simpa [markers] using hstart.trans
    (h56.trans (h68.trans (h89.trans hend)))

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
