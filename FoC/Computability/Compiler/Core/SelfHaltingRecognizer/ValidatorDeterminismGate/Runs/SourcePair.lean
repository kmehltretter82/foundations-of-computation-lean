import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.Basic

set_option doc.verso true

/-!
# Exact-code validator: source-key pairing runs

The determinism gate compares two unary source fields by marking one tick on
each trip.  These lemmas expose that loop independently of the action fields
and of the outer row iteration.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

theorem lookup_state6_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 6 symbol =
      some
        { source := 6
          read := symbol
          write := symbol
          move := Direction.right
          target := 6 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem lookup_state9_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 9 symbol =
      some
        { source := 9
          read := symbol
          write := symbol
          move := Direction.left
          target := 9 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

/-- Mutable source-field layout at state 5.  {lean}`middle` starts just after the
outer source terminator and ends immediately before the selected inner-row
marker; {lean}`after` starts just after the inner source terminator. -/
def sourcePairRight
    (outerRemaining innerRemaining paired : Nat)
    (middle after : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate paired .marker010)
    (List.append (List.replicate outerRemaining .tick)
      (.done ::
        List.append middle
          (.marker001 ::
            List.append (List.replicate paired .marker010)
              (List.append (List.replicate innerRemaining .tick)
                (.done :: after)))))

theorem sourcePairCorridor_mem
    (outerRemaining paired : Nat)
    (middle : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.append (List.replicate paired .marker010)
          (List.append (List.replicate outerRemaining .tick)
            (.done :: middle)))) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  rcases List.mem_append.mp hmem with hmarkers | htail
  · have heq : symbol = .marker010 :=
      (List.mem_replicate.mp hmarkers).2
    subst symbol
    exact ValidatorCountedRows.marker010_mem_corridor
  · rcases List.mem_append.mp htail with hticks | htail
    · have heq : symbol = .tick :=
        (List.mem_replicate.mp hticks).2
      subst symbol
      exact ValidatorCountedRows.tick_mem_corridor
    · rcases List.mem_cons.mp htail with hdone | hmiddle'
      · subst symbol
        exact ValidatorCountedRows.done_mem_corridor
      · exact hmiddle symbol hmiddle'

/-- Pair one tick from each selected source field and return to the beginning
of the outer source field. -/
theorem reaches_pair_source_tick
    (outerRemaining innerRemaining paired : Nat)
    (before middle after : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 5 (List.append before [.marker001])
          (sourcePairRight (outerRemaining + 1)
            (innerRemaining + 1) paired middle after))
        (configuration 5 (List.append before [.marker001])
          (sourcePairRight outerRemaining innerRemaining
            (paired + 1) middle after)) := by
  let outerMarkers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let innerMarkers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let outerRest : Word ValidatorBlockSymbol :=
    List.append (List.replicate outerRemaining .tick)
      (.done :: middle)
  let innerRest : Word ValidatorBlockSymbol :=
    List.append (List.replicate innerRemaining .tick) (.done :: after)
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append
      (List.append outerMarkers [.marker010]) outerRest

  let c5 := configuration 7
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append (List.append before [.marker001]) outerMarkers)
            [.marker010]) outerRest)
        [.marker001]) innerMarkers)
    (.tick :: innerRest)
  let c6 := configuration 8
    (List.append (List.append before [.marker001]) returnCorridor)
    (.marker001 :: List.append innerMarkers (.marker010 :: innerRest))

  have houterMarkers := reaches_scan_right_markers
    (state := 5) (by decide) paired
    (List.append before [.marker001])
    (.tick :: List.append outerRest
      (.marker001 :: List.append innerMarkers (.tick :: innerRest)))
  have houterTick := reaches_one_right
    (state := 5) (target := 6)
    (read := .tick) (write := .marker010)
    (by decide)
    (List.append (List.append before [.marker001]) outerMarkers)
    (List.append outerRest
      (.marker001 :: List.append innerMarkers (.tick :: innerRest)))
  have houterRest := reaches_scan_right_list outerRest
    (fun symbol hsymbol =>
      lookup_state6_corridor symbol
        (sourcePairCorridor_mem outerRemaining 0 middle hmiddle symbol
          (by simpa [outerRest] using hsymbol)))
    (List.append
      (List.append (List.append before [.marker001]) outerMarkers)
      [.marker010])
    (.marker001 :: List.append innerMarkers (.tick :: innerRest))
  have hinnerMarker := reaches_one_right
    (state := 6) (target := 7)
    (read := .marker001) (write := .marker001)
    (by decide)
    (List.append
      (List.append
        (List.append (List.append before [.marker001]) outerMarkers)
        [.marker010]) outerRest)
    (List.append innerMarkers (.tick :: innerRest))
  have hinnerMarkers := reaches_scan_right_markers
    (state := 7) (by decide) paired
    (List.append
      (List.append
        (List.append
          (List.append (List.append before [.marker001]) outerMarkers)
          [.marker010]) outerRest)
      [.marker001])
    (.tick :: innerRest)
  have hpairInner := reaches_cross_scan_left_word innerMarkers
    (entry := 7) (scan := 8)
    (entryRead := .tick) (entryWrite := .marker010)
    (boundary := .marker001)
    (by decide)
    (by
      intro symbol hsymbol
      have heq : symbol = .marker010 :=
        (List.mem_replicate.mp hsymbol).2
      subst symbol
      decide)
    (List.append (List.append before [.marker001]) returnCorridor)
    innerRest
  have hreturn := reaches_cross_scan_left_word returnCorridor
    (entry := 8) (scan := 9)
    (entryRead := .marker001) (entryWrite := .marker001)
    (boundary := .marker001)
    (by decide)
    (fun symbol hsymbol =>
      lookup_state9_corridor symbol
        (sourcePairCorridor_mem outerRemaining (paired + 1)
          middle hmiddle symbol (by simpa [returnCorridor,
            outerMarkers, outerRest, List.replicate_succ',
            List.append_assoc] using hsymbol)))
    before
    (List.append innerMarkers (.marker010 :: innerRest))
  have houterMarker := reaches_one_right
    (state := 9) (target := 5)
    (read := .marker001) (write := .marker001)
    (by decide) before
    (List.append returnCorridor
      (.marker001 :: List.append innerMarkers (.marker010 :: innerRest)))

  have hstart : blockDescription.Reaches
      (configuration 5 (List.append before [.marker001])
        (sourcePairRight (outerRemaining + 1) (innerRemaining + 1)
          paired middle after)) c5 := by
    have hrun := houterMarkers.trans (houterTick.trans
      (houterRest.trans (hinnerMarker.trans hinnerMarkers)))
    simpa [c5, sourcePairRight, outerMarkers, innerMarkers,
      outerRest, innerRest, List.replicate_succ,
      List.append_assoc] using hrun
  have h56 : blockDescription.Reaches c5 c6 := by
    simpa [c5, c6, returnCorridor, outerMarkers,
      List.append_assoc] using hpairInner
  have hend : blockDescription.Reaches c6
      (configuration 5 (List.append before [.marker001])
        (sourcePairRight outerRemaining innerRemaining
          (paired + 1) middle after)) := by
    have hrun := hreturn.trans houterMarker
    simpa [c6, sourcePairRight, outerMarkers, innerMarkers,
      outerRest, innerRest, returnCorridor, List.replicate_succ',
      List.append_assoc] using hrun
  exact hstart.trans (h56.trans hend)

/-- Pair all ticks of two equal source fields. -/
theorem reaches_pair_equal_sources
    (count paired : Nat)
    (before middle after : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 5 (List.append before [.marker001])
          (sourcePairRight count count paired middle after))
        (configuration 5 (List.append before [.marker001])
          (sourcePairRight 0 0 (paired + count) middle after)) := by
  induction count generalizing paired with
  | zero =>
      simpa using ValidatorBlockDescription.reaches_refl blockDescription
        (configuration 5 (List.append before [.marker001])
          (sourcePairRight 0 0 paired middle after))
  | succ count ih =>
      have hpair := reaches_pair_source_tick count count paired
        before middle after hmiddle
      have htail := ih (paired + 1)
      have hpaired : paired + (count + 1) = (paired + 1) + count := by
        lia
      simpa [hpaired] using hpair.trans htail

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
