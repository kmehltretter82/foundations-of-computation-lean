import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.PairMove

set_option doc.verso true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Exact-code validator: target-field comparison

Unary target fields are paired after the action components agree.  Equality
reaches state 82 on the inner target terminator; either unequal-length branch
reaches the explicit conflict state.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

private theorem lookup_state65_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 65 symbol =
      some
        { source := 65, read := symbol, write := symbol
          move := Direction.right, target := 65 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem lookup_state71_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 71 symbol =
      some
        { source := 71, read := symbol, write := symbol
          move := Direction.left, target := 71 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem lookup_state72_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 72 symbol =
      some
        { source := 72, read := symbol, write := symbol
          move := Direction.left, target := 72 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

private theorem lookup_state77_corridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.lookup 77 symbol =
      some
        { source := 77, read := symbol, write := symbol
          move := Direction.right, target := 77 } := by
  cases symbol <;>
    simp [ValidatorCountedRows.corridorSymbols,
      ValidatorCountedRows.canonicalCorridorSymbols] at hmem <;>
    decide

/-- Mutable target-pair layout at state 64. -/
def targetPairRight
    (_outer inner : TransitionDescription)
    (sourcePaired outerRemaining innerRemaining targetPaired : Nat)
    (between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate targetPaired .marker010)
    (List.append (List.replicate outerRemaining .tick)
      (.done ::
        List.append between
          (.marker001 ::
            List.append (List.replicate sourcePaired .marker010)
              (.done :: ValidatorCountedRows.cellBlock inner.read ::
                ValidatorCountedRows.cellBlock inner.write ::
                ValidatorCountedRows.directionBlock inner.move ::
                List.append (List.replicate targetPaired .marker010)
                  (List.append (List.replicate innerRemaining .tick)
                    (innerEnd :: rest))))))

/-- Fixed left context at state 64 before the outer target field. -/
def targetPairLeft
    (outer : TransitionDescription) (sourcePaired : Nat)
    (before : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append
    (List.append
      (List.append
        (List.append
          (List.append before [.marker001])
          (List.replicate sourcePaired .marker010)) [.done])
      [ValidatorCountedRows.cellBlock outer.read])
    [ValidatorCountedRows.cellBlock outer.write,
      ValidatorCountedRows.directionBlock outer.move]

/-- The named state-64 pair layout starts with no target markers. -/
theorem selectedPairTargetRight_eq_targetPairRight
    (outer inner : TransitionDescription) (sourcePaired : Nat)
    (between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    selectedPairTargetRight outer inner sourcePaired between innerEnd rest =
      targetPairRight outer inner sourcePaired outer.target inner.target 0
        between innerEnd rest := by
  simp [selectedPairTargetRight, targetPairRight, markedSourceInterior,
    rowAfterSourceBlocks, rowAfterReadBlocks, rowAfterWriteBlocks,
    rowTargetAndEndBlocks, List.append_assoc]

private theorem innerPrefix_mem_corridor
    (inner : TransitionDescription) (sourcePaired targetPaired : Nat)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.append (List.replicate sourcePaired .marker010)
          (.done :: ValidatorCountedRows.cellBlock inner.read ::
            ValidatorCountedRows.cellBlock inner.write ::
            ValidatorCountedRows.directionBlock inner.move ::
            List.replicate targetPaired .marker010))) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  rcases List.mem_append.mp hmem with hsource | htail
  · have heq : symbol = .marker010 :=
      (List.mem_replicate.mp hsource).2
    subst symbol
    exact ValidatorCountedRows.marker010_mem_corridor
  · rcases List.mem_cons.mp htail with hdone | htail
    · subst symbol
      exact ValidatorCountedRows.done_mem_corridor
    · rcases List.mem_cons.mp htail with hread | htail
      · subst symbol
        exact ValidatorCountedRows.mem_corridor_of_canonical
          (ValidatorCountedRows.cellBlock_mem_canonicalCorridor inner.read)
      · rcases List.mem_cons.mp htail with hwrite | htail
        · subst symbol
          exact ValidatorCountedRows.mem_corridor_of_canonical
            (ValidatorCountedRows.cellBlock_mem_canonicalCorridor inner.write)
        · rcases List.mem_cons.mp htail with hmove | htarget
          · subst symbol
            exact ValidatorCountedRows.mem_corridor_of_canonical
              (ValidatorCountedRows.directionBlock_mem_canonicalCorridor
                inner.move)
          · have heq : symbol = .marker010 :=
              (List.mem_replicate.mp htarget).2
            subst symbol
            exact ValidatorCountedRows.marker010_mem_corridor

private theorem targetReturnCorridor_mem
    (outer : TransitionDescription)
    (sourcePaired outerRemaining targetPaired : Nat)
    (between : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.append (List.replicate sourcePaired .marker010)
          (.done :: ValidatorCountedRows.cellBlock outer.read ::
            ValidatorCountedRows.cellBlock outer.write ::
            ValidatorCountedRows.directionBlock outer.move ::
            List.append (List.replicate targetPaired .marker010)
              (.marker010 ::
                List.append (List.replicate outerRemaining .tick)
                  (.done :: between))))) :
    symbol ∈ ValidatorCountedRows.corridorSymbols := by
  rcases List.mem_append.mp hmem with hsource | htail
  · have heq : symbol = .marker010 :=
      (List.mem_replicate.mp hsource).2
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
        · rcases List.mem_cons.mp htail with hmove | htail
          · subst symbol
            exact ValidatorCountedRows.mem_corridor_of_canonical
              (ValidatorCountedRows.directionBlock_mem_canonicalCorridor
                outer.move)
          · rcases List.mem_append.mp htail with htarget | htail
            · have heq : symbol = .marker010 :=
                (List.mem_replicate.mp htarget).2
              subst symbol
              exact ValidatorCountedRows.marker010_mem_corridor
            · rcases List.mem_cons.mp htail with hmarker | htail
              · subst symbol
                exact ValidatorCountedRows.marker010_mem_corridor
              · rcases List.mem_append.mp htail with htick | htail
                · have heq : symbol = .tick :=
                    (List.mem_replicate.mp htick).2
                  subst symbol
                  exact ValidatorCountedRows.tick_mem_corridor
                · rcases List.mem_cons.mp htail with hdone | hbetween'
                  · subst symbol
                    exact ValidatorCountedRows.done_mem_corridor
                  · exact hbetween symbol hbetween'

private def targetInnerProbeConfig
    (outer inner : TransitionDescription)
    (sourcePaired outerRemaining innerRemaining targetPaired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration 70
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append
                    (List.append
                      (targetPairLeft outer sourcePaired before)
                      (List.replicate targetPaired .marker010)) [.marker010])
                  (List.append (List.replicate outerRemaining .tick)
                    (.done :: between))) [.marker001])
              (List.replicate sourcePaired .marker010)) [.done])
          [ValidatorCountedRows.cellBlock inner.read])
        [ValidatorCountedRows.cellBlock inner.write])
      (ValidatorCountedRows.directionBlock inner.move ::
        List.replicate targetPaired .marker010))
    (List.append (List.replicate innerRemaining .tick) (innerEnd :: rest))

/-- Mark one outer target tick and cross the fixed inner-row prefix to the
corresponding inner-target probe. -/
private theorem reaches_target_inner_probe
    (outer inner : TransitionDescription)
    (sourcePaired outerRemaining innerRemaining targetPaired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 64 (targetPairLeft outer sourcePaired before)
          (targetPairRight outer inner sourcePaired (outerRemaining + 1)
            innerRemaining targetPaired between innerEnd rest))
        (targetInnerProbeConfig outer inner sourcePaired outerRemaining
          innerRemaining targetPaired before between innerEnd rest) := by
  let sourceMarkers : Word ValidatorBlockSymbol :=
    List.replicate sourcePaired .marker010
  let targetMarkers : Word ValidatorBlockSymbol :=
    List.replicate targetPaired .marker010
  let outerRest : Word ValidatorBlockSymbol :=
    List.append (List.replicate outerRemaining .tick) (.done :: between)
  let innerTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate innerRemaining .tick) (innerEnd :: rest)
  let innerPrefix : Word ValidatorBlockSymbol :=
    List.append sourceMarkers
      (.done :: ValidatorCountedRows.cellBlock inner.read ::
        ValidatorCountedRows.cellBlock inner.write ::
        ValidatorCountedRows.directionBlock inner.move :: targetMarkers)
  let base := targetPairLeft outer sourcePaired before
  have houterMarkers := reaches_scan_right_markers
    (state := 64) (by decide) targetPaired base
    (.tick :: List.append outerRest
      (.marker001 :: List.append innerPrefix innerTail))
  have houterTick := reaches_one_right
    (state := 64) (target := 65)
    (read := .tick) (write := .marker010) (by decide)
    (List.append base targetMarkers)
    (List.append outerRest
      (.marker001 :: List.append innerPrefix innerTail))
  have houterRest := reaches_scan_right_list outerRest
    (fun symbol hsymbol => lookup_state65_corridor symbol
      (by
        unfold outerRest at hsymbol
        rcases List.mem_append.mp hsymbol with htick | htail
        · have heq : symbol = .tick := (List.mem_replicate.mp htick).2
          subst symbol
          exact ValidatorCountedRows.tick_mem_corridor
        · rcases List.mem_cons.mp htail with hdone | hbetween'
          · subst symbol
            exact ValidatorCountedRows.done_mem_corridor
          · exact hbetween symbol hbetween'))
    (List.append (List.append base targetMarkers) [.marker010])
    (.marker001 :: List.append innerPrefix innerTail)
  have hinnerMarker := reaches_one_right
    (state := 65) (target := 66)
    (read := .marker001) (write := .marker001) (by decide)
    (List.append
      (List.append (List.append base targetMarkers) [.marker010]) outerRest)
    (List.append innerPrefix innerTail)
  have hsourceMarkers := reaches_scan_right_markers
    (state := 66) (by decide) sourcePaired
    (List.append
      (List.append
        (List.append (List.append base targetMarkers) [.marker010]) outerRest)
      [.marker001])
    (.done :: ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append targetMarkers innerTail)
  have hdone := reaches_one_right
    (state := 66) (target := 67)
    (read := .done) (write := .done) (by decide)
    (List.append
      (List.append
        (List.append
          (List.append (List.append base targetMarkers) [.marker010]) outerRest)
        [.marker001]) sourceMarkers)
    (ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append targetMarkers innerTail)
  have hread := reaches_one_right
    (state := 67) (target := 68)
    (read := ValidatorCountedRows.cellBlock inner.read)
    (write := ValidatorCountedRows.cellBlock inner.read)
    (by cases inner.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append (List.append base targetMarkers) [.marker010])
            outerRest) [.marker001]) sourceMarkers) [.done])
    (ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append targetMarkers innerTail)
  have hwrite := reaches_one_right
    (state := 68) (target := 69)
    (read := ValidatorCountedRows.cellBlock inner.write)
    (write := ValidatorCountedRows.cellBlock inner.write)
    (by cases inner.write with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append (List.append base targetMarkers) [.marker010])
              outerRest) [.marker001]) sourceMarkers) [.done])
      [ValidatorCountedRows.cellBlock inner.read])
    (ValidatorCountedRows.directionBlock inner.move ::
      List.append targetMarkers innerTail)
  have hmove := reaches_one_right
    (state := 69) (target := 70)
    (read := ValidatorCountedRows.directionBlock inner.move)
    (write := ValidatorCountedRows.directionBlock inner.move)
    (by cases inner.move <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append (List.append base targetMarkers) [.marker010])
                outerRest) [.marker001]) sourceMarkers) [.done])
        [ValidatorCountedRows.cellBlock inner.read])
      [ValidatorCountedRows.cellBlock inner.write])
    (List.append targetMarkers innerTail)
  have htarget := reaches_scan_right_markers
    (state := 70) (by decide) targetPaired
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append (List.append base targetMarkers) [.marker010])
                  outerRest) [.marker001]) sourceMarkers) [.done])
          [ValidatorCountedRows.cellBlock inner.read])
        [ValidatorCountedRows.cellBlock inner.write])
      [ValidatorCountedRows.directionBlock inner.move])
    innerTail
  have hfront := houterMarkers.trans
    (houterTick.trans (houterRest.trans hinnerMarker))
  have hfront' : blockDescription.Reaches
      (configuration 64 (targetPairLeft outer sourcePaired before)
        (targetPairRight outer inner sourcePaired (outerRemaining + 1)
          innerRemaining targetPaired between innerEnd rest))
      (configuration 66
        (List.append
          (List.append
            (List.append (List.append base targetMarkers) [.marker010])
            outerRest) [.marker001])
        (List.append sourceMarkers
          (.done :: ValidatorCountedRows.cellBlock inner.read ::
            ValidatorCountedRows.cellBlock inner.write ::
            ValidatorCountedRows.directionBlock inner.move ::
            List.append targetMarkers innerTail))) := by
    simpa [targetPairRight, base, sourceMarkers, targetMarkers, outerRest,
      innerTail, innerPrefix, List.replicate_succ, List.append_assoc] using hfront
  have hrun := hfront'.trans (hsourceMarkers.trans
    (hdone.trans (hread.trans (hwrite.trans (hmove.trans htarget)))))
  simpa [targetInnerProbeConfig, base, sourceMarkers, targetMarkers,
    outerRest, innerTail, List.append_assoc] using hrun

/-- Pair one target tick on each selected row. -/
theorem reaches_pair_target_tick
    (outer inner : TransitionDescription)
    (sourcePaired outerRemaining innerRemaining targetPaired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 64 (targetPairLeft outer sourcePaired before)
          (targetPairRight outer inner sourcePaired
            (outerRemaining + 1) (innerRemaining + 1) targetPaired
            between innerEnd rest))
        (configuration 64 (targetPairLeft outer sourcePaired before)
          (targetPairRight outer inner sourcePaired
            outerRemaining innerRemaining (targetPaired + 1)
            between innerEnd rest)) := by
  let sourceMarkers : Word ValidatorBlockSymbol :=
    List.replicate sourcePaired .marker010
  let targetMarkers : Word ValidatorBlockSymbol :=
    List.replicate targetPaired .marker010
  let outerRest : Word ValidatorBlockSymbol :=
    List.append (List.replicate outerRemaining .tick) (.done :: between)
  let innerRest : Word ValidatorBlockSymbol :=
    List.append (List.replicate innerRemaining .tick) (innerEnd :: rest)
  let innerPrefix : Word ValidatorBlockSymbol :=
    List.append sourceMarkers
      (.done :: ValidatorCountedRows.cellBlock inner.read ::
        ValidatorCountedRows.cellBlock inner.write ::
        ValidatorCountedRows.directionBlock inner.move :: targetMarkers)
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append sourceMarkers
      (.done :: ValidatorCountedRows.cellBlock outer.read ::
        ValidatorCountedRows.cellBlock outer.write ::
        ValidatorCountedRows.directionBlock outer.move ::
        List.append targetMarkers (.marker010 :: outerRest))
  have hprobe := reaches_target_inner_probe outer inner sourcePaired
    outerRemaining (innerRemaining + 1) targetPaired before between
    innerEnd rest hbetween
  have hpairInner := reaches_cross_scan_left_word innerPrefix
    (entry := 70) (scan := 71)
    (entryRead := .tick) (entryWrite := .marker010)
    (boundary := .marker001) (by decide)
    (fun symbol hsymbol => lookup_state71_corridor symbol
      (innerPrefix_mem_corridor inner sourcePaired targetPaired
        symbol (by simpa [innerPrefix, sourceMarkers, targetMarkers]
          using hsymbol)))
    (List.append (List.append before [.marker001]) returnCorridor)
    innerRest
  have hreturn := reaches_cross_scan_left_word returnCorridor
    (entry := 71) (scan := 72)
    (entryRead := .marker001) (entryWrite := .marker001)
    (boundary := .marker001) (by decide)
    (fun symbol hsymbol => lookup_state72_corridor symbol
      (targetReturnCorridor_mem outer sourcePaired outerRemaining
        targetPaired between hbetween symbol
        (by simpa [returnCorridor, sourceMarkers, targetMarkers,
          outerRest] using hsymbol)))
    before
    (List.append innerPrefix (.marker010 :: innerRest))
  have houterMarker := reaches_one_right
    (state := 72) (target := 73)
    (read := .marker001) (write := .marker001) (by decide)
    before
    (List.append returnCorridor
      (.marker001 :: List.append innerPrefix (.marker010 :: innerRest)))
  have hsourceReturn := reaches_scan_right_markers
    (state := 73) (by decide) sourcePaired
    (List.append before [.marker001])
    (.done :: ValidatorCountedRows.cellBlock outer.read ::
      ValidatorCountedRows.cellBlock outer.write ::
      ValidatorCountedRows.directionBlock outer.move ::
      List.append targetMarkers
        (.marker010 :: List.append outerRest
          (.marker001 :: List.append innerPrefix (.marker010 :: innerRest))))
  have hdoneReturn := reaches_one_right
    (state := 73) (target := 74)
    (read := .done) (write := .done) (by decide)
    (List.append (List.append before [.marker001]) sourceMarkers)
    (ValidatorCountedRows.cellBlock outer.read ::
      ValidatorCountedRows.cellBlock outer.write ::
      ValidatorCountedRows.directionBlock outer.move ::
      List.append targetMarkers
        (.marker010 :: List.append outerRest
          (.marker001 :: List.append innerPrefix (.marker010 :: innerRest))))
  have hreadReturn := reaches_one_right
    (state := 74) (target := 75)
    (read := ValidatorCountedRows.cellBlock outer.read)
    (write := ValidatorCountedRows.cellBlock outer.read)
    (by cases outer.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append (List.append before [.marker001]) sourceMarkers) [.done])
    (ValidatorCountedRows.cellBlock outer.write ::
      ValidatorCountedRows.directionBlock outer.move ::
      List.append targetMarkers
        (.marker010 :: List.append outerRest
          (.marker001 :: List.append innerPrefix (.marker010 :: innerRest))))
  have hwriteReturn := reaches_one_right
    (state := 75) (target := 76)
    (read := ValidatorCountedRows.cellBlock outer.write)
    (write := ValidatorCountedRows.cellBlock outer.write)
    (by cases outer.write with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append (List.append before [.marker001]) sourceMarkers) [.done])
      [ValidatorCountedRows.cellBlock outer.read])
    (ValidatorCountedRows.directionBlock outer.move ::
      List.append targetMarkers
        (.marker010 :: List.append outerRest
          (.marker001 :: List.append innerPrefix (.marker010 :: innerRest))))
  have hmoveReturn := reaches_one_right
    (state := 76) (target := 64)
    (read := ValidatorCountedRows.directionBlock outer.move)
    (write := ValidatorCountedRows.directionBlock outer.move)
    (by cases outer.move <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append (List.append before [.marker001]) sourceMarkers) [.done])
        [ValidatorCountedRows.cellBlock outer.read])
      [ValidatorCountedRows.cellBlock outer.write])
    (List.append targetMarkers
      (.marker010 :: List.append outerRest
        (.marker001 :: List.append innerPrefix (.marker010 :: innerRest))))

  have hprobe' : blockDescription.Reaches
      (configuration 64 (targetPairLeft outer sourcePaired before)
        (targetPairRight outer inner sourcePaired (outerRemaining + 1)
          (innerRemaining + 1) targetPaired between innerEnd rest))
      (configuration 70
        (List.append
          (List.append
            (List.append (List.append before [.marker001]) returnCorridor)
            [.marker001]) innerPrefix)
        (.tick :: innerRest)) := by
    simpa [targetInnerProbeConfig, targetPairLeft, returnCorridor,
      innerPrefix, sourceMarkers, targetMarkers, outerRest, innerRest,
      List.replicate_succ, List.append_assoc] using hprobe

  have hsourceReturn' : blockDescription.Reaches
      (configuration 73 (List.append before [.marker001])
        (List.append returnCorridor
          (.marker001 :: List.append innerPrefix (.marker010 :: innerRest))))
      (configuration 73
        (List.append (List.append before [.marker001]) sourceMarkers)
        (.done :: ValidatorCountedRows.cellBlock outer.read ::
          ValidatorCountedRows.cellBlock outer.write ::
          ValidatorCountedRows.directionBlock outer.move ::
          List.append targetMarkers
            (.marker010 :: List.append outerRest
              (.marker001 :: List.append innerPrefix
                (.marker010 :: innerRest))))) := by
    simpa [returnCorridor, List.append_assoc] using hsourceReturn

  have hrun := hprobe'.trans (hpairInner.trans (hreturn.trans
    (houterMarker.trans (hsourceReturn'.trans
      (hdoneReturn.trans (hreadReturn.trans
        (hwriteReturn.trans hmoveReturn)))))))
  have htargetMarkerSucc :
      List.replicate (targetPaired + 1) ValidatorBlockSymbol.marker010 =
        List.append (List.replicate targetPaired .marker010) [.marker010] :=
    List.replicate_succ'
  simpa [targetPairLeft, targetPairRight, sourceMarkers,
    targetMarkers, outerRest, innerRest, innerPrefix, returnCorridor,
    htargetMarkerSucc, List.append_assoc] using hrun

/-- Pair all ticks of two equal target fields. -/
theorem reaches_pair_equal_targets
    (outer inner : TransitionDescription)
    (sourcePaired count targetPaired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 64 (targetPairLeft outer sourcePaired before)
          (targetPairRight outer inner sourcePaired count count targetPaired
            between innerEnd rest))
        (configuration 64 (targetPairLeft outer sourcePaired before)
          (targetPairRight outer inner sourcePaired 0 0
            (targetPaired + count) between innerEnd rest)) := by
  induction count generalizing targetPaired with
  | zero =>
      simpa using ValidatorBlockDescription.reaches_refl blockDescription
        (configuration 64 (targetPairLeft outer sourcePaired before)
          (targetPairRight outer inner sourcePaired 0 0 targetPaired
            between innerEnd rest))
  | succ count ih =>
      have hpair := reaches_pair_target_tick outer inner sourcePaired
        count count targetPaired before between innerEnd rest hbetween
      have htail := ih (targetPaired + 1)
      have hpaired :
          targetPaired + (count + 1) = (targetPaired + 1) + count := by
        lia
      simpa [hpaired] using hpair.trans htail

/-- If the outer target still has a tick when the inner target is exhausted,
the inner terminator probe reaches the explicit conflict state. -/
theorem reaches_outer_longer_target_conflict
    (outer inner : TransitionDescription)
    (sourcePaired outerRemaining targetPaired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (hinnerEnd : innerEnd = .done ∨ innerEnd = .marker011) :
    ReachesConflict
      (configuration 64 (targetPairLeft outer sourcePaired before)
        (targetPairRight outer inner sourcePaired (outerRemaining + 1) 0
          targetPaired between innerEnd rest)) := by
  let sourceMarkers : Word ValidatorBlockSymbol :=
    List.replicate sourcePaired .marker010
  let targetMarkers : Word ValidatorBlockSymbol :=
    List.replicate targetPaired .marker010
  let outerRest : Word ValidatorBlockSymbol :=
    List.append (List.replicate outerRemaining .tick) (.done :: between)
  let innerPrefix : Word ValidatorBlockSymbol :=
    List.append sourceMarkers
      (.done :: ValidatorCountedRows.cellBlock inner.read ::
        ValidatorCountedRows.cellBlock inner.write ::
        ValidatorCountedRows.directionBlock inner.move :: targetMarkers)
  let base := targetPairLeft outer sourcePaired before
  let probeLeft : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append
                    (List.append base targetMarkers) [.marker010]) outerRest)
                [.marker001]) sourceMarkers) [.done])
          [ValidatorCountedRows.cellBlock inner.read])
        [ValidatorCountedRows.cellBlock inner.write])
      (ValidatorCountedRows.directionBlock inner.move :: targetMarkers)

  have hprobeRaw := reaches_target_inner_probe outer inner sourcePaired
    outerRemaining 0 targetPaired before between innerEnd rest hbetween
  have hprobe : blockDescription.Reaches
      (configuration 64 (targetPairLeft outer sourcePaired before)
        (targetPairRight outer inner sourcePaired (outerRemaining + 1) 0
          targetPaired between innerEnd rest))
      (configuration 70 probeLeft (innerEnd :: rest)) := by
    simpa [targetInnerProbeConfig, probeLeft, base, sourceMarkers,
      targetMarkers, outerRest, List.append_assoc] using hprobeRaw
  rcases hinnerEnd with rfl | rfl
  · have hstep := reaches_one_right
      (state := 70) (target := 100)
      (read := .done) (write := .done) (by decide) probeLeft rest
    exact ⟨List.append probeLeft [.done], rest, hprobe.trans hstep⟩
  · have hstep := reaches_one_right
      (state := 70) (target := 100)
      (read := .marker011) (write := .marker011) (by decide) probeLeft rest
    exact ⟨List.append probeLeft [.marker011], rest, hprobe.trans hstep⟩

/-- Configuration after the outer target is exhausted and the already-paired
inner target prefix has been crossed.  The remaining inner target may still
contain ticks; that is precisely the inner-longer conflict branch. -/
def targetEndProbeConfig
    (outer inner : TransitionDescription)
    (sourcePaired targetPaired innerRemaining : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  configuration 82
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append
                    (targetPairLeft outer sourcePaired before)
                    (List.replicate targetPaired .marker010)) [.done])
                between) [.marker001])
            (List.replicate sourcePaired .marker010)) [.done])
        [ValidatorCountedRows.cellBlock inner.read,
          ValidatorCountedRows.cellBlock inner.write])
      (ValidatorCountedRows.directionBlock inner.move ::
        List.replicate targetPaired .marker010))
    (List.append (List.replicate innerRemaining .tick) (innerEnd :: rest))

/-- Configuration immediately before the equal-target terminator test. -/
def targetEndCheckConfig
    (outer inner : TransitionDescription)
    (sourcePaired targetPaired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  targetEndProbeConfig outer inner sourcePaired targetPaired 0
    before between innerEnd rest

/-- Exhausting the outer target reaches the remaining-inner-target probe. -/
theorem reaches_target_end_probe
    (outer inner : TransitionDescription)
    (sourcePaired targetPaired innerRemaining : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 64 (targetPairLeft outer sourcePaired before)
          (targetPairRight outer inner sourcePaired 0 innerRemaining targetPaired
            between innerEnd rest))
        (targetEndProbeConfig outer inner sourcePaired targetPaired innerRemaining
          before between innerEnd rest) := by
  let sourceMarkers : Word ValidatorBlockSymbol :=
    List.replicate sourcePaired .marker010
  let targetMarkers : Word ValidatorBlockSymbol :=
    List.replicate targetPaired .marker010
  let innerTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate innerRemaining .tick) (innerEnd :: rest)
  let base := targetPairLeft outer sourcePaired before
  have houterMarkers := reaches_scan_right_markers
    (state := 64) (by decide) targetPaired base
    (.done :: List.append between
      (.marker001 :: List.append sourceMarkers
        (.done :: ValidatorCountedRows.cellBlock inner.read ::
          ValidatorCountedRows.cellBlock inner.write ::
          ValidatorCountedRows.directionBlock inner.move ::
          List.append targetMarkers innerTail)))
  have houterDone := reaches_one_right
    (state := 64) (target := 77)
    (read := .done) (write := .done) (by decide)
    (List.append base targetMarkers)
    (List.append between
      (.marker001 :: List.append sourceMarkers
        (.done :: ValidatorCountedRows.cellBlock inner.read ::
          ValidatorCountedRows.cellBlock inner.write ::
          ValidatorCountedRows.directionBlock inner.move ::
          List.append targetMarkers innerTail)))
  have hbetweenRun := reaches_scan_right_list between
    (fun symbol hsymbol =>
      lookup_state77_corridor symbol (hbetween symbol hsymbol))
    (List.append (List.append base targetMarkers) [.done])
    (.marker001 :: List.append sourceMarkers
      (.done :: ValidatorCountedRows.cellBlock inner.read ::
        ValidatorCountedRows.cellBlock inner.write ::
        ValidatorCountedRows.directionBlock inner.move ::
        List.append targetMarkers innerTail))
  have hmarker := reaches_one_right
    (state := 77) (target := 78)
    (read := .marker001) (write := .marker001) (by decide)
    (List.append
      (List.append (List.append base targetMarkers) [.done]) between)
    (List.append sourceMarkers
      (.done :: ValidatorCountedRows.cellBlock inner.read ::
        ValidatorCountedRows.cellBlock inner.write ::
        ValidatorCountedRows.directionBlock inner.move ::
        List.append targetMarkers innerTail))
  have hsource := reaches_scan_right_markers
    (state := 78) (by decide) sourcePaired
    (List.append
      (List.append
        (List.append (List.append base targetMarkers) [.done]) between)
      [.marker001])
    (.done :: ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append targetMarkers innerTail)
  have hdone := reaches_one_right
    (state := 78) (target := 79)
    (read := .done) (write := .done) (by decide)
    (List.append
      (List.append
        (List.append
          (List.append (List.append base targetMarkers) [.done]) between)
        [.marker001]) sourceMarkers)
    (ValidatorCountedRows.cellBlock inner.read ::
      ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append targetMarkers innerTail)
  have hread := reaches_one_right
    (state := 79) (target := 80)
    (read := ValidatorCountedRows.cellBlock inner.read)
    (write := ValidatorCountedRows.cellBlock inner.read)
    (by cases inner.read with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append (List.append base targetMarkers) [.done]) between)
          [.marker001]) sourceMarkers) [.done])
    (ValidatorCountedRows.cellBlock inner.write ::
      ValidatorCountedRows.directionBlock inner.move ::
      List.append targetMarkers innerTail)
  have hwrite := reaches_one_right
    (state := 80) (target := 81)
    (read := ValidatorCountedRows.cellBlock inner.write)
    (write := ValidatorCountedRows.cellBlock inner.write)
    (by cases inner.write with
      | none => decide
      | some bit => cases bit <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append (List.append base targetMarkers) [.done]) between)
            [.marker001]) sourceMarkers) [.done])
      [ValidatorCountedRows.cellBlock inner.read])
    (ValidatorCountedRows.directionBlock inner.move ::
      List.append targetMarkers innerTail)
  have hmove := reaches_one_right
    (state := 81) (target := 82)
    (read := ValidatorCountedRows.directionBlock inner.move)
    (write := ValidatorCountedRows.directionBlock inner.move)
    (by cases inner.move <;> decide)
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append (List.append base targetMarkers) [.done]) between)
              [.marker001]) sourceMarkers) [.done])
        [ValidatorCountedRows.cellBlock inner.read])
      [ValidatorCountedRows.cellBlock inner.write])
    (List.append targetMarkers innerTail)
  have htarget := reaches_scan_right_markers
    (state := 82) (by decide) targetPaired
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append (List.append base targetMarkers) [.done])
                  between) [.marker001]) sourceMarkers) [.done])
          [ValidatorCountedRows.cellBlock inner.read])
        [ValidatorCountedRows.cellBlock inner.write])
      [ValidatorCountedRows.directionBlock inner.move])
    innerTail
  have hrun := houterMarkers.trans (houterDone.trans
    (hbetweenRun.trans (hmarker.trans (hsource.trans
      (hdone.trans (hread.trans (hwrite.trans (hmove.trans htarget))))))))
  simpa [targetPairLeft, targetPairRight, targetEndProbeConfig,
    base, sourceMarkers, targetMarkers, innerTail, List.append_assoc] using hrun

/-- Exhausted equal target fields reach the inner terminator test. -/
theorem reaches_target_end_check
    (outer inner : TransitionDescription)
    (sourcePaired targetPaired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    blockDescription.Reaches
        (configuration 64 (targetPairLeft outer sourcePaired before)
          (targetPairRight outer inner sourcePaired 0 0 targetPaired
            between innerEnd rest))
        (targetEndCheckConfig outer inner sourcePaired targetPaired
          before between innerEnd rest) := by
  simpa [targetEndCheckConfig, targetEndProbeConfig] using
    reaches_target_end_probe outer inner sourcePaired targetPaired 0
      before between innerEnd rest hbetween

/-- Once the outer target is exhausted, any remaining inner target tick is a
determinism conflict. -/
theorem reaches_inner_longer_target_conflict
    (outer inner : TransitionDescription)
    (sourcePaired targetPaired extra : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols) :
    ReachesConflict
      (configuration 64 (targetPairLeft outer sourcePaired before)
        (targetPairRight outer inner sourcePaired 0 (extra + 1) targetPaired
          between innerEnd rest)) := by
  have hprobe := reaches_target_end_probe outer inner sourcePaired targetPaired
    (extra + 1) before between innerEnd rest hbetween
  let probeLeft : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (List.append
          (List.append
            (List.append
              (List.append
                (List.append
                  (List.append
                    (targetPairLeft outer sourcePaired before)
                    (List.replicate targetPaired .marker010)) [.done])
                between) [.marker001])
            (List.replicate sourcePaired .marker010)) [.done])
        [ValidatorCountedRows.cellBlock inner.read,
          ValidatorCountedRows.cellBlock inner.write])
      (ValidatorCountedRows.directionBlock inner.move ::
        List.replicate targetPaired .marker010)
  let innerTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate extra .tick) (innerEnd :: rest)
  have hstep := reaches_one_right
    (state := 82) (target := 100)
    (read := .tick) (write := .tick) (by decide)
    probeLeft innerTail
  apply ReachesConflict.of_reaches hprobe
  refine ⟨List.append probeLeft [.tick], innerTail, ?_⟩
  simpa [targetEndProbeConfig, probeLeft, innerTail,
    List.replicate_succ, configuration,
    ValidatorBlockDescription.blockConfiguration, List.append_assoc] using hstep

/-- The complete unary target comparison either reaches the equal-target end
check or the explicit conflict state. -/
theorem reaches_target_comparison
    (outer inner : TransitionDescription)
    (sourcePaired outerRemaining innerRemaining targetPaired : Nat)
    (before between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol)
    (hbetween : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from between) ->
        symbol ∈ ValidatorCountedRows.corridorSymbols)
    (hinnerEnd : innerEnd = .done ∨ innerEnd = .marker011) :
    (outerRemaining = innerRemaining ∧
      blockDescription.Reaches
        (configuration 64 (targetPairLeft outer sourcePaired before)
          (targetPairRight outer inner sourcePaired outerRemaining
            innerRemaining targetPaired between innerEnd rest))
        (targetEndCheckConfig outer inner sourcePaired
          (targetPaired + outerRemaining) before between innerEnd rest)) ∨
    (outerRemaining ≠ innerRemaining ∧
      ReachesConflict
        (configuration 64 (targetPairLeft outer sourcePaired before)
          (targetPairRight outer inner sourcePaired outerRemaining
            innerRemaining targetPaired between innerEnd rest))) := by
  induction outerRemaining generalizing innerRemaining targetPaired with
  | zero =>
      cases innerRemaining with
      | zero =>
          exact Or.inl ⟨rfl, by
            simpa using reaches_target_end_check outer inner sourcePaired
              targetPaired before between innerEnd rest hbetween⟩
      | succ extra =>
          exact Or.inr ⟨by simp, reaches_inner_longer_target_conflict
            outer inner sourcePaired targetPaired extra before between
              innerEnd rest hbetween⟩
  | succ outerRemaining ih =>
      cases innerRemaining with
      | zero =>
          exact Or.inr ⟨by simp, reaches_outer_longer_target_conflict
            outer inner sourcePaired outerRemaining targetPaired before between
              innerEnd rest hbetween hinnerEnd⟩
      | succ innerRemaining =>
          have hpair := reaches_pair_target_tick outer inner sourcePaired
            outerRemaining innerRemaining targetPaired before between
              innerEnd rest hbetween
          rcases ih (innerRemaining := innerRemaining)
              (targetPaired := targetPaired + 1) with hequal | hconflict
          · apply Or.inl
            constructor
            · exact congrArg Nat.succ hequal.1
            · have hrun := hpair.trans hequal.2
              have hpaired :
                  targetPaired + (outerRemaining + 1) =
                    (targetPaired + 1) + outerRemaining := by
                lia
              simpa [hpaired] using hrun
          · apply Or.inr
            constructor
            · intro heq
              exact hconflict.1 (Nat.succ.inj heq)
            · exact ReachesConflict.of_reaches hpair hconflict.2

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
