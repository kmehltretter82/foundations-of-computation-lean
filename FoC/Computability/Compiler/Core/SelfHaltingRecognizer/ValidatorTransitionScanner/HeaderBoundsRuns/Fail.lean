import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.HeaderBoundsRuns.Base

set_option doc.verso true

/-! # Exact-code validator: header rejection runs -/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorHeaderBounds

open Languages
open MachineDescription
/-!
## Logical failure runs
-/

private theorem reaches_zero_stateCount_stuck
    (start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    blockDescription.Reaches
      (logicalStartConfig 0 start halt transitionCount tokens)
      (configuration 4 []
        (.header :: .done ::
          List.append (List.replicate start .tick)
            (.done ::
              List.append (List.replicate halt .tick)
                (.done ::
                  List.append (List.replicate transitionCount .tick)
                    (.done :: validatorCanonicalBlocks tokens))))) := by
  let code := validatorCanonicalBlocks tokens
  let beforeHaltDone : Word ValidatorBlockSymbol :=
    .header ::
      List.append (natBlocks 0)
        (List.append (natBlocks start) (List.replicate halt .tick))
  let afterHaltDone : Word ValidatorBlockSymbol :=
    List.append (List.replicate transitionCount .tick) (.done :: code)
  let beforeStartDone : Word ValidatorBlockSymbol :=
    .header ::
      List.append (natBlocks 0) (List.replicate start .tick)
  let afterStartDone : Word ValidatorBlockSymbol :=
    List.append (List.replicate halt .tick) (.done :: afterHaltDone)
  let beforeStateDone : Word ValidatorBlockSymbol := [.header]
  let afterStateDone : Word ValidatorBlockSymbol :=
    List.append (List.replicate start .tick) (.done :: afterStartDone)

  have htransitionCount := reaches_cross_done_scan_left
    (entry := 0) (scan := 1) (by decide) (by decide)
    transitionCount beforeHaltDone code .done
  have hhalt := reaches_cross_done_scan_left
    (entry := 1) (scan := 2) (by decide) (by decide)
    halt beforeStartDone afterHaltDone .done
  have hstart := reaches_cross_done_scan_left
    (entry := 2) (scan := 3) (by decide) (by decide)
    start beforeStateDone afterStartDone .done
  have htransitionCount' :
      blockDescription.Reaches
        (logicalStartConfig 0 start halt transitionCount tokens)
        (configuration 1 beforeHaltDone (.done :: afterHaltDone)) := by
    simpa [logicalStartConfig, startLeftBlocks, natBlocks,
      blockDescription, beforeHaltDone, afterHaltDone, code, configuration,
      List.append_assoc] using htransitionCount
  have hhalt' :
      blockDescription.Reaches
        (configuration 1 beforeHaltDone (.done :: afterHaltDone))
        (configuration 2 beforeStartDone (.done :: afterStartDone)) := by
    simpa [beforeHaltDone, afterHaltDone, beforeStartDone,
      afterStartDone, natBlocks, configuration, List.append_assoc] using hhalt
  have hstart' :
      blockDescription.Reaches
        (configuration 2 beforeStartDone (.done :: afterStartDone))
        (configuration 3 beforeStateDone (.done :: afterStateDone)) := by
    simpa [beforeStartDone, afterStartDone, beforeStateDone,
      afterStateDone, natBlocks, configuration, List.append_assoc] using hstart
  have hboundary := reaches_one_left
    (state := 3) (target := 4) (read := .done) (write := .done)
    (by decide) [] afterStateDone .header
  have hrun := htransitionCount'.trans
    (hhalt'.trans (hstart'.trans hboundary))
  simpa [beforeStateDone, afterStateDone, afterStartDone, afterHaltDone,
    code, configuration, List.append_assoc] using hrun

private theorem reaches_pair_start_until_state_exhausted
    (extra count marked : Nat)
    (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
      (configuration 6
        (comparisonStateLeft count marked)
        (List.append (markedTicks (extra + count) marked)
          (.done :: after)))
      (configuration 6
        (comparisonStateLeft 0 (marked + count))
        (List.append (markedTicks extra (marked + count))
          (.done :: after))) := by
  induction count generalizing marked with
  | zero =>
      simpa [configuration] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration 6
            (comparisonStateLeft 0 marked)
            (List.append (markedTicks extra marked) (.done :: after)))
  | succ count ih =>
      have hpair := reaches_pair_start_tick
        count (extra + count) marked after
      have htail := ih (marked + 1)
      have hextra : extra + (count + 1) = (extra + count) + 1 := by
        lia
      have hmarked : marked + (count + 1) = (marked + 1) + count := by
        lia
      simpa [hextra, hmarked] using hpair.trans htail

private def startEqualStuckRight
    (count : Nat) (after : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate count .marker010)
    (.done ::
      List.append (List.replicate count .marker010) (.done :: after))

private theorem reaches_start_equal_stuck
    (count : Nat) (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
      (configuration 6
        (List.append [.header] (natBlocks count))
        (List.append (List.replicate count .tick) (.done :: after)))
      (configuration 12 [] (.header :: startEqualStuckRight count after)) := by
  let stateMarkers : Word ValidatorBlockSymbol :=
    List.replicate count .marker010
  let stateBeforeDone : Word ValidatorBlockSymbol :=
    .header :: stateMarkers
  let stateLeft : Word ValidatorBlockSymbol :=
    List.append stateBeforeDone [.done]
  have hpairs := reaches_pair_start_until_state_exhausted
    0 count 0 after
  have hscan := reaches_scan_right_prefix
    (state := 6) (symbol := .marker010) (boundary := .done)
    (by decide) count stateLeft after
  have hstartBack := reaches_cross_read_scan_left
    (entry := 6) (scan := 7)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .done)
    (by decide) (by decide) count stateBeforeDone after
  have hstateBack := reaches_cross_read_scan_left
    (entry := 7) (scan := 12)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .header)
    (by decide) (by decide) count []
    (List.append stateMarkers (.done :: after))
  have hpair' :
      blockDescription.Reaches
        (configuration 6
          (List.append [.header] (natBlocks count))
          (List.append (List.replicate count .tick) (.done :: after)))
        (configuration 6 stateLeft
          (List.append stateMarkers (.done :: after))) := by
    simpa [stateLeft, stateBeforeDone, stateMarkers, comparisonStateLeft,
      markedTicks, natBlocks, configuration, List.append_assoc] using hpairs
  have hscan' :
      blockDescription.Reaches
        (configuration 6 stateLeft
          (List.append stateMarkers (.done :: after)))
        (configuration 6 (List.append stateLeft stateMarkers)
          (.done :: after)) := by
    simpa [stateMarkers] using hscan
  have hstartBack' :
      blockDescription.Reaches
        (configuration 6 (List.append stateLeft stateMarkers)
          (.done :: after))
        (configuration 7 stateBeforeDone
          (.done :: List.append stateMarkers (.done :: after))) := by
    simpa [stateLeft, stateMarkers, configuration,
      List.append_assoc] using hstartBack
  have hrun := hpair'.trans
    (hscan'.trans (hstartBack'.trans hstateBack))
  simpa [stateBeforeDone, stateMarkers, startEqualStuckRight,
    configuration, List.append_assoc] using hrun

private def startGreaterStuckRight
    (extra count : Nat) (after : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate count .marker010)
    (.done ::
      List.append (List.replicate extra .tick)
        (.marker010 ::
          List.append (List.replicate count .marker010) (.done :: after)))

private theorem reaches_start_greater_stuck
    (extra count : Nat) (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
      (configuration 6
        (List.append [.header] (natBlocks count))
        (List.append (List.replicate (extra + 1 + count) .tick)
          (.done :: after)))
      (configuration 9 []
        (.header :: startGreaterStuckRight extra count after)) := by
  let stateMarkers : Word ValidatorBlockSymbol :=
    List.replicate count .marker010
  let stateBeforeDone : Word ValidatorBlockSymbol :=
    .header :: stateMarkers
  let stateLeft : Word ValidatorBlockSymbol :=
    List.append stateBeforeDone [.done]
  let afterTicks : Word ValidatorBlockSymbol :=
    List.append stateMarkers (.done :: after)
  have hpairs := reaches_pair_start_until_state_exhausted
    (extra + 1) count 0 after
  have hticks := reaches_scan_right_tail
    (state := 6) (symbol := .tick) (by decide)
    (extra + 1) stateLeft afterTicks (by
      intro hempty
      have hlength := congrArg List.length hempty
      simp [afterTicks] at hlength)
  have hmarkers := reaches_scan_right_prefix
    (state := 6) (symbol := .marker010) (boundary := .done)
    (by decide) count
    (List.append stateLeft (List.replicate (extra + 1) .tick)) after
  have hstartMarkersBack := reaches_cross_read_scan_left
    (entry := 6) (scan := 7)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .tick)
    (by decide) (by decide) count
    (List.append stateLeft (List.replicate extra .tick)) after
  have hextraBack := reaches_cross_read_scan_left
    (entry := 7) (scan := 8)
    (entryRead := .tick) (entryWrite := .marker010)
    (scanSymbol := .tick) (boundary := .done)
    (by decide) (by decide) extra stateBeforeDone
    (List.append stateMarkers (.done :: after))
  have hstateBack := reaches_cross_read_scan_left
    (entry := 8) (scan := 9)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .header)
    (by decide) (by decide) count []
    (List.append (List.replicate extra .tick)
      (.marker010 :: List.append stateMarkers (.done :: after)))
  have hpair' :
      blockDescription.Reaches
        (configuration 6
          (List.append [.header] (natBlocks count))
          (List.append (List.replicate (extra + 1 + count) .tick)
            (.done :: after)))
        (configuration 6 stateLeft
          (List.append (List.replicate (extra + 1) .tick) afterTicks)) := by
    simpa [stateLeft, stateBeforeDone, stateMarkers, afterTicks,
      comparisonStateLeft, markedTicks, natBlocks, configuration,
      replicate_add_eq_append, List.append_assoc] using hpairs
  have hstartMarkersBack' :
      blockDescription.Reaches
        (configuration 6
          (List.append
            (List.append stateLeft
              (List.replicate (extra + 1) .tick)) stateMarkers)
          (.done :: after))
        (configuration 7
          (List.append stateLeft (List.replicate extra .tick))
          (.tick :: List.append stateMarkers (.done :: after))) := by
    simpa [stateMarkers, List.replicate_succ', List.append_assoc] using
      hstartMarkersBack
  have hextraBack' :
      blockDescription.Reaches
        (configuration 7
          (List.append stateLeft (List.replicate extra .tick))
          (.tick :: List.append stateMarkers (.done :: after)))
        (configuration 8 stateBeforeDone
          (.done ::
            List.append (List.replicate extra .tick)
              (.marker010 :: List.append stateMarkers (.done :: after)))) := by
    simpa [stateLeft] using hextraBack
  have hstateBack' :
      blockDescription.Reaches
        (configuration 8 stateBeforeDone
          (.done ::
            List.append (List.replicate extra .tick)
              (.marker010 :: List.append stateMarkers (.done :: after))))
        (configuration 9 []
          (.header :: startGreaterStuckRight extra count after)) := by
    simpa [stateBeforeDone, stateMarkers, startGreaterStuckRight,
      List.append_assoc] using hstateBack
  have hrun := hpair'.trans
    (hticks.trans (hmarkers.trans
      (hstartMarkersBack'.trans (hextraBack'.trans hstateBack'))))
  simpa [stateLeft, stateBeforeDone, stateMarkers, afterTicks,
    startGreaterStuckRight, configuration, List.replicate_succ',
    List.append_assoc] using hrun

private theorem reaches_pair_halt_until_state_exhausted
    (extra count marked start : Nat)
    (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
      (configuration 16
        (comparisonHaltLeft count marked start)
        (List.append (markedTicks (extra + count) marked)
          (.done :: after)))
      (configuration 16
        (comparisonHaltLeft 0 (marked + count) start)
        (List.append (markedTicks extra (marked + count))
          (.done :: after))) := by
  induction count generalizing marked with
  | zero =>
      simpa [configuration] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration 16
            (comparisonHaltLeft 0 marked start)
            (List.append (markedTicks extra marked) (.done :: after)))
  | succ count ih =>
      have hpair := reaches_pair_halt_tick
        count (extra + count) marked start after
      have htail := ih (marked + 1)
      have hextra : extra + (count + 1) = (extra + count) + 1 := by
        lia
      have hmarked : marked + (count + 1) = (marked + 1) + count := by
        lia
      simpa [hextra, hmarked] using hpair.trans htail

private def haltEqualStuckRight
    (count start : Nat) (after : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate count .marker010)
    (.done ::
      List.append (List.replicate start .tick)
        (.done ::
          List.append (List.replicate count .marker010) (.done :: after)))

private theorem reaches_halt_equal_stuck
    (count start : Nat) (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
      (configuration 16 (restoredStartLeft count start)
        (List.append (List.replicate count .tick) (.done :: after)))
      (configuration 24 []
        (.header :: haltEqualStuckRight count start after)) := by
  let stateMarkers : Word ValidatorBlockSymbol :=
    List.replicate count .marker010
  let stateBeforeDone : Word ValidatorBlockSymbol :=
    .header :: stateMarkers
  let stateDoneLeft : Word ValidatorBlockSymbol :=
    List.append stateBeforeDone [.done]
  let startBeforeDone : Word ValidatorBlockSymbol :=
    List.append stateDoneLeft (List.replicate start .tick)
  let startLeft : Word ValidatorBlockSymbol :=
    List.append startBeforeDone [.done]
  have hpairs := reaches_pair_halt_until_state_exhausted
    0 count 0 start after
  have hscan := reaches_scan_right_prefix
    (state := 16) (symbol := .marker010) (boundary := .done)
    (by decide) count startLeft after
  have hhaltBack := reaches_cross_read_scan_left
    (entry := 16) (scan := 17)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .done)
    (by decide) (by decide) count startBeforeDone after
  have hstartBack := reaches_cross_read_scan_left
    (entry := 17) (scan := 22)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .tick) (boundary := .done)
    (by decide) (by decide) start stateBeforeDone
    (List.append stateMarkers (.done :: after))
  have hstateBack := reaches_cross_read_scan_left
    (entry := 22) (scan := 24)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .header)
    (by decide) (by decide) count []
    (List.append (List.replicate start .tick)
      (.done :: List.append stateMarkers (.done :: after)))
  have hpair' :
      blockDescription.Reaches
        (configuration 16 (restoredStartLeft count start)
          (List.append (List.replicate count .tick) (.done :: after)))
        (configuration 16 startLeft
          (List.append stateMarkers (.done :: after))) := by
    simpa [startLeft, startBeforeDone, stateDoneLeft, stateBeforeDone,
      stateMarkers, restoredStartLeft, comparisonHaltLeft, markedTicks,
      natBlocks, configuration, List.append_assoc] using hpairs
  have hscan' :
      blockDescription.Reaches
        (configuration 16 startLeft
          (List.append stateMarkers (.done :: after)))
        (configuration 16 (List.append startLeft stateMarkers)
          (.done :: after)) := by
    simpa [stateMarkers] using hscan
  have hhaltBack' :
      blockDescription.Reaches
        (configuration 16 (List.append startLeft stateMarkers)
          (.done :: after))
        (configuration 17 startBeforeDone
          (.done :: List.append stateMarkers (.done :: after))) := by
    simpa [startLeft, stateMarkers, configuration,
      List.append_assoc] using hhaltBack
  have hstartBack' :
      blockDescription.Reaches
        (configuration 17 startBeforeDone
          (.done :: List.append stateMarkers (.done :: after)))
        (configuration 22 stateBeforeDone
          (.done ::
            List.append (List.replicate start .tick)
              (.done :: List.append stateMarkers (.done :: after)))) := by
    simpa [startBeforeDone, stateDoneLeft, List.append_assoc] using hstartBack
  have hstateBack' :
      blockDescription.Reaches
        (configuration 22 stateBeforeDone
          (.done ::
            List.append (List.replicate start .tick)
              (.done :: List.append stateMarkers (.done :: after))))
        (configuration 24 []
          (.header :: haltEqualStuckRight count start after)) := by
    simpa [stateBeforeDone, stateMarkers, haltEqualStuckRight,
      List.append_assoc] using hstateBack
  exact hpair'.trans (hscan'.trans
    (hhaltBack'.trans (hstartBack'.trans hstateBack')))

private def haltGreaterAfterState
    (extra count start : Nat) (after : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate start .tick)
    (.done ::
      List.append (List.replicate extra .tick)
        (.marker010 ::
          List.append (List.replicate count .marker010) (.done :: after)))

private def haltGreaterStuckRight
    (extra count start : Nat) (after : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate count .marker010)
    (.done :: haltGreaterAfterState extra count start after)

private theorem reaches_halt_greater_stuck
    (extra count start : Nat) (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
      (configuration 16 (restoredStartLeft count start)
        (List.append (List.replicate (extra + 1 + count) .tick)
          (.done :: after)))
      (configuration 20 []
        (.header :: haltGreaterStuckRight extra count start after)) := by
  let stateMarkers : Word ValidatorBlockSymbol :=
    List.replicate count .marker010
  let stateBeforeDone : Word ValidatorBlockSymbol :=
    .header :: stateMarkers
  let stateDoneLeft : Word ValidatorBlockSymbol :=
    List.append stateBeforeDone [.done]
  let startBeforeDone : Word ValidatorBlockSymbol :=
    List.append stateDoneLeft (List.replicate start .tick)
  let startLeft : Word ValidatorBlockSymbol :=
    List.append startBeforeDone [.done]
  let afterTicks : Word ValidatorBlockSymbol :=
    List.append stateMarkers (.done :: after)
  have hpairs := reaches_pair_halt_until_state_exhausted
    (extra + 1) count 0 start after
  have hticks := reaches_scan_right_tail
    (state := 16) (symbol := .tick) (by decide)
    (extra + 1) startLeft afterTicks (by
      intro hempty
      have hlength := congrArg List.length hempty
      simp [afterTicks] at hlength)
  have hmarkers := reaches_scan_right_prefix
    (state := 16) (symbol := .marker010) (boundary := .done)
    (by decide) count
    (List.append startLeft (List.replicate (extra + 1) .tick)) after
  have hhaltMarkersBack := reaches_cross_read_scan_left
    (entry := 16) (scan := 17)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .tick)
    (by decide) (by decide) count
    (List.append startLeft (List.replicate extra .tick)) after
  have hextraBack := reaches_cross_read_scan_left
    (entry := 17) (scan := 18)
    (entryRead := .tick) (entryWrite := .marker010)
    (scanSymbol := .tick) (boundary := .done)
    (by decide) (by decide) extra startBeforeDone
    (List.append stateMarkers (.done :: after))
  have hstartBack := reaches_cross_read_scan_left
    (entry := 18) (scan := 19)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .tick) (boundary := .done)
    (by decide) (by decide) start stateBeforeDone
    (List.append (List.replicate extra .tick)
      (.marker010 :: List.append stateMarkers (.done :: after)))
  have hstateBack := reaches_cross_read_scan_left
    (entry := 19) (scan := 20)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .header)
    (by decide) (by decide) count []
    (List.append (List.replicate start .tick)
      (.done ::
        List.append (List.replicate extra .tick)
          (.marker010 :: List.append stateMarkers (.done :: after))))
  have hpair' :
      blockDescription.Reaches
        (configuration 16 (restoredStartLeft count start)
          (List.append (List.replicate (extra + 1 + count) .tick)
            (.done :: after)))
        (configuration 16 startLeft
          (List.append (List.replicate (extra + 1) .tick) afterTicks)) := by
    simpa [startLeft, startBeforeDone, stateDoneLeft, stateBeforeDone,
      stateMarkers, afterTicks, restoredStartLeft, comparisonHaltLeft,
      markedTicks, natBlocks, configuration, replicate_add_eq_append,
      List.append_assoc] using hpairs
  have hhaltMarkersBack' :
      blockDescription.Reaches
        (configuration 16
          (List.append
            (List.append startLeft
              (List.replicate (extra + 1) .tick)) stateMarkers)
          (.done :: after))
        (configuration 17
          (List.append startLeft (List.replicate extra .tick))
          (.tick :: List.append stateMarkers (.done :: after))) := by
    simpa [stateMarkers, List.replicate_succ', List.append_assoc] using
      hhaltMarkersBack
  have hextraBack' :
      blockDescription.Reaches
        (configuration 17
          (List.append startLeft (List.replicate extra .tick))
          (.tick :: List.append stateMarkers (.done :: after)))
        (configuration 18 startBeforeDone
          (.done ::
            List.append (List.replicate extra .tick)
              (.marker010 :: List.append stateMarkers (.done :: after)))) := by
    simpa [startLeft] using hextraBack
  have hstartBack' :
      blockDescription.Reaches
        (configuration 18 startBeforeDone
          (.done ::
            List.append (List.replicate extra .tick)
              (.marker010 :: List.append stateMarkers (.done :: after))))
        (configuration 19 stateBeforeDone
          (.done :: haltGreaterAfterState extra count start after)) := by
    simpa [startBeforeDone, stateDoneLeft, stateMarkers,
      haltGreaterAfterState, List.append_assoc] using hstartBack
  have hstateBack' :
      blockDescription.Reaches
        (configuration 19 stateBeforeDone
          (.done :: haltGreaterAfterState extra count start after))
        (configuration 20 []
          (.header :: haltGreaterStuckRight extra count start after)) := by
    simpa [stateBeforeDone, stateMarkers, haltGreaterStuckRight,
      haltGreaterAfterState, List.append_assoc] using hstateBack
  have hrun0 := hpair'.trans hticks
  have hrun1 := hrun0.trans hmarkers
  have hrun2 := hrun1.trans hhaltMarkersBack'
  have hrun3 := hrun2.trans hextraBack'
  have hrun4 := hrun3.trans hstartBack'
  exact hrun4.trans hstateBack'

set_option maxRecDepth 100000 in
/-- If one of the three header bounds fails, the logical block machine reaches
a concrete generated Boolean leaf with no outgoing transition. -/
def leafStuckWitness_of_bounds_false
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (hfalse :
      validatorHeaderBoundsBool stateCount start halt = false) :
    ValidatorBlockLeafStuckWitness blockDescription Description
      (logicalStartConfig
        stateCount start halt transitionCount tokens) := by
  by_cases hpositive : 0 < stateCount
  · by_cases hstart : start < stateCount
    · by_cases hhalt : halt < stateCount
      · simp [validatorHeaderBoundsBool, hpositive, hstart, hhalt] at hfalse
      · let transitionTail : Word ValidatorBlockSymbol :=
          List.append (List.replicate transitionCount .tick)
            (.done :: validatorCanonicalBlocks tokens)
        let haltTail : Word ValidatorBlockSymbol :=
          List.append (List.replicate halt .tick) (.done :: transitionTail)
        have hlocate := reaches_start_comparison_entry
          stateCount start halt transitionCount tokens hpositive
        have hstartRun := reaches_start_bound_from_entry
          stateCount start haltTail hstart
        have hentry :
            blockDescription.Reaches
              (logicalStartConfig
                stateCount start halt transitionCount tokens)
              (configuration 16 (restoredStartLeft stateCount start)
                haltTail) := by
          have hlocate' :
              blockDescription.Reaches
                (logicalStartConfig
                  stateCount start halt transitionCount tokens)
                (configuration 6
                  (List.append [.header] (natBlocks stateCount))
                  (List.append (List.replicate start .tick)
                    (.done :: haltTail))) := by
            simpa [haltTail, transitionTail, configuration,
              List.append_assoc] using hlocate
          exact hlocate'.trans hstartRun
        have hle : stateCount ≤ halt := by lia
        by_cases heq : halt = stateCount
        · subst halt
          have hstuck := reaches_halt_equal_stuck
            stateCount start transitionTail
          have hrun := hentry.trans hstuck
          exact
            { logical := 24
              left := []
              right := haltEqualStuckRight
                stateCount start transitionTail
              read := .header
              reaches := by simpa [configuration] using hrun
              logical_lt := by decide
              logical_ne_halt := by decide
              leaf_none := by decide
              leaf_ne_halt := by decide }
        · let extra := halt - (stateCount + 1)
          have hdecomp : halt = extra + 1 + stateCount := by
            dsimp [extra]
            lia
          have hstuck := reaches_halt_greater_stuck
            extra stateCount start transitionTail
          have hstuck' :
              blockDescription.Reaches
                (configuration 16 (restoredStartLeft stateCount start)
                  haltTail)
                (configuration 20 []
                  (.header :: haltGreaterStuckRight
                    extra stateCount start transitionTail)) := by
            simpa [haltTail, hdecomp] using hstuck
          have hrun := hentry.trans hstuck'
          exact
            { logical := 20
              left := []
              right := haltGreaterStuckRight
                extra stateCount start transitionTail
              read := .header
              reaches := by simpa [configuration] using hrun
              logical_lt := by decide
              logical_ne_halt := by decide
              leaf_none := by decide
              leaf_ne_halt := by decide }
    · let after : Word ValidatorBlockSymbol :=
        List.append (List.replicate halt .tick)
          (.done ::
            List.append (List.replicate transitionCount .tick)
              (.done :: validatorCanonicalBlocks tokens))
      have hlocate := reaches_start_comparison_entry
        stateCount start halt transitionCount tokens hpositive
      have hlocate' :
          blockDescription.Reaches
            (logicalStartConfig
              stateCount start halt transitionCount tokens)
            (configuration 6
              (List.append [.header] (natBlocks stateCount))
              (List.append (List.replicate start .tick) (.done :: after))) := by
        simpa [after, configuration, List.append_assoc] using hlocate
      have hle : stateCount ≤ start := by lia
      by_cases heq : start = stateCount
      · subst start
        have hstuck := reaches_start_equal_stuck stateCount after
        have hrun := hlocate'.trans hstuck
        exact
          { logical := 12
            left := []
            right := startEqualStuckRight stateCount after
            read := .header
            reaches := by simpa [configuration] using hrun
            logical_lt := by decide
            logical_ne_halt := by decide
            leaf_none := by decide
            leaf_ne_halt := by decide }
      · let extra := start - (stateCount + 1)
        have hdecomp : start = extra + 1 + stateCount := by
          dsimp [extra]
          lia
        have hstuck := reaches_start_greater_stuck
          extra stateCount after
        have hstuck' :
            blockDescription.Reaches
              (configuration 6
                (List.append [.header] (natBlocks stateCount))
                (List.append (List.replicate start .tick) (.done :: after)))
              (configuration 9 []
                (.header :: startGreaterStuckRight
                  extra stateCount after)) := by
          simpa [hdecomp] using hstuck
        have hrun := hlocate'.trans hstuck'
        exact
          { logical := 9
            left := []
            right := startGreaterStuckRight extra stateCount after
            read := .header
            reaches := by simpa [configuration] using hrun
            logical_lt := by decide
            logical_ne_halt := by decide
            leaf_none := by decide
            leaf_ne_halt := by decide }
  · have hzero : stateCount = 0 := by lia
    subst stateCount
    let right : Word ValidatorBlockSymbol :=
      .done ::
        List.append (List.replicate start .tick)
          (.done ::
            List.append (List.replicate halt .tick)
              (.done ::
                List.append (List.replicate transitionCount .tick)
                  (.done :: validatorCanonicalBlocks tokens)))
    have hrun := reaches_zero_stateCount_stuck
      start halt transitionCount tokens
    exact
      { logical := 4
        left := []
        right := right
        read := .header
        reaches := by simpa [configuration, right] using hrun
        logical_lt := by decide
        logical_ne_halt := by decide
        leaf_none := by decide
        leaf_ne_halt := by decide }

/-!
## Complete logical execution
-/

/--
The aligned 31-state table validates all three fixed header bounds, restores
every temporary marker, and halts at the original transition-region head.
-/
theorem reaches_logicalHeaderBounds
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (hpositive : 0 < stateCount)
    (hstart : start < stateCount)
    (hhalt : halt < stateCount) :
    blockDescription.Reaches
      (logicalStartConfig stateCount start halt transitionCount tokens)
      (logicalHandoffConfig stateCount start halt transitionCount tokens) := by
  let code := validatorCanonicalBlocks tokens
  let transitionTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate transitionCount .tick) (.done :: code)
  let haltTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate halt .tick) (.done :: transitionTail)

  have hlocate := reaches_start_comparison_entry
    stateCount start halt transitionCount tokens hpositive
  have hstartRun := reaches_start_bound_from_entry
    stateCount start haltTail hstart
  have hhaltRun := reaches_halt_bound_from_entry
    stateCount start halt transitionTail hhalt
  have hreturn := reaches_right_over_tick_field
    (scan := 29) (target := 30) (by decide) (by decide)
    transitionCount (restoredHaltLeft stateCount start halt) code

  have hlocate' :
      blockDescription.Reaches
        (logicalStartConfig stateCount start halt transitionCount tokens)
        (configuration 6
          (List.append [.header] (natBlocks stateCount))
          (List.append (List.replicate start .tick) (.done :: haltTail))) := by
    simpa [haltTail, transitionTail, code, configuration,
      List.append_assoc] using hlocate
  have hstartRun' :
      blockDescription.Reaches
        (configuration 6
          (List.append [.header] (natBlocks stateCount))
          (List.append (List.replicate start .tick) (.done :: haltTail)))
        (configuration 16 (restoredStartLeft stateCount start) haltTail) := by
    exact hstartRun
  have hhaltRun' :
      blockDescription.Reaches
        (configuration 16 (restoredStartLeft stateCount start) haltTail)
        (configuration 29
          (restoredHaltLeft stateCount start halt) transitionTail) := by
    exact hhaltRun
  have hrun := hlocate'.trans
    (hstartRun'.trans (hhaltRun'.trans hreturn))
  simpa [logicalHandoffConfig, prefixBlocks, restoredHaltLeft,
    transitionTail, code, natBlocks, blockDescription, configuration,
    List.append_assoc] using hrun

end ValidatorHeaderBounds
end SelfHaltingRecognizer
end Computability
end FoC
