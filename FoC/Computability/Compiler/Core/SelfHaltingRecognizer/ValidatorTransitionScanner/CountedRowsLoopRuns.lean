import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsRuns

set_option doc.verso true

/-!
# Exact-code validator: counted-row loop runs

This module closes the outer declared-count loop around the checked one-row
execution.  It is separate from the endpoint-comparison proof so both modules
remain below the repository size ceiling.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorCountedRows

open Languages
open MachineDescription

private theorem reaches_scan_tick_field
    {state target : Nat}
    (htick :
      blockDescription.lookup state .tick =
        some
          { source := state
            read := .tick
            write := .tick
            move := Direction.right
            target := state })
    (hdone :
      blockDescription.lookup state .done =
        some
          { source := state
            read := .done
            write := .done
            move := Direction.right
            target := target })
    (count : Nat) (left after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state left
          (List.append (List.replicate count .tick) (.done :: after)))
        (configuration target
          (List.append
            (List.append left (List.replicate count .tick)) [.done])
          after) := by
  have hscan := reaches_scan_right_list
    (state := state)
    (show List ValidatorBlockSymbol from List.replicate count .tick)
    (by
      intro symbol hsymbol
      have heq : symbol = .tick :=
        (List.mem_replicate.mp hsymbol).2
      subst symbol
      exact htick)
    left (.done :: after)
  have hfinish := reaches_one_right hdone
    (List.append left (List.replicate count .tick)) after
  simpa [configuration, List.append_assoc] using hscan.trans hfinish

private theorem mem_canonical_leftCorridor
    {symbol : ValidatorBlockSymbol}
    (hmem : symbol ∈ canonicalCorridorSymbols) :
    symbol ∈ leftCorridorSymbols := by
  exact List.mem_append_left [.marker001]
    (List.mem_append_left [.marker010] hmem)

private theorem natBlocks_mem_leftCorridor
    (value : Nat) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        ValidatorHeaderBounds.natBlocks value)) :
    symbol ∈ leftCorridorSymbols := by
  unfold ValidatorHeaderBounds.natBlocks at hmem
  rcases List.mem_append.mp hmem with htick | hdone
  · have heq : symbol = .tick := (List.mem_replicate.mp htick).2
    subst symbol
    simp [leftCorridorSymbols, corridorSymbols,
      canonicalCorridorSymbols]
  · have heq : symbol = .done := List.mem_singleton.mp hdone
    subst symbol
    simp [leftCorridorSymbols, corridorSymbols,
      canonicalCorridorSymbols]

private theorem natBlocks_mem_corridor
    (value : Nat) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        ValidatorHeaderBounds.natBlocks value)) :
    symbol ∈ corridorSymbols := by
  unfold ValidatorHeaderBounds.natBlocks at hmem
  rcases List.mem_append.mp hmem with htick | hdone
  · have heq : symbol = .tick := (List.mem_replicate.mp htick).2
    subst symbol
    simp [corridorSymbols, canonicalCorridorSymbols]
  · have heq : symbol = .done := List.mem_singleton.mp hdone
    subst symbol
    simp [corridorSymbols, canonicalCorridorSymbols]

/-- Mutable left context at one declared-count loop boundary. -/
def loopLeftBlocks
    (stateCount start halt processed remaining : Nat)
    (bridge : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (fixedPrefixBlocks stateCount start halt)
    (List.append (List.replicate processed .marker010)
      (List.append (List.replicate remaining .tick) bridge))

/-- Corridor between the state-count terminator and the marked current row. -/
def rowMiddleBlocks
    (start halt processed remaining : Nat)
    (bridge : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (ValidatorHeaderBounds.natBlocks start)
    (List.append (ValidatorHeaderBounds.natBlocks halt)
      (List.append (List.replicate processed .marker010)
        (List.append (List.replicate remaining .tick)
          (List.append bridge [.done]))))

/-- Every block in a selected row's preserved middle context belongs to the
logical scan corridor. -/
theorem rowMiddleBlocks_mem_corridor
    (start halt processed remaining : Nat)
    (bridge : Word ValidatorBlockSymbol)
    (hbridge : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from bridge) ->
        symbol ∈ canonicalCorridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        rowMiddleBlocks start halt processed remaining bridge)) :
    symbol ∈ corridorSymbols := by
  unfold rowMiddleBlocks at hmem
  rcases List.mem_append.mp hmem with hstart | htail
  · exact natBlocks_mem_corridor start symbol hstart
  · rcases List.mem_append.mp htail with hhalt | htail
    · exact natBlocks_mem_corridor halt symbol hhalt
    · rcases List.mem_append.mp htail with hprocessed | htail
      · have heq : symbol = .marker010 :=
          (List.mem_replicate.mp hprocessed).2
        subst symbol
        simp [corridorSymbols]
      · rcases List.mem_append.mp htail with hremaining | htail
        · have heq : symbol = .tick :=
            (List.mem_replicate.mp hremaining).2
          subst symbol
          simp [corridorSymbols, canonicalCorridorSymbols]
        · rcases List.mem_append.mp htail with hbridge' | hdone
          · exact List.mem_append_left [.marker010]
              (hbridge symbol hbridge')
          · have heq : symbol = .done := List.mem_singleton.mp hdone
            subst symbol
            simp [corridorSymbols, canonicalCorridorSymbols]

private theorem lookup_state6_rightCorridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ corridorSymbols) :
    blockDescription.lookup 6 symbol =
      some
        { source := 6
          read := symbol
          write := symbol
          move := Direction.right
          target := 6 } := by
  cases symbol <;>
    simp [corridorSymbols, canonicalCorridorSymbols] at hmem <;>
    decide

private theorem reaches_select_counted_row
    (stateCount start halt processed remaining : Nat)
    (row : TransitionDescription)
    (bridge after : Word ValidatorBlockSymbol)
    (hbridge : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from bridge) ->
        symbol ∈ canonicalCorridorSymbols) :
    blockDescription.Reaches
        (configuration 0
          (loopLeftBlocks stateCount start halt processed
            (remaining + 1) bridge)
          (.done :: List.append (rowBlocks row) after))
        (configuration 8
          (sourcePairLeft stateCount 0
            (rowMiddleBlocks start halt (processed + 1)
              remaining bridge))
          (List.append (List.replicate row.source .tick)
            (.done :: cellBlock row.read :: cellBlock row.write ::
              directionBlock row.move ::
                List.append (List.replicate row.target .tick)
                  (.done :: after)))) := by
  let headerTail : Word ValidatorBlockSymbol :=
    List.append (ValidatorHeaderBounds.natBlocks stateCount)
      (List.append (ValidatorHeaderBounds.natBlocks start)
        (ValidatorHeaderBounds.natBlocks halt))
  let countMarkers : Word ValidatorBlockSymbol :=
    List.replicate processed .marker010
  let countTicks : Word ValidatorBlockSymbol :=
    List.replicate (remaining + 1) .tick
  let scanCorridor : Word ValidatorBlockSymbol :=
    List.append headerTail
      (List.append countMarkers (List.append countTicks bridge))
  let rowTail : Word ValidatorBlockSymbol :=
    List.append (rowBlocks row) after
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append (List.replicate remaining .tick) bridge

  let c0 := configuration 0
    (.header :: scanCorridor) (.done :: rowTail)
  let c1 := configuration 1 []
    (.header :: List.append scanCorridor (.marker011 :: rowTail))
  let c2 := configuration 2 [.header]
    (List.append scanCorridor (.marker011 :: rowTail))
  let c3 := configuration 3
    (List.append [.header]
      (ValidatorHeaderBounds.natBlocks stateCount))
    (List.append (ValidatorHeaderBounds.natBlocks start)
      (List.append (ValidatorHeaderBounds.natBlocks halt)
        (List.append countMarkers
          (List.append countTicks (List.append bridge
            (.marker011 :: rowTail))))))
  let c4 := configuration 4
    (List.append
      (List.append [.header]
        (ValidatorHeaderBounds.natBlocks stateCount))
      (ValidatorHeaderBounds.natBlocks start))
    (List.append (ValidatorHeaderBounds.natBlocks halt)
      (List.append countMarkers
        (List.append countTicks (List.append bridge
          (.marker011 :: rowTail)))))
  let c5 := configuration 5
    (fixedPrefixBlocks stateCount start halt)
    (List.append countMarkers
      (List.append countTicks (List.append bridge
        (.marker011 :: rowTail))))
  let c6 := configuration 5
    (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
    (.tick :: List.append (List.replicate remaining .tick)
      (List.append bridge (.marker011 :: rowTail)))
  let c7 := configuration 6
    (List.append
      (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
      [.marker010])
    (List.append returnCorridor (.marker011 :: rowTail))
  let c8 := configuration 6
    (List.append
      (List.append
        (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
      [.marker010]) returnCorridor)
    (.marker011 :: rowTail)
  let c9Left : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (List.append
          (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
          [.marker010]) returnCorridor)
      [.done]
  let c9 := configuration 7 c9Left rowTail
  let c10 := configuration 8
    (List.append c9Left [.marker001])
    (List.append (ValidatorHeaderBounds.natBlocks row.source)
      (cellBlock row.read :: cellBlock row.write ::
        directionBlock row.move ::
          List.append (ValidatorHeaderBounds.natBlocks row.target) after))

  have htoHeader := reaches_to_header
    (entry := 0) (scan := 1)
    (entryRead := .done) (entryWrite := .marker011)
    (by decide) (by decide) scanCorridor rowTail
    (by
      intro symbol hsymbol
      unfold scanCorridor at hsymbol
      rcases List.mem_append.mp hsymbol with hheader | hcount
      · unfold headerTail at hheader
        rcases List.mem_append.mp hheader with hstate | htail
        · exact natBlocks_mem_leftCorridor stateCount symbol hstate
        · rcases List.mem_append.mp htail with hstart | hhalt
          · exact natBlocks_mem_leftCorridor start symbol hstart
          · exact natBlocks_mem_leftCorridor halt symbol hhalt
      · rcases List.mem_append.mp hcount with hmarkers | htail
        · have heq : symbol = .marker010 :=
            (List.mem_replicate.mp hmarkers).2
          subst symbol
          simp [leftCorridorSymbols, corridorSymbols]
        · rcases List.mem_append.mp htail with hticks | hbridge'
          · have heq : symbol = .tick :=
              (List.mem_replicate.mp hticks).2
            subst symbol
            simp [leftCorridorSymbols, corridorSymbols,
              canonicalCorridorSymbols]
          · exact mem_canonical_leftCorridor
              (hbridge symbol hbridge'))
  have hheader := reaches_one_right
    (state := 1) (target := 2)
    (read := .header) (write := .header)
    (by decide) []
    (List.append scanCorridor (.marker011 :: rowTail))
  have hstateField := reaches_scan_tick_field
    (state := 2) (target := 3) (by decide) (by decide)
    stateCount [.header]
    (List.append (ValidatorHeaderBounds.natBlocks start)
      (List.append (ValidatorHeaderBounds.natBlocks halt)
        (List.append countMarkers
          (List.append countTicks (List.append bridge
            (.marker011 :: rowTail))))))
  have hstartField := reaches_scan_tick_field
    (state := 3) (target := 4) (by decide) (by decide)
    start
    (List.append [.header]
      (ValidatorHeaderBounds.natBlocks stateCount))
    (List.append (ValidatorHeaderBounds.natBlocks halt)
      (List.append countMarkers
        (List.append countTicks (List.append bridge
          (.marker011 :: rowTail)))))
  have hhaltField := reaches_scan_tick_field
    (state := 4) (target := 5) (by decide) (by decide)
    halt
    (List.append
      (List.append [.header]
        (ValidatorHeaderBounds.natBlocks stateCount))
      (ValidatorHeaderBounds.natBlocks start))
    (List.append countMarkers
      (List.append countTicks (List.append bridge
        (.marker011 :: rowTail))))
  have hcountMarkers := reaches_scan_right_list
    (state := 5)
    (show List ValidatorBlockSymbol from countMarkers)
    (by
      intro symbol hsymbol
      have heq : symbol = .marker010 :=
        (List.mem_replicate.mp hsymbol).2
      subst symbol
      decide)
    (fixedPrefixBlocks stateCount start halt)
    (List.append countTicks (List.append bridge
      (.marker011 :: rowTail)))
  have hcountTick := reaches_one_right
    (state := 5) (target := 6)
    (read := .tick) (write := .marker010)
    (by decide)
    (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
    (List.append (List.replicate remaining .tick)
      (List.append bridge (.marker011 :: rowTail)))
  have hreturn := reaches_scan_right_list
    (state := 6)
    (show List ValidatorBlockSymbol from returnCorridor)
    (fun symbol hsymbol =>
      lookup_state6_rightCorridor symbol (by
        unfold returnCorridor at hsymbol
        rcases List.mem_append.mp hsymbol with htick | hbridge'
        · have heq : symbol = .tick :=
            (List.mem_replicate.mp htick).2
          subst symbol
          simp [corridorSymbols, canonicalCorridorSymbols]
        · exact List.mem_append_left [.marker010]
            (hbridge symbol hbridge')))
    (List.append
      (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
      [.marker010])
    (.marker011 :: rowTail)
  have hboundary := reaches_one_right
    (state := 6) (target := 7)
    (read := .marker011) (write := .done)
    (by decide)
    (List.append
      (List.append
        (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
        [.marker010]) returnCorridor)
    rowTail
  have htransition := reaches_one_right
    (state := 7) (target := 8)
    (read := .transition) (write := .marker001)
    (by decide) c9Left
    (List.append (ValidatorHeaderBounds.natBlocks row.source)
      (cellBlock row.read :: cellBlock row.write ::
        directionBlock row.move ::
          List.append (ValidatorHeaderBounds.natBlocks row.target) after))

  have h01 : blockDescription.Reaches c0 c1 := htoHeader
  have h12 : blockDescription.Reaches c1 c2 := hheader
  have h23 : blockDescription.Reaches c2 c3 := by
    simpa [c2, c3, scanCorridor, headerTail, countMarkers, countTicks,
      rowTail, configuration, ValidatorHeaderBounds.natBlocks,
      List.append_assoc] using hstateField
  have h34 : blockDescription.Reaches c3 c4 := by
    simpa [c3, c4, configuration, ValidatorHeaderBounds.natBlocks,
      List.append_assoc] using hstartField
  have h45 : blockDescription.Reaches c4 c5 := by
    simpa [c4, c5, fixedPrefixBlocks, configuration,
      ValidatorHeaderBounds.natBlocks, List.append_assoc] using hhaltField
  have h56 : blockDescription.Reaches c5 c6 := by
    simpa [c5, c6, countTicks, configuration,
      List.replicate_succ, List.append_assoc] using hcountMarkers
  have h67 : blockDescription.Reaches c6 c7 := by
    simpa [c6, c7, returnCorridor, configuration,
      List.append_assoc] using hcountTick
  have h78 : blockDescription.Reaches c7 c8 := hreturn
  have h89 : blockDescription.Reaches c8 c9 := hboundary
  have h910 : blockDescription.Reaches c9 c10 := by
    simpa [c9, c10, c9Left, rowTail, rowBlocks, configuration,
      ValidatorHeaderBounds.natBlocks, List.append_assoc] using
      htransition
  have hrun := h01.trans (h12.trans (h23.trans (h34.trans
    (h45.trans (h56.trans (h67.trans (h78.trans (h89.trans h910))))))))
  simpa [c0, c10, c9Left, loopLeftBlocks, rowMiddleBlocks,
    sourcePairLeft_zero, scanCorridor, headerTail, countMarkers, countTicks,
    returnCorridor, rowTail, rowBlocks, fixedPrefixBlocks,
    ValidatorHeaderBounds.natBlocks, configuration,
    List.replicate_succ', List.append_assoc] using hrun

/-- A successful checked row restores exactly the next loop's left context. -/
theorem restoredRowLeft_eq_next_loop
    (stateCount start halt processed remaining : Nat)
    (row : TransitionDescription)
    (bridge : Word ValidatorBlockSymbol) :
    restoredRowLeft stateCount row.target row
        (rowMiddleBlocks start halt (processed + 1) remaining bridge) =
      loopLeftBlocks stateCount start halt (processed + 1) remaining
        (List.append (List.append bridge [.done]) (rowBodyBlocks row)) := by
  simp [restoredRowLeft, rowMiddleBlocks, loopLeftBlocks,
    fixedPrefixBlocks, rowBodyBlocks, ValidatorHeaderBounds.natBlocks,
    List.append_assoc]

private theorem reaches_one_counted_row
    (stateCount start halt processed remaining : Nat)
    (row : TransitionDescription)
    (bridge after : Word ValidatorBlockSymbol)
    (hbridge : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from bridge) ->
        symbol ∈ canonicalCorridorSymbols)
    (hsource : row.source < stateCount)
    (htarget : row.target < stateCount) :
    blockDescription.Reaches
        (configuration 0
          (loopLeftBlocks stateCount start halt processed
            (remaining + 1) bridge)
          (.done :: List.append (rowBlocks row) after))
        (configuration 0
          (loopLeftBlocks stateCount start halt (processed + 1)
            remaining
            (List.append (List.append bridge [.done])
              (rowBodyBlocks row)))
          (.done :: after)) := by
  have hselect := reaches_select_counted_row
    stateCount start halt processed remaining row bridge after hbridge
  have hcheck := reaches_checked_row
    stateCount row
    (rowMiddleBlocks start halt (processed + 1) remaining bridge)
    after
    (rowMiddleBlocks_mem_corridor start halt (processed + 1)
      remaining bridge hbridge)
    hsource htarget
  have hrun := hselect.trans hcheck
  simpa [restoredRowLeft_eq_next_loop] using hrun

private def rowLoopBlocks : List TransitionDescription ->
    Word ValidatorBlockSymbol
  | [] => []
  | row :: rest =>
      List.append (List.append [.done] (rowBodyBlocks row))
        (rowLoopBlocks rest)

private theorem rowBodyBlocks_mem_canonical
    (row : TransitionDescription) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from rowBodyBlocks row)) :
    symbol ∈ canonicalCorridorSymbols := by
  apply canonicalCorridor_rowBlocks row symbol
  rw [rowBlocks_eq_body_append_done]
  exact List.mem_append_left [.done] hmem

/-- Extending the processed-row bridge preserves its canonical alphabet. -/
theorem extendedBridge_mem_canonical
    (row : TransitionDescription)
    (bridge : Word ValidatorBlockSymbol)
    (hbridge : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from bridge) ->
        symbol ∈ canonicalCorridorSymbols)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        List.append (List.append bridge [.done])
          (rowBodyBlocks row))) :
    symbol ∈ canonicalCorridorSymbols := by
  rcases List.mem_append.mp hmem with hprefix | hbody
  · rcases List.mem_append.mp hprefix with hbridge' | hdone
    · exact hbridge symbol hbridge'
    · have heq : symbol = .done := List.mem_singleton.mp hdone
      subst symbol
      simp [canonicalCorridorSymbols]
  · exact rowBodyBlocks_mem_canonical row symbol hbody

private theorem reaches_counted_rows
    (stateCount start halt processed : Nat)
    (rows : List TransitionDescription)
    (bridge after : Word ValidatorBlockSymbol)
    (hbridge : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from bridge) ->
        symbol ∈ canonicalCorridorSymbols)
    (hbounds : forall row : TransitionDescription,
      row ∈ rows -> row.source < stateCount ∧ row.target < stateCount) :
    blockDescription.Reaches
        (configuration 0
          (loopLeftBlocks stateCount start halt processed
            rows.length bridge)
          (.done :: List.append (rowsBlocks rows) after))
        (configuration 0
          (loopLeftBlocks stateCount start halt
            (processed + rows.length) 0
            (List.append bridge (rowLoopBlocks rows)))
          (.done :: after)) := by
  induction rows generalizing processed bridge with
  | nil =>
      simpa [rowLoopBlocks, rowsBlocks, configuration] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration 0
            (loopLeftBlocks stateCount start halt processed 0 bridge)
            (.done :: after))
  | cons row rest ih =>
      have hrowBounds := hbounds row List.mem_cons_self
      let nextBridge : Word ValidatorBlockSymbol :=
        List.append (List.append bridge [.done]) (rowBodyBlocks row)
      have hfirst := reaches_one_counted_row
        stateCount start halt processed rest.length row bridge
        (List.append (rowsBlocks rest) after) hbridge
        hrowBounds.1 hrowBounds.2
      have hnextBridge : forall symbol : ValidatorBlockSymbol,
          symbol ∈ (show List ValidatorBlockSymbol from nextBridge) ->
            symbol ∈ canonicalCorridorSymbols := by
        exact extendedBridge_mem_canonical row bridge hbridge
      have hrest := ih (processed := processed + 1)
        (bridge := nextBridge) hnextBridge
        (fun candidate hcandidate =>
          hbounds candidate (List.mem_cons_of_mem row hcandidate))
      have hrun := hfirst.trans hrest
      simpa [nextBridge, rowLoopBlocks, rowsBlocks, configuration,
        List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hrun

private theorem reaches_to_count_field
    (stateCount start halt : Nat)
    (tail after : Word ValidatorBlockSymbol)
    (htail : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from tail) ->
        symbol ∈ leftCorridorSymbols) :
    blockDescription.Reaches
        (configuration 0
          (List.append (fixedPrefixBlocks stateCount start halt) tail)
          (.done :: after))
        (configuration 5
          (fixedPrefixBlocks stateCount start halt)
          (List.append tail (.marker011 :: after))) := by
  let headerTail : Word ValidatorBlockSymbol :=
    List.append (ValidatorHeaderBounds.natBlocks stateCount)
      (List.append (ValidatorHeaderBounds.natBlocks start)
        (ValidatorHeaderBounds.natBlocks halt))
  let scanCorridor : Word ValidatorBlockSymbol :=
    List.append headerTail tail
  let c0 := configuration 0
    (.header :: scanCorridor) (.done :: after)
  let c1 := configuration 1 []
    (.header :: List.append scanCorridor (.marker011 :: after))
  let c2 := configuration 2 [.header]
    (List.append scanCorridor (.marker011 :: after))
  let c3 := configuration 3
    (List.append [.header]
      (ValidatorHeaderBounds.natBlocks stateCount))
    (List.append (ValidatorHeaderBounds.natBlocks start)
      (List.append (ValidatorHeaderBounds.natBlocks halt)
        (List.append tail (.marker011 :: after))))
  let c4 := configuration 4
    (List.append
      (List.append [.header]
        (ValidatorHeaderBounds.natBlocks stateCount))
      (ValidatorHeaderBounds.natBlocks start))
    (List.append (ValidatorHeaderBounds.natBlocks halt)
      (List.append tail (.marker011 :: after)))
  let c5 := configuration 5
    (fixedPrefixBlocks stateCount start halt)
    (List.append tail (.marker011 :: after))

  have htoHeader := reaches_to_header
    (entry := 0) (scan := 1)
    (entryRead := .done) (entryWrite := .marker011)
    (by decide) (by decide) scanCorridor after
    (by
      intro symbol hsymbol
      unfold scanCorridor at hsymbol
      rcases List.mem_append.mp hsymbol with hheader | htail'
      · unfold headerTail at hheader
        rcases List.mem_append.mp hheader with hstate | hrest
        · exact natBlocks_mem_leftCorridor stateCount symbol hstate
        · rcases List.mem_append.mp hrest with hstart | hhalt
          · exact natBlocks_mem_leftCorridor start symbol hstart
          · exact natBlocks_mem_leftCorridor halt symbol hhalt
      · exact htail symbol htail')
  have hheader := reaches_one_right
    (state := 1) (target := 2)
    (read := .header) (write := .header)
    (by decide) []
    (List.append scanCorridor (.marker011 :: after))
  have hstateField := reaches_scan_tick_field
    (state := 2) (target := 3) (by decide) (by decide)
    stateCount [.header]
    (List.append (ValidatorHeaderBounds.natBlocks start)
      (List.append (ValidatorHeaderBounds.natBlocks halt)
        (List.append tail (.marker011 :: after))))
  have hstartField := reaches_scan_tick_field
    (state := 3) (target := 4) (by decide) (by decide)
    start
    (List.append [.header]
      (ValidatorHeaderBounds.natBlocks stateCount))
    (List.append (ValidatorHeaderBounds.natBlocks halt)
      (List.append tail (.marker011 :: after)))
  have hhaltField := reaches_scan_tick_field
    (state := 4) (target := 5) (by decide) (by decide)
    halt
    (List.append
      (List.append [.header]
        (ValidatorHeaderBounds.natBlocks stateCount))
      (ValidatorHeaderBounds.natBlocks start))
    (List.append tail (.marker011 :: after))

  have h01 : blockDescription.Reaches c0 c1 := htoHeader
  have h12 : blockDescription.Reaches c1 c2 := hheader
  have h23 : blockDescription.Reaches c2 c3 := by
    simpa [c2, c3, scanCorridor, headerTail, configuration,
      ValidatorHeaderBounds.natBlocks, List.append_assoc] using hstateField
  have h34 : blockDescription.Reaches c3 c4 := by
    simpa [c3, c4, configuration, ValidatorHeaderBounds.natBlocks,
      List.append_assoc] using hstartField
  have h45 : blockDescription.Reaches c4 c5 := by
    simpa [c4, c5, fixedPrefixBlocks, configuration,
      ValidatorHeaderBounds.natBlocks, List.append_assoc] using hhaltField
  have hrun := h01.trans (h12.trans (h23.trans (h34.trans h45)))
  simpa [c0, c5, scanCorridor, headerTail, fixedPrefixBlocks,
    configuration, ValidatorHeaderBounds.natBlocks,
    List.append_assoc] using hrun

/-- Select one remaining declared-row boundary without assuming that the next
token is a transition token. -/
theorem reaches_select_counted_boundary
    (stateCount start halt processed remaining : Nat)
    (bridge after : Word ValidatorBlockSymbol)
    (hbridge : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from bridge) ->
        symbol ∈ canonicalCorridorSymbols) :
    blockDescription.Reaches
        (configuration 0
          (loopLeftBlocks stateCount start halt processed
            (remaining + 1) bridge)
          (.done :: after))
        (configuration 7
          (List.append
            (loopLeftBlocks stateCount start halt (processed + 1)
              remaining bridge)
            [.done])
          after) := by
  let countMarkers : Word ValidatorBlockSymbol :=
    List.replicate processed .marker010
  let countTicks : Word ValidatorBlockSymbol :=
    List.replicate (remaining + 1) .tick
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append (List.replicate remaining .tick) bridge
  let tail : Word ValidatorBlockSymbol :=
    List.append countMarkers (List.append countTicks bridge)
  let c5 := configuration 5
    (fixedPrefixBlocks stateCount start halt)
    (List.append tail (.marker011 :: after))
  let c6 := configuration 5
    (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
    (.tick :: List.append (List.replicate remaining .tick)
      (List.append bridge (.marker011 :: after)))
  let c7 := configuration 6
    (List.append
      (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
      [.marker010])
    (List.append returnCorridor (.marker011 :: after))
  let c8 := configuration 6
    (List.append
      (List.append
        (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
        [.marker010])
      returnCorridor)
    (.marker011 :: after)
  let c9 := configuration 7
    (List.append
      (List.append
        (List.append
          (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
          [.marker010])
        returnCorridor)
      [.done])
    after

  have hprefix := reaches_to_count_field
    stateCount start halt tail after (by
      intro symbol hsymbol
      unfold tail at hsymbol
      rcases List.mem_append.mp hsymbol with hmarkers | htail
      · have heq : symbol = .marker010 :=
          (List.mem_replicate.mp hmarkers).2
        subst symbol
        simp [leftCorridorSymbols, corridorSymbols]
      · rcases List.mem_append.mp htail with hticks | hbridge'
        · have heq : symbol = .tick :=
            (List.mem_replicate.mp hticks).2
          subst symbol
          simp [leftCorridorSymbols, corridorSymbols,
            canonicalCorridorSymbols]
        · exact mem_canonical_leftCorridor
            (hbridge symbol hbridge'))
  have hmarkers := reaches_scan_right_list
    (state := 5)
    (show List ValidatorBlockSymbol from countMarkers)
    (by
      intro symbol hsymbol
      have heq : symbol = .marker010 :=
        (List.mem_replicate.mp hsymbol).2
      subst symbol
      decide)
    (fixedPrefixBlocks stateCount start halt)
    (List.append countTicks (List.append bridge
      (.marker011 :: after)))
  have htick := reaches_one_right
    (state := 5) (target := 6)
    (read := .tick) (write := .marker010)
    (by decide)
    (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
    (List.append (List.replicate remaining .tick)
      (List.append bridge (.marker011 :: after)))
  have hreturn := reaches_scan_right_list
    (state := 6)
    (show List ValidatorBlockSymbol from returnCorridor)
    (fun symbol hsymbol =>
      lookup_state6_rightCorridor symbol (by
        unfold returnCorridor at hsymbol
        rcases List.mem_append.mp hsymbol with htick' | hbridge'
        · have heq : symbol = .tick :=
            (List.mem_replicate.mp htick').2
          subst symbol
          simp [corridorSymbols, canonicalCorridorSymbols]
        · exact List.mem_append_left [.marker010]
            (hbridge symbol hbridge')))
    (List.append
      (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
      [.marker010])
    (.marker011 :: after)
  have hboundary := reaches_one_right
    (state := 6) (target := 7)
    (read := .marker011) (write := .done)
    (by decide)
    (List.append
      (List.append
        (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
        [.marker010])
      returnCorridor)
    after

  have h05 : blockDescription.Reaches
      (configuration 0
        (loopLeftBlocks stateCount start halt processed
          (remaining + 1) bridge)
        (.done :: after))
      c5 := by
    simpa [c5, tail, countMarkers, countTicks, loopLeftBlocks,
      configuration, List.append_assoc] using hprefix
  have h56 : blockDescription.Reaches c5 c6 := by
    simpa [c5, c6, tail, countTicks, configuration,
      List.replicate_succ, List.append_assoc] using hmarkers
  have h67 : blockDescription.Reaches c6 c7 := by
    simpa [c6, c7, returnCorridor, configuration,
      List.append_assoc] using htick
  have h78 : blockDescription.Reaches c7 c8 := hreturn
  have h89 : blockDescription.Reaches c8 c9 := hboundary
  have hrun := h05.trans (h56.trans (h67.trans (h78.trans h89)))
  simpa [c9, countMarkers, returnCorridor, loopLeftBlocks,
    configuration, List.replicate_succ', List.append_assoc] using hrun

private theorem reaches_restore_count_markers
    (count : Nat)
    (before after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 38
          (List.append (List.append before [.done])
            (List.replicate count .marker010))
          (.marker010 :: after))
        (configuration 39
          (List.append before [.done])
          (List.append (List.replicate (count + 1) .tick) after)) := by
  induction count generalizing after with
  | zero =>
      have hmarker := reaches_one_left
        (state := 38) (target := 38)
        (read := .marker010) (write := .tick)
        (by decide) before after .done
      have hdone := reaches_one_right
        (state := 38) (target := 39)
        (read := .done) (write := .done)
        (by decide) before (.tick :: after)
      simpa [configuration] using hmarker.trans hdone
  | succ count ih =>
      have hmarker := reaches_one_left
        (state := 38) (target := 38)
        (read := .marker010) (write := .tick)
        (by decide)
        (List.append (List.append before [.done])
          (List.replicate count .marker010))
        after .marker010
      have htail := ih (after := .tick :: after)
      have hrun := hmarker.trans htail
      simpa [configuration, List.replicate_succ',
        List.append_assoc] using hrun

private theorem lookup_state39_rightCorridor
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ corridorSymbols) :
    blockDescription.lookup 39 symbol =
      some
        { source := 39
          read := symbol
          write := symbol
          move := Direction.right
          target := 39 } := by
  cases symbol <;>
    simp [corridorSymbols, canonicalCorridorSymbols] at hmem <;>
    decide

private theorem reaches_state39_handoff
    (symbols left after : Word ValidatorBlockSymbol)
    (hsymbols : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from symbols) ->
        symbol ∈ corridorSymbols) :
    blockDescription.Reaches
        (configuration 39 left
          (List.append symbols (.marker011 :: after)))
        (configuration 40
          (List.append (List.append left symbols) [.done]) after) := by
  have hscan := reaches_scan_right_list
    (state := 39) (show List ValidatorBlockSymbol from symbols)
    (fun symbol hsymbol =>
      lookup_state39_rightCorridor symbol (hsymbols symbol hsymbol))
    left (.marker011 :: after)
  have hfinish := reaches_one_right
    (state := 39) (target := 40)
    (read := .marker011) (write := .done)
    (by decide) (List.append left symbols) after
  simpa [configuration, List.append_assoc] using hscan.trans hfinish

private theorem reaches_finish_zero_rows
    (stateCount start halt : Nat)
    (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 0
          (loopLeftBlocks stateCount start halt 0 0 [])
          (.done :: after))
        (configuration 40
          (List.append (fixedPrefixBlocks stateCount start halt) [.done])
          after) := by
  have hprefix := reaches_to_count_field
    stateCount start halt [] after (by simp)
  have hfinish := reaches_one_right
    (state := 5) (target := 40)
    (read := .marker011) (write := .done)
    (by decide) (fixedPrefixBlocks stateCount start halt) after
  simpa [loopLeftBlocks, configuration] using hprefix.trans hfinish

private theorem reaches_finish_nonempty
    (stateCount start halt processed : Nat)
    (bridgeTail after : Word ValidatorBlockSymbol)
    (hbridgeTail : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from bridgeTail) ->
        symbol ∈ canonicalCorridorSymbols) :
    blockDescription.Reaches
        (configuration 0
          (loopLeftBlocks stateCount start halt (processed + 1) 0
            (.done :: bridgeTail))
          (.done :: after))
        (configuration 40
          (List.append
            (loopLeftBlocks stateCount start halt 0 (processed + 1)
              (.done :: bridgeTail))
            [.done])
          after) := by
  let countMarkers : Word ValidatorBlockSymbol :=
    List.replicate (processed + 1) .marker010
  let countTail : Word ValidatorBlockSymbol :=
    List.append countMarkers (.done :: bridgeTail)
  let restoredSymbols : Word ValidatorBlockSymbol :=
    List.append (List.replicate (processed + 1) .tick)
      (.done :: bridgeTail)
  let beforeCount : Word ValidatorBlockSymbol :=
    .header ::
      List.append (ValidatorHeaderBounds.natBlocks stateCount)
        (List.append (ValidatorHeaderBounds.natBlocks start)
          (List.replicate halt .tick))

  let c0 := configuration 0
    (loopLeftBlocks stateCount start halt (processed + 1) 0
      (.done :: bridgeTail))
    (.done :: after)
  let c5 := configuration 5
    (fixedPrefixBlocks stateCount start halt)
    (List.append countTail (.marker011 :: after))
  let c6 := configuration 5
    (List.append (fixedPrefixBlocks stateCount start halt) countMarkers)
    (.done :: List.append bridgeTail (.marker011 :: after))
  let c38 := configuration 38
    (List.append (fixedPrefixBlocks stateCount start halt)
      (List.replicate processed .marker010))
    (.marker010 :: .done ::
      List.append bridgeTail (.marker011 :: after))
  let c39 := configuration 39
    (fixedPrefixBlocks stateCount start halt)
    (List.append restoredSymbols (.marker011 :: after))
  let c40 := configuration 40
    (List.append
      (loopLeftBlocks stateCount start halt 0 (processed + 1)
        (.done :: bridgeTail))
      [.done])
    after

  have hprefix := reaches_to_count_field
    stateCount start halt countTail after
    (by
      intro symbol hsymbol
      unfold countTail at hsymbol
      rcases List.mem_append.mp hsymbol with hmarker | htail
      · have heq : symbol = .marker010 :=
          (List.mem_replicate.mp hmarker).2
        subst symbol
        simp [leftCorridorSymbols, corridorSymbols]
      · rcases List.mem_cons.mp htail with hdone | hbridge
        · subst symbol
          simp [leftCorridorSymbols, corridorSymbols,
            canonicalCorridorSymbols]
        · exact mem_canonical_leftCorridor
            (hbridgeTail symbol hbridge))
  have hmarkers := reaches_scan_right_list
    (state := 5) (show List ValidatorBlockSymbol from countMarkers)
    (by
      intro symbol hsymbol
      have heq : symbol = .marker010 :=
        (List.mem_replicate.mp hsymbol).2
      subst symbol
      decide)
    (fixedPrefixBlocks stateCount start halt)
    (.done :: List.append bridgeTail (.marker011 :: after))
  have hdone := reaches_one_left
    (state := 5) (target := 38)
    (read := .done) (write := .done)
    (by decide)
    (List.append (fixedPrefixBlocks stateCount start halt)
      (List.replicate processed .marker010))
    (List.append bridgeTail (.marker011 :: after))
    .marker010
  have hrestore := reaches_restore_count_markers
    processed beforeCount
    (.done :: List.append bridgeTail (.marker011 :: after))
  have hhandoff := reaches_state39_handoff
    restoredSymbols (fixedPrefixBlocks stateCount start halt) after
    (by
      intro symbol hsymbol
      unfold restoredSymbols at hsymbol
      rcases List.mem_append.mp hsymbol with htick | htail
      · have heq : symbol = .tick :=
          (List.mem_replicate.mp htick).2
        subst symbol
        simp [corridorSymbols, canonicalCorridorSymbols]
      · rcases List.mem_cons.mp htail with hdone | hbridge
        · subst symbol
          simp [corridorSymbols, canonicalCorridorSymbols]
        · exact List.mem_append_left [.marker010]
            (hbridgeTail symbol hbridge))

  have h05 : blockDescription.Reaches c0 c5 := by
    simpa [c0, c5, countTail, countMarkers, loopLeftBlocks,
      configuration, List.append_assoc] using hprefix
  have h56 : blockDescription.Reaches c5 c6 := by
    simpa [c5, c6, countTail, configuration,
      List.append_assoc] using hmarkers
  have h638 : blockDescription.Reaches c6 c38 := by
    simpa [c6, c38, countMarkers, configuration,
      List.replicate_succ', List.append_assoc] using hdone
  have h3839 : blockDescription.Reaches c38 c39 := by
    simpa [c38, c39, beforeCount, restoredSymbols,
      fixedPrefixBlocks, ValidatorHeaderBounds.natBlocks,
      configuration, List.append_assoc] using hrestore
  have h3940 : blockDescription.Reaches c39 c40 := by
    simpa [c39, c40, restoredSymbols, loopLeftBlocks,
      configuration, List.append_assoc] using hhandoff
  exact h05.trans (h56.trans (h638.trans (h3839.trans h3940)))

private theorem rowLoopBlocks_append_done
    (rows : List TransitionDescription) :
    List.append (rowLoopBlocks rows) [.done] =
      .done :: rowsBlocks rows := by
  induction rows with
  | nil => simp [rowLoopBlocks, rowsBlocks]
  | cons row rest ih =>
      have htail := congrArg
        (fun tail : Word ValidatorBlockSymbol =>
          List.append (List.append [.done] (rowBodyBlocks row)) tail)
        ih
      simpa [rowLoopBlocks, rowsBlocks, rowBlocks_eq_body_append_done,
        List.append_assoc] using htail

private theorem rowLoopBlocks_mem_canonical
    (rows : List TransitionDescription)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from rowLoopBlocks rows)) :
    symbol ∈ canonicalCorridorSymbols := by
  induction rows generalizing symbol with
  | nil => simp [rowLoopBlocks] at hmem
  | cons row rest ih =>
      unfold rowLoopBlocks at hmem
      rcases List.mem_append.mp hmem with hprefix | hrest
      · rcases List.mem_append.mp hprefix with hdone | hbody
        · have heq : symbol = .done := List.mem_singleton.mp hdone
          subst symbol
          simp [canonicalCorridorSymbols]
        · exact rowBodyBlocks_mem_canonical row symbol hbody
      · exact ih symbol hrest

private theorem reaches_finish_rows
    (stateCount start halt : Nat)
    (rows : List TransitionDescription)
    (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 0
          (loopLeftBlocks stateCount start halt rows.length 0
            (rowLoopBlocks rows))
          (.done :: after))
        (configuration 40
          (List.append
            (loopLeftBlocks stateCount start halt 0 rows.length
              (rowLoopBlocks rows))
            [.done])
          after) := by
  cases rows with
  | nil =>
      simpa [rowLoopBlocks, loopLeftBlocks] using
        reaches_finish_zero_rows stateCount start halt after
  | cons row rest =>
      let bridgeTail : Word ValidatorBlockSymbol :=
        List.append (rowBodyBlocks row) (rowLoopBlocks rest)
      have hbridgeTail : forall symbol : ValidatorBlockSymbol,
          symbol ∈ (show List ValidatorBlockSymbol from bridgeTail) ->
            symbol ∈ canonicalCorridorSymbols := by
        intro symbol hsymbol
        unfold bridgeTail at hsymbol
        rcases List.mem_append.mp hsymbol with hbody | hrest
        · exact rowBodyBlocks_mem_canonical row symbol hbody
        · exact rowLoopBlocks_mem_canonical rest symbol hrest
      have hfinish := reaches_finish_nonempty
        stateCount start halt rest.length bridgeTail after hbridgeTail
      simpa [bridgeTail, rowLoopBlocks, List.append_assoc] using hfinish

private theorem finishedLoopLeft_eq_handoff
    (stateCount start halt : Nat)
    (rows : List TransitionDescription) :
    List.append
        (loopLeftBlocks stateCount start halt 0 rows.length
          (rowLoopBlocks rows))
        [.done] =
      List.append
        (ValidatorHeaderBounds.prefixBlocks
          stateCount start halt rows.length)
        (rowsBlocks rows) := by
  have htail := congrArg
    (fun tail : Word ValidatorBlockSymbol =>
      List.append
        (List.append (fixedPrefixBlocks stateCount start halt)
          (List.replicate rows.length .tick))
        tail)
    (rowLoopBlocks_append_done rows)
  simpa [loopLeftBlocks, fixedPrefixBlocks,
    ValidatorHeaderBounds.prefixBlocks, ValidatorHeaderBounds.natBlocks,
    List.append_assoc] using htail

/-- All declared rows with bounded endpoints reach the restored suffix handoff. -/
theorem reaches_logical_handoff
    (stateCount start halt : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (hbounds : forall row : TransitionDescription,
      row ∈ rows -> row.source < stateCount ∧ row.target < stateCount) :
    blockDescription.Reaches
        (logicalStartConfig stateCount start halt rows.length rows suffix)
        (logicalHandoffConfig stateCount start halt rows.length rows suffix) := by
  have hstart : blockDescription.start = 0 := rfl
  have hhalt : blockDescription.halt = 40 := rfl
  let suffixBlocks : Word ValidatorBlockSymbol :=
    validatorCanonicalBlocks suffix
  have hrows := reaches_counted_rows
    stateCount start halt 0 rows [] suffixBlocks
    (by simp) hbounds
  have hfinish := reaches_finish_rows
    stateCount start halt rows suffixBlocks
  have hrows' : blockDescription.Reaches
      (logicalStartConfig stateCount start halt rows.length rows suffix)
      (configuration 0
        (loopLeftBlocks stateCount start halt rows.length 0
          (rowLoopBlocks rows))
        (.done :: suffixBlocks)) := by
    simpa [logicalStartConfig,
      startLeftBlocks_eq_fixedPrefix_append_ticks,
      loopLeftBlocks, suffixBlocks, configuration, hstart] using hrows
  have hfinish' : blockDescription.Reaches
      (configuration 0
        (loopLeftBlocks stateCount start halt rows.length 0
          (rowLoopBlocks rows))
        (.done :: suffixBlocks))
      (logicalHandoffConfig stateCount start halt rows.length rows suffix) := by
    rw [finishedLoopLeft_eq_handoff stateCount start halt rows] at hfinish
    simpa [logicalHandoffConfig, suffixBlocks, configuration, hhalt] using
      hfinish
  exact hrows'.trans hfinish'

/-- Count-indexed form of the complete bounded-row logical run. -/
theorem reaches_logical_handoff_of_count
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (hcount : rows.length = transitionCount)
    (hbounds : forall row : TransitionDescription,
      row ∈ rows -> row.source < stateCount ∧ row.target < stateCount) :
    blockDescription.Reaches
        (logicalStartConfig stateCount start halt transitionCount rows suffix)
        (logicalHandoffConfig stateCount start halt transitionCount rows suffix) := by
  subst transitionCount
  exact reaches_logical_handoff stateCount start halt rows suffix hbounds

end ValidatorCountedRows
end SelfHaltingRecognizer
end Computability
end FoC
