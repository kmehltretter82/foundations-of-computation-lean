import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRows

set_option doc.verso true

/-!
# Exact-code validator: logical counted-row runs

This module proves the forward execution of the counted-row block table.  The
proof is factored through heterogeneous corridor scans and one-row cycles so
the unbounded row list and both unbounded unary endpoints remain explicit.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorCountedRows

open Languages
open MachineDescription

/-- Compact logical configuration notation for counted-row proofs. -/
def configuration
    (state : Nat)
    (left right : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  { state := state
    tape := validatorLogicalBlockTape left right }

/-- Internal one-step right move shared with target restoration. -/
theorem reaches_one_right
    {state target : Nat} {read write : ValidatorBlockSymbol}
    (hlookup :
      blockDescription.lookup state read =
        some
          { source := state
            read := read
            write := write
            move := Direction.right
            target := target })
    (left rest : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state left (read :: rest))
        (configuration target (List.append left [write]) rest) := by
  simpa [configuration, ValidatorBlockDescription.blockConfiguration] using
    (ValidatorBlockDescription.reaches_one_right hlookup left rest)

/-- Internal one-step left move shared with target restoration. -/
theorem reaches_one_left
    {state target : Nat} {read write : ValidatorBlockSymbol}
    (hlookup :
      blockDescription.lookup state read =
        some
          { source := state
            read := read
            write := write
            move := Direction.left
            target := target })
    (left rest : Word ValidatorBlockSymbol)
    (previous : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state
          (List.append left [previous]) (read :: rest))
        (configuration target left (previous :: write :: rest)) := by
  simpa [configuration, ValidatorBlockDescription.blockConfiguration] using
    (ValidatorBlockDescription.reaches_one_left
      hlookup left rest previous)

/-- Scan a heterogeneous right word while preserving every symbol. -/
theorem reaches_scan_right_list
    {state : Nat} (symbols : List ValidatorBlockSymbol)
    (hlookup : forall symbol : ValidatorBlockSymbol,
      symbol ∈ symbols ->
        blockDescription.lookup state symbol =
          some
            { source := state
              read := symbol
              write := symbol
              move := Direction.right
              target := state })
    (left rest : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state left (List.append symbols rest))
        (configuration state (List.append left symbols) rest) := by
  simpa [configuration, ValidatorBlockDescription.blockConfiguration] using
    (ValidatorBlockDescription.reaches_scan_right_list
      symbols hlookup left rest)

/-!
The next helper states a left scan in the order in which symbols are
encountered.  Therefore the encountered word appears reversed in the physical
left context.
-/

private theorem reaches_cross_scan_left_list
    {entry scan : Nat}
    {entryRead entryWrite boundary : ValidatorBlockSymbol}
    (encountered : List ValidatorBlockSymbol)
    (hentry :
      blockDescription.lookup entry entryRead =
        some
          { source := entry
            read := entryRead
            write := entryWrite
            move := Direction.left
            target := scan })
    (hscan : forall symbol : ValidatorBlockSymbol,
      symbol ∈ encountered ->
        blockDescription.lookup scan symbol =
          some
            { source := scan
              read := symbol
              write := symbol
              move := Direction.left
              target := scan })
    (before after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration entry
          (List.append
            (List.append before [boundary]) encountered.reverse)
          (entryRead :: after))
        (configuration scan before
          (boundary ::
            List.append encountered.reverse (entryWrite :: after))) := by
  simpa [configuration, ValidatorBlockDescription.blockConfiguration] using
    (ValidatorBlockDescription.reaches_cross_scan_left_list
      encountered hentry hscan before after)

private theorem canonicalCorridor_natBlocks
    (value : Nat) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from
        ValidatorHeaderBounds.natBlocks value)) :
    symbol ∈ canonicalCorridorSymbols := by
  unfold ValidatorHeaderBounds.natBlocks at hmem
  rcases List.mem_append.mp hmem with htick | hdone
  · have heq : symbol = .tick := (List.mem_replicate.mp htick).2
    subst symbol
    simp [canonicalCorridorSymbols]
  · have heq : symbol = .done := List.mem_singleton.mp hdone
    subst symbol
    simp [canonicalCorridorSymbols]

/-- Encoded cell blocks belong to the canonical corridor alphabet. -/
theorem cellBlock_mem_canonicalCorridor
    (cell : Option Bool) :
    cellBlock cell ∈ canonicalCorridorSymbols := by
  cases cell with
  | none => simp [cellBlock, canonicalCorridorSymbols]
  | some bit => cases bit <;> simp [cellBlock, canonicalCorridorSymbols]

/-- Encoded direction blocks belong to the canonical corridor alphabet. -/
theorem directionBlock_mem_canonicalCorridor
    (move : Direction) :
    directionBlock move ∈ canonicalCorridorSymbols := by
  cases move <;> simp [directionBlock, canonicalCorridorSymbols]

/-- Every block of one canonical row belongs to the scan corridor alphabet. -/
theorem canonicalCorridor_rowBlocks
    (row : TransitionDescription) (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from rowBlocks row)) :
    symbol ∈ canonicalCorridorSymbols := by
  unfold rowBlocks at hmem
  rcases List.mem_cons.mp hmem with htransition | hrest
  · subst symbol
    simp [canonicalCorridorSymbols]
  · rcases List.mem_append.mp hrest with hsource | htail
    · exact canonicalCorridor_natBlocks row.source symbol hsource
    · rcases List.mem_append.mp htail with hfixed | htarget
      · rcases List.mem_cons.mp hfixed with hread | hfixed
        · subst symbol
          exact cellBlock_mem_canonicalCorridor row.read
        · rcases List.mem_cons.mp hfixed with hwrite | hfixed
          · subst symbol
            exact cellBlock_mem_canonicalCorridor row.write
          · have hmove := List.mem_singleton.mp hfixed
            subst symbol
            exact directionBlock_mem_canonicalCorridor row.move
      · exact canonicalCorridor_natBlocks row.target symbol htarget

/-- Every block of canonical rows belongs to the scan corridor alphabet. -/
theorem canonicalCorridor_rowsBlocks
    (rows : List TransitionDescription)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈
      (show List ValidatorBlockSymbol from rowsBlocks rows)) :
    symbol ∈ canonicalCorridorSymbols := by
  induction rows generalizing symbol with
  | nil => simp [rowsBlocks] at hmem
  | cons row rest ih =>
      unfold rowsBlocks at hmem
      rcases List.mem_append.mp hmem with hrow | hrest
      · exact canonicalCorridor_rowBlocks row symbol hrow
      · exact ih symbol hrest

private theorem lookup_leftCorridor
    (state : Nat)
    (hstate : state = 1 ∨ state = 9 ∨ state = 12 ∨
      state = 21 ∨ state = 28)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ leftCorridorSymbols) :
    blockDescription.lookup state symbol =
      some
        { source := state
          read := symbol
          write := symbol
          move := Direction.left
          target := state } := by
  rcases hstate with rfl | rfl | rfl | rfl | rfl <;>
    cases symbol <;>
      simp [leftCorridorSymbols, corridorSymbols,
        canonicalCorridorSymbols] at hmem <;>
      decide

private theorem lookup_rightCorridor
    (state : Nat)
    (hstate : state = 6 ∨ state = 11 ∨ state = 15 ∨
      state = 23 ∨ state = 31 ∨ state = 39)
    (symbol : ValidatorBlockSymbol)
    (hmem : symbol ∈ corridorSymbols) :
    blockDescription.lookup state symbol =
      some
        { source := state
          read := symbol
          write := symbol
          move := Direction.right
          target := state } := by
  rcases hstate with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases symbol <;>
      simp [corridorSymbols, canonicalCorridorSymbols] at hmem <;>
      decide

/-- Canonical row symbols are valid bidirectional corridor symbols. -/
theorem mem_corridor_of_canonical
    {symbol : ValidatorBlockSymbol}
    (hmem : symbol ∈ canonicalCorridorSymbols) :
    symbol ∈ corridorSymbols := by
  exact List.mem_append_left [.marker010] hmem

/-- Every bidirectional corridor symbol is valid in a leftward corridor. -/
theorem mem_leftCorridor_of_corridor
    {symbol : ValidatorBlockSymbol}
    (hmem : symbol ∈ corridorSymbols) :
    symbol ∈ leftCorridorSymbols := by
  exact List.mem_append_left [.marker001] hmem

/-- The unary tick belongs to the bidirectional corridor alphabet. -/
theorem tick_mem_corridor :
    ValidatorBlockSymbol.tick ∈ corridorSymbols := by
  simp [corridorSymbols, canonicalCorridorSymbols]

/-- The unary terminator belongs to the bidirectional corridor alphabet. -/
theorem done_mem_corridor :
    ValidatorBlockSymbol.done ∈ corridorSymbols := by
  simp [corridorSymbols, canonicalCorridorSymbols]

/-- The paired-tick marker belongs to the bidirectional corridor alphabet. -/
theorem marker010_mem_corridor :
    ValidatorBlockSymbol.marker010 ∈ corridorSymbols := by
  simp [corridorSymbols]

/-- Header fields before the transition-count unary field. -/
def fixedPrefixBlocks
    (stateCount start halt : Nat) :
    Word ValidatorBlockSymbol :=
  .header ::
    List.append (ValidatorHeaderBounds.natBlocks stateCount)
      (List.append (ValidatorHeaderBounds.natBlocks start)
        (ValidatorHeaderBounds.natBlocks halt))

/-- One row without its final target-field terminator. -/
def rowBodyBlocks (row : TransitionDescription) :
    Word ValidatorBlockSymbol :=
  .transition ::
    List.append (ValidatorHeaderBounds.natBlocks row.source)
      (List.append
        [cellBlock row.read, cellBlock row.write, directionBlock row.move]
        (List.replicate row.target .tick))

/-- A row is its boundary-free body followed by the target terminator. -/
theorem rowBlocks_eq_body_append_done
    (row : TransitionDescription) :
    rowBlocks row = List.append (rowBodyBlocks row) [.done] := by
  simp [rowBlocks, rowBodyBlocks, ValidatorHeaderBounds.natBlocks,
    List.append_assoc]

/-- The initial left context ends in the declared count ticks. -/
theorem startLeftBlocks_eq_fixedPrefix_append_ticks
    (stateCount start halt transitionCount : Nat) :
    ValidatorHeaderBounds.startLeftBlocks
        stateCount start halt transitionCount =
      List.append (fixedPrefixBlocks stateCount start halt)
        (List.replicate transitionCount .tick) := by
  simp [ValidatorHeaderBounds.startLeftBlocks, fixedPrefixBlocks,
    ValidatorHeaderBounds.natBlocks, List.append_assoc]

/-- Cross one selected symbol and return left across the canonical corridor to
the header block. -/
theorem reaches_to_header
    {entry scan : Nat}
    {entryRead entryWrite : ValidatorBlockSymbol}
    (hscanState : scan = 1 ∨ scan = 9 ∨ scan = 12 ∨
      scan = 21 ∨ scan = 28)
    (hentry :
      blockDescription.lookup entry entryRead =
        some
          { source := entry
            read := entryRead
            write := entryWrite
            move := Direction.left
            target := scan })
    (corridor after : Word ValidatorBlockSymbol)
    (hcorridor : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from corridor) ->
        symbol ∈ leftCorridorSymbols) :
    blockDescription.Reaches
        (configuration entry (.header :: corridor) (entryRead :: after))
        (configuration scan []
          (.header :: List.append corridor (entryWrite :: after))) := by
  have hrun := reaches_cross_scan_left_list
    (show List ValidatorBlockSymbol from corridor.reverse)
    hentry
    (fun symbol hsymbol =>
      lookup_leftCorridor scan hscanState symbol
        (hcorridor symbol (by simpa using hsymbol)))
    (before := []) (after := after) (boundary := .header)
  simpa [configuration, List.append_assoc] using hrun

/-- Shared heterogeneous rightward corridor scan. -/
theorem reaches_scan_right_corridor
    {state : Nat}
    (hstate : state = 6 ∨ state = 11 ∨ state = 15 ∨
      state = 23 ∨ state = 31 ∨ state = 39)
    (symbols left rest : Word ValidatorBlockSymbol)
    (hsymbols : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from symbols) ->
        symbol ∈ corridorSymbols) :
    blockDescription.Reaches
        (configuration state left (List.append symbols rest))
        (configuration state (List.append left symbols) rest) := by
  exact reaches_scan_right_list
    (show List ValidatorBlockSymbol from symbols)
    (fun symbol hsymbol =>
      lookup_rightCorridor state hstate symbol (hsymbols symbol hsymbol))
    left rest

/-- State-field layout with processed markers before remaining ticks. -/
def markedTicks (unmarked marked : Nat) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate marked .marker010)
    (List.replicate unmarked .tick)

/-- Mutable layout while source ticks are paired with state-count ticks. -/
def sourcePairLeft
    (stateRemaining marked : Nat)
    (middle : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  .header ::
    List.append (markedTicks stateRemaining marked)
      (.done ::
        List.append middle
          (.marker001 :: List.replicate marked .marker010))

/-- Initial source-pairing layout before any state/source ticks are marked. -/
theorem sourcePairLeft_zero
    (stateCount : Nat) (middle : Word ValidatorBlockSymbol) :
    sourcePairLeft stateCount 0 middle =
      .header ::
        List.append (List.replicate stateCount .tick)
          (.done :: List.append middle [.marker001]) := by
  simp [sourcePairLeft, markedTicks]

/-- Scan a homogeneous marker run to its right boundary. -/
theorem reaches_scan_right_markers
    {state : Nat}
    (hlookup :
      blockDescription.lookup state .marker010 =
        some
          { source := state
            read := .marker010
            write := .marker010
            move := Direction.right
            target := state })
    (count : Nat) (left rest : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state left
          (List.append (List.replicate count .marker010) rest))
        (configuration state
          (List.append left (List.replicate count .marker010)) rest) := by
  apply reaches_scan_right_list
  · intro symbol hsymbol
    have heq : symbol = .marker010 :=
      (List.mem_replicate.mp hsymbol).2
    subst symbol
    exact hlookup

/-- Pair one source-state tick with one state-count tick. -/
theorem reaches_pair_source_tick
    (stateRemaining sourceRemaining marked : Nat)
    (middle tail : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    blockDescription.Reaches
        (configuration 8
          (sourcePairLeft (stateRemaining + 1) marked middle)
          (List.append (List.replicate (sourceRemaining + 1) .tick)
            tail))
        (configuration 8
          (sourcePairLeft stateRemaining (marked + 1) middle)
          (List.append (List.replicate sourceRemaining .tick)
            tail)) := by
  let stateMarkers : Word ValidatorBlockSymbol :=
    List.replicate marked .marker010
  let stateTicks : Word ValidatorBlockSymbol :=
    List.replicate (stateRemaining + 1) .tick
  let sourceMarkers : Word ValidatorBlockSymbol :=
    List.replicate marked .marker010
  let sourceRest : Word ValidatorBlockSymbol :=
    List.append (List.replicate sourceRemaining .tick) tail
  let toHeaderCorridor : Word ValidatorBlockSymbol :=
    List.append (List.append stateMarkers stateTicks)
      (.done ::
        List.append middle (.marker001 :: sourceMarkers))
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append (List.replicate stateRemaining .tick)
      (.done :: middle)

  let c0 := configuration 8
    (.header :: toHeaderCorridor) (.tick :: sourceRest)
  let c1 := configuration 9 []
    (.header :: List.append toHeaderCorridor (.marker010 :: sourceRest))
  let c2 := configuration 10 [.header]
    (List.append toHeaderCorridor (.marker010 :: sourceRest))
  let c3 := configuration 10
    (List.append [.header] stateMarkers)
    (List.append stateTicks
      (.done :: List.append middle
        (.marker001 :: List.append sourceMarkers
          (.marker010 :: sourceRest))))
  let c4 := configuration 11
    (List.append (List.append [.header] stateMarkers) [.marker010])
    (List.append returnCorridor
      (.marker001 :: List.append sourceMarkers
        (.marker010 :: sourceRest)))
  let c5 := configuration 11
    (List.append
      (List.append (List.append [.header] stateMarkers) [.marker010])
      returnCorridor)
    (.marker001 :: List.append sourceMarkers
      (.marker010 :: sourceRest))
  let c6 := configuration 8
    (List.append
      (List.append
        (List.append (List.append [.header] stateMarkers) [.marker010])
        returnCorridor)
      [.marker001])
    (List.append sourceMarkers (.marker010 :: sourceRest))
  let c7 := configuration 8
    (List.append
      (List.append
        (List.append
          (List.append
            (List.append [.header] stateMarkers) [.marker010])
          returnCorridor)
        [.marker001])
      (List.replicate (marked + 1) .marker010))
    sourceRest

  have htoHeader := reaches_to_header
    (entry := 8) (scan := 9)
    (entryRead := .tick) (entryWrite := .marker010)
    (Or.inr (Or.inl rfl)) (by decide)
    toHeaderCorridor sourceRest
    (by
      intro symbol hsymbol
      unfold toHeaderCorridor at hsymbol
      rcases List.mem_append.mp hsymbol with hstate | htail
      · rcases List.mem_append.mp hstate with hmarkers | hticks
        · apply mem_leftCorridor_of_corridor
          have heq : symbol = .marker010 :=
            (List.mem_replicate.mp hmarkers).2
          subst symbol
          exact marker010_mem_corridor
        · have heq : symbol = .tick :=
            (List.mem_replicate.mp hticks).2
          subst symbol
          exact mem_leftCorridor_of_corridor tick_mem_corridor
      · rcases List.mem_cons.mp htail with hdone | htail
        · subst symbol
          exact mem_leftCorridor_of_corridor done_mem_corridor
        · rcases List.mem_append.mp htail with hmiddle' | htail
          · exact mem_leftCorridor_of_corridor
              (hmiddle symbol hmiddle')
          · rcases List.mem_cons.mp htail with hmarker | hsource
            · subst symbol
              simp [leftCorridorSymbols]
            · have heq : symbol = .marker010 :=
                (List.mem_replicate.mp hsource).2
              subst symbol
              exact mem_leftCorridor_of_corridor
                marker010_mem_corridor)
  have hheader := reaches_one_right
    (state := 9) (target := 10)
    (read := .header) (write := .header)
    (by decide) []
    (List.append toHeaderCorridor (.marker010 :: sourceRest))
  have hstateMarkers := reaches_scan_right_markers
    (state := 10) (by decide) marked [.header]
    (List.append stateTicks
      (.done :: List.append middle
        (.marker001 :: List.append sourceMarkers
          (.marker010 :: sourceRest))))
  have hmarkState := reaches_one_right
    (state := 10) (target := 11)
    (read := .tick) (write := .marker010)
    (by decide)
    (List.append [.header] stateMarkers)
    (List.append (List.replicate stateRemaining .tick)
      (.done :: List.append middle
        (.marker001 :: List.append sourceMarkers
          (.marker010 :: sourceRest))))
  have hreturn := reaches_scan_right_corridor
    (state := 11) (Or.inr (Or.inl rfl))
    returnCorridor
    (List.append (List.append [.header] stateMarkers) [.marker010])
    (.marker001 :: List.append sourceMarkers
      (.marker010 :: sourceRest))
    (by
      intro symbol hsymbol
      unfold returnCorridor at hsymbol
      rcases List.mem_append.mp hsymbol with htick | htail
      · have heq : symbol = .tick :=
          (List.mem_replicate.mp htick).2
        subst symbol
        exact tick_mem_corridor
      · rcases List.mem_cons.mp htail with hdone | hmiddle'
        · subst symbol
          exact done_mem_corridor
        · exact hmiddle symbol hmiddle')
  have hrowMarker := reaches_one_right
    (state := 11) (target := 8)
    (read := .marker001) (write := .marker001)
    (by decide)
    (List.append
      (List.append (List.append [.header] stateMarkers) [.marker010])
      returnCorridor)
    (List.append sourceMarkers (.marker010 :: sourceRest))
  have hsourceMarkers := reaches_scan_right_markers
    (state := 8) (by decide) (marked + 1)
    (List.append
      (List.append
        (List.append (List.append [.header] stateMarkers) [.marker010])
        returnCorridor)
      [.marker001]) sourceRest

  have h01 : blockDescription.Reaches c0 c1 := htoHeader
  have h12 : blockDescription.Reaches c1 c2 := hheader
  have h23 : blockDescription.Reaches c2 c3 := by
    simpa [c2, c3, toHeaderCorridor, stateMarkers, stateTicks,
      sourceMarkers, sourceRest, configuration, List.append_assoc] using
      hstateMarkers
  have h34 : blockDescription.Reaches c3 c4 := by
    simpa [c3, c4, stateTicks, returnCorridor, configuration,
      List.replicate_succ, List.append_assoc] using hmarkState
  have h45 : blockDescription.Reaches c4 c5 := hreturn
  have h56 : blockDescription.Reaches c5 c6 := hrowMarker
  have h67 : blockDescription.Reaches c6 c7 := by
    simpa [c6, c7, sourceMarkers, sourceRest, configuration,
      List.replicate_succ', List.append_assoc] using hsourceMarkers
  have hstateSucc :
      List.replicate (stateRemaining + 1) ValidatorBlockSymbol.tick =
        .tick :: List.replicate stateRemaining .tick := by
    exact List.replicate_succ
  have hsourceSucc :
      List.replicate (sourceRemaining + 1) ValidatorBlockSymbol.tick =
        .tick :: List.replicate sourceRemaining .tick := by
    exact List.replicate_succ
  have hmarkerSucc :
      List.replicate (marked + 1) ValidatorBlockSymbol.marker010 =
        List.append (List.replicate marked .marker010) [.marker010] := by
    exact List.replicate_succ'
  have hrun := h01.trans (h12.trans (h23.trans (h34.trans
    (h45.trans (h56.trans h67)))))
  simpa [c0, c7, sourcePairLeft, markedTicks, toHeaderCorridor,
    returnCorridor, stateMarkers, stateTicks, sourceMarkers, sourceRest,
    configuration, hstateSucc, hsourceSucc, hmarkerSucc,
    List.append_assoc] using hrun

/-- Pair an arbitrary source-tick prefix while leaving its following tail
untouched. -/
theorem reaches_pair_all_source_ticks
    (stateRemainder count marked : Nat)
    (middle tail : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    blockDescription.Reaches
        (configuration 8
          (sourcePairLeft (stateRemainder + count) marked middle)
          (List.append (List.replicate count .tick) tail))
        (configuration 8
          (sourcePairLeft stateRemainder (marked + count) middle)
          tail) := by
  induction count generalizing marked with
  | zero =>
      simpa [configuration] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration 8
            (sourcePairLeft (stateRemainder + 0) marked middle)
            tail)
  | succ count ih =>
      have hpair := reaches_pair_source_tick
        (stateRemainder + count) count marked middle tail hmiddle
      have htail := ih (marked + 1)
      have hstate :
          stateRemainder + (count + 1) =
            (stateRemainder + count) + 1 := by
        lia
      have hmarked :
          marked + (count + 1) = (marked + 1) + count := by
        lia
      simpa [hstate, hmarked] using hpair.trans htail

/-- Shared leftward rewrite run used by both endpoint comparisons. -/
theorem reaches_cross_rewrite_left_replicate
    {entry scan : Nat}
    {entryRead entryWrite scanRead scanWrite boundary :
      ValidatorBlockSymbol}
    (hentry :
      blockDescription.lookup entry entryRead =
        some
          { source := entry
            read := entryRead
            write := entryWrite
            move := Direction.left
            target := scan })
    (hscan :
      blockDescription.lookup scan scanRead =
        some
          { source := scan
            read := scanRead
            write := scanWrite
            move := Direction.left
            target := scan })
    (count : Nat) (before after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration entry
          (List.append (List.append before [boundary])
            (List.replicate count scanRead))
          (entryRead :: after))
        (configuration scan before
          (boundary ::
            List.append (List.replicate count scanWrite)
              (entryWrite :: after))) := by
  induction count generalizing entry entryRead entryWrite after with
  | zero =>
      have hrun := reaches_one_left hentry before after boundary
      simpa [configuration] using hrun
  | succ count ih =>
      have hfirst := reaches_one_left hentry
        (List.append (List.append before [boundary])
          (List.replicate count scanRead)) after scanRead
      have htail := ih
        (entry := scan) (entryRead := scanRead) (entryWrite := scanWrite)
        (hentry := hscan) (after := entryWrite :: after)
      simpa [configuration, List.replicate_succ', List.append_assoc] using
        hfirst.trans htail

private theorem reaches_rewrite_right_replicate
    {state target : Nat}
    {read write boundary : ValidatorBlockSymbol}
    (hlookup :
      blockDescription.lookup state read =
        some
          { source := state
            read := read
            write := write
            move := Direction.right
            target := state })
    (hboundary :
      blockDescription.lookup state boundary =
        some
          { source := state
            read := boundary
            write := boundary
            move := Direction.right
            target := target })
    (count : Nat) (left after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state left
          (List.append (List.replicate count read) (boundary :: after)))
        (configuration target
          (List.append
            (List.append left (List.replicate count write)) [boundary])
          after) := by
  cases count with
  | zero =>
      have hrun := reaches_one_right hboundary left after
      simpa [configuration] using hrun
  | succ count =>
      have hrewrite : blockDescription.Reaches
          (configuration state left
            (List.append (List.replicate (count + 1) read)
              (boundary :: after)))
          (configuration state
            (List.append left (List.replicate (count + 1) write))
            (boundary :: after)) := by
        apply ValidatorBlockDescription.reaches_of_runConfig
        exact ValidatorBlockDescription.runConfig_rewriteRight_replicate
          hlookup rfl rfl rfl count left after
      have hfinish := reaches_one_right hboundary
        (List.append left (List.replicate (count + 1) write)) after
      simpa [configuration, List.append_assoc] using
        hrewrite.trans hfinish

/-- Restored source-field layout immediately before the fixed row tokens. -/
def restoredSourceLeft
    (stateCount source : Nat)
    (middle : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  .header ::
    List.append (List.replicate stateCount .tick)
      (.done ::
        List.append middle
          (.marker001 ::
            List.append (List.replicate source .tick) [.done]))

private theorem reaches_finish_source_comparison
    (extra paired : Nat)
    (middle after : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    blockDescription.Reaches
        (configuration 8
          (sourcePairLeft (extra + 1) paired middle)
          (.done :: after))
        (configuration 17
          (restoredSourceLeft ((extra + 1) + paired) paired middle)
          after) := by
  let stateMarkers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let extraTicks : Word ValidatorBlockSymbol :=
    List.replicate extra .tick
  let sourceMarkers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let toHeaderCorridor : Word ValidatorBlockSymbol :=
    List.append
      (List.append stateMarkers (.tick :: extraTicks))
      (.done ::
        List.append middle (.marker001 :: sourceMarkers))
  let restoredStateTicks : Word ValidatorBlockSymbol :=
    List.append (List.replicate paired .tick) (.tick :: extraTicks)
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append restoredStateTicks (.done :: middle)

  let c0 := configuration 8
    (.header :: toHeaderCorridor) (.done :: after)
  let c1 := configuration 12 []
    (.header :: List.append toHeaderCorridor (.done :: after))
  let c2 := configuration 13 [.header]
    (List.append toHeaderCorridor (.done :: after))
  let c3 := configuration 13
    (List.append [.header] stateMarkers)
    (.tick :: List.append extraTicks
      (.done :: List.append middle
        (.marker001 :: List.append sourceMarkers (.done :: after))))
  let c4 := configuration 14 []
    (.header ::
      List.append (List.replicate paired .tick)
        (.tick :: List.append extraTicks
          (.done :: List.append middle
            (.marker001 :: List.append sourceMarkers (.done :: after)))))
  let c5 := configuration 15 [.header]
    (List.append restoredStateTicks
      (.done :: List.append middle
        (.marker001 :: List.append sourceMarkers (.done :: after))))
  let c6 := configuration 15
    (List.append [.header] returnCorridor)
    (.marker001 :: List.append sourceMarkers (.done :: after))
  let c7 := configuration 16
    (List.append (List.append [.header] returnCorridor) [.marker001])
    (List.append sourceMarkers (.done :: after))
  let c8 := configuration 17
    (List.append
      (List.append
        (List.append (List.append [.header] returnCorridor) [.marker001])
        (List.replicate paired .tick))
      [.done]) after

  have htoHeader := reaches_to_header
    (entry := 8) (scan := 12)
    (entryRead := .done) (entryWrite := .done)
    (Or.inr (Or.inr (Or.inl rfl))) (by decide)
    toHeaderCorridor after
    (by
      intro symbol hsymbol
      unfold toHeaderCorridor at hsymbol
      rcases List.mem_append.mp hsymbol with hstate | htail
      · rcases List.mem_append.mp hstate with hmarkers | hticks
        · have heq : symbol = .marker010 :=
            (List.mem_replicate.mp hmarkers).2
          subst symbol
          exact mem_leftCorridor_of_corridor marker010_mem_corridor
        · rcases List.mem_cons.mp hticks with htick | hextra
          · subst symbol
            exact mem_leftCorridor_of_corridor tick_mem_corridor
          · have heq : symbol = .tick :=
              (List.mem_replicate.mp hextra).2
            subst symbol
            exact mem_leftCorridor_of_corridor tick_mem_corridor
      · rcases List.mem_cons.mp htail with hdone | htail
        · subst symbol
          exact mem_leftCorridor_of_corridor done_mem_corridor
        · rcases List.mem_append.mp htail with hmiddle' | htail
          · exact mem_leftCorridor_of_corridor
              (hmiddle symbol hmiddle')
          · rcases List.mem_cons.mp htail with hmarker | hsource
            · subst symbol
              simp [leftCorridorSymbols]
            · have heq : symbol = .marker010 :=
                (List.mem_replicate.mp hsource).2
              subst symbol
              exact mem_leftCorridor_of_corridor
                marker010_mem_corridor)
  have hheader12 := reaches_one_right
    (state := 12) (target := 13)
    (read := .header) (write := .header)
    (by decide) []
    (List.append toHeaderCorridor (.done :: after))
  have hstateMarkers := reaches_scan_right_markers
    (state := 13) (by decide) paired [.header]
    (.tick :: List.append extraTicks
      (.done :: List.append middle
        (.marker001 :: List.append sourceMarkers (.done :: after))))
  have hrestoreState := reaches_cross_rewrite_left_replicate
    (entry := 13) (scan := 14)
    (entryRead := .tick) (entryWrite := .tick)
    (scanRead := .marker010) (scanWrite := .tick)
    (boundary := .header)
    (by decide) (by decide) paired []
    (List.append extraTicks
      (.done :: List.append middle
        (.marker001 :: List.append sourceMarkers (.done :: after))))
  have hheader14 := reaches_one_right
    (state := 14) (target := 15)
    (read := .header) (write := .header)
    (by decide) []
    (List.append restoredStateTicks
      (.done :: List.append middle
        (.marker001 :: List.append sourceMarkers (.done :: after))))
  have hreturn := reaches_scan_right_corridor
    (state := 15) (Or.inr (Or.inr (Or.inl rfl)))
    returnCorridor [.header]
    (.marker001 :: List.append sourceMarkers (.done :: after))
    (by
      intro symbol hsymbol
      unfold returnCorridor at hsymbol
      rcases List.mem_append.mp hsymbol with hstate | htail
      · unfold restoredStateTicks at hstate
        rcases List.mem_append.mp hstate with hpaired | hextra
        · have heq : symbol = .tick :=
            (List.mem_replicate.mp hpaired).2
          subst symbol
          exact tick_mem_corridor
        · rcases List.mem_cons.mp hextra with htick | hextra
          · subst symbol
            exact tick_mem_corridor
          · have heq : symbol = .tick :=
              (List.mem_replicate.mp hextra).2
            subst symbol
            exact tick_mem_corridor
      · rcases List.mem_cons.mp htail with hdone | hmiddle'
        · subst symbol
          exact done_mem_corridor
        · exact hmiddle symbol hmiddle')
  have hrowMarker := reaches_one_right
    (state := 15) (target := 16)
    (read := .marker001) (write := .marker001)
    (by decide) (List.append [.header] returnCorridor)
    (List.append sourceMarkers (.done :: after))
  have hrestoreSource := reaches_rewrite_right_replicate
    (state := 16) (target := 17)
    (read := .marker010) (write := .tick) (boundary := .done)
    (by decide) (by decide) paired
    (List.append (List.append [.header] returnCorridor) [.marker001])
    after

  have h01 : blockDescription.Reaches c0 c1 := htoHeader
  have h12 : blockDescription.Reaches c1 c2 := hheader12
  have h23 : blockDescription.Reaches c2 c3 := by
    simpa [c2, c3, toHeaderCorridor, stateMarkers, extraTicks,
      sourceMarkers, configuration, List.append_assoc] using hstateMarkers
  have h34 : blockDescription.Reaches c3 c4 := by
    simpa [c3, c4, stateMarkers, restoredStateTicks, configuration,
      List.append_assoc] using hrestoreState
  have h45 : blockDescription.Reaches c4 c5 := by
    simpa [c4, c5, restoredStateTicks, configuration,
      List.append_assoc] using hheader14
  have h56 : blockDescription.Reaches c5 c6 := by
    simpa [c5, c6, returnCorridor, configuration,
      List.append_assoc] using hreturn
  have h67 : blockDescription.Reaches c6 c7 := hrowMarker
  have h78 : blockDescription.Reaches c7 c8 := by
    simpa [c7, c8, sourceMarkers, configuration,
      List.append_assoc] using hrestoreSource
  have hrestoredState :
      restoredStateTicks =
        List.replicate ((extra + 1) + paired) .tick := by
    change
      (List.append (List.replicate paired ValidatorBlockSymbol.tick)
        (.tick :: List.replicate extra .tick) :
        List ValidatorBlockSymbol) =
      List.replicate ((extra + 1) + paired) .tick
    have hrep :=
      (list_replicate_add_append ValidatorBlockSymbol.tick
        paired (extra + 1) []).symm
    simpa [List.replicate_succ,
      show paired + (extra + 1) = (extra + 1) + paired by lia]
      using hrep
  have hrun := h01.trans (h12.trans (h23.trans (h34.trans
    (h45.trans (h56.trans (h67.trans h78))))))
  simpa [c0, c8, sourcePairLeft, markedTicks, restoredSourceLeft,
    toHeaderCorridor, stateMarkers, extraTicks, sourceMarkers,
    returnCorridor, hrestoredState, configuration,
    List.replicate_succ, List.append_assoc] using hrun

/-- A bounded source field reaches the first fixed cell token. -/
theorem reaches_source_bound
    (stateCount source : Nat)
    (middle after : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols)
    (hbound : source < stateCount) :
    blockDescription.Reaches
        (configuration 8
          (sourcePairLeft stateCount 0 middle)
          (List.append (List.replicate source .tick) (.done :: after)))
        (configuration 17
          (restoredSourceLeft stateCount source middle) after) := by
  let extra := stateCount - (source + 1)
  have hdecomp : stateCount = (extra + 1) + source := by
    dsimp [extra]
    lia
  have hpairs := reaches_pair_all_source_ticks
    (extra + 1) source 0 middle (.done :: after) hmiddle
  have hfinish := reaches_finish_source_comparison
    extra source middle after hmiddle
  have hpairs' : blockDescription.Reaches
      (configuration 8
        (sourcePairLeft stateCount 0 middle)
        (List.append (List.replicate source .tick) (.done :: after)))
      (configuration 8
        (sourcePairLeft (extra + 1) source middle)
        (.done :: after)) := by
    simpa [hdecomp] using hpairs
  have hfinish' : blockDescription.Reaches
      (configuration 8
        (sourcePairLeft (extra + 1) source middle)
        (.done :: after))
      (configuration 17
        (restoredSourceLeft stateCount source middle) after) := by
    simpa [hdecomp] using hfinish
  exact hpairs'.trans hfinish'

private theorem lookup_readCell
    (cell : Option Bool) :
    blockDescription.lookup 17 (cellBlock cell) =
      some
        { source := 17
          read := cellBlock cell
          write := cellBlock cell
          move := Direction.right
          target := 18 } := by
  cases cell with
  | none => decide
  | some bit => cases bit <;> decide

private theorem lookup_writeCell
    (cell : Option Bool) :
    blockDescription.lookup 18 (cellBlock cell) =
      some
        { source := 18
          read := cellBlock cell
          write := cellBlock cell
          move := Direction.right
          target := 19 } := by
  cases cell with
  | none => decide
  | some bit => cases bit <;> decide

private theorem lookup_move
    (move : Direction) :
    blockDescription.lookup 19 (directionBlock move) =
      some
        { source := 19
          read := directionBlock move
          write := directionBlock move
          move := Direction.right
          target := 20 } := by
  cases move <;> decide

private def rowBeforeTargetLeft
    (stateCount : Nat) (row : TransitionDescription)
    (middle : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (restoredSourceLeft stateCount row.source middle)
    [cellBlock row.read, cellBlock row.write, directionBlock row.move]

/-- Parse the two cells and direction of one canonical transition row. -/
theorem reaches_parse_fixed_row_fields
    (stateCount : Nat) (row : TransitionDescription)
    (middle tail : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 17
          (restoredSourceLeft stateCount row.source middle)
          (cellBlock row.read :: cellBlock row.write ::
            directionBlock row.move :: tail))
        (configuration 20
          (rowBeforeTargetLeft stateCount row middle) tail) := by
  have hread := reaches_one_right (lookup_readCell row.read)
    (restoredSourceLeft stateCount row.source middle)
    (cellBlock row.write :: directionBlock row.move :: tail)
  have hwrite := reaches_one_right (lookup_writeCell row.write)
    (List.append (restoredSourceLeft stateCount row.source middle)
      [cellBlock row.read])
    (directionBlock row.move :: tail)
  have hmove := reaches_one_right (lookup_move row.move)
    (List.append
      (List.append (restoredSourceLeft stateCount row.source middle)
        [cellBlock row.read])
      [cellBlock row.write]) tail
  simpa [rowBeforeTargetLeft, configuration, List.append_assoc] using
    hread.trans (hwrite.trans hmove)

/-- Mutable layout while target ticks are paired with state-count ticks. -/
def targetPairLeft
    (stateRemaining marked : Nat)
    (row : TransitionDescription)
    (middle : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  .header ::
    List.append (markedTicks stateRemaining marked)
      (.done ::
        List.append middle
          (.marker001 ::
            List.append (List.replicate row.source .tick)
              (.done ::
                cellBlock row.read :: cellBlock row.write ::
                  directionBlock row.move ::
                    List.replicate marked .marker010)))

/-- Initial target-pairing layout before any tick is marked. -/
theorem targetPairLeft_zero
    (stateCount : Nat) (row : TransitionDescription)
    (middle : Word ValidatorBlockSymbol) :
    targetPairLeft stateCount 0 row middle =
      rowBeforeTargetLeft stateCount row middle := by
  simp [targetPairLeft, rowBeforeTargetLeft, restoredSourceLeft,
    markedTicks, List.append_assoc]

private theorem lookup_targetReturnRead
    (cell : Option Bool) :
    blockDescription.lookup 25 (cellBlock cell) =
      some
        { source := 25
          read := cellBlock cell
          write := cellBlock cell
          move := Direction.right
          target := 26 } := by
  cases cell with
  | none => decide
  | some bit => cases bit <;> decide

private theorem lookup_targetReturnWrite
    (cell : Option Bool) :
    blockDescription.lookup 26 (cellBlock cell) =
      some
        { source := 26
          read := cellBlock cell
          write := cellBlock cell
          move := Direction.right
          target := 27 } := by
  cases cell with
  | none => decide
  | some bit => cases bit <;> decide

private theorem lookup_targetReturnMove
    (move : Direction) :
    blockDescription.lookup 27 (directionBlock move) =
      some
        { source := 27
          read := directionBlock move
          write := directionBlock move
          move := Direction.right
          target := 20 } := by
  cases move <;> decide

/-- Pair one target-state tick with one state-count tick. -/
theorem reaches_pair_target_tick
    (stateRemaining targetRemaining marked : Nat)
    (row : TransitionDescription)
    (middle tail : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    blockDescription.Reaches
        (configuration 20
          (targetPairLeft (stateRemaining + 1) marked row middle)
          (List.append (List.replicate (targetRemaining + 1) .tick)
            tail))
        (configuration 20
          (targetPairLeft stateRemaining (marked + 1) row middle)
          (List.append (List.replicate targetRemaining .tick)
            tail)) := by
  let stateMarkers : Word ValidatorBlockSymbol :=
    List.replicate marked .marker010
  let stateTicks : Word ValidatorBlockSymbol :=
    List.replicate (stateRemaining + 1) .tick
  let sourceTicks : Word ValidatorBlockSymbol :=
    List.replicate row.source .tick
  let targetMarkers : Word ValidatorBlockSymbol :=
    List.replicate marked .marker010
  let targetRest : Word ValidatorBlockSymbol :=
    List.append (List.replicate targetRemaining .tick) tail
  let fixedBlocks : Word ValidatorBlockSymbol :=
    [cellBlock row.read, cellBlock row.write, directionBlock row.move]
  let toHeaderCorridor : Word ValidatorBlockSymbol :=
    List.append (List.append stateMarkers stateTicks)
      (.done ::
        List.append middle
          (.marker001 ::
            List.append sourceTicks
              (.done :: List.append fixedBlocks targetMarkers)))
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append (List.replicate stateRemaining .tick)
      (.done :: middle)
  let markerLeft : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (List.append (List.append [.header] stateMarkers) [.marker010])
        returnCorridor)
      [.marker001]
  let sourceDoneLeft : Word ValidatorBlockSymbol :=
    List.append (List.append markerLeft sourceTicks) [.done]
  let readLeft : Word ValidatorBlockSymbol :=
    List.append sourceDoneLeft [cellBlock row.read]
  let writeLeft : Word ValidatorBlockSymbol :=
    List.append readLeft [cellBlock row.write]
  let moveLeft : Word ValidatorBlockSymbol :=
    List.append writeLeft [directionBlock row.move]

  let c0 := configuration 20
    (.header :: toHeaderCorridor) (.tick :: targetRest)
  let c1 := configuration 21 []
    (.header :: List.append toHeaderCorridor (.marker010 :: targetRest))
  let c2 := configuration 22 [.header]
    (List.append toHeaderCorridor (.marker010 :: targetRest))
  let c3 := configuration 22
    (List.append [.header] stateMarkers)
    (List.append stateTicks
      (.done ::
        List.append middle
          (.marker001 ::
            List.append sourceTicks
              (.done :: List.append fixedBlocks
                (List.append targetMarkers (.marker010 :: targetRest))))))
  let c4 := configuration 23
    (List.append (List.append [.header] stateMarkers) [.marker010])
    (List.append returnCorridor
      (.marker001 ::
        List.append sourceTicks
          (.done :: List.append fixedBlocks
            (List.append targetMarkers (.marker010 :: targetRest)))))
  let c5 := configuration 23
    (List.append
      (List.append (List.append [.header] stateMarkers) [.marker010])
      returnCorridor)
    (.marker001 ::
      List.append sourceTicks
        (.done :: List.append fixedBlocks
          (List.append targetMarkers (.marker010 :: targetRest))))
  let c6 := configuration 24
    (List.append
      (List.append
        (List.append (List.append [.header] stateMarkers) [.marker010])
        returnCorridor)
      [.marker001])
    (List.append sourceTicks
      (.done :: List.append fixedBlocks
        (List.append targetMarkers (.marker010 :: targetRest))))
  let c7 := configuration 25
    sourceDoneLeft
    (List.append fixedBlocks
      (List.append targetMarkers (.marker010 :: targetRest)))
  let c8 := configuration 26
    readLeft
    (cellBlock row.write :: directionBlock row.move ::
      List.append targetMarkers (.marker010 :: targetRest))
  let c9 := configuration 27
    writeLeft
    (directionBlock row.move ::
      List.append targetMarkers (.marker010 :: targetRest))
  let c10 := configuration 20
    moveLeft
    (List.append targetMarkers (.marker010 :: targetRest))
  let c11 := configuration 20
    (List.append moveLeft
      (List.replicate (marked + 1) .marker010)) targetRest

  have htoHeader := reaches_to_header
    (entry := 20) (scan := 21)
    (entryRead := .tick) (entryWrite := .marker010)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide)
    toHeaderCorridor targetRest
    (by
      intro symbol hsymbol
      unfold toHeaderCorridor at hsymbol
      rcases List.mem_append.mp hsymbol with hstate | htail
      · rcases List.mem_append.mp hstate with hmarkers | hticks
        · have heq : symbol = .marker010 :=
            (List.mem_replicate.mp hmarkers).2
          subst symbol
          exact mem_leftCorridor_of_corridor marker010_mem_corridor
        · have heq : symbol = .tick :=
            (List.mem_replicate.mp hticks).2
          subst symbol
          exact mem_leftCorridor_of_corridor tick_mem_corridor
      · rcases List.mem_cons.mp htail with hdone | htail
        · subst symbol
          exact mem_leftCorridor_of_corridor done_mem_corridor
        · rcases List.mem_append.mp htail with hmiddle' | htail
          · exact mem_leftCorridor_of_corridor
              (hmiddle symbol hmiddle')
          · rcases List.mem_cons.mp htail with hmarker | htail
            · subst symbol
              simp [leftCorridorSymbols]
            · rcases List.mem_append.mp htail with hsource | htail
              · have heq : symbol = .tick :=
                  (List.mem_replicate.mp hsource).2
                subst symbol
                exact mem_leftCorridor_of_corridor tick_mem_corridor
              · rcases List.mem_cons.mp htail with hdone | htail
                · subst symbol
                  exact mem_leftCorridor_of_corridor done_mem_corridor
                · rcases List.mem_append.mp htail with hfixed | htarget
                  · unfold fixedBlocks at hfixed
                    rcases List.mem_cons.mp hfixed with hread | hfixed
                    · subst symbol
                      exact mem_leftCorridor_of_corridor
                        (mem_corridor_of_canonical
                          (cellBlock_mem_canonicalCorridor row.read))
                    · rcases List.mem_cons.mp hfixed with hwrite | hfixed
                      · subst symbol
                        exact mem_leftCorridor_of_corridor
                          (mem_corridor_of_canonical
                            (cellBlock_mem_canonicalCorridor row.write))
                      · have hmove := List.mem_singleton.mp hfixed
                        subst symbol
                        exact mem_leftCorridor_of_corridor
                          (mem_corridor_of_canonical
                            (directionBlock_mem_canonicalCorridor row.move))
                  · have heq : symbol = .marker010 :=
                      (List.mem_replicate.mp htarget).2
                    subst symbol
                    exact mem_leftCorridor_of_corridor
                      marker010_mem_corridor)
  have hheader21 := reaches_one_right
    (state := 21) (target := 22)
    (read := .header) (write := .header)
    (by decide) []
    (List.append toHeaderCorridor (.marker010 :: targetRest))
  have hstateMarkers := reaches_scan_right_markers
    (state := 22) (by decide) marked [.header]
    (List.append stateTicks
      (.done ::
        List.append middle
          (.marker001 ::
            List.append sourceTicks
              (.done :: List.append fixedBlocks
                (List.append targetMarkers (.marker010 :: targetRest))))))
  have hmarkState := reaches_one_right
    (state := 22) (target := 23)
    (read := .tick) (write := .marker010)
    (by decide)
    (List.append [.header] stateMarkers)
    (List.append (List.replicate stateRemaining .tick)
      (.done ::
        List.append middle
          (.marker001 ::
            List.append sourceTicks
              (.done :: List.append fixedBlocks
                (List.append targetMarkers (.marker010 :: targetRest))))))
  have hreturn := reaches_scan_right_corridor
    (state := 23) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    returnCorridor
    (List.append (List.append [.header] stateMarkers) [.marker010])
    (.marker001 ::
      List.append sourceTicks
        (.done :: List.append fixedBlocks
          (List.append targetMarkers (.marker010 :: targetRest))))
    (by
      intro symbol hsymbol
      unfold returnCorridor at hsymbol
      rcases List.mem_append.mp hsymbol with htick | htail
      · have heq : symbol = .tick :=
          (List.mem_replicate.mp htick).2
        subst symbol
        exact tick_mem_corridor
      · rcases List.mem_cons.mp htail with hdone | hmiddle'
        · subst symbol
          exact done_mem_corridor
        · exact hmiddle symbol hmiddle')
  have hrowMarker := reaches_one_right
    (state := 23) (target := 24)
    (read := .marker001) (write := .marker001)
    (by decide)
    (List.append
      (List.append (List.append [.header] stateMarkers) [.marker010])
      returnCorridor)
    (List.append sourceTicks
      (.done :: List.append fixedBlocks
        (List.append targetMarkers (.marker010 :: targetRest))))
  have hsourceScan := reaches_scan_right_list
    (state := 24)
    (show List ValidatorBlockSymbol from sourceTicks)
    (by
      intro symbol hsymbol
      have heq : symbol = .tick :=
        (List.mem_replicate.mp hsymbol).2
      subst symbol
      decide)
    (List.append
      (List.append
        (List.append (List.append [.header] stateMarkers) [.marker010])
        returnCorridor)
      [.marker001])
    (.done :: List.append fixedBlocks
      (List.append targetMarkers (.marker010 :: targetRest)))
  have hsourceDone := reaches_one_right
    (state := 24) (target := 25)
    (read := .done) (write := .done)
    (by decide)
    (List.append
      (List.append
        (List.append
          (List.append (List.append [.header] stateMarkers) [.marker010])
          returnCorridor)
        [.marker001]) sourceTicks)
    (List.append fixedBlocks
      (List.append targetMarkers (.marker010 :: targetRest)))
  have hread := reaches_one_right (lookup_targetReturnRead row.read)
    sourceDoneLeft
    (cellBlock row.write :: directionBlock row.move ::
      List.append targetMarkers (.marker010 :: targetRest))
  have hwrite := reaches_one_right (lookup_targetReturnWrite row.write)
    readLeft
    (directionBlock row.move ::
      List.append targetMarkers (.marker010 :: targetRest))
  have hmove := reaches_one_right (lookup_targetReturnMove row.move)
    writeLeft
    (List.append targetMarkers (.marker010 :: targetRest))
  have htargetMarkers := reaches_scan_right_markers
    (state := 20) (by decide) (marked + 1)
    moveLeft targetRest

  have h01 : blockDescription.Reaches c0 c1 := htoHeader
  have h12 : blockDescription.Reaches c1 c2 := hheader21
  have h23 : blockDescription.Reaches c2 c3 := by
    simpa [c2, c3, toHeaderCorridor, stateMarkers, stateTicks,
      sourceTicks, fixedBlocks, targetMarkers, targetRest,
      configuration, List.append_assoc] using hstateMarkers
  have h34 : blockDescription.Reaches c3 c4 := by
    simpa [c3, c4, stateTicks, returnCorridor, configuration,
      List.replicate_succ, List.append_assoc] using hmarkState
  have h45 : blockDescription.Reaches c4 c5 := hreturn
  have h56 : blockDescription.Reaches c5 c6 := hrowMarker
  have h67 : blockDescription.Reaches c6 c7 := by
    simpa [c6, c7, markerLeft, sourceDoneLeft, fixedBlocks,
      configuration, List.append_assoc] using
      hsourceScan.trans hsourceDone
  have h78 : blockDescription.Reaches c7 c8 := by
    simpa [c7, c8, sourceDoneLeft, readLeft, fixedBlocks,
      configuration, List.append_assoc] using hread
  have h89 : blockDescription.Reaches c8 c9 := by
    simpa [c8, c9, readLeft, writeLeft, configuration,
      List.append_assoc] using hwrite
  have h910 : blockDescription.Reaches c9 c10 := by
    simpa [c9, c10, writeLeft, moveLeft, configuration,
      List.append_assoc] using hmove
  have h1011 : blockDescription.Reaches c10 c11 := by
    simpa [c10, c11, configuration, List.replicate_succ',
      List.append_assoc] using htargetMarkers
  have hstateSucc :
      List.replicate (stateRemaining + 1) ValidatorBlockSymbol.tick =
        .tick :: List.replicate stateRemaining .tick :=
    List.replicate_succ
  have htargetSucc :
      List.replicate (targetRemaining + 1) ValidatorBlockSymbol.tick =
        .tick :: List.replicate targetRemaining .tick :=
    List.replicate_succ
  have hmarkerSucc :
      List.replicate (marked + 1) ValidatorBlockSymbol.marker010 =
        List.append (List.replicate marked .marker010) [.marker010] :=
    List.replicate_succ'
  have hrun := h01.trans (h12.trans (h23.trans (h34.trans
    (h45.trans (h56.trans (h67.trans (h78.trans (h89.trans
      (h910.trans h1011)))))))))
  simpa [c0, c11, targetPairLeft, markedTicks, toHeaderCorridor,
    returnCorridor, stateMarkers, stateTicks, sourceTicks,
    targetMarkers, targetRest, fixedBlocks, markerLeft, sourceDoneLeft,
    readLeft, writeLeft, moveLeft, configuration,
    hstateSucc, htargetSucc, hmarkerSucc,
    List.append_assoc] using hrun


end ValidatorCountedRows
end SelfHaltingRecognizer
end Computability
end FoC
