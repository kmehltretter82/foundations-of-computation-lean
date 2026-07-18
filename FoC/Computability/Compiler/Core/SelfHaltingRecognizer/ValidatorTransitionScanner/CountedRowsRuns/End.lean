import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsRuns.Basic

set_option doc.verso true

/-! # Exact-code validator: target phase and row restoration -/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorCountedRows

open Languages
open MachineDescription
/-- Pair an arbitrary target-tick prefix while leaving its following tail
untouched. -/
theorem reaches_pair_all_target_ticks
    (stateRemainder count marked : Nat)
    (row : TransitionDescription)
    (middle tail : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    blockDescription.Reaches
        (configuration 20
          (targetPairLeft (stateRemainder + count) marked row middle)
          (List.append (List.replicate count .tick) tail))
        (configuration 20
          (targetPairLeft stateRemainder (marked + count) row middle)
          tail) := by
  induction count generalizing marked with
  | zero =>
      simpa [configuration] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration 20
            (targetPairLeft (stateRemainder + 0) marked row middle)
            tail)
  | succ count ih =>
      have hpair := reaches_pair_target_tick
        (stateRemainder + count) count marked row middle tail hmiddle
      have htail := ih (marked + 1)
      have hstate :
          stateRemainder + (count + 1) =
            (stateRemainder + count) + 1 := by
        lia
      have hmarked :
          marked + (count + 1) = (marked + 1) + count := by
        lia
      simpa [hstate, hmarked] using hpair.trans htail

private theorem reaches_rewrite_right_only_replicate
    {state : Nat} {read write boundary : ValidatorBlockSymbol}
    (hlookup :
      blockDescription.lookup state read =
        some
          { source := state
            read := read
            write := write
            move := Direction.right
            target := state })
    (count : Nat) (left after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state left
          (List.append (List.replicate count read) (boundary :: after)))
        (configuration state
          (List.append left (List.replicate count write))
          (boundary :: after)) := by
  cases count with
  | zero =>
      simpa [configuration] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration state left (boundary :: after))
  | succ count =>
      apply ValidatorBlockDescription.reaches_of_runConfig
      exact ValidatorBlockDescription.runConfig_rewriteRight_replicate
        hlookup rfl rfl rfl count left after

private theorem lookup_finishSourceRead
    (cell : Option Bool) :
    blockDescription.lookup 33 (cellBlock cell) =
      some
        { source := 33
          read := cellBlock cell
          write := cellBlock cell
          move := Direction.right
          target := 34 } := by
  cases cell with
  | none => decide
  | some bit => cases bit <;> decide

private theorem lookup_finishSourceWrite
    (cell : Option Bool) :
    blockDescription.lookup 34 (cellBlock cell) =
      some
        { source := 34
          read := cellBlock cell
          write := cellBlock cell
          move := Direction.right
          target := 35 } := by
  cases cell with
  | none => decide
  | some bit => cases bit <;> decide

private theorem lookup_finishSourceMove
    (move : Direction) :
    blockDescription.lookup 35 (directionBlock move) =
      some
        { source := 35
          read := directionBlock move
          write := directionBlock move
          move := Direction.right
          target := 36 } := by
  cases move <;> decide

private theorem lookup_bounceDirection
    (move : Direction) :
    blockDescription.lookup 37 (directionBlock move) =
      some
        { source := 37
          read := directionBlock move
          write := directionBlock move
          move := Direction.right
          target := 0 } := by
  cases move <;> decide

private theorem reaches_bounce_target_done
    (move : Direction) (target : Nat)
    (before after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 36
          (List.append
            (List.append before [directionBlock move])
            (List.replicate target .tick))
          (.done :: after))
        (configuration 0
          (List.append
            (List.append before [directionBlock move])
            (List.replicate target .tick))
          (.done :: after)) := by
  cases target with
  | zero =>
      have hleft := reaches_one_left
        (state := 36) (target := 37)
        (read := .done) (write := .done)
        (by decide) before after (directionBlock move)
      have hright := reaches_one_right
        (lookup_bounceDirection move) before (.done :: after)
      simpa [configuration] using hleft.trans hright
  | succ target =>
      have hleft := reaches_one_left
        (state := 36) (target := 37)
        (read := .done) (write := .done)
        (by decide)
        (List.append (List.append before [directionBlock move])
          (List.replicate target .tick)) after .tick
      have hright := reaches_one_right
        (state := 37) (target := 0)
        (read := .tick) (write := .tick)
        (by decide)
        (List.append (List.append before [directionBlock move])
          (List.replicate target .tick))
        (.done :: after)
      simpa [configuration, List.replicate_succ',
        List.append_assoc] using hleft.trans hright

/-- Restored row prefix after both endpoint comparisons. -/
def restoredRowLeft
    (stateCount target : Nat) (row : TransitionDescription)
    (middle : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  .header ::
    List.append (List.replicate stateCount .tick)
      (.done ::
        List.append middle
          (.transition ::
            List.append (List.replicate row.source .tick)
              (.done :: cellBlock row.read :: cellBlock row.write ::
                directionBlock row.move ::
                  List.replicate target .tick)))

private theorem reaches_finish_target_comparison
    (extra paired : Nat) (row : TransitionDescription)
    (middle after : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    blockDescription.Reaches
        (configuration 20
          (targetPairLeft (extra + 1) paired row middle)
          (.done :: after))
        (configuration 0
          (restoredRowLeft ((extra + 1) + paired) paired row middle)
          (.done :: after)) := by
  let stateMarkers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let extraTicks : Word ValidatorBlockSymbol :=
    List.replicate extra .tick
  let sourceTicks : Word ValidatorBlockSymbol :=
    List.replicate row.source .tick
  let targetMarkers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let fixedBlocks : Word ValidatorBlockSymbol :=
    [cellBlock row.read, cellBlock row.write, directionBlock row.move]
  let toHeaderCorridor : Word ValidatorBlockSymbol :=
    List.append
      (List.append stateMarkers (.tick :: extraTicks))
      (.done ::
        List.append middle
          (.marker001 ::
            List.append sourceTicks
              (.done :: List.append fixedBlocks targetMarkers)))
  let restoredStateTicks : Word ValidatorBlockSymbol :=
    List.append (List.replicate paired .tick) (.tick :: extraTicks)
  let returnCorridor : Word ValidatorBlockSymbol :=
    List.append restoredStateTicks (.done :: middle)
  let transitionLeft : Word ValidatorBlockSymbol :=
    List.append (List.append [.header] returnCorridor) [.transition]
  let sourceDoneLeft : Word ValidatorBlockSymbol :=
    List.append (List.append transitionLeft sourceTicks) [.done]
  let readLeft : Word ValidatorBlockSymbol :=
    List.append sourceDoneLeft [cellBlock row.read]
  let writeLeft : Word ValidatorBlockSymbol :=
    List.append readLeft [cellBlock row.write]
  let beforeDirection : Word ValidatorBlockSymbol := writeLeft
  let directionLeft : Word ValidatorBlockSymbol :=
    List.append beforeDirection [directionBlock row.move]

  let c0 := configuration 20
    (.header :: toHeaderCorridor) (.done :: after)
  let c1 := configuration 28 []
    (.header :: List.append toHeaderCorridor (.done :: after))
  let c2 := configuration 29 [.header]
    (List.append toHeaderCorridor (.done :: after))
  let c3 := configuration 29
    (List.append [.header] stateMarkers)
    (.tick :: List.append extraTicks
      (.done ::
        List.append middle
          (.marker001 ::
            List.append sourceTicks
              (.done :: List.append fixedBlocks
                (List.append targetMarkers (.done :: after))))))
  let c4 := configuration 30 []
    (.header ::
      List.append (List.replicate paired .tick)
        (.tick :: List.append extraTicks
          (.done ::
            List.append middle
              (.marker001 ::
                List.append sourceTicks
                  (.done :: List.append fixedBlocks
                    (List.append targetMarkers (.done :: after)))))))
  let c5 := configuration 31 [.header]
    (List.append restoredStateTicks
      (.done ::
        List.append middle
          (.marker001 ::
            List.append sourceTicks
              (.done :: List.append fixedBlocks
                (List.append targetMarkers (.done :: after))))))
  let c6 := configuration 31
    (List.append [.header] returnCorridor)
    (.marker001 ::
      List.append sourceTicks
        (.done :: List.append fixedBlocks
          (List.append targetMarkers (.done :: after))))
  let c7 := configuration 32 transitionLeft
    (List.append sourceTicks
      (.done :: List.append fixedBlocks
        (List.append targetMarkers (.done :: after))))
  let c8 := configuration 33 sourceDoneLeft
    (List.append fixedBlocks
      (List.append targetMarkers (.done :: after)))
  let c9 := configuration 34 readLeft
    (cellBlock row.write :: directionBlock row.move ::
      List.append targetMarkers (.done :: after))
  let c10 := configuration 35 writeLeft
    (directionBlock row.move ::
      List.append targetMarkers (.done :: after))
  let c11 := configuration 36 directionLeft
    (List.append targetMarkers (.done :: after))
  let c12 := configuration 36
    (List.append directionLeft (List.replicate paired .tick))
    (.done :: after)
  let c13 := configuration 0
    (List.append directionLeft (List.replicate paired .tick))
    (.done :: after)

  have htoHeader := reaches_to_header
    (entry := 20) (scan := 28)
    (entryRead := .done) (entryWrite := .done)
    (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by decide) toHeaderCorridor after
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
  have hheader28 := reaches_one_right
    (state := 28) (target := 29)
    (read := .header) (write := .header)
    (by decide) []
    (List.append toHeaderCorridor (.done :: after))
  have hstateMarkers := reaches_scan_right_markers
    (state := 29) (by decide) paired [.header]
    (.tick :: List.append extraTicks
      (.done ::
        List.append middle
          (.marker001 ::
            List.append sourceTicks
              (.done :: List.append fixedBlocks
                (List.append targetMarkers (.done :: after))))))
  have hrestoreState := reaches_cross_rewrite_left_replicate
    (entry := 29) (scan := 30)
    (entryRead := .tick) (entryWrite := .tick)
    (scanRead := .marker010) (scanWrite := .tick)
    (boundary := .header)
    (by decide) (by decide) paired []
    (List.append extraTicks
      (.done ::
        List.append middle
          (.marker001 ::
            List.append sourceTicks
              (.done :: List.append fixedBlocks
                (List.append targetMarkers (.done :: after))))))
  have hheader30 := reaches_one_right
    (state := 30) (target := 31)
    (read := .header) (write := .header)
    (by decide) []
    (List.append restoredStateTicks
      (.done ::
        List.append middle
          (.marker001 ::
            List.append sourceTicks
              (.done :: List.append fixedBlocks
                (List.append targetMarkers (.done :: after))))))
  have hreturn := reaches_scan_right_corridor
    (state := 31)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    returnCorridor [.header]
    (.marker001 ::
      List.append sourceTicks
        (.done :: List.append fixedBlocks
          (List.append targetMarkers (.done :: after))))
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
    (state := 31) (target := 32)
    (read := .marker001) (write := .transition)
    (by decide) (List.append [.header] returnCorridor)
    (List.append sourceTicks
      (.done :: List.append fixedBlocks
        (List.append targetMarkers (.done :: after))))
  have hsourceScan := reaches_scan_right_list
    (state := 32) (show List ValidatorBlockSymbol from sourceTicks)
    (by
      intro symbol hsymbol
      have heq : symbol = .tick :=
        (List.mem_replicate.mp hsymbol).2
      subst symbol
      decide)
    transitionLeft
    (.done :: List.append fixedBlocks
      (List.append targetMarkers (.done :: after)))
  have hsourceDone := reaches_one_right
    (state := 32) (target := 33)
    (read := .done) (write := .done)
    (by decide) (List.append transitionLeft sourceTicks)
    (List.append fixedBlocks
      (List.append targetMarkers (.done :: after)))
  have hread := reaches_one_right (lookup_finishSourceRead row.read)
    sourceDoneLeft
    (cellBlock row.write :: directionBlock row.move ::
      List.append targetMarkers (.done :: after))
  have hwrite := reaches_one_right (lookup_finishSourceWrite row.write)
    readLeft
    (directionBlock row.move ::
      List.append targetMarkers (.done :: after))
  have hmove := reaches_one_right (lookup_finishSourceMove row.move)
    writeLeft (List.append targetMarkers (.done :: after))
  have hrestoreTarget := reaches_rewrite_right_only_replicate
    (state := 36) (read := .marker010) (write := .tick)
    (boundary := .done) (by decide) paired directionLeft after
  have hbounce := reaches_bounce_target_done
    row.move paired beforeDirection after

  have h01 : blockDescription.Reaches c0 c1 := htoHeader
  have h12 : blockDescription.Reaches c1 c2 := hheader28
  have h23 : blockDescription.Reaches c2 c3 := by
    simpa [c2, c3, toHeaderCorridor, stateMarkers, extraTicks,
      sourceTicks, fixedBlocks, targetMarkers, configuration,
      List.append_assoc] using hstateMarkers
  have h34 : blockDescription.Reaches c3 c4 := by
    simpa [c3, c4, stateMarkers, restoredStateTicks, configuration,
      List.append_assoc] using hrestoreState
  have h45 : blockDescription.Reaches c4 c5 := by
    simpa [c4, c5, restoredStateTicks, configuration,
      List.append_assoc] using hheader30
  have h56 : blockDescription.Reaches c5 c6 := by
    simpa [c5, c6, returnCorridor, configuration,
      List.append_assoc] using hreturn
  have h67 : blockDescription.Reaches c6 c7 := by
    simpa [c6, c7, transitionLeft, configuration,
      List.append_assoc] using hrowMarker
  have h78 : blockDescription.Reaches c7 c8 := by
    simpa [c7, c8, sourceDoneLeft, fixedBlocks, configuration,
      List.append_assoc] using hsourceScan.trans hsourceDone
  have h89 : blockDescription.Reaches c8 c9 := by
    simpa [c8, c9, sourceDoneLeft, readLeft, fixedBlocks,
      configuration, List.append_assoc] using hread
  have h910 : blockDescription.Reaches c9 c10 := by
    simpa [c9, c10, readLeft, writeLeft, configuration,
      List.append_assoc] using hwrite
  have h1011 : blockDescription.Reaches c10 c11 := by
    simpa [c10, c11, writeLeft, beforeDirection, directionLeft,
      configuration, List.append_assoc] using hmove
  have h1112 : blockDescription.Reaches c11 c12 := by
    simpa [c11, c12, targetMarkers, configuration,
      List.append_assoc] using hrestoreTarget
  have h1213 : blockDescription.Reaches c12 c13 := by
    simpa [c12, c13, beforeDirection, directionLeft,
      configuration, List.append_assoc] using hbounce
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
    (h45.trans (h56.trans (h67.trans (h78.trans (h89.trans
      (h910.trans (h1011.trans (h1112.trans h1213)))))))))))
  simpa [c0, c13, targetPairLeft, markedTicks, restoredRowLeft,
    toHeaderCorridor, stateMarkers, extraTicks, sourceTicks,
    targetMarkers, fixedBlocks, returnCorridor,
    transitionLeft, sourceDoneLeft, readLeft, writeLeft,
    beforeDirection, directionLeft, hrestoredState, configuration,
    List.replicate_succ, List.append_assoc] using hrun

/-- A bounded target field restores the complete row and returns to state zero. -/
theorem reaches_target_bound
    (stateCount : Nat) (row : TransitionDescription)
    (middle after : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols)
    (hbound : row.target < stateCount) :
    blockDescription.Reaches
        (configuration 20
          (targetPairLeft stateCount 0 row middle)
          (List.append (List.replicate row.target .tick) (.done :: after)))
        (configuration 0
          (restoredRowLeft stateCount row.target row middle)
          (.done :: after)) := by
  let extra := stateCount - (row.target + 1)
  have hdecomp : stateCount = (extra + 1) + row.target := by
    dsimp [extra]
    lia
  have hpairs := reaches_pair_all_target_ticks
    (extra + 1) row.target 0 row middle (.done :: after) hmiddle
  have hfinish := reaches_finish_target_comparison
    extra row.target row middle after hmiddle
  have hpairs' : blockDescription.Reaches
      (configuration 20
        (targetPairLeft stateCount 0 row middle)
        (List.append (List.replicate row.target .tick) (.done :: after)))
      (configuration 20
        (targetPairLeft (extra + 1) row.target row middle)
        (.done :: after)) := by
    simpa [hdecomp] using hpairs
  have hfinish' : blockDescription.Reaches
      (configuration 20
        (targetPairLeft (extra + 1) row.target row middle)
        (.done :: after))
      (configuration 0
        (restoredRowLeft stateCount row.target row middle)
        (.done :: after)) := by
    simpa [hdecomp] using hfinish
  exact hpairs'.trans hfinish'

/-- One canonical row with bounded endpoints is parsed and fully restored. -/
theorem reaches_checked_row
    (stateCount : Nat) (row : TransitionDescription)
    (middle after : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols)
    (hsource : row.source < stateCount)
    (htarget : row.target < stateCount) :
    blockDescription.Reaches
        (configuration 8
          (sourcePairLeft stateCount 0 middle)
          (List.append (List.replicate row.source .tick)
            (.done :: cellBlock row.read :: cellBlock row.write ::
              directionBlock row.move ::
                List.append (List.replicate row.target .tick)
                  (.done :: after))))
        (configuration 0
          (restoredRowLeft stateCount row.target row middle)
          (.done :: after)) := by
  let sourceAfter : Word ValidatorBlockSymbol :=
    cellBlock row.read :: cellBlock row.write ::
      directionBlock row.move ::
        List.append (List.replicate row.target .tick) (.done :: after)
  have hsourceRun := reaches_source_bound
    stateCount row.source middle sourceAfter hmiddle hsource
  have hfixed := reaches_parse_fixed_row_fields
    stateCount row middle
    (List.append (List.replicate row.target .tick) (.done :: after))
  have htargetRun := reaches_target_bound
    stateCount row middle after hmiddle htarget
  have hsourceRun' : blockDescription.Reaches
      (configuration 8
        (sourcePairLeft stateCount 0 middle)
        (List.append (List.replicate row.source .tick)
          (.done :: cellBlock row.read :: cellBlock row.write ::
            directionBlock row.move ::
              List.append (List.replicate row.target .tick)
                (.done :: after))))
      (configuration 17
        (restoredSourceLeft stateCount row.source middle)
        (cellBlock row.read :: cellBlock row.write ::
          directionBlock row.move ::
            List.append (List.replicate row.target .tick)
              (.done :: after))) := by
    simpa [sourceAfter, configuration, List.append_assoc] using hsourceRun
  have hfixed' : blockDescription.Reaches
      (configuration 17
        (restoredSourceLeft stateCount row.source middle)
        (cellBlock row.read :: cellBlock row.write ::
          directionBlock row.move ::
            List.append (List.replicate row.target .tick)
              (.done :: after)))
      (configuration 20
        (targetPairLeft stateCount 0 row middle)
        (List.append (List.replicate row.target .tick)
          (.done :: after))) := by
    simpa [targetPairLeft_zero] using hfixed
  exact hsourceRun'.trans (hfixed'.trans htargetRun)

end ValidatorCountedRows
end SelfHaltingRecognizer
end Computability
end FoC
