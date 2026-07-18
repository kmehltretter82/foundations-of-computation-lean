import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.HeaderBounds
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockMachineInversion

set_option doc.verso true

/-!
# Exact-code validator: foundational header-bound runs

This module proves the forward execution of the compact 31-state aligned-block
table.  It deliberately stays in the logical block semantics; the following
compiler-simulation module transports the result to the generated Boolean
description and accounts for the four raw entry moves.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorHeaderBounds

open Languages
open MachineDescription

/-- Compact logical configuration notation shared with rejection runs. -/
def configuration
    (state : Nat)
    (left right : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  { state := state
    tape := validatorLogicalBlockTape left right }

/-- Shared one-step right move for header success and rejection runs. -/
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

/-- Shared one-step left move for header success and rejection runs. -/
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

private theorem reaches_scan_left_symbol
    {state : Nat} {symbol : ValidatorBlockSymbol}
    (hlookup :
      blockDescription.lookup state symbol =
        some
          { source := state
            read := symbol
            write := symbol
            move := Direction.left
            target := state })
    (count : Nat) (before processed : Word ValidatorBlockSymbol)
    (boundary : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state
          (List.append (List.append before [boundary])
            (List.replicate count symbol))
          (symbol :: processed))
        (configuration state before
          (boundary ::
            List.append (List.replicate (count + 1) symbol) processed)) := by
  apply ValidatorBlockDescription.reaches_of_runConfig
  exact ValidatorBlockDescription.runConfig_scanLeft_replicate
    hlookup rfl rfl rfl count before processed

private theorem reaches_scan_right_symbol
    {state : Nat} {symbol : ValidatorBlockSymbol}
    (hlookup :
      blockDescription.lookup state symbol =
        some
          { source := state
            read := symbol
            write := symbol
            move := Direction.right
            target := state })
    (count : Nat) (processed after : Word ValidatorBlockSymbol)
    (boundary : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state processed
          (symbol ::
            List.append (List.replicate count symbol) (boundary :: after)))
        (configuration state
          (List.append processed (List.replicate (count + 1) symbol))
          (boundary :: after)) := by
  apply ValidatorBlockDescription.reaches_of_runConfig
  exact ValidatorBlockDescription.runConfig_scanRight_replicate
    hlookup rfl rfl rfl count processed after

private theorem reaches_scan_left_ticks
    {state : Nat}
    (hlookup :
      blockDescription.lookup state .tick =
        some
          { source := state
            read := .tick
            write := .tick
            move := Direction.left
            target := state })
    (count : Nat) (before processed : Word ValidatorBlockSymbol)
    (boundary : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state
          (List.append (List.append before [boundary])
            (List.replicate count .tick))
          (.tick :: processed))
        (configuration state before
          (boundary ::
            List.append (List.replicate (count + 1) .tick) processed)) := by
  exact reaches_scan_left_symbol hlookup count before processed boundary

private theorem reaches_scan_right_ticks
    {state : Nat}
    (hlookup :
      blockDescription.lookup state .tick =
        some
          { source := state
            read := .tick
            write := .tick
            move := Direction.right
            target := state })
    (count : Nat) (processed after : Word ValidatorBlockSymbol)
    (boundary : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state processed
          (.tick ::
            List.append (List.replicate count .tick) (boundary :: after)))
        (configuration state
          (List.append processed (List.replicate (count + 1) .tick))
          (boundary :: after)) := by
  exact reaches_scan_right_symbol hlookup count processed after boundary

/-- Cross one symbol left, then scan a homogeneous run to its boundary. -/
theorem reaches_cross_read_scan_left
    {entry scan : Nat}
    {entryRead entryWrite scanSymbol boundary : ValidatorBlockSymbol}
    (hentry :
      blockDescription.lookup entry entryRead =
        some
          { source := entry
            read := entryRead
            write := entryWrite
            move := Direction.left
            target := scan })
    (hscan :
      blockDescription.lookup scan scanSymbol =
        some
          { source := scan
            read := scanSymbol
            write := scanSymbol
            move := Direction.left
            target := scan })
    (count : Nat) (before after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration entry
          (List.append (List.append before [boundary])
            (List.replicate count scanSymbol))
          (entryRead :: after))
        (configuration scan before
          (boundary ::
            List.append (List.replicate count scanSymbol)
              (entryWrite :: after))) := by
  cases count with
  | zero =>
      have hrun := reaches_one_left hentry before after boundary
      simpa [configuration] using hrun
  | succ count =>
      have hfirst := reaches_one_left hentry
        (List.append (List.append before [boundary])
          (List.replicate count scanSymbol))
        after scanSymbol
      have htail := reaches_scan_left_symbol hscan count before
        (entryWrite :: after) boundary
      simpa [configuration, List.replicate_succ', List.append_assoc] using
        hfirst.trans htail

/-- Scan an arbitrary-length homogeneous prefix without crossing its boundary. -/
theorem reaches_scan_right_prefix
    {state : Nat} {symbol boundary : ValidatorBlockSymbol}
    (hscan :
      blockDescription.lookup state symbol =
        some
          { source := state
            read := symbol
            write := symbol
            move := Direction.right
            target := state })
    (count : Nat) (processed after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state processed
          (List.append (List.replicate count symbol) (boundary :: after)))
        (configuration state
          (List.append processed (List.replicate count symbol))
          (boundary :: after)) := by
  cases count with
  | zero =>
      simpa [configuration] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration state processed (boundary :: after))
  | succ count =>
      have hsource :
          (List.append (List.replicate (count + 1) symbol)
              (boundary :: after) : Word ValidatorBlockSymbol) =
            (symbol ::
              List.append (List.replicate count symbol) (boundary :: after) :
              Word ValidatorBlockSymbol) := by
        rfl
      rw [hsource]
      exact reaches_scan_right_symbol hscan count processed after boundary

theorem reaches_scan_right_tail
    {state : Nat} {symbol : ValidatorBlockSymbol}
    (hscan :
      blockDescription.lookup state symbol =
        some
          { source := state
            read := symbol
            write := symbol
            move := Direction.right
            target := state })
    (count : Nat) (processed tail : Word ValidatorBlockSymbol)
    (htail : tail ≠ []) :
    blockDescription.Reaches
        (configuration state processed
          (List.append (List.replicate count symbol) tail))
        (configuration state
          (List.append processed (List.replicate count symbol)) tail) := by
  change List ValidatorBlockSymbol at tail
  cases tail with
  | nil =>
      exact False.elim (htail rfl)
  | cons boundary after =>
      exact reaches_scan_right_prefix hscan count processed after

private theorem reaches_rewrite_right_prefix
    {state : Nat} {read write boundary : ValidatorBlockSymbol}
    (hlookup :
      blockDescription.lookup state read =
        some
          { source := state
            read := read
            write := write
            move := Direction.right
            target := state })
    (count : Nat) (processed after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration state processed
          (List.append (List.replicate count read) (boundary :: after)))
        (configuration state
          (List.append processed (List.replicate count write))
          (boundary :: after)) := by
  cases count with
  | zero =>
      simpa [configuration] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration state processed (boundary :: after))
  | succ count =>
      have hsource :
          (List.append (List.replicate (count + 1) read)
              (boundary :: after) : Word ValidatorBlockSymbol) =
            (read ::
              List.append (List.replicate count read) (boundary :: after) :
              Word ValidatorBlockSymbol) := by
        rfl
      rw [hsource]
      apply ValidatorBlockDescription.reaches_of_runConfig
      exact ValidatorBlockDescription.runConfig_rewriteRight_replicate
        hlookup rfl rfl rfl count processed after

/-- Cross a field terminator, then scan the preceding unary field to its boundary. -/
theorem reaches_cross_done_scan_left
    {entry scan : Nat}
    (hdone :
      blockDescription.lookup entry .done =
        some
          { source := entry
            read := .done
            write := .done
            move := Direction.left
            target := scan })
    (htick :
      blockDescription.lookup scan .tick =
        some
          { source := scan
            read := .tick
            write := .tick
            move := Direction.left
            target := scan })
    (count : Nat) (before after : Word ValidatorBlockSymbol)
    (boundary : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration entry
          (List.append (List.append before [boundary])
            (List.replicate count .tick))
          (.done :: after))
        (configuration scan before
          (boundary ::
            List.append (List.replicate count .tick) (.done :: after))) := by
  exact reaches_cross_read_scan_left hdone htick count before after

/-- Enter a right-terminated unary field, scan it left, and cross its boundary. -/
private theorem reaches_left_over_tick_field
    {entry scan target : Nat}
    (hentry :
      blockDescription.lookup entry .done =
        some
          { source := entry
            read := .done
            write := .done
            move := Direction.left
            target := scan })
    (htick :
      blockDescription.lookup scan .tick =
        some
          { source := scan
            read := .tick
            write := .tick
            move := Direction.left
            target := scan })
    (hdone :
      blockDescription.lookup scan .done =
        some
          { source := scan
            read := .done
            write := .done
            move := Direction.left
            target := target })
    (count : Nat) (earlier after : Word ValidatorBlockSymbol)
    (previous : ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration entry
          (List.append
            (List.append (List.append earlier [previous]) [.done])
            (List.replicate count .tick))
          (.done :: after))
        (configuration target earlier
          (previous :: .done ::
            List.append (List.replicate count .tick) (.done :: after))) := by
  cases count with
  | zero =>
      have hfirst := reaches_one_left hentry
        (List.append earlier [previous]) after .done
      have hsecond := reaches_one_left hdone earlier (.done :: after) previous
      simpa [configuration] using hfirst.trans hsecond
  | succ count =>
      have hfirst := reaches_one_left hentry
        (List.append
          (List.append (List.append earlier [previous]) [.done])
          (List.replicate count .tick))
        after .tick
      have hscan := reaches_scan_left_ticks htick count
        (List.append earlier [previous]) (.done :: after) .done
      have hlast := reaches_one_left hdone earlier
        (List.append (List.replicate (count + 1) .tick) (.done :: after))
        previous
      simpa [configuration, List.replicate_succ', List.append_assoc] using
        hfirst.trans (hscan.trans hlast)

/-- Scan a unary field rightward and cross its terminating token. -/
theorem reaches_right_over_tick_field
    {scan target : Nat}
    (htick :
      blockDescription.lookup scan .tick =
        some
          { source := scan
            read := .tick
            write := .tick
            move := Direction.right
            target := scan })
    (hdone :
      blockDescription.lookup scan .done =
        some
          { source := scan
            read := .done
            write := .done
            move := Direction.right
            target := target })
    (count : Nat) (processed after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration scan processed
          (List.append (List.replicate count .tick) (.done :: after)))
        (configuration target
          (List.append processed (natBlocks count)) after) := by
  cases count with
  | zero =>
      have hrun := reaches_one_right hdone processed after
      simpa [configuration, natBlocks] using hrun
  | succ count =>
      have hsource :
          (List.append
              (List.replicate (count + 1) ValidatorBlockSymbol.tick)
              (ValidatorBlockSymbol.done :: after) :
            Word ValidatorBlockSymbol) =
            (ValidatorBlockSymbol.tick ::
              List.append
                (List.replicate count ValidatorBlockSymbol.tick)
                (ValidatorBlockSymbol.done :: after) :
              Word ValidatorBlockSymbol) := by
        rfl
      rw [hsource]
      have hscan := reaches_scan_right_ticks htick count processed after .done
      have hdoneRun := reaches_one_right hdone
        (List.append processed (List.replicate (count + 1) .tick)) after
      simpa [configuration, natBlocks, List.append_assoc] using
        hscan.trans hdoneRun

/-!
## Header location and positivity
-/

/-- Reach the start-bound comparison after checking positive state count. -/
theorem reaches_start_comparison_entry
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (hpositive : 0 < stateCount) :
    blockDescription.Reaches
        (logicalStartConfig
          stateCount start halt transitionCount tokens)
        (configuration 6
          (List.append [.header] (natBlocks stateCount))
          (List.append (List.replicate start .tick)
            (.done ::
              List.append (List.replicate halt .tick)
                (.done ::
                  List.append (List.replicate transitionCount .tick)
                    (.done :: validatorCanonicalBlocks tokens))))) := by
  let code := validatorCanonicalBlocks tokens
  let beforeHaltDone : Word ValidatorBlockSymbol :=
    .header ::
      List.append (natBlocks stateCount)
        (List.append (natBlocks start) (List.replicate halt .tick))
  let afterHaltDone : Word ValidatorBlockSymbol :=
    List.append (List.replicate transitionCount .tick) (.done :: code)
  let beforeStartDone : Word ValidatorBlockSymbol :=
    .header ::
      List.append (natBlocks stateCount) (List.replicate start .tick)
  let afterStartDone : Word ValidatorBlockSymbol :=
    List.append (List.replicate halt .tick) (.done :: afterHaltDone)
  let beforeStateDone : Word ValidatorBlockSymbol :=
    .header :: List.replicate stateCount .tick
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
        (logicalStartConfig
          stateCount start halt transitionCount tokens)
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

  have hlocate :
      blockDescription.Reaches
        (logicalStartConfig
          stateCount start halt transitionCount tokens)
        (configuration 3 beforeStateDone (.done :: afterStateDone)) := by
    exact htransitionCount'.trans (hhalt'.trans hstart')

  cases stateCount with
  | zero =>
      simp at hpositive
  | succ remaining =>
      have hboundary := reaches_one_left
        (state := 3) (target := 4) (read := .done) (write := .done)
        (by decide)
        (.header :: List.replicate remaining .tick)
        afterStateDone .tick
      have hfirstTick := reaches_one_right
        (state := 4) (target := 5) (read := .tick) (write := .tick)
        (by decide)
        (.header :: List.replicate remaining .tick)
        (.done :: afterStateDone)
      have hstateDone := reaches_one_right
        (state := 5) (target := 6) (read := .done) (write := .done)
        (by decide)
        (List.append (.header :: List.replicate remaining .tick) [.tick])
        afterStateDone
      have hboundary' :
          blockDescription.Reaches
            (configuration 3 beforeStateDone (.done :: afterStateDone))
            (configuration 4
              (.header :: List.replicate remaining .tick)
              (.tick :: .done :: afterStateDone)) := by
        simpa [beforeStateDone, configuration, List.replicate_succ',
          List.append_assoc] using hboundary
      have hfirstTick' :
          blockDescription.Reaches
            (configuration 4
              (.header :: List.replicate remaining .tick)
              (.tick :: .done :: afterStateDone))
            (configuration 5
              (List.append
                (.header :: List.replicate remaining .tick) [.tick])
              (.done :: afterStateDone)) := by
        exact hfirstTick
      have hstateDone' :
          blockDescription.Reaches
            (configuration 5
              (List.append
                (.header :: List.replicate remaining .tick) [.tick])
              (.done :: afterStateDone))
            (configuration 6
              (List.append
                (List.append
                  (.header :: List.replicate remaining .tick) [.tick])
                [.done])
              afterStateDone) := by
        exact hstateDone
      simpa [beforeStateDone, afterStateDone, afterStartDone, afterHaltDone,
        natBlocks, code,
        configuration, List.replicate_succ', List.append_assoc] using
        hlocate.trans (hboundary'.trans (hfirstTick'.trans hstateDone'))

/-!
## Start/state-count comparison
-/

/-- State-field ticks split into marked and unmarked portions. -/
def markedTicks (unmarked marked : Nat) :
    Word ValidatorBlockSymbol :=
  List.append
    (List.replicate unmarked .tick)
    (List.replicate marked .marker010)

/-- Split a homogeneous run at an additive length boundary. -/
theorem replicate_add_eq_append
    (left right : Nat) (symbol : ValidatorBlockSymbol) :
    List.replicate (left + right) symbol =
      List.append (List.replicate left symbol) (List.replicate right symbol) := by
  induction right with
  | zero =>
      simp
  | succ right ih =>
      simp only [Nat.add_succ, List.replicate_succ', ih]
      exact List.append_assoc
        (List.replicate left symbol) (List.replicate right symbol) [symbol]

/-- Mutable left layout during the start-state comparison. -/
def comparisonStateLeft (unmarked marked : Nat) :
    Word ValidatorBlockSymbol :=
  List.append (.header :: markedTicks unmarked marked) [.done]

/-- Pair one start-state tick with one state-count tick. -/
theorem reaches_pair_start_tick
    (stateRemaining startRemaining marked : Nat)
    (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 6
          (comparisonStateLeft (stateRemaining + 1) marked)
          (List.append (markedTicks (startRemaining + 1) marked)
            (.done :: after)))
        (configuration 6
          (comparisonStateLeft stateRemaining (marked + 1))
          (List.append (markedTicks startRemaining (marked + 1))
            (.done :: after))) := by
  let stateBeforeDone : Word ValidatorBlockSymbol :=
    .header :: markedTicks (stateRemaining + 1) marked
  let stateLeft : Word ValidatorBlockSymbol :=
    List.append stateBeforeDone [.done]
  let startTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate startRemaining .tick)
      (List.append (List.replicate (marked + 1) .marker010)
        (.done :: after))

  let c0 := configuration 6 stateLeft
    (List.append (markedTicks (startRemaining + 1) marked) (.done :: after))
  let c1 := configuration 6
    (List.append stateLeft (List.replicate (startRemaining + 1) .tick))
    (List.append (List.replicate marked .marker010) (.done :: after))
  let c2 := configuration 6
    (List.append
      (List.append stateLeft (List.replicate (startRemaining + 1) .tick))
      (List.replicate marked .marker010))
    (.done :: after)
  let c3 := configuration 7
    (List.append stateLeft (List.replicate startRemaining .tick))
    (.tick ::
      List.append (List.replicate marked .marker010) (.done :: after))
  let c4 := configuration 8 stateBeforeDone (.done :: startTail)
  let c5 := configuration 9
    (.header :: List.replicate stateRemaining .tick)
    (.tick ::
      List.append (List.replicate marked .marker010) (.done :: startTail))
  let c6 := configuration 10
    (List.append
      (.header :: List.replicate stateRemaining .tick) [.marker010])
    (List.append (List.replicate marked .marker010) (.done :: startTail))
  let c7 := configuration 10
    (List.append
      (List.append
        (.header :: List.replicate stateRemaining .tick) [.marker010])
      (List.replicate marked .marker010))
    (.done :: startTail)
  let c8 := configuration 6
    (List.append
      (List.append
        (List.append
          (.header :: List.replicate stateRemaining .tick) [.marker010])
        (List.replicate marked .marker010))
      [.done])
    startTail

  have h6ticks := reaches_scan_right_tail
    (state := 6) (symbol := .tick) (by decide)
    (startRemaining + 1) stateLeft
    (List.append (List.replicate marked .marker010) (.done :: after))
    (by
      intro hempty
      have hlength := congrArg List.length hempty
      simp at hlength)
  have h6markers := reaches_scan_right_prefix
    (state := 6) (symbol := .marker010) (boundary := .done)
    (by decide) marked
    (List.append stateLeft (List.replicate (startRemaining + 1) .tick))
    after
  have h7 := reaches_cross_read_scan_left
    (entry := 6) (scan := 7)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .tick)
    (by decide) (by decide) marked
    (List.append stateLeft (List.replicate startRemaining .tick)) after
  have h8 := reaches_cross_read_scan_left
    (entry := 7) (scan := 8)
    (entryRead := .tick) (entryWrite := .marker010)
    (scanSymbol := .tick) (boundary := .done)
    (by decide) (by decide) startRemaining
    stateBeforeDone
    (List.append (List.replicate marked .marker010) (.done :: after))
  have h9 := reaches_cross_read_scan_left
    (entry := 8) (scan := 9)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .tick)
    (by decide) (by decide) marked
    (.header :: List.replicate stateRemaining .tick) startTail
  have h9write := reaches_one_right
    (state := 9) (target := 10)
    (read := .tick) (write := .marker010)
    (by decide)
    (.header :: List.replicate stateRemaining .tick)
    (List.append (List.replicate marked .marker010) (.done :: startTail))
  have h10markers := reaches_scan_right_prefix
    (state := 10) (symbol := .marker010) (boundary := .done)
    (by decide) marked
    (List.append
      (.header :: List.replicate stateRemaining .tick) [.marker010])
    startTail
  have h10done := reaches_one_right
    (state := 10) (target := 6)
    (read := .done) (write := .done)
    (by decide)
    (List.append
      (List.append
        (.header :: List.replicate stateRemaining .tick) [.marker010])
      (List.replicate marked .marker010))
    startTail

  have hstateTickRight :
      List.replicate (stateRemaining + 1) ValidatorBlockSymbol.tick =
        List.append
          (List.replicate stateRemaining ValidatorBlockSymbol.tick) [.tick] := by
    exact List.replicate_succ'
  have hstartTickRight :
      List.replicate (startRemaining + 1) ValidatorBlockSymbol.tick =
        List.append
          (List.replicate startRemaining ValidatorBlockSymbol.tick) [.tick] := by
    exact List.replicate_succ'
  have hmarkerFront :
      List.replicate (marked + 1) ValidatorBlockSymbol.marker010 =
        .marker010 ::
          List.replicate marked ValidatorBlockSymbol.marker010 := by
    rfl

  have h01 : blockDescription.Reaches c0 c1 := by
    simpa [c0, c1, markedTicks, configuration, List.append_assoc] using h6ticks
  have h12 : blockDescription.Reaches c1 c2 := by
    exact h6markers
  have h23 : blockDescription.Reaches c2 c3 := by
    simpa [c2, c3, configuration, List.replicate_succ',
      List.append_assoc] using h7
  have h34 : blockDescription.Reaches c3 c4 := by
    simpa [c3, c4, stateLeft, stateBeforeDone, startTail, configuration,
      hmarkerFront, List.append_assoc] using h8
  have h45 : blockDescription.Reaches c4 c5 := by
    simpa [c4, c5, stateBeforeDone, markedTicks, configuration,
      hstateTickRight, List.append_assoc] using h9
  have h56 : blockDescription.Reaches c5 c6 := by
    exact h9write
  have h67 : blockDescription.Reaches c6 c7 := by
    exact h10markers
  have h78 : blockDescription.Reaches c7 c8 := by
    exact h10done
  have hrun := h01.trans (h12.trans (h23.trans (h34.trans
    (h45.trans (h56.trans (h67.trans h78))))))
  simpa [c0, c8, stateLeft, stateBeforeDone, startTail,
    comparisonStateLeft, markedTicks, configuration,
    hstateTickRight, hstartTickRight, hmarkerFront,
    List.append_assoc] using hrun

private theorem reaches_pair_all_start_ticks
    (stateRemainder count marked : Nat)
    (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 6
          (comparisonStateLeft (stateRemainder + count) marked)
          (List.append (markedTicks count marked) (.done :: after)))
        (configuration 6
          (comparisonStateLeft stateRemainder (marked + count))
          (List.append (markedTicks 0 (marked + count)) (.done :: after))) := by
  induction count generalizing marked with
  | zero =>
      simpa [configuration] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration 6
            (comparisonStateLeft (stateRemainder + 0) marked)
            (List.append (markedTicks 0 marked) (.done :: after)))
  | succ count ih =>
      have hpair := reaches_pair_start_tick
        (stateRemainder + count) count marked after
      have htail := ih (marked + 1)
      have hstate :
          stateRemainder + (count + 1) =
            (stateRemainder + count) + 1 := by
        lia
      have hmarked :
          marked + (count + 1) = (marked + 1) + count := by
        lia
      simpa [hstate, hmarked] using hpair.trans htail

/-- Restored state/start prefix handed to the halt comparison. -/
def restoredStartLeft (stateCount start : Nat) :
    Word ValidatorBlockSymbol :=
  .header :: List.append (natBlocks stateCount) (natBlocks start)

private theorem reaches_finish_start_comparison
    (extra paired : Nat) (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 6
          (comparisonStateLeft (extra + 1) paired)
          (List.append (markedTicks 0 paired) (.done :: after)))
        (configuration 16
          (restoredStartLeft ((extra + 1) + paired) paired) after) := by
  let stateBeforeDone : Word ValidatorBlockSymbol :=
    .header :: markedTicks (extra + 1) paired
  let stateLeft : Word ValidatorBlockSymbol :=
    List.append stateBeforeDone [.done]
  let startMarkers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let pairedTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate paired .marker010)
      (.done ::
        List.append (List.replicate paired .marker010) (.done :: after))
  let stateTicksLeft : Word ValidatorBlockSymbol :=
    List.append [.header] (List.replicate (extra + 1) .tick)
  let restoredStateLeft : Word ValidatorBlockSymbol :=
    List.append stateTicksLeft (List.replicate paired .tick)

  let c0 := configuration 6 stateLeft
    (List.append startMarkers (.done :: after))
  let c1 := configuration 6
    (List.append stateLeft startMarkers) (.done :: after)
  let c2 := configuration 7 stateBeforeDone
    (.done :: List.append startMarkers (.done :: after))
  let c3 := configuration 12
    (.header :: List.replicate extra .tick) (.tick :: pairedTail)
  let c4 := configuration 13 []
    (.header :: List.append (List.replicate (extra + 1) .tick) pairedTail)
  let c5 := configuration 14 [.header]
    (List.append (List.replicate (extra + 1) .tick) pairedTail)
  let c6 := configuration 14 stateTicksLeft
    (List.append (List.replicate paired .marker010)
      (.done :: List.append startMarkers (.done :: after)))
  let c7 := configuration 14 restoredStateLeft
    (.done :: List.append startMarkers (.done :: after))
  let c8 := configuration 15
    (List.append restoredStateLeft [.done])
    (List.append startMarkers (.done :: after))
  let c9 := configuration 15
    (List.append
      (List.append restoredStateLeft [.done])
      (List.replicate paired .tick))
    (.done :: after)
  let c10 := configuration 16
    (List.append
      (List.append
        (List.append restoredStateLeft [.done])
        (List.replicate paired .tick))
      [.done])
    after

  have h6markers := reaches_scan_right_prefix
    (state := 6) (symbol := .marker010) (boundary := .done)
    (by decide) paired stateLeft after
  have h7 := reaches_cross_read_scan_left
    (entry := 6) (scan := 7)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .done)
    (by decide) (by decide) paired stateBeforeDone
    after
  have h12 := reaches_cross_read_scan_left
    (entry := 7) (scan := 12)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .tick)
    (by decide) (by decide) paired
    (.header :: List.replicate extra .tick)
    (List.append startMarkers (.done :: after))
  have h13 := reaches_cross_read_scan_left
    (entry := 12) (scan := 13)
    (entryRead := .tick) (entryWrite := .tick)
    (scanSymbol := .tick) (boundary := .header)
    (by decide) (by decide) extra []
    (List.append (List.replicate paired .marker010)
      (.done :: List.append startMarkers (.done :: after)))
  have h14 := reaches_one_right
    (state := 13) (target := 14)
    (read := .header) (write := .header)
    (by decide) []
    (List.append (List.replicate (extra + 1) .tick) pairedTail)
  have h14ticks := reaches_scan_right_tail
    (state := 14) (symbol := .tick) (by decide)
    (extra + 1) [.header] pairedTail
    (by
      intro hempty
      have hlength := congrArg List.length hempty
      simp [pairedTail] at hlength)
  have h14restore := reaches_rewrite_right_prefix
    (state := 14) (read := .marker010) (write := .tick)
    (boundary := .done) (by decide) paired stateTicksLeft
    (List.append startMarkers (.done :: after))
  have h15 := reaches_one_right
    (state := 14) (target := 15)
    (read := .done) (write := .done)
    (by decide) restoredStateLeft
    (List.append startMarkers (.done :: after))
  have h15restore := reaches_rewrite_right_prefix
    (state := 15) (read := .marker010) (write := .tick)
    (boundary := .done) (by decide) paired
    (List.append restoredStateLeft [.done]) after
  have h16 := reaches_one_right
    (state := 15) (target := 16)
    (read := .done) (write := .done)
    (by decide)
    (List.append
      (List.append restoredStateLeft [.done])
      (List.replicate paired .tick))
    after

  have h01 : blockDescription.Reaches c0 c1 := by
    simpa [c0, c1, startMarkers, configuration] using h6markers
  have h12' : blockDescription.Reaches c1 c2 := by
    simpa [c1, c2, stateLeft, configuration, List.append_assoc] using h7
  have h23 : blockDescription.Reaches c2 c3 := by
    simpa [c2, c3, stateBeforeDone, markedTicks, pairedTail,
      startMarkers, configuration, List.replicate_succ',
      List.append_assoc] using h12
  have h34 : blockDescription.Reaches c3 c4 := by
    simpa [c3, c4, pairedTail, startMarkers, configuration,
      List.replicate_succ', List.append_assoc] using h13
  have h45 : blockDescription.Reaches c4 c5 := by
    exact h14
  have h56 : blockDescription.Reaches c5 c6 := by
    simpa [c5, c6, stateTicksLeft, pairedTail, startMarkers,
      configuration, List.append_assoc] using h14ticks
  have h67 : blockDescription.Reaches c6 c7 := by
    simpa [c6, c7, restoredStateLeft, startMarkers,
      configuration, List.append_assoc] using h14restore
  have h78 : blockDescription.Reaches c7 c8 := by
    exact h15
  have h89 : blockDescription.Reaches c8 c9 := by
    simpa [c8, c9, startMarkers, configuration,
      List.append_assoc] using h15restore
  have h910 : blockDescription.Reaches c9 c10 := by
    exact h16
  have hrun := h01.trans (h12'.trans (h23.trans (h34.trans
    (h45.trans (h56.trans (h67.trans (h78.trans (h89.trans h910))))))))
  simpa [c0, c10, stateLeft, stateBeforeDone, startMarkers,
    stateTicksLeft, restoredStateLeft, comparisonStateLeft, markedTicks,
    restoredStartLeft, natBlocks, configuration,
    List.append_assoc] using hrun

/-- Complete successful start-state bound comparison from its entry. -/
theorem reaches_start_bound_from_entry
    (stateCount start : Nat) (after : Word ValidatorBlockSymbol)
    (hbound : start < stateCount) :
    blockDescription.Reaches
        (configuration 6
          (List.append [.header] (natBlocks stateCount))
          (List.append (List.replicate start .tick) (.done :: after)))
        (configuration 16 (restoredStartLeft stateCount start) after) := by
  let extra := stateCount - (start + 1)
  have hdecomp : stateCount = (extra + 1) + start := by
    dsimp [extra]
    lia
  have hpairs := reaches_pair_all_start_ticks
    (extra + 1) start 0 after
  have hfinish := reaches_finish_start_comparison extra start after
  have hpairs' :
      blockDescription.Reaches
        (configuration 6
          (List.append [.header] (natBlocks stateCount))
          (List.append (List.replicate start .tick) (.done :: after)))
        (configuration 6
          (comparisonStateLeft (extra + 1) start)
          (List.append (markedTicks 0 start) (.done :: after))) := by
    simpa [hdecomp, comparisonStateLeft, markedTicks, natBlocks,
      configuration, List.append_assoc] using hpairs
  have hfinish' :
      blockDescription.Reaches
        (configuration 6
          (comparisonStateLeft (extra + 1) start)
          (List.append (markedTicks 0 start) (.done :: after)))
        (configuration 16 (restoredStartLeft stateCount start) after) := by
    simpa [hdecomp] using hfinish
  exact hpairs'.trans hfinish'

/-!
## Halt/state-count comparison
-/

/-- Mutable left layout during the halt-state comparison. -/
def comparisonHaltLeft
    (stateUnmarked stateMarked start : Nat) :
    Word ValidatorBlockSymbol :=
  .header ::
    List.append (markedTicks stateUnmarked stateMarked)
      (.done :: natBlocks start)

private def haltPairStateTail
    (marked start haltRemaining : Nat)
    (after : Word ValidatorBlockSymbol) : Word ValidatorBlockSymbol :=
  .tick ::
    List.append (List.replicate marked .marker010)
      (.done ::
        List.append (List.replicate start .tick)
          (.done ::
            List.append (markedTicks haltRemaining (marked + 1))
              (.done :: after)))

private theorem reaches_halt_pair_to_state_tick
    (stateRemaining haltRemaining marked start : Nat)
    (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 16
          (comparisonHaltLeft (stateRemaining + 1) marked start)
          (List.append (markedTicks (haltRemaining + 1) marked)
            (.done :: after)))
        (configuration 20
          (.header :: List.replicate stateRemaining .tick)
          (haltPairStateTail marked start haltRemaining after)) := by
  let stateBeforeDone : Word ValidatorBlockSymbol :=
    .header :: markedTicks (stateRemaining + 1) marked
  let stateDoneLeft : Word ValidatorBlockSymbol :=
    List.append stateBeforeDone [.done]
  let startBeforeDone : Word ValidatorBlockSymbol :=
    List.append stateDoneLeft (List.replicate start .tick)
  let startLeft : Word ValidatorBlockSymbol :=
    List.append startBeforeDone [.done]
  let haltTail : Word ValidatorBlockSymbol :=
    List.append (markedTicks haltRemaining (marked + 1)) (.done :: after)
  let startAndHaltTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate start .tick) (.done :: haltTail)

  have h16ticks := reaches_scan_right_tail
    (state := 16) (symbol := .tick) (by decide)
    (haltRemaining + 1) startLeft
    (List.append (List.replicate marked .marker010) (.done :: after))
    (by
      intro hempty
      have hlength := congrArg List.length hempty
      simp at hlength)
  have h16markers := reaches_scan_right_prefix
    (state := 16) (symbol := .marker010) (boundary := .done)
    (by decide) marked
    (List.append startLeft (List.replicate (haltRemaining + 1) .tick))
    after
  have h17 := reaches_cross_read_scan_left
    (entry := 16) (scan := 17)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .tick)
    (by decide) (by decide) marked
    (List.append startLeft (List.replicate haltRemaining .tick)) after
  have h18 := reaches_cross_read_scan_left
    (entry := 17) (scan := 18)
    (entryRead := .tick) (entryWrite := .marker010)
    (scanSymbol := .tick) (boundary := .done)
    (by decide) (by decide) haltRemaining startBeforeDone
    (List.append (List.replicate marked .marker010) (.done :: after))
  have h19 := reaches_cross_read_scan_left
    (entry := 18) (scan := 19)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .tick) (boundary := .done)
    (by decide) (by decide) start stateBeforeDone haltTail
  have h20 := reaches_cross_read_scan_left
    (entry := 19) (scan := 20)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .tick)
    (by decide) (by decide) marked
    (.header :: List.replicate stateRemaining .tick) startAndHaltTail

  have hhaltTickRight :
      List.replicate (haltRemaining + 1) ValidatorBlockSymbol.tick =
        List.append
          (List.replicate haltRemaining ValidatorBlockSymbol.tick) [.tick] := by
    exact List.replicate_succ'
  have hstateTickRight :
      List.replicate (stateRemaining + 1) ValidatorBlockSymbol.tick =
        List.append
          (List.replicate stateRemaining ValidatorBlockSymbol.tick) [.tick] := by
    exact List.replicate_succ'
  have hmarkerFront :
      List.replicate (marked + 1) ValidatorBlockSymbol.marker010 =
        .marker010 ::
          List.replicate marked ValidatorBlockSymbol.marker010 := by
    rfl
  have h01 := h16ticks.trans h16markers
  have h17' :
      blockDescription.Reaches
        (configuration 16
          (List.append
            (List.append startLeft
              (List.replicate (haltRemaining + 1) .tick))
            (List.replicate marked .marker010))
          (.done :: after))
        (configuration 17
          (List.append startLeft (List.replicate haltRemaining .tick))
          (.tick ::
            List.append (List.replicate marked .marker010) (.done :: after))) := by
    simpa [hhaltTickRight, List.append_assoc] using h17
  have h18' :
      blockDescription.Reaches
        (configuration 17
          (List.append startLeft (List.replicate haltRemaining .tick))
          (.tick ::
            List.append (List.replicate marked .marker010) (.done :: after)))
        (configuration 18 startBeforeDone (.done :: haltTail)) := by
    simpa [startLeft, haltTail, markedTicks, hmarkerFront,
      List.append_assoc] using h18
  have h19' :
      blockDescription.Reaches
        (configuration 18 startBeforeDone (.done :: haltTail))
        (configuration 19 stateBeforeDone (.done :: startAndHaltTail)) := by
    simpa [startBeforeDone, stateDoneLeft, startAndHaltTail,
      List.append_assoc] using h19
  have h20' :
      blockDescription.Reaches
        (configuration 19 stateBeforeDone (.done :: startAndHaltTail))
        (configuration 20
          (.header :: List.replicate stateRemaining .tick)
          (haltPairStateTail marked start haltRemaining after)) := by
    simpa [stateBeforeDone, markedTicks, haltPairStateTail,
      startAndHaltTail, haltTail, hstateTickRight, hmarkerFront,
      List.append_assoc] using h20
  have hrun := h01.trans (h17'.trans (h18'.trans (h19'.trans h20')))
  simpa [stateBeforeDone, stateDoneLeft, startBeforeDone, startLeft,
    haltTail, startAndHaltTail, comparisonHaltLeft, markedTicks,
    haltPairStateTail, natBlocks, configuration, hhaltTickRight,
    hstateTickRight, hmarkerFront,
    List.append_assoc] using hrun

private theorem reaches_halt_pair_from_state_tick
    (stateRemaining haltRemaining marked start : Nat)
    (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 20
          (.header :: List.replicate stateRemaining .tick)
          (haltPairStateTail marked start haltRemaining after))
        (configuration 16
          (comparisonHaltLeft stateRemaining (marked + 1) start)
          (List.append (markedTicks haltRemaining (marked + 1))
            (.done :: after))) := by
  let haltTail : Word ValidatorBlockSymbol :=
    List.append (markedTicks haltRemaining (marked + 1)) (.done :: after)
  let returnTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate start .tick) (.done :: haltTail)
  let markedStateBeforeDone : Word ValidatorBlockSymbol :=
    List.append
      (List.append
        (.header :: List.replicate stateRemaining .tick) [.marker010])
      (List.replicate marked .marker010)
  let markedStateLeft : Word ValidatorBlockSymbol :=
    List.append markedStateBeforeDone [.done]

  have h20write := reaches_one_right
    (state := 20) (target := 21)
    (read := .tick) (write := .marker010)
    (by decide)
    (.header :: List.replicate stateRemaining .tick)
    (List.append (List.replicate marked .marker010)
      (.done :: returnTail))
  have h21markers := reaches_scan_right_prefix
    (state := 21) (symbol := .marker010) (boundary := .done)
    (by decide) marked
    (List.append
      (.header :: List.replicate stateRemaining .tick) [.marker010])
    returnTail
  have h23 := reaches_one_right
    (state := 21) (target := 23)
    (read := .done) (write := .done)
    (by decide) markedStateBeforeDone returnTail
  have h16return := reaches_right_over_tick_field
    (scan := 23) (target := 16) (by decide) (by decide)
    start markedStateLeft haltTail

  have hmarkerFront :
      List.replicate (marked + 1) ValidatorBlockSymbol.marker010 =
        .marker010 ::
          List.replicate marked ValidatorBlockSymbol.marker010 := by
    rfl
  have hrun := h20write.trans (h21markers.trans (h23.trans h16return))
  simpa [haltPairStateTail, haltTail, returnTail,
    markedStateBeforeDone, markedStateLeft, comparisonHaltLeft,
    markedTicks, natBlocks, configuration, hmarkerFront,
    List.append_assoc] using hrun

/-- Pair one halt-state tick with one state-count tick. -/
theorem reaches_pair_halt_tick
    (stateRemaining haltRemaining marked start : Nat)
    (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 16
          (comparisonHaltLeft (stateRemaining + 1) marked start)
          (List.append (markedTicks (haltRemaining + 1) marked)
            (.done :: after)))
        (configuration 16
          (comparisonHaltLeft stateRemaining (marked + 1) start)
          (List.append (markedTicks haltRemaining (marked + 1))
            (.done :: after))) := by
  exact (reaches_halt_pair_to_state_tick
    stateRemaining haltRemaining marked start after).trans
      (reaches_halt_pair_from_state_tick
        stateRemaining haltRemaining marked start after)

private theorem reaches_pair_all_halt_ticks
    (stateRemainder count marked start : Nat)
    (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 16
          (comparisonHaltLeft (stateRemainder + count) marked start)
          (List.append (markedTicks count marked) (.done :: after)))
        (configuration 16
          (comparisonHaltLeft stateRemainder (marked + count) start)
          (List.append (markedTicks 0 (marked + count)) (.done :: after))) := by
  induction count generalizing marked with
  | zero =>
      simpa [configuration] using
        ValidatorBlockDescription.reaches_refl blockDescription
          (configuration 16
            (comparisonHaltLeft (stateRemainder + 0) marked start)
            (List.append (markedTicks 0 marked) (.done :: after)))
  | succ count ih =>
      have hpair := reaches_pair_halt_tick
        (stateRemainder + count) count marked start after
      have htail := ih (marked + 1)
      have hstate :
          stateRemainder + (count + 1) =
            (stateRemainder + count) + 1 := by
        lia
      have hmarked :
          marked + (count + 1) = (marked + 1) + count := by
        lia
      simpa [hstate, hmarked] using hpair.trans htail

private def haltFinishStateTail
    (paired start : Nat) (after : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  .tick ::
    List.append (List.replicate paired .marker010)
      (.done ::
        List.append (List.replicate start .tick)
          (.done ::
            List.append (List.replicate paired .marker010)
              (.done :: after)))

private theorem reaches_halt_finish_to_extra_tick
    (extra paired start : Nat) (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 16
          (comparisonHaltLeft (extra + 1) paired start)
          (List.append (markedTicks 0 paired) (.done :: after)))
        (configuration 24
          (.header :: List.replicate extra .tick)
          (haltFinishStateTail paired start after)) := by
  let stateBeforeDone : Word ValidatorBlockSymbol :=
    .header :: markedTicks (extra + 1) paired
  let stateDoneLeft : Word ValidatorBlockSymbol :=
    List.append stateBeforeDone [.done]
  let startBeforeDone : Word ValidatorBlockSymbol :=
    List.append stateDoneLeft (List.replicate start .tick)
  let startLeft : Word ValidatorBlockSymbol :=
    List.append startBeforeDone [.done]
  let haltMarkers : Word ValidatorBlockSymbol :=
    List.replicate paired .marker010
  let haltTail : Word ValidatorBlockSymbol :=
    List.append haltMarkers (.done :: after)
  let startAndHaltTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate start .tick) (.done :: haltTail)

  have h16markers := reaches_scan_right_prefix
    (state := 16) (symbol := .marker010) (boundary := .done)
    (by decide) paired startLeft after
  have h17 := reaches_cross_read_scan_left
    (entry := 16) (scan := 17)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .done)
    (by decide) (by decide) paired startBeforeDone after
  have h22 := reaches_cross_read_scan_left
    (entry := 17) (scan := 22)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .tick) (boundary := .done)
    (by decide) (by decide) start stateBeforeDone haltTail
  have h24 := reaches_cross_read_scan_left
    (entry := 22) (scan := 24)
    (entryRead := .done) (entryWrite := .done)
    (scanSymbol := .marker010) (boundary := .tick)
    (by decide) (by decide) paired
    (.header :: List.replicate extra .tick) startAndHaltTail

  have hstateTickRight :
      List.replicate (extra + 1) ValidatorBlockSymbol.tick =
        List.append (List.replicate extra ValidatorBlockSymbol.tick) [.tick] := by
    exact List.replicate_succ'
  have h24' :
      blockDescription.Reaches
        (configuration 22 stateBeforeDone (.done :: startAndHaltTail))
        (configuration 24
          (.header :: List.replicate extra .tick)
          (haltFinishStateTail paired start after)) := by
    simpa [stateBeforeDone, markedTicks, haltFinishStateTail,
      startAndHaltTail, haltTail, haltMarkers, hstateTickRight,
      List.append_assoc] using h24
  have hrun := h16markers.trans (h17.trans (h22.trans h24'))
  simpa [stateBeforeDone, stateDoneLeft, startBeforeDone, startLeft,
    haltMarkers, haltTail, startAndHaltTail, comparisonHaltLeft,
    haltFinishStateTail, markedTicks, natBlocks, configuration,
    hstateTickRight, List.append_assoc] using hrun

/-- Restored state/start/halt prefix before the transition-count field. -/
def restoredHaltLeft
    (stateCount start halt : Nat) : Word ValidatorBlockSymbol :=
  .header ::
    List.append (natBlocks stateCount)
      (List.append (natBlocks start) (natBlocks halt))

private theorem reaches_restore_halt_fields
    (extra paired start : Nat) (after : Word ValidatorBlockSymbol) :
    blockDescription.Reaches
        (configuration 24
          (.header :: List.replicate extra .tick)
          (haltFinishStateTail paired start after))
        (configuration 29
          (restoredHaltLeft ((extra + 1) + paired) start paired) after) := by
  let stateMarkerTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate paired .marker010)
      (.done ::
        List.append (List.replicate start .tick)
          (.done ::
            List.append (List.replicate paired .marker010) (.done :: after)))
  let stateTicksLeft : Word ValidatorBlockSymbol :=
    List.append [.header] (List.replicate (extra + 1) .tick)
  let restoredStateLeft : Word ValidatorBlockSymbol :=
    List.append stateTicksLeft (List.replicate paired .tick)
  let startTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate start .tick)
      (.done ::
        List.append (List.replicate paired .marker010) (.done :: after))
  let haltMarkerTail : Word ValidatorBlockSymbol :=
    List.append (List.replicate paired .marker010) (.done :: after)

  have h25 := reaches_cross_read_scan_left
    (entry := 24) (scan := 25)
    (entryRead := .tick) (entryWrite := .tick)
    (scanSymbol := .tick) (boundary := .header)
    (by decide) (by decide) extra [] stateMarkerTail
  have h26 := reaches_one_right
    (state := 25) (target := 26)
    (read := .header) (write := .header)
    (by decide) []
    (List.append (List.replicate (extra + 1) .tick) stateMarkerTail)
  have h26ticks := reaches_scan_right_tail
    (state := 26) (symbol := .tick) (by decide)
    (extra + 1) [.header] stateMarkerTail
    (by
      intro hempty
      have hlength := congrArg List.length hempty
      simp [stateMarkerTail] at hlength)
  have h26restore := reaches_rewrite_right_prefix
    (state := 26) (read := .marker010) (write := .tick)
    (boundary := .done) (by decide) paired stateTicksLeft startTail
  have h27 := reaches_one_right
    (state := 26) (target := 27)
    (read := .done) (write := .done)
    (by decide) restoredStateLeft startTail
  have h28 := reaches_right_over_tick_field
    (scan := 27) (target := 28) (by decide) (by decide)
    start (List.append restoredStateLeft [.done]) haltMarkerTail
  have h28restore := reaches_rewrite_right_prefix
    (state := 28) (read := .marker010) (write := .tick)
    (boundary := .done) (by decide) paired
    (List.append
      (List.append (List.append restoredStateLeft [.done])
        (List.replicate start .tick))
      [.done])
    after
  have h29 := reaches_one_right
    (state := 28) (target := 29)
    (read := .done) (write := .done)
    (by decide)
    (List.append
      (List.append
        (List.append
          (List.append restoredStateLeft [.done])
          (List.replicate start .tick))
        [.done])
      (List.replicate paired .tick))
    after

  have hextraTickRight :
      List.replicate (extra + 1) ValidatorBlockSymbol.tick =
        List.append (List.replicate extra ValidatorBlockSymbol.tick) [.tick] := by
    exact List.replicate_succ'
  have h26' :
      blockDescription.Reaches
        (configuration 25 []
          (.header ::
            List.append (List.replicate extra .tick)
              (.tick :: stateMarkerTail)))
        (configuration 26 [.header]
          (List.append (List.replicate (extra + 1) .tick)
            stateMarkerTail)) := by
    simpa [hextraTickRight, List.append_assoc] using h26
  have h28' :
      blockDescription.Reaches
        (configuration 27 (List.append restoredStateLeft [.done]) startTail)
        (configuration 28
          (List.append
            (List.append (List.append restoredStateLeft [.done])
              (List.replicate start .tick))
            [.done])
          haltMarkerTail) := by
    simpa [startTail, haltMarkerTail, natBlocks, List.append_assoc] using h28
  have hrun := h25.trans (h26'.trans (h26ticks.trans
    (h26restore.trans (h27.trans (h28'.trans (h28restore.trans h29))))))
  simpa [stateMarkerTail, stateTicksLeft, restoredStateLeft, startTail,
    haltMarkerTail, haltFinishStateTail, restoredHaltLeft, natBlocks,
    configuration, replicate_add_eq_append, List.replicate_succ',
    List.append_assoc] using hrun

/-- Complete successful halt-state bound comparison from its entry. -/
theorem reaches_halt_bound_from_entry
    (stateCount start halt : Nat) (after : Word ValidatorBlockSymbol)
    (hbound : halt < stateCount) :
    blockDescription.Reaches
        (configuration 16 (restoredStartLeft stateCount start)
          (List.append (List.replicate halt .tick) (.done :: after)))
        (configuration 29 (restoredHaltLeft stateCount start halt) after) := by
  let extra := stateCount - (halt + 1)
  have hdecomp : stateCount = (extra + 1) + halt := by
    dsimp [extra]
    lia
  have hpairs := reaches_pair_all_halt_ticks
    (extra + 1) halt 0 start after
  have hextra := reaches_halt_finish_to_extra_tick
    extra halt start after
  have hrestore := reaches_restore_halt_fields extra halt start after
  have hpairs' :
      blockDescription.Reaches
        (configuration 16 (restoredStartLeft stateCount start)
          (List.append (List.replicate halt .tick) (.done :: after)))
        (configuration 16
          (comparisonHaltLeft (extra + 1) halt start)
          (List.append (markedTicks 0 halt) (.done :: after))) := by
    simpa [hdecomp, restoredStartLeft, comparisonHaltLeft,
      markedTicks, natBlocks, configuration, List.append_assoc] using hpairs
  have hrestore' :
      blockDescription.Reaches
        (configuration 24
          (.header :: List.replicate extra .tick)
          (haltFinishStateTail halt start after))
        (configuration 29 (restoredHaltLeft stateCount start halt) after) := by
    simpa [hdecomp] using hrestore
  exact hpairs'.trans (hextra.trans hrestore')


end ValidatorHeaderBounds
end SelfHaltingRecognizer
end Computability
end FoC
