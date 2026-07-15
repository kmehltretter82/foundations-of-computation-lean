import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpoint.CloseoutPrefixRuns

/-! Copy, finish, and assembly runs for the direct joined-output closeout. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf

open CommonGround.FiniteTransducers

namespace DirectJoinedCloseout

open Structured.MultiTapeLowering.ThreeTape


theorem lookup40_false
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some false) :
    description.lookupTransition (config 40 source scratch work) =
      some (row 40 (some false) (Tape.read scratch) (Tape.read work)
        keepR (writeBitR true) (writeBitR false) 40) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 40
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_same, allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource, hscratch, hwork]

theorem lookup40_true
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some true) :
    description.lookupTransition (config 40 source scratch work) =
      some (row 40 (some true) (Tape.read scratch) (Tape.read work)
        keepR (writeBitR true) (writeBitR true) 40) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 40
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_same, allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource, hscratch, hwork]

theorem lookup40_none
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = none) :
    description.lookupTransition (config 40 source scratch work) =
      some (row 40 none (Tape.read scratch) (Tape.read work)
        keepS keepL keepL 41) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 40
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_same, allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource, hscratch, hwork]

theorem lookup41_true
    (source scratch work : Tape Bool)
    (hscratch : Tape.read scratch = some true) :
    description.lookupTransition (config 41 source scratch work) =
      some (row 41 (Tape.read source) (some true) (Tape.read work)
        keepS eraseL keepS 42) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 41
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hsource : Tape.read source <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_same, allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource, hscratch, hwork]

theorem lookup42_true
    (source scratch work : Tape Bool)
    (hscratch : Tape.read scratch = some true) :
    description.lookupTransition (config 42 source scratch work) =
      some (row 42 (Tape.read source) (some true) (Tape.read work)
        keepS eraseL keepL 42) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 42
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hsource : Tape.read source <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_same, allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource, hscratch, hwork]

theorem lookup42_none
    (source scratch work : Tape Bool)
    (hscratch : Tape.read scratch = none) :
    description.lookupTransition (config 42 source scratch work) =
      some (row 42 (Tape.read source) none (Tape.read work)
        keepS keepS keepS 43) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 42
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hsource : Tape.read source <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_same, allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource, hscratch, hwork]

theorem run40_bit
    (bit : Bool) (leftRev : List (Option Bool)) (tail : Word Bool)
    (scratch work : Tape Bool) :
    description.runConfig 1
        (config 40 (cursorTape leftRev (bit :: tail)) scratch work) =
      config 40 (cursorTape (some bit :: leftRev) tail)
        ((writeBitR true).apply scratch)
        ((writeBitR bit).apply work) := by
  simp only [Structured.Description.runConfig]
  cases bit
  · rw [Structured.Description.stepConfig,
      lookup40_false _ _ _ (by simp [cursorTape, tapeAtCells, Tape.read])]
    cases tail <;> three_tape_step [description, cursorTape]
  · rw [Structured.Description.stepConfig,
      lookup40_true _ _ _ (by simp [cursorTape, tapeAtCells, Tape.read])]
    cases tail <;> three_tape_step [description, cursorTape]

theorem run40_done
    (leftRev : List (Option Bool)) (scratch work : Tape Bool) :
    description.runConfig 1
        (config 40 (cursorTape leftRev []) scratch work) =
      config 41 (cursorTape leftRev [])
        (Tape.move Direction.left scratch)
        (Tape.move Direction.left work) := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    lookup40_none _ _ _ (by simp [cursorTape, tapeAtCells, Tape.read])]
  three_tape_step [description]

theorem run41_true
    (source scratch work : Tape Bool)
    (hscratch : Tape.read scratch = some true) :
    description.runConfig 1 (config 41 source scratch work) =
      config 42 source (eraseL.apply scratch) work := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    lookup41_true _ _ _ hscratch]
  three_tape_step [description]

theorem run42_true
    (source scratch work : Tape Bool)
    (hscratch : Tape.read scratch = some true) :
    description.runConfig 1 (config 42 source scratch work) =
      config 42 source (eraseL.apply scratch)
        (Tape.move Direction.left work) := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    lookup42_true _ _ _ hscratch]
  three_tape_step [description]

theorem run42_done
    (source scratch work : Tape Bool)
    (hscratch : Tape.read scratch = none) :
    description.runConfig 1 (config 42 source scratch work) =
      config 43 source scratch work := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    lookup42_none _ _ _ hscratch]
  three_tape_step [description]

theorem writeBitR_apply_tapeAtCells
    (bit : Bool) (left cells : List (Option Bool)) :
    (writeBitR bit).apply (tapeAtCells left cells) =
      tapeAtCells (some bit :: left) (cells.drop 1) := by
  cases cells with
  | nil => rfl
  | cons head tail =>
      cases tail <;> rfl

theorem writeBitR_apply_outputFromBits
    (bit : Bool) (bits : Word Bool) :
    (writeBitR bit).apply (outputFromBits bits) =
      outputFromBits (List.append bits [bit]) := by
  simp [writeBitR, writeR, Structured.TapeAction.apply,
    Structured.HeadMove.apply, Tape.write, Tape.move, Tape.moveRight,
    outputFromBits, List.reverse_append, List.map_append]

theorem run_copy_bits
    (leftRev scratchLeft scratchCells : List (Option Bool))
    (bits outputPrefix : Word Bool) :
    description.runConfig bits.length
        (config 40 (cursorTape leftRev bits)
          (tapeAtCells scratchLeft scratchCells)
          (outputFromBits outputPrefix)) =
      config 40
        (cursorTape
          (List.append (bits.reverse.map some) leftRev) [])
        (tapeAtCells
          (List.append
            (List.replicate bits.length (some true)) scratchLeft)
          (scratchCells.drop bits.length))
        (outputFromBits (List.append outputPrefix bits)) := by
  induction bits generalizing leftRev scratchLeft scratchCells outputPrefix with
  | nil =>
      simp [Structured.Description.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [Structured.Description.runConfig_add]
      rw [run40_bit]
      rw [writeBitR_apply_tapeAtCells]
      rw [writeBitR_apply_outputFromBits]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc,
        List.replicate_succ, List.drop_drop, Nat.add_comm,
        list_replicate_append_cons_eq_cons_append]

def moveLeftN : Nat → Tape Bool → Tape Bool
  | 0, tape => tape
  | n + 1, tape => moveLeftN n (Tape.move Direction.left tape)

theorem eraseL_apply_tapeAtCells_true
    (cell : Option Bool) (left right : List (Option Bool)) :
    eraseL.apply (tapeAtCells (cell :: left) (some true :: right)) =
      tapeAtCells left (cell :: none :: right) := by
  rfl

theorem run42_markers
    (markers : Nat) (baseLeft right : List (Option Bool))
    (source work : Tape Bool) :
    description.runConfig (markers + 2)
        (config 42 source
          (tapeAtCells
            (List.append (List.replicate markers (some true))
              (none :: baseLeft))
            (some true :: right))
          work) =
      config 43 source
        (tapeAtCells baseLeft
          (none ::
            List.append (List.replicate (markers + 1) none) right))
        (moveLeftN (markers + 1) work) := by
  induction markers generalizing right work with
  | zero =>
      rw [show 0 + 2 = 1 + 1 by rfl,
        Structured.Description.runConfig_add]
      rw [run42_true _ _ _
        (by simp [tapeAtCells, Tape.read])]
      rw [show List.append (List.replicate 0 (some true))
          (none :: baseLeft) = none :: baseLeft by rfl]
      rw [eraseL_apply_tapeAtCells_true]
      rw [run42_done _ _ _
        (by simp [tapeAtCells, Tape.read])]
      rfl
  | succ markers ih =>
      rw [show (markers + 1) + 2 = 1 + (markers + 2) by lia,
        Structured.Description.runConfig_add]
      rw [run42_true _ _ _
        (by simp [tapeAtCells, Tape.read])]
      have hleft :
          List.append (List.replicate (markers + 1) (some true))
              (none :: baseLeft) =
            some true ::
              List.append (List.replicate markers (some true))
                (none :: baseLeft) := by
        simp [List.replicate_succ]
      rw [hleft]
      rw [eraseL_apply_tapeAtCells_true]
      rw [ih]
      simp [moveLeftN, List.replicate_succ,
        list_replicate_append_cons_eq_cons_append, Nat.add_assoc]

theorem run41_markers
    (markers : Nat) (baseLeft right : List (Option Bool))
    (source work : Tape Bool) :
    description.runConfig (markers + 3)
        (config 41 source
          (tapeAtCells
            (List.append (List.replicate (markers + 1) (some true))
              (none :: baseLeft))
            (some true :: right))
          work) =
      config 43 source
        (tapeAtCells baseLeft
          (none ::
            List.append (List.replicate (markers + 1) none)
              (none :: right)))
        (moveLeftN (markers + 1) work) := by
  rw [show markers + 3 = 1 + (markers + 2) by lia,
    Structured.Description.runConfig_add]
  rw [run41_true _ _ _
    (by simp [tapeAtCells, Tape.read])]
  have hleft :
      List.append (List.replicate (markers + 1) (some true))
          (none :: baseLeft) =
        some true ::
          List.append (List.replicate markers (some true))
            (none :: baseLeft) := by
    simp [List.replicate_succ]
  rw [hleft]
  rw [eraseL_apply_tapeAtCells_true]
  rw [run42_markers markers baseLeft (none :: right)]

theorem run_finish_markerBlock
    (markers : Nat) (baseLeft leftRev : List (Option Bool))
    (work : Tape Bool) :
    description.runConfig (markers + 4)
        (config 40 (cursorTape leftRev [])
          (tapeAtCells
            (List.append (List.replicate (markers + 2) (some true))
              (none :: baseLeft))
            [])
          work) =
      config 43 (cursorTape leftRev [])
        (tapeAtCells baseLeft
          (none ::
            List.append (List.replicate (markers + 1) none)
              [none, none]))
        (moveLeftN (markers + 2) work) := by
  rw [show markers + 4 = 1 + (markers + 3) by lia,
    Structured.Description.runConfig_add]
  rw [run40_done]
  have hscratch :
      Tape.move Direction.left
          (tapeAtCells
            (List.append (List.replicate (markers + 2) (some true))
              (none :: baseLeft))
            []) =
        tapeAtCells
          (List.append (List.replicate (markers + 1) (some true))
            (none :: baseLeft))
          [some true, none] := by
    simp [List.replicate_succ, tapeAtCells, Tape.move, Tape.moveLeft]
  rw [hscratch]
  rw [run41_markers markers baseLeft [none]]
  rfl

def representedCells : List (Option Bool) → List (Option Bool)
  | [] => [none]
  | cells => cells

theorem run_finish_markerBlock_cells
    (markers : Nat) (baseLeft scratchCells : List (Option Bool))
    (leftRev : List (Option Bool)) (work : Tape Bool) :
    description.runConfig (markers + 4)
        (config 40 (cursorTape leftRev [])
          (tapeAtCells
            (List.append (List.replicate (markers + 2) (some true))
              (none :: baseLeft))
            scratchCells)
          work) =
      config 43 (cursorTape leftRev [])
        (tapeAtCells baseLeft
          (none ::
            List.append (List.replicate (markers + 1) none)
              (none :: representedCells scratchCells)))
        (moveLeftN (markers + 2) work) := by
  rw [show markers + 4 = 1 + (markers + 3) by lia,
    Structured.Description.runConfig_add]
  rw [run40_done]
  have hscratch :
      Tape.move Direction.left
          (tapeAtCells
            (List.append (List.replicate (markers + 2) (some true))
              (none :: baseLeft))
            scratchCells) =
        tapeAtCells
          (List.append (List.replicate (markers + 1) (some true))
            (none :: baseLeft))
          (some true :: representedCells scratchCells) := by
    cases scratchCells <;>
      simp [List.replicate_succ, representedCells, tapeAtCells,
        Tape.move, Tape.moveLeft]
  rw [hscratch]
  rw [run41_markers markers baseLeft (representedCells scratchCells)]
  rfl

theorem moveLeftN_tapeAtCells_all_left
    (left cells : List (Option Bool)) :
    moveLeftN left.length (tapeAtCells left cells) =
      tapeAtCells []
        (List.append left.reverse (representedCells cells)) := by
  induction left generalizing cells with
  | nil =>
      cases cells <;> rfl
  | cons cell left ih =>
      rw [List.length_cons]
      unfold moveLeftN
      have hstep :
          Tape.move Direction.left
              (tapeAtCells (cell :: left) cells) =
            tapeAtCells left (cell :: representedCells cells) := by
        cases cells <;> rfl
      rw [hstep, ih]
      simp [representedCells, List.reverse_cons, List.append_assoc]

def paddedWordTape (bits : Word Bool) : Tape Bool :=
  tapeAtCells [] (List.append (bits.map some) [none])

theorem moveLeftN_outputFromBits
    (bits : Word Bool) :
    moveLeftN bits.length (outputFromBits bits) =
      paddedWordTape bits := by
  change List Bool at bits
  change
    moveLeftN bits.length (tapeAtCells (bits.reverse.map some) []) =
      tapeAtCells [] (List.append (bits.map some) [none])
  simpa [representedCells, List.map_reverse] using
    moveLeftN_tapeAtCells_all_left
      (bits.reverse.map some) ([] : List (Option Bool))

theorem paddedWordTape_equiv_input
    (bits : Word Bool) :
    Tape.Equiv (paddedWordTape bits) (Tape.input bits) := by
  cases bits with
  | nil =>
      simp [paddedWordTape, tapeAtCells, Tape.input, Tape.blank,
        Tape.Equiv, Tape.dropTrailingNone]
  | cons bit rest =>
      simp [paddedWordTape, tapeAtCells, Tape.input,
        Tape.Equiv, Tape.dropTrailingNone, List.map_append,
        FoC.Computability.dropTrailingNone_append_none]

theorem run_copy_finish
    (markers : Nat) (baseLeft leftRev scratchCells : List (Option Bool))
    (bits outputPrefix : Word Bool)
    (houtputLength : outputPrefix.length = markers + 2)
    (hscratchCovered : scratchCells.length ≤ bits.length) :
    description.runConfig
        (bits.length + ((bits.length + markers) + 4))
        (config 40 (cursorTape leftRev bits)
          (tapeAtCells
            (List.append (List.replicate (markers + 2) (some true))
              (none :: baseLeft))
            scratchCells)
          (outputFromBits outputPrefix)) =
      config 43
        (cursorTape
          (List.append (bits.reverse.map some) leftRev) [])
        (tapeAtCells baseLeft
          (none ::
            List.append
              (List.replicate (bits.length + markers + 1) none)
              [none, none]))
        (paddedWordTape (List.append outputPrefix bits)) := by
  rw [Structured.Description.runConfig_add]
  rw [run_copy_bits]
  have hdrop : scratchCells.drop bits.length = [] := by
    exact List.drop_eq_nil_of_le hscratchCovered
  rw [hdrop]
  have hmarkers :
      List.append (List.replicate bits.length (some true))
          (List.append (List.replicate (markers + 2) (some true))
            (none :: baseLeft)) =
        List.append
          (List.replicate ((bits.length + markers) + 2) (some true))
          (none :: baseLeft) := by
    rw [show (bits.length + markers) + 2 =
      bits.length + (markers + 2) by lia]
    exact
      (list_replicate_add_append (some true : Option Bool)
        bits.length (markers + 2) (none :: baseLeft)).symm
  rw [hmarkers]
  rw [run_finish_markerBlock (bits.length + markers)]
  have htotal :
      (bits.length + markers) + 2 =
        (List.append outputPrefix bits).length := by
    simp [houtputLength]
    lia
  have hwork :
      moveLeftN ((bits.length + markers) + 2)
          (outputFromBits (List.append outputPrefix bits)) =
        paddedWordTape (List.append outputPrefix bits) := by
    rw [htotal, moveLeftN_outputFromBits]
  rw [hwork]

theorem run_copy_finish_cells
    (markers : Nat) (baseLeft leftRev scratchCells : List (Option Bool))
    (bits outputPrefix : Word Bool)
    (houtputLength : outputPrefix.length = markers + 2) :
    description.runConfig
        (bits.length + ((bits.length + markers) + 4))
        (config 40 (cursorTape leftRev bits)
          (tapeAtCells
            (List.append (List.replicate (markers + 2) (some true))
              (none :: baseLeft))
            scratchCells)
          (outputFromBits outputPrefix)) =
      config 43
        (cursorTape
          (List.append (bits.reverse.map some) leftRev) [])
        (tapeAtCells baseLeft
          (none ::
            List.append
              (List.replicate (bits.length + markers + 1) none)
              (none :: representedCells (scratchCells.drop bits.length))))
        (paddedWordTape (List.append outputPrefix bits)) := by
  rw [Structured.Description.runConfig_add]
  rw [run_copy_bits]
  have hmarkers :
      List.append (List.replicate bits.length (some true))
          (List.append (List.replicate (markers + 2) (some true))
            (none :: baseLeft)) =
        List.append
          (List.replicate ((bits.length + markers) + 2) (some true))
          (none :: baseLeft) := by
    rw [show (bits.length + markers) + 2 =
      bits.length + (markers + 2) by lia]
    exact
      (list_replicate_add_append (some true : Option Bool)
        bits.length (markers + 2) (none :: baseLeft)).symm
  rw [hmarkers]
  rw [run_finish_markerBlock_cells (bits.length + markers)]
  have htotal :
      (bits.length + markers) + 2 =
        (List.append outputPrefix bits).length := by
    simp [houtputLength]
    lia
  have hwork :
      moveLeftN ((bits.length + markers) + 2)
          (outputFromBits (List.append outputPrefix bits)) =
        paddedWordTape (List.append outputPrefix bits) := by
    rw [htotal, moveLeftN_outputFromBits]
  rw [hwork]

def quoteScanFuel : Word Bool → Nat
  | [] => 2
  | _ :: rest => 8 * rest.length + 12

def quoteScanScratchCells : Word Bool → List (Option Bool)
  | [] => [none, none]
  | _ :: rest =>
      none :: List.append (List.replicate rest.length none) [none, none]

theorem run_quoteScan_to_copy
    (w rawTail : Word Bool) (leftRev prefixLeft : List (Option Bool))
    (work : Tape Bool) :
    description.runConfig (quoteScanFuel w)
        (config 27
          (cursorTape leftRev
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                w)
              rawTail))
          (parserMarkerBuildTape 0 prefixLeft)
          work) =
      config 40
        (cursorTape
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              w).reverse.map some)
            leftRev)
          rawTail)
        (tapeAtCells prefixLeft (quoteScanScratchCells w))
        work := by
  cases w with
  | nil =>
      simpa [quoteScanFuel, quoteScanScratchCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix,
        parserMarkerBuildTape, tapeAtCells, Tape.move, Tape.moveLeft] using
        run_empty_quote_prefix leftRev rawTail prefixLeft [] work
  | cons bit rest =>
      change Word Bool at rest
      rw [show quoteScanFuel (bit :: rest) =
          2 + ((4 * rest.length + 4) +
            (1 + (4 + (4 * rest.length + 1)))) by
        simp [quoteScanFuel]
        lia]
      rw [Structured.Description.runConfig_add]
      have hsource :
          List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                (bit :: rest))
              rawTail =
            List.append ([true, false] : Word Bool)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  rest.length)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits bit)
                  (List.append
                    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits rest)
                    rawTail))) := by
        simp [
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix,
          List.append_assoc]
      rw [hsource]
      rw [run_nonempty_quote_dispatch]
      rw [Structured.Description.runConfig_add]
      rw [run_stageNatBits]
      rw [Structured.Description.runConfig_add]
      rw [run_begin_cell_skip]
      rw [Structured.Description.runConfig_add]
      rw [run_skip_cellBits]
      rw [Structured.Description.runConfig_add]
      simp only [Nat.zero_add]
      rw [run_skip_cellsBits (bits := rest) (tail := rawTail)]
      rw [run_cell_skip_done]
      have hleft :
          List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                rest).reverse.map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  bit).reverse.map some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    rest.length).reverse.map some)
                  (some false :: some true :: leftRev))) =
            List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                (bit :: rest)).reverse.map some)
              leftRev := by
        simp [
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix,
          List.reverse_append, List.map_append, List.append_assoc]
      have hscratch :
          skipCounterTape 0 prefixLeft
              (List.append (List.replicate rest.length none) [none, none]) =
            tapeAtCells prefixLeft (quoteScanScratchCells (bit :: rest)) := by
        simp [skipCounterTape, quoteScanScratchCells]
      rw [hleft, hscratch]

theorem run_prefix_parse_copy_finish
    (markers : Nat) (baseLeft leftRev : List (Option Bool))
    (w rawTail outputPrefix : Word Bool)
    (houtputLength : outputPrefix.length = markers + 2) :
    description.runConfig
        (6 + (quoteScanFuel w +
          (rawTail.length + ((rawTail.length + markers) + 4))))
        (config 21
          (cursorTape leftRev
            (List.append fixedSourcePrefix
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                  w)
                rawTail)))
          (Tape.move Direction.right
            (markerBuildTape (markers + 2) (none :: baseLeft)))
          (outputFromBits outputPrefix)) =
      config 43
        (cursorTape
          (List.append
            ((List.append fixedSourcePrefix
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                  w)
                rawTail)).reverse.map some)
            leftRev)
          [])
        (tapeAtCells baseLeft
          (none ::
            List.append
              (List.replicate (rawTail.length + markers + 1) none)
              (none :: representedCells
                ((quoteScanScratchCells w).drop rawTail.length))))
        (paddedWordTape (List.append outputPrefix rawTail)) := by
  rw [show 6 + (quoteScanFuel w +
      (rawTail.length + ((rawTail.length + markers) + 4))) =
    6 + (quoteScanFuel w +
      (rawTail.length + ((rawTail.length + markers) + 4))) by rfl]
  rw [Structured.Description.runConfig_add]
  rw [run_skip_fixed_source_prefix]
  have hscratch :
      Tape.move Direction.right
          (markerBuildTape (markers + 2) (none :: baseLeft)) =
        parserMarkerBuildTape 0
          (List.append (List.replicate (markers + 2) (some true))
            (none :: baseLeft)) := by
    simp [markerBuildTape, parserMarkerBuildTape, tapeAtCells,
      Tape.move, Tape.moveRight]
  rw [hscratch]
  rw [Structured.Description.runConfig_add]
  rw [run_quoteScan_to_copy]
  rw [run_copy_finish_cells markers (houtputLength := houtputLength)]
  have hleft :
      List.append (rawTail.reverse.map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              w).reverse.map some)
            (List.append (fixedSourcePrefix.reverse.map some) leftRev)) =
        List.append
          ((List.append fixedSourcePrefix
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                w)
              rawTail)).reverse.map some)
          leftRev := by
    simp [List.reverse_append, List.map_append, List.append_assoc]
  rw [hleft]

def closeoutFuel
    (sourceInitLength sourceLength : Nat) (w rawTail : Word Bool) : Nat :=
  (sourceInitLength + 3) +
    ((8 * sourceLength) +
      (1 +
        (9 +
          ((sourceInitLength + 2) +
            (6 +
              (quoteScanFuel w +
                (rawTail.length +
                  ((rawTail.length + (8 * sourceLength + 6)) + 4))))))))

theorem run_full_closeout
    (sourceBits sourceInit w rawTail outputPrefix : Word Bool)
    (last : Bool)
    (hsourceLast : sourceBits = List.append sourceInit [last])
    (hsourceShape :
      sourceBits =
        List.append fixedSourcePrefix
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              w)
            rawTail))
    (houtputLength : outputPrefix.length = 8 * sourceBits.length + 8) :
    description.runConfig
        (closeoutFuel sourceInit.length sourceBits.length w rawTail)
        (config 0
          (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
            sourceBits.reverse [])
          (structuredMixedOptionCellQuoteLiveTailRewindScratchTape
            0 sourceBits.length)
          (outputFromBits outputPrefix)) =
      config 43
        (cursorTape
          (List.append
            ((List.append fixedSourcePrefix
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                  w)
                rawTail)).reverse.map some)
            [none])
          [])
        (tapeAtCells
          (List.append (List.replicate sourceBits.length (some true)) [none])
          (none ::
            List.append
              (List.replicate
                (rawTail.length + (8 * sourceBits.length + 6) + 1) none)
              (none :: representedCells
                ((quoteScanScratchCells w).drop rawTail.length))))
        (paddedWordTape (List.append outputPrefix rawTail)) := by
  unfold closeoutFuel
  rw [Structured.Description.runConfig_add]
  have hstart :=
    run_rewind0_to_count sourceInit last
      (structuredMixedOptionCellQuoteLiveTailRewindScratchTape
        0 sourceBits.length)
      (outputFromBits outputPrefix)
  have hstart' :
      description.runConfig (sourceInit.length + 3)
          (config 0
            (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
              sourceBits.reverse [])
            (structuredMixedOptionCellQuoteLiveTailRewindScratchTape
              0 sourceBits.length)
            (outputFromBits outputPrefix)) =
        config 3 (sourceScanTape [] sourceBits)
          (Tape.move Direction.right
            (structuredMixedOptionCellQuoteLiveTailRewindScratchTape
              0 sourceBits.length))
          (outputFromBits outputPrefix) := by
    simpa [hsourceLast, sourceScanTape,
      structuredMixedOptionCellQuoteLiveTailCellPassSourceTape] using hstart
  rw [hstart']
  have hscratch0 :
      Tape.move Direction.right
          (structuredMixedOptionCellQuoteLiveTailRewindScratchTape
            0 sourceBits.length) =
        markerBuildTape 0
          (none ::
            List.append (List.replicate sourceBits.length (some true))
              [none]) := by
    simp [structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
      markerBuildTape, tapeAtCells, Tape.move, Tape.moveRight]
  rw [hscratch0]
  rw [Structured.Description.runConfig_add]
  rw [run_count_source]
  simp only [Nat.zero_add]
  have hcountSource :
      sourceScanTape (List.append sourceBits.reverse []) [] =
        tapeAtCells
          (List.append (sourceBits.reverse.map some) [none]) [none] := by
    simp [sourceScanTape]
  rw [hcountSource]
  rw [Structured.Description.runConfig_add]
  rw [run_count_source_done]
  rw [Structured.Description.runConfig_add]
  rw [run_fixed_prefix_markers]
  have hrewindSource :
      Tape.move Direction.left
          (tapeAtCells
            (List.append (sourceBits.reverse.map some) [none]) [none]) =
        sourceRewindTape sourceInit.reverse last [] := by
    rw [hsourceLast]
    simp [sourceRewindTape, tapeAtCells,
      Tape.move, Tape.moveLeft, List.reverse_append, List.map_reverse]
  rw [hrewindSource]
  rw [Structured.Description.runConfig_add]
  have hrewind :=
    run_rewind20_to_prefix sourceInit last
      (Tape.move Direction.right
        (markerBuildTape (8 * sourceBits.length + 8)
          (none ::
            List.append (List.replicate sourceBits.length (some true))
              [none])))
      (outputFromBits outputPrefix)
  have hrewind' :
      description.runConfig (sourceInit.length + 2)
          (config 20 (sourceRewindTape sourceInit.reverse last [])
            (Tape.move Direction.right
              (markerBuildTape (8 * sourceBits.length + 8)
                (none ::
                  List.append
                    (List.replicate sourceBits.length (some true)) [none])))
            (outputFromBits outputPrefix)) =
        config 21 (sourceScanTape [] sourceBits)
          (Tape.move Direction.right
            (markerBuildTape (8 * sourceBits.length + 8)
              (none ::
                List.append
                  (List.replicate sourceBits.length (some true)) [none])))
          (outputFromBits outputPrefix) := by
    simpa [hsourceLast] using hrewind
  rw [hrewind']
  have hsource21 :
      sourceScanTape [] sourceBits =
        cursorTape [none]
          (List.append fixedSourcePrefix
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                w)
              rawTail)) := by
    rw [hsourceShape]
    simp [sourceScanTape, cursorTape]
  rw [hsource21]
  have hmarkerCount :
      8 * sourceBits.length + 8 =
        (8 * sourceBits.length + 6) + 2 := by
    lia
  rw [hmarkerCount]
  rw [run_prefix_parse_copy_finish (8 * sourceBits.length + 6)]
  congr 3

theorem assemblySourceBits_eq_fixed_quote_raw
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyInputBits p =
      List.append fixedSourcePrefix
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
            p.w)
          (assemblySourceRestLiveTailEmitterRawTail p)) := by
  cases p with
  | mk w sourceRestBits stage =>
      unfold structuredLiveTailEmitterAssemblyInputBits
        assemblySourceRestLiveTailEmitterRawTail
      rw [assemblySourceRestFinishSourceBits,
        DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_eq_prefix_stageNat,
        assemblySourceRestFinishRawTailBits]
      cases w with
      | nil =>
          simp [fixedSourcePrefix,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix,
            encodeCodeSymbolAsInput]
      | cons bit rest =>
          simp [fixedSourcePrefix,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix,
            encodeCodeSymbolAsInput, List.append_assoc]

theorem assemblyOutputPrefix_length
    (p : AssemblySourceRestLiveTailEmitterParam) :
    (structuredLiveTailEmitterAssemblyOutputPrefix p).length =
      8 * (structuredLiveTailEmitterAssemblyInputBits p).length + 8 := by
  cases p with
  | mk w sourceRestBits stage =>
      simp [structuredLiveTailEmitterAssemblyOutputPrefix,
        structuredLiveTailEmitterAssemblyInputBits,
        assemblySourceRestFinishTargetPrefixBits,
        encodeCodeSymbolAsInput_length,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length,
        preservingCellPassCellBits_length]
      lia

def assemblyCloseoutSourceTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  cursorTape
    (List.append
      ((structuredLiveTailEmitterAssemblyInputBits p).reverse.map some)
      [none])
    []

def assemblyCloseoutScratchTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  let sourceBits := structuredLiveTailEmitterAssemblyInputBits p
  let rawTail := assemblySourceRestLiveTailEmitterRawTail p
  tapeAtCells
    (List.append (List.replicate sourceBits.length (some true)) [none])
    (none ::
      List.append
        (List.replicate
          (rawTail.length + (8 * sourceBits.length + 6) + 1) none)
        (none :: representedCells
          ((quoteScanScratchCells p.w).drop rawTail.length)))

def assemblyCloseoutOutputTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  paddedWordTape
    (List.append (structuredLiveTailEmitterAssemblyOutputPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p))

def assemblyCloseoutFinalTapes
    (p : AssemblySourceRestLiveTailEmitterParam) : List (Tape Bool) :=
  [assemblyCloseoutSourceTape p,
    assemblyCloseoutScratchTape p,
    assemblyCloseoutOutputTape p]

theorem description_haltsWithTapes_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    description.HaltsWithTapes
      (config 0
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          (structuredLiveTailEmitterAssemblyInputBits p).reverse [])
        (structuredMixedOptionCellQuoteLiveTailRewindScratchTape
          0 (structuredLiveTailEmitterAssemblyInputBits p).length)
        (outputFromBits
          (structuredLiveTailEmitterAssemblyOutputPrefix p)))
      (assemblyCloseoutFinalTapes p) := by
  have hlastSplit :
      exists sourceInit : Word Bool, exists last : Bool,
        structuredLiveTailEmitterAssemblyInputBits p =
          List.append sourceInit [last] := by
    rcases assemblySourceRestFinishRawTailBits_lastSplit_exists
        p.sourceRestBits p.stage with ⟨rawInit, last, hraw⟩
    refine
      ⟨List.append fixedSourcePrefix
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
            p.w)
          rawInit),
        last, ?_⟩
    rw [assemblySourceBits_eq_fixed_quote_raw]
    have hraw' :
        assemblySourceRestLiveTailEmitterRawTail p =
          List.append rawInit [last] := by
      simpa [assemblySourceRestLiveTailEmitterRawTail] using hraw
    rw [hraw']
    simp [List.append_assoc]
  rcases hlastSplit with
    ⟨sourceInit, last, hlast⟩
  refine
    ⟨closeoutFuel sourceInit.length
      (structuredLiveTailEmitterAssemblyInputBits p).length p.w
      (assemblySourceRestLiveTailEmitterRawTail p), ?_⟩
  have hrun := run_full_closeout
    (structuredLiveTailEmitterAssemblyInputBits p)
    sourceInit p.w
    (assemblySourceRestLiveTailEmitterRawTail p)
    (structuredLiveTailEmitterAssemblyOutputPrefix p)
    last hlast
    (assemblySourceBits_eq_fixed_quote_raw p)
    (assemblyOutputPrefix_length p)
  have hsourceTape :
      cursorTape
          (List.append
            ((List.append fixedSourcePrefix
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                  p.w)
                (assemblySourceRestLiveTailEmitterRawTail p))).reverse.map some)
            [none])
          [] =
        assemblyCloseoutSourceTape p := by
    simp [assemblyCloseoutSourceTape,
      assemblySourceBits_eq_fixed_quote_raw]
  rw [hsourceTape] at hrun
  have hhalt : description.halt = 43 := rfl
  rw [hhalt]
  simpa [assemblyCloseoutFinalTapes, assemblyCloseoutSourceTape,
    assemblyCloseoutScratchTape, assemblyCloseoutOutputTape,
    config] using hrun

theorem description_haltsWithTapes_from_emitterFinal
    (p : AssemblySourceRestLiveTailEmitterParam) :
    description.HaltsWithTapes
      { state := description.start
        tapes := (structuredLiveTailEmitterAssemblyFinalConfig p []).tapes }
      (assemblyCloseoutFinalTapes p) := by
  have hstart : description.start = 0 := rfl
  rw [hstart]
  simpa [config,
    structuredLiveTailEmitterAssemblyFinalConfig,
    structuredLiveTailEmitterAssemblyOutputBits,
    structuredMixedOptionCellQuoteLiveTailOutputTape,
    structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig] using
    description_haltsWithTapes_assembly p

def loweredCloseoutDescription : MachineDescription :=
  Structured.MultiTapeLowering.lowerStructured3Description description

def assemblyCloseoutEncodedFinalTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  Structured.MultiTapeLowering.encodedGuardedStructuredTapes
    (assemblyCloseoutFinalTapes p)

theorem loweredCloseoutDescription_haltsFrom_emitterFinal
    (hwellFormed : description.WellFormed)
    (hhaltFree : description.HaltTransitionFree)
    (hsupported :
      Structured.MultiTapeLowering.SupportsReadWriteRows3 description)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    loweredCloseoutDescription.HaltsFromTapeEquiv
      (structuredLiveTailEmitterAssemblyEncodedFinalTape p)
      (assemblyCloseoutEncodedFinalTape p) := by
  simpa [loweredCloseoutDescription,
    structuredLiveTailEmitterAssemblyEncodedFinalTape,
    assemblyCloseoutEncodedFinalTape] using
    Structured.MultiTapeLowering.lowerStructured3Description_haltsFromConfigWithTapes
      hwellFormed hhaltFree hsupported
      (c :=
        { state := description.start
          tapes :=
            (structuredLiveTailEmitterAssemblyFinalConfig p []).tapes })
      (tapes := assemblyCloseoutFinalTapes p)
      rfl
      (by
        simp [description,
          structuredLiveTailEmitterAssemblyFinalConfig,
          structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig,
          Structured.MultiTapeLowering.ThreeTape.description,
          Structured.MultiTapeLowering.ThreeTape.config])
      (description_haltsWithTapes_from_emitterFinal p)

/-
set_option maxHeartbeats 600000 in
example
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig 6
        (config 21
          (cursorTape leftRev
            (List.append fixedSourcePrefix tail)) tape1 tape2) =
      config 27
        (cursorTape
          (List.append (fixedSourcePrefix.reverse.map some) leftRev)
          tail) tape1 tape2 := by
  rw [show 6 = 3 + 3 by rfl, Structured.Description.runConfig_add]
  have hfirst :
      description.runConfig 3
          (config 21
            (cursorTape leftRev
              (List.append fixedSourcePrefix tail)) tape1 tape2) =
        config 24
          (cursorTape
            (some false :: some false :: some false :: leftRev)
            (List.append ([true, false, false] : Word Bool) tail))
          tape1 tape2 := by
    cases tape1 with
    | mk left1 head1 right1 =>
      cases tape2 with
      | mk left2 head2 right2 =>
        cases head1 <;> (try cases ‹Bool›) <;>
          cases head2 <;> (try cases ‹Bool›) <;>
            three_tape_step [description, rows,
              rowsForTape0Read, rowsForTape1Read, allReadRows3, allReads3,
              allReads2, fixedSourcePrefix, cursorTape, List.find?]
  rw [hfirst]
  cases tail <;>
    cases tape1 with
    | mk left1 head1 right1 =>
      cases tape2 with
      | mk left2 head2 right2 =>
        cases head1 <;> (try cases ‹Bool›) <;>
          cases head2 <;> (try cases ‹Bool›) <;>
            three_tape_step [description, rows,
              rowsForTape0Read, rowsForTape1Read, allReadRows3, allReads3,
              allReads2, fixedSourcePrefix, cursorTape,
              List.find?]
-/

end DirectJoinedCloseout
end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
