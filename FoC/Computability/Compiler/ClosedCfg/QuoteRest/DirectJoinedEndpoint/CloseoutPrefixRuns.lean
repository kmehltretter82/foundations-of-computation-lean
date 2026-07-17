import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpointCore

/-! Prefix parsing runs for the direct joined-output closeout machine. -/

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

/-! Exact copy, rewind, and assembly-level closeout proofs are kept separate
from the initializer and parser implementation. -/

/- Static readiness is checked separately after the execution stack closes.
theorem description_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3 description := by
  exact Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    (by decide)

set_option maxHeartbeats 1000000 in
theorem description_wellFormed : description.WellFormed := by
  exact structuredDescription_wellFormed_of_transition_checks description
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem description_haltTransitionFree : description.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_transition_checks description
    (by decide)

theorem description_subroutineReady : description.SubroutineReady :=
  ⟨description_wellFormed, description_haltTransitionFree⟩
-/

theorem run_count_source
    (processedRev remaining : Word Bool)
    (markers : Nat) (baseLeft : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig (8 * remaining.length)
        (config 3 (sourceScanTape processedRev remaining)
          (markerBuildTape markers baseLeft) tape2) =
      config 3
        (sourceScanTape
          (List.append remaining.reverse processedRev) [])
        (markerBuildTape (markers + 8 * remaining.length) baseLeft)
        tape2 := by
  induction remaining generalizing processedRev markers with
  | nil =>
      simp [Structured.Description.runConfig, sourceScanTape]
  | cons bit rest ih =>
      rw [show 8 * (bit :: rest).length = 8 + 8 * rest.length by
        simp; lia]
      rw [Structured.Description.runConfig_add]
      change description.runConfig (8 * rest.length)
          (description.runConfig 8
            (config 3
              (tapeAtCells
                (List.append (processedRev.map some) [none])
                (some bit ::
                  List.append (rest.map some) [none]))
              (markerBuildTape markers baseLeft) tape2)) = _
      rw [run_count_source_bit]
      have htape :
          Tape.move Direction.right
              (tapeAtCells
                (List.append (processedRev.map some) [none])
                (some bit :: List.append (rest.map some) [none])) =
            sourceScanTape (bit :: processedRev) rest := by
        cases rest <;>
          simp [sourceScanTape, tapeAtCells, Tape.move, Tape.moveRight]
      rw [htape]
      rw [ih]
      have hsource :
          List.append rest.reverse (bit :: processedRev) =
            List.append (bit :: rest).reverse processedRev := by
        simp [List.reverse_cons, List.append_assoc]
      have hmarkers :
          (markers + 8) + 8 * rest.length =
            markers + (8 + 8 * rest.length) := by
        lia
      rw [hsource, hmarkers]

theorem run_count_source_done
    (left baseLeft : List (Option Bool)) (markers : Nat)
    (tape2 : Tape Bool) :
    description.runConfig 1
        (config 3 (tapeAtCells left [none])
          (markerBuildTape markers baseLeft) tape2) =
      config 11 (tapeAtCells left [none])
        (markerBuildTape markers baseLeft) tape2 := by
  cases tape2 with
  | mk left2 head2 right2 =>
    cases head2 <;> (try cases ‹Bool›) <;>
      three_tape_step [description, rows, rowsForTape0Read,
        rowsForTape1Read, allReadRows3, allReads3, allReads2,
        List.find?, markerBuildTape]

theorem run_fixed_prefix_markers
    (left baseLeft : List (Option Bool)) (markers : Nat)
    (tape2 : Tape Bool) :
    description.runConfig 9
        (config 11 (tapeAtCells left [none])
          (markerBuildTape markers baseLeft) tape2) =
      config 20
        (Tape.move Direction.left (tapeAtCells left [none]))
        (Tape.move Direction.right
          (markerBuildTape (markers + 8) baseLeft)) tape2 := by
  have hmarkers4 :
      some true :: some true :: some true :: some true ::
          (List.replicate markers (some true) ++ baseLeft) =
        List.replicate (markers + 4) (some true) ++ baseLeft := by
    rw [show markers + 4 = 4 + markers by lia]
    simpa using (list_replicate_add_append
      (some true : Option Bool) 4 markers baseLeft).symm
  have hmarkers8 :
      some true :: some true :: some true :: some true ::
          (List.replicate (markers + 4) (some true) ++ baseLeft) =
        List.replicate (markers + 8) (some true) ++ baseLeft := by
    rw [show markers + 8 = 4 + (markers + 4) by lia]
    simpa using (list_replicate_add_append
      (some true : Option Bool) 4 (markers + 4) baseLeft).symm
  rw [show 9 = 4 + (4 + 1) by rfl, Structured.Description.runConfig_add]
  have hfirst :
      description.runConfig 4
          (config 11 (tapeAtCells left [none])
            (markerBuildTape markers baseLeft) tape2) =
        config 15 (tapeAtCells left [none])
          (markerBuildTape (markers + 4) baseLeft) tape2 := by
    cases tape2 with
    | mk left2 head2 right2 =>
      cases head2 <;> (try cases ‹Bool›) <;>
        three_tape_step [description, rows, rowsForTape0Read,
          rowsForTape1Read, allReadRows3, allReads3, allReads2,
          List.find?, markerBuildTape, hmarkers4]
  rw [hfirst]
  rw [Structured.Description.runConfig_add]
  have hsecond :
      description.runConfig 4
          (config 15 (tapeAtCells left [none])
            (markerBuildTape (markers + 4) baseLeft) tape2) =
        config 19 (tapeAtCells left [none])
          (markerBuildTape (markers + 8) baseLeft) tape2 := by
    cases tape2 with
    | mk left2 head2 right2 =>
      cases head2 <;> (try cases ‹Bool›) <;>
        three_tape_step [description, rows, rowsForTape0Read,
          rowsForTape1Read, allReadRows3, allReads3, allReads2,
          List.find?, markerBuildTape, hmarkers8]
  rw [hsecond]
  cases tape2 with
  | mk left2 head2 right2 =>
    cases head2 <;> (try cases ‹Bool›) <;>
      three_tape_step [description, rows, rowsForTape0Read,
        rowsForTape1Read, allReadRows3, allReads3, allReads2,
        List.find?, markerBuildTape]

theorem lookup21
    (source scratch work : Tape Bool) :
    description.lookupTransition (config 21 source scratch work) =
      some (row 21 (Tape.read source) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 22) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 21
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
    allReadRows3_find?_same, allReadRows3_find?_other,
    row, Structured.Description.Matches]

theorem lookup22
    (source scratch work : Tape Bool) :
    description.lookupTransition (config 22 source scratch work) =
      some (row 22 (Tape.read source) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 23) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 22
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
    allReadRows3_find?_same, allReadRows3_find?_other,
    row, Structured.Description.Matches]

theorem lookup23
    (source scratch work : Tape Bool) :
    description.lookupTransition (config 23 source scratch work) =
      some (row 23 (Tape.read source) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 24) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 23
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
    allReadRows3_find?_same, allReadRows3_find?_other,
    row, Structured.Description.Matches]

theorem lookup24
    (source scratch work : Tape Bool) :
    description.lookupTransition (config 24 source scratch work) =
      some (row 24 (Tape.read source) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 25) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 24
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
    allReadRows3_find?_same, allReadRows3_find?_other,
    row, Structured.Description.Matches]

theorem lookup25
    (source scratch work : Tape Bool) :
    description.lookupTransition (config 25 source scratch work) =
      some (row 25 (Tape.read source) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 26) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 25
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
    allReadRows3_find?_same, allReadRows3_find?_other,
    row, Structured.Description.Matches]

theorem lookup26
    (source scratch work : Tape Bool) :
    description.lookupTransition (config 26 source scratch work) =
      some (row 26 (Tape.read source) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 27) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 26
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
    allReadRows3_find?_same, allReadRows3_find?_other,
    row, Structured.Description.Matches]

theorem run_keepR_of_lookup
    (state target : Nat)
    (hlookup : ∀ source scratch work,
      description.lookupTransition (config state source scratch work) =
        some (row state (Tape.read source) (Tape.read scratch)
          (Tape.read work) keepR keepS keepS target))
    (leftRev : List (Option Bool)) (bit : Bool) (tail : Word Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig 1
        (config state (cursorTape leftRev (bit :: tail)) tape1 tape2) =
      config target (cursorTape (some bit :: leftRev) tail) tape1 tape2 := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig, hlookup]
  cases tail <;> cases bit <;>
    three_tape_step [description, cursorTape]

theorem run_skip_fixed_source_prefix
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
  simp only [fixedSourcePrefix, List.append, List.reverse]
  rw [show 6 = 1 + 5 by rfl, Structured.Description.runConfig_add]
  rw [run_keepR_of_lookup 21 22 lookup21]
  rw [show 5 = 1 + 4 by rfl, Structured.Description.runConfig_add]
  rw [run_keepR_of_lookup 22 23 lookup22]
  rw [show 4 = 1 + 3 by rfl, Structured.Description.runConfig_add]
  rw [run_keepR_of_lookup 23 24 lookup23]
  rw [show 3 = 1 + 2 by rfl, Structured.Description.runConfig_add]
  rw [run_keepR_of_lookup 24 25 lookup24]
  rw [show 2 = 1 + 1 by rfl, Structured.Description.runConfig_add]
  rw [run_keepR_of_lookup 25 26 lookup25]
  rw [run_keepR_of_lookup 26 27 lookup26]
  simp

theorem lookup27_true
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some true) :
    description.lookupTransition (config 27 source scratch work) =
      some (row 27 (some true) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 28) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 27
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource]

theorem lookup28_true
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some true) :
    description.lookupTransition (config 28 source scratch work) =
      some (row 28 (some true) (Tape.read scratch) (Tape.read work)
        keepR keepL keepS 40) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 28
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource]

theorem lookup28_false
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some false) :
    description.lookupTransition (config 28 source scratch work) =
      some (row 28 (some false) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 29) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 28
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource]

theorem run27_true
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig 1
        (config 27 (cursorTape leftRev (true :: tail)) tape1 tape2) =
      config 28 (cursorTape (some true :: leftRev) tail) tape1 tape2 := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    lookup27_true _ _ _ (by simp [cursorTape, tapeAtCells, Tape.read])]
  cases tail <;>
    three_tape_step [description, cursorTape]

theorem run28_true
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig 1
        (config 28 (cursorTape leftRev (true :: tail)) tape1 tape2) =
      config 40 (cursorTape (some true :: leftRev) tail)
        (Tape.move Direction.left tape1) tape2 := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    lookup28_true _ _ _ (by simp [cursorTape, tapeAtCells, Tape.read])]
  cases tail <;>
    three_tape_step [description, cursorTape]

theorem run28_false
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig 1
        (config 28 (cursorTape leftRev (false :: tail)) tape1 tape2) =
      config 29 (cursorTape (some false :: leftRev) tail) tape1 tape2 := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    lookup28_false _ _ _ (by simp [cursorTape, tapeAtCells, Tape.read])]
  cases tail <;>
    three_tape_step [description, cursorTape]

theorem run_empty_quote_prefix
    (leftRev : List (Option Bool)) (rawTail : Word Bool)
    (prefixLeft rightPadding : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig 2
        (config 27
          (cursorTape leftRev
            (List.append ([true, true] : Word Bool) rawTail))
          (tapeAtCells (none :: prefixLeft) rightPadding) tape2) =
      config 40
        (cursorTape
          (some true :: some true :: leftRev) rawTail)
        (Tape.move Direction.left
          (tapeAtCells (none :: prefixLeft) rightPadding)) tape2 := by
  simp only [List.append]
  rw [show 2 = 1 + 1 by rfl, Structured.Description.runConfig_add]
  rw [run27_true]
  rw [run28_true]

theorem run_nonempty_quote_dispatch
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (prefixLeft : List (Option Bool)) (tape2 : Tape Bool) :
    description.runConfig 2
        (config 27
          (cursorTape leftRev
            (List.append ([true, false] : Word Bool) tail))
          (parserMarkerBuildTape 0 prefixLeft) tape2) =
      config 29
        (cursorTape (some false :: some true :: leftRev) tail)
        (parserMarkerBuildTape 0 prefixLeft) tape2 := by
  simp only [List.append]
  rw [show 2 = 1 + 1 by rfl, Structured.Description.runConfig_add]
  rw [run27_true]
  rw [run28_false]

theorem lookup29_false
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some false) :
    description.lookupTransition (config 29 source scratch work) =
      some (row 29 (some false) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 30) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 29
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource]

theorem lookup30_false
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some false) :
    description.lookupTransition (config 30 source scratch work) =
      some (row 30 (some false) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 31) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 30
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource]

theorem lookup31_true
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some true) :
    description.lookupTransition (config 31 source scratch work) =
      some (row 31 (some true) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 32) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 31
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource]

theorem lookup32_false
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some false) :
    description.lookupTransition (config 32 source scratch work) =
      some (row 32 (some false) (Tape.read scratch) (Tape.read work)
        keepR (writeBitR false) keepS 29) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 32
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource]

theorem lookup32_true
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some true) :
    description.lookupTransition (config 32 source scratch work) =
      some (row 32 (some true) (Tape.read scratch) (Tape.read work)
        keepR (writeBitR false) keepS 33) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 32
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hscratch : Tape.read scratch <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_other,
        row, Structured.Description.Matches, hsource]

theorem run_read_keepR_of_lookup
    (state target : Nat) (bit : Bool)
    (hlookup : ∀ source scratch work,
      Tape.read source = some bit ->
      description.lookupTransition (config state source scratch work) =
        some (row state (some bit) (Tape.read scratch)
          (Tape.read work) keepR keepS keepS target))
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (tape1 tape2 : Tape Bool) :
    description.runConfig 1
        (config state (cursorTape leftRev (bit :: tail)) tape1 tape2) =
      config target (cursorTape (some bit :: leftRev) tail) tape1 tape2 := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    hlookup _ _ _ (by simp [cursorTape, tapeAtCells, Tape.read])]
  cases tail <;>
    three_tape_step [description, cursorTape]

theorem run32_of_lookup
    (bit : Bool) (target : Nat)
    (hlookup : ∀ source scratch work,
      Tape.read source = some bit ->
      description.lookupTransition (config 32 source scratch work) =
        some (row 32 (some bit) (Tape.read scratch)
          (Tape.read work) keepR (writeBitR false) keepS target))
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (markers : Nat) (prefixLeft : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig 1
        (config 32 (cursorTape leftRev (bit :: tail))
          (parserMarkerBuildTape markers prefixLeft) tape2) =
      config target (cursorTape (some bit :: leftRev) tail)
        (parserMarkerBuildTape (markers + 1) prefixLeft) tape2 := by
  have hmarkers :
      some false ::
          (List.replicate markers (some false) ++ none :: prefixLeft) =
        List.replicate (markers + 1) (some false) ++ none :: prefixLeft := by
    rw [show markers + 1 = 1 + markers by lia]
    simpa using (list_replicate_add_append
      (some false : Option Bool) 1 markers (none :: prefixLeft)).symm
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    hlookup _ _ _ (by simp [cursorTape, tapeAtCells, Tape.read])]
  cases tail <;>
    three_tape_step [description, cursorTape, parserMarkerBuildTape, hmarkers]

theorem run_nat_tick
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (markers : Nat) (prefixLeft : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig 4
        (config 29
          (cursorTape leftRev
            (List.append ([false, false, true, false] : Word Bool) tail))
          (parserMarkerBuildTape markers prefixLeft) tape2) =
      config 29
        (cursorTape
          (some false :: some true :: some false :: some false :: leftRev)
          tail)
        (parserMarkerBuildTape (markers + 1) prefixLeft) tape2 := by
  simp only [List.append]
  rw [show 4 = 1 + 3 by rfl, Structured.Description.runConfig_add]
  rw [run_read_keepR_of_lookup 29 30 false lookup29_false]
  rw [show 3 = 1 + 2 by rfl, Structured.Description.runConfig_add]
  rw [run_read_keepR_of_lookup 30 31 false lookup30_false]
  rw [show 2 = 1 + 1 by rfl, Structured.Description.runConfig_add]
  rw [run_read_keepR_of_lookup 31 32 true lookup31_true]
  rw [run32_of_lookup false 29 lookup32_false]

theorem run_nat_done
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (markers : Nat) (prefixLeft : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig 4
        (config 29
          (cursorTape leftRev
            (List.append ([false, false, true, true] : Word Bool) tail))
          (parserMarkerBuildTape markers prefixLeft) tape2) =
      config 33
        (cursorTape
          (some true :: some true :: some false :: some false :: leftRev)
          tail)
        (parserMarkerBuildTape (markers + 1) prefixLeft) tape2 := by
  simp only [List.append]
  rw [show 4 = 1 + 3 by rfl, Structured.Description.runConfig_add]
  rw [run_read_keepR_of_lookup 29 30 false lookup29_false]
  rw [show 3 = 1 + 2 by rfl, Structured.Description.runConfig_add]
  rw [run_read_keepR_of_lookup 30 31 false lookup30_false]
  rw [show 2 = 1 + 1 by rfl, Structured.Description.runConfig_add]
  rw [run_read_keepR_of_lookup 31 32 true lookup31_true]
  rw [run32_of_lookup true 33 lookup32_true]

theorem run_stageNatBits
    (leftRev : List (Option Bool)) (stage : Nat) (tail : Word Bool)
    (markers : Nat) (prefixLeft : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig (4 * stage + 4)
        (config 29
          (cursorTape leftRev
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              tail))
          (parserMarkerBuildTape markers prefixLeft) tape2) =
      config 33
        (cursorTape
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            leftRev)
          tail)
        (parserMarkerBuildTape (markers + stage + 1) prefixLeft)
        tape2 := by
  induction stage generalizing leftRev markers with
  | zero =>
      simpa using run_nat_done leftRev tail markers prefixLeft tape2
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 = 4 + (4 * stage + 4) by lia]
      rw [Structured.Description.runConfig_add]
      have hinput :
          List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                (stage + 1))
              tail =
            List.append ([false, false, true, false] : Word Bool)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage)
                tail) := by
        simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ]
      rw [hinput]
      rw [run_nat_tick]
      rw [ih]
      have hleft :
          List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).reverse.map some)
              (some false :: some true :: some false :: some false :: leftRev) =
            List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                (stage + 1)).reverse.map some)
              leftRev := by
        simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
          List.map_append, List.append_assoc]
      have hmarkers :
          (markers + 1) + stage + 1 = markers + (stage + 1) + 1 := by
        lia
      rw [hleft, hmarkers]

theorem lookup33
    (source scratch work : Tape Bool) :
    description.lookupTransition (config 33 source scratch work) =
      some (row 33 (Tape.read source) (Tape.read scratch) (Tape.read work)
        keepS keepL keepS 34) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 33
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
    allReadRows3_find?_same, allReadRows3_find?_other,
    row, Structured.Description.Matches]

theorem lookup34_false
    (source scratch work : Tape Bool)
    (hscratch : Tape.read scratch = some false) :
    description.lookupTransition (config 34 source scratch work) =
      some (row 34 (Tape.read source) (some false) (Tape.read work)
        keepR eraseL keepS 35) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 34
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hsource : Tape.read source <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_other,
        row, Structured.Description.Matches, hscratch]

theorem lookup34_none
    (source scratch work : Tape Bool)
    (hscratch : Tape.read scratch = none) :
    description.lookupTransition (config 34 source scratch work) =
      some (row 34 (Tape.read source) none (Tape.read work)
        keepS keepS keepS 40) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 34
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  cases hsource : Tape.read source <;> (try cases ‹Bool›) <;>
    cases hwork : Tape.read work <;> (try cases ‹Bool›) <;>
      simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
        allReadRows3_find?_other,
        row, Structured.Description.Matches, hscratch]

theorem lookup35
    (source scratch work : Tape Bool) :
    description.lookupTransition (config 35 source scratch work) =
      some (row 35 (Tape.read source) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 36) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 35
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
    allReadRows3_find?_same, allReadRows3_find?_other,
    row, Structured.Description.Matches]

theorem lookup36
    (source scratch work : Tape Bool) :
    description.lookupTransition (config 36 source scratch work) =
      some (row 36 (Tape.read source) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 37) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 36
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
    allReadRows3_find?_same, allReadRows3_find?_other,
    row, Structured.Description.Matches]

theorem lookup37
    (source scratch work : Tape Bool) :
    description.lookupTransition (config 37 source scratch work) =
      some (row 37 (Tape.read source) (Tape.read scratch) (Tape.read work)
        keepR keepS keepS 34) := by
  rw [Structured.Description.lookupTransition]
  change rows.find?
      (Structured.Description.Matches 37
        [Tape.read source, Tape.read scratch, Tape.read work]) = _
  simp [rows, rowsForTape0Read, rowsForTape1Read, allReads2,
    allReadRows3_find?_same, allReadRows3_find?_other,
    row, Structured.Description.Matches]

theorem run_begin_cell_skip
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (markers : Nat) (prefixLeft : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig 1
        (config 33 (cursorTape leftRev tail)
          (parserMarkerBuildTape (markers + 1) prefixLeft) tape2) =
      config 34 (cursorTape leftRev tail)
        (skipCounterTape (markers + 1) prefixLeft [none]) tape2 := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig, lookup33]
  three_tape_step [description, parserMarkerBuildTape, skipCounterTape,
    List.replicate_succ, list_replicate_add_append]

theorem run34_false
    (leftRev : List (Option Bool)) (bit : Bool) (tail : Word Bool)
    (markers : Nat) (prefixLeft rightPadding : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig 1
        (config 34 (cursorTape leftRev (bit :: tail))
          (skipCounterTape (markers + 1) prefixLeft rightPadding) tape2) =
      config 35 (cursorTape (some bit :: leftRev) tail)
        (skipCounterTape markers prefixLeft (none :: rightPadding)) tape2 := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    lookup34_false _ _ _
      (by simp [skipCounterTape, tapeAtCells, Tape.read])]
  cases markers <;> cases tail <;> cases bit <;>
    three_tape_step [description, cursorTape, skipCounterTape,
      List.replicate_succ, list_replicate_add_append]

theorem run_skip_cellBits
    (leftRev : List (Option Bool)) (bit : Bool) (tail : Word Bool)
    (markers : Nat) (prefixLeft rightPadding : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig 4
        (config 34
          (cursorTape leftRev
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                bit)
              tail))
          (skipCounterTape (markers + 1) prefixLeft rightPadding)
          tape2) =
      config 34
        (cursorTape
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
              bit).reverse.map some)
            leftRev)
          tail)
        (skipCounterTape markers prefixLeft (none :: rightPadding))
        tape2 := by
  cases bit <;>
    simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits,
      encodeCodeSymbolAsInput]
  · rw [show 4 = 1 + 3 by rfl, Structured.Description.runConfig_add]
    rw [run34_false]
    rw [show 3 = 1 + 2 by rfl, Structured.Description.runConfig_add]
    rw [run_keepR_of_lookup 35 36 lookup35]
    rw [show 2 = 1 + 1 by rfl, Structured.Description.runConfig_add]
    rw [run_keepR_of_lookup 36 37 lookup36]
    rw [run_keepR_of_lookup 37 34 lookup37]
  · rw [show 4 = 1 + 3 by rfl, Structured.Description.runConfig_add]
    rw [run34_false]
    rw [show 3 = 1 + 2 by rfl, Structured.Description.runConfig_add]
    rw [run_keepR_of_lookup 35 36 lookup35]
    rw [show 2 = 1 + 1 by rfl, Structured.Description.runConfig_add]
    rw [run_keepR_of_lookup 36 37 lookup36]
    rw [run_keepR_of_lookup 37 34 lookup37]

theorem run_skip_cellsBits
    (leftRev : List (Option Bool)) (bits tail : Word Bool)
    (prefixLeft rightPadding : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig (4 * bits.length)
        (config 34
          (cursorTape leftRev
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                bits)
              tail))
          (skipCounterTape bits.length prefixLeft rightPadding)
          tape2) =
      config 34
        (cursorTape
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              bits).reverse.map some)
            leftRev)
          tail)
        (skipCounterTape 0 prefixLeft
          (List.append (List.replicate bits.length none) rightPadding))
        tape2 := by
  induction bits generalizing leftRev rightPadding with
  | nil =>
      simp [Structured.Description.runConfig,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_nil]
  | cons bit rest ih =>
      rw [show 4 * (bit :: rest).length = 4 + 4 * rest.length by
        simp; lia]
      rw [Structured.Description.runConfig_add]
      have hinput :
          List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                (bit :: rest))
              tail =
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                bit)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                  rest)
                tail) := by
        simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_cons,
          List.append_assoc]
      rw [hinput]
      simp only [List.length_cons]
      rw [run_skip_cellBits]
      rw [ih]
      have hleft :
          List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                rest).reverse.map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  bit).reverse.map some)
                leftRev) =
            List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                (bit :: rest)).reverse.map some)
              leftRev := by
        simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_cons,
          List.reverse_append, List.map_append, List.append_assoc]
      have hpadding :
          List.append (List.replicate rest.length none)
              (none :: rightPadding) =
            List.append (List.replicate (rest.length + 1) none)
              rightPadding := by
        have blank_shift : ∀ n : Nat,
            List.append (List.replicate n none) (none :: rightPadding) =
              List.append (List.replicate (n + 1) none) rightPadding := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
              simp only [List.replicate_succ]
              exact congrArg (List.cons none) ih
        exact blank_shift rest.length
      rw [hleft, hpadding]

theorem run_cell_skip_done
    (leftRev : List (Option Bool)) (tail : Word Bool)
    (prefixLeft rightPadding : List (Option Bool))
    (tape2 : Tape Bool) :
    description.runConfig 1
        (config 34 (cursorTape leftRev tail)
          (skipCounterTape 0 prefixLeft rightPadding) tape2) =
      config 40 (cursorTape leftRev tail)
        (skipCounterTape 0 prefixLeft rightPadding) tape2 := by
  simp only [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig,
    lookup34_none _ _ _
      (by simp [skipCounterTape, tapeAtCells, Tape.read])]
  three_tape_step [description]

end DirectJoinedCloseout
end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
