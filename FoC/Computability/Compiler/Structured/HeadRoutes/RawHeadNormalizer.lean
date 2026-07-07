import FoC.Computability.Compiler.Structured.HeadRoutes.Base

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

namespace SelectedSegmentLogicalTapeDecoderRawHeadNormalizer

def startState : Nat := 0

def haltState : Nat := 99

/--
Lowerer-facing row table for the raw selected-head normalizer.

The machine starts with tape 0 on the selected segment separator.  It copies
decoded cells before the raw {lit}`[true, true]` marker to tape 2's left side,
skips the marker, copies the head/right cells to tape 2, then scans tape 0
backwards to the marker while rewinding tape 2 to the decoded head cell.
Tape 1 is deliberately unused so the endpoint can keep it exactly blank.
-/
def rows : List Transition :=
  [ ThreeTape.row 0 none none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 1

  , ThreeTape.row 1 (some false) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 2
  , ThreeTape.row 1 (some true) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 3
  , ThreeTape.row 2 (some false) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepR 1
  , ThreeTape.row 2 (some true) none none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR (some false)) 1
  , ThreeTape.row 3 (some false) none none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR (some true)) 1
  , ThreeTape.row 3 (some true) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 4

  , ThreeTape.row 4 none none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 4 (some false) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 5
  , ThreeTape.row 4 (some true) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepS 6
  , ThreeTape.row 5 (some false) none none
      ThreeTape.keepR ThreeTape.keepS ThreeTape.keepR 4
  , ThreeTape.row 5 (some true) none none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR (some false)) 4
  , ThreeTape.row 6 (some false) none none
      ThreeTape.keepR ThreeTape.keepS (ThreeTape.writeR (some true)) 4

  , ThreeTape.row 10 (some false) none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 12
  , ThreeTape.row 10 (some false) none (some false)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 12
  , ThreeTape.row 10 (some false) none (some true)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 12
  , ThreeTape.row 10 (some true) none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 11
  , ThreeTape.row 10 (some true) none (some false)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 11
  , ThreeTape.row 10 (some true) none (some true)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 11
  , ThreeTape.row 11 (some false) none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 10
  , ThreeTape.row 11 (some false) none (some false)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 10
  , ThreeTape.row 11 (some false) none (some true)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepL 10
  , ThreeTape.row 11 (some true) none none
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepS haltState
  , ThreeTape.row 11 (some true) none (some false)
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepS haltState
  , ThreeTape.row 11 (some true) none (some true)
      ThreeTape.keepS ThreeTape.keepS ThreeTape.keepS haltState
  , ThreeTape.row 12 (some false) none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 12 (some false) none (some false)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 12 (some false) none (some true)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 12 (some true) none none
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 12 (some true) none (some false)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10
  , ThreeTape.row 12 (some true) none (some true)
      ThreeTape.keepL ThreeTape.keepS ThreeTape.keepS 10 ]

def description : Description :=
  ThreeTape.description 100 startState haltState rows

theorem description_wellFormed :
    description.WellFormed :=
  structuredDescription_wellFormed_of_bool description (by decide)

theorem description_haltTransitionFree :
    description.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_bool description (by decide)

theorem description_supportsReadWriteRows3 :
    SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_wellFormed
      description_supportsReadWriteRows3

def initialConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  ThreeTape.config startState
    (selectedSegmentLogicalTapeDecoderRawHeadSourceTape
      target rest encodedPrefix)
    Tape.blank
    Tape.blank

def finalConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  ThreeTape.config haltState
    (selectedSegmentLogicalTapeDecoderRawHeadFinalSourceTape
      target rest encodedPrefix)
    Tape.blank
    (selectedSegmentLogicalTapeDecoderRawHeadOutputTape target)

def targetCells (target : Tape Bool) : List (Option Bool) :=
  let guarded := guardLogicalTape target
  List.append guarded.left.reverse
    (guarded.head :: guarded.right)

def rightEdgeOutputTape (target : Tape Bool) : Tape Bool :=
  tapeAtCells (targetCells target).reverse []

def afterLeftCopyConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  let guarded := guardLogicalTape target
  ThreeTape.config 4
    (tapeAtEncodedSplit
      (List.append encodedPrefix
        (List.append tapeSeparatorCells
          (List.append (logicalCellListCode guarded.left.reverse)
            headMarkerCells)))
      (List.append (logicalCellCode guarded.head)
        (List.append (logicalCellListCode guarded.right)
          (encodedStructuredTapeCells rest))))
    Tape.blank
    (tapeAtCells guarded.left [])

def afterRightCopyConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  let guarded := guardLogicalTape target
  ThreeTape.config 4
    (tapeAtEncodedSplit
      (List.append encodedPrefix
        (List.append tapeSeparatorCells
          (logicalTapeCode guarded)))
      (encodedStructuredTapeCells rest))
    Tape.blank
    (rightEdgeOutputTape target)

def rewindStartConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  let guarded := guardLogicalTape target
  ThreeTape.config 10
    (ThreeTape.keepL.apply
      (tapeAtEncodedSplit
        (List.append encodedPrefix
          (List.append tapeSeparatorCells
            (logicalTapeCode guarded)))
        (encodedStructuredTapeCells rest)))
    Tape.blank
    (rightEdgeOutputTape target)

def rewindMarkerSecondConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) : Configuration :=
  let guarded := guardLogicalTape target
  ThreeTape.config 10
    (tapeAtEncodedSplit
      (List.append
        (List.append encodedPrefix
          (List.append tapeSeparatorCells
            (logicalCellListCode guarded.left.reverse)))
        [some true])
      (List.append [some true]
        (List.append (logicalCellCode guarded.head)
          (List.append (logicalCellListCode guarded.right)
            (encodedStructuredTapeCells rest)))))
    Tape.blank
        (selectedSegmentLogicalTapeDecoderRawHeadOutputTape target)

private def rewindOutputCurrentCells
    (cells : List (Option Bool)) : List (Option Bool) :=
  match cells with
  | [] => [none]
  | _ => cells

@[simp] private theorem rewindOutputCurrentCells_cons
    (cell : Option Bool) (tail : List (Option Bool)) :
    rewindOutputCurrentCells (cell :: tail) = cell :: tail := by
  rfl

@[simp] private theorem rewindOutputCurrentCells_logicalCellListCode_singleton_append
    (cell : Option Bool) (tail : List (Option Bool)) :
    rewindOutputCurrentCells
        (List.append (logicalCellListCode [cell]) tail) =
      List.append (logicalCellListCode [cell]) tail := by
  cases cell with
  | none =>
      simp [rewindOutputCurrentCells, logicalCellListCode, logicalCellCode]
  | some bit =>
      cases bit <;>
        simp [rewindOutputCurrentCells, logicalCellListCode,
          logicalCellCode]

@[simp] private theorem rewindOutputCurrentCells_logicalCellListBits_singleton_append
    (cell : Option Bool) (tail : List (Option Bool)) :
    rewindOutputCurrentCells
        (List.append (List.map some (logicalCellListBits [cell])) tail) =
      List.append (List.map some (logicalCellListBits [cell])) tail := by
  cases cell with
  | none =>
      simp [rewindOutputCurrentCells, logicalCellListBits,
        logicalCellBits]
  | some bit =>
      cases bit <;>
        simp [rewindOutputCurrentCells, logicalCellListBits,
          logicalCellBits]

@[simp] private theorem rewindOutputCurrentCells_encodedStructuredTapeCells
    (rest : List (Tape Bool)) :
    rewindOutputCurrentCells (encodedStructuredTapeCells rest) =
      encodedStructuredTapeCells rest := by
  cases rest with
  | nil =>
      simp [rewindOutputCurrentCells, encodedStructuredTapeCells,
        tapeSeparatorCells]
  | cons T rest =>
      simp [rewindOutputCurrentCells, encodedStructuredTapeCells,
        tapeSeparatorCells]

private def rewindCellStackConfig
    (baseLeft stack sourceRight outputLeft outputRight :
      List (Option Bool)) : Configuration :=
  ThreeTape.config 10
    (ThreeTape.keepL.apply
      (tapeAtCells
        (List.append (logicalCellListCode stack.reverse).reverse baseLeft)
        sourceRight))
    Tape.blank
    (tapeAtCells (List.append stack outputLeft) outputRight)

private def rewindCellStackDoneConfig
    (baseLeft stack sourceRight outputLeft outputRight :
      List (Option Bool)) : Configuration :=
  ThreeTape.config 10
    (ThreeTape.keepL.apply
      (tapeAtCells baseLeft
        (List.append (logicalCellListCode stack.reverse)
          (rewindOutputCurrentCells sourceRight))))
    Tape.blank
    (tapeAtCells outputLeft
      (List.append stack.reverse (rewindOutputCurrentCells outputRight)))

private theorem description_rewinds_cellStack_step_nilSource
    (baseLeft stack outputLeft outputRight :
      List (Option Bool)) (cell : Option Bool) :
    description.runConfig 2
        (rewindCellStackConfig baseLeft (cell :: stack)
          [] outputLeft outputRight) =
      rewindCellStackConfig baseLeft stack
        (List.append (logicalCellListCode [cell])
          (rewindOutputCurrentCells []))
        outputLeft
        (cell :: rewindOutputCurrentCells outputRight) := by
  cases cell with
  | none =>
      cases outputRight with
      | nil =>
          three_tape_step [
            description, rows, rewindCellStackConfig,
            rewindOutputCurrentCells, logicalCellCode,
            logicalCellListCode, logicalCellListBits, logicalCellBits,
            tapeAtCells]
      | cons outHead outTail =>
          cases outHead with
          | none =>
              three_tape_step [
                description, rows, rewindCellStackConfig,
                rewindOutputCurrentCells, logicalCellCode,
                logicalCellListCode, logicalCellListBits,
                logicalCellBits,
                tapeAtCells]
          | some outBit =>
              cases outBit <;>
                three_tape_step [
                  description, rows, rewindCellStackConfig,
                  rewindOutputCurrentCells, logicalCellCode,
                  logicalCellListCode, logicalCellListBits,
                  logicalCellBits,
                  tapeAtCells]
  | some bit =>
      cases bit <;>
        cases outputRight with
        | nil =>
            three_tape_step [
              description, rows, rewindCellStackConfig,
              rewindOutputCurrentCells, logicalCellCode,
              logicalCellListCode, logicalCellListBits, logicalCellBits,
              tapeAtCells]
        | cons outHead outTail =>
            cases outHead with
            | none =>
                three_tape_step [
                  description, rows, rewindCellStackConfig,
                  rewindOutputCurrentCells, logicalCellCode,
                  logicalCellListCode, logicalCellListBits,
                  logicalCellBits,
                  tapeAtCells]
            | some outBit =>
                cases outBit <;>
                  three_tape_step [
                    description, rows, rewindCellStackConfig,
                    rewindOutputCurrentCells, logicalCellCode,
                    logicalCellListCode, logicalCellListBits,
                    logicalCellBits,
                    tapeAtCells]

private theorem description_rewinds_cellStack_step_sourceHeadNone
    (baseLeft stack sourceTail outputLeft outputRight :
      List (Option Bool)) (cell : Option Bool) :
    description.runConfig 2
        (rewindCellStackConfig baseLeft (cell :: stack)
          (none :: sourceTail) outputLeft outputRight) =
      rewindCellStackConfig baseLeft stack
        (List.append (logicalCellListCode [cell])
          (rewindOutputCurrentCells (none :: sourceTail)))
        outputLeft
        (cell :: rewindOutputCurrentCells outputRight) := by
  cases cell with
  | none =>
      cases outputRight with
      | nil =>
          three_tape_step [
            description, rows, rewindCellStackConfig,
            rewindOutputCurrentCells, logicalCellCode,
            logicalCellListCode, logicalCellListBits,
            logicalCellBits,
            tapeAtCells]
      | cons outHead outTail =>
          cases outHead with
          | none =>
              three_tape_step [
                description, rows, rewindCellStackConfig,
                rewindOutputCurrentCells, logicalCellCode,
                logicalCellListCode, logicalCellListBits,
                logicalCellBits,
                tapeAtCells]
          | some outBit =>
              cases outBit <;>
                three_tape_step [
                  description, rows, rewindCellStackConfig,
                  rewindOutputCurrentCells, logicalCellCode,
                  logicalCellListCode, logicalCellListBits,
                  logicalCellBits,
                  tapeAtCells]
  | some bit =>
      cases bit <;>
        cases outputRight with
        | nil =>
            three_tape_step [
              description, rows, rewindCellStackConfig,
              rewindOutputCurrentCells, logicalCellCode,
              logicalCellListCode, logicalCellListBits,
              logicalCellBits,
              tapeAtCells]
        | cons outHead outTail =>
            cases outHead with
            | none =>
                three_tape_step [
                  description, rows, rewindCellStackConfig,
                  rewindOutputCurrentCells, logicalCellCode,
                  logicalCellListCode, logicalCellListBits,
                  logicalCellBits,
                  tapeAtCells]
            | some outBit =>
                cases outBit <;>
                  three_tape_step [
                    description, rows, rewindCellStackConfig,
                    rewindOutputCurrentCells, logicalCellCode,
                    logicalCellListCode, logicalCellListBits,
                    logicalCellBits,
                    tapeAtCells]

private theorem description_rewinds_cellStack_step_sourceHeadSome
    (baseLeft stack sourceTail outputLeft outputRight :
      List (Option Bool)) (sourceBit : Bool) (cell : Option Bool) :
    description.runConfig 2
        (rewindCellStackConfig baseLeft (cell :: stack)
          (some sourceBit :: sourceTail) outputLeft outputRight) =
      rewindCellStackConfig baseLeft stack
        (List.append (logicalCellListCode [cell])
          (rewindOutputCurrentCells (some sourceBit :: sourceTail)))
        outputLeft
        (cell :: rewindOutputCurrentCells outputRight) := by
  cases sourceBit <;>
    cases cell with
    | none =>
        cases outputRight with
        | nil =>
            three_tape_step [
              description, rows, rewindCellStackConfig,
              rewindOutputCurrentCells, logicalCellCode,
              logicalCellListCode, logicalCellListBits,
              logicalCellBits,
              tapeAtCells]
        | cons outHead outTail =>
            cases outHead with
            | none =>
                three_tape_step [
                  description, rows, rewindCellStackConfig,
                  rewindOutputCurrentCells, logicalCellCode,
                  logicalCellListCode, logicalCellListBits,
                  logicalCellBits,
                  tapeAtCells]
            | some outBit =>
                cases outBit <;>
                  three_tape_step [
                    description, rows, rewindCellStackConfig,
                    rewindOutputCurrentCells, logicalCellCode,
                    logicalCellListCode, logicalCellListBits,
                    logicalCellBits,
                    tapeAtCells]
    | some bit =>
        cases bit <;>
          cases outputRight with
          | nil =>
              three_tape_step [
                description, rows, rewindCellStackConfig,
                rewindOutputCurrentCells, logicalCellCode,
                logicalCellListCode, logicalCellListBits,
                logicalCellBits,
                tapeAtCells]
          | cons outHead outTail =>
              cases outHead with
              | none =>
                  three_tape_step [
                    description, rows, rewindCellStackConfig,
                    rewindOutputCurrentCells, logicalCellCode,
                    logicalCellListCode, logicalCellListBits,
                    logicalCellBits,
                    tapeAtCells]
              | some outBit =>
                  cases outBit <;>
                    three_tape_step [
                      description, rows, rewindCellStackConfig,
                      rewindOutputCurrentCells, logicalCellCode,
                      logicalCellListCode, logicalCellListBits,
                      logicalCellBits,
                      tapeAtCells]

private theorem description_rewinds_cellStack_step
    (baseLeft stack sourceRight outputLeft outputRight :
      List (Option Bool)) (cell : Option Bool) :
    description.runConfig 2
        (rewindCellStackConfig baseLeft (cell :: stack)
          sourceRight outputLeft outputRight) =
      rewindCellStackConfig baseLeft stack
        (List.append (logicalCellListCode [cell])
          (rewindOutputCurrentCells sourceRight))
        outputLeft
        (cell :: rewindOutputCurrentCells outputRight) := by
  cases sourceRight with
  | nil =>
      exact description_rewinds_cellStack_step_nilSource
        baseLeft stack outputLeft outputRight cell
  | cons sourceHead sourceTail =>
      cases sourceHead with
      | none =>
          exact description_rewinds_cellStack_step_sourceHeadNone
            baseLeft stack sourceTail outputLeft outputRight cell
      | some sourceBit =>
          exact description_rewinds_cellStack_step_sourceHeadSome
            baseLeft stack sourceTail outputLeft outputRight sourceBit cell

private theorem description_rewinds_cellStackConfig
    (baseLeft stack sourceRight outputLeft outputRight :
      List (Option Bool)) :
    description.runConfig (2 * stack.length)
      (rewindCellStackConfig
        baseLeft stack sourceRight outputLeft outputRight) =
      rewindCellStackDoneConfig
        baseLeft stack sourceRight outputLeft outputRight := by
  induction stack generalizing sourceRight outputRight with
  | nil =>
      cases sourceRight <;> cases outputRight <;>
        simp [rewindCellStackConfig, rewindCellStackDoneConfig,
          rewindOutputCurrentCells, logicalCellListBits,
          Structured.Description.runConfig, tapeAtCells]
  | cons cell stack ih =>
      rw [show 2 * (cell :: stack).length =
        2 + 2 * stack.length by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [description_rewinds_cellStack_step]
      rw [ih (List.append (logicalCellListCode [cell])
          (rewindOutputCurrentCells sourceRight))
        (cell :: rewindOutputCurrentCells outputRight)]
      change
        ThreeTape.config 10
          (ThreeTape.keepL.apply
            (tapeAtCells baseLeft
              (List.append (logicalCellListCode stack.reverse)
                (rewindOutputCurrentCells
                  (List.append (logicalCellListCode [cell])
                    (rewindOutputCurrentCells sourceRight))))))
          Tape.blank
          (tapeAtCells outputLeft
            (List.append stack.reverse
              (rewindOutputCurrentCells
                (cell :: rewindOutputCurrentCells outputRight)))) = _
      rw [rewindOutputCurrentCells_logicalCellListCode_singleton_append]
      simp [rewindCellStackDoneConfig, List.reverse_cons, List.append_assoc]

private def leftCopyConfig
    (baseLeft processed remaining suffix :
      List (Option Bool)) : Configuration :=
  ThreeTape.config 1
    (tapeAtEncodedSplit
      (List.append baseLeft (logicalCellListCode processed))
      (List.append (logicalCellListCode remaining)
        (List.append headMarkerCells suffix)))
    Tape.blank
    (tapeAtCells processed.reverse [])

private theorem description_enters_leftCopyConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    description.runConfig 1
        (initialConfig target rest encodedPrefix) =
      leftCopyConfig
        (List.append encodedPrefix tapeSeparatorCells)
        []
        (guardLogicalTape target).left.reverse
        (List.append (logicalCellCode (guardLogicalTape target).head)
          (List.append (logicalCellListCode (guardLogicalTape target).right)
            (encodedStructuredTapeCells rest))) := by
  cases target with
  | mk left head right =>
      cases head with
      | none =>
          three_tape_step [
            description, rows, initialConfig, leftCopyConfig,
            selectedSegmentLogicalTapeDecoderRawHeadSourceTape,
            guardLogicalTape, logicalTapeCode, logicalCellListCode,
            logicalCellCode, logicalCellListBits, logicalCellBits,
            encodedStructuredTapeCells, tapeAtEncodedSplit,
            tapeSeparatorCells, headMarkerCells, startState, haltState,
            List.map_append, List.append_assoc]
      | some bit =>
          cases bit <;>
            three_tape_step [
              description, rows, initialConfig, leftCopyConfig,
              selectedSegmentLogicalTapeDecoderRawHeadSourceTape,
              guardLogicalTape, logicalTapeCode, logicalCellListCode,
              logicalCellCode, logicalCellListBits, logicalCellBits,
              encodedStructuredTapeCells, tapeAtEncodedSplit,
              tapeSeparatorCells, headMarkerCells, startState, haltState,
              List.map_append, List.append_assoc]

private theorem description_leftCopy_cell
    (baseLeft processed remaining suffix : List (Option Bool))
    (cell : Option Bool) :
    description.runConfig 2
        (leftCopyConfig baseLeft processed (cell :: remaining) suffix) =
      leftCopyConfig baseLeft (List.append processed [cell])
        remaining suffix := by
  cases cell with
  | none =>
      three_tape_step [
        description, rows, leftCopyConfig, logicalCellListCode,
        logicalCellCode, logicalCellListBits, logicalCellBits,
        tapeAtEncodedSplit, tapeAtCells, List.map_append,
        List.reverse_append, List.append_assoc]
      cases
          (List.map some (logicalCellListBits remaining) ++
            (headMarkerCells ++ suffix)) <;>
        rfl
  | some bit =>
      cases bit <;>
        three_tape_step [
          description, rows, leftCopyConfig, logicalCellListCode,
          logicalCellCode, logicalCellListBits, logicalCellBits,
          tapeAtEncodedSplit, tapeAtCells, List.map_append,
          List.reverse_append, List.append_assoc]
      all_goals
        cases
            (List.map some (logicalCellListBits remaining) ++
              (headMarkerCells ++ suffix)) <;>
          rfl

private theorem description_leftCopy_cells
    (baseLeft processed remaining suffix : List (Option Bool)) :
    description.runConfig (2 * remaining.length)
        (leftCopyConfig baseLeft processed remaining suffix) =
      leftCopyConfig baseLeft (List.append processed remaining)
        [] suffix := by
  induction remaining generalizing processed with
  | nil =>
      simp [leftCopyConfig, Structured.Description.runConfig]
  | cons cell remaining ih =>
      rw [show 2 * (cell :: remaining).length =
        2 + 2 * remaining.length by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [description_leftCopy_cell]
      rw [ih (List.append processed [cell])]
      simp [List.append_assoc]

private theorem description_leftCopy_headMarker
    (baseLeft processed suffix : List (Option Bool)) :
    description.runConfig 2
        (leftCopyConfig baseLeft processed [] suffix) =
      ThreeTape.config 4
        (tapeAtEncodedSplit
          (List.append
            (List.append baseLeft (logicalCellListCode processed))
            headMarkerCells)
          suffix)
        Tape.blank
        (tapeAtCells processed.reverse []) := by
  cases suffix with
  | nil =>
      three_tape_step [
        description, rows, leftCopyConfig, logicalCellListCode,
        logicalCellCode, tapeAtEncodedSplit, tapeAtCells,
        headMarkerCells, List.reverse_append, List.append_assoc]
  | cons sourceHead sourceTail =>
      cases sourceHead with
      | none =>
          three_tape_step [
            description, rows, leftCopyConfig, logicalCellListCode,
            logicalCellCode, tapeAtEncodedSplit, tapeAtCells,
            headMarkerCells, List.reverse_append, List.append_assoc]
      | some sourceBit =>
          cases sourceBit <;>
            three_tape_step [
              description, rows, leftCopyConfig, logicalCellListCode,
              logicalCellCode, tapeAtEncodedSplit, tapeAtCells,
              headMarkerCells, List.reverse_append, List.append_assoc]

theorem description_reaches_afterLeftCopyConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
        (initialConfig target rest encodedPrefix) =
        afterLeftCopyConfig target rest encodedPrefix := by
  let guarded : Tape Bool := guardLogicalTape target
  let baseLeft : List (Option Bool) :=
    List.append encodedPrefix tapeSeparatorCells
  let suffix : List (Option Bool) :=
    List.append (logicalCellCode guarded.head)
      (List.append (logicalCellListCode guarded.right)
        (encodedStructuredTapeCells rest))
  refine ⟨1 + (2 * guarded.left.reverse.length + 2), ?_⟩
  rw [Description.runConfig_add]
  rw [description_enters_leftCopyConfig]
  change
    description.runConfig (2 * guarded.left.reverse.length + 2)
        (leftCopyConfig baseLeft [] guarded.left.reverse suffix) =
      afterLeftCopyConfig target rest encodedPrefix
  rw [Description.runConfig_add]
  rw [description_leftCopy_cells]
  rw [description_leftCopy_headMarker]
  simp [guarded, baseLeft, suffix, afterLeftCopyConfig, tapeAtEncodedSplit,
    List.append_assoc]

private def rightCopyConfig
    (baseLeft outputBaseLeft processed remaining suffix :
      List (Option Bool)) : Configuration :=
  ThreeTape.config 4
    (tapeAtEncodedSplit
      (List.append baseLeft (logicalCellListCode processed))
      (List.append (logicalCellListCode remaining) suffix))
    Tape.blank
    (tapeAtCells (List.append processed.reverse outputBaseLeft) [])

private theorem description_rightCopy_cell
    (baseLeft outputBaseLeft processed remaining suffix :
      List (Option Bool)) (cell : Option Bool) :
    description.runConfig 2
        (rightCopyConfig baseLeft outputBaseLeft processed
          (cell :: remaining) suffix) =
      rightCopyConfig baseLeft outputBaseLeft
        (List.append processed [cell]) remaining suffix := by
  cases cell with
  | none =>
      three_tape_step [
        description, rows, rightCopyConfig, logicalCellListCode,
        logicalCellCode, logicalCellListBits, logicalCellBits,
        tapeAtEncodedSplit, tapeAtCells, List.map_append,
        List.reverse_append, List.append_assoc]
      cases
          (List.map some (logicalCellListBits remaining) ++ suffix) <;>
        rfl
  | some bit =>
      cases bit <;>
        three_tape_step [
          description, rows, rightCopyConfig, logicalCellListCode,
          logicalCellCode, logicalCellListBits, logicalCellBits,
          tapeAtEncodedSplit, tapeAtCells, List.map_append,
          List.reverse_append, List.append_assoc]
      all_goals
        cases
            (List.map some (logicalCellListBits remaining) ++ suffix) <;>
          rfl

private theorem description_rightCopy_cells
    (baseLeft outputBaseLeft processed remaining suffix :
      List (Option Bool)) :
    description.runConfig (2 * remaining.length)
        (rightCopyConfig baseLeft outputBaseLeft processed
          remaining suffix) =
      rightCopyConfig baseLeft outputBaseLeft
        (List.append processed remaining) [] suffix := by
  induction remaining generalizing processed with
  | nil =>
      simp [rightCopyConfig, Structured.Description.runConfig]
  | cons cell remaining ih =>
      rw [show 2 * (cell :: remaining).length =
        2 + 2 * remaining.length by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [description_rightCopy_cell]
      rw [ih (List.append processed [cell])]
      simp [List.append_assoc]

theorem description_reaches_afterRightCopyConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
        (afterLeftCopyConfig target rest encodedPrefix) =
        afterRightCopyConfig target rest encodedPrefix := by
  let guarded : Tape Bool := guardLogicalTape target
  let baseLeft : List (Option Bool) :=
    List.append encodedPrefix
      (List.append tapeSeparatorCells
        (List.append (logicalCellListCode guarded.left.reverse)
          headMarkerCells))
  let cells : List (Option Bool) :=
    guarded.head :: guarded.right
  let suffix : List (Option Bool) := encodedStructuredTapeCells rest
  refine ⟨2 * cells.length, ?_⟩
  have h :=
    description_rightCopy_cells baseLeft guarded.left [] cells suffix
  simpa [guarded, baseLeft, cells, suffix, rightCopyConfig,
    afterLeftCopyConfig, afterRightCopyConfig, rightEdgeOutputTape,
    targetCells, logicalTapeCode, logicalCellListCode,
    logicalCellListBits, tapeAtEncodedSplit, List.map_append,
    List.reverse_append, List.append_assoc] using h

theorem description_enters_rewind
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    description.runConfig 1
      (afterRightCopyConfig target rest encodedPrefix) =
      rewindStartConfig target rest encodedPrefix := by
  cases target with
  | mk left head right =>
      cases rest with
      | nil =>
          three_tape_step [
            description, rows, afterRightCopyConfig, rewindStartConfig,
            rightEdgeOutputTape, targetCells, guardLogicalTape,
            logicalTapeCode, encodedStructuredTapeCells, tapeAtEncodedSplit,
            tapeSeparatorCells]
      | cons next rest =>
          three_tape_step [
            description, rows, afterRightCopyConfig, rewindStartConfig,
            rightEdgeOutputTape, targetCells, guardLogicalTape,
            logicalTapeCode, encodedStructuredTapeCells, tapeAtEncodedSplit,
            tapeSeparatorCells]

theorem description_rewinds_to_markerSecondConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
        (rewindStartConfig target rest encodedPrefix) =
        rewindMarkerSecondConfig target rest encodedPrefix := by
  cases target with
  | mk left head right =>
      let guarded : Tape Bool :=
        guardLogicalTape { left := left, head := head, right := right }
      let stack : List (Option Bool) :=
        (guarded.head :: guarded.right).reverse
      let baseLeft : List (Option Bool) :=
        List.append [some true, some true]
          (List.append encodedPrefix
            (List.append tapeSeparatorCells
              (logicalCellListCode guarded.left.reverse))).reverse
      refine ⟨2 * stack.length, ?_⟩
      have h :=
        description_rewinds_cellStackConfig
          baseLeft stack (encodedStructuredTapeCells rest)
          guarded.left []
      cases rest with
      | nil =>
          cases head with
          | none =>
              simpa [guarded, stack, baseLeft, rewindStartConfig,
                rewindMarkerSecondConfig, rewindCellStackConfig,
                rewindCellStackDoneConfig,
                selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
                rightEdgeOutputTape, targetCells, guardLogicalTape,
                logicalTapeCode, tapeAtEncodedSplit, tapeSeparatorCells,
                headMarkerCells, rewindOutputCurrentCells,
                logicalCellListBits, logicalCellBits, List.map_append,
                ThreeTape.keepL, Structured.TapeAction.apply,
                Structured.HeadMove.apply,
                Tape.move, Tape.moveLeft, tapeAtCells,
                List.reverse_append, List.append_assoc] using h
          | some bit =>
              cases bit <;>
                simpa [guarded, stack, baseLeft, rewindStartConfig,
                  rewindMarkerSecondConfig, rewindCellStackConfig,
                  rewindCellStackDoneConfig,
                  selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
                  rightEdgeOutputTape, targetCells, guardLogicalTape,
                  logicalTapeCode, tapeAtEncodedSplit, tapeSeparatorCells,
                  headMarkerCells, rewindOutputCurrentCells,
                  logicalCellListBits, logicalCellBits, List.map_append,
                  ThreeTape.keepL, Structured.TapeAction.apply,
                  Structured.HeadMove.apply,
                  Tape.move, Tape.moveLeft, tapeAtCells,
                  List.reverse_append, List.append_assoc] using h
      | cons next restTail =>
          cases head with
          | none =>
              simpa [guarded, stack, baseLeft, rewindStartConfig,
                rewindMarkerSecondConfig, rewindCellStackConfig,
                rewindCellStackDoneConfig,
                selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
                rightEdgeOutputTape, targetCells, guardLogicalTape,
                logicalTapeCode, tapeAtEncodedSplit, tapeSeparatorCells,
                headMarkerCells, rewindOutputCurrentCells,
                logicalCellListBits, logicalCellBits, List.map_append,
                ThreeTape.keepL, Structured.TapeAction.apply,
                Structured.HeadMove.apply,
                Tape.move, Tape.moveLeft, tapeAtCells,
                List.reverse_append, List.append_assoc] using h
          | some bit =>
              cases bit <;>
                simpa [guarded, stack, baseLeft, rewindStartConfig,
                  rewindMarkerSecondConfig, rewindCellStackConfig,
                  rewindCellStackDoneConfig,
                  selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
                  rightEdgeOutputTape, targetCells, guardLogicalTape,
                  logicalTapeCode, tapeAtEncodedSplit, tapeSeparatorCells,
                  headMarkerCells, rewindOutputCurrentCells,
                  logicalCellListBits, logicalCellBits, List.map_append,
                  ThreeTape.keepL, Structured.TapeAction.apply,
                  Structured.HeadMove.apply,
                  Tape.move, Tape.moveLeft, tapeAtCells,
                  List.reverse_append, List.append_assoc] using h

theorem description_rewinds_markerSecond_to_finalConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    description.runConfig 2
      (rewindMarkerSecondConfig target rest encodedPrefix) =
      finalConfig target rest encodedPrefix := by
  cases target with
  | mk left head right =>
      cases head with
      | none =>
          three_tape_step [
            description, rows, rewindMarkerSecondConfig, finalConfig,
            selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
            selectedSegmentLogicalTapeDecoderRawHeadFinalSourceTape,
            guardLogicalTape, logicalCellListCode, logicalCellCode,
            encodedStructuredTapeCells, tapeAtEncodedSplit,
            tapeSeparatorCells, headMarkerCells]
      | some bit =>
          cases bit <;>
            three_tape_step [
              description, rows, rewindMarkerSecondConfig, finalConfig,
              selectedSegmentLogicalTapeDecoderRawHeadOutputTape,
              selectedSegmentLogicalTapeDecoderRawHeadFinalSourceTape,
              guardLogicalTape, logicalCellListCode, logicalCellCode,
              encodedStructuredTapeCells, tapeAtEncodedSplit,
              tapeSeparatorCells, headMarkerCells]

theorem description_rewinds_to_finalConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
        (rewindStartConfig target rest encodedPrefix) =
        finalConfig target rest encodedPrefix := by
  rcases description_rewinds_to_markerSecondConfig target rest encodedPrefix with
    ⟨steps, hsteps⟩
  refine ⟨steps + 2, ?_⟩
  rw [Description.runConfig_add]
  rw [hsteps]
  exact description_rewinds_markerSecond_to_finalConfig
    target rest encodedPrefix

theorem description_reaches_finalConfig
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
        (afterRightCopyConfig target rest encodedPrefix) =
        finalConfig target rest encodedPrefix := by
  rcases description_rewinds_to_finalConfig target rest encodedPrefix with
    ⟨steps, hsteps⟩
  refine ⟨1 + steps, ?_⟩
  rw [Description.runConfig_add]
  rw [description_enters_rewind target rest encodedPrefix]
  exact hsteps

theorem description_haltsWithTapes
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    description.HaltsWithTapes
      (initialConfig target rest encodedPrefix)
      (finalConfig target rest encodedPrefix).tapes := by
  rcases
    description_reaches_afterLeftCopyConfig target rest encodedPrefix with
    ⟨leftSteps, hleft⟩
  rcases
    description_reaches_afterRightCopyConfig target rest encodedPrefix with
    ⟨rightSteps, hright⟩
  rcases
    description_reaches_finalConfig target rest encodedPrefix with
    ⟨rewindSteps, hrewind⟩
  refine ⟨(leftSteps + rightSteps) + rewindSteps, ?_⟩
  simpa [finalConfig] using
    ThreeTape.runConfig_chain3 hleft hright hrewind

theorem loweredDescription_haltsFromTapeEquiv
    (target : Tape Bool) (rest : List (Tape Bool))
    (encodedPrefix : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape
        target rest encodedPrefix)
      (selectedSegmentLogicalTapeDecoderRawHeadStructuredOutputTape
        target rest encodedPrefix) := by
  simpa [
    loweredDescription,
    initialConfig,
    finalConfig,
    selectedSegmentLogicalTapeDecoderRawHeadStructuredInputTape,
    selectedSegmentLogicalTapeDecoderRawHeadStructuredOutputTape,
    encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_wellFormed
      description_haltTransitionFree
      description_supportsReadWriteRows3
      (c := initialConfig target rest encodedPrefix)
      (tapes := (finalConfig target rest encodedPrefix).tapes)
      (by rfl)
      (by rfl)
      (description_haltsWithTapes target rest encodedPrefix)

theorem loweredDescription_spec :
    SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerSpec
      loweredDescription := by
  constructor
  · exact loweredDescription_subroutineReady
  · intro target rest encodedPrefix
    exact loweredDescription_haltsFromTapeEquiv target rest encodedPrefix

theorem construction :
    SelectedSegmentLogicalTapeDecoderRawHeadThreeTapeNormalizerConstruction :=
  ⟨loweredDescription, loweredDescription_spec⟩

end SelectedSegmentLogicalTapeDecoderRawHeadNormalizer

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
