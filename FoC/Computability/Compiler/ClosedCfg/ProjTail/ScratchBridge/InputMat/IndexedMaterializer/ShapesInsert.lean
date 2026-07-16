import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.InPlaceDecoderCopier
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.Shapes
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic

set_option doc.verso true

/-!
Tape shapes and the finite inserter used by both materializer branches.
-/

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat

open CanonicalLayouts.DovetailLayoutScanner

def directScratchBlankDriverBits
    (useAccept : Bool) (L : DovetailLayout) : Word Bool :=
  List.append (boolWordFieldBits L.input []).tail
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage)
      (List.append
        (selectedProjectionPaddedTailCleanupSelectedConfigBits useAccept L)
        (List.append (boolFieldBits L.acceptHit [])
          (boolFieldBits L.rejectHit []))))

theorem directScratchBlankDriverBits_length
    (useAccept : Bool) (L : DovetailLayout) :
    (directScratchBlankDriverBits useAccept L).length =
      (selectedProjectionPaddedTailCleanupScratchCountBits
        useAccept L).length + 2 := by
  have haccept := configurationFieldBits_length_pos L.acceptConfig
  have hreject := configurationFieldBits_length_pos L.rejectConfig
  cases useAccept <;>
    simp [directScratchBlankDriverBits, scratchCountBits_length,
      selectedProjectionPaddedTailCleanupSentinelBaseScratch,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      parsedLayoutBits_length, boolWordFieldBits_nil_length,
      boolFieldBits_nil_length,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_length]
  all_goals lia
theorem sourcePadding_accept_eq_acceptConfig_length
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput true) :
    countWindowPostFieldDecodedPrefixStructuredSourcePadding
        true input.L input.deletedTail =
      List.replicate
        ((configurationFieldBits input.L.acceptConfig []).length + 6)
        (none : Option Bool) := by
  rw [sourcePadding_accept_closedForm]
  rw [acceptConfigField_length_of_hdeleted input.hdeleted]

theorem sourcePadding_reject_eq_acceptConfig_length
    (input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput false) :
    countWindowPostFieldDecodedPrefixStructuredSourcePadding
        false input.L input.deletedTail =
      List.append
        (List.replicate
          ((configurationFieldBits input.L.acceptConfig []).length + 3)
          (none : Option Bool))
        (List.append
          ((selectedProjectionPaddedTailCleanupSelectedHitBits
            false input.L).map some)
          [none, none]) := by
  rw [sourcePadding_reject_closedForm]
  rw [acceptConfigField_length_of_hdeleted input.hdeleted]

end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape
namespace CountWindowInputMat
namespace AcceptConfigInserter

open EncRewriters.CanonicalLayouts.DovetailLayoutScanner

def rewind : Nat := 0
def header1 : Nat := 1
def header2 : Nat := 2
def header3 : Nat := 3
def header4 : Nat := 4
def count1 : Nat := 5
def count2 : Nat := 6
def count3 : Nat := 7
def count4 : Nat := 8
def stage1 : Nat := 9
def stage2 : Nat := 10
def stage3 : Nat := 11
def stage4 : Nat := 12
def halt : Nat := 13
def rowsForSourceRead
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read1 read2 =>
      row source sourceRead read1 read2
        action0 action1 action2 target)

def rowsForOutputRead
    (source : Nat) (outputRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read0 read1 =>
      row source read0 read1 outputRead
        action0 action1 action2 target)

def rows : List Transition :=
  [ rowsForSourceRead rewind (some false) keepL keepS keepS rewind
  , rowsForSourceRead rewind (some true) keepL keepS keepS rewind
  , rowsForSourceRead rewind none keepR keepS keepS header1
  , rowsForSourceRead header1 (some false) keepR keepS keepS header2
  , rowsForSourceRead header2 (some false) keepR keepS keepS header3
  , rowsForSourceRead header3 (some false) keepR keepS keepS header4
  , rowsForSourceRead header4 (some false) keepR keepS keepS count1
  , rowsForSourceRead count1 (some false) keepR keepS keepS count2
  , rowsForSourceRead count2 (some false) keepR keepS keepS count3
  , rowsForSourceRead count3 (some true) keepR keepS keepS count4
  , rowsForSourceRead count4 (some false) keepR keepS eraseR count1
  , rowsForSourceRead count4 (some true) keepR keepS keepS halt
  , rowsForOutputRead stage1 (some false) keepS keepS keepR stage2
  , rowsForOutputRead stage2 (some false) keepS keepS keepR stage3
  , rowsForOutputRead stage3 (some true) keepS keepS keepR stage4
  , rowsForOutputRead stage4 (some false) keepS keepS keepR stage1
  , rowsForOutputRead stage4 (some true) keepS keepS keepR halt ].flatten
def description : Description :=
  ThreeTape.description 14 rewind halt rows

syntax "position_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| position_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [
          description, rows, rowsForSourceRead, rowsForOutputRead,
          allReads2, allReadCells, List.find?,
          rewind, header1, header2, header3, header4,
          count1, count2, count3, count4,
          stage1, stage2, stage3, stage4, halt, $lemmas,*])

theorem description_subroutineReady : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem description_supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
def boundaryTape
    (pre tail : List Bool) : Tape Bool :=
  tapeAtCells
    (List.append (pre.reverse.map some) [none])
    (List.append ((false :: tail).map some) [none])

def forwardTape
    (pre tail : List Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append ((List.append pre (false :: tail)).map some) [none])

def sourceCellStartTape
    (n : Nat) (bits suffixTail : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append
      ((List.append boolWordRawBitsDecoderHeaderBits
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          n)).reverse.map some)
      [none])
    (List.append
      ((List.append (cellsCodeBits (bits.map some))
        (false :: suffixTail)).map some)
      [none])
theorem sourceTargetTape_eq_boundaryTape
    (bits suffixTail : Word Bool) :
    structuredBoolWordRawBitsDecoderSourceTargetTape bits suffixTail [] =
      boundaryTape
        (List.append boolWordRawBitsDecoderHeaderBits
          (boolWordRawBitsDecoderEncodedFieldBits bits))
        suffixTail := by
  simp [structuredBoolWordRawBitsDecoderSourceTargetTape, boundaryTape,
    List.map_append, List.reverse_append, List.append_assoc, tapeAtCells]

theorem rewind_step_bit
    (right : List (Option Bool))
    (current outputBit : Bool) (remaining : List Bool)
    (outputLeft outputRight : List (Option Bool)) :
    description.runConfig 1
        (config rewind
          (tapeAtCells
            (List.append (remaining.map some) [none])
            (some current :: right))
          Tape.blank
          (tapeAtCells outputLeft (some outputBit :: outputRight))) =
      match remaining with
      | [] =>
          config rewind
            (tapeAtCells [] (none :: some current :: right))
            Tape.blank
            (tapeAtCells outputLeft (some outputBit :: outputRight))
      | next :: rest =>
          config rewind
            (tapeAtCells
              (List.append (rest.map some) [none])
              (some next :: some current :: right))
            Tape.blank
            (tapeAtCells outputLeft (some outputBit :: outputRight)) := by
  cases remaining with
  | nil =>
      cases current <;> cases outputBit <;>
        position_step [tapeAtCells]
  | cons next rest =>
      cases current <;> cases next <;> cases outputBit <;>
        position_step [tapeAtCells]

theorem rewind_run
    (right : List (Option Bool))
    (current outputBit : Bool) (remaining processed : List Bool)
    (outputLeft outputRight : List (Option Bool)) :
    description.runConfig (remaining.length + 1)
        (config rewind
          (tapeAtCells
            (List.append (remaining.map some) [none])
            (some current ::
              List.append (processed.map some) right))
          Tape.blank
          (tapeAtCells outputLeft (some outputBit :: outputRight))) =
      config rewind
        (tapeAtCells []
          (none ::
            List.append
              ((List.append remaining.reverse
                (current :: processed)).map some)
              right))
        Tape.blank
        (tapeAtCells outputLeft (some outputBit :: outputRight)) := by
  induction remaining generalizing current processed with
  | nil =>
      simpa [List.append_assoc] using
        rewind_step_bit
          (List.append (processed.map some) right)
          current outputBit [] outputLeft outputRight
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [Description.runConfig_add]
      change
        description.runConfig (rest.length + 1)
          (description.runConfig 1
            (config rewind
              (tapeAtCells
                (List.append ((next :: rest).map some) [none])
                (some current ::
                  List.append (processed.map some) right))
              Tape.blank
              (tapeAtCells outputLeft
                (some outputBit :: outputRight)))) = _
      rw [rewind_step_bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih next (current :: processed)
theorem rewind_finish_step
    (first : Bool) (rest tail : List Bool)
    (outputBit : Bool)
    (outputLeft outputRight : List (Option Bool)) :
    description.runConfig 1
        (config rewind
          (tapeAtCells []
            (none ::
              List.append ((first :: rest).map some)
                (some false :: List.append (tail.map some) [none])))
          Tape.blank
          (tapeAtCells outputLeft (some outputBit :: outputRight))) =
      config header1
        (forwardTape (first :: rest) tail)
        Tape.blank
        (tapeAtCells outputLeft (some outputBit :: outputRight)) := by
  cases first <;> cases outputBit <;>
    position_step [forwardTape, tapeAtCells, List.map_append,
      List.append_assoc]

theorem rewind_run_empty
    (right : List (Option Bool))
    (current outputBit : Bool) (remaining : List Bool)
    (outputLeft outputRight : List (Option Bool)) :
    description.runConfig (remaining.length + 1)
        (config rewind
          (tapeAtCells
            (List.append (remaining.map some) [none])
            (some current :: right))
          Tape.blank
          (tapeAtCells outputLeft (some outputBit :: outputRight))) =
      config rewind
        (tapeAtCells []
          (none ::
            List.append
              ((List.append remaining.reverse [current]).map some)
              right))
        Tape.blank
        (tapeAtCells outputLeft (some outputBit :: outputRight)) := by
  simpa using
    rewind_run right current outputBit remaining [] outputLeft outputRight

theorem rewind_boundary_step
    (current outputBit : Bool) (remaining tail : List Bool)
    (outputLeft outputRight : List (Option Bool)) :
    description.runConfig 1
        (config rewind
          (boundaryTape ((current :: remaining).reverse) tail)
          Tape.blank
          (tapeAtCells outputLeft (some outputBit :: outputRight))) =
      config rewind
        (tapeAtCells
          (List.append (remaining.map some) [none])
          (some current ::
            some false :: List.append (tail.map some) [none]))
        Tape.blank
        (tapeAtCells outputLeft (some outputBit :: outputRight)) := by
  cases current <;> cases outputBit <;>
    position_step [boundaryTape, tapeAtCells, List.reverse_cons,
      List.map_append, List.append_assoc]
theorem rewind_from_boundary
    (first outputBit : Bool) (rest tail : List Bool)
    (outputLeft outputRight : List (Option Bool)) :
    description.runConfig ((first :: rest).length + 2)
        (config rewind (boundaryTape (first :: rest) tail)
          Tape.blank
          (tapeAtCells outputLeft (some outputBit :: outputRight))) =
      config header1 (forwardTape (first :: rest) tail)
        Tape.blank
        (tapeAtCells outputLeft (some outputBit :: outputRight)) := by
  cases hrev : (first :: rest).reverse with
  | nil => simp at hrev
  | cons current remaining =>
      have hword : (current :: remaining).reverse = first :: rest := by
        rw [← hrev]
        simp
      have hlen : remaining.length = rest.length := by
        have := congrArg List.length hrev
        simp at this
        lia
      rw [show (first :: rest).length + 2 =
          1 + ((remaining.length + 1) + 1) by simp [hlen]; lia]
      rw [Description.runConfig_add]
      rw [← hword]
      rw [rewind_boundary_step]
      rw [Description.runConfig_add]
      rw [rewind_run_empty
        (some false :: List.append (tail.map some) [none])
        current outputBit remaining outputLeft outputRight]
      rw [show List.append remaining.reverse [current] =
          (current :: remaining).reverse by simp]
      rw [hword]
      rw [rewind_finish_step]

def scanTape
    (left : List (Option Bool)) (bits : List Bool) : Tape Bool :=
  tapeAtCells left (List.append (bits.map some) [none])

def fieldTail
    (bits suffixTail : Word Bool) : List Bool :=
  List.append (cellsCodeBits (bits.map some)) (false :: suffixTail)
theorem header_run_scan
    (following output : List Bool)
    (outputLeft : List (Option Bool)) :
    description.runConfig 4
        (config header1
          (scanTape [none]
            (List.append boolWordRawBitsDecoderHeaderBits following))
          Tape.blank (scanTape outputLeft output)) =
      config count1
        (scanTape
          (List.append (boolWordRawBitsDecoderHeaderBits.reverse.map some)
            [none])
          following)
        Tape.blank (scanTape outputLeft output) := by
  cases output with
  | nil =>
      cases following <;>
        position_step [scanTape, boolWordRawBitsDecoderHeaderBits,
          encodeCodeSymbolAsInput, tapeAtCells, List.reverse_append,
          List.map_append, List.append_assoc]
  | cons outputBit outputRest =>
      cases outputBit <;> cases following <;>
        position_step [scanTape, boolWordRawBitsDecoderHeaderBits,
          encodeCodeSymbolAsInput, tapeAtCells, List.reverse_append,
          List.map_append, List.append_assoc]

theorem count_tick_run
    (sourceLeft outputLeft : List (Option Bool))
    (sourceRest outputRest : List Bool) (outputBit : Bool) :
    description.runConfig 4
        (config count1
          (scanTape sourceLeft
            (List.append [false, false, true, false] sourceRest))
          Tape.blank
          (scanTape outputLeft (outputBit :: outputRest))) =
      config count1
        (scanTape
          (some false :: some true :: some false :: some false ::
            sourceLeft)
          sourceRest)
        Tape.blank
        (scanTape (none :: outputLeft) outputRest) := by
  cases sourceRest <;> cases outputRest <;> cases outputBit <;>
    position_step [scanTape, tapeAtCells, List.append_assoc]

theorem count_done_run
    (sourceLeft outputLeft : List (Option Bool))
    (sourceRest outputRest : List Bool) (outputBit : Bool) :
    description.runConfig 4
        (config count1
          (scanTape sourceLeft
            (List.append [false, false, true, true] sourceRest))
          Tape.blank
          (scanTape outputLeft (outputBit :: outputRest))) =
      config halt
        (scanTape
          (some true :: some true :: some false :: some false ::
            sourceLeft)
          sourceRest)
        Tape.blank
        (scanTape outputLeft (outputBit :: outputRest)) := by
  cases sourceRest <;> cases outputRest <;> cases outputBit <;>
    position_step [scanTape, tapeAtCells, List.append_assoc]
theorem count_run
    (processed sourceRest outputTail : List Bool)
    (bits : Word Bool) (sourceBase outputBase : List (Option Bool))
    (outputHead : Bool) :
    description.runConfig (4 * (bits.length + 1))
        (config count1
          (scanTape
            (List.append (processed.reverse.map some) sourceBase)
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                bits.length)
              sourceRest))
          Tape.blank
          (scanTape outputBase
            (List.append bits (outputHead :: outputTail)))) =
      config halt
        (scanTape
          (List.append
            ((List.append processed
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                bits.length)).reverse.map some)
            sourceBase)
          sourceRest)
        Tape.blank
        (scanTape
          (List.append
            (List.replicate bits.length (none : Option Bool)) outputBase)
          (outputHead :: outputTail)) := by
  induction bits generalizing processed outputBase with
  | nil =>
      simpa using
        count_done_run
          (List.append (processed.reverse.map some) sourceBase)
          outputBase sourceRest outputTail outputHead
  | cons bit rest ih =>
      rw [show 4 * ((bit :: rest).length + 1) =
          4 + 4 * (rest.length + 1) by simp; lia]
      rw [Description.runConfig_add]
      change
        description.runConfig (4 * (rest.length + 1))
          (description.runConfig 4
            (config count1
              (scanTape
                (List.append (processed.reverse.map some) sourceBase)
                (List.append [false, false, true, false]
                  (List.append
                    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      rest.length)
                    sourceRest)))
              Tape.blank
              (scanTape outputBase
                (bit :: List.append rest (outputHead :: outputTail))))) = _
      rw [count_tick_run]
      have hsourceLeft :
          some false :: some true :: some false :: some false ::
              List.append (processed.reverse.map some) sourceBase =
            List.append
              ((List.append processed [false, false, true, false]).reverse.map
                some)
              sourceBase := by
        simp [List.reverse_append, List.map_append, List.append_assoc]
      rw [hsourceLeft]
      have hih :=
        ih (List.append processed [false, false, true, false])
          (none :: outputBase)
      rw [FoC.Computability.CommonGround.FiniteTransducers.replicate_none_append_none_cons]
        at hih
      simpa [List.reverse_cons, List.map_append,
        List.replicate_succ, List.append_assoc] using hih

def decoderPrefix (bits : Word Bool) : List Bool :=
  List.append boolWordRawBitsDecoderHeaderBits
    (boolWordRawBitsDecoderEncodedFieldBits bits)
def positionFuel (bits : Word Bool) : Nat :=
  (decoderPrefix bits).length + 2 +
    (4 + 4 * (bits.length + 1))

theorem sourceTargetTape_eq_boundaryTape_decoderPrefix
    (bits suffixTail : Word Bool) :
    structuredBoolWordRawBitsDecoderSourceTargetTape bits suffixTail [] =
      boundaryTape (decoderPrefix bits) suffixTail := by
  simpa [decoderPrefix] using
    sourceTargetTape_eq_boundaryTape bits suffixTail

theorem decoderPrefix_eq_false_cons (bits : Word Bool) :
    decoderPrefix bits =
      false ::
        List.append [false, false, false]
          (boolWordRawBitsDecoderEncodedFieldBits bits) := by
  rfl
theorem forwardTape_decoderPrefix_eq_scanTape
    (bits suffixTail : Word Bool) :
    forwardTape (decoderPrefix bits) suffixTail =
      scanTape [none]
        (List.append boolWordRawBitsDecoderHeaderBits
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              bits.length)
            (fieldTail bits suffixTail))) := by
  simp [forwardTape, scanTape, decoderPrefix, fieldTail,
    boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
    List.append_assoc, tapeAtCells]

theorem count_target_source_eq_cellStart
    (bits suffixTail : Word Bool) :
    scanTape
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            bits.length).reverse.map some)
          (List.append
            (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none]))
        (fieldTail bits suffixTail) =
      sourceCellStartTape bits.length bits suffixTail := by
  simp [scanTape, sourceCellStartTape, fieldTail,
    List.reverse_append, List.map_append, List.append_assoc, tapeAtCells]

theorem position_erase_run_with_outputBase
    (bits suffixTail outputRest : Word Bool) (stage : Nat)
    (outputBase : List (Option Bool)) :
    description.runConfig (positionFuel bits)
        (config rewind
          (structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail [])
          Tape.blank
          (scanTape outputBase
            (List.append bits
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage)
                outputRest)))) =
      config halt
        (sourceCellStartTape bits.length bits suffixTail)
        Tape.blank
        (scanTape
          (List.append
            (List.replicate bits.length (none : Option Bool)) outputBase)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage)
            outputRest)) := by
  rcases stageNatBits_cons_false stage with
    ⟨stageTail, hstage⟩
  have houtput :
      exists outputBit outputRight,
        scanTape outputBase
            (List.append bits
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage)
                outputRest)) =
          tapeAtCells outputBase (some outputBit :: outputRight) := by
    rw [hstage]
    cases bits with
    | nil =>
        refine ⟨false,
          List.append ((List.append stageTail outputRest).map some) [none], ?_⟩
        simp [scanTape, tapeAtCells, List.map_append, List.append_assoc]
    | cons bit rest =>
        refine ⟨bit,
          List.append
            ((List.append rest
              (List.append (false :: stageTail) outputRest)).map some)
            [none], ?_⟩
        simp [scanTape, tapeAtCells, List.map_append, List.append_assoc]
  rcases houtput with ⟨outputBit, outputRight, houtput⟩
  rw [positionFuel]
  rw [Description.runConfig_add]
  rw [sourceTargetTape_eq_boundaryTape_decoderPrefix]
  rw [houtput]
  rw [decoderPrefix_eq_false_cons]
  rw [rewind_from_boundary]
  rw [← decoderPrefix_eq_false_cons bits]
  rw [← houtput]
  rw [forwardTape_decoderPrefix_eq_scanTape]
  rw [Description.runConfig_add]
  rw [header_run_scan]
  rw [hstage]
  have hcount :=
    count_run ([] : List Bool) (fieldTail bits suffixTail)
      (List.append stageTail outputRest) bits
      (List.append (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none])
      outputBase false
  rw [← count_target_source_eq_cellStart bits suffixTail]
  simpa [hstage,
    List.reverse_append, List.map_append,
    List.append_assoc] using hcount

end AcceptConfigInserter
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
