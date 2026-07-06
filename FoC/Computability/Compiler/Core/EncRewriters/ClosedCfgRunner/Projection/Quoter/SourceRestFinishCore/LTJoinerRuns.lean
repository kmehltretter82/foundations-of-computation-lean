import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTEmitterRuns

set_option doc.verso true

/-!
# Source-rest live-tail joiner runs

This module contains the reusable tape-shape facts and family contracts for
joining the emitted source-rest live tail back into the assembly target.  The
arbitrary stage/source joiner impossibility result is kept here as a guardrail
next to the joiner source and target shapes.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

def MixedParserStackWholeSourceAfterRawTailScanTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  match assemblySourceRestFinishRawTailBits sourceRestBits stage with
  | [] =>
      MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage
  | head :: rawTailRest =>
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
        ((List.append
          (MixedParserStackRewriterLengthHeader
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage)
            sourceRestBits)
          (MixedParserStackRewriterPrefixQuote
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage))).reverse.map some)
        0 head rawTailRest
        (List.append
          ((preservingCellPassCellBits sourceRestBits).map some)
          [none])

theorem rightBlankGapPayloadScanDescription_haltsFrom_prefixQuotedSeparatedTape_to_afterRawTailScan
    (w sourceRestBits : Word Bool) (stage : Nat) :
    CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription.HaltsFromTape
      (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage)
      (MixedParserStackWholeSourceAfterRawTailScanTape
        w sourceRestBits stage) := by
  rcases assemblySourceRestFinishRawTailBits_cons_exists
      sourceRestBits stage with
    ⟨head, rawTailRest, hraw⟩
  rw [MixedParserStackWholeSourceAfterRawTailScanTape, hraw]
  exact
    rightBlankGapPayloadScanDescription_haltsFrom_prefixQuotedSeparatedTape
      w sourceRestBits stage head rawTailRest hraw

theorem rightBlankGapPayloadScanTargetTape_move_left_move_right
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
            baseLeft gap current payloadRest padding)) =
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
        baseLeft gap current payloadRest padding := by
  rw [CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape]
  rw [show
      List.append ((current :: payloadRest).reverse.map some)
          (List.append (List.replicate gap (none : Option Bool)) baseLeft) =
        List.append (payloadRest.reverse.map some)
          (some current ::
            List.append (List.replicate gap (none : Option Bool))
              baseLeft) by
    simp [List.reverse_cons, List.map_append, List.append_assoc]]
  rw [CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_append_cons
    (payloadRest.reverse.map some)
    (List.append (List.replicate gap (none : Option Bool)) baseLeft)
    (none :: padding)
    (some current)]

theorem rightBlankGapPayloadScanTargetTape_defaultedCells
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
            baseLeft gap current payloadRest padding)) =
      List.append (List.map optionBitDefaultFalse baseLeft.reverse)
        (List.append
          (List.replicate gap false)
          (List.append (current :: payloadRest)
            (false :: List.map optionBitDefaultFalse padding))) := by
  rw [CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape]
  rw [show
      List.append ((current :: payloadRest).reverse.map some)
          (List.append (List.replicate gap (none : Option Bool)) baseLeft) =
        List.append (payloadRest.reverse.map some)
          (some current ::
            List.append (List.replicate gap (none : Option Bool))
              baseLeft) by
    simp [List.reverse_cons, List.map_append, List.append_assoc]]
  rw [CommonGround.FiniteTransducers.tapeAtCells_move_left_cells_append_cons_right_cons
    (payloadRest.reverse.map some)
    (List.append (List.replicate gap (none : Option Bool)) baseLeft)
    padding (some current) none]
  simp [List.reverse_append, List.map_reverse, List.map_append,
    List.append_assoc, optionBitDefaultFalse, Function.comp_def]

theorem rightBlankGapPayloadScanTargetTape_cells
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.cells
        (CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
          baseLeft gap current payloadRest padding) =
      List.append baseLeft.reverse
        (List.append (List.replicate gap (none : Option Bool))
          (some current ::
            List.append (payloadRest.map some) (none :: padding))) := by
  rw [CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape]
  rw [show
      List.append ((current :: payloadRest).reverse.map some)
          (List.append (List.replicate gap (none : Option Bool)) baseLeft) =
        List.append (payloadRest.reverse.map some)
          (some current ::
            List.append (List.replicate gap (none : Option Bool))
              baseLeft) by
    simp [List.reverse_cons, List.map_append, List.append_assoc]]
  rw [CommonGround.FiniteTransducers.tapeAtCells_move_left_cells_append_cons_right_cons
    (payloadRest.reverse.map some)
    (List.append (List.replicate gap (none : Option Bool)) baseLeft)
    padding (some current) none]
  simp [List.reverse_append, List.map_reverse, List.append_assoc]

theorem MixedParserStackWholeSourceAfterRawTailScanTape_move_right_eq_rightEndSource
    (w sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (rawTailRest : Word Bool)
    (hraw :
      assemblySourceRestFinishRawTailBits sourceRestBits stage =
        head :: rawTailRest) :
    Tape.move Direction.right
        (MixedParserStackWholeSourceAfterRawTailScanTape
          w sourceRestBits stage) =
      CommonGround.FiniteTransducers.rightEndCompactionSourceTapeWithRightPadding
        (List.append
          (((List.append
            (MixedParserStackRewriterLengthHeader
              (assemblySourceRestFinishParserPrefixCells w)
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              sourceRestBits)
            (MixedParserStackRewriterPrefixQuote
              (assemblySourceRestFinishParserPrefixCells w)
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage))).reverse.map some).reverse)
          ((head :: rawTailRest).map some))
        (List.append
          ((preservingCellPassCellBits sourceRestBits).map some)
          [none]) := by
  rw [MixedParserStackWholeSourceAfterRawTailScanTape, hraw]
  simp only
  rw [CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape,
    CommonGround.FiniteTransducers.rightEndCompactionSourceTapeWithRightPadding]
  rw [show
      (List.append
          (((List.append
            (MixedParserStackRewriterLengthHeader
              (assemblySourceRestFinishParserPrefixCells w)
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              sourceRestBits)
            (MixedParserStackRewriterPrefixQuote
              (assemblySourceRestFinishParserPrefixCells w)
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage))).reverse.map some).reverse)
          ((head :: rawTailRest).map some)).reverse =
        List.append (rawTailRest.reverse.map some)
          (some head ::
            ((List.append
              (MixedParserStackRewriterLengthHeader
                (assemblySourceRestFinishParserPrefixCells w)
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage)
                sourceRestBits)
              (MixedParserStackRewriterPrefixQuote
                (assemblySourceRestFinishParserPrefixCells w)
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage))).reverse.map some)) by
    simp [List.reverse_append, List.map_reverse, List.append_assoc]]
  simpa [List.reverse_cons, List.map_append, List.map_reverse,
    List.append_assoc] using
    CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_append_cons
      (rawTailRest.reverse.map some)
      ((List.append
        (MixedParserStackRewriterLengthHeader
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits)
        (MixedParserStackRewriterPrefixQuote
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage))).reverse.map some)
      (none ::
        List.append
          ((preservingCellPassCellBits sourceRestBits).map some)
          [none])
      (some head)

theorem MixedParserStackWholeSourceAfterRawTailScanTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (MixedParserStackWholeSourceAfterRawTailScanTape
            w sourceRestBits stage)) =
      MixedParserStackWholeSourceAfterRawTailScanTape
        w sourceRestBits stage := by
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  rw [MixedParserStackWholeSourceAfterRawTailScanTape,
    assemblySourceRestFinishRawTailBits, hstage]
  exact
    rightBlankGapPayloadScanTargetTape_move_left_move_right
      ((List.append
        (MixedParserStackRewriterLengthHeader
          (assemblySourceRestFinishParserPrefixCells w)
          (head :: next :: right)
          sourceRestBits)
        (MixedParserStackRewriterPrefixQuote
          (assemblySourceRestFinishParserPrefixCells w)
          (head :: next :: right))).reverse.map some)
      0 head (next :: List.append right sourceRestBits)
      (List.append
        ((preservingCellPassCellBits sourceRestBits).map some)
        [none])

def mixedOptionCellQuoteLiveTailSeparatedTape
    (emittedPrefix rawTail quoteRest : Word Bool) : Tape Bool :=
  match rawTail with
  | [] =>
      tapeAtCells
        (emittedPrefix.reverse.map some)
        (none :: List.append (quoteRest.map some) [none])
  | head :: rawTailRest =>
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
        (emittedPrefix.reverse.map some)
        0 head rawTailRest
        (List.append (quoteRest.map some) [none])

def mixedOptionCellQuoteLiveTailJoinedTape
    (emittedPrefix rawTail quoteRest : Word Bool) : Tape Bool :=
  tapeAtCells
    ((List.append emittedPrefix quoteRest).reverse.map some)
    (rawTail.map some)

theorem mixedOptionCellQuoteLiveTailSeparatedTape_cells_cons
    (emittedPrefix quoteRest : Word Bool)
    (head : Bool) (rawTailRest : Word Bool) :
    Tape.cells
        (mixedOptionCellQuoteLiveTailSeparatedTape
          emittedPrefix (head :: rawTailRest) quoteRest) =
      List.append (emittedPrefix.map some)
        (List.append ((head :: rawTailRest).map some)
          (none :: List.append (quoteRest.map some) [none])) := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape]
  rw [rightBlankGapPayloadScanTargetTape_cells]
  simp [List.map_reverse]

theorem mixedOptionCellQuoteLiveTailSeparatedTape_eq_rawTailLast
    (emittedPrefix rawTailInit quoteRest : Word Bool) (last : Bool) :
    mixedOptionCellQuoteLiveTailSeparatedTape
        emittedPrefix (List.append rawTailInit [last]) quoteRest =
      tapeAtCells
        (List.append (rawTailInit.reverse.map some)
          (emittedPrefix.reverse.map some))
        (some last :: none ::
          List.append (quoteRest.map some) [none]) := by
  cases rawTailInit with
  | nil =>
      simp [mixedOptionCellQuoteLiveTailSeparatedTape,
        CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape,
        tapeAtCells, CommonGround.FiniteTransducers.tapeAtCells,
        Tape.move, Tape.moveLeft]
  | cons head tail =>
      simp [mixedOptionCellQuoteLiveTailSeparatedTape,
        CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape,
        tapeAtCells, CommonGround.FiniteTransducers.tapeAtCells,
        Tape.move, Tape.moveLeft, List.reverse_append, List.map_append,
        List.append_assoc]

theorem mixedOptionCellQuoteLiveTailSeparatedTape_move_right_rawTailLast
    (emittedPrefix rawTailInit quoteRest : Word Bool) (last : Bool) :
    Tape.move Direction.right
        (mixedOptionCellQuoteLiveTailSeparatedTape
          emittedPrefix (List.append rawTailInit [last]) quoteRest) =
      tapeAtCells
        (some last ::
          List.append (rawTailInit.reverse.map some)
            (emittedPrefix.reverse.map some))
        (none :: List.append (quoteRest.map some) [none]) := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_eq_rawTailLast]
  simp [tapeAtCells, Tape.move, Tape.moveRight]

theorem mixedOptionCellQuoteLiveTailSeparatedTape_move_right_right_rawTailLast_preservingCons
    (emittedPrefix rawTailInit sourceRestTail : Word Bool)
    (last bit : Bool) :
    Tape.move Direction.right
        (Tape.move Direction.right
          (mixedOptionCellQuoteLiveTailSeparatedTape
            emittedPrefix (List.append rawTailInit [last])
            (preservingCellPassCellBits (bit :: sourceRestTail)))) =
      tapeAtCells
        (none :: some last ::
          List.append (rawTailInit.reverse.map some)
            (emittedPrefix.reverse.map some))
        (some false :: some true :: some bit ::
          some (if bit then false else true) ::
            List.append
              ((preservingCellPassCellBits sourceRestTail).map some)
              [none]) := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_move_right_rawTailLast]
  rw [preservingCellPassCellBits_cons_explicit_map_some]
  simp [tapeAtCells, Tape.move, Tape.moveRight]

theorem mixedOptionCellQuoteLiveTailSeparatedTape_move_right_right_assembly_sourceRestCons
    (w sourceRestTail : Word Bool) (bit : Bool) (stage : Nat) :
    exists rawTailInit : Word Bool,
    exists last : Bool,
      assemblySourceRestFinishRawTailBits (bit :: sourceRestTail) stage =
        List.append rawTailInit [last] ∧
      Tape.move Direction.right
          (Tape.move Direction.right
            (mixedOptionCellQuoteLiveTailSeparatedTape
              (assemblySourceRestFinishPrefixQuoteOutputBits
                w (bit :: sourceRestTail) stage)
              (assemblySourceRestFinishRawTailBits
                (bit :: sourceRestTail) stage)
              (preservingCellPassCellBits (bit :: sourceRestTail)))) =
        tapeAtCells
          (none :: some last ::
            List.append (rawTailInit.reverse.map some)
              ((assemblySourceRestFinishPrefixQuoteOutputBits
                w (bit :: sourceRestTail) stage).reverse.map some))
          (some false :: some true :: some bit ::
            some (if bit then false else true) ::
              List.append
                ((preservingCellPassCellBits sourceRestTail).map some)
                [none]) := by
  rcases assemblySourceRestFinishRawTailBits_lastSplit_exists
      (bit :: sourceRestTail) stage with
    ⟨rawTailInit, last, hraw⟩
  refine ⟨rawTailInit, last, hraw, ?_⟩
  rw [hraw]
  exact
    mixedOptionCellQuoteLiveTailSeparatedTape_move_right_right_rawTailLast_preservingCons
      (assemblySourceRestFinishPrefixQuoteOutputBits
        w (bit :: sourceRestTail) stage)
      rawTailInit sourceRestTail last bit

theorem mixedOptionCellQuoteLiveTailJoinedTape_cells_cons
    (emittedPrefix quoteRest : Word Bool)
    (head : Bool) (rawTailRest : Word Bool) :
    Tape.cells
        (mixedOptionCellQuoteLiveTailJoinedTape
          emittedPrefix (head :: rawTailRest) quoteRest) =
      List.append (emittedPrefix.map some)
        (List.append (quoteRest.map some)
          ((head :: rawTailRest).map some)) := by
  cases rawTailRest <;>
    simp [mixedOptionCellQuoteLiveTailJoinedTape,
      tapeAtCells, Tape.cells, List.map_reverse, List.map_append,
      List.append_assoc]

theorem mixedOptionCellQuoteLiveTailSeparatedTape_defaultedCells
    (emittedPrefix rawTail quoteRest : Word Bool) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailSeparatedTape
            emittedPrefix rawTail quoteRest)) =
      List.append emittedPrefix
        (List.append rawTail
          (false :: List.append quoteRest [false])) := by
  cases rawTail with
  | nil =>
      simp [mixedOptionCellQuoteLiveTailSeparatedTape,
        tapeAtCells, Tape.cells, List.map_reverse,
        List.map_append, List.map_map, optionBitDefaultFalse,
        optionBitDefaultFalse_map_some]
  | cons head rawTailRest =>
      rw [mixedOptionCellQuoteLiveTailSeparatedTape]
      rw [rightBlankGapPayloadScanTargetTape_defaultedCells]
      simp [List.map_reverse, List.map_map,
        optionBitDefaultFalse, optionBitDefaultFalse_map_some]

theorem mixedOptionCellQuoteLiveTailJoinedTape_defaultedCells_cons
    (emittedPrefix quoteRest : Word Bool)
    (head : Bool) (rawTailRest : Word Bool) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailJoinedTape
            emittedPrefix (head :: rawTailRest) quoteRest)) =
      List.append emittedPrefix
        (List.append quoteRest (head :: rawTailRest)) := by
  cases rawTailRest <;>
    simp [mixedOptionCellQuoteLiveTailJoinedTape,
      tapeAtCells, Tape.cells, List.map_reverse, List.map_append,
      List.map_map, optionBitDefaultFalse,
      optionBitDefaultFalse_map_some, List.append_assoc]

theorem MixedParserStackWholeSourceAfterRawTailScanTape_eq_mixedOptionCellQuoteLiveTailSeparatedTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackWholeSourceAfterRawTailScanTape
        w sourceRestBits stage =
      mixedOptionCellQuoteLiveTailSeparatedTape
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) := by
  rw [MixedParserStackWholeSourceAfterRawTailScanTape]
  rw [MixedParserStackRewriterPrefixQuote_eq_assemblyQuotedPrefix]
  rw [MixedParserStackRewriterLengthHeader_eq_assemblyLengthHeader]
  rw [assemblySourceRestFinishPrefixQuoteOutputBits]
  cases hraw :
      assemblySourceRestFinishRawTailBits sourceRestBits stage with
  | nil =>
      rcases assemblySourceRestFinishRawTailBits_cons_exists
          sourceRestBits stage with
        ⟨head, rawTailRest, hcons⟩
      rw [hraw] at hcons
      contradiction
  | cons head rawTailRest =>
      simp [mixedOptionCellQuoteLiveTailSeparatedTape]

theorem mixedOptionCellQuoteLiveTailSeparatedTape_cells_assembly
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) =
      List.append
        ((assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage).map some)
        (List.append
          ((assemblySourceRestFinishRawTailBits
            sourceRestBits stage).map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) := by
  rcases assemblySourceRestFinishRawTailBits_cons_exists
      sourceRestBits stage with
    ⟨head, rawTailRest, hraw⟩
  rw [hraw]
  exact
    mixedOptionCellQuoteLiveTailSeparatedTape_cells_cons
      (assemblySourceRestFinishPrefixQuoteOutputBits
        w sourceRestBits stage)
      (preservingCellPassCellBits sourceRestBits)
      head rawTailRest

theorem mixedOptionCellQuoteLiveTailJoinedTape_cells_assembly
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) =
      List.append
        ((assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage).map some)
        (List.append
          ((preservingCellPassCellBits sourceRestBits).map some)
          ((assemblySourceRestFinishRawTailBits
            sourceRestBits stage).map some)) := by
  rcases assemblySourceRestFinishRawTailBits_cons_exists
      sourceRestBits stage with
    ⟨head, rawTailRest, hraw⟩
  rw [hraw]
  exact
    mixedOptionCellQuoteLiveTailJoinedTape_cells_cons
      (assemblySourceRestFinishPrefixQuoteOutputBits
        w sourceRestBits stage)
      (preservingCellPassCellBits sourceRestBits)
      head rawTailRest

theorem mixedOptionCellQuoteLiveTailJoinedTape_eq_assembly_stageSplit
    (w sourceRestBits : Word Bool) (stage : Nat) :
    mixedOptionCellQuoteLiveTailJoinedTape
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) =
      tapeAtCells
        ((List.append
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)).reverse.map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (sourceRestBits.map some)) := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape,
    assemblySourceRestFinishRawTailBits]
  simp [List.map_append]

theorem mixedOptionCellQuoteLiveTailJoinedTape_eq_assemblyQuoteRestJoinedTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    mixedOptionCellQuoteLiveTailJoinedTape
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) =
      assemblySourceRestFinishQuoteRestJoinedTape
        w sourceRestBits stage := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape,
    assemblySourceRestFinishQuoteRestJoinedTape]

theorem mixedOptionCellQuoteLiveTailSeparatedTape_defaultedCells_assembly
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailSeparatedTape
            (assemblySourceRestFinishPrefixQuoteOutputBits
              w sourceRestBits stage)
            (assemblySourceRestFinishRawTailBits sourceRestBits stage)
            (preservingCellPassCellBits sourceRestBits))) =
      List.append
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (List.append
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (false ::
            List.append (preservingCellPassCellBits sourceRestBits)
              [false])) := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_defaultedCells]

theorem mixedOptionCellQuoteLiveTailJoinedTape_defaultedCells_assembly
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailJoinedTape
            (assemblySourceRestFinishPrefixQuoteOutputBits
              w sourceRestBits stage)
            (assemblySourceRestFinishRawTailBits sourceRestBits stage)
            (preservingCellPassCellBits sourceRestBits))) =
      List.append
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (List.append
          (preservingCellPassCellBits sourceRestBits)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)) := by
  rcases assemblySourceRestFinishRawTailBits_cons_exists
      sourceRestBits stage with
    ⟨head, rawTailRest, hraw⟩
  rw [hraw]
  exact
    mixedOptionCellQuoteLiveTailJoinedTape_defaultedCells_cons
      (assemblySourceRestFinishPrefixQuoteOutputBits
        w sourceRestBits stage)
      (preservingCellPassCellBits sourceRestBits)
      head rawTailRest

theorem assemblySourceRestLiveTailJoinerSeparatedTape_eq_afterRawTailScanTape
    (p : AssemblySourceRestLiveTailEmitterParam) :
    mixedOptionCellQuoteLiveTailSeparatedTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) =
      MixedParserStackWholeSourceAfterRawTailScanTape
        p.w p.sourceRestBits p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rw [assemblySourceRestLiveTailEmitterEmittedPrefix,
        assemblySourceRestLiveTailEmitterRawTail,
        assemblySourceRestLiveTailEmitterQuoteRest]
      exact
        (MixedParserStackWholeSourceAfterRawTailScanTape_eq_mixedOptionCellQuoteLiveTailSeparatedTape
          w sourceRestBits stage).symm

theorem assemblySourceRestLiveTailJoinerJoinedTape_eq_quoteRestJoinedTape
    (p : AssemblySourceRestLiveTailEmitterParam) :
    mixedOptionCellQuoteLiveTailJoinedTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) =
      assemblySourceRestFinishQuoteRestJoinedTape
        p.w p.sourceRestBits p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rw [assemblySourceRestLiveTailEmitterEmittedPrefix,
        assemblySourceRestLiveTailEmitterRawTail,
        assemblySourceRestLiveTailEmitterQuoteRest]
      exact
        mixedOptionCellQuoteLiveTailJoinedTape_eq_assemblyQuoteRestJoinedTape
          w sourceRestBits stage

theorem assemblySourceRestLiveTailJoinerJoinedTape_eq_targetTape
    (p : AssemblySourceRestLiveTailEmitterParam) :
    mixedOptionCellQuoteLiveTailJoinedTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) =
      assemblySourceRestFinishTargetTape
        p.w p.sourceRestBits p.stage := by
  rw [
    assemblySourceRestLiveTailJoinerJoinedTape_eq_quoteRestJoinedTape,
    assemblySourceRestFinishQuoteRestJoinedTape_eq_targetTape]

def mixedOptionCellQuoteLiveTailStageSourceRawTail
    (sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      stage)
    sourceRestBits

def MixedOptionCellQuoteLiveTailStageSourceJoinerSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (emittedPrefix sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (mixedOptionCellQuoteLiveTailSeparatedTape
          emittedPrefix
          (mixedOptionCellQuoteLiveTailStageSourceRawTail
            sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits))
        (mixedOptionCellQuoteLiveTailJoinedTape
          emittedPrefix
          (mixedOptionCellQuoteLiveTailStageSourceRawTail
            sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits))

def MixedOptionCellQuoteLiveTailStageSourceJoinerConstruction :
    Prop :=
  exists finish : MachineDescription,
    MixedOptionCellQuoteLiveTailStageSourceJoinerSpec finish

theorem mixedOptionCellQuoteLiveTailStageSourceJoiner_source_ambiguous :
    mixedOptionCellQuoteLiveTailSeparatedTape
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits
        (mixedOptionCellQuoteLiveTailStageSourceRawTail [false] 0)
        (preservingCellPassCellBits [false]) =
      mixedOptionCellQuoteLiveTailSeparatedTape
        []
        (mixedOptionCellQuoteLiveTailStageSourceRawTail [false] 1)
        (preservingCellPassCellBits [false]) := by
  decide

theorem mixedOptionCellQuoteLiveTailStageSourceJoiner_target_not_ambiguous :
    mixedOptionCellQuoteLiveTailJoinedTape
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits
        (mixedOptionCellQuoteLiveTailStageSourceRawTail [false] 0)
        (preservingCellPassCellBits [false]) ≠
      mixedOptionCellQuoteLiveTailJoinedTape
        []
        (mixedOptionCellQuoteLiveTailStageSourceRawTail [false] 1)
        (preservingCellPassCellBits [false]) := by
  decide

theorem not_MixedOptionCellQuoteLiveTailStageSourceJoinerSpec
    (finish : MachineDescription) :
    ¬ MixedOptionCellQuoteLiveTailStageSourceJoinerSpec finish := by
  intro hfinish
  have hleft :=
    hfinish.right
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits
      [false] 0
  have hright :=
    hfinish.right [] [false] 1
  have hright_from_left :
      finish.HaltsFromTape
        (mixedOptionCellQuoteLiveTailSeparatedTape
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits
          (mixedOptionCellQuoteLiveTailStageSourceRawTail [false] 0)
          (preservingCellPassCellBits [false]))
        (mixedOptionCellQuoteLiveTailJoinedTape
          []
          (mixedOptionCellQuoteLiveTailStageSourceRawTail [false] 1)
          (preservingCellPassCellBits [false])) := by
    simpa [
      mixedOptionCellQuoteLiveTailStageSourceJoiner_source_ambiguous]
      using hright
  have htargets :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hfinish.left.right hleft hright_from_left
  exact
    mixedOptionCellQuoteLiveTailStageSourceJoiner_target_not_ambiguous
      htargets

theorem not_MixedOptionCellQuoteLiveTailStageSourceJoinerConstruction :
    ¬ MixedOptionCellQuoteLiveTailStageSourceJoinerConstruction := by
  intro hconstruction
  rcases hconstruction with ⟨finish, hfinish⟩
  exact
    not_MixedOptionCellQuoteLiveTailStageSourceJoinerSpec finish hfinish

def MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits))
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits))

def MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestSpec finish

def MixedOptionCellQuoteLiveTailJoinerFamilySpec
    {ι : Type}
    (emittedPrefix rawTail quoteRest : ι -> Word Bool)
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall p : ι,
      finish.HaltsFromTape
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (emittedPrefix p) (rawTail p) (quoteRest p))
        (mixedOptionCellQuoteLiveTailJoinedTape
          (emittedPrefix p) (rawTail p) (quoteRest p))

def MixedOptionCellQuoteLiveTailJoinerFamilyConstruction
    {ι : Type}
    (emittedPrefix rawTail quoteRest : ι -> Word Bool) : Prop :=
  exists finish : MachineDescription,
    MixedOptionCellQuoteLiveTailJoinerFamilySpec
      emittedPrefix rawTail quoteRest finish

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
