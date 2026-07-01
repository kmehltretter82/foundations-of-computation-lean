import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.Construction
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.JoinerBridge
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Compaction
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.GapPayloadScan

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

def assemblySourceRestReusableQuoteAfterSourceRestScanTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  scanRightToBlankLeftHaltTapeWithRight
    (List.append (assemblySourceRestBoundaryLeftRev w stage) [none])
    sourceRestBits
    (List.append
      ((preservingCellPassCellBits sourceRestBits).map some)
      [none])

theorem
    scanRightToBlankLeftDescription_haltsFrom_defaultedSourceRestBoundary_to_afterSourceRest
    (w sourceRestBits : Word Bool) (stage : Nat) :
    scanRightToBlankLeftDescription.HaltsFromTape
      (MixedParserStackRewriterDefaultedSourceRestBoundaryTape
        w sourceRestBits
        (preservingCellPassCellBits sourceRestBits)
        stage)
      (assemblySourceRestReusableQuoteAfterSourceRestScanTape
        w sourceRestBits stage) := by
  rw [MixedParserStackRewriterDefaultedSourceRestBoundaryTape,
    assemblySourceRestReusableQuoteAfterSourceRestScanTape]
  exact
    scanRightToBlankLeftDescription_haltsFromTape_withRight
      (List.append (assemblySourceRestBoundaryLeftRev w stage) [none])
      sourceRestBits
      (List.append
        ((preservingCellPassCellBits sourceRestBits).map some)
        [none])

theorem assemblySourceRestReusableQuoteAfterSourceRestScanTape_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.right
        (assemblySourceRestReusableQuoteAfterSourceRestScanTape
          w sourceRestBits stage) =
      tapeAtCells
        (List.append (sourceRestBits.reverse.map some)
          (List.append (assemblySourceRestBoundaryLeftRev w stage)
            [none]))
        (none :: List.append
          ((preservingCellPassCellBits sourceRestBits).map some)
          [none]) := by
  rw [assemblySourceRestReusableQuoteAfterSourceRestScanTape,
    scanRightToBlankLeftHaltTapeWithRight]
  generalize hleft :
      (List.map some sourceRestBits).reverse ++
        (assemblySourceRestBoundaryLeftRev w stage ++ [none]) =
        leftCells
  cases leftCells with
  | nil =>
      simp at hleft
  | cons cell rest =>
      simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
        hleft]

theorem
    assemblySourceRestReusableQuoteAfterSourceRestScanTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (assemblySourceRestReusableQuoteAfterSourceRestScanTape
            w sourceRestBits stage)) =
      assemblySourceRestReusableQuoteAfterSourceRestScanTape
        w sourceRestBits stage := by
  rw [assemblySourceRestReusableQuoteAfterSourceRestScanTape,
    scanRightToBlankLeftHaltTapeWithRight]
  generalize hleft :
      (List.map some sourceRestBits).reverse ++
        (assemblySourceRestBoundaryLeftRev w stage ++ [none]) =
        leftCells
  cases leftCells with
  | nil =>
      simp at hleft
  | cons cell rest =>
      simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
        hleft]

theorem assemblySourceRestReusableQuoteAfterSourceRestScanTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestReusableQuoteAfterSourceRestScanTape
          w sourceRestBits stage) =
      none ::
        List.append
          (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
          (List.append (sourceRestBits.map some)
            (none ::
              List.append
                ((preservingCellPassCellBits sourceRestBits).map some)
                [none])) := by
  rw [assemblySourceRestReusableQuoteAfterSourceRestScanTape,
    scanRightToBlankLeftHaltTapeWithRight]
  have hleft :
      List.append
          (sourceRestBits.reverse.map some)
          (List.append (assemblySourceRestBoundaryLeftRev w stage) [none])
        ≠ [] := by
    cases sourceRestBits <;> simp
  rw [tapeAtCells_move_left_none_cons_cells_of_left_ne_nil _ _ hleft]
  simp [List.reverse_append, List.map_reverse, List.append_assoc]

theorem assemblySourceRestReusableQuoteAfterSourceRestScanTape_defaultedCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestReusableQuoteAfterSourceRestScanTape
            w sourceRestBits stage)) =
      false ::
        List.append
          (assemblySourceRestFinishSourcePrefixBits w stage)
          (List.append sourceRestBits
            (false ::
              List.append (preservingCellPassCellBits sourceRestBits)
                [false])) := by
  rw [assemblySourceRestReusableQuoteAfterSourceRestScanTape_cells]
  have hprefix :=
    assemblySourceRestBoundaryLeftRev_defaultBits_eq_sourcePrefix
      w stage
  simp [List.map_append, List.map_map, optionBitDefaultFalse,
    optionBitDefaultFalse_map_some, hprefix]

theorem
    assemblySourceRestReusableQuoteAfterSourceRestScanTape_eq_mixedParserStackSource_withSentinel
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestReusableQuoteAfterSourceRestScanTape
        w sourceRestBits stage =
      MixedParserStackRewriterSourceTape
        (none :: assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        (preservingCellPassCellBits sourceRestBits) := by
  rw [assemblySourceRestReusableQuoteAfterSourceRestScanTape,
    MixedParserStackRewriterSourceTape,
    scanRightToBlankLeftHaltTapeWithRight,
    scanLeftToBlankLeftHaltTape]
  cases w with
  | nil =>
      simp [assemblySourceRestBoundaryLeftRev,
        assemblySourceRestFinishParserPrefixCells,
        List.reverse_append, List.map_reverse, List.append_assoc]
  | cons b rest =>
      simp [assemblySourceRestBoundaryLeftRev,
        assemblySourceRestFinishParserPrefixCells,
        List.reverse_append, List.map_reverse, List.append_assoc]

theorem assemblySourceRestFinishTargetTape_eq_rawBoolSourceStartTargetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetTape w sourceRestBits stage =
      assemblySourceRestFinishRawBoolSourceStartTargetTape
        w sourceRestBits stage := by
  rw [assemblySourceRestFinishTargetTape,
    assemblySourceRestFinishRawBoolSourceStartTargetTape,
    assemblySourceRestFinishTargetPrefixBits,
    assemblySourceRestFinishRawTailBits]

theorem assemblySourceRestFinishTargetTape_eq_rawBoolReusableQuoteTargetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetTape w sourceRestBits stage =
      assemblySourceRestFinishRawBoolReusableQuoteTargetTape
        w sourceRestBits stage := by
  rw [assemblySourceRestFinishTargetTape_eq_rawBoolSourceStartTargetTape,
    assemblySourceRestFinishRawBoolSourceStartTargetTape_eq_reusableQuote]

theorem
    MixedParserStackRewriterTargetTape_eq_rawBoolReusableQuoteTargetTape_computed
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterTargetTape
        (MixedParserStackRewriterPrefixQuote
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage))
        (MixedParserStackRewriterLengthHeader
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        (preservingCellPassCellBits sourceRestBits) =
      assemblySourceRestFinishRawBoolReusableQuoteTargetTape
        w sourceRestBits stage := by
  rw [MixedParserStackRewriterTargetTape_eq_targetTape_computed,
    assemblySourceRestFinishTargetTape_eq_rawBoolReusableQuoteTargetTape]

theorem
    mixedParserStackSeekLeftBoundaryDescription_run_payloadRev_withSentinel
    (scanRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    mixedParserStackSeekLeftBoundaryDescription.runConfig
        (scanRev.length + 1)
        { state := mixedParserStackSeekLeftBoundaryDescription.start
          tape :=
            tapeAtCells
              (List.append (scanRev.map some)
                (none ::
                  List.append
                    (List.reverse
                      assemblySourceRestFinishParserMarkerLeftCells)
                    [none]))
              (some current :: right) } =
      { state := mixedParserStackSeekLeftBoundaryDescription.start
        tape :=
          tapeAtCells
            (List.append
              (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
              [none])
            (none ::
              List.append (scanRev.reverse.map some)
                (some current :: right)) } := by
  induction scanRev generalizing current right with
  | nil =>
      cases current <;>
        simp [mixedParserStackSeekLeftBoundaryDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons prev rest ih =>
      rw [show (prev :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          mixedParserStackSeekLeftBoundaryDescription.runConfig 1
              { state := mixedParserStackSeekLeftBoundaryDescription.start
                tape :=
                  tapeAtCells
                    (List.append ((prev :: rest).map some)
                      (none ::
                        List.append
                          (List.reverse
                            assemblySourceRestFinishParserMarkerLeftCells)
                          [none]))
                    (some current :: right) } =
            { state := mixedParserStackSeekLeftBoundaryDescription.start
              tape :=
                tapeAtCells
                  (List.append (rest.map some)
                    (none ::
                      List.append
                        (List.reverse
                          assemblySourceRestFinishParserMarkerLeftCells)
                        [none]))
                  (some prev :: some current :: right) } := by
        cases current <;> cases prev <;>
          simp [mixedParserStackSeekLeftBoundaryDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih prev (some current :: right)

theorem
    mixedParserStackSeekLeftBoundaryDescription_run_markerLeft_withSentinel
    (right : List (Option Bool)) :
    mixedParserStackSeekLeftBoundaryDescription.runConfig 6
        { state := mixedParserStackSeekLeftBoundaryDescription.start
          tape :=
            tapeAtCells
              (List.append
                (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
                [none])
              (none :: right) } =
      { state := mixedParserStackSeekLeftBoundaryDescription.halt
        tape :=
          tapeAtCells []
            (none ::
              List.append assemblySourceRestFinishParserMarkerLeftCells
                (none :: right)) } := by
  simp [mixedParserStackSeekLeftBoundaryDescription,
    assemblySourceRestFinishParserMarkerLeftCells,
    transitionPrefixLeftTail, runConfig, stepConfig, lookupTransition,
    Matches, transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft]

theorem
    mixedParserStackSeekLeftBoundaryDescription_run_payloadToLeftBoundary_withSentinel
    (scanRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    mixedParserStackSeekLeftBoundaryDescription.runConfig
        (scanRev.length + 7)
        { state := mixedParserStackSeekLeftBoundaryDescription.start
          tape :=
            tapeAtCells
              (List.append (scanRev.map some)
                (none ::
                  List.append
                    (List.reverse
                      assemblySourceRestFinishParserMarkerLeftCells)
                    [none]))
              (some current :: right) } =
      { state := mixedParserStackSeekLeftBoundaryDescription.halt
        tape :=
          tapeAtCells []
            (none ::
              List.append assemblySourceRestFinishParserMarkerLeftCells
                (none ::
                  List.append (scanRev.reverse.map some)
                    (some current :: right))) } := by
  rw [show scanRev.length + 7 = (scanRev.length + 1) + 6 by omega]
  rw [runConfig_add]
  rw [
    mixedParserStackSeekLeftBoundaryDescription_run_payloadRev_withSentinel]
  rw [
    mixedParserStackSeekLeftBoundaryDescription_run_markerLeft_withSentinel]

theorem
    MixedParserStackRewriterSentinelSourceTape_eq_seekLeftBoundarySource
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat)
    (scanRev : Word Bool) (current : Bool)
    (hpayload :
      assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage =
          List.append scanRev.reverse [current]) :
    MixedParserStackRewriterSourceTape
        (none :: assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        quoteRestBits =
      tapeAtCells
        (List.append (scanRev.map some)
          (none ::
            List.append
              (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
              [none]))
        (some current ::
          none :: List.append (quoteRestBits.map some) [none]) := by
  rw [MixedParserStackRewriterSourceTape,
    scanLeftToBlankLeftHaltTape]
  rw [assemblySourceRestFinishParserPrefixCells_eq_marker_split]
  rw [assemblySourceRestFinishParserMarkerRightCells_eq_bits]
  have hpayloadCells :
      List.append (sourceRestBits.reverse.map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append
              ((assemblySourceRestFinishParserMarkerRightBits w).reverse.map
                some)
              (none ::
                List.append
                  (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
                  [none]))) =
        some current ::
          List.append (scanRev.map some)
            (none ::
              List.append
                (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
                [none]) := by
    have hrev :=
      congrArg (fun bits => bits.reverse.map some) hpayload
    simpa [assemblySourceRestFinishRightPayloadBits, List.reverse_append,
      List.append_assoc] using congrArg
        (fun cells =>
          List.append cells
            (none ::
              List.append
                (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
                [none]))
        hrev
  have hpayloadCells' :
      (List.map some sourceRestBits).reverse ++
          ((List.map some
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)).reverse ++
            ((List.map some
                (assemblySourceRestFinishParserMarkerRightBits w)).reverse ++
              none ::
                (assemblySourceRestFinishParserMarkerLeftCells.reverse ++
                  [none]))) =
        some current ::
          List.append (scanRev.map some)
            (none ::
              List.append
                (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
                [none]) := by
    simpa [List.map_reverse] using hpayloadCells
  simp [List.reverse_append, List.append_assoc, hpayloadCells',
    tapeAtCells, Tape.move, Tape.moveLeft]

theorem
    mixedParserStackSeekLeftBoundaryDescription_haltsFrom_sentinelSourceTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    mixedParserStackSeekLeftBoundaryDescription.HaltsFromTape
      (MixedParserStackRewriterSourceTape
        (none :: assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        quoteRestBits)
      (MixedParserStackRewriterTrueLeftBoundaryTape
        w sourceRestBits quoteRestBits stage) := by
  rcases exists_reverse_append_singleton_of_nonempty
      (assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage)
      (assemblySourceRestFinishRightPayloadBits_ne_nil
        w sourceRestBits stage) with
    ⟨scanRev, current, hpayload⟩
  refine ⟨scanRev.length + 7, ?_⟩
  have hrun :=
    mixedParserStackSeekLeftBoundaryDescription_run_payloadToLeftBoundary_withSentinel
      scanRev current
      (none :: List.append (quoteRestBits.map some) [none])
  have hsource :=
    MixedParserStackRewriterSentinelSourceTape_eq_seekLeftBoundarySource
      w sourceRestBits quoteRestBits stage scanRev current hpayload
  have htarget :=
    MixedParserStackRewriterTrueLeftBoundaryTape_eq_payloadSplit
      w sourceRestBits quoteRestBits stage scanRev current hpayload
  constructor
  · simpa [hsource] using congrArg Configuration.state hrun
  · simpa [hsource, htarget] using congrArg Configuration.tape hrun

def AssemblySourceRestReusableQuoteAfterSourceRestScanFinisherSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestReusableQuoteAfterSourceRestScanTape
          w sourceRestBits stage)
        (assemblySourceRestFinishRawBoolReusableQuoteTargetTape
          w sourceRestBits stage)

def AssemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction :
    Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestReusableQuoteAfterSourceRestScanFinisherSpec finish

def MixedParserStackSentinelSourceFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterSourceTape
          (none :: assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits
          (preservingCellPassCellBits sourceRestBits))
        (MixedParserStackRewriterTargetTape
          (MixedParserStackRewriterPrefixQuote
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage))
          (MixedParserStackRewriterLengthHeader
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage)
            sourceRestBits)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits
          (preservingCellPassCellBits sourceRestBits))

def MixedParserStackSentinelSourceFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackSentinelSourceFinisherAssemblySourceRestSpec finish

theorem
    AssemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction_of_sentinelSource
    (h : MixedParserStackSentinelSourceFinisherConstructionForAssemblySourceRest) :
    AssemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  rw [
    assemblySourceRestReusableQuoteAfterSourceRestScanTape_eq_mixedParserStackSource_withSentinel]
  simpa [MixedParserStackRewriterTargetTape_eq_rawBoolReusableQuoteTargetTape_computed]
    using hfinish.right w sourceRestBits stage

theorem
    AssemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction_of_afterSourceRestScan
    (h : AssemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction) :
    AssemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine ⟨SeqViaCanonical scanRightToBlankLeftDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanRightToBlankLeftDescription_haltsFrom_defaultedSourceRestBoundary_to_afterSourceRest
          w sourceRestBits stage)
        (assemblySourceRestReusableQuoteAfterSourceRestScanTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.right w sourceRestBits stage)

theorem
    MixedParserStackSentinelSourceFinisherConstructionForAssemblySourceRest_of_trueLeftBoundary
    (h :
      MixedParserStackTrueLeftBoundaryFinisherConstructionForAssemblySourceRest) :
    MixedParserStackSentinelSourceFinisherConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical mixedParserStackSeekLeftBoundaryDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        mixedParserStackSeekLeftBoundaryDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        mixedParserStackSeekLeftBoundaryDescription_subroutineReady
        hfinish.left
        (mixedParserStackSeekLeftBoundaryDescription_haltsFrom_sentinelSourceTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterTrueLeftBoundaryTape_move_left_move_right
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (hfinish.right w sourceRestBits stage)

theorem MixedParserStackRewriterWholeSourceTargetTape_cells_assembly
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterWholeSourceTargetTape
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)) =
      List.append
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (MixedParserStackRewriterTrueSourceCells
                w sourceRestBits stage).length)
            (mixedParserStackQuotedCellsBits
              (MixedParserStackRewriterTrueSourceCells
                w sourceRestBits stage)))).map some)
        ((assemblySourceRestFinishRawTailBits sourceRestBits stage).map
          some) := by
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  rw [MixedParserStackRewriterWholeSourceTargetTape,
    assemblySourceRestFinishRawTailBits, hstage]
  simp [tapeAtCells, Tape.cells, List.map_reverse, List.map_append,
    List.append_assoc]

theorem MixedParserStackRewriterWholeSourceTargetTape_defaultedCells_assembly
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackRewriterWholeSourceTargetTape
            (MixedParserStackRewriterTrueSourceCells
              w sourceRestBits stage)
            (assemblySourceRestFinishRawTailBits sourceRestBits stage))) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (assemblySourceRestFinishSourceBits
              w sourceRestBits stage).length)
          (List.append
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourceBits
                w sourceRestBits stage))
            (assemblySourceRestFinishRawTailBits
              sourceRestBits stage))) := by
  rw [MixedParserStackRewriterWholeSourceTargetTape_cells_assembly]
  rw [MixedParserStackRewriterTrueSourceCells_length]
  rw [MixedParserStackRewriterTrueSourceCells_quotedBits_eq_sourceBits]
  simp [List.map_append, List.map_map, optionBitDefaultFalse_map_some,
    List.append_assoc]

theorem
    MixedParserStackRewriterWholeSourceTargetTape_defaultedCells_eq_targetBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackRewriterWholeSourceTargetTape
            (MixedParserStackRewriterTrueSourceCells
              w sourceRestBits stage)
            (assemblySourceRestFinishRawTailBits sourceRestBits stage))) =
      assemblySourceRestFinishTargetBits w sourceRestBits stage := by
  rw [MixedParserStackRewriterWholeSourceTargetTape_eq_rawBoolTargetTape]
  rw [← assemblySourceRestFinishTargetTape_eq_rawBoolSourceStartTargetTape]
  exact assemblySourceRestFinishTargetTape_defaultedCells_eq_targetBits
    w sourceRestBits stage

theorem
    MixedParserStackRewriterWholeSourceTargetTape_eq_quoteRestJoinedTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterWholeSourceTargetTape
        (MixedParserStackRewriterTrueSourceCells
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage) =
      assemblySourceRestFinishQuoteRestJoinedTape
        w sourceRestBits stage := by
  rw [MixedParserStackRewriterWholeSourceTargetTape_eq_rawBoolTargetTape]
  rw [assemblySourceRestFinishRawBoolSourceStartTargetTape_eq_reusableQuote]
  rw [← assemblySourceRestFinishTargetTape_eq_rawBoolReusableQuoteTargetTape]
  rw [← assemblySourceRestFinishQuoteRestJoinedTape_eq_targetTape]

def MixedParserStackWholeSourcePrefixQuotedSeparatedTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
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
    (List.append
      ((assemblySourceRestFinishRawTailBits sourceRestBits stage).map some)
      (none ::
        List.append
          ((preservingCellPassCellBits sourceRestBits).map some)
          [none]))

theorem
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage) =
      List.append
        ((List.append
          (MixedParserStackRewriterLengthHeader
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage)
            sourceRestBits)
          (MixedParserStackRewriterPrefixQuote
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage))).map some)
        (List.append
          ((assemblySourceRestFinishRawTailBits
            sourceRestBits stage).map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) := by
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape]
  rw [assemblySourceRestFinishRawTailBits, hstage]
  simp [tapeAtCells, Tape.cells, List.map_reverse,
    List.map_append, List.append_assoc]

theorem
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_defaultedCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
            w sourceRestBits stage)) =
      List.append
        (MixedParserStackRewriterLengthHeader
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits)
        (List.append
          (MixedParserStackRewriterPrefixQuote
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage))
          (List.append
            (assemblySourceRestFinishRawTailBits sourceRestBits stage)
            (false ::
              List.append (preservingCellPassCellBits sourceRestBits)
                [false]))) := by
  rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape_cells]
  simp [List.map_append, List.map_map, optionBitDefaultFalse,
    optionBitDefaultFalse_map_some, List.append_assoc]

theorem
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_defaultedCells_computed
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (List.append
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (false ::
            List.append (preservingCellPassCellBits sourceRestBits)
              [false])) := by
  rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape_defaultedCells]
  rw [MixedParserStackRewriterPrefixQuote_eq_assemblyQuotedPrefix]
  rw [MixedParserStackRewriterLengthHeader_eq_assemblyLengthHeader]
  rw [assemblySourceRestFinishPrefixQuoteOutputBits]
  simp [List.append_assoc]

theorem
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
            w sourceRestBits stage)) =
      MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage := by
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape,
    assemblySourceRestFinishRawTailBits, hstage]
  simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

def mixedOptionCellQuoteLiveTailEmitterSourceTape
    (leftRev : List (Option Bool)) (scanInput quoteRest : Word Bool) :
    Tape Bool :=
  tapeAtCells leftRev
    (List.append (scanInput.map some)
      (none :: List.append (quoteRest.map some) [none]))

def mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
    (leftRev : List (Option Bool))
    (quoteScan rawTail quoteRest : Word Bool) : Tape Bool :=
  tapeAtCells leftRev
    (List.append (quoteScan.map some)
      (List.append (rawTail.map some)
        (none :: List.append (quoteRest.map some) [none])))

theorem mixedOptionCellQuoteLiveTailEmitterSourceTape_eq_split
    (leftRev : List (Option Bool))
    (quoteScan rawTail quoteRest : Word Bool) :
    mixedOptionCellQuoteLiveTailEmitterSourceTape
        leftRev (List.append quoteScan rawTail) quoteRest =
      mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
        leftRev quoteScan rawTail quoteRest := by
  rw [mixedOptionCellQuoteLiveTailEmitterSourceTape,
    mixedOptionCellQuoteLiveTailEmitterSplitSourceTape]
  simp [List.map_append, List.append_assoc]

def mixedOptionCellQuoteLiveTailEmitterTargetTape
    (emittedPrefix rawTail quoteRest : Word Bool) : Tape Bool :=
  tapeAtCells
    (emittedPrefix.reverse.map some)
    (List.append (rawTail.map some)
      (none :: List.append (quoteRest.map some) [none]))

theorem mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_cells
    (leftRev : List (Option Bool))
    (quoteScan rawTail quoteRest : Word Bool) :
    Tape.cells
        (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
          leftRev quoteScan rawTail quoteRest) =
      List.append leftRev.reverse
        (List.append (quoteScan.map some)
          (List.append (rawTail.map some)
            (none :: List.append (quoteRest.map some) [none]))) := by
  cases quoteScan <;> cases rawTail <;>
    simp [mixedOptionCellQuoteLiveTailEmitterSplitSourceTape,
      tapeAtCells, Tape.cells]

theorem mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_defaultedCells
    (leftRev : List (Option Bool))
    (quoteScan rawTail quoteRest : Word Bool) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
            leftRev quoteScan rawTail quoteRest)) =
      List.append (List.map optionBitDefaultFalse leftRev.reverse)
        (List.append quoteScan
          (List.append rawTail
            (false :: List.append quoteRest [false]))) := by
  rw [mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_cells]
  simp [List.map_append, List.map_map,
    optionBitDefaultFalse, optionBitDefaultFalse_map_some]

theorem mixedOptionCellQuoteLiveTailEmitterTargetTape_cells
    (emittedPrefix rawTail quoteRest : Word Bool) :
    Tape.cells
        (mixedOptionCellQuoteLiveTailEmitterTargetTape
          emittedPrefix rawTail quoteRest) =
      List.append (emittedPrefix.map some)
        (List.append (rawTail.map some)
          (none :: List.append (quoteRest.map some) [none])) := by
  cases rawTail <;>
    simp [mixedOptionCellQuoteLiveTailEmitterTargetTape,
      tapeAtCells, Tape.cells, List.map_reverse]

theorem mixedOptionCellQuoteLiveTailEmitterTargetTape_defaultedCells
    (emittedPrefix rawTail quoteRest : Word Bool) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailEmitterTargetTape
            emittedPrefix rawTail quoteRest)) =
      List.append emittedPrefix
        (List.append rawTail
          (false :: List.append quoteRest [false])) := by
  rw [mixedOptionCellQuoteLiveTailEmitterTargetTape_cells]
  simp [List.map_append, List.map_map,
    optionBitDefaultFalse, optionBitDefaultFalse_map_some]

def mixedOptionCellQuoteLiveTailEmitterSourceBits
    (leftRev : List (Option Bool))
    (quoteScan rawTail quoteRest : Word Bool) : Word Bool :=
  List.append (List.map optionBitDefaultFalse leftRev.reverse)
    (List.append quoteScan
      (List.append rawTail
        (false :: List.append quoteRest [false])))

def mixedOptionCellQuoteLiveTailEmitterTargetBits
    (emittedPrefix rawTail quoteRest : Word Bool) : Word Bool :=
  List.append emittedPrefix
    (List.append rawTail
      (false :: List.append quoteRest [false]))

theorem mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_defaultedCells_eq_sourceBits
    (leftRev : List (Option Bool))
    (quoteScan rawTail quoteRest : Word Bool) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
            leftRev quoteScan rawTail quoteRest)) =
      mixedOptionCellQuoteLiveTailEmitterSourceBits
        leftRev quoteScan rawTail quoteRest := by
  rw [mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_defaultedCells]
  rfl

theorem mixedOptionCellQuoteLiveTailEmitterTargetTape_defaultedCells_eq_targetBits
    (emittedPrefix rawTail quoteRest : Word Bool) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailEmitterTargetTape
            emittedPrefix rawTail quoteRest)) =
      mixedOptionCellQuoteLiveTailEmitterTargetBits
        emittedPrefix rawTail quoteRest := by
  rw [mixedOptionCellQuoteLiveTailEmitterTargetTape_defaultedCells]
  rfl

theorem assemblySourceRestFinishRightPayloadBits_eq_markerRight_append_rawTail
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishRightPayloadBits w sourceRestBits stage =
      List.append (assemblySourceRestFinishParserMarkerRightBits w)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage) := by
  rw [assemblySourceRestFinishRightPayloadBits,
    assemblySourceRestFinishRawTailBits]

theorem assemblySourceRestFinishParserMarkerRightBits_eq_stageInputTailPrefix
    (w : Word Bool) :
    assemblySourceRestFinishParserMarkerRightBits w =
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
        w := by
  cases w <;> rfl

theorem assemblySourceRestFinishRightPayloadBits_eq_stageInputTailPrefix_append_rawTail
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishRightPayloadBits w sourceRestBits stage =
      List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
          w)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage) := by
  rw [assemblySourceRestFinishRightPayloadBits_eq_markerRight_append_rawTail]
  rw [assemblySourceRestFinishParserMarkerRightBits_eq_stageInputTailPrefix]

theorem
    assemblySourceRestFinishRightPayloadBits_eq_stageInputSecondBitTail_append_sourceRest
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishRightPayloadBits w sourceRestBits stage =
      List.append
        (DovetailInitialLayoutInitializer.stageInputSecondBitTail w stage)
        sourceRestBits := by
  rw [assemblySourceRestFinishRightPayloadBits_eq_stageInputTailPrefix_append_rawTail]
  rw [assemblySourceRestFinishRawTailBits]
  rw [
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_eq_prefix_stageNat]
  simp [List.append_assoc]

theorem assemblySourceRestFinishQuotedPrefixBits_eq_marker_chunks
    (w : Word Bool) (stage : Nat) :
    assemblySourceRestFinishQuotedPrefixBits w stage =
      List.append
        (mixedParserStackQuotedCellsBits
          assemblySourceRestFinishParserMarkerLeftCells)
        (List.append preservingCellPassZeroBits
          (List.append
            (preservingCellPassCellBits
              (assemblySourceRestFinishParserMarkerRightBits w))
            (preservingCellPassCellBits
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)))) := by
  rw [← MixedParserStackRewriterPrefixQuote_eq_assemblyQuotedPrefix]
  rw [MixedParserStackRewriterPrefixQuote_marker_split]
  rw [mixedParserStackQuotedCellsBits_markerRight_eq_bits]

theorem assemblySourceRestFinishPrefixQuoteOutputBits_eq_marker_chunks
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishPrefixQuoteOutputBits w sourceRestBits stage =
      List.append
        (assemblySourceRestFinishLengthHeaderBits w sourceRestBits stage)
        (List.append
          (mixedParserStackQuotedCellsBits
            assemblySourceRestFinishParserMarkerLeftCells)
          (List.append preservingCellPassZeroBits
            (List.append
              (preservingCellPassCellBits
                (assemblySourceRestFinishParserMarkerRightBits w))
              (preservingCellPassCellBits
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage))))) := by
  rw [assemblySourceRestFinishPrefixQuoteOutputBits]
  rw [assemblySourceRestFinishQuotedPrefixBits_eq_marker_chunks]

theorem assemblySourceRestFinishPrefixQuoteOutputBits_headerPrefix
    (w sourceRestBits : Word Bool) (stage : Nat) :
    exists rest : Word Bool,
      assemblySourceRestFinishPrefixQuoteOutputBits w sourceRestBits stage =
        List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          rest := by
  refine
    ⟨List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        ((assemblySourceRestFinishSourcePrefixBits w stage).length +
          sourceRestBits.length))
      (assemblySourceRestFinishQuotedPrefixBits w stage), ?_⟩
  rw [assemblySourceRestFinishPrefixQuoteOutputBits,
    assemblySourceRestFinishLengthHeaderBits]
  simp [List.append_assoc]

theorem assemblySourceRestFinishPrefixQuoteOutputBits_map_some_eq_marker_chunks
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (assemblySourceRestFinishPrefixQuoteOutputBits
      w sourceRestBits stage).map some =
      List.append
        ((assemblySourceRestFinishLengthHeaderBits
          w sourceRestBits stage).map some)
        (List.append
          ((mixedParserStackQuotedCellsBits
            assemblySourceRestFinishParserMarkerLeftCells).map some)
          (List.append (preservingCellPassZeroBits.map some)
            (List.append
              ((preservingCellPassCellBits
                (assemblySourceRestFinishParserMarkerRightBits w)).map some)
              ((preservingCellPassCellBits
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage)).map some)))) := by
  rw [assemblySourceRestFinishPrefixQuoteOutputBits_eq_marker_chunks]
  simp [List.map_append]

theorem
    MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSourceTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits quoteRestBits stage =
      mixedOptionCellQuoteLiveTailEmitterSourceTape
        (some false ::
          List.append
            (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
            [none])
        (assemblySourceRestFinishRightPayloadBits
          w sourceRestBits stage)
        quoteRestBits := by
  rw [MixedParserStackRewriterDefaultedInternalMarkerTape,
    mixedOptionCellQuoteLiveTailEmitterSourceTape]

theorem
    MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits quoteRestBits stage =
      mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
        (some false ::
          List.append
            (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
            [none])
        (assemblySourceRestFinishParserMarkerRightBits w)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        quoteRestBits := by
  rw [
    MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSourceTape]
  rw [assemblySourceRestFinishRightPayloadBits_eq_markerRight_append_rawTail]
  rw [mixedOptionCellQuoteLiveTailEmitterSourceTape_eq_split]

theorem
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_mixedOptionCellQuoteLiveTailEmitterTargetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage =
      mixedOptionCellQuoteLiveTailEmitterTargetTape
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) := by
  rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape,
    mixedOptionCellQuoteLiveTailEmitterTargetTape]
  rw [MixedParserStackRewriterPrefixQuote_eq_assemblyQuotedPrefix]
  rw [MixedParserStackRewriterLengthHeader_eq_assemblyLengthHeader]
  rw [assemblySourceRestFinishPrefixQuoteOutputBits]

theorem
    mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_defaultedCells_assembly
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
            (some false ::
              List.append
                (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
                [none])
            (assemblySourceRestFinishParserMarkerRightBits w)
            (assemblySourceRestFinishRawTailBits sourceRestBits stage)
            quoteRestBits)) =
      false ::
        List.append
          (assemblySourceRestFinishSourceBits w sourceRestBits stage)
          (false :: List.append quoteRestBits [false]) := by
  rw [
    ← MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSplitSourceTape]
  exact MixedParserStackRewriterDefaultedInternalMarkerTape_defaultedCells
    w sourceRestBits quoteRestBits stage

theorem
    mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_cells_assembly_stageSplit
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
          (some false ::
            List.append
              (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
              [none])
          (assemblySourceRestFinishParserMarkerRightBits w)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          quoteRestBits) =
      none ::
        List.append assemblySourceRestFinishParserMarkerLeftCells
          (some false ::
            List.append
              ((assemblySourceRestFinishParserMarkerRightBits w).map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage).map some)
                (List.append (sourceRestBits.map some)
                  (none :: List.append (quoteRestBits.map some) [none])))) := by
  rw [mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_cells]
  simp [assemblySourceRestFinishRawTailBits, List.reverse_append,
    List.map_append, List.append_assoc]

theorem
    mixedOptionCellQuoteLiveTailEmitterTargetTape_defaultedCells_assembly
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailEmitterTargetTape
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
  rw [
    ← MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_mixedOptionCellQuoteLiveTailEmitterTargetTape]
  exact
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_defaultedCells_computed
      w sourceRestBits stage

theorem
    mixedOptionCellQuoteLiveTailEmitterTargetTape_cells_assembly_stageSplit
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (mixedOptionCellQuoteLiveTailEmitterTargetTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) =
      List.append
        ((assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage).map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (List.append (sourceRestBits.map some)
            (none ::
              List.append
                ((preservingCellPassCellBits sourceRestBits).map some)
                [none]))) := by
  rw [mixedOptionCellQuoteLiveTailEmitterTargetTape_cells]
  simp [assemblySourceRestFinishRawTailBits, List.map_append,
    List.append_assoc]

def assemblySourceRestFinishPrefixQuotedSeparatedBits
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (assemblySourceRestFinishPrefixQuoteOutputBits w sourceRestBits stage)
    (List.append
      (assemblySourceRestFinishRawTailBits sourceRestBits stage)
      (false ::
        List.append (preservingCellPassCellBits sourceRestBits) [false]))

theorem
    mixedOptionCellQuoteLiveTailEmitterTargetTape_defaultedCells_eq_prefixQuotedSeparatedBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailEmitterTargetTape
            (assemblySourceRestFinishPrefixQuoteOutputBits
              w sourceRestBits stage)
            (assemblySourceRestFinishRawTailBits sourceRestBits stage)
            (preservingCellPassCellBits sourceRestBits))) =
      assemblySourceRestFinishPrefixQuotedSeparatedBits
        w sourceRestBits stage := by
  rw [mixedOptionCellQuoteLiveTailEmitterTargetTape_defaultedCells_assembly]
  rfl

def MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
          (some false ::
            List.append
              (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
              [none])
          (assemblySourceRestFinishParserMarkerRightBits w)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits))
        (mixedOptionCellQuoteLiveTailEmitterTargetTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits))

def MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestSpec finish

def MixedOptionCellQuoteLiveTailEmitterFamilySpec
    {ι : Type}
    (sourceLeftRev : ι -> List (Option Bool))
    (quoteScan rawTail quoteRest emittedPrefix : ι -> Word Bool)
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall p : ι,
      finish.HaltsFromTape
        (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
          (sourceLeftRev p) (quoteScan p) (rawTail p) (quoteRest p))
        (mixedOptionCellQuoteLiveTailEmitterTargetTape
          (emittedPrefix p) (rawTail p) (quoteRest p))

def MixedOptionCellQuoteLiveTailEmitterFamilyConstruction
    {ι : Type}
    (sourceLeftRev : ι -> List (Option Bool))
    (quoteScan rawTail quoteRest emittedPrefix : ι -> Word Bool) : Prop :=
  exists finish : MachineDescription,
    MixedOptionCellQuoteLiveTailEmitterFamilySpec
      sourceLeftRev quoteScan rawTail quoteRest emittedPrefix finish

structure AssemblySourceRestLiveTailEmitterParam where
  w : Word Bool
  sourceRestBits : Word Bool
  stage : Nat

def assemblySourceRestLiveTailEmitterLeftRev
    (_p : AssemblySourceRestLiveTailEmitterParam) :
    List (Option Bool) :=
  some false ::
    List.append
      (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
      [none]

def assemblySourceRestLiveTailEmitterQuoteScan
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  assemblySourceRestFinishParserMarkerRightBits p.w

def assemblySourceRestLiveTailEmitterRawTail
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  assemblySourceRestFinishRawTailBits p.sourceRestBits p.stage

def assemblySourceRestLiveTailEmitterQuoteRest
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  preservingCellPassCellBits p.sourceRestBits

def assemblySourceRestLiveTailEmitterEmittedPrefix
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  assemblySourceRestFinishPrefixQuoteOutputBits
    p.w p.sourceRestBits p.stage

def assemblySourceRestLiveTailEmitterSourceBits
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  mixedOptionCellQuoteLiveTailEmitterSourceBits
    (assemblySourceRestLiveTailEmitterLeftRev p)
    (assemblySourceRestLiveTailEmitterQuoteScan p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def assemblySourceRestLiveTailEmitterTargetBits
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  mixedOptionCellQuoteLiveTailEmitterTargetBits
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem
    assemblySourceRestLiveTailEmitterQuoteScan_append_stageNatBits_eq_stageInputSecondBitTail
    (p : AssemblySourceRestLiveTailEmitterParam) :
    List.append
        (assemblySourceRestLiveTailEmitterQuoteScan p)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          p.stage) =
      DovetailInitialLayoutInitializer.stageInputSecondBitTail p.w p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rw [assemblySourceRestLiveTailEmitterQuoteScan]
      rw [assemblySourceRestFinishParserMarkerRightBits_eq_stageInputTailPrefix]
      rw [
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_eq_prefix_stageNat]

theorem
    assemblySourceRestLiveTailEmitterQuoteScan_append_rawTail_eq_rightPayload
    (p : AssemblySourceRestLiveTailEmitterParam) :
    List.append
        (assemblySourceRestLiveTailEmitterQuoteScan p)
        (assemblySourceRestLiveTailEmitterRawTail p) =
      assemblySourceRestFinishRightPayloadBits
        p.w p.sourceRestBits p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rw [assemblySourceRestLiveTailEmitterQuoteScan,
        assemblySourceRestLiveTailEmitterRawTail]
      rw [assemblySourceRestFinishRightPayloadBits_eq_markerRight_append_rawTail]

theorem
    assemblySourceRestLiveTailEmitterSourceBits_eq_defaultedSource
    (p : AssemblySourceRestLiveTailEmitterParam) :
    assemblySourceRestLiveTailEmitterSourceBits p =
      false ::
        List.append
          (assemblySourceRestFinishSourceBits p.w p.sourceRestBits p.stage)
          (false ::
            List.append
              (assemblySourceRestLiveTailEmitterQuoteRest p)
              [false]) := by
  cases p with
  | mk w sourceRestBits stage =>
      rw [assemblySourceRestLiveTailEmitterSourceBits]
      rw [
        ← mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_defaultedCells_eq_sourceBits]
      exact
        mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_defaultedCells_assembly
          w sourceRestBits (preservingCellPassCellBits sourceRestBits) stage

theorem
    assemblySourceRestLiveTailEmitterTargetBits_eq_prefixQuotedSeparated
    (p : AssemblySourceRestLiveTailEmitterParam) :
    assemblySourceRestLiveTailEmitterTargetBits p =
      assemblySourceRestFinishPrefixQuotedSeparatedBits
        p.w p.sourceRestBits p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rw [assemblySourceRestLiveTailEmitterTargetBits]
      rw [
        ← mixedOptionCellQuoteLiveTailEmitterTargetTape_defaultedCells_eq_targetBits]
      exact
        mixedOptionCellQuoteLiveTailEmitterTargetTape_defaultedCells_eq_prefixQuotedSeparatedBits
          w sourceRestBits stage

theorem
    assemblySourceRestLiveTailEmitterEmittedPrefix_append_quoteRest_eq_targetPrefix
    (p : AssemblySourceRestLiveTailEmitterParam) :
    List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) =
      assemblySourceRestFinishTargetPrefixBits
        p.w p.sourceRestBits p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rw [assemblySourceRestLiveTailEmitterEmittedPrefix,
        assemblySourceRestLiveTailEmitterQuoteRest]
      exact
        (assemblySourceRestFinishTargetPrefixBits_eq_prefixQuote_append_restQuote
          w sourceRestBits stage).symm

theorem
    assemblySourceRestLiveTailEmitterSourceTape_eq_defaultedInternalMarkerTape
    (p : AssemblySourceRestLiveTailEmitterParam) :
    mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
        (assemblySourceRestLiveTailEmitterLeftRev p)
        (assemblySourceRestLiveTailEmitterQuoteScan p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) =
      MixedParserStackRewriterDefaultedInternalMarkerTape
        p.w p.sourceRestBits
        (preservingCellPassCellBits p.sourceRestBits) p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rw [assemblySourceRestLiveTailEmitterLeftRev,
        assemblySourceRestLiveTailEmitterQuoteScan,
        assemblySourceRestLiveTailEmitterRawTail,
        assemblySourceRestLiveTailEmitterQuoteRest]
      exact
        (MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
          w sourceRestBits (preservingCellPassCellBits sourceRestBits)
          stage).symm

theorem
    assemblySourceRestLiveTailEmitterTargetTape_eq_prefixQuotedSeparatedTape
    (p : AssemblySourceRestLiveTailEmitterParam) :
    mixedOptionCellQuoteLiveTailEmitterTargetTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) =
      MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        p.w p.sourceRestBits p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rw [assemblySourceRestLiveTailEmitterEmittedPrefix,
        assemblySourceRestLiveTailEmitterRawTail,
        assemblySourceRestLiveTailEmitterQuoteRest]
      exact
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_mixedOptionCellQuoteLiveTailEmitterTargetTape
          w sourceRestBits stage).symm

theorem
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_gapPayloadScanSource
    (w sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (rawTailRest : Word Bool)
    (hraw :
      assemblySourceRestFinishRawTailBits sourceRestBits stage =
        head :: rawTailRest) :
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage =
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanSourceTape
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
          [none]) := by
  rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape,
    CommonGround.FiniteTransducers.rightBlankGapPayloadScanSourceTape]
  rw [hraw]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    CommonGround.FiniteTransducers.tapeAtCells]

theorem
    rightBlankGapPayloadScanDescription_haltsFrom_prefixQuotedSeparatedTape
    (w sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (rawTailRest : Word Bool)
    (hraw :
      assemblySourceRestFinishRawTailBits sourceRestBits stage =
        head :: rawTailRest) :
    CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription.HaltsFromTape
      (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage)
      (CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
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
          [none])) := by
  rw [
    MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_gapPayloadScanSource
      w sourceRestBits stage head rawTailRest hraw]
  exact
    CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription_haltsFromTape
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

theorem
    rightBlankGapPayloadScanDescription_haltsFrom_prefixQuotedSeparatedTape_to_afterRawTailScan
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

theorem commonGround_tapeAtCells_move_right_move_left_append_cons
    (pref tail right : List (Option Bool)) (cell : Option Bool) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (CommonGround.FiniteTransducers.tapeAtCells
            (List.append pref (cell :: tail)) right)) =
      CommonGround.FiniteTransducers.tapeAtCells
        (List.append pref (cell :: tail)) right := by
  cases pref <;> cases right <;>
    simp [CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem commonGround_tapeAtCells_move_left_cells_append_cons_right_cons
    (pref tail right : List (Option Bool)) (cell head : Option Bool) :
    Tape.cells
        (Tape.move Direction.left
          (CommonGround.FiniteTransducers.tapeAtCells
            (List.append pref (cell :: tail)) (head :: right))) =
      List.append tail.reverse
        (cell :: List.append pref.reverse (head :: right)) := by
  cases pref <;>
    simp [CommonGround.FiniteTransducers.tapeAtCells,
      Tape.cells, Tape.move, Tape.moveLeft, List.reverse_append,
      List.append_assoc]

theorem
    rightBlankGapPayloadScanTargetTape_move_left_move_right
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
  rw [commonGround_tapeAtCells_move_right_move_left_append_cons
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
  rw [commonGround_tapeAtCells_move_left_cells_append_cons_right_cons
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
  rw [commonGround_tapeAtCells_move_left_cells_append_cons_right_cons
    (payloadRest.reverse.map some)
    (List.append (List.replicate gap (none : Option Bool)) baseLeft)
    padding (some current) none]
  simp [List.reverse_append, List.map_reverse, List.append_assoc]

theorem
    MixedParserStackWholeSourceAfterRawTailScanTape_move_right_eq_rightEndSource
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
    commonGround_tapeAtCells_move_right_move_left_append_cons
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

theorem
    MixedParserStackWholeSourceAfterRawTailScanTape_defaultedCells_computed
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackWholeSourceAfterRawTailScanTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (List.append
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (false ::
            List.append (preservingCellPassCellBits sourceRestBits)
              [false])) := by
  rcases assemblySourceRestFinishRawTailBits_cons_exists
      sourceRestBits stage with
    ⟨head, rawTailRest, hraw⟩
  rw [MixedParserStackWholeSourceAfterRawTailScanTape, hraw]
  rw [rightBlankGapPayloadScanTargetTape_defaultedCells]
  rw [MixedParserStackRewriterPrefixQuote_eq_assemblyQuotedPrefix]
  rw [MixedParserStackRewriterLengthHeader_eq_assemblyLengthHeader]
  rw [assemblySourceRestFinishPrefixQuoteOutputBits]
  simp [List.map_reverse, List.map_map,
    optionBitDefaultFalse, optionBitDefaultFalse_map_some,
    List.append_assoc]

theorem
    MixedParserStackWholeSourceAfterRawTailScanTape_move_left_move_right
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

theorem mixedOptionCellQuoteLiveTailSeparatedTape_head_rawTailLast
    (emittedPrefix rawTailInit quoteRest : Word Bool) (last : Bool) :
    (mixedOptionCellQuoteLiveTailSeparatedTape
        emittedPrefix (List.append rawTailInit [last]) quoteRest).head =
      some last := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_eq_rawTailLast]
  simp [tapeAtCells]

theorem mixedOptionCellQuoteLiveTailSeparatedTape_left_rawTailLast
    (emittedPrefix rawTailInit quoteRest : Word Bool) (last : Bool) :
    (mixedOptionCellQuoteLiveTailSeparatedTape
        emittedPrefix (List.append rawTailInit [last]) quoteRest).left =
      List.append (rawTailInit.reverse.map some)
        (emittedPrefix.reverse.map some) := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_eq_rawTailLast]
  simp [tapeAtCells]

theorem mixedOptionCellQuoteLiveTailSeparatedTape_right_rawTailLast
    (emittedPrefix rawTailInit quoteRest : Word Bool) (last : Bool) :
    (mixedOptionCellQuoteLiveTailSeparatedTape
        emittedPrefix (List.append rawTailInit [last]) quoteRest).right =
      none :: List.append (quoteRest.map some) [none] := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_eq_rawTailLast]
  simp [tapeAtCells]

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

theorem mixedOptionCellQuoteLiveTailSeparatedTape_move_right_right_rawTailLast_quoteRestCons
    (emittedPrefix rawTailInit quoteTail : Word Bool)
    (last quoteHead : Bool) :
    Tape.move Direction.right
        (Tape.move Direction.right
          (mixedOptionCellQuoteLiveTailSeparatedTape
            emittedPrefix (List.append rawTailInit [last])
            (quoteHead :: quoteTail))) =
      tapeAtCells
        (none :: some last ::
          List.append (rawTailInit.reverse.map some)
            (emittedPrefix.reverse.map some))
        (some quoteHead :: List.append (quoteTail.map some) [none]) := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_move_right_rawTailLast]
  simp [tapeAtCells, Tape.move, Tape.moveRight]

theorem
    mixedOptionCellQuoteLiveTailSeparatedTape_move_right_right_rawTailLast_preservingCons
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

theorem
    mixedOptionCellQuoteLiveTailSeparatedTape_move_right_right_assembly_sourceRestCons
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

theorem
    MixedParserStackWholeSourceAfterRawTailScanTape_eq_mixedOptionCellQuoteLiveTailSeparatedTape
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

theorem
    mixedOptionCellQuoteLiveTailSeparatedTape_cells_assembly
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

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_cells_assembly
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

theorem
    mixedOptionCellQuoteLiveTailSeparatedTape_cells_assembly_stageSplit
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
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (List.append (sourceRestBits.map some)
            (none ::
              List.append
                ((preservingCellPassCellBits sourceRestBits).map some)
                [none]))) := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_cells_assembly]
  rw [assemblySourceRestFinishRawTailBits_map_some]
  simp [List.append_assoc]

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_cells_assembly_stageSplit
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
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).map some)
            (sourceRestBits.map some))) := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape_cells_assembly]
  rw [assemblySourceRestFinishRawTailBits_map_some]

theorem
    mixedOptionCellQuoteLiveTailSeparatedTape_cells_assembly_sourceRestCons
    (w : Word Bool) (bit : Bool) (sourceRestTail : Word Bool)
    (stage : Nat) :
    Tape.cells
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w (bit :: sourceRestTail) stage)
          (assemblySourceRestFinishRawTailBits
            (bit :: sourceRestTail) stage)
          (preservingCellPassCellBits (bit :: sourceRestTail))) =
      List.append
        ((assemblySourceRestFinishPrefixQuoteOutputBits
          w (bit :: sourceRestTail) stage).map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (some bit ::
            List.append (sourceRestTail.map some)
              (none ::
                some false :: some true :: some bit ::
                  some (if bit then false else true) ::
                    List.append
                      ((preservingCellPassCellBits sourceRestTail).map some)
                      [none]))) := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_cells_assembly_stageSplit]
  rw [preservingCellPassCellBits_cons_explicit_map_some]
  simp

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_cells_assembly_sourceRestCons
    (w : Word Bool) (bit : Bool) (sourceRestTail : Word Bool)
    (stage : Nat) :
    Tape.cells
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w (bit :: sourceRestTail) stage)
          (assemblySourceRestFinishRawTailBits
            (bit :: sourceRestTail) stage)
          (preservingCellPassCellBits (bit :: sourceRestTail))) =
      List.append
        ((assemblySourceRestFinishPrefixQuoteOutputBits
          w (bit :: sourceRestTail) stage).map some)
        (List.append
          (some false :: some true :: some bit ::
            some (if bit then false else true) ::
              (preservingCellPassCellBits sourceRestTail).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).map some)
            (some bit :: sourceRestTail.map some))) := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape_cells_assembly_stageSplit]
  rw [preservingCellPassCellBits_cons_explicit_map_some]
  simp

theorem
    mixedOptionCellQuoteLiveTailSeparatedTape_eq_assembly_stageSplit
    (w sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (stageTail : Word Bool)
    (hstage :
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage = head :: stageTail) :
    mixedOptionCellQuoteLiveTailSeparatedTape
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) =
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
        ((assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage).reverse.map some)
        0 head (List.append stageTail sourceRestBits)
        (List.append
          ((preservingCellPassCellBits sourceRestBits).map some)
          [none]) := by
  rw [assemblySourceRestFinishRawTailBits, hstage]
  simp [mixedOptionCellQuoteLiveTailSeparatedTape]

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_eq_assembly_stageSplit
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

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_head_assembly_stageSplit
    (w sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (stageTail : Word Bool)
    (hstage :
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage = head :: stageTail) :
    (mixedOptionCellQuoteLiveTailJoinedTape
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits)).head =
      some head := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape_eq_assembly_stageSplit]
  rw [hstage]
  simp [tapeAtCells]

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_left_assembly_stageSplit
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (mixedOptionCellQuoteLiveTailJoinedTape
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits)).left =
      ((List.append
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits)).reverse.map some) := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape_eq_assembly_stageSplit]
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  rw [hstage]
  simp [tapeAtCells]

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_right_assembly_stageSplit
    (w sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (stageTail : Word Bool)
    (hstage :
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage = head :: stageTail) :
    (mixedOptionCellQuoteLiveTailJoinedTape
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits)).right =
      List.append (stageTail.map some) (sourceRestBits.map some) := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape_eq_assembly_stageSplit]
  rw [hstage]
  simp [tapeAtCells, List.map_append]

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_eq_assemblyQuoteRestJoinedTape
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

theorem
    mixedOptionCellQuoteLiveTailSeparatedTape_defaultedCells_assembly
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

theorem
    mixedOptionCellQuoteLiveTailSeparatedTape_defaultedCells_eq_prefixQuotedSeparatedBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailSeparatedTape
            (assemblySourceRestFinishPrefixQuoteOutputBits
              w sourceRestBits stage)
            (assemblySourceRestFinishRawTailBits sourceRestBits stage)
            (preservingCellPassCellBits sourceRestBits))) =
      assemblySourceRestFinishPrefixQuotedSeparatedBits
        w sourceRestBits stage := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_defaultedCells_assembly]
  rfl

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_defaultedCells_assembly
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

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_defaultedCells_eq_targetBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailJoinedTape
            (assemblySourceRestFinishPrefixQuoteOutputBits
              w sourceRestBits stage)
            (assemblySourceRestFinishRawTailBits sourceRestBits stage)
            (preservingCellPassCellBits sourceRestBits))) =
      assemblySourceRestFinishTargetBits w sourceRestBits stage := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape_defaultedCells_assembly]
  rw [assemblySourceRestFinishTargetBits]

theorem
    assemblySourceRestLiveTailJoinerSeparatedTape_eq_afterRawTailScanTape
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

theorem
    assemblySourceRestLiveTailJoinerJoinedTape_eq_quoteRestJoinedTape
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

theorem
    assemblySourceRestLiveTailJoinerJoinedTape_eq_targetTape
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

theorem mixedOptionCellQuoteLiveTailSeparatedTape_arbitrarySplit_ambiguous :
    mixedOptionCellQuoteLiveTailSeparatedTape [false] [true] [] =
      mixedOptionCellQuoteLiveTailSeparatedTape [] [false, true] [] := by
  native_decide

theorem mixedOptionCellQuoteLiveTailJoinedTape_arbitrarySplit_not_ambiguous :
    mixedOptionCellQuoteLiveTailJoinedTape [false] [true] [] ≠
      mixedOptionCellQuoteLiveTailJoinedTape [] [false, true] [] := by
  native_decide

def mixedOptionCellQuoteLiveTailStageSourceRawTail
    (sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      stage)
    sourceRestBits

theorem
    mixedOptionCellQuoteLiveTailStageSourceRawTail_eq_assemblyRawTail
    (sourceRestBits : Word Bool) (stage : Nat) :
    mixedOptionCellQuoteLiveTailStageSourceRawTail sourceRestBits stage =
      assemblySourceRestFinishRawTailBits sourceRestBits stage := by
  rfl

theorem mixedOptionCellQuoteLiveTailStageSourceRawTail_map_some
    (sourceRestBits : Word Bool) (stage : Nat) :
    (mixedOptionCellQuoteLiveTailStageSourceRawTail
        sourceRestBits stage).map some =
      List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage).map some)
        (sourceRestBits.map some) := by
  simp [mixedOptionCellQuoteLiveTailStageSourceRawTail, List.map_append]

theorem
    mixedOptionCellQuoteLiveTailSeparatedTape_eq_stageSource_stageSplit
    (emittedPrefix sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (stageTail : Word Bool)
    (hstage :
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage = head :: stageTail) :
    mixedOptionCellQuoteLiveTailSeparatedTape
        emittedPrefix
        (mixedOptionCellQuoteLiveTailStageSourceRawTail
          sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) =
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
        (emittedPrefix.reverse.map some)
        0 head (List.append stageTail sourceRestBits)
        (List.append
          ((preservingCellPassCellBits sourceRestBits).map some)
          [none]) := by
  rw [mixedOptionCellQuoteLiveTailStageSourceRawTail, hstage]
  simp [mixedOptionCellQuoteLiveTailSeparatedTape]

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_eq_stageSource_stageSplit
    (emittedPrefix sourceRestBits : Word Bool) (stage : Nat) :
    mixedOptionCellQuoteLiveTailJoinedTape
        emittedPrefix
        (mixedOptionCellQuoteLiveTailStageSourceRawTail
          sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) =
      tapeAtCells
        ((List.append emittedPrefix
          (preservingCellPassCellBits sourceRestBits)).reverse.map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (sourceRestBits.map some)) := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape,
    mixedOptionCellQuoteLiveTailStageSourceRawTail]
  simp [List.map_append]

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_head_stageSource_stageSplit
    (emittedPrefix sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (stageTail : Word Bool)
    (hstage :
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage = head :: stageTail) :
    (mixedOptionCellQuoteLiveTailJoinedTape
        emittedPrefix
        (mixedOptionCellQuoteLiveTailStageSourceRawTail
          sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits)).head =
      some head := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape_eq_stageSource_stageSplit]
  rw [hstage]
  simp [tapeAtCells]

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_left_stageSource_stageSplit
    (emittedPrefix sourceRestBits : Word Bool) (stage : Nat) :
    (mixedOptionCellQuoteLiveTailJoinedTape
        emittedPrefix
        (mixedOptionCellQuoteLiveTailStageSourceRawTail
          sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits)).left =
      ((List.append emittedPrefix
        (preservingCellPassCellBits sourceRestBits)).reverse.map some) := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape_eq_stageSource_stageSplit]
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  rw [hstage]
  simp [tapeAtCells]

theorem
    mixedOptionCellQuoteLiveTailJoinedTape_right_stageSource_stageSplit
    (emittedPrefix sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (stageTail : Word Bool)
    (hstage :
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage = head :: stageTail) :
    (mixedOptionCellQuoteLiveTailJoinedTape
        emittedPrefix
        (mixedOptionCellQuoteLiveTailStageSourceRawTail
          sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits)).right =
      List.append (stageTail.map some) (sourceRestBits.map some) := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape_eq_stageSource_stageSplit]
  rw [hstage]
  simp [tapeAtCells, List.map_append]

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

theorem
    mixedOptionCellQuoteLiveTailStageSourceJoiner_source_ambiguous :
    mixedOptionCellQuoteLiveTailSeparatedTape
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits
        (mixedOptionCellQuoteLiveTailStageSourceRawTail [false] 0)
        (preservingCellPassCellBits [false]) =
      mixedOptionCellQuoteLiveTailSeparatedTape
        []
        (mixedOptionCellQuoteLiveTailStageSourceRawTail [false] 1)
        (preservingCellPassCellBits [false]) := by
  native_decide

theorem
    mixedOptionCellQuoteLiveTailStageSourceJoiner_target_not_ambiguous :
    mixedOptionCellQuoteLiveTailJoinedTape
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits
        (mixedOptionCellQuoteLiveTailStageSourceRawTail [false] 0)
        (preservingCellPassCellBits [false]) ≠
      mixedOptionCellQuoteLiveTailJoinedTape
        []
        (mixedOptionCellQuoteLiveTailStageSourceRawTail [false] 1)
        (preservingCellPassCellBits [false]) := by
  native_decide

theorem
    not_MixedOptionCellQuoteLiveTailStageSourceJoinerSpec
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

theorem
    not_MixedOptionCellQuoteLiveTailStageSourceJoinerConstruction :
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
end EncodedRewriters

end Computability
end FoC
