import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.Construction

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

/--
Core finite-machine obligation for the mixed parser-stack whole-source finisher.
The raw source word has no general delimiter for arbitrary Bool-word splits, so
the remaining leaf is stated at the parsed internal-marker layout where the live
tail boundary is part of the encoded assembly/source-rest structure.
-/
theorem
    mixedParserStackWholeSourceFinisherConstruction_for_assemblySourceRest :
    MixedParserStackWholeSourceFinisherConstructionForAssemblySourceRest := by
  sorry

theorem
    mixedParserStackDefaultedInternalMarkerFinisherConstruction_for_assemblySourceRest :
    MixedParserStackDefaultedInternalMarkerFinisherConstructionForAssemblySourceRest :=
  MixedParserStackDefaultedInternalMarkerFinisherConstructionForAssemblySourceRest_of_wholeSource
    mixedParserStackWholeSourceFinisherConstruction_for_assemblySourceRest

theorem
    mixedParserStackTrueLeftBoundaryFinisherConstruction_for_assemblySourceRest :
    MixedParserStackTrueLeftBoundaryFinisherConstructionForAssemblySourceRest :=
  MixedParserStackTrueLeftBoundaryFinisherConstructionForAssemblySourceRest_of_defaultedInternalMarker
    mixedParserStackDefaultedInternalMarkerFinisherConstruction_for_assemblySourceRest

theorem
    mixedParserStackSentinelSourceFinisherConstruction_for_assemblySourceRest :
    MixedParserStackSentinelSourceFinisherConstructionForAssemblySourceRest :=
  MixedParserStackSentinelSourceFinisherConstructionForAssemblySourceRest_of_trueLeftBoundary
    mixedParserStackTrueLeftBoundaryFinisherConstruction_for_assemblySourceRest

theorem
    assemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction :
    AssemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction := by
  exact
    AssemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction_of_sentinelSource
      mixedParserStackSentinelSourceFinisherConstruction_for_assemblySourceRest

theorem
    assemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction :
    AssemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction := by
  exact
    AssemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction_of_afterSourceRestScan
      assemblySourceRestReusableQuoteAfterSourceRestScanFinisherConstruction

theorem assemblySourceRestReusableQuoteSourceStartFinisherConstruction :
    AssemblySourceRestReusableQuoteSourceStartFinisherConstruction :=
  AssemblySourceRestReusableQuoteSourceStartFinisherConstruction_of_sourceRestBoundary
    assemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction

theorem assemblySourceRestRawBoolSourceStartFinisherConstruction :
    AssemblySourceRestRawBoolSourceStartFinisherConstruction :=
  AssemblySourceRestRawBoolSourceStartFinisherConstruction_of_reusableQuote
    assemblySourceRestReusableQuoteSourceStartFinisherConstruction

theorem
    mixedParserStackSourceStartFinisherConstruction_for_assemblySourceRest :
    MixedParserStackSourceStartFinisherConstructionForAssemblySourceRest :=
  MixedParserStackSourceStartFinisherConstructionForAssemblySourceRest_of_rawBool
    assemblySourceRestRawBoolSourceStartFinisherConstruction

theorem
    mixedParserStackRightBoundaryFinisherConstruction_for_assemblySourceRest :
    MixedParserStackRightBoundaryFinisherConstructionForAssemblySourceRest :=
  MixedParserStackRightBoundaryFinisherConstructionForAssemblySourceRest_of_sourceStart
    mixedParserStackSourceStartFinisherConstruction_for_assemblySourceRest

theorem mixedParserStackFinisherConstruction_for_assemblySourceRest :
    MixedParserStackFinisherConstructionForAssemblySourceRest :=
  MixedParserStackFinisherConstructionForAssemblySourceRest_of_trueLeftBoundary
    mixedParserStackTrueLeftBoundaryFinisherConstruction_for_assemblySourceRest

/--
Core finite-machine obligation for the left-boundary source-rest finish phase.
All surrounding results are exact-tape adapters; this leaf is responsible for
rewriting the mixed parser-stack/source-rest layout into
{name}`assemblySourceRestFinishTargetTape`.
-/
theorem assemblySourceRestFinishLeftBoundaryCoreConstruction :
    AssemblySourceRestFinishLeftBoundaryCoreConstruction :=
  assemblySourceRestFinishLeftBoundaryCoreConstruction_of_mixedParserStackFinisher
    mixedParserStackFinisherConstruction_for_assemblySourceRest

theorem assemblySourceRestFinishLeftBoundaryConstruction :
    AssemblySourceRestFinishLeftBoundaryConstruction :=
  assemblySourceRestFinishLeftBoundaryConstruction_of_core
    assemblySourceRestFinishLeftBoundaryCoreConstruction

theorem assemblySourceRestFinishQuoteBoundaryConstruction :
    AssemblySourceRestFinishQuoteBoundaryConstruction :=
  assemblySourceRestFinishQuoteBoundaryConstruction_of_leftBoundary
    assemblySourceRestFinishLeftBoundaryConstruction

theorem assemblySourceRestFinishConstruction :
    AssemblySourceRestFinishConstruction :=
  assemblySourceRestFinishConstruction_of_quoteBoundary
    assemblySourceRestFinishQuoteBoundaryConstruction

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
