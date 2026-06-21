import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Basic

set_option doc.verso true

/-!
# Composed dovetail-layout scanner fields

This module assembles the primitive suffix-aware scanner components into tape
and configuration field scanners.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

/-!
## Composed tape and configuration field scanners

These descriptions assemble the primitive suffix-aware scanners into the
grammar-level fields used by complete dovetail layouts.  The run theorems below
continue to work with explicit base-left contexts so the composed recognizer can
be chained field by field.
-/

def TapeSuffixScannerDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    CellListSuffixScannerDescription
    (MachineDescription.seqSubroutine
      CellSuffixScannerDescription
      CellListSuffixScannerDescription
      Direction.right)
    Direction.right

theorem tapeSuffixScannerDescription_subroutineReady :
    TapeSuffixScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    cellListSuffixScannerDescription_subroutineReady
    (MachineDescription.seqSubroutine_subroutineReady
      cellSuffixScannerDescription_subroutineReady
      cellListSuffixScannerDescription_subroutineReady)

def ConfigurationSuffixScannerDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    DovetailStagePrefix.NatSuffixScannerDescription
    TapeSuffixScannerDescription
    Direction.right

theorem configurationSuffixScannerDescription_subroutineReady :
    ConfigurationSuffixScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    DovetailStagePrefix.natSuffixScannerDescription_subroutineReady
    tapeSuffixScannerDescription_subroutineReady

def FinalHitFlagsScannerDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    BoolSuffixScannerDescription
    BoolFinalScannerDescription
    Direction.right

theorem finalHitFlagsScannerDescription_subroutineReady :
    FinalHitFlagsScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    boolSuffixScannerDescription_subroutineReady
    boolFinalScannerDescription_subroutineReady

theorem run_finalHitFlags_raw_to_handoff_withBase
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FinalHitFlagsScannerDescription.runConfig steps
          { state := FinalHitFlagsScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])).map some) } =
        { state := FinalHitFlagsScannerDescription.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                baseLeft)).tape } := by
  rcases cellCodeBits_cons_false (some rejectHit) with
    ⟨tail, htail⟩
  rcases run_boolOnlySuffix_raw_to_handoff_withBase
      acceptHit baseLeft false tail with
    ⟨acceptSteps, haccept⟩
  let baseAfterAccept :=
    List.append ((cellCodeBits (some acceptHit)).reverse.map some)
      baseLeft
  let Tmid :=
    boolOnlySuffixHandoffConfigWithBase acceptHit baseLeft
      (false :: tail)
  have hAready : BoolSuffixScannerDescription.SubroutineReady :=
    boolSuffixScannerDescription_subroutineReady
  have hBready : BoolFinalScannerDescription.SubroutineReady :=
    boolFinalScannerDescription_subroutineReady
  have hArun :
      BoolSuffixScannerDescription.runConfig acceptSteps
          { state := BoolSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])).map some) } =
        { state := BoolSuffixScannerDescription.halt
          tape := Tmid.tape } := by
    change
      BoolSuffixScannerDescription.runConfig acceptSteps
          (config 10 baseLeft
            ((boolFieldBits acceptHit
              (boolFieldBits rejectHit [])).map some)) =
        Tmid
    rw [show
        ((boolFieldBits acceptHit
          (boolFieldBits rejectHit [])).map some) =
          List.append ((cellCodeBits (some acceptHit)).map some)
            (some false :: tail.map some) by
      change
        (cellFieldBits (some acceptHit)
          (cellFieldBits (some rejectHit) [])).map some =
          List.append ((cellCodeBits (some acceptHit)).map some)
            (some false :: tail.map some)
      simp [cellFieldBits, htail, List.map_append]]
    simpa [Tmid] using haccept
  have hBReach :
      exists nB : Nat,
        BoolFinalScannerDescription.runConfig nB
            { state := BoolFinalScannerDescription.start
              tape := Tape.move Direction.right Tmid.tape } =
          { state := BoolFinalScannerDescription.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                baseAfterAccept).tape } := by
    rcases run_boolFinal_raw_to_handoff_withBase
        rejectHit baseAfterAccept with
      ⟨finalSteps, hfinal⟩
    refine ⟨finalSteps, ?_⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterAccept
            ((cellCodeBits (some rejectHit)).map some) := by
      simpa [Tmid, baseAfterAccept, htail] using
        boolOnlySuffixHandoffConfigWithBase_move_right
          acceptHit baseLeft false tail
    rw [show
        ({ state := BoolFinalScannerDescription.start
           tape := Tape.move Direction.right Tmid.tape } :
            MachineDescription.Configuration) =
          { state := BoolFinalScannerDescription.start
            tape :=
              tapeAtCells baseAfterAccept
                ((cellCodeBits (some rejectHit)).map some) } by
        simp [hmove]]
    simpa [config] using hfinal
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := BoolSuffixScannerDescription)
        (B := BoolFinalScannerDescription)
        (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [FinalHitFlagsScannerDescription, Tmid, baseAfterAccept]
    using hsteps

theorem run_cellThenCellList_raw_to_handoff_withBase
    (head : Option Bool) (right baseLeft : List (Option Bool))
    (suffixTail : Word Bool) :
    exists steps : Nat,
      (MachineDescription.seqSubroutine
          CellSuffixScannerDescription
          CellListSuffixScannerDescription
          Direction.right).runConfig steps
          { state :=
              (MachineDescription.seqSubroutine
                CellSuffixScannerDescription
                CellListSuffixScannerDescription
                Direction.right).start
            tape :=
              tapeAtCells baseLeft
                ((cellFieldBits head
                  (cellListFieldBits right
                    (false :: suffixTail))).map some) } =
        { state :=
            (MachineDescription.seqSubroutine
              CellSuffixScannerDescription
              CellListSuffixScannerDescription
              Direction.right).halt
          tape :=
            (cellListCanonicalHandoffConfigWithBase right
              (List.append ((cellCodeBits head).reverse.map some)
                baseLeft)
              (false :: suffixTail)).tape } := by
  rcases cellListFieldBits_cons_false right (false :: suffixTail) with
    ⟨fieldTail, hfieldTail⟩
  rcases run_cellSuffix_raw_to_handoff_withBase
      head baseLeft false fieldTail with
    ⟨headSteps, hhead⟩
  let baseAfterHead :=
    List.append ((cellCodeBits head).reverse.map some) baseLeft
  let Tmid := cellSuffixHandoffConfigWithBase head baseLeft
    (false :: fieldTail)
  have hAready : CellSuffixScannerDescription.SubroutineReady :=
    cellSuffixScannerDescription_subroutineReady
  have hBready : CellListSuffixScannerDescription.SubroutineReady :=
    cellListSuffixScannerDescription_subroutineReady
  have hArun :
      CellSuffixScannerDescription.runConfig headSteps
          { state := CellSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((cellFieldBits head
                  (cellListFieldBits right
                    (false :: suffixTail))).map some) } =
        { state := CellSuffixScannerDescription.halt
          tape := Tmid.tape } := by
    simpa [Tmid, cellFieldBits, hfieldTail, List.map_append] using
      hhead
  have hBReach :
      exists nB : Nat,
        CellListSuffixScannerDescription.runConfig nB
            { state := CellListSuffixScannerDescription.start
              tape := Tape.move Direction.right Tmid.tape } =
          { state := CellListSuffixScannerDescription.halt
            tape :=
              (cellListCanonicalHandoffConfigWithBase right
                baseAfterHead (false :: suffixTail)).tape } := by
    rcases run_cellList_raw_to_canonical_handoff_withBase
        right baseAfterHead suffixTail with
      ⟨rightSteps, hright⟩
    refine ⟨rightSteps, ?_⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterHead
            ((cellListFieldBits right
              (false :: suffixTail)).map some) := by
      simpa [Tmid, baseAfterHead, hfieldTail] using
        cellSuffixHandoffConfigWithBase_move_right
          head baseLeft false fieldTail
    rw [show
        ({ state := CellListSuffixScannerDescription.start
           tape := Tape.move Direction.right Tmid.tape } :
            MachineDescription.Configuration) =
          (config 100 baseAfterHead
            (List.append ((stageNatBits right.length).map some)
              (List.append ((cellsCodeBits right).map some)
                (some false :: suffixTail.map some)))) by
        simp [CellListSuffixScannerDescription, config,
          cellListFieldBits, hmove, List.map_append]]
    simpa [baseAfterHead] using hright
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := CellSuffixScannerDescription)
        (B := CellListSuffixScannerDescription)
        (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [Tmid, baseAfterHead, cellFieldBits, hfieldTail,
    List.map_append] using hsteps

theorem run_tapeSuffix_raw_to_handoff_withBase
    (T : Tape Bool) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool) :
    exists steps : Nat,
      TapeSuffixScannerDescription.runConfig steps
          { state := TapeSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((tapeFieldBits T (false :: suffixTail)).map some) } =
        { state := TapeSuffixScannerDescription.halt
          tape :=
            (cellListCanonicalHandoffConfigWithBase T.right
              (List.append ((cellCodeBits T.head).reverse.map some)
                (cellListCanonicalRestoredLeftWithBase T.left baseLeft))
              (false :: suffixTail)).tape } := by
  rcases cellFieldBits_cons_false T.head
      (cellListFieldBits T.right (false :: suffixTail)) with
    ⟨headTail, hheadTail⟩
  rcases run_cellList_raw_to_canonical_handoff_withBase
      T.left baseLeft headTail with
    ⟨leftSteps, hleft⟩
  let baseAfterLeft := cellListCanonicalRestoredLeftWithBase T.left baseLeft
  let Tmid := cellListCanonicalHandoffConfigWithBase T.left baseLeft
    (false :: headTail)
  have hAready : CellListSuffixScannerDescription.SubroutineReady :=
    cellListSuffixScannerDescription_subroutineReady
  have hBready :
      (MachineDescription.seqSubroutine
        CellSuffixScannerDescription
        CellListSuffixScannerDescription
        Direction.right).SubroutineReady :=
    MachineDescription.seqSubroutine_subroutineReady
      cellSuffixScannerDescription_subroutineReady
      cellListSuffixScannerDescription_subroutineReady
  have hArun :
      CellListSuffixScannerDescription.runConfig leftSteps
          { state := CellListSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((tapeFieldBits T (false :: suffixTail)).map some) } =
        { state := CellListSuffixScannerDescription.halt
          tape := Tmid.tape } := by
    change
      CellListSuffixScannerDescription.runConfig leftSteps
          (config 100 baseLeft
            ((tapeFieldBits T (false :: suffixTail)).map some)) =
        Tmid
    rw [show
        ((tapeFieldBits T (false :: suffixTail)).map some) =
          List.append ((stageNatBits T.left.length).map some)
            (List.append ((cellsCodeBits T.left).map some)
              (some false :: headTail.map some)) by
      change
        (cellListFieldBits T.left
          (cellFieldBits T.head
            (cellListFieldBits T.right (false :: suffixTail)))).map
            some =
          List.append ((stageNatBits T.left.length).map some)
            (List.append ((cellsCodeBits T.left).map some)
              (some false :: headTail.map some))
      rw [hheadTail]
      simp [cellListFieldBits, List.map_append]]
    simpa [Tmid] using hleft
  have hBReach :
      exists nB : Nat,
        (MachineDescription.seqSubroutine
          CellSuffixScannerDescription
          CellListSuffixScannerDescription
          Direction.right).runConfig nB
            { state :=
                (MachineDescription.seqSubroutine
                  CellSuffixScannerDescription
                  CellListSuffixScannerDescription
                  Direction.right).start
              tape := Tape.move Direction.right Tmid.tape } =
          { state :=
              (MachineDescription.seqSubroutine
                CellSuffixScannerDescription
                CellListSuffixScannerDescription
                Direction.right).halt
            tape :=
              (cellListCanonicalHandoffConfigWithBase T.right
                (List.append ((cellCodeBits T.head).reverse.map some)
                  baseAfterLeft)
                (false :: suffixTail)).tape } := by
    rcases run_cellThenCellList_raw_to_handoff_withBase
        T.head T.right baseAfterLeft suffixTail with
      ⟨innerSteps, hinner⟩
    refine ⟨innerSteps, ?_⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterLeft
            ((cellFieldBits T.head
              (cellListFieldBits T.right
                (false :: suffixTail))).map some) := by
      simpa [Tmid, baseAfterLeft, hheadTail] using
        cellListCanonicalHandoffConfigWithBase_move_right
          T.left baseLeft false headTail
    rw [show
        ({ state :=
             (MachineDescription.seqSubroutine
               CellSuffixScannerDescription
               CellListSuffixScannerDescription
               Direction.right).start
           tape := Tape.move Direction.right Tmid.tape } :
            MachineDescription.Configuration) =
          { state :=
              (MachineDescription.seqSubroutine
                CellSuffixScannerDescription
                CellListSuffixScannerDescription
                Direction.right).start
            tape :=
              tapeAtCells baseAfterLeft
                ((cellFieldBits T.head
                  (cellListFieldBits T.right
                    (false :: suffixTail))).map some) } by
        simp [hmove]]
    simpa [baseAfterLeft] using hinner
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := CellListSuffixScannerDescription)
        (B :=
          MachineDescription.seqSubroutine
            CellSuffixScannerDescription
            CellListSuffixScannerDescription
            Direction.right)
        (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [TapeSuffixScannerDescription, Tmid, baseAfterLeft,
    tapeFieldBits, hheadTail, List.map_append] using
    hsteps

theorem run_configurationSuffix_raw_to_handoff_withBase
    (cfg : MachineDescription.Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    exists steps : Nat,
      ConfigurationSuffixScannerDescription.runConfig steps
          { state := ConfigurationSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits cfg
                  (false :: suffixTail)).map some) } =
        { state := ConfigurationSuffixScannerDescription.halt
          tape :=
            (cellListCanonicalHandoffConfigWithBase cfg.tape.right
              (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
                (cellListCanonicalRestoredLeftWithBase cfg.tape.left
                  (List.append ((stageNatBits cfg.state).reverse.map some)
                    baseLeft)))
              (false :: suffixTail)).tape } := by
  rcases tapeFieldBits_cons_false cfg.tape (false :: suffixTail) with
    ⟨tapeTail, htapeTail⟩
  rcases
      DovetailStagePrefix.run_natSuffix_raw_to_handoff_withBase
        cfg.state baseLeft false tapeTail with
    ⟨stateSteps, hstate⟩
  let baseAfterState :=
    List.append ((stageNatBits cfg.state).reverse.map some) baseLeft
  let Tmid :=
    DovetailStagePrefix.natSuffixHandoffConfigWithBase
      cfg.state baseLeft (false :: tapeTail)
  have hAready :
      DovetailStagePrefix.NatSuffixScannerDescription.SubroutineReady :=
    DovetailStagePrefix.natSuffixScannerDescription_subroutineReady
  have hBready : TapeSuffixScannerDescription.SubroutineReady :=
    tapeSuffixScannerDescription_subroutineReady
  have hArun :
      DovetailStagePrefix.NatSuffixScannerDescription.runConfig
          stateSteps
          { state :=
              DovetailStagePrefix.NatSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits cfg
                  (false :: suffixTail)).map some) } =
        { state := DovetailStagePrefix.NatSuffixScannerDescription.halt
          tape := Tmid.tape } := by
    change
      DovetailStagePrefix.NatSuffixScannerDescription.runConfig
          stateSteps
          (config 200 baseLeft
            ((configurationFieldBits cfg
              (false :: suffixTail)).map some)) =
        Tmid
    rw [show
        ((configurationFieldBits cfg
          (false :: suffixTail)).map some) =
          List.append ((stageNatBits cfg.state).map some)
            (some false :: tapeTail.map some) by
      change
        (List.append (stageNatBits cfg.state)
          (tapeFieldBits cfg.tape (false :: suffixTail))).map some =
          List.append ((stageNatBits cfg.state).map some)
            (some false :: tapeTail.map some)
      rw [htapeTail]
      simp [List.map_append]]
    simpa [Tmid] using hstate
  have hBReach :
      exists nB : Nat,
        TapeSuffixScannerDescription.runConfig nB
            { state := TapeSuffixScannerDescription.start
              tape := Tape.move Direction.right Tmid.tape } =
          { state := TapeSuffixScannerDescription.halt
            tape :=
              (cellListCanonicalHandoffConfigWithBase cfg.tape.right
                (List.append
                  ((cellCodeBits cfg.tape.head).reverse.map some)
                  (cellListCanonicalRestoredLeftWithBase cfg.tape.left
                    baseAfterState))
                (false :: suffixTail)).tape } := by
    rcases run_tapeSuffix_raw_to_handoff_withBase
        cfg.tape baseAfterState suffixTail with
      ⟨tapeSteps, htape⟩
    refine ⟨tapeSteps, ?_⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterState
            ((tapeFieldBits cfg.tape
              (false :: suffixTail)).map some) := by
      simpa [Tmid, baseAfterState, htapeTail] using
        DovetailStagePrefix.natSuffixHandoffConfigWithBase_move_right
          cfg.state baseLeft false tapeTail
    rw [show
        ({ state := TapeSuffixScannerDescription.start
           tape := Tape.move Direction.right Tmid.tape } :
            MachineDescription.Configuration) =
          { state := TapeSuffixScannerDescription.start
            tape :=
              tapeAtCells baseAfterState
                ((tapeFieldBits cfg.tape
                  (false :: suffixTail)).map some) } by
        simp [hmove]]
    simpa [baseAfterState] using htape
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := DovetailStagePrefix.NatSuffixScannerDescription)
        (B := TapeSuffixScannerDescription)
        (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [ConfigurationSuffixScannerDescription, Tmid, baseAfterState,
    configurationFieldBits, htapeTail, List.map_append] using hsteps

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
