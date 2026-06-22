import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputMarkedScanner.ClosedBasic

set_option doc.verso true

/-!
# TailBits

Supporting declarations and helper lemmas for Computability Compiler Core DovetailInitialLayoutInitializer StageInputMarkedScanner TailBits.
-/


namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer
namespace StageInputMarkedScanner

def finishStartConfigWithTailBits
    (w tailBits : Word Bool) : MachineDescription.Configuration :=
  config 150 (finishStartLeft w)
    (List.append ((markedCellsBits w).map some)
      (tailBits.map some))

def markingState120WithTailBits
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool) :
    MachineDescription.Configuration :=
  config 120 (activeLengthPrefixRev processed.length)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsBits processed).map some)
        (List.append ((cellBits b).map some)
          (List.append ((cellsBits rest).map some)
            (tailBits.map some)))))

def state100AfterMarkedWithTailBits
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool) :
    MachineDescription.Configuration :=
  config 100 (finishLengthPrefixRev processed.length)
    (List.append ((stageNatBits rest.length).map some)
      (List.append ((markedCellsBits processed).map some)
        (List.append ((markedCellBits b).map some)
          (List.append ((cellsBits rest).map some)
            (tailBits.map some)))))

 /-- {name}`run_mark_current_to_state100_with_tailBits` states the corresponding theorem run form. -/
theorem run_mark_current_to_state100_with_tailBits
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (markingState120WithTailBits processed b rest tailBits) =
        state100AfterMarkedWithTailBits processed b rest tailBits := by
  let scanRev := markingReturnScanRev processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [MachineDescription.runConfig_add]
  unfold markingState120WithTailBits
  rw [run_state120_stageNat]
  rw [MachineDescription.runConfig_add]
  rw [run_state130_markedCells]
  rw [MachineDescription.runConfig_add]
  rw [run_state130_currentCell]
  have hreturn :=
    run_state140_returnToLengthMarker scanRev b
      (activeLengthPrefixTail processed.length)
      (some (!b) ::
        List.append ((cellsBits rest).map some)
          (tailBits.map some))
  cases b <;>
  simpa [state100AfterMarkedWithTailBits, scanRev,
    markingReturnScanRev, activeLengthPrefixRev,
    activeLengthPrefixRestored, markedCellBits,
    List.map_append, List.reverse_append, List.append_assoc]
    using hreturn

 /-- {name}`run_marking_loop_from_state120_with_tailBits` states the corresponding theorem run form. -/
theorem run_marking_loop_from_state120_with_tailBits
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (markingState120WithTailBits processed b rest tailBits) =
        finishStartConfigWithTailBits
          (List.append processed (b :: rest)) tailBits := by
  induction rest generalizing processed b with
  | nil =>
      rcases run_mark_current_to_state100_with_tailBits
          processed b [] tailBits with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [MachineDescription.runConfig_add]
      rw [hmark]
      unfold state100AfterMarkedWithTailBits
      change
        StageInputMarkedScannerDescription.runConfig 4
            (config 100 (finishLengthPrefixRev processed.length)
              (List.append (doneBits.map some)
                (List.append ((markedCellsBits processed).map some)
                  (List.append ((markedCellBits b).map some)
                    (tailBits.map some))))) =
          finishStartConfigWithTailBits (List.append processed [b])
            tailBits
      rw [run_state100_done]
      unfold finishStartConfigWithTailBits finishStartLeft
      rw [markedCellsBits_append_single_map]
      simp [List.length_append, List.append_assoc]
  | cons next rest ih =>
      rcases run_mark_current_to_state100_with_tailBits processed b
          (next :: rest) tailBits with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [b]) next with
        ⟨recSteps, hrec⟩
      refine ⟨markSteps + 4 + recSteps, ?_⟩
      rw [show markSteps + 4 + recSteps =
          markSteps + (4 + recSteps) by omega]
      rw [MachineDescription.runConfig_add]
      rw [hmark]
      rw [MachineDescription.runConfig_add]
      unfold state100AfterMarkedWithTailBits
      rw [show
          (stageNatBits (next :: rest).length).map some =
            List.append (tickBits.map some)
              ((stageNatBits rest.length).map some) by
        simp [stageNatBits_succ, tickBits,
          MachineDescription.encodeCodeSymbolAsInput]]
      change
        StageInputMarkedScannerDescription.runConfig recSteps
            (StageInputMarkedScannerDescription.runConfig 4
              (config 100 (finishLengthPrefixRev processed.length)
                (List.append (tickBits.map some)
                  (List.append ((stageNatBits rest.length).map some)
                    (List.append ((markedCellsBits processed).map some)
                      (List.append ((markedCellBits b).map some)
                        (List.append
                          ((cellsBits (next :: rest)).map some)
                          (tailBits.map some)))))))) =
          finishStartConfigWithTailBits
            (List.append processed (b :: next :: rest)) tailBits
      rw [run_state100_tick]
      unfold markingState120WithTailBits at hrec
      rw [markedCellsBits_append_single_map] at hrec
      simpa [activeLengthPrefixRev_succ, cellsBits_cons,
        List.length_append, List.map_append, List.append_assoc] using hrec

 /-- {name}`run_state120_bool_tail_to_finish` states the corresponding theorem run form. -/
theorem run_state120_bool_tail_to_finish
    (b : Bool) (rest tailBits : Word Bool) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (config 120 [none, some true, none, some false]
            (List.append ((stageNatBits rest.length).map some)
              (List.append ((cellBits b).map some)
                (List.append ((cellsBits rest).map some)
                  (tailBits.map some))))) =
        finishStartConfigWithTailBits (b :: rest) tailBits := by
  rcases run_marking_loop_from_state120_with_tailBits
      ([] : Word Bool) b rest tailBits with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [markingState120WithTailBits, activeLengthPrefixRev_zero]
    using hsteps

def state160AfterRestoreWithTailBits
    (w tailBits : Word Bool) : MachineDescription.Configuration :=
  config 160
    (List.append ((cellsBits w).reverse.map some)
      (finishStartLeft w))
    (some false :: none :: tailBits.map some)

def appendBlankStartConfigWithTailBits
    (w tailBits : Word Bool) : MachineDescription.Configuration :=
  config 180 [none, some false]
    (List.append ((stageInputSecondBitTailPrefix w).map some)
      (some false :: none :: tailBits.map some))

 /-- {name}`run_finish_restore_cells_tailBits` states the corresponding theorem run form. -/
theorem run_finish_restore_cells_tailBits
    (w tailBits : Word Bool) :
    StageInputMarkedScannerDescription.runConfig (4 * w.length + 2)
        (finishStartConfigWithTailBits w (false :: false :: tailBits)) =
      state160AfterRestoreWithTailBits w tailBits := by
  rw [MachineDescription.runConfig_add]
  change
    StageInputMarkedScannerDescription.runConfig 2
        (StageInputMarkedScannerDescription.runConfig (4 * w.length)
          (config 150 (finishStartLeft w)
            (List.append ((markedCellsBits w).map some)
              (some false :: some false :: tailBits.map some)))) =
      state160AfterRestoreWithTailBits w tailBits
  rw [run_state150_markedCells]
  rw [run_state150_to_state160]
  simp [state160AfterRestoreWithTailBits]

 /-- {name}`run_finish_scan_left_to_append_tailBits` states the corresponding theorem run form. -/
theorem run_finish_scan_left_to_append_tailBits
    (b : Bool) (rest tailBits : Word Bool) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (state160AfterRestoreWithTailBits (b :: rest) tailBits) =
        appendBlankStartConfigWithTailBits (b :: rest) tailBits := by
  let bits := finishScanBits (b :: rest)
  let scanRight := none :: tailBits.map some
  have hstart :
      state160AfterRestoreWithTailBits (b :: rest) tailBits =
        state160ScanConfig bits none [some false] scanRight := by
    cases b <;>
    simp [bits, scanRight, finishScanBits,
      state160AfterRestoreWithTailBits, finishStartLeft,
      finishLengthPrefixRev_eq_scanBits, state160ScanConfig,
      cellsBits_cons, cellBits, List.map_append,
      List.reverse_append, List.append_assoc]
  refine ⟨bits.length + 3, ?_⟩
  rw [show bits.length + 3 = bits.length + (1 + (1 + 1)) by
    omega]
  rw [MachineDescription.runConfig_add]
  rw [hstart]
  rw [run_state160_bits_to_boundary]
  rw [MachineDescription.runConfig_add]
  rw [run_state160_none_to_state161]
  rw [MachineDescription.runConfig_add]
  rw [run_state161_false_to_state170]
  rw [run_state170_none_to_state180]
  simp [appendBlankStartConfigWithTailBits, bits, scanRight,
    finishScanBits_reverse_nonempty, List.map_append, List.append_assoc]

 /-- {name}`run_append_blank_to_state200_tailBits` states the corresponding theorem run form. -/
theorem run_append_blank_to_state200_tailBits
    (b : Bool) (rest tailBits : Word Bool) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (appendBlankStartConfigWithTailBits (b :: rest) tailBits) =
        config 200
          (List.append
            ((stageInputSecondBitTailPrefix (b :: rest)).reverse.map some)
            (none :: [some false]))
          (some false :: some false :: tailBits.map some) := by
  let tailPrefix := stageInputSecondBitTailPrefix (b :: rest)
  refine ⟨tailPrefix.length + 2, ?_⟩
  rw [show tailPrefix.length + 2 = tailPrefix.length + (1 + 1) by
    omega]
  rw [MachineDescription.runConfig_add]
  unfold appendBlankStartConfigWithTailBits
  change
    StageInputMarkedScannerDescription.runConfig (1 + 1)
        (StageInputMarkedScannerDescription.runConfig tailPrefix.length
          (config 180 [none, some false]
            (List.append (tailPrefix.map some)
              (some false :: none :: tailBits.map some)))) =
      config 200
        (List.append (tailPrefix.reverse.map some)
          (none :: [some false]))
        (some false :: some false :: tailBits.map some)
  rw [run_state180_bits]
  rw [MachineDescription.runConfig_add]
  rw [run_state180_some]
  rw [run_state180_none_cons]

 /-- {name}`run_finish_tail_false_false_to_state200` states the corresponding theorem run form. -/
theorem run_finish_tail_false_false_to_state200
    (b : Bool) (rest tailBits : Word Bool) :
    exists steps : Nat,
      StageInputMarkedScannerDescription.runConfig steps
          (finishStartConfigWithTailBits (b :: rest)
            (false :: false :: tailBits)) =
        config 200
          (List.append
            ((stageInputSecondBitTailPrefix (b :: rest)).reverse.map some)
            (none :: [some false]))
          (some false :: some false :: tailBits.map some) := by
  rcases run_finish_scan_left_to_append_tailBits b rest tailBits with
    ⟨scanSteps, hscan⟩
  rcases run_append_blank_to_state200_tailBits b rest tailBits with
    ⟨appendSteps, happend⟩
  refine
    ⟨(4 * (b :: rest).length + 2) + scanSteps + appendSteps, ?_⟩
  rw [show
      (4 * (b :: rest).length + 2) + scanSteps + appendSteps =
        (4 * (b :: rest).length + 2) +
          (scanSteps + appendSteps) by
    omega]
  rw [MachineDescription.runConfig_add]
  rw [run_finish_restore_cells_tailBits]
  rw [MachineDescription.runConfig_add]
  rw [hscan]
  exact happend

 /-- {name}`decodeBoolWord_tick_tail_shape` captures the core lemma for this local construction. -/
theorem decodeBoolWord_tick_tail_shape
    {rest suffix : Word MachineCodeSymbol} {w : Word Bool}
    (hinput :
      MachineDescription.decodeBoolWord
          (MachineCodeSymbol.tick :: rest) =
        some (w, suffix)) :
    exists b : Bool,
    exists restW : Word Bool,
      w = b :: restW ∧
        rest =
          MachineDescription.encodeNatAppend restW.length
            (MachineDescription.encodeCellAppend (some b)
              (MachineDescription.encodeCellsAppend
                (restW.map some) suffix)) := by
  have htokens :
      MachineCodeSymbol.tick :: rest =
        MachineDescription.encodeBoolWordAppend w suffix :=
    MachineDescription.decodeBoolWord_eq_some_encodeBoolWordAppend hinput
  cases w with
  | nil =>
      simp [MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat] at htokens
  | cons b restW =>
      refine ⟨b, restW, rfl, ?_⟩
      simp [MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCellsAppend,
        MachineDescription.encodeCellAppend,
        MachineDescription.encodeCell] at htokens
      exact htokens

 /-- {name}`run_finish_tail_blank_ne_halt` states the corresponding theorem run form. -/
theorem run_finish_tail_blank_ne_halt
    (b : Bool) (rest : Word Bool)
    (suffixTail : Word MachineCodeSymbol) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (finishStartConfigWithTailBits (b :: rest)
        (MachineDescription.encodeCodeWordAsInput
          (MachineCodeSymbol.blank :: suffixTail)))).state ≠
      StageInputMarkedScannerDescription.halt := by
  let stuck :=
    config 151
      (some false ::
        List.append ((cellsBits (b :: rest)).reverse.map some)
          (finishStartLeft (b :: rest)))
      (some true :: some false :: some false ::
        (MachineDescription.encodeCodeWordAsInput suffixTail).map some)
  have hstuck :
      StageInputMarkedScannerDescription.runConfig
          (4 * (b :: rest).length + 1)
          (finishStartConfigWithTailBits (b :: rest)
            (MachineDescription.encodeCodeWordAsInput
              (MachineCodeSymbol.blank :: suffixTail))) =
        stuck := by
    rw [MachineDescription.runConfig_add]
    simpa [stuck, finishStartConfigWithTailBits,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput] using
      congrArg (StageInputMarkedScannerDescription.runConfig 1)
        (run_state150_markedCells (b :: rest)
          (finishStartLeft (b :: rest))
          ((MachineDescription.encodeCodeWordAsInput
            (MachineCodeSymbol.blank :: suffixTail)).map some))
  exact
    scanner_ne_halt_of_reaches_stuck
      (k := 4 * (b :: rest).length + 1)
      (stuck := stuck) hstuck rfl
      (by
        simp [stuck, config, StageInputMarkedScannerDescription])

 /-- {name}`run_finish_tail_zero_ne_halt` states the corresponding theorem run form. -/
theorem run_finish_tail_zero_ne_halt
    (b : Bool) (rest : Word Bool)
    (suffixTail : Word MachineCodeSymbol) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (finishStartConfigWithTailBits (b :: rest)
        (MachineDescription.encodeCodeWordAsInput
          (MachineCodeSymbol.zero :: suffixTail)))).state ≠
      StageInputMarkedScannerDescription.halt := by
  let stuck :=
    config 151
      (some false ::
        List.append ((cellsBits (b :: rest)).reverse.map some)
          (finishStartLeft (b :: rest)))
      (some true :: some false :: some true ::
        (MachineDescription.encodeCodeWordAsInput suffixTail).map some)
  have hstuck :
      StageInputMarkedScannerDescription.runConfig
          (4 * (b :: rest).length + 1)
          (finishStartConfigWithTailBits (b :: rest)
            (MachineDescription.encodeCodeWordAsInput
              (MachineCodeSymbol.zero :: suffixTail))) =
        stuck := by
    rw [MachineDescription.runConfig_add]
    simpa [stuck, finishStartConfigWithTailBits,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput] using
      congrArg (StageInputMarkedScannerDescription.runConfig 1)
        (run_state150_markedCells (b :: rest)
          (finishStartLeft (b :: rest))
          ((MachineDescription.encodeCodeWordAsInput
            (MachineCodeSymbol.zero :: suffixTail)).map some))
  exact
    scanner_ne_halt_of_reaches_stuck
      (k := 4 * (b :: rest).length + 1)
      (stuck := stuck) hstuck rfl
      (by
        simp [stuck, config, StageInputMarkedScannerDescription])

 /-- {name}`run_finish_tail_one_ne_halt` states the corresponding theorem run form. -/
theorem run_finish_tail_one_ne_halt
    (b : Bool) (rest : Word Bool)
    (suffixTail : Word MachineCodeSymbol) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (finishStartConfigWithTailBits (b :: rest)
        (MachineDescription.encodeCodeWordAsInput
          (MachineCodeSymbol.one :: suffixTail)))).state ≠
      StageInputMarkedScannerDescription.halt := by
  let stuck :=
    config 151
      (some false ::
        List.append ((cellsBits (b :: rest)).reverse.map some)
          (finishStartLeft (b :: rest)))
      (some true :: some true :: some false ::
        (MachineDescription.encodeCodeWordAsInput suffixTail).map some)
  have hstuck :
      StageInputMarkedScannerDescription.runConfig
          (4 * (b :: rest).length + 1)
          (finishStartConfigWithTailBits (b :: rest)
            (MachineDescription.encodeCodeWordAsInput
              (MachineCodeSymbol.one :: suffixTail))) =
        stuck := by
    rw [MachineDescription.runConfig_add]
    simpa [stuck, finishStartConfigWithTailBits,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput] using
      congrArg (StageInputMarkedScannerDescription.runConfig 1)
        (run_state150_markedCells (b :: rest)
          (finishStartLeft (b :: rest))
          ((MachineDescription.encodeCodeWordAsInput
            (MachineCodeSymbol.one :: suffixTail)).map some))
  exact
    scanner_ne_halt_of_reaches_stuck
      (k := 4 * (b :: rest).length + 1)
      (stuck := stuck) hstuck rfl
      (by
        simp [stuck, config, StageInputMarkedScannerDescription])

 /-- {name}`run_finish_tail_moveLeft_ne_halt` states the corresponding theorem run form. -/
theorem run_finish_tail_moveLeft_ne_halt
    (b : Bool) (rest : Word Bool)
    (suffixTail : Word MachineCodeSymbol) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (finishStartConfigWithTailBits (b :: rest)
        (MachineDescription.encodeCodeWordAsInput
          (MachineCodeSymbol.moveLeft :: suffixTail)))).state ≠
      StageInputMarkedScannerDescription.halt := by
  let stuck :=
    config 151
      (some false ::
        List.append ((cellsBits (b :: rest)).reverse.map some)
          (finishStartLeft (b :: rest)))
      (some true :: some true :: some true ::
        (MachineDescription.encodeCodeWordAsInput suffixTail).map some)
  have hstuck :
      StageInputMarkedScannerDescription.runConfig
          (4 * (b :: rest).length + 1)
          (finishStartConfigWithTailBits (b :: rest)
            (MachineDescription.encodeCodeWordAsInput
              (MachineCodeSymbol.moveLeft :: suffixTail))) =
        stuck := by
    rw [MachineDescription.runConfig_add]
    simpa [stuck, finishStartConfigWithTailBits,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput] using
      congrArg (StageInputMarkedScannerDescription.runConfig 1)
        (run_state150_markedCells (b :: rest)
          (finishStartLeft (b :: rest))
          ((MachineDescription.encodeCodeWordAsInput
            (MachineCodeSymbol.moveLeft :: suffixTail)).map some))
  exact
    scanner_ne_halt_of_reaches_stuck
      (k := 4 * (b :: rest).length + 1)
      (stuck := stuck) hstuck rfl
      (by
        simp [stuck, config, StageInputMarkedScannerDescription])

 /-- {name}`run_finish_tail_moveRight_ne_halt` states the corresponding theorem run form. -/
theorem run_finish_tail_moveRight_ne_halt
    (b : Bool) (rest : Word Bool)
    (suffixTail : Word MachineCodeSymbol) (n : Nat) :
    (StageInputMarkedScannerDescription.runConfig n
      (finishStartConfigWithTailBits (b :: rest)
        (MachineDescription.encodeCodeWordAsInput
          (MachineCodeSymbol.moveRight :: suffixTail)))).state ≠
      StageInputMarkedScannerDescription.halt := by
  let stuck :=
    config 152
      (some false ::
        List.append ((cellsBits (b :: rest)).reverse.map some)
          (finishStartLeft (b :: rest)))
      (some false :: some false :: some false ::
        (MachineDescription.encodeCodeWordAsInput suffixTail).map some)
  have hstuck :
      StageInputMarkedScannerDescription.runConfig
          (4 * (b :: rest).length + 1)
          (finishStartConfigWithTailBits (b :: rest)
            (MachineDescription.encodeCodeWordAsInput
              (MachineCodeSymbol.moveRight :: suffixTail))) =
        stuck := by
    rw [MachineDescription.runConfig_add]
    simpa [stuck, finishStartConfigWithTailBits,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput] using
      congrArg (StageInputMarkedScannerDescription.runConfig 1)
        (run_state150_markedCells (b :: rest)
          (finishStartLeft (b :: rest))
          ((MachineDescription.encodeCodeWordAsInput
            (MachineCodeSymbol.moveRight :: suffixTail)).map some))
  exact
    scanner_ne_halt_of_reaches_stuck
      (k := 4 * (b :: rest).length + 1)
      (stuck := stuck) hstuck rfl
      (by
        simp [stuck, config, StageInputMarkedScannerDescription])

 /-- {name}`encode_bool_tail_input_bits` captures the core lemma for this local construction. -/
theorem encode_bool_tail_input_bits
    (b : Bool) (restW : Word Bool)
    (suffix : Word MachineCodeSymbol) :
    (MachineDescription.encodeCodeWordAsInput
      (MachineDescription.encodeNatAppend restW.length
        (MachineDescription.encodeCellAppend (some b)
          (MachineDescription.encodeCellsAppend
            (restW.map some) suffix)))).map some =
      List.append ((stageNatBits restW.length).map some)
        (List.append ((cellBits b).map some)
          (List.append ((cellsBits restW).map some)
            ((MachineDescription.encodeCodeWordAsInput suffix).map
              some))) := by
  cases b <;>
  simp [stageNatBits, cellBits, cellsBits,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeCellAppend,
    MachineDescription.encodeCell]
  · rw [show
        MachineDescription.encodeCellsAppend (List.map some restW)
            suffix =
          List.append
            (MachineDescription.encodeCellsAppend
              (List.map some restW) [])
            suffix by
        simpa using
          (encodeCellsAppend_append (List.map some restW)
            ([] : Word MachineCodeSymbol) suffix)]
    change
      List.map some
        (MachineDescription.encodeCodeWordAsInput
          (List.append (MachineDescription.encodeNat restW.length)
            (MachineCodeSymbol.zero ::
              List.append
                (MachineDescription.encodeCellsAppend
                  (List.map some restW) [])
                suffix))) = _
    rw [MachineDescription.encodeCodeWordAsInput_append]
    simp [MachineDescription.encodeCodeWordAsInput, List.map_append]
    change
      List.map some
        (MachineDescription.encodeCodeWordAsInput
          (List.append
            (MachineDescription.encodeCellsAppend
              (List.map some restW) [])
            suffix)) = _
    rw [MachineDescription.encodeCodeWordAsInput_append]
    simp [List.map_append]
  · rw [show
        MachineDescription.encodeCellsAppend (List.map some restW)
            suffix =
          List.append
            (MachineDescription.encodeCellsAppend
              (List.map some restW) [])
            suffix by
        simpa using
          (encodeCellsAppend_append (List.map some restW)
            ([] : Word MachineCodeSymbol) suffix)]
    change
      List.map some
        (MachineDescription.encodeCodeWordAsInput
          (List.append (MachineDescription.encodeNat restW.length)
            (MachineCodeSymbol.one ::
              List.append
                (MachineDescription.encodeCellsAppend
                  (List.map some restW) [])
                suffix))) = _
    rw [MachineDescription.encodeCodeWordAsInput_append]
    simp [MachineDescription.encodeCodeWordAsInput, List.map_append]
    change
      List.map some
        (MachineDescription.encodeCodeWordAsInput
          (List.append
            (MachineDescription.encodeCellsAppend
              (List.map some restW) [])
            suffix)) = _
    rw [MachineDescription.encodeCodeWordAsInput_append]
    simp [List.map_append]

 /-- {name}`state120_tick_tail_stage_suffix_inv` captures the core lemma for this local construction. -/
theorem state120_tick_tail_stage_suffix_inv
    {rest suffix : Word MachineCodeSymbol} {w : Word Bool}
    {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (config 120 [none, some true, none, some false]
              ((MachineDescription.encodeCodeWordAsInput rest).map some)) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T })
    (hinput :
      MachineDescription.decodeBoolWord
          (MachineCodeSymbol.tick :: rest) =
        some (w, suffix)) :
    exists stage : Nat,
      suffix = MachineDescription.encodeNat stage := by
  rcases decodeBoolWord_tick_tail_shape hinput with
    ⟨b, restW, hw, hrest⟩
  subst w
  have htailBits :
      (MachineDescription.encodeCodeWordAsInput rest).map some =
        List.append ((stageNatBits restW.length).map some)
          (List.append ((cellBits b).map some)
            (List.append ((cellsBits restW).map some)
              ((MachineDescription.encodeCodeWordAsInput suffix).map
                some))) := by
    rw [hrest]
    exact encode_bool_tail_input_bits b restW suffix
  have hscannerTail :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (config 120 [none, some true, none, some false]
              (List.append ((stageNatBits restW.length).map some)
                (List.append ((cellBits b).map some)
                  (List.append ((cellsBits restW).map some)
                    ((MachineDescription.encodeCodeWordAsInput suffix).map
                      some))))) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T } := by
    rcases hscanner with ⟨steps, hsteps⟩
    refine ⟨steps, ?_⟩
    rw [← htailBits]
    exact hsteps
  rcases run_state120_bool_tail_to_finish b restW
      (MachineDescription.encodeCodeWordAsInput suffix) with
    ⟨finishSteps, hfinish⟩
  have hfinishState :
      (finishStartConfigWithTailBits (b :: restW)
        (MachineDescription.encodeCodeWordAsInput suffix)).state ≠
        StageInputMarkedScannerDescription.halt := by
    simp [finishStartConfigWithTailBits, config,
      StageInputMarkedScannerDescription]
  rcases
      runConfig_halt_after_prefix
        stageInputMarkedScannerDescription_haltTransitionFree
        hfinish hfinishState hscannerTail with
    ⟨finishRem, hscannerFinish⟩
  cases suffix with
  | nil =>
      have hno :
          (StageInputMarkedScannerDescription.runConfig finishRem
            (finishStartConfigWithTailBits (b :: restW)
              ([] : Word Bool))).state ≠
            StageInputMarkedScannerDescription.halt := by
        have hstuck :
            StageInputMarkedScannerDescription.runConfig
                (4 * (b :: restW).length)
                (finishStartConfigWithTailBits (b :: restW)
                  ([] : Word Bool)) =
              config 150
                (List.append
                  ((cellsBits (b :: restW)).reverse.map some)
                  (finishStartLeft (b :: restW)))
                ([] : List (Option Bool)) := by
          simpa [finishStartConfigWithTailBits] using
            run_state150_markedCells (b :: restW)
              (finishStartLeft (b :: restW))
              ([] : List (Option Bool))
        exact
          scanner_ne_halt_of_reaches_stuck
            (k := 4 * (b :: restW).length)
            (stuck :=
              config 150
                (List.append
                  ((cellsBits (b :: restW)).reverse.map some)
                  (finishStartLeft (b :: restW)))
                ([] : List (Option Bool)))
            hstuck
            rfl
            (by
              change (150 : Nat) ≠ 999
              omega)
      have hhalt :
          (StageInputMarkedScannerDescription.runConfig finishRem
            (finishStartConfigWithTailBits (b :: restW)
              ([] : Word Bool))).state =
            StageInputMarkedScannerDescription.halt := by
        simpa using
          congrArg MachineDescription.Configuration.state hscannerFinish
      exact False.elim (hno hhalt)
  | cons symbol suffixTail =>
      cases symbol with
      | header =>
          rcases run_finish_tail_false_false_to_state200 b restW
              (false :: false ::
                MachineDescription.encodeCodeWordAsInput suffixTail) with
            ⟨prefixSteps, hprefix⟩
          have hmid :
              (config 200
                (List.append
                  ((stageInputSecondBitTailPrefix
                    (b :: restW)).reverse.map some)
                  (none :: [some false]))
                ((MachineDescription.encodeCodeWordAsInput
                  (MachineCodeSymbol.header :: suffixTail)).map some)).state ≠
                StageInputMarkedScannerDescription.halt := by
            simp [config, StageInputMarkedScannerDescription]
          have hprefix' :
              StageInputMarkedScannerDescription.runConfig prefixSteps
                  (finishStartConfigWithTailBits (b :: restW)
                    (MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: suffixTail))) =
                config 200
                  (List.append
                    ((stageInputSecondBitTailPrefix
                      (b :: restW)).reverse.map some)
                    (none :: [some false]))
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: suffixTail)).map some) := by
            simpa [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput]
              using hprefix
          rcases
              runConfig_halt_after_prefix
                stageInputMarkedScannerDescription_haltTransitionFree
                hprefix' hmid ⟨finishRem, hscannerFinish⟩ with
            ⟨rem, hrem⟩
          exact state200_code_tail_nat_inv ⟨rem, hrem⟩
      | transition =>
          rcases run_finish_tail_false_false_to_state200 b restW
              (false :: true ::
                MachineDescription.encodeCodeWordAsInput suffixTail) with
            ⟨prefixSteps, hprefix⟩
          have hmid :
              (config 200
                (List.append
                  ((stageInputSecondBitTailPrefix
                    (b :: restW)).reverse.map some)
                  (none :: [some false]))
                ((MachineDescription.encodeCodeWordAsInput
                  (MachineCodeSymbol.transition :: suffixTail)).map
                    some)).state ≠
                StageInputMarkedScannerDescription.halt := by
            simp [config, StageInputMarkedScannerDescription]
          have hprefix' :
              StageInputMarkedScannerDescription.runConfig prefixSteps
                  (finishStartConfigWithTailBits (b :: restW)
                    (MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: suffixTail))) =
                config 200
                  (List.append
                    ((stageInputSecondBitTailPrefix
                      (b :: restW)).reverse.map some)
                    (none :: [some false]))
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: suffixTail)).map
                      some) := by
            simpa [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput]
              using hprefix
          rcases
              runConfig_halt_after_prefix
                stageInputMarkedScannerDescription_haltTransitionFree
                hprefix' hmid ⟨finishRem, hscannerFinish⟩ with
            ⟨rem, hrem⟩
          exact state200_code_tail_nat_inv ⟨rem, hrem⟩
      | tick =>
          rcases run_finish_tail_false_false_to_state200 b restW
              (true :: false ::
                MachineDescription.encodeCodeWordAsInput suffixTail) with
            ⟨prefixSteps, hprefix⟩
          have hmid :
              (config 200
                (List.append
                  ((stageInputSecondBitTailPrefix
                    (b :: restW)).reverse.map some)
                  (none :: [some false]))
                ((MachineDescription.encodeCodeWordAsInput
                  (MachineCodeSymbol.tick :: suffixTail)).map some)).state ≠
                StageInputMarkedScannerDescription.halt := by
            simp [config, StageInputMarkedScannerDescription]
          have hprefix' :
              StageInputMarkedScannerDescription.runConfig prefixSteps
                  (finishStartConfigWithTailBits (b :: restW)
                    (MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.tick :: suffixTail))) =
                config 200
                  (List.append
                    ((stageInputSecondBitTailPrefix
                      (b :: restW)).reverse.map some)
                    (none :: [some false]))
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.tick :: suffixTail)).map some) := by
            simpa [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput]
              using hprefix
          rcases
              runConfig_halt_after_prefix
                stageInputMarkedScannerDescription_haltTransitionFree
                hprefix' hmid ⟨finishRem, hscannerFinish⟩ with
            ⟨rem, hrem⟩
          exact state200_code_tail_nat_inv ⟨rem, hrem⟩
      | done =>
          rcases run_finish_tail_false_false_to_state200 b restW
              (true :: true ::
                MachineDescription.encodeCodeWordAsInput suffixTail) with
            ⟨prefixSteps, hprefix⟩
          have hmid :
              (config 200
                (List.append
                  ((stageInputSecondBitTailPrefix
                    (b :: restW)).reverse.map some)
                  (none :: [some false]))
                ((MachineDescription.encodeCodeWordAsInput
                  (MachineCodeSymbol.done :: suffixTail)).map some)).state ≠
                StageInputMarkedScannerDescription.halt := by
            simp [config, StageInputMarkedScannerDescription]
          have hprefix' :
              StageInputMarkedScannerDescription.runConfig prefixSteps
                  (finishStartConfigWithTailBits (b :: restW)
                    (MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.done :: suffixTail))) =
                config 200
                  (List.append
                    ((stageInputSecondBitTailPrefix
                      (b :: restW)).reverse.map some)
                    (none :: [some false]))
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.done :: suffixTail)).map some) := by
            simpa [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput]
              using hprefix
          rcases
              runConfig_halt_after_prefix
                stageInputMarkedScannerDescription_haltTransitionFree
                hprefix' hmid ⟨finishRem, hscannerFinish⟩ with
            ⟨rem, hrem⟩
          exact state200_code_tail_nat_inv ⟨rem, hrem⟩
      | blank =>
          have hno :=
            run_finish_tail_blank_ne_halt b restW suffixTail finishRem
          have hhalt :
              (StageInputMarkedScannerDescription.runConfig finishRem
                (finishStartConfigWithTailBits (b :: restW)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.blank :: suffixTail)))).state =
                StageInputMarkedScannerDescription.halt := by
            simpa using
              congrArg MachineDescription.Configuration.state
                hscannerFinish
          exact False.elim (hno hhalt)
      | zero =>
          have hno :=
            run_finish_tail_zero_ne_halt b restW suffixTail finishRem
          have hhalt :
              (StageInputMarkedScannerDescription.runConfig finishRem
                (finishStartConfigWithTailBits (b :: restW)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.zero :: suffixTail)))).state =
                StageInputMarkedScannerDescription.halt := by
            simpa using
              congrArg MachineDescription.Configuration.state
                hscannerFinish
          exact False.elim (hno hhalt)
      | one =>
          have hno :=
            run_finish_tail_one_ne_halt b restW suffixTail finishRem
          have hhalt :
              (StageInputMarkedScannerDescription.runConfig finishRem
                (finishStartConfigWithTailBits (b :: restW)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.one :: suffixTail)))).state =
                StageInputMarkedScannerDescription.halt := by
            simpa using
              congrArg MachineDescription.Configuration.state
                hscannerFinish
          exact False.elim (hno hhalt)
      | moveLeft =>
          have hno :=
            run_finish_tail_moveLeft_ne_halt b restW suffixTail finishRem
          have hhalt :
              (StageInputMarkedScannerDescription.runConfig finishRem
                (finishStartConfigWithTailBits (b :: restW)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: suffixTail)))).state =
                StageInputMarkedScannerDescription.halt := by
            simpa using
              congrArg MachineDescription.Configuration.state
                hscannerFinish
          exact False.elim (hno hhalt)
      | moveRight =>
          have hno :=
            run_finish_tail_moveRight_ne_halt b restW suffixTail finishRem
          have hhalt :
              (StageInputMarkedScannerDescription.runConfig finishRem
                (finishStartConfigWithTailBits (b :: restW)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: suffixTail)))).state =
                StageInputMarkedScannerDescription.halt := by
            simpa using
              congrArg MachineDescription.Configuration.state
                hscannerFinish
          exact False.elim (hno hhalt)

 /-- {name}`state120_tick_tail_code_inv` captures the core lemma for this local construction. -/
theorem state120_tick_tail_code_inv
    {rest : Word MachineCodeSymbol} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (config 120 [none, some true, none, some false]
              ((MachineDescription.encodeCodeWordAsInput rest).map some)) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists stage : Nat,
      MachineCodeSymbol.tick :: rest =
        PairedRecognizerDovetailStageInputCode w stage := by
  rcases state120_tick_tail_decodeBoolWord_inv hscanner with
    ⟨w, suffix, hinput⟩
  rcases state120_tick_tail_stage_suffix_inv hscanner hinput with
    ⟨stage, hsuffix⟩
  refine ⟨w, stage, ?_⟩
  apply MachineDescription.DovetailLayout.decodeStageInputComplete_eq_some_stageInputCode
  unfold MachineDescription.DovetailLayout.decodeStageInputComplete
  unfold MachineDescription.DovetailLayout.decodeStageInput
  rw [hinput, hsuffix]
  simp only
  rw [show
      MachineDescription.decodeNat (MachineDescription.encodeNat stage) =
        some (stage, []) by
    simpa [MachineDescription.encodeNatAppend] using
      MachineDescription.decodeNat_encodeNatAppend stage []]

 /-- {name}`scanner_marked_tick_tail_code_inv` characterizes a scan safety phase. -/
theorem scanner_marked_tick_tail_code_inv
    {rest : Word MachineCodeSymbol} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig
              (true :: false ::
                MachineDescription.encodeCodeWordAsInput rest)) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists stage : Nat,
      MachineCodeSymbol.tick :: rest =
        PairedRecognizerDovetailStageInputCode w stage := by
  have hprefix :=
    run_marked_tail_tick_to_state120
      (MachineDescription.encodeCodeWordAsInput rest)
  have hmid :
      (config 120 [none, some true, none, some false]
        ((MachineDescription.encodeCodeWordAsInput rest).map some)).state ≠
        StageInputMarkedScannerDescription.halt := by
    simp [config, StageInputMarkedScannerDescription]
  rcases
      runConfig_halt_after_prefix
        stageInputMarkedScannerDescription_haltTransitionFree
        hprefix hmid hscanner with
    ⟨rem, hrem⟩
  exact state120_tick_tail_code_inv ⟨rem, hrem⟩

 /-- {name}`scanner_marked_tick_tail_bits_shape_inv` characterizes a scan safety phase. -/
theorem scanner_marked_tick_tail_bits_shape_inv
    {rest : Word MachineCodeSymbol} {T : Tape Bool}
    (hscanner :
      exists steps : Nat,
        StageInputMarkedScannerDescription.runConfig steps
            (markedTailStartConfig
              (true :: false ::
                MachineDescription.encodeCodeWordAsInput rest)) =
          { state := StageInputMarkedScannerDescription.halt
            tape := T }) :
    exists w : Word Bool,
    exists stage : Nat,
      stageInputBits w stage =
        false :: false :: true :: false ::
          MachineDescription.encodeCodeWordAsInput rest := by
  rcases scanner_marked_tick_tail_code_inv hscanner with
    ⟨w, stage, hcode⟩
  exact ⟨w, stage, stageInputBits_tick_code_eq hcode⟩


end StageInputMarkedScanner
end DovetailInitialLayoutInitializer
end Computability
end FoC
