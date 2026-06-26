import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.ReturnAppendDirect

set_option doc.verso true

/-!
# Checked raw Bool-word append helpers

These lemmas package the existing marked-prefix append machine on checked raw
Boolean input.  The machine appends already-encoded code bits after the raw
payload; it does not by itself quote that raw payload as a length-prefixed
{name (full := FoC.Computability.MachineDescription.encodeBoolWordAppend)}`encodeBoolWordAppend`
field.
-/

namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

def checkedNonemptyBoolWordQuoteDirectSourceBits
    (b : Bool) (rest : Word Bool)
    (suffix : Word MachineCodeSymbol) : Word Bool :=
  List.append
    (MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.tick)
    (List.append
      (List.append
        (inputTapeRightCellsDirectCopierTickBits rest.length)
        inputTapeRightCellsDirectCopierDoneBits)
      (List.append (inputTapeRightCellsDirectCopierHeadBits b)
        (List.append (inputTapeRightCellsDirectCopierCellBits rest)
          (MachineDescription.encodeCodeWordAsInput suffix))))

theorem inputTapeRightCellsDirectCopierTickDoneBits_eq_natBits
    (n : Nat) :
    List.append (inputTapeRightCellsDirectCopierTickBits n)
        inputTapeRightCellsDirectCopierDoneBits =
      MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeNat n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [inputTapeRightCellsDirectCopierTickBits_succ]
      calc
        List.append
            (List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.tick)
              (inputTapeRightCellsDirectCopierTickBits n))
            inputTapeRightCellsDirectCopierDoneBits =
          List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.tick)
            (List.append (inputTapeRightCellsDirectCopierTickBits n)
              inputTapeRightCellsDirectCopierDoneBits) := by
            simp [List.append_assoc]
        _ =
          List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.tick)
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeNat n)) := by
            rw [ih]
        _ =
          MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeNat (n + 1)) := by
            rfl

theorem inputTapeRightCellsDirectCopierCellBits_append_suffix
    (cells : Word Bool) (suffix : Word MachineCodeSymbol) :
    List.append (inputTapeRightCellsDirectCopierCellBits cells)
        (MachineDescription.encodeCodeWordAsInput suffix) =
      MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeCellsAppend (cells.map some) suffix) := by
  have h :=
    encodeCellsAppend_append (cells.map some)
      ([] : Word MachineCodeSymbol) suffix
  rw [show
      MachineDescription.encodeCellsAppend (cells.map some) suffix =
        List.append
          (MachineDescription.encodeCellsAppend (cells.map some) [])
          suffix by
      simpa using h]
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

theorem checkedNonemptyBoolWordQuoteDirectSourceBits_eq
    (b : Bool) (rest : Word Bool)
    (suffix : Word MachineCodeSymbol) :
    checkedNonemptyBoolWordQuoteDirectSourceBits b rest suffix =
      MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeBoolWordAppend (b :: rest) suffix) := by
  have hnat :=
    inputTapeRightCellsDirectCopierTickDoneBits_eq_natBits
      rest.length
  have hcells :=
    inputTapeRightCellsDirectCopierCellBits_append_suffix
      rest suffix
  cases b
  · rw [show
        checkedNonemptyBoolWordQuoteDirectSourceBits false rest suffix =
          List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.tick)
            (List.append
              (List.append
                (inputTapeRightCellsDirectCopierTickBits rest.length)
                inputTapeRightCellsDirectCopierDoneBits)
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput
                  MachineCodeSymbol.zero)
                (List.append (inputTapeRightCellsDirectCopierCellBits rest)
                  (MachineDescription.encodeCodeWordAsInput suffix)))) by
        rfl]
    rw [hnat, hcells]
    simp only [MachineDescription.encodeBoolWordAppend,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend]
    rw [MachineDescription.encodeCodeWordAsInput_append]
    simp [MachineDescription.encodeNat,
      MachineDescription.encodeCellsAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell,
      MachineDescription.encodeCodeWordAsInput,
      List.append_assoc]
  · rw [show
        checkedNonemptyBoolWordQuoteDirectSourceBits true rest suffix =
          List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.tick)
            (List.append
              (List.append
                (inputTapeRightCellsDirectCopierTickBits rest.length)
                inputTapeRightCellsDirectCopierDoneBits)
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput
                  MachineCodeSymbol.one)
                (List.append (inputTapeRightCellsDirectCopierCellBits rest)
                  (MachineDescription.encodeCodeWordAsInput suffix)))) by
        rfl]
    rw [hnat, hcells]
    simp only [MachineDescription.encodeBoolWordAppend,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend]
    rw [MachineDescription.encodeCodeWordAsInput_append]
    simp [MachineDescription.encodeNat,
      MachineDescription.encodeCellsAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell,
      MachineDescription.encodeCodeWordAsInput,
      List.append_assoc]

def checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits
    (rest : Word Bool) : Word Bool :=
  List.append (inputTapeRightCellsDirectCopierTickBits rest.length)
    (List.append inputTapeRightCellsDirectCopierDoneBits
      (inputTapeRightCellsDirectCopierCellBits rest))

theorem checkedNonemptyBoolWordQuoteDirectSourceBits_encodeNatAppend
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol) :
    checkedNonemptyBoolWordQuoteDirectSourceBits b rest
        (MachineDescription.encodeNatAppend stage suffix) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.tick)
        (inputTapeRightCellsDirectCopierCoreSourceBits b rest stage
          (MachineDescription.encodeCodeWordAsInput suffix)) := by
  unfold checkedNonemptyBoolWordQuoteDirectSourceBits
  unfold inputTapeRightCellsDirectCopierCoreSourceBits
  unfold inputTapeRightCellsDirectCopierNatBits
  simp only [MachineDescription.encodeNatAppend]
  rw [MachineDescription.encodeCodeWordAsInput_append]
  simp [List.append_assoc]

theorem inputTapeRightCellsDirectCopierDescription_run_checkedQuoteNative
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffix : Word MachineCodeSymbol) :
    exists steps : Nat,
      InputTapeRightCellsDirectCopierDescription.runConfig steps
          (config 0
            (List.append
              ((MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.tick).reverse.map some)
              [none, some false])
            ((inputTapeRightCellsDirectCopierCoreSourceBits b rest stage
              (MachineDescription.encodeCodeWordAsInput suffix)).map
              some)) =
        config 99 [some false]
          (some false ::
            ((List.append
              (checkedNonemptyBoolWordQuoteDirectSourceBits b rest
                (MachineDescription.encodeNatAppend stage suffix))
              (checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits
                rest)).map some)) := by
  let pre0 :=
    MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.tick
  let tickBits := inputTapeRightCellsDirectCopierTickBits rest.length
  let doneBits := inputTapeRightCellsDirectCopierDoneBits
  let headBits := inputTapeRightCellsDirectCopierHeadBits b
  let cellBits := inputTapeRightCellsDirectCopierCellBits rest
  let stageBits := inputTapeRightCellsDirectCopierNatBits stage
  let suffixBits := MachineDescription.encodeCodeWordAsInput suffix
  let sourceTailAfterDone : Word Bool :=
    List.append cellBits (List.append stageBits suffixBits)
  let outputAfterDone : Word Bool :=
    List.append tickBits doneBits
  let preAfterDone : Word Bool :=
    List.append pre0
      (List.append tickBits (List.append doneBits headBits))
  rcases
      inputTapeRightCellsDirectCopierDescription_run_copy_ticks
        rest.length [some false] pre0
        (List.append doneBits
          (List.append headBits sourceTailAfterDone))
        [] with
    ⟨tickSteps, hticks⟩
  have hdoneExists :
      exists steps : Nat,
        InputTapeRightCellsDirectCopierDescription.runConfig steps
            (config 0
              (List.append ((List.append pre0 tickBits).reverse.map some)
                [none, some false])
              ((List.append doneBits
                (List.append headBits
                  (List.append sourceTailAfterDone tickBits))).map some)) =
          config 10
            (List.append (preAfterDone.reverse.map some)
              [none, some false])
            ((List.append sourceTailAfterDone outputAfterDone).map
              some) := by
    by_cases hb : b = true
    · subst b
      simpa [headBits, inputTapeRightCellsDirectCopierHeadBits,
        doneBits, inputTapeRightCellsDirectCopierDoneBits,
        sourceTailAfterDone, outputAfterDone, preAfterDone,
        List.reverse_append, List.map_append, List.append_assoc] using
        inputTapeRightCellsDirectCopierDescription_run_copy_done_skip_four
          [some false] (List.append pre0 tickBits)
          sourceTailAfterDone tickBits false true true false
    · cases b
      · simpa [headBits, inputTapeRightCellsDirectCopierHeadBits,
          doneBits, inputTapeRightCellsDirectCopierDoneBits,
          sourceTailAfterDone, outputAfterDone, preAfterDone,
          List.reverse_append, List.map_append, List.append_assoc] using
          inputTapeRightCellsDirectCopierDescription_run_copy_done_skip_four
            [some false] (List.append pre0 tickBits)
            sourceTailAfterDone tickBits false true false true
      · contradiction
  rcases hdoneExists with ⟨doneSteps, hdone⟩
  rcases
      inputTapeRightCellsDirectCopierDescription_run_copy_cells
        rest preAfterDone (List.append stageBits suffixBits)
        outputAfterDone with
    ⟨cellSteps, hcells⟩
  have hstop :=
    inputTapeRightCellsDirectCopierDescription_run_stop_at_natBits
      (List.append preAfterDone cellBits) stage
      (List.append suffixBits
        (List.append outputAfterDone cellBits))
  refine
    ⟨tickSteps + doneSteps + cellSteps +
      ((List.append preAfterDone cellBits).length + 5), ?_⟩
  rw [show tickSteps + doneSteps + cellSteps +
        ((List.append preAfterDone cellBits).length + 5) =
      tickSteps + (doneSteps + (cellSteps +
        ((List.append preAfterDone cellBits).length + 5))) by
      omega]
  rw [MachineDescription.runConfig_add]
  rw [show
      config 0
        (List.append
          ((MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.tick).reverse.map some)
          [none, some false])
        ((inputTapeRightCellsDirectCopierCoreSourceBits b rest stage
          (MachineDescription.encodeCodeWordAsInput suffix)).map some) =
      config 0
        (List.append (pre0.reverse.map some) [none, some false])
        ((List.append tickBits
          (List.append
            (List.append doneBits
              (List.append headBits sourceTailAfterDone))
            [])).map some) by
      simp [pre0, tickBits, doneBits, headBits, cellBits,
        stageBits, suffixBits, sourceTailAfterDone,
        inputTapeRightCellsDirectCopierCoreSourceBits]]
  rw [hticks]
  rw [MachineDescription.runConfig_add]
  rw [show
      config 0
        (List.append (tickBits.reverse.map some)
          (List.append (pre0.reverse.map some) [none, some false]))
        ((List.append
          (List.append doneBits
            (List.append headBits sourceTailAfterDone))
          (List.append [] tickBits)).map some) =
      config 0
        (List.append ((List.append pre0 tickBits).reverse.map some)
          [none, some false])
        ((List.append doneBits
          (List.append headBits
            (List.append sourceTailAfterDone tickBits))).map some) by
      simp [List.reverse_append, List.map_append, List.append_assoc]]
  rw [hdone]
  rw [MachineDescription.runConfig_add]
  rw [show
      config 10
        (List.append (preAfterDone.reverse.map some) [none, some false])
        ((List.append sourceTailAfterDone
          (List.append tickBits doneBits)).map some) =
      config 10
        (List.append (preAfterDone.reverse.map some) [none, some false])
        ((List.append cellBits
          (List.append (List.append stageBits suffixBits)
            outputAfterDone)).map some) by
      simp [sourceTailAfterDone, outputAfterDone, List.append_assoc]]
  rw [hcells]
  rw [show
      config 10
        (List.append
          ((List.append preAfterDone
            (inputTapeRightCellsDirectCopierCellBits rest)).reverse.map
              some)
          [none, some false])
        ((List.append (List.append stageBits suffixBits)
          (List.append outputAfterDone
            (inputTapeRightCellsDirectCopierCellBits rest))).map some) =
      config 10
        (List.append ((List.append preAfterDone cellBits).reverse.map some)
          [none, some false])
        ((List.append
          (inputTapeRightCellsDirectCopierNatBits stage)
          (List.append suffixBits
            (List.append outputAfterDone cellBits))).map some) by
      simp [cellBits, stageBits, List.append_assoc]]
  rw [hstop]
  rw [checkedNonemptyBoolWordQuoteDirectSourceBits_encodeNatAppend]
  simp [pre0, tickBits, doneBits, headBits, cellBits,
    suffixBits, outputAfterDone, preAfterDone,
    checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits,
    inputTapeRightCellsDirectCopierCoreSourceBits,
    inputTapeRightCellsDirectCopierDoneBits,
    inputTapeRightCellsDirectCopierNatBits,
    List.map_append, List.append_assoc]

def CheckedRawBoolWordAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MarkedPrefixAppendCodeWordReturnDescription code

theorem checkedRawBoolWordAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (CheckedRawBoolWordAppendCodeWordReturnDescription code).SubroutineReady :=
  markedPrefixAppendCodeWordReturnDescription_subroutineReady code hcode

theorem checkedRawBoolWordAppendCodeWordReturnDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (CheckedRawBoolWordAppendCodeWordReturnDescription code).runConfig steps
          { state :=
              (CheckedRawBoolWordAppendCodeWordReturnDescription code).start
            tape :=
              tapeAtCells []
                (List.append (some b :: rest.map some) [none]) } =
        { state :=
            (CheckedRawBoolWordAppendCodeWordReturnDescription code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  simpa [CheckedRawBoolWordAppendCodeWordReturnDescription] using
    markedPrefixAppendCodeWordReturnDescription_run_checked
      code hcode b rest

theorem checkedRawBoolWordAppendCodeWordReturnDescription_haltsFromTape
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (b : Bool) (rest : Word Bool) :
    (CheckedRawBoolWordAppendCodeWordReturnDescription code).HaltsFromTape
      (tapeAtCells []
        (List.append (some b :: rest.map some) [none]))
      (tapeAtCells [some false]
        (some false ::
          ((List.append (false :: true :: b :: rest)
            (MachineDescription.encodeCodeWordAsInput code)).map
            some))) := by
  rcases
      checkedRawBoolWordAppendCodeWordReturnDescription_run
        code hcode b rest with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.tape hsteps

def CheckedRawBoolWordAppendHeaderReturnDescription
    (suffix : Word MachineCodeSymbol) : MachineDescription :=
  CheckedRawBoolWordAppendCodeWordReturnDescription
    (MachineCodeSymbol.header :: suffix)

theorem
    checkedRawBoolWordAppendHeaderReturnDescription_subroutineReady
    (suffix : Word MachineCodeSymbol) :
    (CheckedRawBoolWordAppendHeaderReturnDescription
      suffix).SubroutineReady :=
  checkedRawBoolWordAppendCodeWordReturnDescription_subroutineReady
    (MachineCodeSymbol.header :: suffix)
    (by intro h; cases h)

theorem checkedRawBoolWordAppendHeaderReturnDescription_run
    (suffix : Word MachineCodeSymbol)
    (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (CheckedRawBoolWordAppendHeaderReturnDescription suffix).runConfig steps
          { state :=
              (CheckedRawBoolWordAppendHeaderReturnDescription suffix).start
            tape :=
              tapeAtCells []
                (List.append (some b :: rest.map some) [none]) } =
        { state :=
            (CheckedRawBoolWordAppendHeaderReturnDescription suffix).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: suffix))).map
                  some)) } := by
  simpa [CheckedRawBoolWordAppendHeaderReturnDescription] using
    checkedRawBoolWordAppendCodeWordReturnDescription_run
      (MachineCodeSymbol.header :: suffix)
      (by intro h; cases h)
      b rest

theorem checkedRawBoolWordAppendHeaderReturnDescription_haltsFromTape
    (suffix : Word MachineCodeSymbol)
    (b : Bool) (rest : Word Bool) :
    (CheckedRawBoolWordAppendHeaderReturnDescription suffix).HaltsFromTape
      (tapeAtCells []
        (List.append (some b :: rest.map some) [none]))
      (tapeAtCells [some false]
        (some false ::
          ((List.append (false :: true :: b :: rest)
            (MachineDescription.encodeCodeWordAsInput
              (MachineCodeSymbol.header :: suffix))).map
            some))) := by
  rcases
      checkedRawBoolWordAppendHeaderReturnDescription_run
        suffix b rest with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.tape hsteps

end DovetailInitialLayoutInitializer
end Computability
end FoC
