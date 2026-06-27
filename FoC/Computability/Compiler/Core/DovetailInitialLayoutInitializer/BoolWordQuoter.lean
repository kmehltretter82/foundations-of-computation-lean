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

def controllerInitialRawBoolWordHeaderEmitterSuffix :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend 0
    (MachineDescription.encodeBoolWordAppend [] [])

def ControllerInitialRawBoolWordHeaderEmitterDescription :
    MachineDescription where
  stateCount := 71
  start := 0
  halt := 70
  transitions :=
    [ MachineDescription.transition 0 (some false) (some false) Direction.right 0
    , MachineDescription.transition 0 (some true) (some true) Direction.right 0
    , MachineDescription.transition 0 none none Direction.right 1
    , MachineDescription.transition 1 (some false) (some false) Direction.right 1
    , MachineDescription.transition 1 (some true) (some true) Direction.right 1
    , MachineDescription.transition 1 none (some false) Direction.right 2
    , MachineDescription.transition 2 none (some false) Direction.right 3
    , MachineDescription.transition 3 none (some false) Direction.right 4
    , MachineDescription.transition 4 none (some false) Direction.right 5
    , MachineDescription.transition 5 none none Direction.left 8
    , MachineDescription.transition 8 (some false) (some false) Direction.left 8
    , MachineDescription.transition 8 (some true) (some true) Direction.left 8
    , MachineDescription.transition 8 none none Direction.left 6
    , MachineDescription.transition 6 (some false) (some false) Direction.left 6
    , MachineDescription.transition 6 (some true) (some true) Direction.left 6
    , MachineDescription.transition 6 none none Direction.right 7
    , MachineDescription.transition 7 (some false) none Direction.right 10
    , MachineDescription.transition 7 (some true) none Direction.right 20
    , MachineDescription.transition 7 none none Direction.right 30
    , MachineDescription.transition 10 (some false) (some false) Direction.right 10
    , MachineDescription.transition 10 (some true) (some true) Direction.right 10
    , MachineDescription.transition 10 none none Direction.right 11
    , MachineDescription.transition 11 (some false) (some false) Direction.right 11
    , MachineDescription.transition 11 (some true) (some true) Direction.right 11
    , MachineDescription.transition 11 none (some false) Direction.right 12
    , MachineDescription.transition 12 none (some false) Direction.right 13
    , MachineDescription.transition 13 none (some true) Direction.right 14
    , MachineDescription.transition 14 none (some false) Direction.right 15
    , MachineDescription.transition 15 none none Direction.left 17
    , MachineDescription.transition 17 (some false) (some false) Direction.left 17
    , MachineDescription.transition 17 (some true) (some true) Direction.left 17
    , MachineDescription.transition 17 none none Direction.left 16
    , MachineDescription.transition 16 (some false) (some false) Direction.left 16
    , MachineDescription.transition 16 (some true) (some true) Direction.left 16
    , MachineDescription.transition 16 none (some false) Direction.right 7
    , MachineDescription.transition 20 (some false) (some false) Direction.right 20
    , MachineDescription.transition 20 (some true) (some true) Direction.right 20
    , MachineDescription.transition 20 none none Direction.right 21
    , MachineDescription.transition 21 (some false) (some false) Direction.right 21
    , MachineDescription.transition 21 (some true) (some true) Direction.right 21
    , MachineDescription.transition 21 none (some false) Direction.right 22
    , MachineDescription.transition 22 none (some false) Direction.right 23
    , MachineDescription.transition 23 none (some true) Direction.right 24
    , MachineDescription.transition 24 none (some false) Direction.right 25
    , MachineDescription.transition 25 none none Direction.left 27
    , MachineDescription.transition 27 (some false) (some false) Direction.left 27
    , MachineDescription.transition 27 (some true) (some true) Direction.left 27
    , MachineDescription.transition 27 none none Direction.left 26
    , MachineDescription.transition 26 (some false) (some false) Direction.left 26
    , MachineDescription.transition 26 (some true) (some true) Direction.left 26
    , MachineDescription.transition 26 none (some true) Direction.right 7
    , MachineDescription.transition 30 (some false) (some false) Direction.right 30
    , MachineDescription.transition 30 (some true) (some true) Direction.right 30
    , MachineDescription.transition 30 none (some false) Direction.right 31
    , MachineDescription.transition 31 none (some false) Direction.right 32
    , MachineDescription.transition 32 none (some true) Direction.right 33
    , MachineDescription.transition 33 none (some true) Direction.right 34
    , MachineDescription.transition 34 none none Direction.left 37
    , MachineDescription.transition 37 (some false) (some false) Direction.left 37
    , MachineDescription.transition 37 (some true) (some true) Direction.left 37
    , MachineDescription.transition 37 none none Direction.left 35
    , MachineDescription.transition 35 (some false) (some false) Direction.left 35
    , MachineDescription.transition 35 (some true) (some true) Direction.left 35
    , MachineDescription.transition 35 none none Direction.right 36
    , MachineDescription.transition 36 (some false) none Direction.right 40
    , MachineDescription.transition 36 (some true) none Direction.right 50
    , MachineDescription.transition 36 none none Direction.right 60
    , MachineDescription.transition 40 (some false) (some false) Direction.right 40
    , MachineDescription.transition 40 (some true) (some true) Direction.right 40
    , MachineDescription.transition 40 none none Direction.right 41
    , MachineDescription.transition 41 (some false) (some false) Direction.right 41
    , MachineDescription.transition 41 (some true) (some true) Direction.right 41
    , MachineDescription.transition 41 none (some false) Direction.right 42
    , MachineDescription.transition 42 none (some true) Direction.right 43
    , MachineDescription.transition 43 none (some false) Direction.right 44
    , MachineDescription.transition 44 none (some true) Direction.right 45
    , MachineDescription.transition 45 none none Direction.left 47
    , MachineDescription.transition 47 (some false) (some false) Direction.left 47
    , MachineDescription.transition 47 (some true) (some true) Direction.left 47
    , MachineDescription.transition 47 none none Direction.left 46
    , MachineDescription.transition 46 (some false) (some false) Direction.left 46
    , MachineDescription.transition 46 (some true) (some true) Direction.left 46
    , MachineDescription.transition 46 none none Direction.right 36
    , MachineDescription.transition 50 (some false) (some false) Direction.right 50
    , MachineDescription.transition 50 (some true) (some true) Direction.right 50
    , MachineDescription.transition 50 none none Direction.right 51
    , MachineDescription.transition 51 (some false) (some false) Direction.right 51
    , MachineDescription.transition 51 (some true) (some true) Direction.right 51
    , MachineDescription.transition 51 none (some false) Direction.right 52
    , MachineDescription.transition 52 none (some true) Direction.right 53
    , MachineDescription.transition 53 none (some true) Direction.right 54
    , MachineDescription.transition 54 none (some false) Direction.right 55
    , MachineDescription.transition 55 none none Direction.left 57
    , MachineDescription.transition 57 (some false) (some false) Direction.left 57
    , MachineDescription.transition 57 (some true) (some true) Direction.left 57
    , MachineDescription.transition 57 none none Direction.left 56
    , MachineDescription.transition 56 (some false) (some false) Direction.left 56
    , MachineDescription.transition 56 (some true) (some true) Direction.left 56
    , MachineDescription.transition 56 none none Direction.right 36
    , MachineDescription.transition 60 (some false) (some false) Direction.right 60
    , MachineDescription.transition 60 (some true) (some true) Direction.right 60
    , MachineDescription.transition 60 none (some false) Direction.right 61
    , MachineDescription.transition 61 none (some false) Direction.right 62
    , MachineDescription.transition 62 none (some true) Direction.right 63
    , MachineDescription.transition 63 none (some true) Direction.right 64
    , MachineDescription.transition 64 none (some false) Direction.right 65
    , MachineDescription.transition 65 none (some false) Direction.right 66
    , MachineDescription.transition 66 none (some true) Direction.right 67
    , MachineDescription.transition 67 none (some true) Direction.right 70
    ]

theorem controllerInitialRawBoolWordHeaderEmitterDescription_wellFormed :
    ControllerInitialRawBoolWordHeaderEmitterDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ControllerInitialRawBoolWordHeaderEmitterDescription.transitions)
      (stateCount :=
        ControllerInitialRawBoolWordHeaderEmitterDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ControllerInitialRawBoolWordHeaderEmitterDescription.transitions)
      (by native_decide)

theorem
    controllerInitialRawBoolWordHeaderEmitterDescription_haltTransitionFree :
    ControllerInitialRawBoolWordHeaderEmitterDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ControllerInitialRawBoolWordHeaderEmitterDescription.transitions)
    (state := ControllerInitialRawBoolWordHeaderEmitterDescription.halt)
    (by native_decide)

theorem controllerInitialRawBoolWordHeaderEmitterDescription_subroutineReady :
    ControllerInitialRawBoolWordHeaderEmitterDescription.SubroutineReady :=
  ⟨controllerInitialRawBoolWordHeaderEmitterDescription_wellFormed,
    controllerInitialRawBoolWordHeaderEmitterDescription_haltTransitionFree⟩

def controllerInitialRawBoolWordHeaderEmitterOutput
    (w : Word Bool) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineCodeSymbol.header ::
      MachineDescription.encodeBoolWordAppend w
        controllerInitialRawBoolWordHeaderEmitterSuffix)

def controllerInitialRawBoolWordHeaderEmitterFinalTape
    (w : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append
      ((controllerInitialRawBoolWordHeaderEmitterOutput w).reverse.map some)
      (List.replicate (w.length + 2) none))
    []

theorem controllerInitialRawBoolWordHeaderEmitterFinalTape_normalizedOutput
    (w : Word Bool) :
    Tape.normalizedOutput
        (controllerInitialRawBoolWordHeaderEmitterFinalTape w) =
      controllerInitialRawBoolWordHeaderEmitterOutput w := by
  rw [Tape.normalizedOutput]
  simp [controllerInitialRawBoolWordHeaderEmitterFinalTape,
    Tape.cells, tapeAtCells, List.filterMap_append,
    List.map_reverse]
  induction controllerInitialRawBoolWordHeaderEmitterOutput w with
  | nil => rfl
  | cons b rest ih => simp [ih]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan0
    (leftRev : List (Option Bool)) (w : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (w.length + 1)
        (config 0 leftRev (w.map some)) =
      config 1
        (none :: List.append (w.reverse.map some) leftRev)
        [] := by
  induction w generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 0 leftRev ((false :: rest).map some)) =
            config 0 (some false :: leftRev) (rest.map some) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 0 leftRev ((true :: rest).map some)) =
            config 0 (some true :: leftRev) (rest.map some) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan10
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (rest.length + 1)
        (config 10 leftRev
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none]))) =
      config 11
        (none :: List.append (rest.reverse.map some) leftRev)
        (List.append (output.map some) [none]) := by
  induction rest generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
      cases output <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 10 leftRev
                (List.append ((false :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 10 (some false :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 10 leftRev
                (List.append ((true :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 10 (some true :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan20
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (rest.length + 1)
        (config 20 leftRev
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none]))) =
      config 21
        (none :: List.append (rest.reverse.map some) leftRev)
        (List.append (output.map some) [none]) := by
  induction rest generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
      cases output <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 20 leftRev
                (List.append ((false :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 20 (some false :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 20 leftRev
                (List.append ((true :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 20 (some true :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan11
    (leftRev : List (Option Bool)) (output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (output.length + 1)
        (config 11 leftRev (List.append (output.map some) [none])) =
      config 12
        (some false :: List.append (output.reverse.map some) leftRev)
        [] := by
  induction output generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 11 leftRev
                (List.append ((false :: rest).map some) [none])) =
            config 11 (some false :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 11 leftRev
                (List.append ((true :: rest).map some) [none])) =
            config 11 (some true :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan21
    (leftRev : List (Option Bool)) (output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (output.length + 1)
        (config 21 leftRev (List.append (output.map some) [none])) =
      config 22
        (some false :: List.append (output.reverse.map some) leftRev)
        [] := by
  induction output generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 21 leftRev
                (List.append ((false :: rest).map some) [none])) =
            config 21 (some false :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 21 leftRev
                (List.append ((true :: rest).map some) [none])) =
            config 21 (some true :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

def controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
    (rawLeft : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) : Tape Bool :=
  match scanRev with
  | [] => tapeAtCells rawLeft (none :: right)
  | b :: rest =>
      { left := List.append (rest.map some) (none :: rawLeft)
        head := some b
        right := right }

def controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
    (leftRev : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) : Tape Bool :=
  match scanRev with
  | [] => tapeAtCells leftRev (none :: right)
  | b :: rest =>
      { left := List.append (rest.map some) (none :: leftRev)
        head := some b
        right := right }

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan17
    (leftRev : List (Option Bool)) (rawRev outputRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 17
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rawRev.map some) (none :: leftRev))
              outputRev right } =
      { state := 16
        tape :=
          controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
            leftRev rawRev
            (none :: List.append (outputRev.reverse.map some) right) } := by
  induction outputRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
        controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        ControllerInitialRawBoolWordHeaderEmitterDescription,
        tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft]
      cases rawRev <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 17
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (false :: rest) right } =
            { state := 17
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 17
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (true :: rest) right } =
            { state := 17
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan27
    (leftRev : List (Option Bool)) (rawRev outputRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 27
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rawRev.map some) (none :: leftRev))
              outputRev right } =
      { state := 26
        tape :=
          controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
            leftRev rawRev
            (none :: List.append (outputRev.reverse.map some) right) } := by
  induction outputRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
        controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        ControllerInitialRawBoolWordHeaderEmitterDescription,
        tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft]
      cases rawRev <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 27
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (false :: rest) right } =
            { state := 27
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 27
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (true :: rest) right } =
            { state := 27
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_return16
    (leftRev : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (scanRev.length + 1)
        { state := 16
          tape :=
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
              leftRev scanRev right } =
      config 7 (some false :: leftRev)
        (List.append (scanRev.reverse.map some) right) := by
  induction scanRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
      cases right <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 16
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (false :: rest) right } =
            { state := 16
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 16
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (true :: rest) right } =
            { state := 16
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_return26
    (leftRev : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (scanRev.length + 1)
        { state := 26
          tape :=
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
              leftRev scanRev right } =
      config 7 (some true :: leftRev)
        (List.append (scanRev.reverse.map some) right) := by
  induction scanRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
      cases right <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 26
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (false :: rest) right } =
            { state := 26
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 26
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (true :: rest) right } =
            { state := 26
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitterDescription_run
    (w : Word Bool) :
    exists steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
          (ControllerInitialRawBoolWordHeaderEmitterDescription.initial w) =
        { state := ControllerInitialRawBoolWordHeaderEmitterDescription.halt
          tape := controllerInitialRawBoolWordHeaderEmitterFinalTape w } := by
  sorry

theorem controllerInitialRawBoolWordHeaderEmitterDescription_haltsWithOutput
    (w : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.HaltsWithOutput w
      (controllerInitialRawBoolWordHeaderEmitterOutput w) := by
  rcases
      controllerInitialRawBoolWordHeaderEmitterDescription_run w with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsWithOutputIn] using
      congrArg MachineDescription.Configuration.state hsteps
  · rw [show
        (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
          steps
          (ControllerInitialRawBoolWordHeaderEmitterDescription.initial
            w)).tape =
          controllerInitialRawBoolWordHeaderEmitterFinalTape w by
        simpa [MachineDescription.HaltsWithOutputIn] using
          congrArg MachineDescription.Configuration.tape hsteps]
    exact
      controllerInitialRawBoolWordHeaderEmitterFinalTape_normalizedOutput w

end DovetailInitialLayoutInitializer
end Computability
end FoC
