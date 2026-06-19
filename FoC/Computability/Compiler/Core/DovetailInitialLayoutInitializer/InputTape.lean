import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.ReturnAppend

set_option doc.verso true

/-!
# InputTape

Supporting declarations and helper lemmas for Computability Compiler Core DovetailInitialLayoutInitializer InputTape.
-/


namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

 /-- `exactIdentityDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem exactIdentityDescription_subroutineReady :
    MachineDescription.ExactIdentityDescription.SubroutineReady :=
  ⟨MachineDescription.exactIdentityDescription_wellFormed,
    MachineDescription.exactIdentityDescription_haltTransitionFree⟩

def TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    MachineDescription.ExactIdentityDescription
    (TransitionPrefixedAppendCodeWordReturnDescription code)
    Direction.right
     /-- `transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (TransitionPrefixedFirstBitAppendCodeWordReturnDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    exactIdentityDescription_subroutineReady
    (transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
      code hcode)
     /-- `transitionPrefixedFirstBitAppendCodeWordReturnDescription_run` captures the core lemma for this local construction. -/

theorem
    transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (payload : Word Bool) :
    exists steps : Nat,
      (TransitionPrefixedFirstBitAppendCodeWordReturnDescription
        code).runConfig steps
          { state :=
              (TransitionPrefixedFirstBitAppendCodeWordReturnDescription
                code).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (TransitionPrefixedFirstBitAppendCodeWordReturnDescription
              code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := MachineDescription.ExactIdentityDescription
  let B := TransitionPrefixedAppendCodeWordReturnDescription code
  let Tin :=
    tapeAtCells []
      (some false :: some false ::
        ((List.append [false, true] payload).map some))
  have hAready : A.SubroutineReady := by
    exact exactIdentityDescription_subroutineReady
  have hBready : B.SubroutineReady := by
    exact
      transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
        code hcode
  have hArun :
      A.runConfig 0
          { state := A.start, tape := Tin } =
        { state := A.halt, tape := Tin } := by
    rfl
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tin } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: payload)
                    (MachineDescription.encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        transitionPrefixedAppendCodeWordReturnDescription_run
          code hcode payload with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tin, tapeAtCells, Tape.move, Tape.moveRight] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [
    TransitionPrefixedFirstBitAppendCodeWordReturnDescription,
    A, B, Tin] using hn

def TransitionPrefixedFirstBitAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    (MachineDescription.encodeNat n)
     /-- `transitionPrefixedFirstBitAppendNatReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    transitionPrefixedFirstBitAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (TransitionPrefixedFirstBitAppendNatReturnDescription
      n).SubroutineReady :=
  transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (encodeNat_ne_nil n)
     /-- `transitionPrefixedFirstBitAppendNatReturnDescription_run` captures the core lemma for this local construction. -/

theorem
    transitionPrefixedFirstBitAppendNatReturnDescription_run
    (n : Nat) (payload : Word Bool) :
    exists steps : Nat,
      (TransitionPrefixedFirstBitAppendNatReturnDescription
        n).runConfig steps
          { state :=
              (TransitionPrefixedFirstBitAppendNatReturnDescription
                n).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (TransitionPrefixedFirstBitAppendNatReturnDescription
              n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNat n))).map some)) } := by
  simpa [
    TransitionPrefixedFirstBitAppendNatReturnDescription] using
    transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      payload

def AppendTwoCodeWordsReturnDescription
    (first second : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    (MarkedPrefixAppendCodeWordReturnDescription first)
    (TransitionPrefixedFirstBitAppendCodeWordReturnDescription
      second)
    Direction.left

 /-- `appendTwoCodeWordsReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem appendTwoCodeWordsReturnDescription_subroutineReady
    (first second : Word MachineCodeSymbol)
    (hfirst : first ≠ []) (hsecond : second ≠ []) :
    (AppendTwoCodeWordsReturnDescription
      first second).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (markedPrefixAppendCodeWordReturnDescription_subroutineReady
      first hfirst)
    (transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
      second hsecond)

 /-- `appendTwoCodeWordsReturnDescription_run` describes append/fold behavior used by later composition. -/
theorem appendTwoCodeWordsReturnDescription_run
    (first second : Word MachineCodeSymbol)
    (hfirst : first ≠ []) (hsecond : second ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (AppendTwoCodeWordsReturnDescription
        first second).runConfig steps
          ((AppendTwoCodeWordsReturnDescription
            first second).initial (b :: rest)) =
        { state :=
            (AppendTwoCodeWordsReturnDescription
              first second).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput first)
                    (MachineDescription.encodeCodeWordAsInput second))).map
                  some)) } := by
  let A := MarkedPrefixAppendCodeWordReturnDescription first
  let B :=
    TransitionPrefixedFirstBitAppendCodeWordReturnDescription
      second
  let firstBits := MachineDescription.encodeCodeWordAsInput first
  let secondBits := MachineDescription.encodeCodeWordAsInput second
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append (false :: true :: b :: rest) firstBits).map some))
  have hAready : A.SubroutineReady := by
    exact
      markedPrefixAppendCodeWordReturnDescription_subroutineReady
        first hfirst
  have hBready : B.SubroutineReady := by
    exact
      transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
        second hsecond
  rcases
      markedPrefixAppendCodeWordReturnDescription_run
        first hfirst b rest with
    ⟨nA, hArunBase⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape := Tape.input (b :: rest) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, firstBits, MachineDescription.initial] using hArunBase
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: b :: rest)
                    (List.append firstBits secondBits)).map some)) } := by
    rcases
        transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
          second hsecond (List.append (b :: rest) firstBits) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, firstBits, secondBits, tapeAtCells,
      Tape.move, Tape.moveLeft, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendTwoCodeWordsReturnDescription,
    MachineDescription.initial, A, B, firstBits, secondBits] using hn

 /-- `appendTwoCodeWordsReturnDescription_run_stageInput` states the corresponding theorem run form. -/
theorem appendTwoCodeWordsReturnDescription_run_stageInput
    (first second : Word MachineCodeSymbol)
    (hfirst : first ≠ []) (hsecond : second ≠ [])
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (AppendTwoCodeWordsReturnDescription
        first second).runConfig steps
          ((AppendTwoCodeWordsReturnDescription
            first second).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (AppendTwoCodeWordsReturnDescription
              first second).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (List.append
                      (MachineDescription.encodeCodeWordAsInput first)
                      (MachineDescription.encodeCodeWordAsInput second)))).map
                  some)) } := by
  rcases stageInputBits_exists_cons w stage with
    ⟨b, rest, hbits⟩
  rcases
      appendTwoCodeWordsReturnDescription_run
        first second hfirst hsecond b rest with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [hbits, MachineDescription.initial, List.append_assoc] using hsteps

def stageInputBits
    (w : Word Bool) (stage : Nat) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (PairedRecognizerDovetailStageInputCode w stage)

 /-- `stageInputBits_move_left_move_right_input` captures the core lemma for this local construction. -/
theorem stageInputBits_move_left_move_right_input
    (w : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.input (stageInputBits w stage))) =
      Tape.input (stageInputBits w stage) := by
  cases w with
  | nil =>
      cases stage <;>
        simp [stageInputBits,
          PairedRecognizerDovetailStageInputCode,
          MachineDescription.DovetailLayout.stageInputCode,
          MachineDescription.DovetailLayout.stageInputCodeAppend,
          MachineDescription.encodeBoolWordAppend,
          MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.input, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest =>
      cases b <;> cases stage <;>
        simp [stageInputBits,
          PairedRecognizerDovetailStageInputCode,
          MachineDescription.DovetailLayout.stageInputCode,
          MachineDescription.DovetailLayout.stageInputCodeAppend,
          MachineDescription.encodeBoolWordAppend,
          MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          Tape.input, Tape.move, Tape.moveLeft, Tape.moveRight]

 /-- `tape_eq_move_right_input_of_move_left_eq_input_cons_cons` provides an important equivalence or equality lemma. -/
theorem tape_eq_move_right_input_of_move_left_eq_input_cons_cons
    {a b : Bool} {rest : Word Bool} {T : Tape Bool}
    (h : Tape.move Direction.left T = Tape.input (a :: b :: rest)) :
    T = Tape.move Direction.right (Tape.input (a :: b :: rest)) := by
  cases T with
  | mk left head right =>
      cases left with
      | nil =>
          simp [Tape.move, Tape.moveLeft, Tape.input] at h
      | cons first leftRest =>
          cases leftRest with
          | nil =>
              simpa [Tape.move, Tape.moveLeft, Tape.moveRight,
                Tape.input] using h
          | cons second more =>
              simp [Tape.move, Tape.moveLeft, Tape.input] at h

 /-- `stageInputBits_exists_cons_cons` provides the witness needed for existential progress. -/
theorem stageInputBits_exists_cons_cons
    (w : Word Bool) (stage : Nat) :
    exists a : Bool,
    exists b : Bool,
    exists rest : Word Bool,
      stageInputBits w stage = a :: b :: rest := by
  cases w with
  | nil =>
      refine ⟨false, false, ?_⟩
      simp [stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]
      exact ⟨_, rfl⟩
  | cons c restw =>
      refine ⟨false, false, ?_⟩
      simp [stageInputBits,
        PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]
      exact ⟨_, rfl⟩

def inputTapeBits
    (w : Word Bool) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.encodeTapeAppend (Tape.input w) [])

def natBits (n : Nat) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.encodeNat n)

@[simp] theorem natBits_zero :
    natBits 0 = [false, false, true, true] := by
  rfl

@[simp] theorem natBits_succ (n : Nat) :
    natBits (n + 1) =
      false :: false :: true :: false :: natBits n := by
  rfl

@[simp] theorem natBits_append_cell_false
    (n : Nat) (tokens : Word MachineCodeSymbol) :
    MachineDescription.encodeCodeWordAsInput
        (List.append (MachineDescription.encodeNat n)
          (MachineCodeSymbol.zero :: tokens)) =
      List.append (natBits n)
        (false :: true :: false :: true ::
          MachineDescription.encodeCodeWordAsInput tokens) := by
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

@[simp] theorem natBits_append_cell_true
    (n : Nat) (tokens : Word MachineCodeSymbol) :
    MachineDescription.encodeCodeWordAsInput
        (List.append (MachineDescription.encodeNat n)
          (MachineCodeSymbol.one :: tokens)) =
      List.append (natBits n)
        (false :: true :: true :: false ::
          MachineDescription.encodeCodeWordAsInput tokens) := by
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

@[simp] theorem encodeCodeWordAsInput_tick_cons
    (tokens : Word MachineCodeSymbol) :
    MachineDescription.encodeCodeWordAsInput
        (MachineCodeSymbol.tick :: tokens) =
      false :: false :: true :: false ::
        MachineDescription.encodeCodeWordAsInput tokens := by
  rfl

@[simp] theorem natBits_map_append_cell_false
    (n : Nat) (tokens : Word MachineCodeSymbol) (suffixBits : Word Bool) :
    List.append
        (List.map some
          (MachineDescription.encodeCodeWordAsInput
            (List.append (MachineDescription.encodeNat n)
              (MachineCodeSymbol.zero :: tokens))))
        (List.map some suffixBits) =
      List.append (List.map some (natBits n))
        (some false :: some true :: some false :: some true ::
          List.append
            (List.map some
              (MachineDescription.encodeCodeWordAsInput tokens))
            (List.map some suffixBits)) := by
  rw [natBits_append_cell_false]
  simp [List.map_append, List.append_assoc]

@[simp] theorem natBits_map_append_cell_true
    (n : Nat) (tokens : Word MachineCodeSymbol) (suffixBits : Word Bool) :
    List.append
        (List.map some
          (MachineDescription.encodeCodeWordAsInput
            (List.append (MachineDescription.encodeNat n)
              (MachineCodeSymbol.one :: tokens))))
        (List.map some suffixBits) =
      List.append (List.map some (natBits n))
        (some false :: some true :: some true :: some false ::
          List.append
            (List.map some
              (MachineDescription.encodeCodeWordAsInput tokens))
            (List.map some suffixBits)) := by
  rw [natBits_append_cell_true]
  simp [List.map_append, List.append_assoc]

def emptyInputTapeCode :
    Word MachineCodeSymbol :=
  MachineDescription.encodeTapeAppend
    (Tape.input ([] : Word Bool)) []

 /-- `emptyInputTapeCode_ne_nil` captures the core lemma for this local construction. -/
theorem emptyInputTapeCode_ne_nil :
    emptyInputTapeCode ≠ [] := by
  simp [emptyInputTapeCode, encodeTapeAppend_input_nil,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat]

def AppendEmptyInputTapeReturnDescription :
    MachineDescription :=
  TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    emptyInputTapeCode
     /-- `appendEmptyInputTapeReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    appendEmptyInputTapeReturnDescription_subroutineReady :
    AppendEmptyInputTapeReturnDescription.SubroutineReady :=
  transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    emptyInputTapeCode
    emptyInputTapeCode_ne_nil

 /-- `inputTapeBits_nil` captures the core lemma for this local construction. -/
theorem inputTapeBits_nil :
    inputTapeBits ([] : Word Bool) =
      MachineDescription.encodeCodeWordAsInput
        emptyInputTapeCode := by
  rfl

 /-- `appendEmptyInputTapeReturnDescription_run` describes append/fold behavior used by later composition. -/
theorem appendEmptyInputTapeReturnDescription_run
    (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      AppendEmptyInputTapeReturnDescription.runConfig steps
          { state := AppendEmptyInputTapeReturnDescription.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([] : Word Bool) stage)
                      suffixBits)).map some)) } =
        { state := AppendEmptyInputTapeReturnDescription.halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits ([] : Word Bool) stage)
                    (List.append suffixBits
                      (inputTapeBits ([] : Word Bool))))).map
                    some)) } := by
  rcases
      transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
        emptyInputTapeCode
        emptyInputTapeCode_ne_nil
        (List.append
          (stageInputBits ([] : Word Bool) stage)
          suffixBits) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendEmptyInputTapeReturnDescription,
    inputTapeBits_nil, List.append_assoc] using hsteps

def inputTapeHeadPrefixCode
    (b : Bool) : Word MachineCodeSymbol :=
  MachineDescription.encodeCellListAppend []
    (MachineDescription.encodeCellAppend (some b) [])

def inputTapeRightCellsCode
    (rest : Word Bool) : Word MachineCodeSymbol :=
  MachineDescription.encodeCellListAppend (rest.map some) []

 /-- `inputTapeRightCellsCode_eq_nat_cells` provides an important equivalence or equality lemma. -/
theorem inputTapeRightCellsCode_eq_nat_cells
    (rest : Word Bool) :
    inputTapeRightCellsCode rest =
      MachineDescription.encodeNatAppend rest.length
        (MachineDescription.encodeCellsAppend (rest.map some) []) := by
  simp [inputTapeRightCellsCode,
    MachineDescription.encodeCellListAppend]

 /-- `inputTapeRightCellsCode_cons_eq_tick_nat_cell_cells` provides an important equivalence or equality lemma. -/
theorem inputTapeRightCellsCode_cons_eq_tick_nat_cell_cells
    (b : Bool) (rest : Word Bool) :
    inputTapeRightCellsCode (b :: rest) =
      MachineCodeSymbol.tick ::
        MachineDescription.encodeNatAppend rest.length
          (MachineDescription.encodeCellAppend (some b)
            (MachineDescription.encodeCellsAppend (rest.map some) [])) := by
  cases b <;>
    simp [inputTapeRightCellsCode,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat,
      MachineDescription.encodeCellsAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell]

 /-- `inputTapeRightCellsBits_eq_nat_cells` provides an important equivalence or equality lemma. -/
theorem inputTapeRightCellsBits_eq_nat_cells
    (rest : Word Bool) :
    MachineDescription.encodeCodeWordAsInput
        (inputTapeRightCellsCode rest) =
      List.append (natBits rest.length)
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellsAppend (rest.map some) [])) := by
  rw [inputTapeRightCellsCode_eq_nat_cells,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeCodeWordAsInput_append]
  rfl

 /-- `inputTapeRightCellsBits_cons_eq_tick_nat_cell_cells` provides an important equivalence or equality lemma. -/
theorem inputTapeRightCellsBits_cons_eq_tick_nat_cell_cells
    (b : Bool) (rest : Word Bool) :
    MachineDescription.encodeCodeWordAsInput
        (inputTapeRightCellsCode (b :: rest)) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.tick)
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeNatAppend rest.length
            (MachineDescription.encodeCellAppend (some b)
              (MachineDescription.encodeCellsAppend (rest.map some) [])))) := by
  rw [inputTapeRightCellsCode_cons_eq_tick_nat_cell_cells]
  rfl

 /-- `inputTapeHeadPrefixCode_ne_nil` captures the core lemma for this local construction. -/
theorem inputTapeHeadPrefixCode_ne_nil
    (b : Bool) :
    inputTapeHeadPrefixCode b ≠ [] := by
  cases b <;>
    simp [inputTapeHeadPrefixCode,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell]

 /-- `inputTapeBits_cons_eq_headPrefix_append` provides an important equivalence or equality lemma. -/
theorem inputTapeBits_cons_eq_headPrefix_append
    (b : Bool) (rest : Word Bool) :
    inputTapeBits (b :: rest) =
      List.append
        (MachineDescription.encodeCodeWordAsInput
          (inputTapeHeadPrefixCode b))
        (MachineDescription.encodeCodeWordAsInput
          (inputTapeRightCellsCode rest)) := by
  rw [inputTapeBits, encodeTapeAppend_input_cons]
  change
    MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeCellListAppend []
          (MachineDescription.encodeCellAppend (some b)
            (MachineDescription.encodeCellListAppend (rest.map some) []))) =
      List.append
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellListAppend []
            (MachineDescription.encodeCellAppend (some b) [])))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellListAppend (rest.map some) []))
  rw [← MachineDescription.encodeCodeWordAsInput_append]
  simp [MachineDescription.encodeCellListAppend,
    MachineDescription.encodeCellsAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat,
    MachineDescription.encodeCellAppend]

def AppendInputTapeHeadPrefixReturnDescription
    (b : Bool) : MachineDescription :=
  TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    (inputTapeHeadPrefixCode b)
     /-- `appendInputTapeHeadPrefixReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    appendInputTapeHeadPrefixReturnDescription_subroutineReady
    (b : Bool) :
    (AppendInputTapeHeadPrefixReturnDescription b).SubroutineReady :=
  transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    (inputTapeHeadPrefixCode b)
    (inputTapeHeadPrefixCode_ne_nil b)

 /-- `appendInputTapeHeadPrefixReturnDescription_run` describes append/fold behavior used by later composition. -/
theorem appendInputTapeHeadPrefixReturnDescription_run
    (b : Bool) (payload suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendInputTapeHeadPrefixReturnDescription b).runConfig steps
          { state := (AppendInputTapeHeadPrefixReturnDescription b).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append payload suffixBits)).map some)) } =
        { state := (AppendInputTapeHeadPrefixReturnDescription b).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append payload
                    (List.append suffixBits
                      (MachineDescription.encodeCodeWordAsInput
                        (inputTapeHeadPrefixCode b))))).map
                    some)) } := by
  rcases
      transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
        (inputTapeHeadPrefixCode b)
        (inputTapeHeadPrefixCode_ne_nil b)
        (List.append payload suffixBits) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendInputTapeHeadPrefixReturnDescription,
    List.append_assoc] using hsteps

def AppendInputTapeRightCellsReturnSpec
    (rightCopier : MachineDescription) : Prop :=
  rightCopier.SubroutineReady ∧
    forall b : Bool,
    forall rest : Word Bool,
    forall stage : Nat,
    forall suffixBits : Word Bool,
      exists steps : Nat,
        rightCopier.runConfig steps
            { state := rightCopier.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits (b :: rest) stage)
                        suffixBits)).map some)) } =
          { state := rightCopier.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      (List.append suffixBits
                        (MachineDescription.encodeCodeWordAsInput
                          (inputTapeRightCellsCode rest))))).map
                    some)) }

def AppendKnownHeadInputTapeReturnDescription
    (b : Bool) (rightCopier : MachineDescription) :
    MachineDescription :=
  MachineDescription.seqSubroutine
    (AppendInputTapeHeadPrefixReturnDescription b)
    rightCopier
    Direction.left
     /-- `appendKnownHeadInputTapeReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    appendKnownHeadInputTapeReturnDescription_subroutineReady
    {rightCopier : MachineDescription}
    (hright : AppendInputTapeRightCellsReturnSpec rightCopier)
    (b : Bool) :
    (AppendKnownHeadInputTapeReturnDescription
      b rightCopier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (appendInputTapeHeadPrefixReturnDescription_subroutineReady b)
    hright.left

 /-- `appendKnownHeadInputTapeReturnDescription_run` describes append/fold behavior used by later composition. -/
theorem appendKnownHeadInputTapeReturnDescription_run
    {rightCopier : MachineDescription}
    (hright : AppendInputTapeRightCellsReturnSpec rightCopier)
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendKnownHeadInputTapeReturnDescription
        b rightCopier).runConfig steps
          { state :=
              (AppendKnownHeadInputTapeReturnDescription
                b rightCopier).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendKnownHeadInputTapeReturnDescription
              b rightCopier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits (b :: rest) stage)
                    (List.append suffixBits
                      (inputTapeBits (b :: rest))))).map some)) } := by
  let A := AppendInputTapeHeadPrefixReturnDescription b
  let B := rightCopier
  let headBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeHeadPrefixCode b)
  let rightBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeRightCellsCode rest)
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true]
          (List.append
            (stageInputBits (b :: rest) stage)
            (List.append suffixBits headBits))).map some))
  have hAready : A.SubroutineReady :=
    appendInputTapeHeadPrefixReturnDescription_subroutineReady b
  have hBready : B.SubroutineReady := hright.left
  rcases
      appendInputTapeHeadPrefixReturnDescription_run
        b (stageInputBits (b :: rest) stage) suffixBits with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, headBits, List.append_assoc] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      (List.append suffixBits
                        (inputTapeBits (b :: rest))))).map some)) } := by
    rcases
        hright.right b rest stage (List.append suffixBits headBits) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, headBits, rightBits, tapeAtCells,
      Tape.move, Tape.moveLeft,
      inputTapeBits_cons_eq_headPrefix_append,
      List.map_append, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendKnownHeadInputTapeReturnDescription,
    A, B] using hn

def AppendEmptyRightCellsReturnDescription :
    MachineDescription :=
  TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    (inputTapeRightCellsCode ([] : Word Bool))

 /-- `inputTapeRightCellsCode_nil_ne_nil` captures the core lemma for this local construction. -/
theorem inputTapeRightCellsCode_nil_ne_nil :
    inputTapeRightCellsCode ([] : Word Bool) ≠ [] := by
  simp [inputTapeRightCellsCode,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat]
     /-- `appendEmptyRightCellsReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    appendEmptyRightCellsReturnDescription_subroutineReady :
    AppendEmptyRightCellsReturnDescription.SubroutineReady :=
  transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
    (inputTapeRightCellsCode ([] : Word Bool))
    inputTapeRightCellsCode_nil_ne_nil

 /-- `appendEmptyRightCellsReturnDescription_run` describes append/fold behavior used by later composition. -/
theorem appendEmptyRightCellsReturnDescription_run
    (b : Bool) (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      AppendEmptyRightCellsReturnDescription.runConfig steps
          { state := AppendEmptyRightCellsReturnDescription.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([b] : Word Bool) stage)
                      suffixBits)).map some)) } =
        { state := AppendEmptyRightCellsReturnDescription.halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits ([b] : Word Bool) stage)
                    (List.append suffixBits
                      (MachineDescription.encodeCodeWordAsInput
                        (inputTapeRightCellsCode
                          ([] : Word Bool)))))).map some)) } := by
  rcases
      transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
        (inputTapeRightCellsCode ([] : Word Bool))
        inputTapeRightCellsCode_nil_ne_nil
        (List.append
          (stageInputBits ([b] : Word Bool) stage)
          suffixBits) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendEmptyRightCellsReturnDescription,
    List.append_assoc] using hsteps

def AppendSingletonInputTapeReturnDescription
    (b : Bool) : MachineDescription :=
  MachineDescription.seqSubroutine
    (AppendInputTapeHeadPrefixReturnDescription b)
    AppendEmptyRightCellsReturnDescription
    Direction.left
     /-- `appendSingletonInputTapeReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    appendSingletonInputTapeReturnDescription_subroutineReady
    (b : Bool) :
    (AppendSingletonInputTapeReturnDescription
      b).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (appendInputTapeHeadPrefixReturnDescription_subroutineReady b)
    appendEmptyRightCellsReturnDescription_subroutineReady

 /-- `appendSingletonInputTapeReturnDescription_run` describes append/fold behavior used by later composition. -/
theorem appendSingletonInputTapeReturnDescription_run
    (b : Bool) (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendSingletonInputTapeReturnDescription b).runConfig steps
          { state :=
              (AppendSingletonInputTapeReturnDescription b).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([b] : Word Bool) stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendSingletonInputTapeReturnDescription b).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits ([b] : Word Bool) stage)
                    (List.append suffixBits
                      (inputTapeBits ([b] : Word Bool))))).map
                    some)) } := by
  let A := AppendInputTapeHeadPrefixReturnDescription b
  let B := AppendEmptyRightCellsReturnDescription
  let headBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeHeadPrefixCode b)
  let rightBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeRightCellsCode ([] : Word Bool))
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true]
          (List.append
            (stageInputBits ([b] : Word Bool) stage)
            (List.append suffixBits headBits))).map some))
  have hAready : A.SubroutineReady :=
    appendInputTapeHeadPrefixReturnDescription_subroutineReady b
  have hBready : B.SubroutineReady :=
    appendEmptyRightCellsReturnDescription_subroutineReady
  rcases
      appendInputTapeHeadPrefixReturnDescription_run
        b (stageInputBits ([b] : Word Bool) stage) suffixBits with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([b] : Word Bool) stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, headBits, List.append_assoc] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([b] : Word Bool) stage)
                      (List.append suffixBits
                        (inputTapeBits ([b] : Word Bool))))).map
                      some)) } := by
    rcases
        appendEmptyRightCellsReturnDescription_run
          b stage (List.append suffixBits headBits) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, headBits, rightBits, tapeAtCells,
      Tape.move, Tape.moveLeft,
      inputTapeBits_cons_eq_headPrefix_append,
      List.map_append, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendSingletonInputTapeReturnDescription,
    A, B] using hn

def AppendEmptyInputTapeSecondBitReturnDescription :
    MachineDescription :=
  TransitionPrefixedAppendCodeWordReturnDescription
    emptyInputTapeCode
     /-- `appendEmptyInputTapeSecondBitReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    appendEmptyInputTapeSecondBitReturnDescription_subroutineReady :
    AppendEmptyInputTapeSecondBitReturnDescription.SubroutineReady :=
  transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    emptyInputTapeCode
    emptyInputTapeCode_ne_nil

 /-- `appendEmptyInputTapeSecondBitReturnDescription_run` describes append/fold behavior used by later composition. -/
theorem appendEmptyInputTapeSecondBitReturnDescription_run
    (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      AppendEmptyInputTapeSecondBitReturnDescription.runConfig steps
          { state :=
              AppendEmptyInputTapeSecondBitReturnDescription.start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([] : Word Bool) stage)
                      suffixBits)).map some)) } =
        { state :=
            AppendEmptyInputTapeSecondBitReturnDescription.halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits ([] : Word Bool) stage)
                    (List.append suffixBits
                      (inputTapeBits ([] : Word Bool))))).map
                  some)) } := by
  rcases
      transitionPrefixedAppendCodeWordReturnDescription_run
        emptyInputTapeCode
        emptyInputTapeCode_ne_nil
        (List.append
          (stageInputBits ([] : Word Bool) stage)
          suffixBits) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendEmptyInputTapeSecondBitReturnDescription,
    inputTapeBits_nil, List.append_assoc] using hsteps

def AppendInputTapeSecondBitHeadPrefixReturnDescription
    (b : Bool) : MachineDescription :=
  TransitionPrefixedAppendCodeWordReturnDescription
    (inputTapeHeadPrefixCode b)
     /-- `appendInputTapeSecondBitHeadPrefixReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    appendInputTapeSecondBitHeadPrefixReturnDescription_subroutineReady
    (b : Bool) :
    (AppendInputTapeSecondBitHeadPrefixReturnDescription
      b).SubroutineReady :=
  transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    (inputTapeHeadPrefixCode b)
    (inputTapeHeadPrefixCode_ne_nil b)
     /-- `appendInputTapeSecondBitHeadPrefixReturnDescription_run` describes append/fold behavior used by later composition. -/

theorem
    appendInputTapeSecondBitHeadPrefixReturnDescription_run
    (b : Bool) (payload suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendInputTapeSecondBitHeadPrefixReturnDescription
        b).runConfig steps
          { state :=
              (AppendInputTapeSecondBitHeadPrefixReturnDescription
                b).start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append payload suffixBits)).map some)) } =
        { state :=
            (AppendInputTapeSecondBitHeadPrefixReturnDescription
              b).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append payload
                    (List.append suffixBits
                      (MachineDescription.encodeCodeWordAsInput
                        (inputTapeHeadPrefixCode b))))).map
                    some)) } := by
  rcases
      transitionPrefixedAppendCodeWordReturnDescription_run
        (inputTapeHeadPrefixCode b)
        (inputTapeHeadPrefixCode_ne_nil b)
        (List.append payload suffixBits) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendInputTapeSecondBitHeadPrefixReturnDescription,
    List.append_assoc] using hsteps

def AppendKnownHeadInputTapeSecondBitReturnDescription
    (b : Bool) (rightCopier : MachineDescription) :
    MachineDescription :=
  MachineDescription.seqSubroutine
    (AppendInputTapeSecondBitHeadPrefixReturnDescription b)
    rightCopier
    Direction.left
     /-- `appendKnownHeadInputTapeSecondBitReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    appendKnownHeadInputTapeSecondBitReturnDescription_subroutineReady
    {rightCopier : MachineDescription}
    (hright : AppendInputTapeRightCellsReturnSpec rightCopier)
    (b : Bool) :
    (AppendKnownHeadInputTapeSecondBitReturnDescription
      b rightCopier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (appendInputTapeSecondBitHeadPrefixReturnDescription_subroutineReady
      b)
    hright.left
     /-- `appendKnownHeadInputTapeSecondBitReturnDescription_run` describes append/fold behavior used by later composition. -/

theorem
    appendKnownHeadInputTapeSecondBitReturnDescription_run
    {rightCopier : MachineDescription}
    (hright : AppendInputTapeRightCellsReturnSpec rightCopier)
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendKnownHeadInputTapeSecondBitReturnDescription
        b rightCopier).runConfig steps
          { state :=
              (AppendKnownHeadInputTapeSecondBitReturnDescription
                b rightCopier).start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendKnownHeadInputTapeSecondBitReturnDescription
              b rightCopier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (stageInputBits (b :: rest) stage)
                    (List.append suffixBits
                      (inputTapeBits (b :: rest))))).map some)) } := by
  let A := AppendInputTapeSecondBitHeadPrefixReturnDescription b
  let B := rightCopier
  let headBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeHeadPrefixCode b)
  let rightBits :=
    MachineDescription.encodeCodeWordAsInput
      (inputTapeRightCellsCode rest)
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true]
          (List.append
            (stageInputBits (b :: rest) stage)
            (List.append suffixBits headBits))).map some))
  have hAready : A.SubroutineReady :=
    appendInputTapeSecondBitHeadPrefixReturnDescription_subroutineReady
      b
  have hBready : B.SubroutineReady := hright.left
  rcases
      appendInputTapeSecondBitHeadPrefixReturnDescription_run
        b (stageInputBits (b :: rest) stage) suffixBits with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, headBits, List.append_assoc] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      (List.append suffixBits
                        (inputTapeBits (b :: rest))))).map some)) } := by
    rcases
        hright.right b rest stage (List.append suffixBits headBits) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, headBits, rightBits, tapeAtCells,
      Tape.move, Tape.moveLeft,
      inputTapeBits_cons_eq_headPrefix_append,
      List.map_append, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendKnownHeadInputTapeSecondBitReturnDescription,
    A, B] using hn


end DovetailInitialLayoutInitializer
end Computability
end FoC
