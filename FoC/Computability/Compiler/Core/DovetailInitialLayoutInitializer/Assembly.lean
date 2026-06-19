import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputMarkedScanner
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.ReturnAppendDirect

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

def finalBoolFlagsCode :
    Word MachineCodeSymbol :=
  MachineDescription.encodeBoolAppend false
    (MachineDescription.encodeBoolAppend false [])

theorem finalBoolFlagsCode_ne_nil :
    finalBoolFlagsCode ≠ [] := by
  simp [finalBoolFlagsCode,
    MachineDescription.encodeBoolAppend,
    MachineDescription.encodeCellAppend,
    MachineDescription.encodeCell]

def AppendFinalBoolFlagsReturnDescription :
    MachineDescription :=
  TransitionPrefixedFirstBitAppendCodeWordReturnDescription
    finalBoolFlagsCode

theorem
    appendFinalBoolFlagsReturnDescription_subroutineReady :
    AppendFinalBoolFlagsReturnDescription.SubroutineReady := by
  exact
    transitionPrefixedFirstBitAppendCodeWordReturnDescription_subroutineReady
      finalBoolFlagsCode
      finalBoolFlagsCode_ne_nil

def AppendSecondInputTapeAndFlagsDescription
    (copier : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    copier
    AppendFinalBoolFlagsReturnDescription
    Direction.left

theorem
    appendSecondInputTapeAndFlagsDescription_subroutineReady
    {copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier) :
    (AppendSecondInputTapeAndFlagsDescription
      copier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hcopier.left
    appendFinalBoolFlagsReturnDescription_subroutineReady

def AppendRejectThenInputTapeAndFlagsDescription
    (reject copier : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    (TransitionPrefixedFirstBitAppendNatReturnDescription
      reject.start)
    (AppendSecondInputTapeAndFlagsDescription copier)
    Direction.left

theorem
    appendRejectThenInputTapeAndFlagsDescription_subroutineReady
    {reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier) :
    (AppendRejectThenInputTapeAndFlagsDescription
      reject copier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (transitionPrefixedFirstBitAppendNatReturnDescription_subroutineReady
      reject.start)
    (appendSecondInputTapeAndFlagsDescription_subroutineReady
      hcopier)

def AppendFirstInputTapeThenRejectDescription
    (reject copier : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    copier
    (AppendRejectThenInputTapeAndFlagsDescription reject copier)
    Direction.left

theorem
    appendFirstInputTapeThenRejectDescription_subroutineReady
    {reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier) :
    (AppendFirstInputTapeThenRejectDescription
      reject copier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    hcopier.left
    (appendRejectThenInputTapeAndFlagsDescription_subroutineReady
      hcopier)

def DescriptionWithCopier
    (accept reject copier : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    (MarkedPrefixAppendNatReturnDescription accept.start)
    (AppendFirstInputTapeThenRejectDescription reject copier)
    Direction.left

theorem
    descriptionWithCopier_subroutineReady
    {accept reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier) :
    (DescriptionWithCopier
      accept reject copier).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (markedPrefixAppendNatReturnDescription_subroutineReady
      accept.start)
    (appendFirstInputTapeThenRejectDescription_subroutineReady
      hcopier)

theorem
    appendSecondInputTapeAndFlagsDescription_run
    {copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendSecondInputTapeAndFlagsDescription
        copier).runConfig steps
          { state :=
              (AppendSecondInputTapeAndFlagsDescription
                copier).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendSecondInputTapeAndFlagsDescription
              copier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append (stageInputBits w stage)
                    (List.append suffixBits
                      (List.append (inputTapeBits w)
                        (MachineDescription.encodeCodeWordAsInput
                          finalBoolFlagsCode))))).map some)) } := by
  let A := copier
  let B := AppendFinalBoolFlagsReturnDescription
  let copiedSuffix :=
    List.append (stageInputBits w stage)
      (List.append suffixBits (inputTapeBits w))
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true] copiedSuffix).map some))
  have hAready : A.SubroutineReady := hcopier.left
  have hBready : B.SubroutineReady :=
    appendFinalBoolFlagsReturnDescription_subroutineReady
  rcases hcopier.right w stage suffixBits with ⟨nA, hArunBase⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, copiedSuffix, List.append_assoc] using hArunBase
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
                    (List.append (stageInputBits w stage)
                      (List.append suffixBits
                        (List.append (inputTapeBits w)
                          (MachineDescription.encodeCodeWordAsInput
                            finalBoolFlagsCode))))).map some)) } := by
    rcases
        transitionPrefixedFirstBitAppendCodeWordReturnDescription_run
          finalBoolFlagsCode
          finalBoolFlagsCode_ne_nil
          copiedSuffix with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, AppendFinalBoolFlagsReturnDescription,
      Tmid, copiedSuffix, tapeAtCells, Tape.move, Tape.moveLeft,
      List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendSecondInputTapeAndFlagsDescription,
    A, B] using hn

theorem
    appendRejectThenInputTapeAndFlagsDescription_run
    {reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendRejectThenInputTapeAndFlagsDescription
        reject copier).runConfig steps
          { state :=
              (AppendRejectThenInputTapeAndFlagsDescription
                reject copier).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendRejectThenInputTapeAndFlagsDescription
              reject copier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append (stageInputBits w stage)
                    (List.append suffixBits
                      (List.append (natBits reject.start)
                        (List.append (inputTapeBits w)
                          (MachineDescription.encodeCodeWordAsInput
                            finalBoolFlagsCode)))))).map some)) } := by
  let A :=
    TransitionPrefixedFirstBitAppendNatReturnDescription
      reject.start
  let B := AppendSecondInputTapeAndFlagsDescription copier
  let rejectSuffix :=
    List.append (stageInputBits w stage)
      (List.append suffixBits (natBits reject.start))
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true] rejectSuffix).map some))
  have hAready : A.SubroutineReady := by
    exact
      transitionPrefixedFirstBitAppendNatReturnDescription_subroutineReady
        reject.start
  have hBready : B.SubroutineReady := by
    exact
      appendSecondInputTapeAndFlagsDescription_subroutineReady
        hcopier
  rcases
      transitionPrefixedFirstBitAppendNatReturnDescription_run
        reject.start
        (List.append (stageInputBits w stage) suffixBits) with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, rejectSuffix, natBits,
      List.append_assoc] using hA
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
                    (List.append (stageInputBits w stage)
                      (List.append suffixBits
                        (List.append (natBits reject.start)
                          (List.append (inputTapeBits w)
                            (MachineDescription.encodeCodeWordAsInput
                              finalBoolFlagsCode)))))).map some)) } := by
    rcases
        appendSecondInputTapeAndFlagsDescription_run
          hcopier w stage
          (List.append suffixBits (natBits reject.start)) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, rejectSuffix, tapeAtCells,
      Tape.move, Tape.moveLeft, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendRejectThenInputTapeAndFlagsDescription,
    A, B] using hn

theorem
    appendFirstInputTapeThenRejectDescription_run
    {reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) (suffixBits : Word Bool) :
    exists steps : Nat,
      (AppendFirstInputTapeThenRejectDescription
        reject copier).runConfig steps
          { state :=
              (AppendFirstInputTapeThenRejectDescription
                reject copier).start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state :=
            (AppendFirstInputTapeThenRejectDescription
              reject copier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append (stageInputBits w stage)
                    (List.append suffixBits
                      (List.append (inputTapeBits w)
                        (List.append (natBits reject.start)
                          (List.append (inputTapeBits w)
                            (MachineDescription.encodeCodeWordAsInput
                              finalBoolFlagsCode))))))).map some)) } := by
  let A := copier
  let B := AppendRejectThenInputTapeAndFlagsDescription
    reject copier
  let firstTapeSuffix :=
    List.append (stageInputBits w stage)
      (List.append suffixBits (inputTapeBits w))
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true] firstTapeSuffix).map some))
  have hAready : A.SubroutineReady := hcopier.left
  have hBready : B.SubroutineReady := by
    exact
      appendRejectThenInputTapeAndFlagsDescription_subroutineReady
        hcopier
  rcases hcopier.right w stage suffixBits with ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append (stageInputBits w stage)
                      suffixBits)).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, firstTapeSuffix, List.append_assoc] using hA
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
                    (List.append (stageInputBits w stage)
                      (List.append suffixBits
                        (List.append (inputTapeBits w)
                          (List.append (natBits reject.start)
                            (List.append (inputTapeBits w)
                              (MachineDescription.encodeCodeWordAsInput
                                finalBoolFlagsCode))))))).map some)) } := by
    rcases
        appendRejectThenInputTapeAndFlagsDescription_run
          (reject := reject) hcopier w stage
          (List.append suffixBits (inputTapeBits w)) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, firstTapeSuffix, tapeAtCells,
      Tape.move, Tape.moveLeft, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendFirstInputTapeThenRejectDescription,
    A, B] using hn

theorem
    descriptionWithCopier_run_bits
    {accept reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (DescriptionWithCopier
        accept reject copier).runConfig steps
          ((DescriptionWithCopier
            accept reject copier).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (DescriptionWithCopier
              accept reject copier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append (stageInputBits w stage)
                    (List.append (natBits accept.start)
                      (List.append (inputTapeBits w)
                        (List.append (natBits reject.start)
                          (List.append (inputTapeBits w)
                            (MachineDescription.encodeCodeWordAsInput
                              finalBoolFlagsCode))))))).map some)) } := by
  let A := MarkedPrefixAppendNatReturnDescription accept.start
  let B := AppendFirstInputTapeThenRejectDescription
    reject copier
  let acceptSuffix :=
    List.append (stageInputBits w stage)
      (natBits accept.start)
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true] acceptSuffix).map some))
  have hAready : A.SubroutineReady := by
    exact
      markedPrefixAppendNatReturnDescription_subroutineReady
        accept.start
  have hBready : B.SubroutineReady := by
    exact
      appendFirstInputTapeThenRejectDescription_subroutineReady
        hcopier
  rcases
      markedPrefixAppendNatReturnDescription_run_stageInput
        accept.start w stage with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              Tape.input
                (MachineDescription.encodeCodeWordAsInput
                  (PairedRecognizerDovetailStageInputCode w stage)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, acceptSuffix, stageInputBits,
      natBits, MachineDescription.initial, List.append_assoc]
      using hA
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
                    (List.append (stageInputBits w stage)
                      (List.append (natBits accept.start)
                        (List.append (inputTapeBits w)
                          (List.append (natBits reject.start)
                            (List.append (inputTapeBits w)
                              (MachineDescription.encodeCodeWordAsInput
                                finalBoolFlagsCode))))))).map some)) } := by
    rcases
        appendFirstInputTapeThenRejectDescription_run
          (reject := reject) hcopier w stage
          (natBits accept.start) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, acceptSuffix, tapeAtCells,
      Tape.move, Tape.moveLeft, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [DescriptionWithCopier,
    MachineDescription.initial, A, B] using hn

theorem
    descriptionWithCopier_run_bits_checked
    {accept reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier)
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (DescriptionWithCopier
        accept reject copier).runConfig steps
          { state :=
              (DescriptionWithCopier
                accept reject copier).start
            tape := stageInputCheckedInputTape w stage } =
        { state :=
            (DescriptionWithCopier
              accept reject copier).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append (stageInputBits w stage)
                    (List.append (natBits accept.start)
                      (List.append (inputTapeBits w)
                        (List.append (natBits reject.start)
                          (List.append (inputTapeBits w)
                            (MachineDescription.encodeCodeWordAsInput
                              finalBoolFlagsCode))))))).map some)) } := by
  let A := MarkedPrefixAppendNatReturnDescription accept.start
  let B := AppendFirstInputTapeThenRejectDescription
    reject copier
  let acceptSuffix :=
    List.append (stageInputBits w stage)
      (natBits accept.start)
  let Tmid :=
    tapeAtCells [some false]
      (some false ::
        ((List.append [false, true] acceptSuffix).map some))
  have hAready : A.SubroutineReady := by
    exact
      markedPrefixAppendNatReturnDescription_subroutineReady
        accept.start
  have hBready : B.SubroutineReady := by
    exact
      appendFirstInputTapeThenRejectDescription_subroutineReady
        hcopier
  rcases
      markedPrefixAppendNatReturnDescription_run_stageInput_checked
        accept.start w stage with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape := stageInputCheckedInputTape w stage } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, acceptSuffix, stageInputCheckedInputTape,
      stageInputBits, natBits, List.append_assoc]
      using hA
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
                    (List.append (stageInputBits w stage)
                      (List.append (natBits accept.start)
                        (List.append (inputTapeBits w)
                          (List.append (natBits reject.start)
                            (List.append (inputTapeBits w)
                              (MachineDescription.encodeCodeWordAsInput
                                finalBoolFlagsCode))))))).map some)) } := by
    rcases
        appendFirstInputTapeThenRejectDescription_run
          (reject := reject) hcopier w stage
          (natBits accept.start) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, acceptSuffix, tapeAtCells,
      Tape.move, Tape.moveLeft, List.append_assoc] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [DescriptionWithCopier,
    A, B] using hn

theorem codeCells_encodeNat
    (n : Nat) :
    codeCells (MachineDescription.encodeNat n) =
      natCodeCells n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        List.append
            (codeSymbolCells MachineCodeSymbol.tick)
            (codeCells (MachineDescription.encodeNat n)) =
          List.append
            (codeSymbolCells MachineCodeSymbol.tick)
            (natCodeCells n)
      rw [ih]

theorem codeCells_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeNatAppend n suffix) =
      List.append (natCodeCells n)
        (codeCells suffix) := by
  rw [MachineDescription.encodeNatAppend, codeCells_append,
    codeCells_encodeNat]

theorem codeCells_encodeCell
    (cell : Option Bool) :
    codeCells (MachineDescription.encodeCell cell) =
      cellCodeCells cell := by
  cases cell with
  | none =>
      rfl
  | some b =>
      cases b <;> rfl

theorem codeCells_encodeCellAppend
    (cell : Option Bool) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeCellAppend cell suffix) =
      List.append (cellCodeCells cell)
        (codeCells suffix) := by
  rw [MachineDescription.encodeCellAppend, codeCells_append,
    codeCells_encodeCell]

theorem codeCells_encodeCellsAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeCellsAppend cells suffix) =
      List.append (cellsCodeCells cells)
        (codeCells suffix) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      rw [MachineDescription.encodeCellsAppend,
        codeCells_encodeCellAppend, ih]
      simp [cellsCodeCells, List.append_assoc]

theorem codeCells_encodeCellListAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeCellListAppend cells suffix) =
      List.append (natCodeCells cells.length)
        (List.append (cellsCodeCells cells)
          (codeCells suffix)) := by
  rw [MachineDescription.encodeCellListAppend,
    codeCells_encodeNatAppend,
    codeCells_encodeCellsAppend]

def inputTapeCodeCells :
    Word Bool -> List (Option Bool)
  | [] =>
      List.append (natCodeCells 0)
        (List.append (cellCodeCells none)
          (natCodeCells 0))
  | b :: rest =>
      List.append (natCodeCells 0)
        (List.append (cellCodeCells (some b))
          (List.append (natCodeCells rest.length)
            (cellsCodeCells (rest.map some))))

theorem codeCells_encodeTapeAppend_input
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeTapeAppend (Tape.input w) suffix) =
      List.append (inputTapeCodeCells w)
        (codeCells suffix) := by
  cases w with
  | nil =>
      rw [encodeTapeAppend_input_nil,
        codeCells_encodeCellListAppend,
        codeCells_encodeCellAppend,
        codeCells_encodeCellListAppend]
      simp [inputTapeCodeCells, cellsCodeCells,
        List.append_assoc]
  | cons b rest =>
      rw [encodeTapeAppend_input_cons,
        codeCells_encodeCellListAppend,
        codeCells_encodeCellAppend,
        codeCells_encodeCellListAppend]
      simp [inputTapeCodeCells, cellsCodeCells,
        List.append_assoc]

def boolCodeCells (b : Bool) :
    List (Option Bool) :=
  cellCodeCells (some b)

theorem codeCells_encodeBoolAppend
    (b : Bool) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeBoolAppend b suffix) =
      List.append (boolCodeCells b)
        (codeCells suffix) := by
  rw [MachineDescription.encodeBoolAppend,
    codeCells_encodeCellAppend]
  rfl

theorem codeCells_encodeBoolWordAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    codeCells
        (MachineDescription.encodeBoolWordAppend w suffix) =
      List.append (boolWordCells w)
        (codeCells suffix) := by
  rw [MachineDescription.encodeBoolWordAppend,
    codeCells_encodeCellListAppend]
  simp [boolWordCells, boolPayloadCells,
    List.append_assoc]

theorem stageInputCells_eq_bool_word_nat
    (w : Word Bool) (stage : Nat) :
    stageInputCells w stage =
      List.append (boolWordCells w)
        (natCodeCells stage) := by
  rw [stageInputCells, PairedRecognizerDovetailStageInputCode,
    MachineDescription.DovetailLayout.stageInputCode,
    MachineDescription.DovetailLayout.stageInputCodeAppend,
    codeCells_encodeBoolWordAppend,
    codeCells_encodeNatAppend]
  simp [codeCells, MachineDescription.encodeCodeWordAsInput]

theorem suffixCells_eq_field_blocks
    (accept reject : MachineDescription)
    (w : Word Bool) :
    suffixCells accept reject w =
      List.append (natCodeCells accept.start)
        (List.append (inputTapeCodeCells w)
          (List.append (natCodeCells reject.start)
            (List.append (inputTapeCodeCells w)
              (List.append (boolCodeCells false)
                (boolCodeCells false))))) := by
  rw [suffixCells, SuffixCode,
    codeCells_encodeNatAppend,
    codeCells_encodeTapeAppend_input,
    codeCells_encodeNatAppend,
    codeCells_encodeTapeAppend_input,
    codeCells_encodeBoolAppend,
    codeCells_encodeBoolAppend]
  simp [codeCells, MachineDescription.encodeCodeWordAsInput]

theorem outputCells_eq_stageInput_append_suffix
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    outputCells accept reject w stage =
      List.append [some false, some false, some false, some true]
        (List.append
          (stageInputCells w stage)
          (suffixCells accept reject w)) := by
  rw [outputCells, stageInputCells,
    suffixCells,
    outputCode_eq_stageInput_append_suffix]
  unfold codeCells
  simp [MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput]
  change
    List.map some
        (MachineDescription.encodeCodeWordAsInput
          (List.append
            (PairedRecognizerDovetailStageInputCode w stage)
            (SuffixCode accept reject w))) =
      List.append
        (List.map some
          (MachineDescription.encodeCodeWordAsInput
            (PairedRecognizerDovetailStageInputCode w stage)))
        (List.map some
          (MachineDescription.encodeCodeWordAsInput
            (SuffixCode accept reject w)))
  rw [MachineDescription.encodeCodeWordAsInput_append]
  exact map_some_append
    (MachineDescription.encodeCodeWordAsInput
      (PairedRecognizerDovetailStageInputCode w stage))
    (MachineDescription.encodeCodeWordAsInput
      (SuffixCode accept reject w))

theorem outputCells_eq_phase_blocks
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    outputCells accept reject w stage =
      List.append [some false, some false, some false, some true]
        (List.append (boolWordCells w)
          (List.append (natCodeCells stage)
            (suffixCells accept reject w))) := by
  rw [outputCells_eq_stageInput_append_suffix,
    stageInputCells_eq_bool_word_nat]
  simp [List.append_assoc]

theorem outputCells_eq_full_field_blocks
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    outputCells accept reject w stage =
      List.append [some false, some false, some false, some true]
        (List.append (boolWordCells w)
          (List.append (natCodeCells stage)
            (List.append (natCodeCells accept.start)
              (List.append (inputTapeCodeCells w)
                (List.append (natCodeCells reject.start)
                  (List.append (inputTapeCodeCells w)
                    (List.append (boolCodeCells false)
                      (boolCodeCells false)))))))) := by
  rw [outputCells_eq_phase_blocks,
    suffixCells_eq_field_blocks]

theorem tapeAtCells_eq_input_transition_prefixed
    (tail : Word Bool) :
    tapeAtCells []
        ((List.append
          (MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.transition) tail).map some) =
      Tape.input
        (List.append
          (MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.transition) tail) := by
  simp [tapeAtCells,
    MachineDescription.encodeCodeSymbolAsInput, Tape.input]

theorem tapeAtCells_right_eq_move_right_input_transition_prefixed
    (tail : Word Bool) :
    tapeAtCells
        [some false]
        (List.append [some false, some false, some true]
          (tail.map some)) =
      Tape.move Direction.right
        (Tape.input
          (List.append
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.transition) tail)) := by
  simp [tapeAtCells,
    MachineDescription.encodeCodeSymbolAsInput, Tape.input,
    Tape.move, Tape.moveRight]

theorem outputTape_eq_cells
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    OutputTape accept reject w stage =
      tapeAtCells
        [some false]
        (List.append [some false, some false, some true]
          (List.append
            ((MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage)).map some)
            ((MachineDescription.encodeCodeWordAsInput
              (SuffixCode
                accept reject w)).map some))) := by
  rw [outputTape_eq_stageInput_append_suffix]
  rw [← tapeAtCells_right_eq_move_right_input_transition_prefixed
    (tail :=
      List.append
        (MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w stage))
        (MachineDescription.encodeCodeWordAsInput
          (SuffixCode
            accept reject w)))]
  rw [map_some_append]

theorem natCodeCells_eq_bits
    (n : Nat) :
    natCodeCells n =
      (natBits n).map some := by
  rw [← codeCells_encodeNat n]
  rfl

theorem inputTapeCodeCells_eq_bits
    (w : Word Bool) :
    inputTapeCodeCells w =
      (inputTapeBits w).map some := by
  have h :=
    codeCells_encodeTapeAppend_input
      w ([] : Word MachineCodeSymbol)
  simpa [inputTapeBits, codeCells,
    MachineDescription.encodeCodeWordAsInput] using h.symm

theorem finalBoolFlagsCodeCells_eq_bits :
    List.append (boolCodeCells false)
        (boolCodeCells false) =
      (MachineDescription.encodeCodeWordAsInput
        finalBoolFlagsCode).map some := by
  simp [finalBoolFlagsCode, boolCodeCells,
    cellCodeCells, codeSymbolCells,
    MachineDescription.encodeBoolAppend, MachineDescription.encodeCellAppend,
    MachineDescription.encodeCell,
    MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput]

theorem outputTape_eq_bits
    (accept reject : MachineDescription)
    (w : Word Bool) (stage : Nat) :
    OutputTape accept reject w stage =
      tapeAtCells [some false]
        (some false ::
          ((List.append [false, true]
            (List.append (stageInputBits w stage)
              (List.append (natBits accept.start)
                (List.append (inputTapeBits w)
                    (List.append (natBits reject.start)
                      (List.append (inputTapeBits w)
                        (MachineDescription.encodeCodeWordAsInput
                          finalBoolFlagsCode))))))).map some)) := by
  rw [outputTape_eq_cells]
  change
    tapeAtCells [some false]
        (List.append [some false, some false, some true]
          (List.append (stageInputCells w stage)
            (suffixCells accept reject w))) =
      tapeAtCells [some false]
        (some false ::
          ((List.append [false, true]
            (List.append (stageInputBits w stage)
              (List.append (natBits accept.start)
                (List.append (inputTapeBits w)
                  (List.append (natBits reject.start)
                    (List.append (inputTapeBits w)
                      (MachineDescription.encodeCodeWordAsInput
                        finalBoolFlagsCode))))))).map some))
  rw [suffixCells_eq_field_blocks]
  simp only [natCodeCells_eq_bits,
    inputTapeCodeCells_eq_bits]
  rw [finalBoolFlagsCodeCells_eq_bits]
  simp [stageInputCells, stageInputBits,
    codeCells, List.map_append]

theorem inputTapeRightCellsDirectCopierNatBits_eq_ticks_done
    (n : Nat) :
    inputTapeRightCellsDirectCopierNatBits n =
      List.append (inputTapeRightCellsDirectCopierTickBits n)
        inputTapeRightCellsDirectCopierDoneBits := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change false :: false :: true :: false ::
          inputTapeRightCellsDirectCopierNatBits n =
        false :: false :: true :: false ::
          List.append (inputTapeRightCellsDirectCopierTickBits n)
            inputTapeRightCellsDirectCopierDoneBits
      rw [ih]

theorem inputTapeRightCellsDirectCopierCellBits_append_natBits
    (rest : Word Bool) (stage : Nat) :
    MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeCellsAppend (rest.map some)
          (MachineDescription.encodeNat stage)) =
      List.append (inputTapeRightCellsDirectCopierCellBits rest)
        (inputTapeRightCellsDirectCopierNatBits stage) := by
  rw [show
      MachineDescription.encodeCellsAppend (rest.map some)
          (MachineDescription.encodeNat stage) =
        List.append
          (MachineDescription.encodeCellsAppend (rest.map some) [])
          (MachineDescription.encodeNat stage) by
      simpa using
        (encodeCellsAppend_append (rest.map some) []
          (MachineDescription.encodeNat stage))]
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

theorem inputTapeRightCellsDirectCopierRightCellsCodeBits_eq
    (rest : Word Bool) :
    MachineDescription.encodeCodeWordAsInput
        (inputTapeRightCellsCode rest) =
      List.append (inputTapeRightCellsDirectCopierTickBits rest.length)
        (List.append inputTapeRightCellsDirectCopierDoneBits
          (inputTapeRightCellsDirectCopierCellBits rest)) := by
  rw [inputTapeRightCellsBits_eq_nat_cells]
  change
    List.append (inputTapeRightCellsDirectCopierNatBits rest.length)
        (inputTapeRightCellsDirectCopierCellBits rest) =
      List.append (inputTapeRightCellsDirectCopierTickBits rest.length)
        (List.append inputTapeRightCellsDirectCopierDoneBits
          (inputTapeRightCellsDirectCopierCellBits rest))
  rw [inputTapeRightCellsDirectCopierNatBits_eq_ticks_done]
  exact
    List.append_assoc
      (inputTapeRightCellsDirectCopierTickBits rest.length)
      inputTapeRightCellsDirectCopierDoneBits
      (inputTapeRightCellsDirectCopierCellBits rest)

theorem inputTapeRightCellsDirectCopierStageInputTailBits_eq
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    MachineDescription.encodeCodeWordAsInput
        (List.append (MachineDescription.encodeNat rest.length)
          ((if b then MachineCodeSymbol.one else MachineCodeSymbol.zero) ::
            MachineDescription.encodeCellsAppend (rest.map some)
              (MachineDescription.encodeNat stage))) =
      List.append (inputTapeRightCellsDirectCopierTickBits rest.length)
        (List.append inputTapeRightCellsDirectCopierDoneBits
          (List.append (inputTapeRightCellsDirectCopierHeadBits b)
            (List.append (inputTapeRightCellsDirectCopierCellBits rest)
              (inputTapeRightCellsDirectCopierNatBits stage)))) := by
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rw [show
      MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeNat rest.length) =
        inputTapeRightCellsDirectCopierNatBits rest.length by
      rfl]
  rw [inputTapeRightCellsDirectCopierNatBits_eq_ticks_done]
  cases b <;>
    simp [MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput,
      inputTapeRightCellsDirectCopierHeadBits,
      inputTapeRightCellsDirectCopierCellBits_append_natBits,
      List.append_assoc]

theorem stageInputBits_cons_eq_directCopierBits
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    stageInputBits (b :: rest) stage =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.tick)
        (List.append (inputTapeRightCellsDirectCopierTickBits rest.length)
          (List.append inputTapeRightCellsDirectCopierDoneBits
            (List.append (inputTapeRightCellsDirectCopierHeadBits b)
              (List.append (inputTapeRightCellsDirectCopierCellBits rest)
                (inputTapeRightCellsDirectCopierNatBits stage))))) := by
  cases b
  · simp [stageInputBits, PairedRecognizerDovetailStageInputCode,
      MachineDescription.DovetailLayout.stageInputCode,
      MachineDescription.DovetailLayout.stageInputCodeAppend,
      MachineDescription.encodeBoolWordAppend,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat,
      MachineDescription.encodeCellsAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell,
      MachineDescription.encodeCodeSymbolAsInput]
    exact congrArg
      (fun bits => false :: false :: true :: false :: bits)
      (inputTapeRightCellsDirectCopierStageInputTailBits_eq
        false rest stage)
  · simp [stageInputBits, PairedRecognizerDovetailStageInputCode,
      MachineDescription.DovetailLayout.stageInputCode,
      MachineDescription.DovetailLayout.stageInputCodeAppend,
      MachineDescription.encodeBoolWordAppend,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat,
      MachineDescription.encodeCellsAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell,
      MachineDescription.encodeCodeSymbolAsInput]
    exact congrArg
      (fun bits => false :: false :: true :: false :: bits)
      (inputTapeRightCellsDirectCopierStageInputTailBits_eq
        true rest stage)

theorem inputTapeRightCellsDirectCopierCoreSourceBits_eq
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) :
    List.append
        (MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.tick)
        (inputTapeRightCellsDirectCopierCoreSourceBits
          b rest stage suffixBits) =
      List.append (stageInputBits (b :: rest) stage) suffixBits := by
  rw [stageInputBits_cons_eq_directCopierBits]
  simp [inputTapeRightCellsDirectCopierCoreSourceBits,
    List.append_assoc]

theorem inputTapeRightCellsDirectCopierCoreOutputBits_eq
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) :
    inputTapeRightCellsDirectCopierCoreOutputBits b rest stage suffixBits =
      List.append [false, true]
        (List.append (stageInputBits (b :: rest) stage)
          (List.append suffixBits
            (MachineDescription.encodeCodeWordAsInput
              (inputTapeRightCellsCode rest)))) := by
  rw [stageInputBits_cons_eq_directCopierBits]
  rw [inputTapeRightCellsDirectCopierRightCellsCodeBits_eq]
  simp [inputTapeRightCellsDirectCopierCoreOutputBits,
    inputTapeRightCellsDirectCopierPreludeBits,
    MachineDescription.encodeCodeSymbolAsInput,
    List.append_assoc]

theorem
    descriptionWithCopier_forward
    {accept reject copier : MachineDescription}
    (hcopier : AppendInputTapeReturnSpec copier) :
    ForwardSpec
      accept reject
      (DescriptionWithCopier
        accept reject copier) := by
  intro w stage
  rcases
      descriptionWithCopier_run_bits
        (accept := accept) (reject := reject) hcopier w stage with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsWithTapeIn] using
      congrArg MachineDescription.Configuration.state hn
  · have htape :=
      congrArg MachineDescription.Configuration.tape hn
    exact htape.trans
      (outputTape_eq_bits
        accept reject w stage).symm

theorem appendInputTapeRightCellsReturnSpec_realizer :
    AppendInputTapeRightCellsReturnConstruction := by
  refine ⟨InputTapeRightCellsDirectReturnDescription, ?_⟩
  constructor
  · exact inputTapeRightCellsDirectReturnDescription_subroutineReady
  · intro b rest stage suffixBits
    rcases
        inputTapeRightCellsDirectReturnDescription_run_core
          b rest stage suffixBits with
      ⟨steps, hsteps⟩
    refine ⟨steps, ?_⟩
    have hsource :=
      inputTapeRightCellsDirectCopierCoreSourceBits_eq
        b rest stage suffixBits
    have houtput :=
      inputTapeRightCellsDirectCopierCoreOutputBits_eq
        b rest stage suffixBits
    rw [hsource] at hsteps
    simpa [houtput, List.map_append,
      List.append_assoc] using hsteps

theorem appendInputTapeHeadTaggedBrancher_realizer :
    AppendInputTapeHeadTaggedBrancherConstruction := by
  intro rightCopier hrightCopier
  let blankBranch := AppendEmptyInputTapeSecondBitReturnDescription
  let falseBranch :=
    AppendKnownHeadInputTapeSecondBitReturnDescription
      false rightCopier
  let trueBranch :=
    AppendKnownHeadInputTapeSecondBitReturnDescription
      true rightCopier
  let brancher :=
    RestoreFirstBitTaggedBrancherDescription
      blankBranch falseBranch trueBranch
  have hblankReady : blankBranch.SubroutineReady := by
    exact appendEmptyInputTapeSecondBitReturnDescription_subroutineReady
  have hfalseReady : falseBranch.SubroutineReady := by
    exact
      appendKnownHeadInputTapeSecondBitReturnDescription_subroutineReady
        hrightCopier false
  have htrueReady : trueBranch.SubroutineReady := by
    exact
      appendKnownHeadInputTapeSecondBitReturnDescription_subroutineReady
        hrightCopier true
  refine ⟨brancher, ?_⟩
  constructor
  · exact
      restoreFirstBitTaggedBrancherDescription_subroutineReady
        hblankReady hfalseReady htrueReady
  constructor
  · intro stage suffixBits
    let T :=
      Tape.move Direction.left
        (appendInputTapeHeadRouterTaggedTape
          none ([] : Word Bool) stage suffixBits)
    let Tout :=
      tapeAtCells [some false]
        (some false ::
          ((List.append [false, true]
            (List.append
              (stageInputBits ([] : Word Bool) stage)
              (List.append suffixBits
                (inputTapeBits ([] : Word Bool))))).map some))
    have hread : Tape.read T = none := by
      simp [T, appendInputTapeHeadRouterTaggedTape,
        tapeAtCells, Tape.move, Tape.moveLeft, Tape.read]
    have hbranch :
        exists steps : Nat,
          blankBranch.runConfig steps
              { state := blankBranch.start
                tape :=
                  Tape.move Direction.right (Tape.write (some false) T) } =
            { state := blankBranch.halt, tape := Tout } := by
      rcases
          appendEmptyInputTapeSecondBitReturnDescription_run
            stage suffixBits with
        ⟨steps, hsteps⟩
      refine ⟨steps, ?_⟩
      simpa [blankBranch, T, Tout,
        appendInputTapeHeadRouterTaggedTape,
        tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
        Tape.write, List.append_assoc] using hsteps
    rcases
        restoreFirstBitTaggedBrancherDescription_run_none
          hblankReady hfalseReady htrueReady hread hbranch with
      ⟨steps, hsteps⟩
    refine ⟨steps, ?_⟩
    simpa [brancher, T, Tout] using hsteps
  · intro b rest stage suffixBits
    cases b
    · let T :=
        Tape.move Direction.left
          (appendInputTapeHeadRouterTaggedTape
            (some false) (false :: rest) stage suffixBits)
      let Tout :=
        tapeAtCells [some false]
          (some false ::
            ((List.append [false, true]
              (List.append
                (stageInputBits (false :: rest) stage)
                (List.append suffixBits
                  (inputTapeBits
                    (false :: rest))))).map some))
      have hread : Tape.read T = some false := by
        simp [T, appendInputTapeHeadRouterTaggedTape,
          tapeAtCells, Tape.move, Tape.moveLeft, Tape.read]
      have hbranch :
          exists steps : Nat,
            falseBranch.runConfig steps
                { state := falseBranch.start
                  tape :=
                    Tape.move Direction.right (Tape.write (some false) T) } =
              { state := falseBranch.halt, tape := Tout } := by
        rcases
            appendKnownHeadInputTapeSecondBitReturnDescription_run
              hrightCopier false rest stage suffixBits with
          ⟨steps, hsteps⟩
        refine ⟨steps, ?_⟩
        simpa [falseBranch, T, Tout,
          appendInputTapeHeadRouterTaggedTape,
          tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
          Tape.write, List.append_assoc] using hsteps
      rcases
          restoreFirstBitTaggedBrancherDescription_run_false
            hblankReady hfalseReady htrueReady hread hbranch with
        ⟨steps, hsteps⟩
      refine ⟨steps, ?_⟩
      simpa [brancher, T, Tout] using hsteps
    · let T :=
        Tape.move Direction.left
          (appendInputTapeHeadRouterTaggedTape
            (some true) (true :: rest) stage suffixBits)
      let Tout :=
        tapeAtCells [some false]
          (some false ::
            ((List.append [false, true]
              (List.append
                (stageInputBits (true :: rest) stage)
                (List.append suffixBits
                  (inputTapeBits
                    (true :: rest))))).map some))
      have hread : Tape.read T = some true := by
        simp [T, appendInputTapeHeadRouterTaggedTape,
          tapeAtCells, Tape.move, Tape.moveLeft, Tape.read]
      have hbranch :
          exists steps : Nat,
            trueBranch.runConfig steps
                { state := trueBranch.start
                  tape :=
                    Tape.move Direction.right (Tape.write (some false) T) } =
              { state := trueBranch.halt, tape := Tout } := by
        rcases
            appendKnownHeadInputTapeSecondBitReturnDescription_run
              hrightCopier true rest stage suffixBits with
          ⟨steps, hsteps⟩
        refine ⟨steps, ?_⟩
        simpa [trueBranch, T, Tout,
          appendInputTapeHeadRouterTaggedTape,
          tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight,
          Tape.write, List.append_assoc] using hsteps
      rcases
          restoreFirstBitTaggedBrancherDescription_run_true
            hblankReady hfalseReady htrueReady hread hbranch with
        ⟨steps, hsteps⟩
      refine ⟨steps, ?_⟩
      simpa [brancher, T, Tout] using hsteps

theorem appendInputTapeHeadDispatcher_realizer :
    AppendInputTapeHeadDispatcherConstruction := by
  intro rightCopier hrightCopier
  rcases
      appendInputTapeHeadTaggedBrancher_realizer
        rightCopier hrightCopier with
    ⟨brancher, hbrancher⟩
  exact
    ⟨AppendInputTapeHeadDispatcherDescription
        AppendInputTapeHeadRouterDescription brancher,
      appendInputTapeHeadDispatcherSpec_of_router_brancher
        appendInputTapeHeadRouterDescription_spec hbrancher⟩

theorem appendInputTapeReturnSpec_realizer :
    exists copier : MachineDescription,
      AppendInputTapeReturnSpec copier := by
  rcases appendInputTapeRightCellsReturnSpec_realizer with
    ⟨rightCopier, hrightCopier⟩
  rcases
      appendInputTapeHeadDispatcher_realizer
        rightCopier hrightCopier with
    ⟨copier, hcopier⟩
  exact
    ⟨copier,
      appendInputTapeReturnSpec_of_headDispatcher hcopier⟩

theorem stageInputMarkedScanner_realizer :
    StageInputMarkedScannerConstruction := by
  exact
    ⟨StageInputMarkedScannerDescription,
      stageInputMarkedScannerDescription_spec⟩

theorem stageInputMarkedCore_realizer :
    StageInputMarkedCoreConstruction := by
  rcases stageInputMarkedScanner_realizer with
    ⟨scanner, hscanner⟩
  exact
    ⟨StageInputMarkedCoreDescription scanner,
      stageInputMarkedCoreSpec_of_markedScanner hscanner⟩

theorem stageInputRecognizer_realizer :
    StageInputRecognizerConstruction := by
  rcases stageInputMarkedCore_realizer with
    ⟨markedCore, hmarkedCore⟩
  exact
    ⟨StageInputRecognizerDescription markedCore,
      stageInputRecognizerSpec_of_markedCore hmarkedCore⟩

theorem stageInputIdentityClosedHandoff_realizer :
    StageInputIdentityClosedHandoffConstruction := by
  rcases stageInputRecognizer_realizer with
    ⟨recognizer, hrecognizer⟩
  exact
    stageInputIdentityClosedHandoffConstruction_of_recognizer
      hrecognizer

theorem stageInputValidatorSpec_realizer :
    exists validator : MachineDescription,
      StageInputValidatorSpec validator := by
  rcases stageInputIdentityClosedHandoff_realizer with
    ⟨validator, hvalidator⟩
  exact
    ⟨validator,
      stageInputValidatorSpec_of_identityClosedHandoff
        hvalidator⟩


end DovetailInitialLayoutInitializer
end Computability
end FoC
