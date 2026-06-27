import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.AppendLast

set_option doc.verso true

/-!
# ReturnAppend

Append-input return helpers for marked transition and stage-input prefixes.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace DovetailInitialLayoutInitializer

def MarkTransitionSecondBitDescription :
    MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition
        0 (some false) none Direction.left 1
    , transition
        1 (some false) (some false) Direction.right 2
    ]

private abbrev MTSB := MarkTransitionSecondBitDescription

theorem markTransitionSecondBitDescription_wellFormed :
    MTSB.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := MTSB.transitions)
      (stateCount :=
        MTSB.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := MTSB.transitions)
      (by decide)

theorem markTransitionSecondBitDescription_haltTransitionFree :
    MTSB.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := MTSB.transitions)
    (state := MTSB.halt)
    (by decide)

theorem markTransitionSecondBitDescription_subroutineReady :
    MTSB.SubroutineReady :=
  ⟨markTransitionSecondBitDescription_wellFormed,
    markTransitionSecondBitDescription_haltTransitionFree⟩

theorem markTransitionSecondBitDescription_run
    (payload : Word Bool) :
    MTSB.runConfig 2
        (config 0 [some false]
          (some false ::
            ((List.append [false, true] payload).map some))) =
      { state := MTSB.halt
        tape :=
          tapeAtCells [some false]
            (none ::
              ((List.append [false, true] payload).map some)) } := by
  cases payload <;>
    simp [MarkTransitionSecondBitDescription,
      config, tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

def TransitionPrefixedThenAppendCodeWordLastDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  seqSubroutine
    MTSB
    (AppendCodeWordLastDescription code)
    Direction.right

theorem
    transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (TransitionPrefixedThenAppendCodeWordLastDescription
      code).SubroutineReady :=
  seqSubroutine_subroutineReady
    markTransitionSecondBitDescription_subroutineReady
    (appendCodeWordLastDescription_subroutineReady code hcode)

theorem
    transitionPrefixedThenAppendCodeWordLastDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (payload : Word Bool) :
    exists steps : Nat,
      (TransitionPrefixedThenAppendCodeWordLastDescription
        code).runConfig steps
          { state :=
              (TransitionPrefixedThenAppendCodeWordLastDescription
                code).start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (TransitionPrefixedThenAppendCodeWordLastDescription
              code).halt
          tape :=
            appendCodeWordLastTapeAtCells
              (List.append
                ((false :: true :: payload).reverse.map some)
                [none, some false])
              code } := by
  let A := MTSB
  let B := AppendCodeWordLastDescription code
  let Tmid :=
    tapeAtCells [some false]
      (none ::
        ((List.append [false, true] payload).map some))
  have hAready : A.SubroutineReady := by
    exact markTransitionSecondBitDescription_subroutineReady
  have hBready : B.SubroutineReady := by
    exact appendCodeWordLastDescription_subroutineReady code hcode
  have hArun :
      A.runConfig 2
          { state := A.start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, config] using
      markTransitionSecondBitDescription_run payload
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tmid } =
          { state := B.halt
            tape :=
              appendCodeWordLastTapeAtCells
                (List.append
                  ((false :: true :: payload).reverse.map some)
                  [none, some false])
                code } := by
    rcases
        appendCodeWordLastDescription_run_from_scan_atCells
          code hcode [none, some false] (false :: true :: payload) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid, tapeAtCells,
      appendScanTapeAtCells, Tape.move, Tape.moveRight] using hB
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [TransitionPrefixedThenAppendCodeWordLastDescription,
    A, B] using hn

def ReturnToCurrentMarkerDescription :
    MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition
        0 (some false) (some false) Direction.left 0
    , transition
        0 (some true) (some true) Direction.left 0
    , transition
        0 none (some false) Direction.right 1
    ]

private abbrev RTCM := ReturnToCurrentMarkerDescription

theorem returnToCurrentMarkerDescription_wellFormed :
    RTCM.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := RTCM.transitions)
      (stateCount :=
        RTCM.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := RTCM.transitions)
      (by decide)

theorem returnToCurrentMarkerDescription_haltTransitionFree :
    RTCM.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := RTCM.transitions)
    (state := RTCM.halt)
    (by decide)

theorem returnToCurrentMarkerDescription_subroutineReady :
    RTCM.SubroutineReady :=
  ⟨returnToCurrentMarkerDescription_wellFormed,
    returnToCurrentMarkerDescription_haltTransitionFree⟩

theorem returnToCurrentMarkerDescription_step_scan
    (preRev : Word Bool) (leftBit current : Bool)
    (leftOfMarker right : List (Option Bool)) :
    RTCM.stepConfig
        (config 0
          (List.append
            (some leftBit :: preRev.map some)
            (none :: leftOfMarker))
          (some current :: right)) =
      some
        (config 0
          (List.append
            (preRev.map some)
            (none :: leftOfMarker))
          (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;>
    simp [ReturnToCurrentMarkerDescription,
      config, tapeAtCells,
      stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]
theorem returnToCurrentMarkerDescription_run
    (preRev : Word Bool) (current : Bool)
    (leftOfMarker right : List (Option Bool)) :
    RTCM.runConfig
        (preRev.length + 2)
        (config 0
          (List.append (preRev.map some) (none :: leftOfMarker))
          (some current :: right)) =
      config 1
        (some false :: leftOfMarker)
        (List.append (preRev.reverse.map some)
          (some current :: right)) := by
  induction preRev generalizing current right with
  | nil =>
      cases current <;>
        simp [ReturnToCurrentMarkerDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      simp only [List.map_cons, List.length_cons, List.reverse_cons]
      rw [show Nat.succ rest.length + 2 = (rest.length + 2) + 1 by omega]
      rw [runConfig]
      rw [returnToCurrentMarkerDescription_step_scan]
      simpa [List.append_assoc] using ih b (some current :: right)

theorem
    returnToCurrentMarkerDescription_run_after_append_four_atCells
    (pre : Word Bool) (leftOfMarker : List (Option Bool))
    (b0 b1 b2 b3 : Bool) :
    RTCM.runConfig
        (pre.length + 4)
        { state := RTCM.start
          tape :=
            Tape.move Direction.left
              (appendRightLastTapeAtCells
                (List.append (pre.reverse.map some)
                  (none :: leftOfMarker)) b0 b1 b2 b3) } =
      config
        RTCM.halt
        (some false :: leftOfMarker)
        ((List.append pre [b0, b1, b2, b3]).map some) := by
  simpa [appendRightLastTapeAtCells, config,
    Tape.move, Tape.moveLeft, List.append_assoc] using
    returnToCurrentMarkerDescription_run
      (List.append [b1, b0] pre.reverse) b2
      leftOfMarker [some b3]

theorem
    returnToCurrentMarkerDescription_run_after_append_atCells :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall pre : Word Bool,
        forall leftOfMarker : List (Option Bool),
          exists steps : Nat,
            RTCM.runConfig steps
                { state := RTCM.start
                  tape :=
                    Tape.move Direction.left
                      (appendCodeWordLastTapeAtCells
                        (List.append (pre.reverse.map some)
                          (none :: leftOfMarker))
                        code) } =
              config
                RTCM.halt
                (some false :: leftOfMarker)
                ((List.append pre
                  (encodeCodeWordAsInput code)).map some)
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro pre leftOfMarker
      cases symbol <;>
        refine ⟨pre.length + 4, ?_⟩ <;>
        simpa [appendCodeWordLastTapeAtCells,
          appendCodeSymbolLastTapeAtCells,
          appendRightLastTapeAtCells,
          encodeCodeSymbolAsInput,
          encodeCodeWordAsInput,
          Tape.move, Tape.moveLeft, List.append_assoc] using
          returnToCurrentMarkerDescription_run_after_append_four_atCells
            pre leftOfMarker _ _ _ _
  | symbol :: next :: rest, _ => by
      intro pre leftOfMarker
      let symbolBits := encodeCodeSymbolAsInput symbol
      rcases
          returnToCurrentMarkerDescription_run_after_append_atCells
            (next :: rest) (by intro h; cases h)
            (List.append pre symbolBits) leftOfMarker with
        ⟨steps, hsteps⟩
      refine ⟨steps, ?_⟩
      have hleft :
          List.append (symbolBits.reverse.map some)
              (List.append (pre.reverse.map some)
                (none :: leftOfMarker)) =
            List.append
              ((List.append pre symbolBits).reverse.map some)
              (none :: leftOfMarker) := by
        simp [List.reverse_append, List.map_append, List.append_assoc]
      have hbits :
          List.append (List.append pre symbolBits)
              (encodeCodeWordAsInput (next :: rest)) =
            List.append pre
              (encodeCodeWordAsInput
                (symbol :: next :: rest)) := by
        simp [symbolBits,
          encodeCodeWordAsInput, List.append_assoc]
      simpa [appendCodeWordLastTapeAtCells, symbolBits,
        hleft, hbits, encodeCodeWordAsInput,
        List.map_append, List.append_assoc] using hsteps

def AppendCodeWordReturnToCurrentMarkerDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  seqSubroutine
    (AppendCodeWordLastDescription code)
    RTCM
    Direction.left

theorem
    appendCodeWordReturnToCurrentMarkerDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (AppendCodeWordReturnToCurrentMarkerDescription
      code).SubroutineReady :=
  seqSubroutine_subroutineReady
    (appendCodeWordLastDescription_subroutineReady code hcode)
    returnToCurrentMarkerDescription_subroutineReady

theorem
    appendCodeWordReturnToCurrentMarkerDescription_run_from_scan
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (pre remaining : Word Bool)
    (leftOfMarker : List (Option Bool)) :
    exists steps : Nat,
      (AppendCodeWordReturnToCurrentMarkerDescription
        code).runConfig steps
          { state :=
              (AppendCodeWordReturnToCurrentMarkerDescription
                code).start
            tape :=
              appendScanTapeAtCells
                (List.append (pre.reverse.map some)
                  (none :: leftOfMarker))
                remaining } =
        config
          (AppendCodeWordReturnToCurrentMarkerDescription
            code).halt
          (some false :: leftOfMarker)
          ((List.append (List.append pre remaining)
            (encodeCodeWordAsInput code)).map some) := by
  let A := AppendCodeWordLastDescription code
  let B := RTCM
  let preAll := List.append pre remaining
  let Tmid :=
    appendCodeWordLastTapeAtCells
      (List.append (remaining.reverse.map some)
        (List.append (pre.reverse.map some)
          (none :: leftOfMarker)))
      code
  have hAready : A.SubroutineReady := by
    exact appendCodeWordLastDescription_subroutineReady code hcode
  have hBready : B.SubroutineReady := by
    exact returnToCurrentMarkerDescription_subroutineReady
  rcases
      appendCodeWordLastDescription_run_from_scan_atCells
        code hcode
        (List.append (pre.reverse.map some) (none :: leftOfMarker))
        remaining with
    ⟨nA, hA⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              appendScanTapeAtCells
                (List.append (pre.reverse.map some)
                  (none :: leftOfMarker))
                remaining } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid] using hA
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          config B.halt
            (some false :: leftOfMarker)
            ((List.append preAll
              (encodeCodeWordAsInput code)).map some) := by
    have hleft :
        List.append ((List.map some remaining).reverse)
            (List.append ((List.map some pre).reverse)
              (none :: leftOfMarker)) =
          List.append ((List.map some preAll).reverse)
            (none :: leftOfMarker) := by
      simp [preAll, List.reverse_append, List.map_append,
        List.append_assoc]
    rcases
        returnToCurrentMarkerDescription_run_after_append_atCells
          code hcode preAll leftOfMarker with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    have hstart :
        ({ state := B.start
           tape := Tape.move Direction.left Tmid } :
            Configuration) =
          { state := B.start
            tape :=
              Tape.move Direction.left
                (appendCodeWordLastTapeAtCells
                  (List.append ((List.map some preAll).reverse)
                    (none :: leftOfMarker))
                  code) } := by
      simp [B, Tmid]
      exact
        congrArg
          (fun left =>
            Tape.move Direction.left
              (appendCodeWordLastTapeAtCells left code))
          hleft
    rw [hstart]
    simpa [B] using hB
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [AppendCodeWordReturnToCurrentMarkerDescription,
    A, B, preAll] using hn

def RightCellsCopierStartDescription :
    MachineDescription where
  stateCount := 9
  start := 0
  halt := 8
  transitions :=
    [ transition
        0 (some false) (some false) Direction.right 1
    , transition
        1 (some false) none Direction.right 2
    , transition
        2 (some false) (some false) Direction.right 3
    , transition
        3 (some true) (some true) Direction.right 4
    , transition
        4 (some false) (some false) Direction.right 5
    , transition
        5 (some false) (some false) Direction.right 6
    , transition
        6 (some true) (some true) Direction.right 7
    , transition
        7 (some false) (some false) Direction.right 8
    ]

theorem rightCellsCopierStartDescription_wellFormed :
    RightCellsCopierStartDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := RightCellsCopierStartDescription.transitions)
      (stateCount :=
        RightCellsCopierStartDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := RightCellsCopierStartDescription.transitions)
      (by decide)

theorem rightCellsCopierStartDescription_haltTransitionFree :
    RightCellsCopierStartDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := RightCellsCopierStartDescription.transitions)
    (state := RightCellsCopierStartDescription.halt)
    (by decide)

theorem rightCellsCopierStartDescription_subroutineReady :
    RightCellsCopierStartDescription.SubroutineReady :=
  ⟨rightCellsCopierStartDescription_wellFormed,
    rightCellsCopierStartDescription_haltTransitionFree⟩

theorem rightCellsCopierStartDescription_run
    (tail : List (Option Bool)) :
    RightCellsCopierStartDescription.runConfig 8
        (config 0 []
          (List.append
            [some false, some false, some false, some true,
              some false, some false, some true, some false]
            tail)) =
      config 8
        [some false, some true, some false, some false,
          some true, some false, none, some false]
        tail := by
  cases tail <;>
    simp [RightCellsCopierStartDescription,
      config, tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

def InputTapeRightCellsDirectCopierDescription :
    MachineDescription where
  stateCount := 100
  start := 0
  halt := 99
  transitions :=
    [ -- Copy the residual unary length prefix.
      transition
        0 (some false) none Direction.right 1
    , transition
        1 (some false) (some false) Direction.right 2
    , transition
        2 (some true) (some true) Direction.right 3
    , transition
        3 (some false) (some false) Direction.right 20
    , transition
        3 (some true) (some true) Direction.right 30

      -- In cell mode, stop when the next source symbol is a nat symbol.
    , transition
        10 (some false) (some false) Direction.right 11
    , transition
        11 (some false) (some false) Direction.left 80
    , transition
        11 (some true) (some true) Direction.left 12
    , transition
        12 (some false) none Direction.right 13
    , transition
        13 (some true) (some true) Direction.right 14
    , transition
        14 (some false) (some false) Direction.right 15
    , transition
        14 (some true) (some true) Direction.right 18
    , transition
        15 (some false) (some false) Direction.right 50
    , transition
        15 (some true) (some true) Direction.right 60
    , transition
        18 (some false) (some false) Direction.right 70

      -- Append a tick symbol, return to its temporary marker, and advance.
    , transition
        20 (some false) (some false) Direction.right 20
    , transition
        20 (some true) (some true) Direction.right 20
    , transition
        20 none (some false) Direction.right 21
    , transition
        21 none (some false) Direction.right 22
    , transition
        22 none (some true) Direction.right 23
    , transition
        23 none (some false) Direction.left 24
    , transition
        24 (some false) (some false) Direction.left 24
    , transition
        24 (some true) (some true) Direction.left 24
    , transition
        24 none (some false) Direction.right 25
    , transition
        25 (some false) (some false) Direction.right 26
    , transition
        25 (some true) (some true) Direction.right 26
    , transition
        26 (some false) (some false) Direction.right 27
    , transition
        26 (some true) (some true) Direction.right 27
    , transition
        27 (some false) (some false) Direction.right 0
    , transition
        27 (some true) (some true) Direction.right 0

      -- Append the done symbol, return, then skip done plus the head cell.
    , transition
        30 (some false) (some false) Direction.right 30
    , transition
        30 (some true) (some true) Direction.right 30
    , transition
        30 none (some false) Direction.right 31
    , transition
        31 none (some false) Direction.right 32
    , transition
        32 none (some true) Direction.right 33
    , transition
        33 none (some true) Direction.left 34
    , transition
        34 (some false) (some false) Direction.left 34
    , transition
        34 (some true) (some true) Direction.left 34
    , transition
        34 none (some false) Direction.right 35
    , transition
        35 (some false) (some false) Direction.right 36
    , transition
        35 (some true) (some true) Direction.right 36
    , transition
        36 (some false) (some false) Direction.right 37
    , transition
        36 (some true) (some true) Direction.right 37
    , transition
        37 (some false) (some false) Direction.right 38
    , transition
        37 (some true) (some true) Direction.right 38
    , transition
        38 (some false) (some false) Direction.right 39
    , transition
        38 (some true) (some true) Direction.right 39
    , transition
        39 (some false) (some false) Direction.right 40
    , transition
        39 (some true) (some true) Direction.right 40
    , transition
        40 (some false) (some false) Direction.right 41
    , transition
        40 (some true) (some true) Direction.right 41
    , transition
        41 (some false) (some false) Direction.right 10
    , transition
        41 (some true) (some true) Direction.right 10

      -- Append blank, zero, and one cell symbols from the remaining cells.
    , transition
        50 (some false) (some false) Direction.right 50
    , transition
        50 (some true) (some true) Direction.right 50
    , transition
        50 none (some false) Direction.right 51
    , transition
        51 none (some true) Direction.right 52
    , transition
        52 none (some false) Direction.right 53
    , transition
        53 none (some false) Direction.left 54
    , transition
        54 (some false) (some false) Direction.left 54
    , transition
        54 (some true) (some true) Direction.left 54
    , transition
        54 none (some false) Direction.right 55
    , transition
        55 (some false) (some false) Direction.right 56
    , transition
        55 (some true) (some true) Direction.right 56
    , transition
        56 (some false) (some false) Direction.right 57
    , transition
        56 (some true) (some true) Direction.right 57
    , transition
        57 (some false) (some false) Direction.right 10
    , transition
        57 (some true) (some true) Direction.right 10

    , transition
        60 (some false) (some false) Direction.right 60
    , transition
        60 (some true) (some true) Direction.right 60
    , transition
        60 none (some false) Direction.right 61
    , transition
        61 none (some true) Direction.right 62
    , transition
        62 none (some false) Direction.right 63
    , transition
        63 none (some true) Direction.left 64
    , transition
        64 (some false) (some false) Direction.left 64
    , transition
        64 (some true) (some true) Direction.left 64
    , transition
        64 none (some false) Direction.right 65
    , transition
        65 (some false) (some false) Direction.right 66
    , transition
        65 (some true) (some true) Direction.right 66
    , transition
        66 (some false) (some false) Direction.right 67
    , transition
        66 (some true) (some true) Direction.right 67
    , transition
        67 (some false) (some false) Direction.right 10
    , transition
        67 (some true) (some true) Direction.right 10

    , transition
        70 (some false) (some false) Direction.right 70
    , transition
        70 (some true) (some true) Direction.right 70
    , transition
        70 none (some false) Direction.right 71
    , transition
        71 none (some true) Direction.right 72
    , transition
        72 none (some true) Direction.right 73
    , transition
        73 none (some false) Direction.left 74
    , transition
        74 (some false) (some false) Direction.left 74
    , transition
        74 (some true) (some true) Direction.left 74
    , transition
        74 none (some false) Direction.right 75
    , transition
        75 (some false) (some false) Direction.right 76
    , transition
        75 (some true) (some true) Direction.right 76
    , transition
        76 (some false) (some false) Direction.right 77
    , transition
        76 (some true) (some true) Direction.right 77
    , transition
        77 (some false) (some false) Direction.right 10
    , transition
        77 (some true) (some true) Direction.right 10

      -- Return to the transition marker and halt on the restored marker.
    , transition
        80 (some false) (some false) Direction.left 80
    , transition
        80 (some true) (some true) Direction.left 80
    , transition
        80 none (some false) Direction.left 81
    , transition
        81 (some false) (some false) Direction.right 99
    , transition
        81 (some true) (some true) Direction.right 99
    ]

private abbrev ITCD := InputTapeRightCellsDirectCopierDescription

theorem inputTapeRightCellsDirectCopierDescription_wellFormed :
    ITCD.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ITCD.transitions)
      (stateCount :=
        ITCD.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := ITCD.transitions)
      (by decide)

theorem inputTapeRightCellsDirectCopierDescription_haltTransitionFree :
    ITCD.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ITCD.transitions)
    (state := ITCD.halt)
    (by decide)

theorem inputTapeRightCellsDirectCopierDescription_subroutineReady :
    ITCD.SubroutineReady :=
  ⟨inputTapeRightCellsDirectCopierDescription_wellFormed,
    inputTapeRightCellsDirectCopierDescription_haltTransitionFree⟩

theorem
    inputTapeRightCellsDirectCopierDescription_step_scan20
    (leftRev : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    ITCD.stepConfig
        (config 20 leftRev (some bit :: rest.map some)) =
      some (config 20 (some bit :: leftRev)
        (rest.map some)) := by
  cases bit <;> cases rest <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_run_scan20
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    ITCD.runConfig
        remaining.length
        (config 20 leftRev (remaining.map some)) =
      config 20
        (List.append (remaining.reverse.map some) leftRev) [] := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [runConfig, config,
        tapeAtCells]
  | cons bit rest ih =>
      simp [runConfig,
        inputTapeRightCellsDirectCopierDescription_step_scan20,
        ih, List.append_assoc]

theorem
    inputTapeRightCellsDirectCopierDescription_run_write_tick
    (leftRev : List (Option Bool)) :
    ITCD.runConfig 4
        (config 20 leftRev []) =
      config 24
        (List.append [some false, some false] leftRev)
        [some true, some false] := by
  simp [InputTapeRightCellsDirectCopierDescription,
    config, tapeAtCells,
    runConfig, stepConfig,
    lookupTransition, Matches,
    transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_step_return24
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (leftBit current : Bool) (right : List (Option Bool)) :
    ITCD.stepConfig
        (config 24
          (List.append (some leftBit :: preRev.map some)
            (none :: leftOfMarker))
          (some current :: right)) =
      some (config 24
        (List.append (preRev.map some) (none :: leftOfMarker))
        (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      stepConfig, lookupTransition,
      Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

theorem
    inputTapeRightCellsDirectCopierDescription_run_return24
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (current : Bool) (right : List (Option Bool)) :
    ITCD.runConfig
        (preRev.length + 2)
        (config 24
          (List.append (preRev.map some) (none :: leftOfMarker))
          (some current :: right)) =
      config 25 (some false :: leftOfMarker)
        (List.append (preRev.reverse.map some)
          (some current :: right)) := by
  induction preRev generalizing current right with
  | nil =>
      cases current <;> cases right <;>
        simp [InputTapeRightCellsDirectCopierDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      simp only [List.map_cons, List.length_cons, List.reverse_cons]
      rw [show rest.length + 1 + 2 = (rest.length + 2) + 1 by
        omega]
      rw [runConfig]
      rw [inputTapeRightCellsDirectCopierDescription_step_return24]
      simpa [List.append_assoc] using ih bit (some current :: right)

theorem
    inputTapeRightCellsDirectCopierDescription_run_advance25_to0
    (leftRev : List (Option Bool)) (b1 b2 b3 : Bool)
    (right : List (Option Bool)) :
    ITCD.runConfig 3
        (config 25 leftRev
          (some b1 :: some b2 :: some b3 :: right)) =
      config 0
        (some b3 :: some b2 :: some b1 :: leftRev) right := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_run_copy_tick
    (leftOfMarker : List (Option Bool))
    (pre remaining : Word Bool) :
    exists steps : Nat,
      ITCD.runConfig steps
          (config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (encodeCodeSymbolAsInput
                MachineCodeSymbol.tick)
              remaining).map some)) =
        config 0
          (List.append
            ((encodeCodeSymbolAsInput
              MachineCodeSymbol.tick).reverse.map some)
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker)))
          ((List.append remaining
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.tick)).map some) := by
  let afterPrefixLeft : List (Option Bool) :=
    List.append [some false, some true, some false, none]
      (List.append (pre.reverse.map some) (none :: leftOfMarker))
  let returnPre : Word Bool :=
    List.append [false, false]
      (List.append remaining.reverse [false, true, false])
  let returnLeft : List (Option Bool) :=
    List.append (pre.reverse.map some) (none :: leftOfMarker)
  have hprefix :
      ITCD.runConfig 4
          (config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (encodeCodeSymbolAsInput
                MachineCodeSymbol.tick)
              remaining).map some)) =
        config 20 afterPrefixLeft (remaining.map some) := by
    simp [afterPrefixLeft,
      InputTapeRightCellsDirectCopierDescription,
      encodeCodeSymbolAsInput,
      config, tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight, List.map_reverse]
    cases List.map some remaining <;> rfl
  refine
    ⟨4 + (remaining.length + (4 + ((returnPre.length + 2) + 3))), ?_⟩
  rw [runConfig_add]
  rw [hprefix]
  rw [runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_scan20]
  rw [runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_write_tick]
  rw [runConfig_add]
  have hleft :
      List.append [some false, some false]
          (List.append (remaining.reverse.map some) afterPrefixLeft) =
        List.append (returnPre.map some) (none :: returnLeft) := by
    simp [afterPrefixLeft, returnPre, returnLeft,
      List.map_append, List.append_assoc]
  rw [show
      config 24
        (List.append [some false, some false]
          (List.append (remaining.reverse.map some) afterPrefixLeft))
        [some true, some false] =
      config 24
        (List.append (returnPre.map some) (none :: returnLeft))
        (some true :: [some false]) by
        simpa [List.map_reverse] using
          congrArg
            (fun left =>
              config 24 left [some true, some false])
            hleft]
  rw [inputTapeRightCellsDirectCopierDescription_run_return24]
  rw [show
      config 25 (some false :: returnLeft)
        (List.append (returnPre.reverse.map some) [some true, some false]) =
      config 25 (some false :: returnLeft)
        (some false :: some true :: some false ::
          ((List.append remaining
            (encodeCodeSymbolAsInput
              MachineCodeSymbol.tick)).map some)) by
        simp [returnPre, encodeCodeSymbolAsInput,
          List.map_append, List.reverse_append, List.append_assoc]]
  rw [inputTapeRightCellsDirectCopierDescription_run_advance25_to0]
  simp [returnLeft, encodeCodeSymbolAsInput,
    List.map_append]

def AppendCodeSymbolReturnToCurrentMarkerDescription
    (symbol : MachineCodeSymbol) : MachineDescription :=
  AppendCodeWordReturnToCurrentMarkerDescription [symbol]

theorem
    appendCodeSymbolReturnToCurrentMarkerDescription_subroutineReady
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolReturnToCurrentMarkerDescription
      symbol).SubroutineReady :=
  appendCodeWordReturnToCurrentMarkerDescription_subroutineReady
    [symbol] (by intro h; cases h)

theorem
    appendCodeSymbolReturnToCurrentMarkerDescription_run_from_scan
    (symbol : MachineCodeSymbol)
    (pre remaining : Word Bool)
    (leftOfMarker : List (Option Bool)) :
    exists steps : Nat,
      (AppendCodeSymbolReturnToCurrentMarkerDescription
        symbol).runConfig steps
          { state :=
              (AppendCodeSymbolReturnToCurrentMarkerDescription
                symbol).start
            tape :=
              appendScanTapeAtCells
                (List.append (pre.reverse.map some)
                  (none :: leftOfMarker))
                remaining } =
        config
          (AppendCodeSymbolReturnToCurrentMarkerDescription
            symbol).halt
          (some false :: leftOfMarker)
          ((List.append (List.append pre remaining)
            (encodeCodeSymbolAsInput symbol)).map
            some) := by
  rcases
      appendCodeWordReturnToCurrentMarkerDescription_run_from_scan
        [symbol] (by intro h; cases h)
        pre remaining leftOfMarker with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendCodeSymbolReturnToCurrentMarkerDescription,
    encodeCodeWordAsInput] using hsteps

def ReturnToTransitionMarkerDescription :
    MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition
        0 (some false) (some false) Direction.left 0
    , transition
        0 (some true) (some true) Direction.left 0
    , transition
        0 none (some false) Direction.left 1
    , transition
        1 (some false) (some false) Direction.right 2
    , transition
        1 (some true) (some true) Direction.right 2
    ]

private abbrev RTTM := ReturnToTransitionMarkerDescription

theorem returnToTransitionMarkerDescription_wellFormed :
    RTTM.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := RTTM.transitions)
      (stateCount :=
        RTTM.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := RTTM.transitions)
      (by decide)

theorem returnToTransitionMarkerDescription_haltTransitionFree :
    RTTM.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := RTTM.transitions)
    (state := RTTM.halt)
    (by decide)

theorem returnToTransitionMarkerDescription_subroutineReady :
    RTTM.SubroutineReady :=
  ⟨returnToTransitionMarkerDescription_wellFormed,
    returnToTransitionMarkerDescription_haltTransitionFree⟩
theorem returnToTransitionMarkerDescription_step_scan
    (preRev : Word Bool) (leftBit current : Bool)
    (right : List (Option Bool)) :
    RTTM.stepConfig
        (config 0
          (List.append
            (some leftBit :: preRev.map some) [none, some false])
          (some current :: right)) =
      some
        (config 0
          (List.append (preRev.map some) [none, some false])
          (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;>
    simp [ReturnToTransitionMarkerDescription,
      config, tapeAtCells,
      stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]
theorem returnToTransitionMarkerDescription_run
    (preRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    RTTM.runConfig
        (preRev.length + 3)
        (config 0
          (List.append (preRev.map some) [none, some false])
          (some current :: right)) =
      config 2 [some false]
        (some false ::
          List.append (preRev.reverse.map some)
            (some current :: right)) := by
  induction preRev generalizing current right with
  | nil =>
      cases current <;>
        simp [ReturnToTransitionMarkerDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      simp only [List.map_cons, List.length_cons, List.reverse_cons]
      rw [show Nat.succ rest.length + 3 = (rest.length + 3) + 1 by omega]
      rw [runConfig]
      rw [returnToTransitionMarkerDescription_step_scan]
      simpa [List.append_assoc] using ih b (some current :: right)

theorem
    returnToTransitionMarkerDescription_run_after_append_four_atCells
    (pre : Word Bool) (b0 b1 b2 b3 : Bool) :
    RTTM.runConfig
        (pre.length + 5)
        { state := RTTM.start
          tape :=
            Tape.move Direction.left
              (appendRightLastTapeAtCells
                (List.append (pre.reverse.map some)
                  [none, some false]) b0 b1 b2 b3) } =
      { state := RTTM.halt
        tape :=
          tapeAtCells [some false]
            (some false ::
              ((List.append pre [b0, b1, b2, b3]).map some)) } := by
  simpa [appendRightLastTapeAtCells, tapeAtCells,
    Tape.move, Tape.moveLeft, List.append_assoc] using
    returnToTransitionMarkerDescription_run
      (List.append [b1, b0] pre.reverse) b2 [some b3]

theorem
    returnToTransitionMarkerDescription_run_after_append_atCells :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall pre : Word Bool,
          exists steps : Nat,
            RTTM.runConfig steps
                { state := RTTM.start
                  tape :=
                    Tape.move Direction.left
                      (appendCodeWordLastTapeAtCells
                        (List.append (pre.reverse.map some)
                          [none, some false])
                        code) } =
              { state := RTTM.halt
                tape :=
                  tapeAtCells [some false]
                    (some false ::
                      ((List.append pre
                        (encodeCodeWordAsInput code)).map
                        some)) }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro pre
      cases symbol <;>
        refine ⟨pre.length + 5, ?_⟩ <;>
        simpa [appendCodeWordLastTapeAtCells,
          appendCodeSymbolLastTapeAtCells,
          appendRightLastTapeAtCells,
          encodeCodeSymbolAsInput,
          encodeCodeWordAsInput,
          Tape.move, Tape.moveLeft, List.append_assoc] using
          returnToTransitionMarkerDescription_run_after_append_four_atCells
            pre _ _ _ _
  | symbol :: next :: rest, _ => by
      intro pre
      let symbolBits := encodeCodeSymbolAsInput symbol
      rcases
          returnToTransitionMarkerDescription_run_after_append_atCells
            (next :: rest) (by intro h; cases h)
            (List.append pre symbolBits) with
        ⟨steps, hsteps⟩
      refine ⟨steps, ?_⟩
      have hleft :
          List.append (symbolBits.reverse.map some)
              (List.append (pre.reverse.map some) [none, some false]) =
            List.append
              ((List.append pre symbolBits).reverse.map some)
              [none, some false] := by
        simp [List.reverse_append, List.map_append, List.append_assoc]
      have hbits :
          List.append (List.append pre symbolBits)
              (encodeCodeWordAsInput (next :: rest)) =
            List.append pre
              (encodeCodeWordAsInput
                (symbol :: next :: rest)) := by
        simp [symbolBits,
          encodeCodeWordAsInput, List.append_assoc]
      simpa [appendCodeWordLastTapeAtCells, symbolBits,
        hleft, hbits, encodeCodeWordAsInput,
        List.map_append, List.append_assoc] using hsteps

def MarkedPrefixAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  seqSubroutine
    (MarkedPrefixThenAppendCodeWordLastDescription code)
    RTTM
    Direction.left

theorem
    markedPrefixAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (MarkedPrefixAppendCodeWordReturnDescription
      code).SubroutineReady :=
  seqSubroutine_subroutineReady
    (markedPrefixThenAppendCodeWordLastDescription_subroutineReady
      code hcode)
    returnToTransitionMarkerDescription_subroutineReady
theorem markedPrefixAppendCodeWordReturnDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (MarkedPrefixAppendCodeWordReturnDescription code).runConfig steps
          ((MarkedPrefixAppendCodeWordReturnDescription
            code).initial (b :: rest)) =
        { state :=
            (MarkedPrefixAppendCodeWordReturnDescription code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := MarkedPrefixThenAppendCodeWordLastDescription code
  let B := RTTM
  let Tmid :=
    appendCodeWordLastTapeAtCells
      (List.append
        ((false :: true :: b :: rest).reverse.map some)
        [none, some false])
      code
  have hAready : A.SubroutineReady := by
    exact
      markedPrefixThenAppendCodeWordLastDescription_subroutineReady
        code hcode
  have hBready : B.SubroutineReady := by
    exact returnToTransitionMarkerDescription_subroutineReady
  rcases
      markedPrefixThenAppendCodeWordLastDescription_run
        code hcode b rest with
    ⟨nA, hArunBase⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape := Tape.input (b :: rest) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid, initial] using hArunBase
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
                    (encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        returnToTransitionMarkerDescription_run_after_append_atCells
          code hcode (false :: true :: b :: rest) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid] using hB
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [MarkedPrefixAppendCodeWordReturnDescription,
    initial, A, B] using hn
theorem markedPrefixAppendCodeWordReturnDescription_run_checked
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (MarkedPrefixAppendCodeWordReturnDescription code).runConfig steps
          { state := (MarkedPrefixAppendCodeWordReturnDescription code).start
            tape :=
              tapeAtCells []
                (List.append (some b :: rest.map some) [none]) } =
        { state :=
            (MarkedPrefixAppendCodeWordReturnDescription code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := MarkedPrefixThenAppendCodeWordLastDescription code
  let B := RTTM
  let Tmid :=
    appendCodeWordLastTapeAtCells
      (List.append
        ((false :: true :: b :: rest).reverse.map some)
        [none, some false])
      code
  have hAready : A.SubroutineReady := by
    exact
      markedPrefixThenAppendCodeWordLastDescription_subroutineReady
        code hcode
  have hBready : B.SubroutineReady := by
    exact returnToTransitionMarkerDescription_subroutineReady
  rcases
      markedPrefixThenAppendCodeWordLastDescription_run_checked
        code hcode b rest with
    ⟨nA, hArunBase⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells []
                (List.append (some b :: rest.map some) [none]) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid] using hArunBase
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
                    (encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        returnToTransitionMarkerDescription_run_after_append_atCells
          code hcode (false :: true :: b :: rest) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid] using hB
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [MarkedPrefixAppendCodeWordReturnDescription,
    A, B] using hn

def MarkedPrefixAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  MarkedPrefixAppendCodeWordReturnDescription
    (encodeNat n)

theorem
    markedPrefixAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (MarkedPrefixAppendNatReturnDescription
      n).SubroutineReady :=
  markedPrefixAppendCodeWordReturnDescription_subroutineReady
    (encodeNat n)
    (encodeNat_ne_nil n)
theorem markedPrefixAppendNatReturnDescription_run
    (n : Nat) (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (MarkedPrefixAppendNatReturnDescription n).runConfig steps
          ((MarkedPrefixAppendNatReturnDescription
            n).initial (b :: rest)) =
        { state :=
            (MarkedPrefixAppendNatReturnDescription n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (encodeCodeWordAsInput
                    (encodeNat n))).map some)) } := by
  simpa [MarkedPrefixAppendNatReturnDescription] using
    markedPrefixAppendCodeWordReturnDescription_run
      (encodeNat n)
      (encodeNat_ne_nil n)
      b rest
theorem markedPrefixAppendNatReturnDescription_run_checked
    (n : Nat) (b : Bool) (rest : Word Bool) :
    exists steps : Nat,
      (MarkedPrefixAppendNatReturnDescription n).runConfig steps
          { state :=
              (MarkedPrefixAppendNatReturnDescription n).start
            tape :=
              tapeAtCells []
                (List.append (some b :: rest.map some) [none]) } =
        { state :=
            (MarkedPrefixAppendNatReturnDescription n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: b :: rest)
                  (encodeCodeWordAsInput
                    (encodeNat n))).map some)) } := by
  simpa [MarkedPrefixAppendNatReturnDescription] using
    markedPrefixAppendCodeWordReturnDescription_run_checked
      (encodeNat n)
      (encodeNat_ne_nil n)
      b rest
theorem stageInputBits_exists_cons
    (w : Word Bool) (stage : Nat) :
    exists b : Bool,
    exists rest : Word Bool,
      encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w stage) =
        b :: rest := by
  have hne :
      encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w stage) ≠ [] := by
    cases w <;>
      simp [PairedRecognizerDovetailStageInputCode,
        DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat,
        encodeCodeWordAsInput,
        encodeCodeSymbolAsInput]
  cases hbits :
      encodeCodeWordAsInput
        (PairedRecognizerDovetailStageInputCode w stage) with
  | nil =>
      exact False.elim (hne hbits)
  | cons b rest =>
      exact ⟨b, rest, rfl⟩

theorem
    markedPrefixAppendCodeWordReturnDescription_run_stageInput
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (MarkedPrefixAppendCodeWordReturnDescription code).runConfig steps
          ((MarkedPrefixAppendCodeWordReturnDescription
            code).initial
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (MarkedPrefixAppendCodeWordReturnDescription code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (encodeCodeWordAsInput code))).map
                  some)) } := by
  rcases stageInputBits_exists_cons w stage with
    ⟨b, rest, hbits⟩
  rcases
      markedPrefixAppendCodeWordReturnDescription_run
        code hcode b rest with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [hbits, initial, List.append_assoc] using hsteps
theorem markedPrefixAppendNatReturnDescription_run_stageInput
    (n : Nat) (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (MarkedPrefixAppendNatReturnDescription n).runConfig steps
          ((MarkedPrefixAppendNatReturnDescription
            n).initial
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (MarkedPrefixAppendNatReturnDescription n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (encodeCodeWordAsInput
                      (encodeNat n)))).map some)) } := by
  simpa [MarkedPrefixAppendNatReturnDescription] using
    markedPrefixAppendCodeWordReturnDescription_run_stageInput
      (encodeNat n)
      (encodeNat_ne_nil n)
      w stage
theorem markedPrefixAppendNatReturnDescription_run_stageInput_checked
    (n : Nat) (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (MarkedPrefixAppendNatReturnDescription n).runConfig steps
          { state :=
              (MarkedPrefixAppendNatReturnDescription n).start
            tape :=
              tapeAtCells []
                (List.append
                  ((encodeCodeWordAsInput
                    (PairedRecognizerDovetailStageInputCode w stage)).map
                    some)
                  [none]) } =
        { state :=
            (MarkedPrefixAppendNatReturnDescription n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (encodeCodeWordAsInput
                      (encodeNat n)))).map some)) } := by
  rcases stageInputBits_exists_cons w stage with
    ⟨b, rest, hbits⟩
  rcases
      markedPrefixAppendNatReturnDescription_run_checked
        n b rest with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [hbits, List.append_assoc] using hsteps

def TransitionPrefixedAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  seqSubroutine
    (TransitionPrefixedThenAppendCodeWordLastDescription code)
    RTTM
    Direction.left

theorem
    transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (TransitionPrefixedAppendCodeWordReturnDescription
      code).SubroutineReady :=
  seqSubroutine_subroutineReady
    (transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
      code hcode)
    returnToTransitionMarkerDescription_subroutineReady
theorem transitionPrefixedAppendCodeWordReturnDescription_run
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (payload : Word Bool) :
    exists steps : Nat,
      (TransitionPrefixedAppendCodeWordReturnDescription
        code).runConfig steps
          { state :=
              (TransitionPrefixedAppendCodeWordReturnDescription
                code).start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (TransitionPrefixedAppendCodeWordReturnDescription
              code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := TransitionPrefixedThenAppendCodeWordLastDescription code
  let B := RTTM
  let Tmid :=
    appendCodeWordLastTapeAtCells
      (List.append
        ((false :: true :: payload).reverse.map some)
        [none, some false])
      code
  have hAready : A.SubroutineReady := by
    exact
      transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
        code hcode
  have hBready : B.SubroutineReady := by
    exact returnToTransitionMarkerDescription_subroutineReady
  rcases
      transitionPrefixedThenAppendCodeWordLastDescription_run
        code hcode payload with
    ⟨nA, hArunBase⟩
  have hArun :
      A.runConfig nA
          { state := A.start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state := A.halt, tape := Tmid } := by
    simpa [A, Tmid] using hArunBase
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.left Tmid } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append (false :: true :: payload)
                    (encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        returnToTransitionMarkerDescription_run_after_append_atCells
          code hcode (false :: true :: payload) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid] using hB
  rcases
      seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [TransitionPrefixedAppendCodeWordReturnDescription,
    A, B] using hn

def TransitionPrefixedAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  TransitionPrefixedAppendCodeWordReturnDescription
    (encodeNat n)

theorem
    transitionPrefixedAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (TransitionPrefixedAppendNatReturnDescription
      n).SubroutineReady :=
  transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    (encodeNat n)
    (encodeNat_ne_nil n)
theorem transitionPrefixedAppendNatReturnDescription_run
    (n : Nat) (payload : Word Bool) :
    exists steps : Nat,
      (TransitionPrefixedAppendNatReturnDescription
        n).runConfig steps
          { state :=
              (TransitionPrefixedAppendNatReturnDescription
                n).start
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true] payload).map some)) } =
        { state :=
            (TransitionPrefixedAppendNatReturnDescription n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append (false :: true :: payload)
                  (encodeCodeWordAsInput
                    (encodeNat n))).map some)) } := by
  simpa [TransitionPrefixedAppendNatReturnDescription] using
    transitionPrefixedAppendCodeWordReturnDescription_run
      (encodeNat n)
      (encodeNat_ne_nil n)
      payload


end DovetailInitialLayoutInitializer
end Computability
end FoC
