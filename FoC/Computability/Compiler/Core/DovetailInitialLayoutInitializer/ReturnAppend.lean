import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.AppendLast

set_option doc.verso true

/-!
# ReturnAppend

Supporting declarations and helper lemmas for Computability Compiler Core DovetailInitialLayoutInitializer ReturnAppend.
-/


namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

def MarkTransitionSecondBitDescription :
    MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ MachineDescription.transition
        0 (some false) none Direction.left 1
    , MachineDescription.transition
        1 (some false) (some false) Direction.right 2
    ]

 /-- {name}`markTransitionSecondBitDescription_wellFormed` captures the core lemma for this local construction. -/
theorem markTransitionSecondBitDescription_wellFormed :
    MarkTransitionSecondBitDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · exact transition_wellFormed_of_all
      (l := MarkTransitionSecondBitDescription.transitions)
      (stateCount :=
        MarkTransitionSecondBitDescription.stateCount)
      (by
        native_decide)
  · exact transition_deterministic_of_all
      (l := MarkTransitionSecondBitDescription.transitions)
      (by
        native_decide)

 /-- {name}`markTransitionSecondBitDescription_haltTransitionFree` establishes the halting condition in this construction. -/
theorem markTransitionSecondBitDescription_haltTransitionFree :
    MarkTransitionSecondBitDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := MarkTransitionSecondBitDescription.transitions)
    (state := MarkTransitionSecondBitDescription.halt)
    (by
      native_decide)

 /-- {name}`markTransitionSecondBitDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem markTransitionSecondBitDescription_subroutineReady :
    MarkTransitionSecondBitDescription.SubroutineReady :=
  ⟨markTransitionSecondBitDescription_wellFormed,
    markTransitionSecondBitDescription_haltTransitionFree⟩

 /-- {name}`markTransitionSecondBitDescription_run` captures the core lemma for this local construction. -/
theorem markTransitionSecondBitDescription_run
    (payload : Word Bool) :
    MarkTransitionSecondBitDescription.runConfig 2
        (config 0 [some false]
          (some false ::
            ((List.append [false, true] payload).map some))) =
      { state := MarkTransitionSecondBitDescription.halt
        tape :=
          tapeAtCells [some false]
            (none ::
              ((List.append [false, true] payload).map some)) } := by
  cases payload <;>
    simp [MarkTransitionSecondBitDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

def TransitionPrefixedThenAppendCodeWordLastDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    MarkTransitionSecondBitDescription
    (AppendCodeWordLastDescription code)
    Direction.right
     /-- {name}`transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (TransitionPrefixedThenAppendCodeWordLastDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    markTransitionSecondBitDescription_subroutineReady
    (appendCodeWordLastDescription_subroutineReady code hcode)
     /-- {name}`transitionPrefixedThenAppendCodeWordLastDescription_run` captures the core lemma for this local construction. -/

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
  let A := MarkTransitionSecondBitDescription
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
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
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
    [ MachineDescription.transition
        0 (some false) (some false) Direction.left 0
    , MachineDescription.transition
        0 (some true) (some true) Direction.left 0
    , MachineDescription.transition
        0 none (some false) Direction.right 1
    ]

 /-- {name}`returnToCurrentMarkerDescription_wellFormed` captures the core lemma for this local construction. -/
theorem returnToCurrentMarkerDescription_wellFormed :
    ReturnToCurrentMarkerDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · exact transition_wellFormed_of_all
      (l := ReturnToCurrentMarkerDescription.transitions)
      (stateCount :=
        ReturnToCurrentMarkerDescription.stateCount)
      (by
        native_decide)
  · exact transition_deterministic_of_all
      (l := ReturnToCurrentMarkerDescription.transitions)
      (by
        native_decide)
     /-- {name}`returnToCurrentMarkerDescription_haltTransitionFree` establishes the halting condition in this construction. -/

theorem
    returnToCurrentMarkerDescription_haltTransitionFree :
    ReturnToCurrentMarkerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ReturnToCurrentMarkerDescription.transitions)
    (state := ReturnToCurrentMarkerDescription.halt)
    (by
      native_decide)
     /-- {name}`returnToCurrentMarkerDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    returnToCurrentMarkerDescription_subroutineReady :
    ReturnToCurrentMarkerDescription.SubroutineReady :=
  ⟨returnToCurrentMarkerDescription_wellFormed,
    returnToCurrentMarkerDescription_haltTransitionFree⟩

 /-- {name}`returnToCurrentMarkerDescription_step_scan` characterizes a scan safety phase. -/
theorem returnToCurrentMarkerDescription_step_scan
    (preRev : Word Bool) (leftBit current : Bool)
    (leftOfMarker right : List (Option Bool)) :
    ReturnToCurrentMarkerDescription.stepConfig
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
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

 /-- {name}`returnToCurrentMarkerDescription_run` captures the core lemma for this local construction. -/
theorem returnToCurrentMarkerDescription_run
    (preRev : Word Bool) (current : Bool)
    (leftOfMarker right : List (Option Bool)) :
    ReturnToCurrentMarkerDescription.runConfig
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
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      simp only [List.map_cons, List.length_cons, List.reverse_cons]
      rw [show Nat.succ rest.length + 2 = (rest.length + 2) + 1 by omega]
      rw [MachineDescription.runConfig]
      rw [returnToCurrentMarkerDescription_step_scan]
      simpa [List.append_assoc] using ih b (some current :: right)
     /-- {name}`returnToCurrentMarkerDescription_run_after_append_four_atCells` states the corresponding theorem run form. -/

theorem
    returnToCurrentMarkerDescription_run_after_append_four_atCells
    (pre : Word Bool) (leftOfMarker : List (Option Bool))
    (b0 b1 b2 b3 : Bool) :
    ReturnToCurrentMarkerDescription.runConfig
        (pre.length + 4)
        { state := ReturnToCurrentMarkerDescription.start
          tape :=
            Tape.move Direction.left
              (appendRightLastTapeAtCells
                (List.append (pre.reverse.map some)
                  (none :: leftOfMarker)) b0 b1 b2 b3) } =
      config
        ReturnToCurrentMarkerDescription.halt
        (some false :: leftOfMarker)
        ((List.append pre [b0, b1, b2, b3]).map some) := by
  simpa [appendRightLastTapeAtCells, config,
    Tape.move, Tape.moveLeft, List.append_assoc] using
    returnToCurrentMarkerDescription_run
      (List.append [b1, b0] pre.reverse) b2
      leftOfMarker [some b3]
     /-- {name}`returnToCurrentMarkerDescription_run_after_append_atCells` states the corresponding theorem run form. -/

theorem
    returnToCurrentMarkerDescription_run_after_append_atCells :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall pre : Word Bool,
        forall leftOfMarker : List (Option Bool),
          exists steps : Nat,
            ReturnToCurrentMarkerDescription.runConfig steps
                { state := ReturnToCurrentMarkerDescription.start
                  tape :=
                    Tape.move Direction.left
                      (appendCodeWordLastTapeAtCells
                        (List.append (pre.reverse.map some)
                          (none :: leftOfMarker))
                        code) } =
              config
                ReturnToCurrentMarkerDescription.halt
                (some false :: leftOfMarker)
                ((List.append pre
                  (MachineDescription.encodeCodeWordAsInput code)).map some)
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro pre leftOfMarker
      cases symbol <;>
        refine ⟨pre.length + 4, ?_⟩ <;>
        simpa [appendCodeWordLastTapeAtCells,
          appendCodeSymbolLastTapeAtCells,
          appendRightLastTapeAtCells,
          MachineDescription.encodeCodeSymbolAsInput,
          MachineDescription.encodeCodeWordAsInput,
          Tape.move, Tape.moveLeft, List.append_assoc] using
          returnToCurrentMarkerDescription_run_after_append_four_atCells
            pre leftOfMarker _ _ _ _
  | symbol :: next :: rest, _ => by
      intro pre leftOfMarker
      let symbolBits := MachineDescription.encodeCodeSymbolAsInput symbol
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
              (MachineDescription.encodeCodeWordAsInput (next :: rest)) =
            List.append pre
              (MachineDescription.encodeCodeWordAsInput
                (symbol :: next :: rest)) := by
        simp [symbolBits,
          MachineDescription.encodeCodeWordAsInput, List.append_assoc]
      simpa [appendCodeWordLastTapeAtCells, symbolBits,
        hleft, hbits, MachineDescription.encodeCodeWordAsInput,
        List.map_append, List.append_assoc] using hsteps

def AppendCodeWordReturnToCurrentMarkerDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    (AppendCodeWordLastDescription code)
    ReturnToCurrentMarkerDescription
    Direction.left
     /-- {name}`appendCodeWordReturnToCurrentMarkerDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    appendCodeWordReturnToCurrentMarkerDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (AppendCodeWordReturnToCurrentMarkerDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (appendCodeWordLastDescription_subroutineReady code hcode)
    returnToCurrentMarkerDescription_subroutineReady
     /-- {name}`appendCodeWordReturnToCurrentMarkerDescription_run_from_scan` states the corresponding theorem run form. -/

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
            (MachineDescription.encodeCodeWordAsInput code)).map some) := by
  let A := AppendCodeWordLastDescription code
  let B := ReturnToCurrentMarkerDescription
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
              (MachineDescription.encodeCodeWordAsInput code)).map some) := by
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
            MachineDescription.Configuration) =
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
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
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
    [ MachineDescription.transition
        0 (some false) (some false) Direction.right 1
    , MachineDescription.transition
        1 (some false) none Direction.right 2
    , MachineDescription.transition
        2 (some false) (some false) Direction.right 3
    , MachineDescription.transition
        3 (some true) (some true) Direction.right 4
    , MachineDescription.transition
        4 (some false) (some false) Direction.right 5
    , MachineDescription.transition
        5 (some false) (some false) Direction.right 6
    , MachineDescription.transition
        6 (some true) (some true) Direction.right 7
    , MachineDescription.transition
        7 (some false) (some false) Direction.right 8
    ]

 /-- {name}`rightCellsCopierStartDescription_wellFormed` captures the core lemma for this local construction. -/
theorem rightCellsCopierStartDescription_wellFormed :
    RightCellsCopierStartDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · exact transition_wellFormed_of_all
      (l := RightCellsCopierStartDescription.transitions)
      (stateCount :=
        RightCellsCopierStartDescription.stateCount)
      (by
        native_decide)
  · exact transition_deterministic_of_all
      (l := RightCellsCopierStartDescription.transitions)
      (by
        native_decide)
     /-- {name}`rightCellsCopierStartDescription_haltTransitionFree` establishes the halting condition in this construction. -/

theorem
    rightCellsCopierStartDescription_haltTransitionFree :
    RightCellsCopierStartDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := RightCellsCopierStartDescription.transitions)
    (state := RightCellsCopierStartDescription.halt)
    (by
      native_decide)
     /-- {name}`rightCellsCopierStartDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    rightCellsCopierStartDescription_subroutineReady :
    RightCellsCopierStartDescription.SubroutineReady :=
  ⟨rightCellsCopierStartDescription_wellFormed,
    rightCellsCopierStartDescription_haltTransitionFree⟩

 /-- {name}`rightCellsCopierStartDescription_run` captures the core lemma for this local construction. -/
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
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

def InputTapeRightCellsDirectCopierDescription :
    MachineDescription where
  stateCount := 100
  start := 0
  halt := 99
  transitions :=
    [ -- Copy the residual unary length prefix.
      MachineDescription.transition
        0 (some false) none Direction.right 1
    , MachineDescription.transition
        1 (some false) (some false) Direction.right 2
    , MachineDescription.transition
        2 (some true) (some true) Direction.right 3
    , MachineDescription.transition
        3 (some false) (some false) Direction.right 20
    , MachineDescription.transition
        3 (some true) (some true) Direction.right 30

      -- In cell mode, stop when the next source symbol is a nat symbol.
    , MachineDescription.transition
        10 (some false) (some false) Direction.right 11
    , MachineDescription.transition
        11 (some false) (some false) Direction.left 80
    , MachineDescription.transition
        11 (some true) (some true) Direction.left 12
    , MachineDescription.transition
        12 (some false) none Direction.right 13
    , MachineDescription.transition
        13 (some true) (some true) Direction.right 14
    , MachineDescription.transition
        14 (some false) (some false) Direction.right 15
    , MachineDescription.transition
        14 (some true) (some true) Direction.right 18
    , MachineDescription.transition
        15 (some false) (some false) Direction.right 50
    , MachineDescription.transition
        15 (some true) (some true) Direction.right 60
    , MachineDescription.transition
        18 (some false) (some false) Direction.right 70

      -- Append a tick symbol, return to its temporary marker, and advance.
    , MachineDescription.transition
        20 (some false) (some false) Direction.right 20
    , MachineDescription.transition
        20 (some true) (some true) Direction.right 20
    , MachineDescription.transition
        20 none (some false) Direction.right 21
    , MachineDescription.transition
        21 none (some false) Direction.right 22
    , MachineDescription.transition
        22 none (some true) Direction.right 23
    , MachineDescription.transition
        23 none (some false) Direction.left 24
    , MachineDescription.transition
        24 (some false) (some false) Direction.left 24
    , MachineDescription.transition
        24 (some true) (some true) Direction.left 24
    , MachineDescription.transition
        24 none (some false) Direction.right 25
    , MachineDescription.transition
        25 (some false) (some false) Direction.right 26
    , MachineDescription.transition
        25 (some true) (some true) Direction.right 26
    , MachineDescription.transition
        26 (some false) (some false) Direction.right 27
    , MachineDescription.transition
        26 (some true) (some true) Direction.right 27
    , MachineDescription.transition
        27 (some false) (some false) Direction.right 0
    , MachineDescription.transition
        27 (some true) (some true) Direction.right 0

      -- Append the done symbol, return, then skip done plus the head cell.
    , MachineDescription.transition
        30 (some false) (some false) Direction.right 30
    , MachineDescription.transition
        30 (some true) (some true) Direction.right 30
    , MachineDescription.transition
        30 none (some false) Direction.right 31
    , MachineDescription.transition
        31 none (some false) Direction.right 32
    , MachineDescription.transition
        32 none (some true) Direction.right 33
    , MachineDescription.transition
        33 none (some true) Direction.left 34
    , MachineDescription.transition
        34 (some false) (some false) Direction.left 34
    , MachineDescription.transition
        34 (some true) (some true) Direction.left 34
    , MachineDescription.transition
        34 none (some false) Direction.right 35
    , MachineDescription.transition
        35 (some false) (some false) Direction.right 36
    , MachineDescription.transition
        35 (some true) (some true) Direction.right 36
    , MachineDescription.transition
        36 (some false) (some false) Direction.right 37
    , MachineDescription.transition
        36 (some true) (some true) Direction.right 37
    , MachineDescription.transition
        37 (some false) (some false) Direction.right 38
    , MachineDescription.transition
        37 (some true) (some true) Direction.right 38
    , MachineDescription.transition
        38 (some false) (some false) Direction.right 39
    , MachineDescription.transition
        38 (some true) (some true) Direction.right 39
    , MachineDescription.transition
        39 (some false) (some false) Direction.right 40
    , MachineDescription.transition
        39 (some true) (some true) Direction.right 40
    , MachineDescription.transition
        40 (some false) (some false) Direction.right 41
    , MachineDescription.transition
        40 (some true) (some true) Direction.right 41
    , MachineDescription.transition
        41 (some false) (some false) Direction.right 10
    , MachineDescription.transition
        41 (some true) (some true) Direction.right 10

      -- Append blank, zero, and one cell symbols from the remaining cells.
    , MachineDescription.transition
        50 (some false) (some false) Direction.right 50
    , MachineDescription.transition
        50 (some true) (some true) Direction.right 50
    , MachineDescription.transition
        50 none (some false) Direction.right 51
    , MachineDescription.transition
        51 none (some true) Direction.right 52
    , MachineDescription.transition
        52 none (some false) Direction.right 53
    , MachineDescription.transition
        53 none (some false) Direction.left 54
    , MachineDescription.transition
        54 (some false) (some false) Direction.left 54
    , MachineDescription.transition
        54 (some true) (some true) Direction.left 54
    , MachineDescription.transition
        54 none (some false) Direction.right 55
    , MachineDescription.transition
        55 (some false) (some false) Direction.right 56
    , MachineDescription.transition
        55 (some true) (some true) Direction.right 56
    , MachineDescription.transition
        56 (some false) (some false) Direction.right 57
    , MachineDescription.transition
        56 (some true) (some true) Direction.right 57
    , MachineDescription.transition
        57 (some false) (some false) Direction.right 10
    , MachineDescription.transition
        57 (some true) (some true) Direction.right 10

    , MachineDescription.transition
        60 (some false) (some false) Direction.right 60
    , MachineDescription.transition
        60 (some true) (some true) Direction.right 60
    , MachineDescription.transition
        60 none (some false) Direction.right 61
    , MachineDescription.transition
        61 none (some true) Direction.right 62
    , MachineDescription.transition
        62 none (some false) Direction.right 63
    , MachineDescription.transition
        63 none (some true) Direction.left 64
    , MachineDescription.transition
        64 (some false) (some false) Direction.left 64
    , MachineDescription.transition
        64 (some true) (some true) Direction.left 64
    , MachineDescription.transition
        64 none (some false) Direction.right 65
    , MachineDescription.transition
        65 (some false) (some false) Direction.right 66
    , MachineDescription.transition
        65 (some true) (some true) Direction.right 66
    , MachineDescription.transition
        66 (some false) (some false) Direction.right 67
    , MachineDescription.transition
        66 (some true) (some true) Direction.right 67
    , MachineDescription.transition
        67 (some false) (some false) Direction.right 10
    , MachineDescription.transition
        67 (some true) (some true) Direction.right 10

    , MachineDescription.transition
        70 (some false) (some false) Direction.right 70
    , MachineDescription.transition
        70 (some true) (some true) Direction.right 70
    , MachineDescription.transition
        70 none (some false) Direction.right 71
    , MachineDescription.transition
        71 none (some true) Direction.right 72
    , MachineDescription.transition
        72 none (some true) Direction.right 73
    , MachineDescription.transition
        73 none (some false) Direction.left 74
    , MachineDescription.transition
        74 (some false) (some false) Direction.left 74
    , MachineDescription.transition
        74 (some true) (some true) Direction.left 74
    , MachineDescription.transition
        74 none (some false) Direction.right 75
    , MachineDescription.transition
        75 (some false) (some false) Direction.right 76
    , MachineDescription.transition
        75 (some true) (some true) Direction.right 76
    , MachineDescription.transition
        76 (some false) (some false) Direction.right 77
    , MachineDescription.transition
        76 (some true) (some true) Direction.right 77
    , MachineDescription.transition
        77 (some false) (some false) Direction.right 10
    , MachineDescription.transition
        77 (some true) (some true) Direction.right 10

      -- Return to the transition marker and halt on the restored marker.
    , MachineDescription.transition
        80 (some false) (some false) Direction.left 80
    , MachineDescription.transition
        80 (some true) (some true) Direction.left 80
    , MachineDescription.transition
        80 none (some false) Direction.left 81
    , MachineDescription.transition
        81 (some false) (some false) Direction.right 99
    , MachineDescription.transition
        81 (some true) (some true) Direction.right 99
    ]

 /-- {name}`inputTapeRightCellsDirectCopierDescription_wellFormed` captures the core lemma for this local construction. -/
theorem inputTapeRightCellsDirectCopierDescription_wellFormed :
    InputTapeRightCellsDirectCopierDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · exact transition_wellFormed_of_all
      (l := InputTapeRightCellsDirectCopierDescription.transitions)
      (stateCount :=
        InputTapeRightCellsDirectCopierDescription.stateCount)
      (by
        native_decide)
  · exact transition_deterministic_of_all
      (l := InputTapeRightCellsDirectCopierDescription.transitions)
      (by
        native_decide)
     /-- {name}`inputTapeRightCellsDirectCopierDescription_haltTransitionFree` establishes the halting condition in this construction. -/

theorem
    inputTapeRightCellsDirectCopierDescription_haltTransitionFree :
    InputTapeRightCellsDirectCopierDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := InputTapeRightCellsDirectCopierDescription.transitions)
    (state := InputTapeRightCellsDirectCopierDescription.halt)
    (by
      native_decide)
     /-- {name}`inputTapeRightCellsDirectCopierDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    inputTapeRightCellsDirectCopierDescription_subroutineReady :
    InputTapeRightCellsDirectCopierDescription.SubroutineReady :=
  ⟨inputTapeRightCellsDirectCopierDescription_wellFormed,
    inputTapeRightCellsDirectCopierDescription_haltTransitionFree⟩
     /-- {name}`inputTapeRightCellsDirectCopierDescription_step_scan20` characterizes a scan safety phase. -/

theorem
    inputTapeRightCellsDirectCopierDescription_step_scan20
    (leftRev : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 20 leftRev (some bit :: rest.map some)) =
      some (config 20 (some bit :: leftRev)
        (rest.map some)) := by
  cases bit <;> cases rest <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]
     /-- {name}`inputTapeRightCellsDirectCopierDescription_run_scan20` states the corresponding theorem run form. -/

theorem
    inputTapeRightCellsDirectCopierDescription_run_scan20
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        remaining.length
        (config 20 leftRev (remaining.map some)) =
      config 20
        (List.append (remaining.reverse.map some) leftRev) [] := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig, config,
        tapeAtCells]
  | cons bit rest ih =>
      simp [MachineDescription.runConfig,
        inputTapeRightCellsDirectCopierDescription_step_scan20,
        ih, List.append_assoc]
     /-- {name}`inputTapeRightCellsDirectCopierDescription_run_write_tick` states the corresponding theorem run form. -/

theorem
    inputTapeRightCellsDirectCopierDescription_run_write_tick
    (leftRev : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig 4
        (config 20 leftRev []) =
      config 24
        (List.append [some false, some false] leftRev)
        [some true, some false] := by
  simp [InputTapeRightCellsDirectCopierDescription,
    config, tapeAtCells,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight]
     /-- {name}`inputTapeRightCellsDirectCopierDescription_step_return24` captures the core lemma for this local construction. -/

theorem
    inputTapeRightCellsDirectCopierDescription_step_return24
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (leftBit current : Bool) (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
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
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, MachineDescription.transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]
     /-- {name}`inputTapeRightCellsDirectCopierDescription_run_return24` states the corresponding theorem run form. -/

theorem
    inputTapeRightCellsDirectCopierDescription_run_return24
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (current : Bool) (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig
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
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      simp only [List.map_cons, List.length_cons, List.reverse_cons]
      rw [show rest.length + 1 + 2 = (rest.length + 2) + 1 by
        omega]
      rw [MachineDescription.runConfig]
      rw [inputTapeRightCellsDirectCopierDescription_step_return24]
      simpa [List.append_assoc] using ih bit (some current :: right)
     /-- {name}`inputTapeRightCellsDirectCopierDescription_run_advance25_to0` states the corresponding theorem run form. -/

theorem
    inputTapeRightCellsDirectCopierDescription_run_advance25_to0
    (leftRev : List (Option Bool)) (b1 b2 b3 : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig 3
        (config 25 leftRev
          (some b1 :: some b2 :: some b3 :: right)) =
      config 0
        (some b3 :: some b2 :: some b1 :: leftRev) right := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]
     /-- {name}`inputTapeRightCellsDirectCopierDescription_run_copy_tick` states the corresponding theorem run form. -/

theorem
    inputTapeRightCellsDirectCopierDescription_run_copy_tick
    (leftOfMarker : List (Option Bool))
    (pre remaining : Word Bool) :
    exists steps : Nat,
      InputTapeRightCellsDirectCopierDescription.runConfig steps
          (config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.tick)
              remaining).map some)) =
        config 0
          (List.append
            ((MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.tick).reverse.map some)
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker)))
          ((List.append remaining
            (MachineDescription.encodeCodeSymbolAsInput
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
      InputTapeRightCellsDirectCopierDescription.runConfig 4
          (config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.tick)
              remaining).map some)) =
        config 20 afterPrefixLeft (remaining.map some) := by
    simp [afterPrefixLeft,
      InputTapeRightCellsDirectCopierDescription,
      MachineDescription.encodeCodeSymbolAsInput,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight, List.map_reverse]
    cases List.map some remaining <;> rfl
  refine
    ⟨4 + (remaining.length + (4 + ((returnPre.length + 2) + 3))), ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [hprefix]
  rw [MachineDescription.runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_scan20]
  rw [MachineDescription.runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_write_tick]
  rw [MachineDescription.runConfig_add]
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
            (MachineDescription.encodeCodeSymbolAsInput
              MachineCodeSymbol.tick)).map some)) by
        simp [returnPre, MachineDescription.encodeCodeSymbolAsInput,
          List.map_append, List.reverse_append, List.append_assoc]]
  rw [inputTapeRightCellsDirectCopierDescription_run_advance25_to0]
  simp [returnLeft, MachineDescription.encodeCodeSymbolAsInput,
    List.map_append]

def AppendCodeSymbolReturnToCurrentMarkerDescription
    (symbol : MachineCodeSymbol) : MachineDescription :=
  AppendCodeWordReturnToCurrentMarkerDescription [symbol]
     /-- {name}`appendCodeSymbolReturnToCurrentMarkerDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    appendCodeSymbolReturnToCurrentMarkerDescription_subroutineReady
    (symbol : MachineCodeSymbol) :
    (AppendCodeSymbolReturnToCurrentMarkerDescription
      symbol).SubroutineReady :=
  appendCodeWordReturnToCurrentMarkerDescription_subroutineReady
    [symbol] (by intro h; cases h)
     /-- {name}`appendCodeSymbolReturnToCurrentMarkerDescription_run_from_scan` states the corresponding theorem run form. -/

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
            (MachineDescription.encodeCodeSymbolAsInput symbol)).map
            some) := by
  rcases
      appendCodeWordReturnToCurrentMarkerDescription_run_from_scan
        [symbol] (by intro h; cases h)
        pre remaining leftOfMarker with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [AppendCodeSymbolReturnToCurrentMarkerDescription,
    MachineDescription.encodeCodeWordAsInput] using hsteps

def ReturnToTransitionMarkerDescription :
    MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ MachineDescription.transition
        0 (some false) (some false) Direction.left 0
    , MachineDescription.transition
        0 (some true) (some true) Direction.left 0
    , MachineDescription.transition
        0 none (some false) Direction.left 1
    , MachineDescription.transition
        1 (some false) (some false) Direction.right 2
    , MachineDescription.transition
        1 (some true) (some true) Direction.right 2
    ]

 /-- {name}`returnToTransitionMarkerDescription_wellFormed` captures the core lemma for this local construction. -/
theorem returnToTransitionMarkerDescription_wellFormed :
    ReturnToTransitionMarkerDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · exact transition_wellFormed_of_all
      (l := ReturnToTransitionMarkerDescription.transitions)
      (stateCount :=
        ReturnToTransitionMarkerDescription.stateCount)
      (by
        native_decide)
  · exact transition_deterministic_of_all
      (l := ReturnToTransitionMarkerDescription.transitions)
      (by
        native_decide)

 /-- {name}`returnToTransitionMarkerDescription_haltTransitionFree` establishes the halting condition in this construction. -/
theorem returnToTransitionMarkerDescription_haltTransitionFree :
    ReturnToTransitionMarkerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ReturnToTransitionMarkerDescription.transitions)
    (state := ReturnToTransitionMarkerDescription.halt)
    (by
      native_decide)

 /-- {name}`returnToTransitionMarkerDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem returnToTransitionMarkerDescription_subroutineReady :
    ReturnToTransitionMarkerDescription.SubroutineReady :=
  ⟨returnToTransitionMarkerDescription_wellFormed,
    returnToTransitionMarkerDescription_haltTransitionFree⟩

 /-- {name}`returnToTransitionMarkerDescription_step_scan` characterizes a scan safety phase. -/
theorem returnToTransitionMarkerDescription_step_scan
    (preRev : Word Bool) (leftBit current : Bool)
    (right : List (Option Bool)) :
    ReturnToTransitionMarkerDescription.stepConfig
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
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft]

 /-- {name}`returnToTransitionMarkerDescription_run` captures the core lemma for this local construction. -/
theorem returnToTransitionMarkerDescription_run
    (preRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    ReturnToTransitionMarkerDescription.runConfig
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
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons b rest ih =>
      simp only [List.map_cons, List.length_cons, List.reverse_cons]
      rw [show Nat.succ rest.length + 3 = (rest.length + 3) + 1 by omega]
      rw [MachineDescription.runConfig]
      rw [returnToTransitionMarkerDescription_step_scan]
      simpa [List.append_assoc] using ih b (some current :: right)
     /-- {name}`returnToTransitionMarkerDescription_run_after_append_four_atCells` states the corresponding theorem run form. -/

theorem
    returnToTransitionMarkerDescription_run_after_append_four_atCells
    (pre : Word Bool) (b0 b1 b2 b3 : Bool) :
    ReturnToTransitionMarkerDescription.runConfig
        (pre.length + 5)
        { state := ReturnToTransitionMarkerDescription.start
          tape :=
            Tape.move Direction.left
              (appendRightLastTapeAtCells
                (List.append (pre.reverse.map some)
                  [none, some false]) b0 b1 b2 b3) } =
      { state := ReturnToTransitionMarkerDescription.halt
        tape :=
          tapeAtCells [some false]
            (some false ::
              ((List.append pre [b0, b1, b2, b3]).map some)) } := by
  simpa [appendRightLastTapeAtCells, tapeAtCells,
    Tape.move, Tape.moveLeft, List.append_assoc] using
    returnToTransitionMarkerDescription_run
      (List.append [b1, b0] pre.reverse) b2 [some b3]
     /-- {name}`returnToTransitionMarkerDescription_run_after_append_atCells` states the corresponding theorem run form. -/

theorem
    returnToTransitionMarkerDescription_run_after_append_atCells :
    forall code : Word MachineCodeSymbol,
      code ≠ [] ->
        forall pre : Word Bool,
          exists steps : Nat,
            ReturnToTransitionMarkerDescription.runConfig steps
                { state := ReturnToTransitionMarkerDescription.start
                  tape :=
                    Tape.move Direction.left
                      (appendCodeWordLastTapeAtCells
                        (List.append (pre.reverse.map some)
                          [none, some false])
                        code) } =
              { state := ReturnToTransitionMarkerDescription.halt
                tape :=
                  tapeAtCells [some false]
                    (some false ::
                      ((List.append pre
                        (MachineDescription.encodeCodeWordAsInput code)).map
                        some)) }
  | [], h => False.elim (h rfl)
  | symbol :: [], _ => by
      intro pre
      cases symbol <;>
        refine ⟨pre.length + 5, ?_⟩ <;>
        simpa [appendCodeWordLastTapeAtCells,
          appendCodeSymbolLastTapeAtCells,
          appendRightLastTapeAtCells,
          MachineDescription.encodeCodeSymbolAsInput,
          MachineDescription.encodeCodeWordAsInput,
          Tape.move, Tape.moveLeft, List.append_assoc] using
          returnToTransitionMarkerDescription_run_after_append_four_atCells
            pre _ _ _ _
  | symbol :: next :: rest, _ => by
      intro pre
      let symbolBits := MachineDescription.encodeCodeSymbolAsInput symbol
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
              (MachineDescription.encodeCodeWordAsInput (next :: rest)) =
            List.append pre
              (MachineDescription.encodeCodeWordAsInput
                (symbol :: next :: rest)) := by
        simp [symbolBits,
          MachineDescription.encodeCodeWordAsInput, List.append_assoc]
      simpa [appendCodeWordLastTapeAtCells, symbolBits,
        hleft, hbits, MachineDescription.encodeCodeWordAsInput,
        List.map_append, List.append_assoc] using hsteps

def MarkedPrefixAppendCodeWordReturnDescription
    (code : Word MachineCodeSymbol) : MachineDescription :=
  MachineDescription.seqSubroutine
    (MarkedPrefixThenAppendCodeWordLastDescription code)
    ReturnToTransitionMarkerDescription
    Direction.left
     /-- {name}`markedPrefixAppendCodeWordReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    markedPrefixAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (MarkedPrefixAppendCodeWordReturnDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (markedPrefixThenAppendCodeWordLastDescription_subroutineReady
      code hcode)
    returnToTransitionMarkerDescription_subroutineReady

 /-- {name}`markedPrefixAppendCodeWordReturnDescription_run` captures the core lemma for this local construction. -/
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
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := MarkedPrefixThenAppendCodeWordLastDescription code
  let B := ReturnToTransitionMarkerDescription
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
    simpa [A, Tmid, MachineDescription.initial] using hArunBase
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
                    (MachineDescription.encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        returnToTransitionMarkerDescription_run_after_append_atCells
          code hcode (false :: true :: b :: rest) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [MarkedPrefixAppendCodeWordReturnDescription,
    MachineDescription.initial, A, B] using hn

 /-- {name}`markedPrefixAppendCodeWordReturnDescription_run_checked` states the corresponding theorem run form. -/
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
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := MarkedPrefixThenAppendCodeWordLastDescription code
  let B := ReturnToTransitionMarkerDescription
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
                    (MachineDescription.encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        returnToTransitionMarkerDescription_run_after_append_atCells
          code hcode (false :: true :: b :: rest) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [MarkedPrefixAppendCodeWordReturnDescription,
    A, B] using hn

def MarkedPrefixAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  MarkedPrefixAppendCodeWordReturnDescription
    (MachineDescription.encodeNat n)
     /-- {name}`markedPrefixAppendNatReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    markedPrefixAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (MarkedPrefixAppendNatReturnDescription
      n).SubroutineReady :=
  markedPrefixAppendCodeWordReturnDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (encodeNat_ne_nil n)

 /-- {name}`markedPrefixAppendNatReturnDescription_run` captures the core lemma for this local construction. -/
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
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNat n))).map some)) } := by
  simpa [MarkedPrefixAppendNatReturnDescription] using
    markedPrefixAppendCodeWordReturnDescription_run
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      b rest

 /-- {name}`markedPrefixAppendNatReturnDescription_run_checked` states the corresponding theorem run form. -/
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
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNat n))).map some)) } := by
  simpa [MarkedPrefixAppendNatReturnDescription] using
    markedPrefixAppendCodeWordReturnDescription_run_checked
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      b rest

 /-- {name}`stageInputBits_exists_cons` provides the witness needed for existential progress. -/
theorem stageInputBits_exists_cons
    (w : Word Bool) (stage : Nat) :
    exists b : Bool,
    exists rest : Word Bool,
      MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w stage) =
        b :: rest := by
  have hne :
      MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w stage) ≠ [] := by
    cases w <;>
      simp [PairedRecognizerDovetailStageInputCode,
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCodeWordAsInput,
        MachineDescription.encodeCodeSymbolAsInput]
  cases hbits :
      MachineDescription.encodeCodeWordAsInput
        (PairedRecognizerDovetailStageInputCode w stage) with
  | nil =>
      exact False.elim (hne hbits)
  | cons b rest =>
      exact ⟨b, rest, rfl⟩
     /-- {name}`markedPrefixAppendCodeWordReturnDescription_run_stageInput` states the corresponding theorem run form. -/

theorem
    markedPrefixAppendCodeWordReturnDescription_run_stageInput
    (code : Word MachineCodeSymbol) (hcode : code ≠ [])
    (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (MarkedPrefixAppendCodeWordReturnDescription code).runConfig steps
          ((MarkedPrefixAppendCodeWordReturnDescription
            code).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (MarkedPrefixAppendCodeWordReturnDescription code).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (MachineDescription.encodeCodeWordAsInput code))).map
                  some)) } := by
  rcases stageInputBits_exists_cons w stage with
    ⟨b, rest, hbits⟩
  rcases
      markedPrefixAppendCodeWordReturnDescription_run
        code hcode b rest with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [hbits, MachineDescription.initial, List.append_assoc] using hsteps

 /-- {name}`markedPrefixAppendNatReturnDescription_run_stageInput` states the corresponding theorem run form. -/
theorem markedPrefixAppendNatReturnDescription_run_stageInput
    (n : Nat) (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (MarkedPrefixAppendNatReturnDescription n).runConfig steps
          ((MarkedPrefixAppendNatReturnDescription
            n).initial
            (MachineDescription.encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w stage))) =
        { state :=
            (MarkedPrefixAppendNatReturnDescription n).halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((List.append [false, true]
                  (List.append
                    (MachineDescription.encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (MachineDescription.encodeCodeWordAsInput
                      (MachineDescription.encodeNat n)))).map some)) } := by
  simpa [MarkedPrefixAppendNatReturnDescription] using
    markedPrefixAppendCodeWordReturnDescription_run_stageInput
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      w stage

 /-- {name}`markedPrefixAppendNatReturnDescription_run_stageInput_checked` states the corresponding theorem run form. -/
theorem markedPrefixAppendNatReturnDescription_run_stageInput_checked
    (n : Nat) (w : Word Bool) (stage : Nat) :
    exists steps : Nat,
      (MarkedPrefixAppendNatReturnDescription n).runConfig steps
          { state :=
              (MarkedPrefixAppendNatReturnDescription n).start
            tape :=
              tapeAtCells []
                (List.append
                  ((MachineDescription.encodeCodeWordAsInput
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
                    (MachineDescription.encodeCodeWordAsInput
                      (PairedRecognizerDovetailStageInputCode w stage))
                    (MachineDescription.encodeCodeWordAsInput
                      (MachineDescription.encodeNat n)))).map some)) } := by
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
  MachineDescription.seqSubroutine
    (TransitionPrefixedThenAppendCodeWordLastDescription code)
    ReturnToTransitionMarkerDescription
    Direction.left
     /-- {name}`transitionPrefixedAppendCodeWordReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (TransitionPrefixedAppendCodeWordReturnDescription
      code).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    (transitionPrefixedThenAppendCodeWordLastDescription_subroutineReady
      code hcode)
    returnToTransitionMarkerDescription_subroutineReady

 /-- {name}`transitionPrefixedAppendCodeWordReturnDescription_run` captures the core lemma for this local construction. -/
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
                  (MachineDescription.encodeCodeWordAsInput code)).map
                  some)) } := by
  let A := TransitionPrefixedThenAppendCodeWordLastDescription code
  let B := ReturnToTransitionMarkerDescription
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
                    (MachineDescription.encodeCodeWordAsInput code)).map
                    some)) } := by
    rcases
        returnToTransitionMarkerDescription_run_after_append_atCells
          code hcode (false :: true :: payload) with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    simpa [B, Tmid] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.left)
        hAready hBready hArun hBReach with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [TransitionPrefixedAppendCodeWordReturnDescription,
    A, B] using hn

def TransitionPrefixedAppendNatReturnDescription
    (n : Nat) : MachineDescription :=
  TransitionPrefixedAppendCodeWordReturnDescription
    (MachineDescription.encodeNat n)
     /-- {name}`transitionPrefixedAppendNatReturnDescription_subroutineReady` packages a subroutine-ready composition step. -/

theorem
    transitionPrefixedAppendNatReturnDescription_subroutineReady
    (n : Nat) :
    (TransitionPrefixedAppendNatReturnDescription
      n).SubroutineReady :=
  transitionPrefixedAppendCodeWordReturnDescription_subroutineReady
    (MachineDescription.encodeNat n)
    (encodeNat_ne_nil n)

 /-- {name}`transitionPrefixedAppendNatReturnDescription_run` captures the core lemma for this local construction. -/
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
                  (MachineDescription.encodeCodeWordAsInput
                    (MachineDescription.encodeNat n))).map some)) } := by
  simpa [TransitionPrefixedAppendNatReturnDescription] using
    transitionPrefixedAppendCodeWordReturnDescription_run
      (MachineDescription.encodeNat n)
      (encodeNat_ne_nil n)
      payload


end DovetailInitialLayoutInitializer
end Computability
end FoC
