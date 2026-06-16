import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.ReturnAppend

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

def RightCellsCopierStartHandoffDescription :
    MachineDescription where
  stateCount := 8
  start := 0
  halt := 7
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
    ]

theorem rightCellsCopierStartHandoffDescription_wellFormed :
    RightCellsCopierStartHandoffDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := RightCellsCopierStartHandoffDescription.transitions)
      (stateCount :=
        RightCellsCopierStartHandoffDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := RightCellsCopierStartHandoffDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem
    rightCellsCopierStartHandoffDescription_haltTransitionFree :
    RightCellsCopierStartHandoffDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := RightCellsCopierStartHandoffDescription.transitions)
    (state := RightCellsCopierStartHandoffDescription.halt)
    (by
      native_decide) t ht

theorem
    rightCellsCopierStartHandoffDescription_subroutineReady :
    RightCellsCopierStartHandoffDescription.SubroutineReady :=
  ⟨rightCellsCopierStartHandoffDescription_wellFormed,
    rightCellsCopierStartHandoffDescription_haltTransitionFree⟩

theorem rightCellsCopierStartHandoffDescription_run
    (tail : List (Option Bool)) :
    RightCellsCopierStartHandoffDescription.runConfig 7
        (config 0 []
          (List.append
            [some false, some false, some false, some true,
              some false, some false, some true, some false]
            tail)) =
      config 7
        [some true, some false, some false, some true, some false, none,
          some false]
        (some false :: tail) := by
  cases tail <;>
    simp [RightCellsCopierStartHandoffDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]
def inputTapeRightCellsDirectCopierTickBits (n : Nat) :
    Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (List.replicate n MachineCodeSymbol.tick)

@[simp] theorem
    inputTapeRightCellsDirectCopierTickBits_zero :
    inputTapeRightCellsDirectCopierTickBits 0 = [] := by
  rfl

@[simp] theorem
    inputTapeRightCellsDirectCopierTickBits_succ
    (n : Nat) :
    inputTapeRightCellsDirectCopierTickBits (n + 1) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.tick)
        (inputTapeRightCellsDirectCopierTickBits n) := by
  simp [inputTapeRightCellsDirectCopierTickBits,
    MachineDescription.encodeCodeWordAsInput, List.replicate_succ]

theorem
    inputTapeRightCellsDirectCopierDescription_run_copy_ticks
    (n : Nat) (leftOfMarker : List (Option Bool))
    (pre sourceTail output : Word Bool) :
    exists steps : Nat,
      InputTapeRightCellsDirectCopierDescription.runConfig steps
          (config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (inputTapeRightCellsDirectCopierTickBits n)
              (List.append sourceTail output)).map some)) =
        config 0
          (List.append
            ((inputTapeRightCellsDirectCopierTickBits n).reverse.map
              some)
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker)))
          ((List.append sourceTail
            (List.append output
              (inputTapeRightCellsDirectCopierTickBits n))).map some) := by
  induction n generalizing pre output with
  | zero =>
      refine ⟨0, ?_⟩
      simp [MachineDescription.runConfig, List.map_append]
  | succ n ih =>
      let tickBits :=
        MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.tick
      rcases
          inputTapeRightCellsDirectCopierDescription_run_copy_tick
            leftOfMarker pre
            (List.append
              (inputTapeRightCellsDirectCopierTickBits n)
              (List.append sourceTail output)) with
        ⟨tickSteps, htick⟩
      rcases ih (List.append pre tickBits)
          (List.append output tickBits) with
        ⟨restSteps, hrest⟩
      refine ⟨tickSteps + restSteps, ?_⟩
      rw [MachineDescription.runConfig_add]
      rw [show
          config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (inputTapeRightCellsDirectCopierTickBits (n + 1))
              (List.append sourceTail output)).map some) =
          config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.tick)
              (List.append
                (inputTapeRightCellsDirectCopierTickBits n)
                (List.append sourceTail output))).map some) by
          simp]
      rw [htick]
      rw [show
          config 0
            (List.append
              ((MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.tick).reverse.map some)
              (List.append (pre.reverse.map some)
                (none :: leftOfMarker)))
            (((List.append
              (inputTapeRightCellsDirectCopierTickBits n)
              (List.append sourceTail output)).append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.tick)).map some) =
          config 0
            (List.append ((List.append pre tickBits).reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (inputTapeRightCellsDirectCopierTickBits n)
              (List.append sourceTail
                (List.append output tickBits))).map some) by
          simp [tickBits, List.reverse_append, List.map_append,
            List.append_assoc]]
      have hstart :
          config 0
            (List.append
              ((inputTapeRightCellsDirectCopierTickBits n).reverse.map
                some)
              (List.append ((List.append pre tickBits).reverse.map some)
                (none :: leftOfMarker)))
            ((List.append sourceTail
              (List.append (List.append output tickBits)
                (inputTapeRightCellsDirectCopierTickBits n))).map some) =
          config 0
            (List.append
              ((inputTapeRightCellsDirectCopierTickBits (n + 1)).reverse.map
                some)
              (List.append (pre.reverse.map some)
                (none :: leftOfMarker)))
            ((List.append sourceTail
              (List.append output
                (inputTapeRightCellsDirectCopierTickBits (n + 1)))).map
                some) := by
        simp [tickBits, List.reverse_append, List.map_append,
          List.append_assoc]
      exact hrest.trans hstart

theorem
    inputTapeRightCellsDirectCopierDescription_step_scan30
    (leftRev : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 30 leftRev (some bit :: rest.map some)) =
      some (config 30 (some bit :: leftRev)
        (rest.map some)) := by
  cases bit <;> cases rest <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_run_scan30
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        remaining.length
        (config 30 leftRev (remaining.map some)) =
      config 30
        (List.append (remaining.reverse.map some) leftRev) [] := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig, config,
        tapeAtCells]
  | cons bit rest ih =>
      simp [MachineDescription.runConfig,
        inputTapeRightCellsDirectCopierDescription_step_scan30,
        ih, List.append_assoc]

theorem
    inputTapeRightCellsDirectCopierDescription_run_write_done
    (leftRev : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig 4
        (config 30 leftRev []) =
      config 34
        (List.append [some false, some false] leftRev)
        [some true, some true] := by
  simp [InputTapeRightCellsDirectCopierDescription,
    config, tapeAtCells,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_step_return34
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (leftBit current : Bool) (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 34
          (List.append (some leftBit :: preRev.map some)
            (none :: leftOfMarker))
          (some current :: right)) =
      some (config 34
        (List.append (preRev.map some) (none :: leftOfMarker))
        (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, MachineDescription.transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

theorem
    inputTapeRightCellsDirectCopierDescription_run_return34
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (current : Bool) (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        (preRev.length + 2)
        (config 34
          (List.append (preRev.map some) (none :: leftOfMarker))
          (some current :: right)) =
      config 35 (some false :: leftOfMarker)
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
      rw [inputTapeRightCellsDirectCopierDescription_step_return34]
      simpa [List.append_assoc] using ih bit (some current :: right)

theorem
    inputTapeRightCellsDirectCopierDescription_step_advance35
    (leftRev : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 35 leftRev (some bit :: right)) =
      some (config 36 (some bit :: leftRev) right) := by
  cases bit <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_step_advance36
    (leftRev : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 36 leftRev (some bit :: right)) =
      some (config 37 (some bit :: leftRev) right) := by
  cases bit <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_step_advance37
    (leftRev : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 37 leftRev (some bit :: right)) =
      some (config 38 (some bit :: leftRev) right) := by
  cases bit <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_step_advance38
    (leftRev : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 38 leftRev (some bit :: right)) =
      some (config 39 (some bit :: leftRev) right) := by
  cases bit <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_step_advance39
    (leftRev : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 39 leftRev (some bit :: right)) =
      some (config 40 (some bit :: leftRev) right) := by
  cases bit <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_step_advance40
    (leftRev : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 40 leftRev (some bit :: right)) =
      some (config 41 (some bit :: leftRev) right) := by
  cases bit <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_step_advance41
    (leftRev : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 41 leftRev (some bit :: right)) =
      some (config 10 (some bit :: leftRev) right) := by
  cases bit <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_run_advance35_to10
    (leftRev : List (Option Bool)) (b1 b2 b3 b4 b5 b6 b7 : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig 7
        (config 35 leftRev
          (some b1 :: some b2 :: some b3 :: some b4 :: some b5 ::
            some b6 :: some b7 :: right)) =
      config 10
        (some b7 :: some b6 :: some b5 :: some b4 :: some b3 ::
          some b2 :: some b1 :: leftRev)
        right := by
  simp only [MachineDescription.runConfig.eq_def]
  rw [inputTapeRightCellsDirectCopierDescription_step_advance35]
  simp only
  rw [inputTapeRightCellsDirectCopierDescription_step_advance36]
  simp only
  rw [inputTapeRightCellsDirectCopierDescription_step_advance37]
  simp only
  rw [inputTapeRightCellsDirectCopierDescription_step_advance38]
  simp only
  rw [inputTapeRightCellsDirectCopierDescription_step_advance39]
  simp only
  rw [inputTapeRightCellsDirectCopierDescription_step_advance40]
  simp only
  rw [inputTapeRightCellsDirectCopierDescription_step_advance41]

theorem
    inputTapeRightCellsDirectCopierDescription_run_copy_done_skip_four
    (leftOfMarker : List (Option Bool))
    (pre sourceTail output : Word Bool)
    (h0 h1 h2 h3 : Bool) :
    exists steps : Nat,
      InputTapeRightCellsDirectCopierDescription.runConfig steps
          (config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.done)
              (List.append [h0, h1, h2, h3]
                (List.append sourceTail output))).map some)) =
        config 10
          (List.append
            ((List.append pre
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput
                  MachineCodeSymbol.done)
                [h0, h1, h2, h3])).reverse.map some)
            (none :: leftOfMarker))
          ((List.append sourceTail
            (List.append output
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.done))).map some) := by
  let doneBits :=
    MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.done
  let headBits : Word Bool := [h0, h1, h2, h3]
  let remaining : Word Bool :=
    List.append headBits (List.append sourceTail output)
  let afterPrefixLeft : List (Option Bool) :=
    List.append [some true, some true, some false, none]
      (List.append (pre.reverse.map some) (none :: leftOfMarker))
  let returnPre : Word Bool :=
    List.append [false, false]
      (List.append remaining.reverse [true, true, false])
  let returnLeft : List (Option Bool) :=
    List.append (pre.reverse.map some) (none :: leftOfMarker)
  have hprefix :
      InputTapeRightCellsDirectCopierDescription.runConfig 4
          (config 0
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append doneBits remaining).map some)) =
        config 30 afterPrefixLeft (remaining.map some) := by
    simp [doneBits, remaining, afterPrefixLeft,
      InputTapeRightCellsDirectCopierDescription,
      MachineDescription.encodeCodeSymbolAsInput,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight, List.map_reverse]
    cases List.map some remaining <;> rfl
  refine
    ⟨4 + (remaining.length + (4 + ((returnPre.length + 2) + 7))), ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [show
      config 0
        (List.append (pre.reverse.map some) (none :: leftOfMarker))
        ((List.append
          (MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.done)
          (List.append [h0, h1, h2, h3]
            (List.append sourceTail output))).map some) =
      config 0
        (List.append (pre.reverse.map some) (none :: leftOfMarker))
        ((List.append doneBits remaining).map some) by
      simp [doneBits, remaining, headBits]]
  rw [hprefix]
  rw [MachineDescription.runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_scan30]
  rw [MachineDescription.runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_write_done]
  rw [MachineDescription.runConfig_add]
  have hleft :
      List.append [some false, some false]
          (List.append (remaining.reverse.map some) afterPrefixLeft) =
        List.append (returnPre.map some) (none :: returnLeft) := by
    simp [afterPrefixLeft, returnPre, returnLeft,
      List.map_append, List.append_assoc]
  rw [show
      config 34
        (List.append [some false, some false]
          (List.append (remaining.reverse.map some) afterPrefixLeft))
        [some true, some true] =
      config 34
        (List.append (returnPre.map some) (none :: returnLeft))
        (some true :: [some true]) by
        simpa [List.map_reverse] using
          congrArg
            (fun left =>
              config 34 left [some true, some true])
            hleft]
  rw [inputTapeRightCellsDirectCopierDescription_run_return34]
  rw [show
      config 35 (some false :: returnLeft)
        (List.append (returnPre.reverse.map some) [some true, some true]) =
      config 35 (some false :: returnLeft)
        (some false :: some true :: some true :: some h0 :: some h1 ::
          some h2 :: some h3 ::
          ((List.append sourceTail
            (List.append output doneBits)).map some)) by
        simp [returnPre, remaining, headBits, doneBits,
          MachineDescription.encodeCodeSymbolAsInput, List.map_append,
          List.reverse_append, List.append_assoc]]
  rw [inputTapeRightCellsDirectCopierDescription_run_advance35_to10]
  simp [returnLeft, doneBits,
    MachineDescription.encodeCodeSymbolAsInput, List.map_append,
    List.reverse_append]

theorem
    inputTapeRightCellsDirectCopierDescription_step_scan60
    (leftRev : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 60 leftRev (some bit :: rest.map some)) =
      some (config 60 (some bit :: leftRev)
        (rest.map some)) := by
  cases bit <;> cases rest <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_run_scan60
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        remaining.length
        (config 60 leftRev (remaining.map some)) =
      config 60
        (List.append (remaining.reverse.map some) leftRev) [] := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig, config,
        tapeAtCells]
  | cons bit rest ih =>
      simp [MachineDescription.runConfig,
        inputTapeRightCellsDirectCopierDescription_step_scan60,
        ih, List.append_assoc]

theorem
    inputTapeRightCellsDirectCopierDescription_run_write_zero
    (leftRev : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig 4
        (config 60 leftRev []) =
      config 64
        (List.append [some true, some false] leftRev)
        [some false, some true] := by
  simp [InputTapeRightCellsDirectCopierDescription,
    config, tapeAtCells,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_step_return64
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (leftBit current : Bool) (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 64
          (List.append (some leftBit :: preRev.map some)
            (none :: leftOfMarker))
          (some current :: right)) =
      some (config 64
        (List.append (preRev.map some) (none :: leftOfMarker))
        (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, MachineDescription.transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

theorem
    inputTapeRightCellsDirectCopierDescription_run_return64
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (current : Bool) (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        (preRev.length + 2)
        (config 64
          (List.append (preRev.map some) (none :: leftOfMarker))
          (some current :: right)) =
      config 65 (some false :: leftOfMarker)
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
      rw [inputTapeRightCellsDirectCopierDescription_step_return64]
      simpa [List.append_assoc] using ih bit (some current :: right)

theorem
    inputTapeRightCellsDirectCopierDescription_run_advance65_to10
    (leftRev : List (Option Bool)) (b1 b2 b3 : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig 3
        (config 65 leftRev
          (some b1 :: some b2 :: some b3 :: right)) =
      config 10
        (some b3 :: some b2 :: some b1 :: leftRev) right := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_run_copy_zero_cell
    (leftOfMarker : List (Option Bool))
    (pre sourceTail output : Word Bool) :
    exists steps : Nat,
      InputTapeRightCellsDirectCopierDescription.runConfig steps
          (config 10
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.zero)
              (List.append sourceTail output)).map some)) =
        config 10
          (List.append
            ((List.append pre
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.zero)).reverse.map some)
            (none :: leftOfMarker))
          ((List.append sourceTail
            (List.append output
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.zero))).map some) := by
  let zeroBits :=
    MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.zero
  let remaining : Word Bool := List.append sourceTail output
  let afterPrefixLeft : List (Option Bool) :=
    List.append [some true, some false, some true, none]
      (List.append (pre.reverse.map some) (none :: leftOfMarker))
  let returnPre : Word Bool :=
    List.append [true, false]
      (List.append remaining.reverse [true, false, true])
  let returnLeft : List (Option Bool) :=
    List.append (pre.reverse.map some) (none :: leftOfMarker)
  have hprefix :
      InputTapeRightCellsDirectCopierDescription.runConfig 6
          (config 10
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append zeroBits remaining).map some)) =
        config 60 afterPrefixLeft (remaining.map some) := by
    simp [zeroBits, remaining, afterPrefixLeft,
      InputTapeRightCellsDirectCopierDescription,
      MachineDescription.encodeCodeSymbolAsInput,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.map_reverse]
    cases List.map some sourceTail ++ List.map some output <;> simp
  refine
    ⟨6 + (remaining.length + (4 + ((returnPre.length + 2) + 3))), ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [show
      config 10
        (List.append (pre.reverse.map some) (none :: leftOfMarker))
        ((List.append
          (MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.zero)
          (List.append sourceTail output)).map some) =
      config 10
        (List.append (pre.reverse.map some) (none :: leftOfMarker))
        ((List.append zeroBits remaining).map some) by
      simp [zeroBits, remaining]]
  rw [hprefix]
  rw [MachineDescription.runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_scan60]
  rw [MachineDescription.runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_write_zero]
  rw [MachineDescription.runConfig_add]
  have hleft :
      List.append [some true, some false]
          (List.append (remaining.reverse.map some) afterPrefixLeft) =
        List.append (returnPre.map some) (none :: returnLeft) := by
    simp [afterPrefixLeft, returnPre, returnLeft,
      List.map_append, List.append_assoc]
  rw [show
      config 64
        (List.append [some true, some false]
          (List.append (remaining.reverse.map some) afterPrefixLeft))
        [some false, some true] =
      config 64
        (List.append (returnPre.map some) (none :: returnLeft))
        (some false :: [some true]) by
        simpa [List.map_reverse] using
          congrArg
            (fun left =>
              config 64 left [some false, some true])
            hleft]
  rw [inputTapeRightCellsDirectCopierDescription_run_return64]
  rw [show
      config 65 (some false :: returnLeft)
        (List.append (returnPre.reverse.map some) [some false, some true]) =
      config 65 (some false :: returnLeft)
        (some true :: some false :: some true ::
          ((List.append sourceTail
            (List.append output zeroBits)).map some)) by
        simp [returnPre, remaining, zeroBits,
          MachineDescription.encodeCodeSymbolAsInput, List.map_append,
          List.reverse_append, List.append_assoc]]
  rw [inputTapeRightCellsDirectCopierDescription_run_advance65_to10]
  simp [returnLeft, zeroBits,
    MachineDescription.encodeCodeSymbolAsInput, List.map_append,
    List.reverse_append]

theorem
    inputTapeRightCellsDirectCopierDescription_step_scan70
    (leftRev : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 70 leftRev (some bit :: rest.map some)) =
      some (config 70 (some bit :: leftRev)
        (rest.map some)) := by
  cases bit <;> cases rest <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_run_scan70
    (leftRev : List (Option Bool)) (remaining : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        remaining.length
        (config 70 leftRev (remaining.map some)) =
      config 70
        (List.append (remaining.reverse.map some) leftRev) [] := by
  induction remaining generalizing leftRev with
  | nil =>
      simp [MachineDescription.runConfig, config,
        tapeAtCells]
  | cons bit rest ih =>
      simp [MachineDescription.runConfig,
        inputTapeRightCellsDirectCopierDescription_step_scan70,
        ih, List.append_assoc]

theorem
    inputTapeRightCellsDirectCopierDescription_run_write_one
    (leftRev : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig 4
        (config 70 leftRev []) =
      config 74
        (List.append [some true, some false] leftRev)
        [some true, some false] := by
  simp [InputTapeRightCellsDirectCopierDescription,
    config, tapeAtCells,
    MachineDescription.runConfig, MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_step_return74
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (leftBit current : Bool) (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 74
          (List.append (some leftBit :: preRev.map some)
            (none :: leftOfMarker))
          (some current :: right)) =
      some (config 74
        (List.append (preRev.map some) (none :: leftOfMarker))
        (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, MachineDescription.transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

theorem
    inputTapeRightCellsDirectCopierDescription_run_return74
    (preRev : Word Bool) (leftOfMarker : List (Option Bool))
    (current : Bool) (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        (preRev.length + 2)
        (config 74
          (List.append (preRev.map some) (none :: leftOfMarker))
          (some current :: right)) =
      config 75 (some false :: leftOfMarker)
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
      rw [inputTapeRightCellsDirectCopierDescription_step_return74]
      simpa [List.append_assoc] using ih bit (some current :: right)

theorem
    inputTapeRightCellsDirectCopierDescription_run_advance75_to10
    (leftRev : List (Option Bool)) (b1 b2 b3 : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig 3
        (config 75 leftRev
          (some b1 :: some b2 :: some b3 :: right)) =
      config 10
        (some b3 :: some b2 :: some b1 :: leftRev) right := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem
    inputTapeRightCellsDirectCopierDescription_run_copy_one_cell
    (leftOfMarker : List (Option Bool))
    (pre sourceTail output : Word Bool) :
    exists steps : Nat,
      InputTapeRightCellsDirectCopierDescription.runConfig steps
          (config 10
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.one)
              (List.append sourceTail output)).map some)) =
        config 10
          (List.append
            ((List.append pre
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.one)).reverse.map some)
            (none :: leftOfMarker))
          ((List.append sourceTail
            (List.append output
              (MachineDescription.encodeCodeSymbolAsInput
                MachineCodeSymbol.one))).map some) := by
  let oneBits :=
    MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.one
  let remaining : Word Bool := List.append sourceTail output
  let afterPrefixLeft : List (Option Bool) :=
    List.append [some false, some true, some true, none]
      (List.append (pre.reverse.map some) (none :: leftOfMarker))
  let returnPre : Word Bool :=
    List.append [true, false]
      (List.append remaining.reverse [false, true, true])
  let returnLeft : List (Option Bool) :=
    List.append (pre.reverse.map some) (none :: leftOfMarker)
  have hprefix :
      InputTapeRightCellsDirectCopierDescription.runConfig 6
          (config 10
            (List.append (pre.reverse.map some)
              (none :: leftOfMarker))
            ((List.append oneBits remaining).map some)) =
        config 70 afterPrefixLeft (remaining.map some) := by
    simp [oneBits, remaining, afterPrefixLeft,
      InputTapeRightCellsDirectCopierDescription,
      MachineDescription.encodeCodeSymbolAsInput,
      config, tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.map_reverse]
    cases List.map some sourceTail ++ List.map some output <;> simp
  refine
    ⟨6 + (remaining.length + (4 + ((returnPre.length + 2) + 3))), ?_⟩
  rw [MachineDescription.runConfig_add]
  rw [show
      config 10
        (List.append (pre.reverse.map some) (none :: leftOfMarker))
        ((List.append
          (MachineDescription.encodeCodeSymbolAsInput
            MachineCodeSymbol.one)
          (List.append sourceTail output)).map some) =
      config 10
        (List.append (pre.reverse.map some) (none :: leftOfMarker))
        ((List.append oneBits remaining).map some) by
      simp [oneBits, remaining]]
  rw [hprefix]
  rw [MachineDescription.runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_scan70]
  rw [MachineDescription.runConfig_add]
  rw [inputTapeRightCellsDirectCopierDescription_run_write_one]
  rw [MachineDescription.runConfig_add]
  have hleft :
      List.append [some true, some false]
          (List.append (remaining.reverse.map some) afterPrefixLeft) =
        List.append (returnPre.map some) (none :: returnLeft) := by
    simp [afterPrefixLeft, returnPre, returnLeft,
      List.map_append, List.append_assoc]
  rw [show
      config 74
        (List.append [some true, some false]
          (List.append (remaining.reverse.map some) afterPrefixLeft))
        [some true, some false] =
      config 74
        (List.append (returnPre.map some) (none :: returnLeft))
        (some true :: [some false]) by
        simpa [List.map_reverse] using
          congrArg
            (fun left =>
              config 74 left [some true, some false])
            hleft]
  rw [inputTapeRightCellsDirectCopierDescription_run_return74]
  rw [show
      config 75 (some false :: returnLeft)
        (List.append (returnPre.reverse.map some) [some true, some false]) =
      config 75 (some false :: returnLeft)
        (some true :: some true :: some false ::
          ((List.append sourceTail
            (List.append output oneBits)).map some)) by
        simp [returnPre, remaining, oneBits,
          MachineDescription.encodeCodeSymbolAsInput, List.map_append,
          List.reverse_append, List.append_assoc]]
  rw [inputTapeRightCellsDirectCopierDescription_run_advance75_to10]
  simp [returnLeft, oneBits,
    MachineDescription.encodeCodeSymbolAsInput, List.map_append,
    List.reverse_append]

theorem
    inputTapeRightCellsDirectCopierDescription_step_return80
    (preRev : Word Bool) (leftBit current : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.stepConfig
        (config 80
          (List.append (some leftBit :: preRev.map some)
            [none, some false])
          (some current :: right)) =
      some (config 80
        (List.append (preRev.map some) [none, some false])
        (some leftBit :: some current :: right)) := by
  cases leftBit <;> cases current <;> cases right <;>
    simp [InputTapeRightCellsDirectCopierDescription,
      config, tapeAtCells,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, MachineDescription.transition, Tape.read,
      Tape.write, Tape.move, Tape.moveLeft]

theorem
    inputTapeRightCellsDirectCopierDescription_run_return80_to99
    (preRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        (preRev.length + 3)
        (config 80
          (List.append (preRev.map some) [none, some false])
          (some current :: right)) =
      config 99 [some false]
        (some false ::
          List.append (preRev.reverse.map some)
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
      rw [show rest.length + 1 + 3 = (rest.length + 3) + 1 by
        omega]
      rw [MachineDescription.runConfig]
      rw [inputTapeRightCellsDirectCopierDescription_step_return80]
      simpa [List.append_assoc] using ih bit (some current :: right)

theorem
    inputTapeRightCellsDirectCopierDescription_run_stop_at_nat_prefix
    (pre tail : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        (pre.length + 5)
        (config 10
          (List.append (pre.reverse.map some) [none, some false])
          ((false :: false :: tail).map some)) =
      config 99 [some false]
        (some false ::
          ((List.append pre (false :: false :: tail)).map some)) := by
  rw [show pre.length + 5 = 2 + (pre.reverse.length + 3) by
    simp
    omega]
  rw [MachineDescription.runConfig_add]
  have hprefix :
      InputTapeRightCellsDirectCopierDescription.runConfig 2
          (config 10
            (List.append (pre.reverse.map some) [none, some false])
            ((false :: false :: tail).map some)) =
        config 80
          (List.append (pre.reverse.map some) [none, some false])
          (some false :: some false :: tail.map some) := by
    cases tail <;>
      simp [InputTapeRightCellsDirectCopierDescription,
        config, tapeAtCells,
        MachineDescription.runConfig, MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write, Tape.move,
        Tape.moveLeft, Tape.moveRight]
  rw [hprefix]
  rw [inputTapeRightCellsDirectCopierDescription_run_return80_to99]
  simp [List.map_append]

def inputTapeRightCellsDirectCopierCellBits
    (cells : Word Bool) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.encodeCellsAppend (cells.map some) [])

@[simp] theorem
    inputTapeRightCellsDirectCopierCellBits_nil :
    inputTapeRightCellsDirectCopierCellBits [] = [] := by
  rfl

@[simp] theorem
    inputTapeRightCellsDirectCopierCellBits_cons_false
    (rest : Word Bool) :
    inputTapeRightCellsDirectCopierCellBits (false :: rest) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.zero)
        (inputTapeRightCellsDirectCopierCellBits rest) := by
  change
    MachineDescription.encodeCodeWordAsInput
        (List.append [MachineCodeSymbol.zero]
          (MachineDescription.encodeCellsAppend (rest.map some) [])) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.zero)
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellsAppend (rest.map some) []))
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

@[simp] theorem
    inputTapeRightCellsDirectCopierCellBits_cons_true
    (rest : Word Bool) :
    inputTapeRightCellsDirectCopierCellBits (true :: rest) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.one)
        (inputTapeRightCellsDirectCopierCellBits rest) := by
  change
    MachineDescription.encodeCodeWordAsInput
        (List.append [MachineCodeSymbol.one]
          (MachineDescription.encodeCellsAppend (rest.map some) [])) =
      List.append
        (MachineDescription.encodeCodeSymbolAsInput
          MachineCodeSymbol.one)
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeCellsAppend (rest.map some) []))
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

theorem
    inputTapeRightCellsDirectCopierDescription_run_copy_cells
    (cells : Word Bool) (pre sourceTail output : Word Bool) :
    exists steps : Nat,
      InputTapeRightCellsDirectCopierDescription.runConfig steps
          (config 10
            (List.append (pre.reverse.map some) [none, some false])
            ((List.append
              (inputTapeRightCellsDirectCopierCellBits cells)
              (List.append sourceTail output)).map some)) =
        config 10
          (List.append
            ((List.append pre
              (inputTapeRightCellsDirectCopierCellBits cells)).reverse.map
                some)
            [none, some false])
          ((List.append sourceTail
            (List.append output
              (inputTapeRightCellsDirectCopierCellBits cells))).map
            some) := by
  induction cells generalizing pre output with
  | nil =>
      refine ⟨0, ?_⟩
      simp [MachineDescription.runConfig, List.map_append]
  | cons cell rest ih =>
      cases cell
      · let cellBits :=
          MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.zero
        rcases
            inputTapeRightCellsDirectCopierDescription_run_copy_zero_cell
              [some false] pre
              (List.append
                (inputTapeRightCellsDirectCopierCellBits rest)
                sourceTail)
              output with
          ⟨cellSteps, hcell⟩
        rcases ih (List.append pre cellBits)
            (List.append output cellBits) with
          ⟨restSteps, hrest⟩
        refine ⟨cellSteps + restSteps, ?_⟩
        rw [MachineDescription.runConfig_add]
        rw [show
            config 10
              (List.append (pre.reverse.map some) [none, some false])
              ((List.append
                (inputTapeRightCellsDirectCopierCellBits (false :: rest))
                (List.append sourceTail output)).map some) =
            config 10
              (List.append (pre.reverse.map some) [none, some false])
              ((List.append cellBits
                (List.append
                  (List.append
                    (inputTapeRightCellsDirectCopierCellBits rest)
                    sourceTail)
                  output)).map some) by
            simp [cellBits, List.append_assoc]]
        rw [hcell]
        rw [show
            config 10
              (List.append ((List.append pre cellBits).reverse.map some)
                [none, some false])
              ((List.append
                (List.append
                  (inputTapeRightCellsDirectCopierCellBits rest)
                  sourceTail)
                (List.append output cellBits)).map some) =
            config 10
              (List.append ((List.append pre cellBits).reverse.map some)
                [none, some false])
              ((List.append
                (inputTapeRightCellsDirectCopierCellBits rest)
                (List.append sourceTail
                  (List.append output cellBits))).map some) by
            simp [List.append_assoc]]
        have hfinish :
            config 10
              (List.append
                ((List.append (List.append pre cellBits)
                  (inputTapeRightCellsDirectCopierCellBits rest)).reverse.map
                    some)
                [none, some false])
              ((List.append sourceTail
                (List.append (List.append output cellBits)
                  (inputTapeRightCellsDirectCopierCellBits rest))).map
                some) =
            config 10
              (List.append
                ((List.append pre
                  (inputTapeRightCellsDirectCopierCellBits
                    (false :: rest))).reverse.map some)
                [none, some false])
              ((List.append sourceTail
                (List.append output
                  (inputTapeRightCellsDirectCopierCellBits
                    (false :: rest)))).map some) := by
          simp [cellBits, List.reverse_append, List.map_append,
            List.append_assoc]
        exact hrest.trans hfinish
      · let cellBits :=
          MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.one
        rcases
            inputTapeRightCellsDirectCopierDescription_run_copy_one_cell
              [some false] pre
              (List.append
                (inputTapeRightCellsDirectCopierCellBits rest)
                sourceTail)
              output with
          ⟨cellSteps, hcell⟩
        rcases ih (List.append pre cellBits)
            (List.append output cellBits) with
          ⟨restSteps, hrest⟩
        refine ⟨cellSteps + restSteps, ?_⟩
        rw [MachineDescription.runConfig_add]
        rw [show
            config 10
              (List.append (pre.reverse.map some) [none, some false])
              ((List.append
                (inputTapeRightCellsDirectCopierCellBits (true :: rest))
                (List.append sourceTail output)).map some) =
            config 10
              (List.append (pre.reverse.map some) [none, some false])
              ((List.append cellBits
                (List.append
                  (List.append
                    (inputTapeRightCellsDirectCopierCellBits rest)
                    sourceTail)
                  output)).map some) by
            simp [cellBits, List.append_assoc]]
        rw [hcell]
        rw [show
            config 10
              (List.append ((List.append pre cellBits).reverse.map some)
                [none, some false])
              ((List.append
                (List.append
                  (inputTapeRightCellsDirectCopierCellBits rest)
                  sourceTail)
                (List.append output cellBits)).map some) =
            config 10
              (List.append ((List.append pre cellBits).reverse.map some)
                [none, some false])
              ((List.append
                (inputTapeRightCellsDirectCopierCellBits rest)
                (List.append sourceTail
                  (List.append output cellBits))).map some) by
            simp [List.append_assoc]]
        have hfinish :
            config 10
              (List.append
                ((List.append (List.append pre cellBits)
                  (inputTapeRightCellsDirectCopierCellBits rest)).reverse.map
                    some)
                [none, some false])
              ((List.append sourceTail
                (List.append (List.append output cellBits)
                  (inputTapeRightCellsDirectCopierCellBits rest))).map
                some) =
            config 10
              (List.append
                ((List.append pre
                  (inputTapeRightCellsDirectCopierCellBits
                    (true :: rest))).reverse.map some)
                [none, some false])
              ((List.append sourceTail
                (List.append output
                  (inputTapeRightCellsDirectCopierCellBits
                    (true :: rest)))).map some) := by
          simp [cellBits, List.reverse_append, List.map_append,
            List.append_assoc]
        exact hrest.trans hfinish

def inputTapeRightCellsDirectCopierNatBits (n : Nat) :
    Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.encodeNat n)

@[simp] theorem
    inputTapeRightCellsDirectCopierNatBits_zero :
    inputTapeRightCellsDirectCopierNatBits 0 =
      [false, false, true, true] := by
  rfl

@[simp] theorem
    inputTapeRightCellsDirectCopierNatBits_succ
    (n : Nat) :
    inputTapeRightCellsDirectCopierNatBits (n + 1) =
      false :: false :: true :: false ::
        inputTapeRightCellsDirectCopierNatBits n := by
  rfl

theorem
    inputTapeRightCellsDirectCopierDescription_run_stop_at_natBits
    (pre : Word Bool) (stage : Nat) (tail : Word Bool) :
    InputTapeRightCellsDirectCopierDescription.runConfig
        (pre.length + 5)
        (config 10
          (List.append (pre.reverse.map some) [none, some false])
          ((List.append
            (inputTapeRightCellsDirectCopierNatBits stage) tail).map
            some)) =
      config 99 [some false]
        (some false ::
          ((List.append pre
            (List.append
              (inputTapeRightCellsDirectCopierNatBits stage)
              tail)).map some)) := by
  cases stage with
  | zero =>
      simpa [List.append_assoc] using
        inputTapeRightCellsDirectCopierDescription_run_stop_at_nat_prefix
          pre (List.append [true, true] tail)
  | succ n =>
      simpa [List.append_assoc] using
        inputTapeRightCellsDirectCopierDescription_run_stop_at_nat_prefix
          pre
            (List.append
              (true :: false ::
                inputTapeRightCellsDirectCopierNatBits n)
              tail)

def inputTapeRightCellsDirectCopierPreludeBits : Word Bool :=
  [false, true, false, false, true, false]

def inputTapeRightCellsDirectCopierDoneBits : Word Bool :=
  MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.done

def inputTapeRightCellsDirectCopierHeadBits
    (b : Bool) : Word Bool :=
  if b then
    MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.one
  else
    MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.zero

def inputTapeRightCellsDirectCopierCoreSourceBits
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) : Word Bool :=
  List.append (inputTapeRightCellsDirectCopierTickBits rest.length)
    (List.append inputTapeRightCellsDirectCopierDoneBits
      (List.append (inputTapeRightCellsDirectCopierHeadBits b)
        (List.append (inputTapeRightCellsDirectCopierCellBits rest)
          (List.append
            (inputTapeRightCellsDirectCopierNatBits stage)
            suffixBits))))

def inputTapeRightCellsDirectCopierCoreOutputBits
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) : Word Bool :=
  List.append inputTapeRightCellsDirectCopierPreludeBits
    (List.append (inputTapeRightCellsDirectCopierTickBits rest.length)
      (List.append inputTapeRightCellsDirectCopierDoneBits
        (List.append (inputTapeRightCellsDirectCopierHeadBits b)
          (List.append (inputTapeRightCellsDirectCopierCellBits rest)
            (List.append
              (inputTapeRightCellsDirectCopierNatBits stage)
              (List.append suffixBits
                (List.append
                  (inputTapeRightCellsDirectCopierTickBits rest.length)
                  (List.append inputTapeRightCellsDirectCopierDoneBits
                    (inputTapeRightCellsDirectCopierCellBits rest)))))))))

theorem
    inputTapeRightCellsDirectCopierDescription_run_core
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) :
    exists steps : Nat,
      InputTapeRightCellsDirectCopierDescription.runConfig steps
          (config 0
            (List.append
              (inputTapeRightCellsDirectCopierPreludeBits.reverse.map some)
              [none, some false])
            ((inputTapeRightCellsDirectCopierCoreSourceBits
              b rest stage suffixBits).map some)) =
        config 99 [some false]
          (some false ::
            ((inputTapeRightCellsDirectCopierCoreOutputBits
              b rest stage suffixBits).map some)) := by
  let pre0 := inputTapeRightCellsDirectCopierPreludeBits
  let tickBits := inputTapeRightCellsDirectCopierTickBits rest.length
  let doneBits := inputTapeRightCellsDirectCopierDoneBits
  let headBits := inputTapeRightCellsDirectCopierHeadBits b
  let cellBits := inputTapeRightCellsDirectCopierCellBits rest
  let stageBits := inputTapeRightCellsDirectCopierNatBits stage
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
  rcases
      inputTapeRightCellsDirectCopierDescription_run_stop_at_natBits
        (List.append preAfterDone cellBits) stage
        (List.append suffixBits
          (List.append outputAfterDone cellBits)) with
    hstop
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
          (inputTapeRightCellsDirectCopierPreludeBits.reverse.map some)
          [none, some false])
        ((inputTapeRightCellsDirectCopierCoreSourceBits
          b rest stage suffixBits).map some) =
      config 0
        (List.append (pre0.reverse.map some) [none, some false])
        ((List.append tickBits
          (List.append
            (List.append doneBits
              (List.append headBits sourceTailAfterDone))
            [])).map some) by
      simp [pre0, tickBits, doneBits, headBits, cellBits,
        stageBits, sourceTailAfterDone,
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
  simp [pre0, tickBits, doneBits, headBits, cellBits,
    outputAfterDone, preAfterDone,
    inputTapeRightCellsDirectCopierPreludeBits,
    inputTapeRightCellsDirectCopierDoneBits,
    inputTapeRightCellsDirectCopierCoreOutputBits,
    List.map_append, List.append_assoc]

def InputTapeRightCellsDirectReturnDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    RightCellsCopierStartHandoffDescription
    InputTapeRightCellsDirectCopierDescription
    Direction.right

theorem
    inputTapeRightCellsDirectReturnDescription_subroutineReady :
    InputTapeRightCellsDirectReturnDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    rightCellsCopierStartHandoffDescription_subroutineReady
    inputTapeRightCellsDirectCopierDescription_subroutineReady

theorem
    inputTapeRightCellsDirectReturnDescription_run_core
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) :
    exists steps : Nat,
      InputTapeRightCellsDirectReturnDescription.runConfig steps
          { state := InputTapeRightCellsDirectReturnDescription.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (MachineDescription.encodeCodeSymbolAsInput
                        MachineCodeSymbol.tick)
                      (inputTapeRightCellsDirectCopierCoreSourceBits
                        b rest stage suffixBits))).map some)) } =
        { state := InputTapeRightCellsDirectReturnDescription.halt
          tape :=
            tapeAtCells [some false]
              (some false ::
                ((inputTapeRightCellsDirectCopierCoreOutputBits
                  b rest stage suffixBits).map some)) } := by
  let A := RightCellsCopierStartHandoffDescription
  let B := InputTapeRightCellsDirectCopierDescription
  let sourceBits :=
    inputTapeRightCellsDirectCopierCoreSourceBits
      b rest stage suffixBits
  let Tmid :=
    config A.halt
      [some true, some false, some false, some true, some false, none,
        some false]
      (some false :: sourceBits.map some)
  have hAready : A.SubroutineReady :=
    rightCellsCopierStartHandoffDescription_subroutineReady
  have hBready : B.SubroutineReady :=
    inputTapeRightCellsDirectCopierDescription_subroutineReady
  have hArun :
      A.runConfig 7
          { state := A.start
            tape :=
              tapeAtCells []
                (some false :: some false ::
                  ((List.append [false, true]
                    (List.append
                      (MachineDescription.encodeCodeSymbolAsInput
                        MachineCodeSymbol.tick)
                      sourceBits)).map some)) } =
        { state := A.halt, tape := Tmid.tape } := by
    simpa [A, Tmid, sourceBits,
      MachineDescription.encodeCodeSymbolAsInput, config,
      tapeAtCells, List.map_append, List.append_assoc] using
      rightCellsCopierStartHandoffDescription_run
        (sourceBits.map some)
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape := Tape.move Direction.right Tmid.tape } =
          { state := B.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((inputTapeRightCellsDirectCopierCoreOutputBits
                    b rest stage suffixBits).map some)) } := by
    rcases
        inputTapeRightCellsDirectCopierDescription_run_core
          b rest stage suffixBits with
      ⟨nB, hB⟩
    refine ⟨nB, ?_⟩
    rw [show
        ({ state := B.start
           tape := Tape.move Direction.right Tmid.tape } :
            MachineDescription.Configuration) =
          (config 0
            (List.append
              (inputTapeRightCellsDirectCopierPreludeBits.reverse.map some)
              [none, some false])
            (sourceBits.map some)) by
        simp [B, Tmid, sourceBits,
          InputTapeRightCellsDirectCopierDescription,
          inputTapeRightCellsDirectCopierPreludeBits,
          config, tapeAtCells, Tape.move, Tape.moveRight]
        cases List.map some sourceBits <;> rfl]
    rw [show
        ({ state := B.halt
           tape :=
            tapeAtCells [some false]
              (some false ::
                ((inputTapeRightCellsDirectCopierCoreOutputBits
                  b rest stage suffixBits).map some)) } :
            MachineDescription.Configuration) =
        config 99 [some false]
          (some false ::
            ((inputTapeRightCellsDirectCopierCoreOutputBits
              b rest stage suffixBits).map some)) by
        simp [B, InputTapeRightCellsDirectCopierDescription,
          config, tapeAtCells]]
    simpa [B, sourceBits] using hB
  rcases
      MachineDescription.seqSubroutine_reaches_of_runConfig_eq
        (A := A) (B := B) (handoffMove := Direction.right)
        hAready hBready hArun hBReach with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [InputTapeRightCellsDirectReturnDescription,
    A, B, sourceBits] using hsteps


end DovetailInitialLayoutInitializer
end Computability
end FoC
