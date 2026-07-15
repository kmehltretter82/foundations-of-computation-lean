import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.AcceptConfigLocator
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.WriteWordRight

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape
namespace CountWindowInputMat
namespace AcceptConfigCopy

open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open EncRewriters.BoundedLayoutRunner.SelectedProjectionPaddedTailCleanup.InputMat

def wrappedBit (bit : Bool) : Word Bool :=
  cellCodeBits (some bit)

def bufferedPendingRows (b0 b1 b2 b3 : Bool) : List Transition :=
  let source := pendingState b0 b1 b2 b3
  [ rowsForSourceRead source (some false) keepR keepS keepS (source + 1)
  , rowsForSourceRead (source + 1) (some false) keepL keepS keepS halt
  , rowsForSourceRead (source + 1) (some true)
      keepR keepS (writeS (some b0)) (source + 2)
  , rowsForSourceRead (source + 2) (some false)
      keepR keepS keepS (source + 3)
  , rowsForSourceRead (source + 2) (some true)
      keepR keepS keepS (source + 4)
  , rowsForSourceRead (source + 3) (some true)
      keepR keepS keepR (pendingState b1 b2 b3 false)
  , rowsForSourceRead (source + 4) (some false)
      keepR keepS keepR (pendingState b1 b2 b3 true) ].flatten

def bufferedAllPendingRows : List Transition :=
  bools.flatMap (fun b0 =>
    bools.flatMap (fun b1 =>
      bools.flatMap (fun b2 =>
        bools.flatMap (fun b3 => bufferedPendingRows b0 b1 b2 b3))))

def bufferedCopyRows : List Transition :=
  List.append initializeRows bufferedAllPendingRows

def bufferedCopyDescription : Description :=
  ThreeTape.description (halt + 1) (tokenBase .initialize) halt
    bufferedCopyRows

theorem buffered_initialize_tick_run :
    TokenRun bufferedCopyDescription .initialize .tick := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [bufferedCopyDescription,
    bufferedCopyRows, initializeRows]

theorem buffered_initialize_done_run :
    TokenRun bufferedCopyDescription .initialize .done := by
  simp only [TokenRun]
  intro left rest T2
  solve_token rest on T2 with [bufferedCopyDescription,
    bufferedCopyRows, initializeRows]

theorem lookup_pending_start
    (b0 b1 b2 b3 : Bool) (read2 : Option Bool) :
    bufferedCopyRows.find?
        (Description.Matches (pendingState b0 b1 b2 b3)
          [some false, none, read2]) =
      some
        (row (pendingState b0 b1 b2 b3)
          (some false) none read2 keepR keepS keepS
          (pendingState b0 b1 b2 b3 + 1)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases read2 with
    | none => decide
    | some bit => cases bit <;> decide

theorem lookup_pending_boundary
    (b0 b1 b2 b3 : Bool) (read2 : Option Bool) :
    bufferedCopyRows.find?
        (Description.Matches (pendingState b0 b1 b2 b3 + 1)
          [some false, none, read2]) =
      some
        (row (pendingState b0 b1 b2 b3 + 1)
          (some false) none read2 keepL keepS keepS halt) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases read2 with
    | none => decide
    | some bit => cases bit <;> decide

theorem lookup_pending_wrapped
    (b0 b1 b2 b3 : Bool) (read2 : Option Bool) :
    bufferedCopyRows.find?
        (Description.Matches (pendingState b0 b1 b2 b3 + 1)
          [some true, none, read2]) =
      some
        (row (pendingState b0 b1 b2 b3 + 1)
          (some true) none read2 keepR keepS (writeS (some b0))
          (pendingState b0 b1 b2 b3 + 2)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases read2 with
    | none => decide
    | some bit => cases bit <;> decide

theorem lookup_pending_value_false
    (b0 b1 b2 b3 : Bool) (read2 : Option Bool) :
    bufferedCopyRows.find?
        (Description.Matches (pendingState b0 b1 b2 b3 + 2)
          [some false, none, read2]) =
      some
        (row (pendingState b0 b1 b2 b3 + 2)
          (some false) none read2 keepR keepS keepS
          (pendingState b0 b1 b2 b3 + 3)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases read2 with
    | none => decide
    | some bit => cases bit <;> decide

theorem lookup_pending_value_true
    (b0 b1 b2 b3 : Bool) (read2 : Option Bool) :
    bufferedCopyRows.find?
        (Description.Matches (pendingState b0 b1 b2 b3 + 2)
          [some true, none, read2]) =
      some
        (row (pendingState b0 b1 b2 b3 + 2)
          (some true) none read2 keepR keepS keepS
          (pendingState b0 b1 b2 b3 + 4)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases read2 with
    | none => decide
    | some bit => cases bit <;> decide

theorem lookup_pending_finish_false
    (b0 b1 b2 b3 : Bool) (read2 : Option Bool) :
    bufferedCopyRows.find?
        (Description.Matches (pendingState b0 b1 b2 b3 + 3)
          [some true, none, read2]) =
      some
        (row (pendingState b0 b1 b2 b3 + 3)
          (some true) none read2 keepR keepS keepR
          (pendingState b1 b2 b3 false)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases read2 with
    | none => decide
    | some bit => cases bit <;> decide

theorem lookup_pending_finish_true
    (b0 b1 b2 b3 : Bool) (read2 : Option Bool) :
    bufferedCopyRows.find?
        (Description.Matches (pendingState b0 b1 b2 b3 + 4)
          [some false, none, read2]) =
      some
        (row (pendingState b0 b1 b2 b3 + 4)
          (some false) none read2 keepR keepS keepR
          (pendingState b1 b2 b3 true)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases read2 with
    | none => decide
    | some bit => cases bit <;> decide

theorem lookupTransition_of_find
    (state : Nat) (source work : Tape Bool)
    (sourceRead : Option Bool) (transition : Transition)
    (hsource : Tape.read source = sourceRead)
    (hfind : bufferedCopyRows.find?
      (Description.Matches state [sourceRead, none, Tape.read work]) =
        some transition) :
    bufferedCopyDescription.lookupTransition
        (config state source Tape.blank work) =
      some transition := by
  simp only [Description.lookupTransition]
  rw [currentReads_config bufferedCopyDescription (by rfl)]
  change source.head = sourceRead at hsource
  simpa [bufferedCopyDescription, ThreeTape.description,
    Tape.blank, Tape.read, hsource] using hfind

theorem lookupTransition_pending_start
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some false) :
    bufferedCopyDescription.lookupTransition
        (config (pendingState b0 b1 b2 b3) source Tape.blank work) =
      some
        (row (pendingState b0 b1 b2 b3)
          (some false) none (Tape.read work) keepR keepS keepS
          (pendingState b0 b1 b2 b3 + 1)) := by
  exact lookupTransition_of_find _ _ _ _ _ hsource
    (lookup_pending_start b0 b1 b2 b3 (Tape.read work))

theorem lookupTransition_pending_boundary
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some false) :
    bufferedCopyDescription.lookupTransition
        (config (pendingState b0 b1 b2 b3 + 1) source Tape.blank work) =
      some
        (row (pendingState b0 b1 b2 b3 + 1)
          (some false) none (Tape.read work) keepL keepS keepS halt) := by
  exact lookupTransition_of_find _ _ _ _ _ hsource
    (lookup_pending_boundary b0 b1 b2 b3 (Tape.read work))

theorem lookupTransition_pending_wrapped
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some true) :
    bufferedCopyDescription.lookupTransition
        (config (pendingState b0 b1 b2 b3 + 1) source Tape.blank work) =
      some
        (row (pendingState b0 b1 b2 b3 + 1)
          (some true) none (Tape.read work) keepR keepS (writeS (some b0))
          (pendingState b0 b1 b2 b3 + 2)) := by
  exact lookupTransition_of_find _ _ _ _ _ hsource
    (lookup_pending_wrapped b0 b1 b2 b3 (Tape.read work))

theorem lookupTransition_pending_value_false
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some false) :
    bufferedCopyDescription.lookupTransition
        (config (pendingState b0 b1 b2 b3 + 2) source Tape.blank work) =
      some
        (row (pendingState b0 b1 b2 b3 + 2)
          (some false) none (Tape.read work) keepR keepS keepS
          (pendingState b0 b1 b2 b3 + 3)) := by
  exact lookupTransition_of_find _ _ _ _ _ hsource
    (lookup_pending_value_false b0 b1 b2 b3 (Tape.read work))

theorem lookupTransition_pending_value_true
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some true) :
    bufferedCopyDescription.lookupTransition
        (config (pendingState b0 b1 b2 b3 + 2) source Tape.blank work) =
      some
        (row (pendingState b0 b1 b2 b3 + 2)
          (some true) none (Tape.read work) keepR keepS keepS
          (pendingState b0 b1 b2 b3 + 4)) := by
  exact lookupTransition_of_find _ _ _ _ _ hsource
    (lookup_pending_value_true b0 b1 b2 b3 (Tape.read work))

theorem lookupTransition_pending_finish_false
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some true) :
    bufferedCopyDescription.lookupTransition
        (config (pendingState b0 b1 b2 b3 + 3) source Tape.blank work) =
      some
        (row (pendingState b0 b1 b2 b3 + 3)
          (some true) none (Tape.read work) keepR keepS keepR
          (pendingState b1 b2 b3 false)) := by
  exact lookupTransition_of_find _ _ _ _ _ hsource
    (lookup_pending_finish_false b0 b1 b2 b3 (Tape.read work))

theorem lookupTransition_pending_finish_true
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some false) :
    bufferedCopyDescription.lookupTransition
        (config (pendingState b0 b1 b2 b3 + 4) source Tape.blank work) =
      some
        (row (pendingState b0 b1 b2 b3 + 4)
          (some false) none (Tape.read work) keepR keepS keepR
          (pendingState b1 b2 b3 true)) := by
  exact lookupTransition_of_find _ _ _ _ _ hsource
    (lookup_pending_finish_true b0 b1 b2 b3 (Tape.read work))

theorem applyActions_buffered
    (action0 action1 action2 : TapeAction)
    (tape0 tape1 tape2 : Tape Bool) :
    bufferedCopyDescription.applyActions
        [action0, action1, action2] [tape0, tape1, tape2] =
      [action0.apply tape0, action1.apply tape1, action2.apply tape2] := by
  exact Description.applyActions_three bufferedCopyDescription (by rfl)
    action0 action1 action2 tape0 tape1 tape2

theorem step_pending_start
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some false) :
    bufferedCopyDescription.stepConfig
        (config (pendingState b0 b1 b2 b3) source Tape.blank work) =
      some
        (config (pendingState b0 b1 b2 b3 + 1)
          (Tape.move Direction.right source) Tape.blank work) := by
  rw [Description.stepConfig,
    lookupTransition_pending_start b0 b1 b2 b3 source work hsource]
  simp [ThreeTape.row, ThreeTape.config, applyActions_buffered,
    ThreeTape.keepR, ThreeTape.keepS, TapeAction.apply, TapeAction.stay,
    HeadMove.apply]

theorem step_pending_boundary
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some false) :
    bufferedCopyDescription.stepConfig
        (config (pendingState b0 b1 b2 b3 + 1)
          source Tape.blank work) =
      some
        (config halt (Tape.move Direction.left source) Tape.blank work) := by
  rw [Description.stepConfig,
    lookupTransition_pending_boundary b0 b1 b2 b3 source work hsource]
  simp [ThreeTape.row, ThreeTape.config, applyActions_buffered,
    ThreeTape.keepL, ThreeTape.keepS, TapeAction.apply, TapeAction.stay,
    HeadMove.apply]

theorem step_pending_wrapped
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some true) :
    bufferedCopyDescription.stepConfig
        (config (pendingState b0 b1 b2 b3 + 1)
          source Tape.blank work) =
      some
        (config (pendingState b0 b1 b2 b3 + 2)
          (Tape.move Direction.right source) Tape.blank
          (Tape.write (some b0) work)) := by
  rw [Description.stepConfig,
    lookupTransition_pending_wrapped b0 b1 b2 b3 source work hsource]
  simp [ThreeTape.row, ThreeTape.config, applyActions_buffered,
    ThreeTape.keepR, ThreeTape.keepS, ThreeTape.writeS,
    TapeAction.apply, TapeAction.stay, HeadMove.apply]

theorem step_pending_value_false
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some false) :
    bufferedCopyDescription.stepConfig
        (config (pendingState b0 b1 b2 b3 + 2)
          source Tape.blank work) =
      some
        (config (pendingState b0 b1 b2 b3 + 3)
          (Tape.move Direction.right source) Tape.blank work) := by
  rw [Description.stepConfig,
    lookupTransition_pending_value_false b0 b1 b2 b3 source work hsource]
  simp [ThreeTape.row, ThreeTape.config, applyActions_buffered,
    ThreeTape.keepR, ThreeTape.keepS, TapeAction.apply, TapeAction.stay,
    HeadMove.apply]

theorem step_pending_value_true
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some true) :
    bufferedCopyDescription.stepConfig
        (config (pendingState b0 b1 b2 b3 + 2)
          source Tape.blank work) =
      some
        (config (pendingState b0 b1 b2 b3 + 4)
          (Tape.move Direction.right source) Tape.blank work) := by
  rw [Description.stepConfig,
    lookupTransition_pending_value_true b0 b1 b2 b3 source work hsource]
  simp [ThreeTape.row, ThreeTape.config, applyActions_buffered,
    ThreeTape.keepR, ThreeTape.keepS, TapeAction.apply, TapeAction.stay,
    HeadMove.apply]

theorem step_pending_finish_false
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some true) :
    bufferedCopyDescription.stepConfig
        (config (pendingState b0 b1 b2 b3 + 3)
          source Tape.blank work) =
      some
        (config (pendingState b1 b2 b3 false)
          (Tape.move Direction.right source) Tape.blank
          (Tape.move Direction.right work)) := by
  rw [Description.stepConfig,
    lookupTransition_pending_finish_false b0 b1 b2 b3 source work hsource]
  simp [ThreeTape.row, ThreeTape.config, applyActions_buffered,
    ThreeTape.keepR, ThreeTape.keepS, TapeAction.apply, TapeAction.stay,
    HeadMove.apply]

theorem step_pending_finish_true
    (b0 b1 b2 b3 : Bool) (source work : Tape Bool)
    (hsource : Tape.read source = some false) :
    bufferedCopyDescription.stepConfig
        (config (pendingState b0 b1 b2 b3 + 4)
          source Tape.blank work) =
      some
        (config (pendingState b1 b2 b3 true)
          (Tape.move Direction.right source) Tape.blank
          (Tape.move Direction.right work)) := by
  rw [Description.stepConfig,
    lookupTransition_pending_finish_true b0 b1 b2 b3 source work hsource]
  simp [ThreeTape.row, ThreeTape.config, applyActions_buffered,
    ThreeTape.keepR, ThreeTape.keepS, TapeAction.apply, TapeAction.stay,
    HeadMove.apply]

syntax "buffer_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| buffer_step [$lemmas,*]) =>
      `(tactic|
        simp (config := { maxSteps := 1000000 }) [
          ThreeTape.row, ThreeTape.description,
          ThreeTape.keepL, ThreeTape.keepR, ThreeTape.keepS,
          ThreeTape.writeL, ThreeTape.writeR, ThreeTape.writeS,
          Description.applyActions_three, Description.runConfig,
          Description.stepConfig,
          TapeAction.apply, TapeAction.stay,
          HeadMove.apply, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight, tapeAtCells,
          route, tokenBase, tokenBlockSize, phaseIndex,
          halt,
          lookupTransition_pending_start,
          lookupTransition_pending_boundary,
          lookupTransition_pending_wrapped,
          lookupTransition_pending_value_false,
          lookupTransition_pending_value_true,
          lookupTransition_pending_finish_false,
          lookupTransition_pending_finish_true,
          applyActions_buffered,
          $lemmas,*])

theorem pending_bit_run
    (b0 b1 b2 b3 bit : Bool)
    (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool) :
    bufferedCopyDescription.runConfig 4
        (config (pendingState b0 b1 b2 b3)
          (scanTape left (List.append (wrappedBit bit) rest))
          Tape.blank T2) =
      config (pendingState b1 b2 b3 bit)
        (scanTape
          (List.append ((wrappedBit bit).reverse.map some) left)
          rest)
        Tape.blank (writeWordRight [b0] T2) := by
  cases bit <;>
    rw [Description.runConfig] <;>
    rw [step_pending_start b0 b1 b2 b3 _ _ (by
      simp [scanTape, wrappedBit, cellCodeBits, encodeCell,
        encodeCodeWordAsInput, encodeCodeSymbolAsInput, tapeAtCells,
        Tape.read])] <;>
    simp only <;>
    rw [Description.runConfig] <;>
    rw [step_pending_wrapped b0 b1 b2 b3 _ _ (by
      simp [scanTape, wrappedBit, cellCodeBits, encodeCell,
        encodeCodeWordAsInput, encodeCodeSymbolAsInput, tapeAtCells,
        Tape.read, Tape.move, Tape.moveRight])] <;>
    simp only <;>
    cases rest <;>
    rw [Description.runConfig]
  · rw [step_pending_value_false b0 b1 b2 b3 _ _ (by rfl)]
    simp only
    rw [Description.runConfig]
    rw [step_pending_finish_false b0 b1 b2 b3 _ _ (by rfl)]
    simp [Description.runConfig, scanTape, wrappedBit, writeWordRight, cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

  · rw [step_pending_value_false b0 b1 b2 b3 _ _ (by rfl)]
    simp only
    rw [Description.runConfig]
    rw [step_pending_finish_false b0 b1 b2 b3 _ _ (by rfl)]
    simp [Description.runConfig, scanTape, wrappedBit, writeWordRight, cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

  · rw [step_pending_value_true b0 b1 b2 b3 _ _ (by rfl)]
    simp only
    rw [Description.runConfig]
    rw [step_pending_finish_true b0 b1 b2 b3 _ _ (by rfl)]
    simp [Description.runConfig, scanTape, wrappedBit, writeWordRight, cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]
  · rw [step_pending_value_true b0 b1 b2 b3 _ _ (by rfl)]
    simp only
    rw [Description.runConfig]
    rw [step_pending_finish_true b0 b1 b2 b3 _ _ (by rfl)]
    simp [Description.runConfig, scanTape, wrappedBit, writeWordRight, cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      tapeAtCells, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem pending_boundary_run
    (b0 b1 b2 b3 : Bool)
    (left : List (Option Bool)) (boundaryRest : List Bool)
    (T2 : Tape Bool) :
    bufferedCopyDescription.runConfig 2
        (config (pendingState b0 b1 b2 b3)
          (scanTape left (false :: false :: boundaryRest))
          Tape.blank T2) =
      config halt
        (scanTape left (false :: false :: boundaryRest))
        Tape.blank T2 := by
  rw [Description.runConfig]
  rw [step_pending_start b0 b1 b2 b3 _ _ (by
    simp [scanTape, tapeAtCells, Tape.read])]
  simp only
  rw [Description.runConfig]
  rw [step_pending_boundary b0 b1 b2 b3 _ _ (by
    simp [scanTape, tapeAtCells, Tape.read, Tape.move, Tape.moveRight])]
  simp [Description.runConfig, scanTape, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

def wrappedBits : Word Bool -> Word Bool
  | [] => []
  | bit :: rest => List.append (wrappedBit bit) (wrappedBits rest)

def fifoEmitted (b0 b1 b2 b3 : Bool) : Word Bool -> Word Bool
  | [] => []
  | bit :: rest => b0 :: fifoEmitted b1 b2 b3 bit rest

theorem wrappedBits_cons_append
    (bit : Bool) (bits : Word Bool) (suffix : List Bool) :
    List.append (wrappedBits (bit :: bits)) suffix =
      List.append (wrappedBit bit)
        (List.append (wrappedBits bits) suffix) := by
  cases bit <;>
    simp [wrappedBits, wrappedBit, cellCodeBits, encodeCell,
      encodeCodeWordAsInput, encodeCodeSymbolAsInput]

theorem wrappedBits_reverse_map_cons_append_left
    (bit : Bool) (bits : Word Bool)
    (left : List (Option Bool)) :
    List.append ((wrappedBits (bit :: bits)).reverse.map some) left =
      List.append ((wrappedBits bits).reverse.map some)
        (List.append ((wrappedBit bit).reverse.map some) left) := by
  cases bit <;>
    simp [wrappedBits, wrappedBit, cellCodeBits, encodeCell,
      encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      List.reverse_append, List.map_append, List.append_assoc]

theorem writeWordRight_fifo_cons
    (b0 b1 b2 b3 bit : Bool) (bits : Word Bool) (T : Tape Bool) :
    writeWordRight (fifoEmitted b1 b2 b3 bit bits)
        (writeWordRight [b0] T) =
      writeWordRight (fifoEmitted b0 b1 b2 b3 (bit :: bits)) T := by
  rfl

theorem pending_fifo_run
    (b0 b1 b2 b3 : Bool) (bits : Word Bool)
    (left : List (Option Bool)) (boundaryRest : List Bool)
    (T2 : Tape Bool) :
    bufferedCopyDescription.runConfig (4 * bits.length + 2)
        (config (pendingState b0 b1 b2 b3)
          (scanTape left
            (List.append (wrappedBits bits)
              (false :: false :: boundaryRest)))
          Tape.blank T2) =
      config halt
        (scanTape
          (List.append ((wrappedBits bits).reverse.map some) left)
          (false :: false :: boundaryRest))
        Tape.blank (writeWordRight (fifoEmitted b0 b1 b2 b3 bits) T2) := by
  induction bits generalizing b0 b1 b2 b3 left T2 with
  | nil =>
      simpa [wrappedBits, fifoEmitted, writeWordRight] using
        pending_boundary_run b0 b1 b2 b3 left boundaryRest T2
  | cons bit bits ih =>
      rw [show 4 * (bit :: bits).length + 2 =
          4 + (4 * bits.length + 2) by
        simp only [List.length_cons]
        lia]
      rw [Description.runConfig_add]
      rw [wrappedBits_cons_append]
      rw [pending_bit_run b0 b1 b2 b3 bit left
        (List.append (wrappedBits bits) (false :: false :: boundaryRest)) T2]
      rw [ih]
      rw [wrappedBits_reverse_map_cons_append_left]
      rw [writeWordRight_fifo_cons]

theorem fifoEmitted_append_flush
    (b0 b1 b2 b3 r0 r1 r2 r3 : Bool) (tail : Word Bool) :
    fifoEmitted b0 b1 b2 b3
        (List.append tail [r0, r1, r2, r3]) =
      List.append [b0, b1, b2, b3] tail := by
  induction tail generalizing b0 b1 b2 b3 with
  | nil =>
      rfl
  | cons bit tail ih =>
      change
        b0 :: fifoEmitted b1 b2 b3 bit
            (List.append tail [r0, r1, r2, r3]) =
          b0 :: b1 :: b2 :: b3 :: bit :: tail
      rw [ih b1 b2 b3 bit]
      rfl

def acceptStateKind (L : DovetailLayout) : Kind :=
  match L.acceptConfig.state with
  | 0 => .done
  | _ + 1 => .tick

def acceptStateRemainder (L : DovetailLayout) : Word Bool :=
  match L.acceptConfig.state with
  | 0 =>
      List.append (tapeFieldBits L.acceptConfig.tape [])
        (acceptOldTail L)
  | n + 1 =>
      List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n)
        (List.append (tapeFieldBits L.acceptConfig.tape [])
          (acceptOldTail L))

def acceptCopyBits (L : DovetailLayout) : Word Bool :=
  List.append (acceptStateRemainder L)
    [false, true, L.rejectHit, !L.rejectHit]

theorem acceptInsertedTail_eq_kind_remainder (L : DovetailLayout) :
    acceptInsertedTail L =
      List.append (acceptStateKind L).bits (acceptStateRemainder L) := by
  cases hstate : L.acceptConfig.state with
  | zero =>
      simp [acceptInsertedTail, acceptStateKind, acceptStateRemainder,
        configurationFieldBits, hstate, Kind.bits, List.append_assoc]
  | succ n =>
      simp [acceptInsertedTail, acceptStateKind, acceptStateRemainder,
        configurationFieldBits, hstate, Kind.bits,
        Nat.succ_eq_add_one, List.append_assoc]

theorem boolFieldBits_eq_flush (b : Bool) :
    boolFieldBits b [] = [false, true, b, !b] := by
  cases b <;>
    rfl

theorem accept_copy_run
    (L : DovetailLayout)
    (sourceLeft outputLeft : List (Option Bool))
    (boundaryRest : List Bool) :
    bufferedCopyDescription.runConfig
        (16 + (4 * (acceptCopyBits L).length + 2))
        (config (tokenBase .initialize)
          (scanTape sourceLeft
            (List.append (wrappedKind (acceptStateKind L))
              (List.append (wrappedBits (acceptCopyBits L))
                (false :: false :: boundaryRest))))
          Tape.blank
          (tapeAtCells outputLeft
            (List.append ((acceptOldTail L).map some) [none]))) =
      config halt
        (scanTape
          (List.append ((wrappedBits (acceptCopyBits L)).reverse.map some)
            (List.append
              ((wrappedKind (acceptStateKind L)).reverse.map some)
              sourceLeft))
          (false :: false :: boundaryRest))
        Tape.blank
        (tapeAtCells
          (List.append ((acceptInsertedTail L).reverse.map some) outputLeft)
          [none]) := by
  cases hstate : L.acceptConfig.state with
  | zero =>
      rw [Description.runConfig_add]
      simp only [acceptStateKind, hstate]
      rw [buffered_initialize_done_run sourceLeft
        (List.append (wrappedBits (acceptCopyBits L))
          (false :: false :: boundaryRest))
        (tapeAtCells outputLeft
          (List.append ((acceptOldTail L).map some) [none]))]
      change
        bufferedCopyDescription.runConfig (4 * (acceptCopyBits L).length + 2)
            (config (pendingState false false true true)
              (scanTape
                (List.append ((wrappedKind .done).reverse.map some) sourceLeft)
                (List.append (wrappedBits (acceptCopyBits L))
                  (false :: false :: boundaryRest)))
              Tape.blank
              (tapeAtCells outputLeft
                (List.append ((acceptOldTail L).map some) [none]))) = _
      rw [pending_fifo_run]
      have hfifo :
          fifoEmitted false false true true (acceptCopyBits L) =
            acceptInsertedTail L := by
        unfold acceptCopyBits
        rw [fifoEmitted_append_flush]
        rw [acceptInsertedTail_eq_kind_remainder]
        simp [acceptStateKind, hstate, Kind.bits]
      rw [hfifo]
      rw [writeWordRight_acceptInsertedTail]
  | succ n =>
      rw [Description.runConfig_add]
      simp only [acceptStateKind, hstate]
      rw [buffered_initialize_tick_run sourceLeft
        (List.append (wrappedBits (acceptCopyBits L))
          (false :: false :: boundaryRest))
        (tapeAtCells outputLeft
          (List.append ((acceptOldTail L).map some) [none]))]
      change
        bufferedCopyDescription.runConfig (4 * (acceptCopyBits L).length + 2)
            (config (pendingState false false true false)
              (scanTape
                (List.append ((wrappedKind .tick).reverse.map some) sourceLeft)
                (List.append (wrappedBits (acceptCopyBits L))
                  (false :: false :: boundaryRest)))
              Tape.blank
              (tapeAtCells outputLeft
                (List.append ((acceptOldTail L).map some) [none]))) = _
      rw [pending_fifo_run]
      have hfifo :
          fifoEmitted false false true false (acceptCopyBits L) =
            acceptInsertedTail L := by
        unfold acceptCopyBits
        rw [fifoEmitted_append_flush]
        rw [acceptInsertedTail_eq_kind_remainder]
        simp [acceptStateKind, hstate, Kind.bits]
      rw [hfifo]
      rw [writeWordRight_acceptInsertedTail]

end AcceptConfigCopy
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
