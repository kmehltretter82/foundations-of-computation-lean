import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.AcceptConfigLocator
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic

set_option doc.verso true

/-!
Generic token routing and exact stream runs used by the indexed materializer.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
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
namespace DirectTokenDriver

open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open _root_.FoC.Computability.CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.AcceptConfigCopy (Kind)

def rowsForSourceRead
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReadCells.map
    (fun read2 =>
      row source sourceRead none read2 action0 action1 action2 target)

def wrappedBitRows
    (source targetFalse targetTrue : Nat)
    (actionFalse actionTrue : TapeAction) : List Transition :=
  [ rowsForSourceRead source (some false) keepR keepS keepS (source + 1)
  , rowsForSourceRead (source + 1) (some true)
      keepR keepS keepS (source + 2)
  , rowsForSourceRead (source + 2) (some false)
      keepR keepS keepS (source + 3)
  , rowsForSourceRead (source + 2) (some true)
      keepR keepS keepS (source + 4)
  , rowsForSourceRead (source + 3) (some true)
      keepR keepS actionFalse targetFalse
  , rowsForSourceRead (source + 4) (some false)
      keepR keepS actionTrue targetTrue ].flatten
def invalid : Nat := 40

def tokenRows
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction) : List Transition :=
  [ wrappedBitRows 0 5 invalid action0 keepS
  , wrappedBitRows 5 10 15 action1 action1
  , wrappedBitRows 10 20 25 action2 action2
  , wrappedBitRows 15 30 35 action2 action2
  , wrappedBitRows 20 invalid (route .transition)
      keepS (action3 .transition)
  , wrappedBitRows 25 (route .tick) (route .done)
      (action3 .tick) (action3 .done)
  , wrappedBitRows 30 (route .blank) (route .zero)
      (action3 .blank) (action3 .zero)
  , wrappedBitRows 35 (route .one) invalid
      (action3 .one) keepS ].flatten

def description
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition := []) : Description :=
  ThreeTape.description stateCount start halt
    (List.append
      (tokenRows route action0 action1 action2 action3)
      restRows)
def scanTape
    (left : List (Option Bool)) (bits : List Bool) : Tape Bool :=
  tapeAtCells left (List.append (bits.map some) [none])

def wrappedRawBit (bit : Bool) : List Bool :=
  cellsCodeBits ([bit].map some)

namespace AcceptConfigCopy

/- List-valued counterparts of the production wrapped-bit helpers.
Keeping these list-valued avoids exposing the {lit}`Word` definition while the
generic stream inductions decompose their inputs. -/
abbrev wrappedBit (bit : Bool) : List Bool :=
  wrappedRawBit bit

def wrappedBits : List Bool -> List Bool
  | [] => []
  | bit :: rest => List.append (wrappedBit bit) (wrappedBits rest)
theorem wrappedBits_cons_append
    (bit : Bool) (bits suffix : List Bool) :
    List.append (wrappedBits (bit :: bits)) suffix =
      List.append (wrappedBit bit)
        (List.append (wrappedBits bits) suffix) := by
  simp [wrappedBits, List.append_assoc]

end AcceptConfigCopy

syntax "token_driver_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| token_driver_simp [$lemmas,*]) =>
      `(tactic|
        simp (config := { maxSteps := 1000000 }) [
          ThreeTape.row, ThreeTape.config, ThreeTape.description,
          ThreeTape.keepL, ThreeTape.keepR, ThreeTape.keepS,
          ThreeTape.writeL, ThreeTape.writeR, ThreeTape.writeS,
          ThreeTape.eraseL, ThreeTape.eraseR,
          ThreeTape.writeBitL, ThreeTape.writeBitR,
          Description.applyActions_three, Description.runConfig,
          Description.stepConfig, Description.lookupTransition,
          Description.Matches, TapeAction.apply, TapeAction.stay,
          HeadMove.apply, Tape.blank, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight, tapeAtCells,
          description, tokenRows, wrappedBitRows, rowsForSourceRead,
          invalid, allReadCells, List.find?, scanTape, wrappedRawBit,
          cellsCodeBits, cellCodeBits, encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, encodeCell, List.reverse_append,
          List.map_append, List.append_assoc, $lemmas,*])

syntax "solve_token_bit" ident "on" ident : tactic

macro_rules
  | `(tactic| solve_token_bit $rest:ident on $T2:ident) =>
      `(tactic|
        cases $rest:ident <;>
          cases h2 : ($T2:ident).head with
          | none =>
              token_driver_simp [h2]
          | some bit =>
              cases bit <;> token_driver_simp [h2])

theorem bit0_false_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 0
          (scanTape left (List.append (wrappedRawBit false) rest))
          Tape.blank T2) =
      config 5
        (scanTape
          (List.append ((wrappedRawBit false).reverse.map some) left)
          rest)
        Tape.blank (action0.apply T2) := by
  solve_token_bit rest on T2

theorem bit1_false_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 5
          (scanTape left (List.append (wrappedRawBit false) rest))
          Tape.blank T2) =
      config 10
        (scanTape
          (List.append ((wrappedRawBit false).reverse.map some) left)
          rest)
        Tape.blank (action1.apply T2) := by
  solve_token_bit rest on T2
theorem bit1_true_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 5
          (scanTape left (List.append (wrappedRawBit true) rest))
          Tape.blank T2) =
      config 15
        (scanTape
          (List.append ((wrappedRawBit true).reverse.map some) left)
          rest)
        Tape.blank (action1.apply T2) := by
  solve_token_bit rest on T2

theorem bit2_transition_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 10
          (scanTape left (List.append (wrappedRawBit false) rest))
          Tape.blank T2) =
      config 20
        (scanTape
          (List.append ((wrappedRawBit false).reverse.map some) left)
          rest)
        Tape.blank (action2.apply T2) := by
  solve_token_bit rest on T2

theorem bit2_nat_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 10
          (scanTape left (List.append (wrappedRawBit true) rest))
          Tape.blank T2) =
      config 25
        (scanTape
          (List.append ((wrappedRawBit true).reverse.map some) left)
          rest)
        Tape.blank (action2.apply T2) := by
  solve_token_bit rest on T2
theorem bit2_zero_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 15
          (scanTape left (List.append (wrappedRawBit false) rest))
          Tape.blank T2) =
      config 30
        (scanTape
          (List.append ((wrappedRawBit false).reverse.map some) left)
          rest)
        Tape.blank (action2.apply T2) := by
  solve_token_bit rest on T2

theorem bit2_one_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 15
          (scanTape left (List.append (wrappedRawBit true) rest))
          Tape.blank T2) =
      config 35
        (scanTape
          (List.append ((wrappedRawBit true).reverse.map some) left)
          rest)
        Tape.blank (action2.apply T2) := by
  solve_token_bit rest on T2

theorem bit3_transition_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 20
          (scanTape left (List.append (wrappedRawBit true) rest))
          Tape.blank T2) =
      config (route .transition)
        (scanTape
          (List.append ((wrappedRawBit true).reverse.map some) left)
          rest)
        Tape.blank ((action3 .transition).apply T2) := by
  solve_token_bit rest on T2
theorem bit3_tick_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 25
          (scanTape left (List.append (wrappedRawBit false) rest))
          Tape.blank T2) =
      config (route .tick)
        (scanTape
          (List.append ((wrappedRawBit false).reverse.map some) left)
          rest)
        Tape.blank ((action3 .tick).apply T2) := by
  solve_token_bit rest on T2

theorem bit3_done_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 25
          (scanTape left (List.append (wrappedRawBit true) rest))
          Tape.blank T2) =
      config (route .done)
        (scanTape
          (List.append ((wrappedRawBit true).reverse.map some) left)
          rest)
        Tape.blank ((action3 .done).apply T2) := by
  solve_token_bit rest on T2

theorem bit3_zero_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 30
          (scanTape left (List.append (wrappedRawBit true) rest))
          Tape.blank T2) =
      config (route .zero)
        (scanTape
          (List.append ((wrappedRawBit true).reverse.map some) left)
          rest)
        Tape.blank ((action3 .zero).apply T2) := by
  solve_token_bit rest on T2
theorem bit3_one_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 4
        (config 35
          (scanTape left (List.append (wrappedRawBit false) rest))
          Tape.blank T2) =
      config (route .one)
        (scanTape
          (List.append ((wrappedRawBit false).reverse.map some) left)
          rest)
        Tape.blank ((action3 .one).apply T2) := by
  solve_token_bit rest on T2

def wrappedKind (kind : Kind) : List Bool :=
  cellsCodeBits (kind.bits.map some)

def applyOutputs
    (action0 action1 action2 action3 : TapeAction)
    (T2 : Tape Bool) : Tape Bool :=
  action3.apply (action2.apply (action1.apply (action0.apply T2)))
def TokenRun
    (kind : Kind)
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition) : Prop :=
  forall (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool),
    (description stateCount start halt route
        action0 action1 action2 action3 restRows).runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind kind) rest))
          Tape.blank T2) =
      config (route kind)
        (scanTape
          (List.append ((wrappedKind kind).reverse.map some) left)
          rest)
        Tape.blank
          (applyOutputs action0 action1 action2 (action3 kind) T2)

theorem wrappedKind_transition_eq :
    wrappedKind .transition =
      List.append (wrappedRawBit false)
        (List.append (wrappedRawBit false)
          (List.append (wrappedRawBit false) (wrappedRawBit true))) := by
  rfl

theorem wrappedKind_tick_eq :
    wrappedKind .tick =
      List.append (wrappedRawBit false)
        (List.append (wrappedRawBit false)
          (List.append (wrappedRawBit true) (wrappedRawBit false))) := by
  rfl
theorem wrappedKind_done_eq :
    wrappedKind .done =
      List.append (wrappedRawBit false)
        (List.append (wrappedRawBit false)
          (List.append (wrappedRawBit true) (wrappedRawBit true))) := by
  rfl

theorem wrappedKind_zero_eq :
    wrappedKind .zero =
      List.append (wrappedRawBit false)
        (List.append (wrappedRawBit true)
          (List.append (wrappedRawBit false) (wrappedRawBit true))) := by
  rfl

theorem wrappedKind_one_eq :
    wrappedKind .one =
      List.append (wrappedRawBit false)
        (List.append (wrappedRawBit true)
          (List.append (wrappedRawBit true) (wrappedRawBit false))) := by
  rfl
theorem wrappedKind_transition_append (rest : List Bool) :
    List.append (wrappedKind .transition) rest =
      List.append (wrappedRawBit false)
        (List.append (wrappedRawBit false)
          (List.append (wrappedRawBit false)
            (List.append (wrappedRawBit true) rest))) := by
  simp [wrappedKind_transition_eq, wrappedRawBit, List.append_assoc]

theorem wrappedKind_tick_append (rest : List Bool) :
    List.append (wrappedKind .tick) rest =
      List.append (wrappedRawBit false)
        (List.append (wrappedRawBit false)
          (List.append (wrappedRawBit true)
            (List.append (wrappedRawBit false) rest))) := by
  simp [wrappedKind_tick_eq, wrappedRawBit, List.append_assoc]

theorem wrappedKind_done_append (rest : List Bool) :
    List.append (wrappedKind .done) rest =
      List.append (wrappedRawBit false)
        (List.append (wrappedRawBit false)
          (List.append (wrappedRawBit true)
            (List.append (wrappedRawBit true) rest))) := by
  simp [wrappedKind_done_eq, wrappedRawBit, List.append_assoc]
theorem wrappedKind_zero_append (rest : List Bool) :
    List.append (wrappedKind .zero) rest =
      List.append (wrappedRawBit false)
        (List.append (wrappedRawBit true)
          (List.append (wrappedRawBit false)
            (List.append (wrappedRawBit true) rest))) := by
  simp [wrappedKind_zero_eq, wrappedRawBit, List.append_assoc]

theorem wrappedKind_one_append (rest : List Bool) :
    List.append (wrappedKind .one) rest =
      List.append (wrappedRawBit false)
        (List.append (wrappedRawBit true)
          (List.append (wrappedRawBit true)
            (List.append (wrappedRawBit false) rest))) := by
  simp [wrappedKind_one_eq, wrappedRawBit, List.append_assoc]

theorem transition_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition) :
    TokenRun .transition stateCount start halt route
      action0 action1 action2 action3 restRows := by
  simp only [TokenRun]
  intro left rest T2
  rw [wrappedKind_transition_append]
  change
    (description stateCount start halt route
      action0 action1 action2 action3 restRows).runConfig
        (4 + (4 + (4 + 4))) _ = _
  rw [Description.runConfig_add]
  rw [bit0_false_run]
  rw [Description.runConfig_add]
  rw [bit1_false_run]
  rw [Description.runConfig_add]
  rw [bit2_transition_run]
  rw [bit3_transition_run]
  simp [applyOutputs, wrappedKind_transition_eq, List.reverse_append,
    List.map_append, List.append_assoc]
theorem tick_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition) :
    TokenRun .tick stateCount start halt route
      action0 action1 action2 action3 restRows := by
  simp only [TokenRun]
  intro left rest T2
  rw [wrappedKind_tick_append]
  change
    (description stateCount start halt route
      action0 action1 action2 action3 restRows).runConfig
        (4 + (4 + (4 + 4))) _ = _
  rw [Description.runConfig_add]
  rw [bit0_false_run]
  rw [Description.runConfig_add]
  rw [bit1_false_run]
  rw [Description.runConfig_add]
  rw [bit2_nat_run]
  rw [bit3_tick_run]
  simp [applyOutputs, wrappedKind_tick_eq, List.reverse_append,
    List.map_append, List.append_assoc]

theorem done_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition) :
    TokenRun .done stateCount start halt route
      action0 action1 action2 action3 restRows := by
  simp only [TokenRun]
  intro left rest T2
  rw [wrappedKind_done_append]
  change
    (description stateCount start halt route
      action0 action1 action2 action3 restRows).runConfig
        (4 + (4 + (4 + 4))) _ = _
  rw [Description.runConfig_add]
  rw [bit0_false_run]
  rw [Description.runConfig_add]
  rw [bit1_false_run]
  rw [Description.runConfig_add]
  rw [bit2_nat_run]
  rw [bit3_done_run]
  simp [applyOutputs, wrappedKind_done_eq, List.reverse_append,
    List.map_append, List.append_assoc]

theorem zero_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition) :
    TokenRun .zero stateCount start halt route
      action0 action1 action2 action3 restRows := by
  simp only [TokenRun]
  intro left rest T2
  rw [wrappedKind_zero_append]
  change
    (description stateCount start halt route
      action0 action1 action2 action3 restRows).runConfig
        (4 + (4 + (4 + 4))) _ = _
  rw [Description.runConfig_add]
  rw [bit0_false_run]
  rw [Description.runConfig_add]
  rw [bit1_true_run]
  rw [Description.runConfig_add]
  rw [bit2_zero_run]
  rw [bit3_zero_run]
  simp [applyOutputs, wrappedKind_zero_eq, List.reverse_append,
    List.map_append, List.append_assoc]
theorem one_run
    (stateCount start halt : Nat)
    (route : Kind -> Nat)
    (action0 action1 action2 : TapeAction)
    (action3 : Kind -> TapeAction)
    (restRows : List Transition) :
    TokenRun .one stateCount start halt route
      action0 action1 action2 action3 restRows := by
  simp only [TokenRun]
  intro left rest T2
  rw [wrappedKind_one_append]
  change
    (description stateCount start halt route
      action0 action1 action2 action3 restRows).runConfig
        (4 + (4 + (4 + 4))) _ = _
  rw [Description.runConfig_add]
  rw [bit0_false_run]
  rw [Description.runConfig_add]
  rw [bit1_true_run]
  rw [Description.runConfig_add]
  rw [bit2_one_run]
  rw [bit3_one_run]
  simp [applyOutputs, wrappedKind_one_eq, List.reverse_append,
    List.map_append, List.append_assoc]

namespace Components

def componentHalt : Nat := 41

def headerRoute : Kind -> Nat
  | .transition => componentHalt
  | _ => invalid
def headerAction3 (_kind : Kind) : TapeAction := keepS

def headerDescription : Description :=
  description 42 0 componentHalt headerRoute
    keepS keepS keepS headerAction3

def firstRoute : Kind -> Nat
  | .tick => componentHalt
  | .done => componentHalt
  | _ => invalid
def firstAction3 : Kind -> TapeAction
  | .tick => writeS (some false)
  | .done => writeS (some true)
  | _ => keepS

def firstDescription : Description :=
  description 42 0 componentHalt firstRoute
    keepS eraseR eraseR firstAction3

def eraseRight : Nat -> Tape Bool -> Tape Bool
  | 0, T => T
  | n + 1, T =>
      eraseRight n (Tape.move Direction.right (Tape.write none T))
def markCurrent (bit : Bool) (T : Tape Bool) : Tape Bool :=
  Tape.write (some bit) T

theorem header_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    headerDescription.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .transition) rest))
          Tape.blank T2) =
      config componentHalt
        (scanTape
          (List.append ((wrappedKind .transition).reverse.map some) left)
          rest)
        Tape.blank T2 := by
  simpa [TokenRun, headerDescription, headerRoute, headerAction3,
      applyOutputs, keepS, TapeAction.apply, TapeAction.stay,
      HeadMove.apply] using
    (transition_run 42 0 componentHalt headerRoute
      keepS keepS keepS headerAction3 [] left rest T2)

theorem first_tick_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    firstDescription.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .tick) rest))
          Tape.blank T2) =
      config componentHalt
        (scanTape
          (List.append ((wrappedKind .tick).reverse.map some) left)
          rest)
        Tape.blank (markCurrent false (eraseRight 2 T2)) := by
  simpa [TokenRun, firstDescription, firstRoute, firstAction3,
      applyOutputs, keepS, eraseR, writeR, writeS,
      TapeAction.apply, TapeAction.stay, HeadMove.apply,
      eraseRight, markCurrent] using
    (tick_run 42 0 componentHalt firstRoute
      keepS eraseR eraseR firstAction3 [] left rest T2)
theorem first_done_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    firstDescription.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .done) rest))
          Tape.blank T2) =
      config componentHalt
        (scanTape
          (List.append ((wrappedKind .done).reverse.map some) left)
          rest)
        Tape.blank (markCurrent true (eraseRight 2 T2)) := by
  simpa [TokenRun, firstDescription, firstRoute, firstAction3,
      applyOutputs, keepS, eraseR, writeR, writeS,
      TapeAction.apply, TapeAction.stay, HeadMove.apply,
      eraseRight, markCurrent] using
    (done_run 42 0 componentHalt firstRoute
      keepS eraseR eraseR firstAction3 [] left rest T2)

def dispatch : Nat := 42

def rowsForMarkerRead
    (source : Nat) (marker : Bool) (target : Nat) : List Transition :=
  allReadCells.map
    (fun read0 =>
      row source read0 none (some marker)
        keepS keepS eraseR target)
def lengthDispatchRows : List Transition :=
  List.append
    (rowsForMarkerRead dispatch false 0)
    (rowsForMarkerRead dispatch true componentHalt)

def lengthRoute : Kind -> Nat
  | .tick => 0
  | .done => componentHalt
  | _ => invalid

def eraseAction3 (_kind : Kind) : TapeAction := eraseR
def lengthDescription : Description :=
  description 43 dispatch componentHalt lengthRoute
    eraseR eraseR eraseR eraseAction3 lengthDispatchRows

theorem length_tick_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    lengthDescription.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .tick) rest))
          Tape.blank T2) =
      config 0
        (scanTape
          (List.append ((wrappedKind .tick).reverse.map some) left)
          rest)
        Tape.blank (eraseRight 4 T2) := by
  simpa [TokenRun, lengthDescription, lengthRoute, eraseAction3,
      applyOutputs, eraseR, writeR, TapeAction.apply, HeadMove.apply,
      eraseRight] using
    (tick_run 43 dispatch componentHalt lengthRoute
      eraseR eraseR eraseR eraseAction3 lengthDispatchRows left rest T2)

theorem length_done_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    lengthDescription.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .done) rest))
          Tape.blank T2) =
      config componentHalt
        (scanTape
          (List.append ((wrappedKind .done).reverse.map some) left)
          rest)
        Tape.blank (eraseRight 4 T2) := by
  simpa [TokenRun, lengthDescription, lengthRoute, eraseAction3,
      applyOutputs, eraseR, writeR, TapeAction.apply, HeadMove.apply,
      eraseRight] using
    (done_run 43 dispatch componentHalt lengthRoute
      eraseR eraseR eraseR eraseAction3 lengthDispatchRows left rest T2)
theorem length_dispatch_false_run
    (T0 T2 : Tape Bool) :
    lengthDescription.runConfig 1
        (config dispatch T0 Tape.blank (markCurrent false T2)) =
      config 0 T0 Tape.blank (eraseRight 1 T2) := by
  cases h0 : T0.head with
  | none =>
      token_driver_simp [h0, lengthDescription, lengthRoute,
        eraseAction3, lengthDispatchRows, rowsForMarkerRead,
        dispatch, componentHalt, markCurrent, eraseRight]
  | some bit =>
      cases bit <;>
        token_driver_simp [h0, lengthDescription, lengthRoute,
          eraseAction3, lengthDispatchRows, rowsForMarkerRead,
          dispatch, componentHalt, markCurrent, eraseRight]

theorem length_dispatch_true_run
    (T0 T2 : Tape Bool) :
    lengthDescription.runConfig 1
        (config dispatch T0 Tape.blank (markCurrent true T2)) =
      config componentHalt T0 Tape.blank (eraseRight 1 T2) := by
  cases h0 : T0.head with
  | none =>
      token_driver_simp [h0, lengthDescription, lengthRoute,
        eraseAction3, lengthDispatchRows, rowsForMarkerRead,
        dispatch, componentHalt, markCurrent, eraseRight]
  | some bit =>
      cases bit <;>
        token_driver_simp [h0, lengthDescription, lengthRoute,
          eraseAction3, lengthDispatchRows, rowsForMarkerRead,
          dispatch, componentHalt, markCurrent, eraseRight]

def wrappedNatTokens : Nat -> List Bool
  | 0 => wrappedKind .done
  | n + 1 => List.append (wrappedKind .tick) (wrappedNatTokens n)
def natFuel : Nat -> Nat
  | 0 => 16
  | n + 1 => 16 + natFuel n

def natOutputCount : Nat -> Nat
  | 0 => 4
  | n + 1 => 4 + natOutputCount n

theorem eraseRight_add (m n : Nat) (T : Tape Bool) :
    eraseRight (m + n) T = eraseRight n (eraseRight m T) := by
  induction m generalizing T with
  | zero =>
      simp [eraseRight]
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [eraseRight]
      rw [ih]
theorem length_tokens_run
    (n : Nat)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    lengthDescription.runConfig (natFuel n)
        (config 0
          (scanTape left
            (List.append (wrappedNatTokens n) rest))
          Tape.blank T2) =
      config componentHalt
        (scanTape
          (List.append ((wrappedNatTokens n).reverse.map some) left)
          rest)
        Tape.blank (eraseRight (natOutputCount n) T2) := by
  induction n generalizing left T2 with
  | zero =>
      simpa [natFuel, natOutputCount, wrappedNatTokens] using
        (length_done_run left rest T2)
  | succ n ih =>
      rw [show
        List.append (wrappedNatTokens (n + 1)) rest =
          List.append (wrappedKind .tick)
            (List.append (wrappedNatTokens n) rest) by
        simp [wrappedNatTokens, List.append_assoc]]
      change lengthDescription.runConfig (16 + natFuel n) _ = _
      rw [Description.runConfig_add]
      rw [length_tick_run]
      rw [ih]
      simp [wrappedNatTokens, natOutputCount, eraseRight_add,
        List.reverse_append, List.map_append, List.append_assoc]

theorem length_after_first_tick_run
    (n : Nat)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    lengthDescription.runConfig (1 + natFuel n)
        (config dispatch
          (scanTape left
            (List.append (wrappedNatTokens n) rest))
          Tape.blank (markCurrent false T2)) =
      config componentHalt
        (scanTape
          (List.append ((wrappedNatTokens n).reverse.map some) left)
          rest)
        Tape.blank (eraseRight (1 + natOutputCount n) T2) := by
  rw [Description.runConfig_add]
  rw [length_dispatch_false_run]
  rw [length_tokens_run]
  rw [eraseRight_add]

theorem length_after_first_done_run
    (T0 T2 : Tape Bool) :
    lengthDescription.runConfig 1
        (config dispatch T0 Tape.blank (markCurrent true T2)) =
      config componentHalt T0 Tape.blank (eraseRight 1 T2) := by
  exact length_dispatch_true_run T0 T2
def cellsRoute : Kind -> Nat
  | .zero => 0
  | .one => 0
  | .tick => componentHalt
  | .done => componentHalt
  | _ => invalid

def cellsAction3 : Kind -> TapeAction
  | .zero => eraseR
  | .one => eraseR
  | .tick => writeS (some false)
  | .done => writeS (some true)
  | _ => keepS

def cellsDescription : Description :=
  description 42 0 componentHalt cellsRoute
    eraseR eraseR eraseR cellsAction3
theorem cells_zero_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    cellsDescription.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .zero) rest))
          Tape.blank T2) =
      config 0
        (scanTape
          (List.append ((wrappedKind .zero).reverse.map some) left)
          rest)
        Tape.blank (eraseRight 4 T2) := by
  simpa [TokenRun, cellsDescription, cellsRoute, cellsAction3,
      applyOutputs, eraseR, writeR, TapeAction.apply, HeadMove.apply,
      eraseRight] using
    (zero_run 42 0 componentHalt cellsRoute
      eraseR eraseR eraseR cellsAction3 [] left rest T2)

theorem cells_one_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    cellsDescription.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .one) rest))
          Tape.blank T2) =
      config 0
        (scanTape
          (List.append ((wrappedKind .one).reverse.map some) left)
          rest)
        Tape.blank (eraseRight 4 T2) := by
  simpa [TokenRun, cellsDescription, cellsRoute, cellsAction3,
      applyOutputs, eraseR, writeR, TapeAction.apply, HeadMove.apply,
      eraseRight] using
    (one_run 42 0 componentHalt cellsRoute
      eraseR eraseR eraseR cellsAction3 [] left rest T2)

theorem cells_tick_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    cellsDescription.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .tick) rest))
          Tape.blank T2) =
      config componentHalt
        (scanTape
          (List.append ((wrappedKind .tick).reverse.map some) left)
          rest)
        Tape.blank (markCurrent false (eraseRight 3 T2)) := by
  simpa [TokenRun, cellsDescription, cellsRoute, cellsAction3,
      applyOutputs, eraseR, writeR, writeS,
      TapeAction.apply, HeadMove.apply, eraseRight, markCurrent] using
    (tick_run 42 0 componentHalt cellsRoute
      eraseR eraseR eraseR cellsAction3 [] left rest T2)
theorem cells_done_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    cellsDescription.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .done) rest))
          Tape.blank T2) =
      config componentHalt
        (scanTape
          (List.append ((wrappedKind .done).reverse.map some) left)
          rest)
        Tape.blank (markCurrent true (eraseRight 3 T2)) := by
  simpa [TokenRun, cellsDescription, cellsRoute, cellsAction3,
      applyOutputs, eraseR, writeR, writeS,
      TapeAction.apply, HeadMove.apply, eraseRight, markCurrent] using
    (done_run 42 0 componentHalt cellsRoute
      eraseR eraseR eraseR cellsAction3 [] left rest T2)

def wrappedCellTokens : List Bool -> List Bool
  | [] => []
  | false :: bits =>
      List.append (wrappedKind .zero) (wrappedCellTokens bits)
  | true :: bits =>
      List.append (wrappedKind .one) (wrappedCellTokens bits)

def cellFuel : List Bool -> Nat
  | [] => 0
  | _ :: bits => 16 + cellFuel bits
def cellOutputCount : List Bool -> Nat
  | [] => 0
  | _ :: bits => 4 + cellOutputCount bits

theorem cells_tokens_run
    (bits : List Bool)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    cellsDescription.runConfig (cellFuel bits)
        (config 0
          (scanTape left
            (List.append (wrappedCellTokens bits) rest))
          Tape.blank T2) =
      config 0
        (scanTape
          (List.append ((wrappedCellTokens bits).reverse.map some) left)
          rest)
        Tape.blank (eraseRight (cellOutputCount bits) T2) := by
  induction bits generalizing left T2 with
  | nil =>
      rfl
  | cons bit bits ih =>
      cases bit with
      | false =>
          rw [show
            List.append (wrappedCellTokens (false :: bits)) rest =
              List.append (wrappedKind .zero)
                (List.append (wrappedCellTokens bits) rest) by
            simp [wrappedCellTokens, List.append_assoc]]
          change cellsDescription.runConfig (16 + cellFuel bits) _ = _
          rw [Description.runConfig_add]
          rw [cells_zero_run]
          rw [ih]
          simp [wrappedCellTokens, cellOutputCount, eraseRight_add,
            List.reverse_append, List.map_append, List.append_assoc]
      | true =>
          rw [show
            List.append (wrappedCellTokens (true :: bits)) rest =
              List.append (wrappedKind .one)
                (List.append (wrappedCellTokens bits) rest) by
            simp [wrappedCellTokens, List.append_assoc]]
          change cellsDescription.runConfig (16 + cellFuel bits) _ = _
          rw [Description.runConfig_add]
          rw [cells_one_run]
          rw [ih]
          simp [wrappedCellTokens, cellOutputCount, eraseRight_add,
            List.reverse_append, List.map_append, List.append_assoc]

theorem cells_then_tick_run
    (bits : List Bool)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    cellsDescription.runConfig (cellFuel bits + 16)
        (config 0
          (scanTape left
            (List.append (wrappedCellTokens bits)
              (List.append (wrappedKind .tick) rest)))
          Tape.blank T2) =
      config componentHalt
        (scanTape
          (List.append
            ((List.append (wrappedCellTokens bits)
              (wrappedKind .tick)).reverse.map some)
            left)
          rest)
        Tape.blank
          (markCurrent false
            (eraseRight (cellOutputCount bits + 3) T2)) := by
  rw [Description.runConfig_add]
  rw [cells_tokens_run]
  rw [cells_tick_run]
  simp [eraseRight_add, List.reverse_append, List.map_append,
    List.append_assoc]
theorem cells_then_done_run
    (bits : List Bool)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    cellsDescription.runConfig (cellFuel bits + 16)
        (config 0
          (scanTape left
            (List.append (wrappedCellTokens bits)
              (List.append (wrappedKind .done) rest)))
          Tape.blank T2) =
      config componentHalt
        (scanTape
          (List.append
            ((List.append (wrappedCellTokens bits)
              (wrappedKind .done)).reverse.map some)
            left)
          rest)
        Tape.blank
          (markCurrent true
            (eraseRight (cellOutputCount bits + 3) T2)) := by
  rw [Description.runConfig_add]
  rw [cells_tokens_run]
  rw [cells_done_run]
  simp [eraseRight_add, List.reverse_append, List.map_append,
    List.append_assoc]

end Components

namespace WrappedStream

/-!
This component scans an arbitrary stream of wrapped raw bits.  The physical
{lit}`false,false` pair following the wrapped stream is its boundary.  Tape 1 is
preserved, and a caller-selected tape-2 action is applied exactly once per raw
bit.  It is the small loop needed both for the full parsed-layout pass and for
copying a selected contiguous field.
-/

def loop : Nat := 0
def second : Nat := 1
def payload : Nat := 2
def payloadFalse : Nat := 3
def payloadTrue : Nat := 4
def halt : Nat := 5

def rowsForRead
    (source : Nat) (read0 : Option Bool)
    (action0 action2 : TapeAction) (target : Nat) : List Transition :=
  allReadCells.map fun read2 =>
    row source read0 none read2 action0 keepS action2 target
def rows (actionFalse actionTrue : TapeAction) : List Transition :=
  [ rowsForRead loop (some false) keepR keepS second
  , rowsForRead second (some true) keepR keepS payload
  , rowsForRead second (some false) keepL keepS halt
  , rowsForRead payload (some false) keepR keepS payloadFalse
  , rowsForRead payload (some true) keepR keepS payloadTrue
  , rowsForRead payloadFalse (some true) keepR actionFalse loop
  , rowsForRead payloadTrue (some false) keepR actionTrue loop ].flatten

def description (actionFalse actionTrue : TapeAction) : Description :=
  ThreeTape.description 6 loop halt (rows actionFalse actionTrue)

syntax "wrapped_stream_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| wrapped_stream_simp [$lemmas,*]) =>
      `(tactic|
        simp (config := { maxSteps := 1000000 }) [
          ThreeTape.row, ThreeTape.config, ThreeTape.description,
          ThreeTape.keepL, ThreeTape.keepR, ThreeTape.keepS,
          ThreeTape.writeL, ThreeTape.writeR, ThreeTape.writeS,
          ThreeTape.eraseL, ThreeTape.eraseR,
          ThreeTape.writeBitL, ThreeTape.writeBitR,
          Description.applyActions_three, Description.runConfig,
          Description.stepConfig, Description.lookupTransition,
          Description.Matches, TapeAction.apply, TapeAction.stay,
          HeadMove.apply, Tape.blank, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight, tapeAtCells,
          description, rows, rowsForRead, loop, second, payload,
          payloadFalse, payloadTrue, halt, allReadCells, List.find?,
          scanTape, wrappedRawBit, cellsCodeBits, cellCodeBits,
          encodeCodeWordAsInput, encodeCodeSymbolAsInput, encodeCell,
          List.reverse_append, List.map_append, List.append_assoc,
          $lemmas,*])

theorem false_run
    (actionFalse actionTrue : TapeAction)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description actionFalse actionTrue).runConfig 4
        (config loop
          (scanTape left (List.append (wrappedRawBit false) rest))
          Tape.blank T2) =
      config loop
        (scanTape
          (List.append ((wrappedRawBit false).reverse.map some) left)
          rest)
        Tape.blank (actionFalse.apply T2) := by
  cases rest <;>
    cases h2 : T2.head with
    | none => wrapped_stream_simp [h2]
    | some bit => cases bit <;> wrapped_stream_simp [h2]
theorem true_run
    (actionFalse actionTrue : TapeAction)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description actionFalse actionTrue).runConfig 4
        (config loop
          (scanTape left (List.append (wrappedRawBit true) rest))
          Tape.blank T2) =
      config loop
        (scanTape
          (List.append ((wrappedRawBit true).reverse.map some) left)
          rest)
        Tape.blank (actionTrue.apply T2) := by
  cases rest <;>
    cases h2 : T2.head with
    | none => wrapped_stream_simp [h2]
    | some bit => cases bit <;> wrapped_stream_simp [h2]

theorem boundary_run
    (actionFalse actionTrue : TapeAction)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    (description actionFalse actionTrue).runConfig 2
        (config loop (scanTape left (false :: false :: rest)) Tape.blank T2) =
      config halt (scanTape left (false :: false :: rest)) Tape.blank T2 := by
  cases rest <;>
    cases h2 : T2.head with
    | none => wrapped_stream_simp [h2]
    | some bit => cases bit <;> wrapped_stream_simp [h2]

def applyBits
    (actionFalse actionTrue : TapeAction) : List Bool -> Tape Bool -> Tape Bool
  | [], T => T
  | false :: bits, T =>
      applyBits actionFalse actionTrue bits (actionFalse.apply T)
  | true :: bits, T =>
      applyBits actionFalse actionTrue bits (actionTrue.apply T)
def fuel (bits : List Bool) : Nat := 4 * bits.length + 2

theorem run
    (actionFalse actionTrue : TapeAction)
    (bits : List Bool)
    (left : List (Option Bool)) (boundaryRest : List Bool)
    (T2 : Tape Bool) :
    (description actionFalse actionTrue).runConfig (fuel bits)
        (config loop
          (scanTape left
            (List.append (AcceptConfigCopy.wrappedBits bits)
              (false :: false :: boundaryRest)))
          Tape.blank T2) =
      config halt
        (scanTape
          (List.append
            ((AcceptConfigCopy.wrappedBits bits).reverse.map some) left)
          (false :: false :: boundaryRest))
        Tape.blank (applyBits actionFalse actionTrue bits T2) := by
  induction bits generalizing left T2 with
  | nil =>
      simpa [fuel, AcceptConfigCopy.wrappedBits, applyBits] using
        boundary_run actionFalse actionTrue left boundaryRest T2
  | cons bit bits ih =>
      rw [show fuel (bit :: bits) = 4 + fuel bits by
        simp [fuel]
        lia]
      rw [Description.runConfig_add]
      rw [AcceptConfigCopy.wrappedBits_cons_append]
      cases bit with
      | false =>
          rw [false_run]
          rw [ih]
          simp [applyBits, AcceptConfigCopy.wrappedBits,
            AcceptConfigCopy.wrappedBit, List.reverse_append,
            List.map_append, List.append_assoc]
      | true =>
          rw [true_run]
          rw [ih]
          simp [applyBits, AcceptConfigCopy.wrappedBits,
            AcceptConfigCopy.wrappedBit, List.reverse_append,
            List.map_append, List.append_assoc]

end WrappedStream

namespace PairStream

/-!
Pair wrapped raw bits on tape 0 with a visible raw counter on tape 2.  Each
counter cell advances both cursors by one logical raw bit; the machine halts
without moving either cursor when tape 2 reaches its right blank.
-/

def loop : Nat := 0
def second : Nat := 1
def payload : Nat := 2
def payloadFalse : Nat := 3
def payloadTrue : Nat := 4
def halt : Nat := 5
def rowsForPairRead
    (source : Nat) (read0 read2 : Option Bool)
    (action0 action2 : TapeAction) (target : Nat) : List Transition :=
  [row source read0 none read2 action0 keepS action2 target]

def rowsForCounterRead
    (source : Nat) (read2 : Option Bool)
    (action0 action2 : TapeAction) (target : Nat) : List Transition :=
  allReadCells.map fun read0 =>
    row source read0 none read2 action0 keepS action2 target

def rows : List Transition :=
  [ rowsForCounterRead loop none keepS keepS halt
  , rowsForPairRead loop (some false) (some false) keepR keepS second
  , rowsForPairRead loop (some false) (some true) keepR keepS second
  , rowsForSourceRead second (some true) keepR keepS keepS payload
  , rowsForSourceRead payload (some false) keepR keepS keepS payloadFalse
  , rowsForSourceRead payload (some true) keepR keepS keepS payloadTrue
  , rowsForSourceRead payloadFalse (some true) keepR keepS keepR loop
  , rowsForSourceRead payloadTrue (some false) keepR keepS keepR loop ].flatten
def description : Description :=
  ThreeTape.description 6 loop halt rows

def counterTape
    (left : List (Option Bool)) (bits : List Bool) : Tape Bool :=
  tapeAtCells left (List.append (bits.map some) [none])

syntax "pair_stream_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pair_stream_simp [$lemmas,*]) =>
      `(tactic|
        simp (config := { maxSteps := 1000000 }) [
          ThreeTape.row, ThreeTape.config, ThreeTape.description,
          ThreeTape.keepL, ThreeTape.keepR, ThreeTape.keepS,
          Description.applyActions_three, Description.runConfig,
          Description.stepConfig, Description.lookupTransition,
          Description.Matches, TapeAction.apply, TapeAction.stay,
          HeadMove.apply, Tape.blank, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight, tapeAtCells,
          description, rows, rowsForPairRead, rowsForCounterRead,
          rowsForSourceRead,
          loop, second, payload, payloadFalse, payloadTrue, halt,
          allReadCells, List.find?, scanTape, counterTape, wrappedRawBit,
          cellsCodeBits, cellCodeBits, encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, encodeCell, List.reverse_append,
          List.map_append, List.append_assoc, $lemmas,*])

theorem false_run
    (left0 left2 : List (Option Bool))
    (rest0 : List Bool) (counterBit : Bool) (rest2 : List Bool) :
    description.runConfig 4
        (config loop
          (scanTape left0 (List.append (wrappedRawBit false) rest0))
          Tape.blank (counterTape left2 (counterBit :: rest2))) =
      config loop
        (scanTape
          (List.append ((wrappedRawBit false).reverse.map some) left0)
          rest0)
        Tape.blank
        (counterTape (some counterBit :: left2) rest2) := by
  cases rest0 <;> cases counterBit <;> cases rest2 <;>
    pair_stream_simp []
theorem true_run
    (left0 left2 : List (Option Bool))
    (rest0 : List Bool) (counterBit : Bool) (rest2 : List Bool) :
    description.runConfig 4
        (config loop
          (scanTape left0 (List.append (wrappedRawBit true) rest0))
          Tape.blank (counterTape left2 (counterBit :: rest2))) =
      config loop
        (scanTape
          (List.append ((wrappedRawBit true).reverse.map some) left0)
          rest0)
        Tape.blank
        (counterTape (some counterBit :: left2) rest2) := by
  cases rest0 <;> cases counterBit <;> cases rest2 <;>
    pair_stream_simp []

theorem finish_run
    (T0 : Tape Bool) (left2 : List (Option Bool)) :
    description.runConfig 1
        (config loop T0 Tape.blank (counterTape left2 [])) =
      config halt T0 Tape.blank (counterTape left2 []) := by
  cases h0 : T0.head with
  | none => pair_stream_simp [h0]
  | some bit => cases bit <;> pair_stream_simp [h0]

def fuel (counter : List Bool) : Nat := 4 * counter.length + 1
theorem run
    (source counter : List Bool)
    (left0 left2 : List (Option Bool)) (rest0 : List Bool)
    (hlength : counter.length <= source.length) :
    description.runConfig (fuel counter)
        (config loop
          (scanTape left0
            (List.append (AcceptConfigCopy.wrappedBits source) rest0))
          Tape.blank (counterTape left2 counter)) =
      config halt
        (scanTape
          (List.append
            ((AcceptConfigCopy.wrappedBits (source.take counter.length)).reverse.map
              some)
            left0)
          (List.append
            (AcceptConfigCopy.wrappedBits (source.drop counter.length)) rest0))
        Tape.blank
        (counterTape
          (List.append (counter.reverse.map some) left2) []) := by
  induction counter generalizing source left0 left2 with
  | nil =>
      simpa [fuel, AcceptConfigCopy.wrappedBits] using
        finish_run
          (scanTape left0
            (List.append (AcceptConfigCopy.wrappedBits source) rest0))
          left2
  | cons counterBit counter ih =>
      cases source with
      | nil => simp at hlength
      | cons sourceBit source =>
          have htail : counter.length <= source.length := by
            simpa using hlength
          rw [show fuel (counterBit :: counter) = 4 + fuel counter by
            simp [fuel]
            lia]
          rw [Description.runConfig_add]
          rw [AcceptConfigCopy.wrappedBits_cons_append]
          cases sourceBit with
          | false =>
              rw [false_run]
              rw [ih source
                (List.append ((wrappedRawBit false).reverse.map some) left0)
                (some counterBit :: left2) htail]
              simp [List.take, List.drop, AcceptConfigCopy.wrappedBits,
                AcceptConfigCopy.wrappedBit, List.reverse_cons,
                List.reverse_append, List.map_append, List.append_assoc]
          | true =>
              rw [true_run]
              rw [ih source
                (List.append ((wrappedRawBit true).reverse.map some) left0)
                (some counterBit :: left2) htail]
              simp [List.take, List.drop, AcceptConfigCopy.wrappedBits,
                AcceptConfigCopy.wrappedBit, List.reverse_cons,
                List.reverse_append, List.map_append, List.append_assoc]

end PairStream

end DirectTokenDriver
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
