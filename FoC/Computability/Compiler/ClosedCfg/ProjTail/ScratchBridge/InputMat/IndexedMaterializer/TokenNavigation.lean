import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.AcceptConfigLocator
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.TokenDriver
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic

set_option doc.verso true

/-!
Exact primary rewinds, marker scans, and marked erasure for routed token streams.
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
namespace PrimaryRewind

/-!
Rewind tape 0 by whole wrapped raw-bit cells to a blank marker immediately to
the left of the stream.  The marker replaces a known {lit}`true` cell; the final
step restores that cell and leaves the head on the first wrapped bit.  Both
other tapes are preserved exactly.
-/

def loop : Nat := 0
def inspect : Nat := 1
def middle1 : Nat := 2
def middle2 : Nat := 3
def halt : Nat := 4

def rowsForRead
    (source : Nat) (read0 : Option Bool)
    (action0 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read1 read2 =>
    row source read0 read1 read2 action0 keepS keepS target
def rows : List Transition :=
  [ rowsForRead loop none keepL inspect
  , rowsForRead loop (some false) keepL inspect
  , rowsForRead loop (some true) keepL inspect
  , rowsForRead inspect none (writeR (some true)) halt
  , rowsForRead inspect (some false) keepL middle1
  , rowsForRead inspect (some true) keepL middle1
  , rowsForRead middle1 (some false) keepL middle2
  , rowsForRead middle1 (some true) keepL middle2
  , rowsForRead middle2 (some false) keepL loop
  , rowsForRead middle2 (some true) keepL loop ].flatten

def description : Description :=
  ThreeTape.description 5 loop halt rows

syntax "primary_rewind_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| primary_rewind_simp [$lemmas,*]) =>
      `(tactic|
        simp (config := { maxSteps := 1000000 }) [
          ThreeTape.row, ThreeTape.config, ThreeTape.description,
          ThreeTape.keepL, ThreeTape.keepR, ThreeTape.keepS,
          ThreeTape.writeR, Description.applyActions_three,
          Description.runConfig, Description.stepConfig,
          Description.lookupTransition, Description.Matches,
          TapeAction.apply, TapeAction.stay, HeadMove.apply,
          Tape.blank, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight, tapeAtCells,
          description, rows, rowsForRead, loop, inspect, middle1,
          middle2, halt, allReads2, allReadCells, List.find?,
          scanTape, wrappedRawBit, cellsCodeBits, cellCodeBits,
          encodeCodeWordAsInput, encodeCodeSymbolAsInput, encodeCell,
          List.reverse_append, List.map_append, List.append_assoc,
          $lemmas,*])

theorem false_step
    (left : List (Option Bool)) (rest : List Bool)
    (T1 T2 : Tape Bool) :
    description.runConfig 4
        (config loop
          (scanTape
            (List.append ((wrappedRawBit false).reverse.map some) left)
            rest)
          T1 T2) =
      config loop
        (scanTape left (List.append (wrappedRawBit false) rest))
        T1 T2 := by
  cases rest with
  | nil =>
      cases h1 : T1.head with
      | none =>
          cases h2 : T2.head with
          | none => primary_rewind_simp [h1, h2]
          | some bit => cases bit <;> primary_rewind_simp [h1, h2]
      | some bit1 =>
          cases bit1 <;>
            cases h2 : T2.head with
            | none => primary_rewind_simp [h1, h2]
            | some bit2 => cases bit2 <;> primary_rewind_simp [h1, h2]
  | cons head tail =>
      cases head <;>
        cases h1 : T1.head with
        | none =>
            cases h2 : T2.head with
            | none => primary_rewind_simp [h1, h2]
            | some bit => cases bit <;> primary_rewind_simp [h1, h2]
        | some bit1 =>
            cases bit1 <;>
              cases h2 : T2.head with
              | none => primary_rewind_simp [h1, h2]
              | some bit2 => cases bit2 <;> primary_rewind_simp [h1, h2]
theorem true_step
    (left : List (Option Bool)) (rest : List Bool)
    (T1 T2 : Tape Bool) :
    description.runConfig 4
        (config loop
          (scanTape
            (List.append ((wrappedRawBit true).reverse.map some) left)
            rest)
          T1 T2) =
      config loop
        (scanTape left (List.append (wrappedRawBit true) rest))
        T1 T2 := by
  cases rest with
  | nil =>
      cases h1 : T1.head with
      | none =>
          cases h2 : T2.head with
          | none => primary_rewind_simp [h1, h2]
          | some bit => cases bit <;> primary_rewind_simp [h1, h2]
      | some bit1 =>
          cases bit1 <;>
            cases h2 : T2.head with
            | none => primary_rewind_simp [h1, h2]
            | some bit2 => cases bit2 <;> primary_rewind_simp [h1, h2]
  | cons head tail =>
      cases head <;>
        cases h1 : T1.head with
        | none =>
            cases h2 : T2.head with
            | none => primary_rewind_simp [h1, h2]
            | some bit => cases bit <;> primary_rewind_simp [h1, h2]
        | some bit1 =>
            cases bit1 <;>
              cases h2 : T2.head with
              | none => primary_rewind_simp [h1, h2]
              | some bit2 => cases bit2 <;> primary_rewind_simp [h1, h2]

theorem marker_finish
    (left : List (Option Bool)) (rest : List Bool)
    (T1 T2 : Tape Bool) :
    description.runConfig 2
        (config loop (scanTape (none :: left) rest) T1 T2) =
      config halt (scanTape (some true :: left) rest) T1 T2 := by
  cases rest with
  | nil =>
      cases h1 : T1.head with
      | none =>
          cases h2 : T2.head with
          | none => primary_rewind_simp [h1, h2]
          | some bit => cases bit <;> primary_rewind_simp [h1, h2]
      | some bit1 =>
          cases bit1 <;>
            cases h2 : T2.head with
            | none => primary_rewind_simp [h1, h2]
            | some bit2 => cases bit2 <;> primary_rewind_simp [h1, h2]
  | cons head tail =>
      cases head <;>
        cases h1 : T1.head with
        | none =>
            cases h2 : T2.head with
            | none => primary_rewind_simp [h1, h2]
            | some bit => cases bit <;> primary_rewind_simp [h1, h2]
        | some bit1 =>
            cases bit1 <;>
              cases h2 : T2.head with
              | none => primary_rewind_simp [h1, h2]
              | some bit2 => cases bit2 <;> primary_rewind_simp [h1, h2]

theorem wrappedBits_append (u v : List Bool) :
    AcceptConfigCopy.wrappedBits (List.append u v) =
      List.append (AcceptConfigCopy.wrappedBits u)
        (AcceptConfigCopy.wrappedBits v) := by
  induction u with
  | nil => rfl
  | cons bit u ih =>
      change
        List.append (AcceptConfigCopy.wrappedBit bit)
            (AcceptConfigCopy.wrappedBits (List.append u v)) =
          List.append
            (List.append (AcceptConfigCopy.wrappedBit bit)
              (AcceptConfigCopy.wrappedBits u))
            (AcceptConfigCopy.wrappedBits v)
      rw [ih]
      exact (List.append_assoc _ _ _).symm
theorem wrappedBits_reverse_cons (bit : Bool) (bits : List Bool) :
    AcceptConfigCopy.wrappedBits (bit :: bits).reverse =
      List.append (AcceptConfigCopy.wrappedBits bits.reverse)
        (wrappedRawBit bit) := by
  calc
    AcceptConfigCopy.wrappedBits (bit :: bits).reverse =
        AcceptConfigCopy.wrappedBits
          (List.append bits.reverse [bit]) := by
            simp only [List.reverse_cons, List.append_eq]
    _ = List.append (AcceptConfigCopy.wrappedBits bits.reverse)
          (AcceptConfigCopy.wrappedBits [bit]) :=
        wrappedBits_append bits.reverse [bit]
    _ = List.append (AcceptConfigCopy.wrappedBits bits.reverse)
          (wrappedRawBit bit) := by
        simp [AcceptConfigCopy.wrappedBits, AcceptConfigCopy.wrappedBit,
          List.append_eq]

def fuel (bits : List Bool) : Nat := 4 * bits.length + 2

theorem run_rev
    (revBits : List Bool)
    (left : List (Option Bool)) (rest : List Bool)
    (T1 T2 : Tape Bool) :
    description.runConfig (fuel revBits)
        (config loop
          (scanTape
            (List.append
              ((AcceptConfigCopy.wrappedBits revBits.reverse).reverse.map some)
              (none :: left))
            rest)
          T1 T2) =
      config halt
        (scanTape (some true :: left)
          (List.append
            (AcceptConfigCopy.wrappedBits revBits.reverse) rest))
        T1 T2 := by
  induction revBits generalizing rest with
  | nil =>
      simpa [fuel, AcceptConfigCopy.wrappedBits] using
        marker_finish left rest T1 T2
  | cons bit revBits ih =>
      rw [show fuel (bit :: revBits) = 4 + fuel revBits by
        simp [fuel]
        lia]
      rw [Description.runConfig_add]
      have hshape :
          List.append
              ((AcceptConfigCopy.wrappedBits
                (bit :: revBits).reverse).reverse.map some)
              (none :: left) =
            List.append ((wrappedRawBit bit).reverse.map some)
              (List.append
                ((AcceptConfigCopy.wrappedBits revBits.reverse).reverse.map
                  some)
                (none :: left)) := by
        rw [wrappedBits_reverse_cons]
        cases bit <;>
          simp [AcceptConfigCopy.wrappedBits,
            AcceptConfigCopy.wrappedBit, wrappedRawBit,
            List.reverse_append, List.map_append, List.append_assoc]
      rw [hshape]
      cases bit with
      | false =>
          rw [false_step]
          rw [ih]
          rw [wrappedBits_reverse_cons]
          simp [List.reverse_cons,
            AcceptConfigCopy.wrappedBits, AcceptConfigCopy.wrappedBit,
            wrappedRawBit, List.append_assoc]
      | true =>
          rw [true_step]
          rw [ih]
          rw [wrappedBits_reverse_cons]
          simp [List.reverse_cons,
            AcceptConfigCopy.wrappedBits, AcceptConfigCopy.wrappedBit,
            wrappedRawBit, List.append_assoc]
theorem run
    (bits : List Bool)
    (left : List (Option Bool)) (rest : List Bool)
    (T1 T2 : Tape Bool) :
    description.runConfig (fuel bits)
        (config loop
          (scanTape
            (List.append
              ((AcceptConfigCopy.wrappedBits bits).reverse.map some)
              (none :: left))
            rest)
          T1 T2) =
      config halt
        (scanTape (some true :: left)
          (List.append (AcceptConfigCopy.wrappedBits bits) rest))
        T1 T2 := by
  simpa [fuel] using run_rev bits.reverse left rest T1 T2

end PrimaryRewind

namespace MarkerScanLeft

/-!
Return tape 2 from a right blank across an arbitrary blank span to a temporary
{lit}`true` marker.  The marker is erased in place, so the final head is exactly the
marked cell and the other two tapes are unchanged.
-/

def enter : Nat := 0
def scan : Nat := 1
def halt : Nat := 2

def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action2 : TapeAction) (target : Nat) : List Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 keepS keepS action2 target
def rows : List Transition :=
  [ rowsForTape2Read enter none keepL scan
  , rowsForTape2Read scan none keepL scan
  , rowsForTape2Read scan (some true) (writeS none) halt ].flatten

def description : Description :=
  ThreeTape.description 3 enter halt rows

syntax "marker_scan_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| marker_scan_simp [$lemmas,*]) =>
      `(tactic|
        three_tape_step [description, rows, rowsForTape2Read,
          allReads2, allReadCells, List.find?, enter, scan, halt, $lemmas,*])

theorem enter_step
    (T0 T1 : Tape Bool) (cell : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        (config enter T0 T1
          (tapeAtCells (cell :: left) (none :: right))) =
      config scan T0 T1
        (tapeAtCells left (cell :: none :: right)) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => marker_scan_simp [tapeAtCells, h0, h1]
      | some bit => cases bit <;> marker_scan_simp [tapeAtCells, h0, h1]
  | some bit0 =>
      cases bit0 <;>
        cases h1 : T1.head with
        | none => marker_scan_simp [tapeAtCells, h0, h1]
        | some bit1 => cases bit1 <;>
            marker_scan_simp [tapeAtCells, h0, h1]
theorem blank_step
    (T0 T1 : Tape Bool) (next : Option Bool)
    (left right : List (Option Bool)) :
    description.runConfig 1
        (config scan T0 T1
          (tapeAtCells (next :: left) (none :: right))) =
      config scan T0 T1
        (tapeAtCells left (next :: none :: right)) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => marker_scan_simp [tapeAtCells, h0, h1]
      | some bit => cases bit <;> marker_scan_simp [tapeAtCells, h0, h1]
  | some bit0 =>
      cases bit0 <;>
        cases h1 : T1.head with
        | none => marker_scan_simp [tapeAtCells, h0, h1]
        | some bit1 => cases bit1 <;>
            marker_scan_simp [tapeAtCells, h0, h1]

theorem marker_step
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    description.runConfig 1
        (config scan T0 T1 (tapeAtCells left (some true :: right))) =
      config halt T0 T1 (tapeAtCells left (none :: right)) := by
  cases h0 : T0.head with
  | none =>
      cases h1 : T1.head with
      | none => marker_scan_simp [tapeAtCells, h0, h1]
      | some bit => cases bit <;> marker_scan_simp [tapeAtCells, h0, h1]
  | some bit0 =>
      cases bit0 <;>
        cases h1 : T1.head with
        | none => marker_scan_simp [tapeAtCells, h0, h1]
        | some bit1 => cases bit1 <;>
            marker_scan_simp [tapeAtCells, h0, h1]

theorem replicate_none_append_cons
    (n : Nat) (right : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool)) (none :: right) =
      none :: List.append (List.replicate n (none : Option Bool)) right := by
  exact
    FoC.Computability.CommonGround.FiniteTransducers.replicate_none_append_none_cons
      n right
theorem scan_blanks_to_marker
    (n : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    description.runConfig (n + 2)
        (config scan T0 T1
          (tapeAtCells
            (List.append (List.replicate n (none : Option Bool))
              (some true :: left))
            (none :: right))) =
      config halt T0 T1
        (tapeAtCells left
          (none :: List.append
            (List.replicate (n + 1) (none : Option Bool)) right)) := by
  induction n generalizing right with
  | zero =>
      rw [show 0 + 2 = 1 + 1 by rfl]
      rw [Description.runConfig_add]
      simp only [List.replicate_zero, List.append_eq, List.nil_append]
      rw [blank_step]
      rw [marker_step]
      rfl
  | succ n ih =>
      rw [show (n + 1) + 2 = 1 + (n + 2) by lia]
      rw [Description.runConfig_add]
      simp only [List.replicate_succ, List.append_eq, List.cons_append]
      rw [blank_step]
      have hih := ih (none :: right)
      simp only [List.append_eq] at hih
      rw [hih]
      have hshift := replicate_none_append_cons n right
      simp only [List.append_eq] at hshift
      simp only [List.replicate_succ, List.cons_append]
      rw [hshift]

def sourceTape
    (left : List (Option Bool)) (n : Nat) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate n (none : Option Bool))
      (some true :: left))
    [none]

def targetTape
    (left : List (Option Bool)) (n : Nat) : Tape Bool :=
  tapeAtCells left
    (none :: List.append
      (List.replicate n (none : Option Bool)) [none])
def fuel (n : Nat) : Nat := n + 2

theorem run
    (n : Nat) (T0 T1 : Tape Bool) (left : List (Option Bool)) :
    description.runConfig (fuel n)
        (config enter T0 T1 (sourceTape left n)) =
      config halt T0 T1 (targetTape left n) := by
  rw [fuel]
  rw [show n + 2 = 1 + (n + 1) by lia]
  rw [Description.runConfig_add]
  rw [sourceTape, show
    List.append (List.replicate n (none : Option Bool))
        (some true :: left) =
      List.append (List.replicate n (none : Option Bool))
        (some true :: left) by rfl]
  cases n with
  | zero =>
      simp only [List.replicate_zero, List.append_eq, List.nil_append]
      rw [enter_step]
      simpa [targetTape, tapeAtCells] using
        marker_step T0 T1 left [none]
  | succ n =>
      simp only [List.replicate_succ, List.append_eq, List.cons_append]
      rw [enter_step]
      simpa [targetTape, List.replicate_succ, List.append_assoc,
        tapeAtCells] using
        scan_blanks_to_marker n T0 T1 left [none]

end MarkerScanLeft

namespace MarkedErase

/-!
Erase one tape-2 cell for every wrapped raw bit.  One wrapped-cell start may
be replaced by {lit}`none`; at that position the machine restores the source's
known leading {lit}`false` and writes a temporary {lit}`true` marker on tape 2 instead
of a blank.  This transfers the reject-branch subtraction point from tape 0
to the otherwise blank output gap.
-/

def loop : Nat := 0
def second : Nat := 1
def payload : Nat := 2
def payloadFalse : Nat := 3
def payloadTrue : Nat := 4
def halt : Nat := 5
def markedSecond : Nat := 6
def markedPayload : Nat := 7
def markedFalse : Nat := 8
def markedTrue : Nat := 9
def rowsForRead
    (source : Nat) (read0 : Option Bool)
    (action0 action2 : TapeAction) (target : Nat) : List Transition :=
  allReadCells.map fun read2 =>
    row source read0 none read2 action0 keepS action2 target

def rows : List Transition :=
  [ rowsForRead loop (some false) keepR keepS second
  , rowsForRead loop none (writeR (some false)) keepS markedSecond
  , rowsForRead second (some true) keepR keepS payload
  , rowsForRead second (some false) keepL keepS halt
  , rowsForRead payload (some false) keepR keepS payloadFalse
  , rowsForRead payload (some true) keepR keepS payloadTrue
  , rowsForRead payloadFalse (some true) keepR eraseR loop
  , rowsForRead payloadTrue (some false) keepR eraseR loop
  , rowsForRead markedSecond (some true) keepR keepS markedPayload
  , rowsForRead markedPayload (some false) keepR keepS markedFalse
  , rowsForRead markedPayload (some true) keepR keepS markedTrue
  , rowsForRead markedFalse (some true) keepR (writeBitR true) loop
  , rowsForRead markedTrue (some false) keepR (writeBitR true) loop ].flatten

def description : Description :=
  ThreeTape.description 10 loop halt rows
def scanOptionTape
    (left cells : List (Option Bool)) : Tape Bool :=
  tapeAtCells left (List.append cells [none])

def wrappedOptions (bit : Bool) : List (Option Bool) :=
  (wrappedRawBit bit).map some

def markedOptions (bit : Bool) : List (Option Bool) :=
  none :: (wrappedRawBit bit).tail.map some

syntax "marked_erase_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| marked_erase_simp [$lemmas,*]) =>
      `(tactic|
        simp (config := { maxSteps := 1000000 }) [
          ThreeTape.row, ThreeTape.config, ThreeTape.description,
          ThreeTape.keepL, ThreeTape.keepR, ThreeTape.keepS,
          ThreeTape.writeR, ThreeTape.eraseR, ThreeTape.writeBitR,
          Description.applyActions_three, Description.runConfig,
          Description.stepConfig, Description.lookupTransition,
          Description.Matches, TapeAction.apply, TapeAction.stay,
          HeadMove.apply, Tape.blank, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight, tapeAtCells,
          description, rows, rowsForRead, loop, second, payload,
          payloadFalse, payloadTrue, halt, markedSecond, markedPayload,
          markedFalse, markedTrue, allReadCells, List.find?,
          scanOptionTape, wrappedOptions, markedOptions, wrappedRawBit,
          cellsCodeBits, cellCodeBits, encodeCodeWordAsInput,
          encodeCodeSymbolAsInput, encodeCell, List.reverse_append,
          List.map_append, List.append_assoc, $lemmas,*])
theorem false_run
    (left rest : List (Option Bool)) (T2 : Tape Bool) :
    description.runConfig 4
        (config loop
          (scanOptionTape left
            (List.append (wrappedOptions false) rest))
          Tape.blank T2) =
      config loop
        (scanOptionTape
          (List.append (wrappedOptions false).reverse left) rest)
        Tape.blank (eraseR.apply T2) := by
  cases rest <;>
    cases h2 : T2.head with
    | none => marked_erase_simp [h2]
    | some bit => cases bit <;> marked_erase_simp [h2]

theorem true_run
    (left rest : List (Option Bool)) (T2 : Tape Bool) :
    description.runConfig 4
        (config loop
          (scanOptionTape left
            (List.append (wrappedOptions true) rest))
          Tape.blank T2) =
      config loop
        (scanOptionTape
          (List.append (wrappedOptions true).reverse left) rest)
        Tape.blank (eraseR.apply T2) := by
  cases rest <;>
    cases h2 : T2.head with
    | none => marked_erase_simp [h2]
    | some bit => cases bit <;> marked_erase_simp [h2]

theorem marked_false_run
    (left rest : List (Option Bool)) (T2 : Tape Bool) :
    description.runConfig 4
        (config loop
          (scanOptionTape left
            (List.append (markedOptions false) rest))
          Tape.blank T2) =
      config loop
        (scanOptionTape
          (List.append (wrappedOptions false).reverse left) rest)
        Tape.blank ((writeBitR true).apply T2) := by
  cases rest <;>
    cases h2 : T2.head with
    | none => marked_erase_simp [h2]
    | some bit => cases bit <;> marked_erase_simp [h2]
theorem marked_true_run
    (left rest : List (Option Bool)) (T2 : Tape Bool) :
    description.runConfig 4
        (config loop
          (scanOptionTape left
            (List.append (markedOptions true) rest))
          Tape.blank T2) =
      config loop
        (scanOptionTape
          (List.append (wrappedOptions true).reverse left) rest)
        Tape.blank ((writeBitR true).apply T2) := by
  cases rest <;>
    cases h2 : T2.head with
    | none => marked_erase_simp [h2]
    | some bit => cases bit <;> marked_erase_simp [h2]

theorem boundary_run
    (left rest : List (Option Bool)) (T2 : Tape Bool) :
    description.runConfig 2
        (config loop
          (scanOptionTape left
            (some false :: some false :: rest))
          Tape.blank T2) =
      config halt
        (scanOptionTape left (some false :: some false :: rest))
        Tape.blank T2 := by
  cases rest <;>
    cases h2 : T2.head with
    | none => marked_erase_simp [h2]
    | some bit => cases bit <;> marked_erase_simp [h2]

def wrappedOptionsWord (bits : List Bool) : List (Option Bool) :=
  (AcceptConfigCopy.wrappedBits bits).map some
def eraseBits : List Bool -> Tape Bool -> Tape Bool
  | [], T => T
  | _ :: bits, T => eraseBits bits (eraseR.apply T)

theorem normal_run
    (bits : List Bool) (left rest : List (Option Bool))
    (T2 : Tape Bool) :
    description.runConfig (4 * bits.length)
        (config loop
          (scanOptionTape left
            (List.append (wrappedOptionsWord bits) rest))
          Tape.blank T2) =
      config loop
        (scanOptionTape
          (List.append (wrappedOptionsWord bits).reverse left) rest)
        Tape.blank (eraseBits bits T2) := by
  induction bits generalizing left T2 with
  | nil => rfl
  | cons bit bits ih =>
      rw [show 4 * (bit :: bits).length = 4 + 4 * bits.length by
        simp
        lia]
      rw [Description.runConfig_add]
      have hshape :
          List.append (wrappedOptionsWord (bit :: bits)) rest =
            List.append (wrappedOptions bit)
              (List.append (wrappedOptionsWord bits) rest) := by
        cases bit <;>
          simp [wrappedOptionsWord, wrappedOptions,
            AcceptConfigCopy.wrappedBits, AcceptConfigCopy.wrappedBit,
            wrappedRawBit, List.map_append, List.append_assoc]
      rw [hshape]
      cases bit with
      | false =>
          rw [false_run]
          rw [ih]
          simp [eraseBits, wrappedOptionsWord, wrappedOptions,
            AcceptConfigCopy.wrappedBits,
            AcceptConfigCopy.wrappedBit, wrappedRawBit,
            List.reverse_append, List.map_append, List.append_assoc]
      | true =>
          rw [true_run]
          rw [ih]
          simp [eraseBits, wrappedOptionsWord, wrappedOptions,
            AcceptConfigCopy.wrappedBits,
            AcceptConfigCopy.wrappedBit, wrappedRawBit,
            List.reverse_append, List.map_append, List.append_assoc]

def markedFuel (before after : List Bool) : Nat :=
  4 * before.length + 4 + 4 * after.length + 2
theorem run
    (before after : List Bool) (markedBit : Bool)
    (left : List (Option Bool)) (boundaryRest : List (Option Bool))
    (T2 : Tape Bool) :
    description.runConfig (markedFuel before after)
        (config loop
          (scanOptionTape left
            (List.append (wrappedOptionsWord before)
              (List.append (markedOptions markedBit)
                (List.append (wrappedOptionsWord after)
                  (some false :: some false :: boundaryRest)))))
          Tape.blank T2) =
      config halt
        (scanOptionTape
          (List.append
            (List.append
              (List.append (wrappedOptionsWord after).reverse
                (wrappedOptions markedBit).reverse)
              (wrappedOptionsWord before).reverse)
            left)
          (some false :: some false :: boundaryRest))
        Tape.blank
        (eraseBits after ((writeBitR true).apply (eraseBits before T2))) := by
  rw [markedFuel]
  rw [show
    4 * before.length + 4 + 4 * after.length + 2 =
      4 * before.length + (4 + (4 * after.length + 2)) by lia]
  rw [Description.runConfig_add]
  rw [normal_run]
  rw [show 4 + (4 * after.length + 2) =
      4 + (4 * after.length + 2) by rfl]
  rw [Description.runConfig_add]
  cases markedBit with
  | false =>
      rw [marked_false_run]
      rw [Description.runConfig_add]
      rw [normal_run]
      rw [boundary_run]
      simp [List.reverse_append, List.append_assoc]
  | true =>
      rw [marked_true_run]
      rw [Description.runConfig_add]
      rw [normal_run]
      rw [boundary_run]
      simp [List.reverse_append, List.append_assoc]

end MarkedErase

end DirectTokenDriver
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
