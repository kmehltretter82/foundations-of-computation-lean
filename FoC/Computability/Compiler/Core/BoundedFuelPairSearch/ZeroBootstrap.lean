import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.DiagonalAdvance

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace BoundedFuelPairSearch
namespace U12ZeroBootstrap

inductive State where
  | lengthScan
  | lengthTick1
  | lengthTick2
  | lengthTick3
  | lengthDone1
  | lengthDone2
  | lengthDone3
  | rawTurn
  | rawRewind
  | rawCopy
  | cell1 (bit : Bool)
  | cell2 (bit : Bool)
  | cell3 (bit : Bool)
  | closePad2
  | fuelWrite0
  | fuelWrite1
  | fuelWrite2
  | fuelWrite3
  | candidateDone2
  | candidateDone3
  | fuelBack1
  | fuelBack2
  | fuelBack3
  | fuelBack4
  | fuelBack5
  | outputRewind
  | halt
deriving DecidableEq, Repr

private def step
    (action0 action1 action2 : TapeAction) (target : State) :
    Option (TypedStep State) :=
  some (TypedStep.mk target action0 action1 action2)

def next : State -> Option Bool -> Option Bool -> Option Bool ->
    Option (TypedStep State)
  | .lengthScan => fun r0 _ _ =>
      match r0 with
      | some _ => step keepR keepS (writeBitR false) .lengthTick1
      | none => step keepS keepS (writeBitR false) .lengthDone1
  | .lengthTick1 => fun _ _ _ =>
      step keepS keepS (writeBitR false) .lengthTick2
  | .lengthTick2 => fun _ _ _ =>
      step keepS keepS (writeBitR true) .lengthTick3
  | .lengthTick3 => fun _ _ _ =>
      step keepS keepS (writeBitR false) .lengthScan
  | .lengthDone1 => fun _ _ _ =>
      step keepS keepS (writeBitR false) .lengthDone2
  | .lengthDone2 => fun _ _ _ =>
      step keepS keepS (writeBitR true) .lengthDone3
  | .lengthDone3 => fun _ _ _ =>
      step keepS keepS (writeBitR true) .rawTurn
  | .rawTurn => fun _ _ _ =>
      step keepL keepS keepS .rawRewind
  | .rawRewind => fun r0 _ _ =>
      match r0 with
      | some _ => step keepL keepS keepS .rawRewind
      | none => step keepR keepS keepS .rawCopy
  | .rawCopy => fun r0 _ _ =>
      match r0 with
      | some bit =>
          step eraseR keepS (writeBitR false) (.cell1 bit)
      | none =>
          step keepR keepR (writeBitR false) .closePad2
  | .cell1 bit => fun _ _ _ =>
      step keepS keepS (writeBitR true) (.cell2 bit)
  | .cell2 bit => fun _ _ _ =>
      step keepS keepS (writeBitR bit) (.cell3 bit)
  | .cell3 bit => fun _ _ _ =>
      step keepS keepS (writeBitR (!bit)) .rawCopy
  | .closePad2 => fun _ _ _ =>
      step keepR keepR (writeBitR false) .fuelWrite0
  | .fuelWrite0 => fun _ _ _ =>
      step (writeBitR false) (writeBitR false) (writeBitR true)
        .fuelWrite1
  | .fuelWrite1 => fun _ _ _ =>
      step (writeBitR false) (writeBitR false) (writeBitR true)
        .fuelWrite2
  | .fuelWrite2 => fun _ _ _ =>
      step (writeBitR true) (writeBitR true) (writeBitR false)
        .fuelWrite3
  | .fuelWrite3 => fun _ _ _ =>
      step (writeBitR true) (writeBitR true) (writeBitR false)
        .candidateDone2
  | .candidateDone2 => fun _ _ _ =>
      step keepS keepS (writeBitR true) .candidateDone3
  | .candidateDone3 => fun _ _ _ =>
      step keepS keepS (writeBitR true) .fuelBack1
  | .fuelBack1 => fun _ _ _ =>
      step keepL keepL keepS .fuelBack2
  | .fuelBack2 => fun _ _ _ =>
      step keepL keepL keepS .fuelBack3
  | .fuelBack3 => fun _ _ _ =>
      step keepL keepL keepS .fuelBack4
  | .fuelBack4 => fun _ _ _ =>
      step keepL keepL keepS .fuelBack5
  | .fuelBack5 => fun _ _ _ =>
      step keepL keepL keepL .outputRewind
  | .outputRewind => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepS keepL .outputRewind
      | none => step keepS keepS keepR .halt
  | .halt => fun _ _ _ => none

def states : List State :=
  [.lengthScan, .lengthTick1, .lengthTick2, .lengthTick3,
    .lengthDone1, .lengthDone2, .lengthDone3,
    .rawTurn, .rawRewind, .rawCopy,
    .cell1 false, .cell1 true,
    .cell2 false, .cell2 true,
    .cell3 false, .cell3 true,
    .closePad2,
    .fuelWrite0, .fuelWrite1, .fuelWrite2, .fuelWrite3,
    .candidateDone2, .candidateDone3,
    .fuelBack1, .fuelBack2, .fuelBack3, .fuelBack4, .fuelBack5,
    .outputRewind, .halt]

theorem state_mem : forall state : State, state ∈ states
  | .lengthScan => by simp [states]
  | .lengthTick1 => by simp [states]
  | .lengthTick2 => by simp [states]
  | .lengthTick3 => by simp [states]
  | .lengthDone1 => by simp [states]
  | .lengthDone2 => by simp [states]
  | .lengthDone3 => by simp [states]
  | .rawTurn => by simp [states]
  | .rawRewind => by simp [states]
  | .rawCopy => by simp [states]
  | .cell1 bit => by cases bit <;> simp [states]
  | .cell2 bit => by cases bit <;> simp [states]
  | .cell3 bit => by cases bit <;> simp [states]
  | .closePad2 => by simp [states]
  | .fuelWrite0 => by simp [states]
  | .fuelWrite1 => by simp [states]
  | .fuelWrite2 => by simp [states]
  | .fuelWrite3 => by simp [states]
  | .candidateDone2 => by simp [states]
  | .candidateDone3 => by simp [states]
  | .fuelBack1 => by simp [states]
  | .fuelBack2 => by simp [states]
  | .fuelBack3 => by simp [states]
  | .fuelBack4 => by simp [states]
  | .fuelBack5 => by simp [states]
  | .outputRewind => by simp [states]
  | .halt => by simp [states]

theorem next_target_mem :
    forall s : State, s ∈ states ->
      forall r0 r1 r2 st, next s r0 r1 r2 = some st ->
        st.target ∈ states := by
  intro _s _hs _r0 _r1 _r2 st _hnext
  exact state_mem st.target

def table : TypedStateTable State :=
  TypedStateTable.ofList states .lengthScan .halt next
    (by simp [states]) (by simp [states])
    (by intros; rfl) next_target_mem

@[simp] theorem table_states : table.states = states := rfl

@[simp] theorem table_next_apply
    (s : State) (r0 r1 r2 : Option Bool) :
    table.next s r0 r1 r2 = next s r0 r1 r2 := rfl

theorem leads_one
    (s : State) (T0 T1 T2 : Tape Bool) (st : TypedStep State)
    (T0' T1' T2' : Tape Bool)
    (hnext :
      next s (Tape.read T0) (Tape.read T1) (Tape.read T2) = some st)
    (h0 : st.action0.apply T0 = T0')
    (h1 : st.action1.apply T1 = T1')
    (h2 : st.action2.apply T2 = T2') :
    table.Leads (table.config s T0 T1 T2)
      (table.config st.target T0' T1' T2') := by
  exact TypedStateTable.leads_step table (state_mem s) hnext h0 h1 h2

def lengthTicks : Nat -> Word Bool
  | 0 => []
  | n + 1 =>
      List.append [false, false, true, false] (lengthTicks n)

@[simp] theorem lengthTicks_nil :
    lengthTicks 0 = [] := rfl

@[simp] theorem lengthTicks_succ (n : Nat) :
    lengthTicks (n + 1) =
      List.append [false, false, true, false] (lengthTicks n) := rfl

theorem leads_lengthTick
    (bit : Bool) (rest : List Bool)
    (left0 outRev : List (Option Bool)) (T1 : Tape Bool) :
    table.Leads
      (table.config .lengthScan
        (tapeAtCells left0 (some bit :: rest.map some)) T1
        (tapeAtCells outRev []))
      (table.config .lengthScan
        (tapeAtCells (some bit :: left0) (rest.map some)) T1
        (tapeAtCells
          ([some false, some true, some false, some false] ++ outRev)
          [])) := by
  refine TypedStateTable.Leads.trans
    (leads_one .lengthScan
      (tapeAtCells left0 (some bit :: rest.map some)) T1
      (tapeAtCells outRev [])
      ⟨.lengthTick1, keepR, keepS, writeBitR false⟩
      (tapeAtCells (some bit :: left0) (rest.map some)) T1
      (tapeAtCells (some false :: outRev) [])
      (by rfl) (keepR_apply_tapeAtCells left0 (some bit) (rest.map some))
      rfl (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .lengthTick1
      (tapeAtCells (some bit :: left0) (rest.map some)) T1
      (tapeAtCells (some false :: outRev) [])
      ⟨.lengthTick2, keepS, keepS, writeBitR false⟩
      (tapeAtCells (some bit :: left0) (rest.map some)) T1
      (tapeAtCells (some false :: some false :: outRev) [])
      (by rfl) rfl rfl (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .lengthTick2
      (tapeAtCells (some bit :: left0) (rest.map some)) T1
      (tapeAtCells (some false :: some false :: outRev) [])
      ⟨.lengthTick3, keepS, keepS, writeBitR true⟩
      (tapeAtCells (some bit :: left0) (rest.map some)) T1
      (tapeAtCells (some true :: some false :: some false :: outRev) [])
      (by rfl) rfl rfl (by rfl)) ?_
  exact leads_one .lengthTick3
    (tapeAtCells (some bit :: left0) (rest.map some)) T1
    (tapeAtCells (some true :: some false :: some false :: outRev) [])
    ⟨.lengthScan, keepS, keepS, writeBitR false⟩
    (tapeAtCells (some bit :: left0) (rest.map some)) T1
    (tapeAtCells
      ([some false, some true, some false, some false] ++ outRev) [])
    (by rfl) rfl rfl (by rfl)

theorem leads_lengthScan_word
    (bits : List Bool) (left0 outRev : List (Option Bool))
    (T1 : Tape Bool) :
    table.Leads
      (table.config .lengthScan
        (tapeAtCells left0 (bits.map some)) T1
        (tapeAtCells outRev []))
      (table.config .lengthScan
        (tapeAtCells
          (List.append (bits.reverse.map some) left0) []) T1
        (tapeAtCells
          (List.append ((lengthTicks bits.length).reverse.map some) outRev)
          [])) := by
  induction bits generalizing left0 outRev with
  | nil =>
      simpa using TypedStateTable.Leads.refl table
        (table.config .lengthScan (tapeAtCells left0 []) T1
          (tapeAtCells outRev []))
  | cons bit rest ih =>
      refine (leads_lengthTick bit rest left0 outRev T1).trans ?_
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left0)
          ([some false, some true, some false, some false] ++ outRev)

theorem leads_lengthDone
    (left0 outRev : List (Option Bool)) (T1 : Tape Bool) :
    table.Leads
      (table.config .lengthScan (tapeAtCells left0 []) T1
        (tapeAtCells outRev []))
      (table.config .rawTurn (tapeAtCells left0 []) T1
        (tapeAtCells
          ([some true, some true, some false, some false] ++ outRev) [])) := by
  refine TypedStateTable.Leads.trans
    (leads_one .lengthScan (tapeAtCells left0 []) T1
      (tapeAtCells outRev [])
      ⟨.lengthDone1, keepS, keepS, writeBitR false⟩
      (tapeAtCells left0 []) T1
      (tapeAtCells (some false :: outRev) [])
      (by rfl) rfl rfl (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .lengthDone1 (tapeAtCells left0 []) T1
      (tapeAtCells (some false :: outRev) [])
      ⟨.lengthDone2, keepS, keepS, writeBitR false⟩
      (tapeAtCells left0 []) T1
      (tapeAtCells (some false :: some false :: outRev) [])
      (by rfl) rfl rfl (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .lengthDone2 (tapeAtCells left0 []) T1
      (tapeAtCells (some false :: some false :: outRev) [])
      ⟨.lengthDone3, keepS, keepS, writeBitR true⟩
      (tapeAtCells left0 []) T1
      (tapeAtCells (some true :: some false :: some false :: outRev) [])
      (by rfl) rfl rfl (by rfl)) ?_
  exact leads_one .lengthDone3 (tapeAtCells left0 []) T1
    (tapeAtCells (some true :: some false :: some false :: outRev) [])
    ⟨.rawTurn, keepS, keepS, writeBitR true⟩
    (tapeAtCells left0 []) T1
    (tapeAtCells
      ([some true, some true, some false, some false] ++ outRev) [])
    (by rfl) rfl rfl (by rfl)

theorem lengthTicks_append_done (n : Nat) :
    List.append (lengthTicks n) [false, false, true, true] =
      stageNatBits n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        List.append (show List Bool from lengthTicks n)
            [false, false, true, true] =
          (show List Bool from stageNatBits n) at ih
      change
        List.append
            (List.append [false, false, true, false]
              (show List Bool from lengthTicks n))
            [false, false, true, true] =
          (show List Bool from stageNatBits (n + 1))
      calc
        _ = List.append [false, false, true, false]
              (List.append (show List Bool from lengthTicks n)
                [false, false, true, true]) :=
            List.append_assoc _ _ _
        _ = List.append [false, false, true, false]
              (show List Bool from stageNatBits n) :=
            congrArg
              (fun tail : List Bool =>
                List.append [false, false, true, false] tail) ih
        _ = (show List Bool from stageNatBits (n + 1)) := by
            rw [stageNatBits_succ]
            rfl

def rawLeftScanTape
    (bits : List Bool) (right : List (Option Bool)) : Tape Bool :=
  match bits with
  | [] => tapeAtCells [] (none :: right)
  | bit :: rest => tapeAtCells (rest.map some) (some bit :: right)

theorem leads_rawRewind_bit
    (bit : Bool) (rest : List Bool)
    (right : List (Option Bool)) (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .rawRewind
        (rawLeftScanTape (bit :: rest) right) T1 T2)
      (table.config .rawRewind
        (rawLeftScanTape rest (some bit :: right)) T1 T2) := by
  apply leads_one .rawRewind
    (rawLeftScanTape (bit :: rest) right) T1 T2
    ⟨.rawRewind, keepL, keepS, keepS⟩
    (rawLeftScanTape rest (some bit :: right)) T1 T2
  · rfl
  · cases rest <;> rfl
  · rfl
  · rfl

theorem leads_rawRewind_bits
    (bits : List Bool) (right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .rawRewind (rawLeftScanTape bits right) T1 T2)
      (table.config .rawCopy
        (tapeAtCells [none]
          (List.append (bits.reverse.map some) right)) T1 T2) := by
  induction bits generalizing right with
  | nil =>
      apply leads_one .rawRewind (rawLeftScanTape [] right) T1 T2
        ⟨.rawCopy, keepR, keepS, keepS⟩
        (tapeAtCells [none] right) T1 T2
      · rfl
      · cases right <;> rfl
      · rfl
      · rfl
  | cons bit rest ih =>
      refine (leads_rawRewind_bit bit rest right T1 T2).trans ?_
      simpa [List.map_reverse, List.append_assoc] using
        ih (some bit :: right)

theorem leads_rawTurn_rewind
    (bits : List Bool) (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .rawTurn
        (tapeAtCells (bits.reverse.map some) []) T1 T2)
      (table.config .rawCopy
        (tapeAtCells [none]
          (List.append (bits.map some) [none])) T1 T2) := by
  refine TypedStateTable.Leads.trans
    (leads_one .rawTurn
      (tapeAtCells (bits.reverse.map some) []) T1 T2
      ⟨.rawRewind, keepL, keepS, keepS⟩
      (rawLeftScanTape bits.reverse [none]) T1 T2
      (by rfl) ?_ rfl rfl) ?_
  · cases hrev : bits.reverse with
    | nil =>
        rfl
    | cons bit rest =>
        rfl
  · simpa using leads_rawRewind_bits bits.reverse [none] T1 T2

theorem cellBits_reverse_map (bit : Bool) :
    (cellBits bit).reverse.map some =
      [some (!bit), some bit, some true, some false] := by
  cases bit <;> rfl

def rawCellsBits : List Bool -> List Bool
  | [] => []
  | false :: rest =>
      List.append [false, true, false, true] (rawCellsBits rest)
  | true :: rest =>
      List.append [false, true, true, false] (rawCellsBits rest)

@[simp] theorem rawCellsBits_nil :
    rawCellsBits [] = [] := rfl

@[simp] theorem rawCellsBits_cons (bit : Bool) (rest : List Bool) :
    rawCellsBits (bit :: rest) =
      List.append [false, true, bit, !bit] (rawCellsBits rest) := by
  cases bit <;> rfl

theorem leads_rawCell
    (bit : Bool) (left0 right0 outRev : List (Option Bool))
    (T1 : Tape Bool) :
    table.Leads
      (table.config .rawCopy
        (tapeAtCells left0 (some bit :: right0)) T1
        (tapeAtCells outRev []))
      (table.config .rawCopy
        (tapeAtCells (none :: left0) right0) T1
        (tapeAtCells
          ([some (!bit), some bit, some true, some false] ++ outRev) [])) := by
  refine TypedStateTable.Leads.trans
    (leads_one .rawCopy
      (tapeAtCells left0 (some bit :: right0)) T1
      (tapeAtCells outRev [])
      ⟨.cell1 bit, eraseR, keepS, writeBitR false⟩
      (tapeAtCells (none :: left0) right0) T1
      (tapeAtCells (some false :: outRev) [])
      (by rfl)
      (writeR_apply_tapeAtCells none left0 (some bit) right0)
      rfl (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one (.cell1 bit)
      (tapeAtCells (none :: left0) right0) T1
      (tapeAtCells (some false :: outRev) [])
      ⟨.cell2 bit, keepS, keepS, writeBitR true⟩
      (tapeAtCells (none :: left0) right0) T1
      (tapeAtCells (some true :: some false :: outRev) [])
      (by rfl) rfl rfl (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one (.cell2 bit)
      (tapeAtCells (none :: left0) right0) T1
      (tapeAtCells (some true :: some false :: outRev) [])
      ⟨.cell3 bit, keepS, keepS, writeBitR bit⟩
      (tapeAtCells (none :: left0) right0) T1
      (tapeAtCells (some bit :: some true :: some false :: outRev) [])
      (by rfl) rfl rfl (by rfl)) ?_
  exact leads_one (.cell3 bit)
    (tapeAtCells (none :: left0) right0) T1
    (tapeAtCells (some bit :: some true :: some false :: outRev) [])
    ⟨.rawCopy, keepS, keepS, writeBitR (!bit)⟩
    (tapeAtCells (none :: left0) right0) T1
    (tapeAtCells
      ([some (!bit), some bit, some true, some false] ++ outRev) [])
    (by rfl) rfl rfl (by rfl)

theorem replicate_none_succ_append
    (n : Nat) (tail : List (Option Bool)) :
    List.append (List.replicate (n + 1) none) tail =
      List.append (List.replicate n none) (none :: tail) := by
  rw [PersistentRestaging.replicate_succ_eq_append]
  simp [List.append_assoc]

theorem leads_rawCopy_word
    (bits : List Bool) (left0 right0 outRev : List (Option Bool))
    (T1 : Tape Bool) :
    table.Leads
      (table.config .rawCopy
        (tapeAtCells left0
          (List.append (bits.map some) right0)) T1
        (tapeAtCells outRev []))
      (table.config .rawCopy
        (tapeAtCells
          (List.append (List.replicate bits.length none) left0) right0)
        T1
        (tapeAtCells
          (List.append ((rawCellsBits bits).reverse.map some) outRev) [])) := by
  induction bits generalizing left0 outRev with
  | nil =>
      simpa using TypedStateTable.Leads.refl table
        (table.config .rawCopy (tapeAtCells left0 right0) T1
          (tapeAtCells outRev []))
  | cons bit rest ih =>
      refine (leads_rawCell bit left0
        (List.append (rest.map some) right0) outRev T1).trans ?_
      simp only [List.length_cons]
      rw [replicate_none_succ_append]
      simpa [rawCellsBits_cons, List.reverse_append, List.map_append,
        List.append_assoc] using
        ih (none :: left0)
          ([some (!bit), some bit, some true, some false] ++ outRev)

theorem leads_closeWrites_rev
    (left0 left1 outRev : List (Option Bool)) :
    table.Leads
      (table.config .rawCopy
        (tapeAtCells left0 [none]) (tapeAtCells left1 [none])
        (tapeAtCells outRev []))
      (table.config .fuelBack1
        (tapeAtCells
          ([some true, some true, some false, some false, none, none] ++
            left0) [])
        (tapeAtCells
          ([some true, some true, some false, some false, none, none] ++
            left1) [])
        (tapeAtCells
          ([some true, some true, some false, some false,
            some true, some true, some false, some false] ++ outRev) [])) := by
  refine TypedStateTable.Leads.trans
    (leads_one .rawCopy
      (tapeAtCells left0 [none]) (tapeAtCells left1 [none])
      (tapeAtCells outRev [])
      ⟨.closePad2, keepR, keepR, writeBitR false⟩
      (tapeAtCells (none :: left0) [])
      (tapeAtCells (none :: left1) [])
      (tapeAtCells (some false :: outRev) [])
      (by rfl)
      (keepR_apply_tapeAtCells left0 none [])
      (keepR_apply_tapeAtCells left1 none []) (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .closePad2
      (tapeAtCells (none :: left0) [])
      (tapeAtCells (none :: left1) [])
      (tapeAtCells (some false :: outRev) [])
      ⟨.fuelWrite0, keepR, keepR, writeBitR false⟩
      (tapeAtCells (none :: none :: left0) [])
      (tapeAtCells (none :: none :: left1) [])
      (tapeAtCells (some false :: some false :: outRev) [])
      (by rfl) (by rfl) (by rfl) (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .fuelWrite0
      (tapeAtCells (none :: none :: left0) [])
      (tapeAtCells (none :: none :: left1) [])
      (tapeAtCells (some false :: some false :: outRev) [])
      ⟨.fuelWrite1, writeBitR false, writeBitR false, writeBitR true⟩
      (tapeAtCells (some false :: none :: none :: left0) [])
      (tapeAtCells (some false :: none :: none :: left1) [])
      (tapeAtCells (some true :: some false :: some false :: outRev) [])
      (by rfl) (by rfl) (by rfl) (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .fuelWrite1
      (tapeAtCells (some false :: none :: none :: left0) [])
      (tapeAtCells (some false :: none :: none :: left1) [])
      (tapeAtCells (some true :: some false :: some false :: outRev) [])
      ⟨.fuelWrite2, writeBitR false, writeBitR false, writeBitR true⟩
      (tapeAtCells (some false :: some false :: none :: none :: left0) [])
      (tapeAtCells (some false :: some false :: none :: none :: left1) [])
      (tapeAtCells
        (some true :: some true :: some false :: some false :: outRev) [])
      (by rfl) (by rfl) (by rfl) (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .fuelWrite2
      (tapeAtCells (some false :: some false :: none :: none :: left0) [])
      (tapeAtCells (some false :: some false :: none :: none :: left1) [])
      (tapeAtCells
        (some true :: some true :: some false :: some false :: outRev) [])
      ⟨.fuelWrite3, writeBitR true, writeBitR true, writeBitR false⟩
      (tapeAtCells
        (some true :: some false :: some false :: none :: none :: left0) [])
      (tapeAtCells
        (some true :: some false :: some false :: none :: none :: left1) [])
      (tapeAtCells
        (some false :: some true :: some true :: some false :: some false ::
          outRev) [])
      (by rfl) (by rfl) (by rfl) (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .fuelWrite3
      (tapeAtCells
        (some true :: some false :: some false :: none :: none :: left0) [])
      (tapeAtCells
        (some true :: some false :: some false :: none :: none :: left1) [])
      (tapeAtCells
        (some false :: some true :: some true :: some false :: some false ::
          outRev) [])
      ⟨.candidateDone2, writeBitR true, writeBitR true, writeBitR false⟩
      (tapeAtCells
        (some true :: some true :: some false :: some false :: none :: none ::
          left0) [])
      (tapeAtCells
        (some true :: some true :: some false :: some false :: none :: none ::
          left1) [])
      (tapeAtCells
        (some false :: some false :: some true :: some true :: some false ::
          some false :: outRev) [])
      (by rfl) (by rfl) (by rfl) (by rfl)) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .candidateDone2
      (tapeAtCells
        (some true :: some true :: some false :: some false :: none :: none ::
          left0) [])
      (tapeAtCells
        (some true :: some true :: some false :: some false :: none :: none ::
          left1) [])
      (tapeAtCells
        (some false :: some false :: some true :: some true :: some false ::
          some false :: outRev) [])
      ⟨.candidateDone3, keepS, keepS, writeBitR true⟩
      (tapeAtCells
        (some true :: some true :: some false :: some false :: none :: none ::
          left0) [])
      (tapeAtCells
        (some true :: some true :: some false :: some false :: none :: none ::
          left1) [])
      (tapeAtCells
        (some true :: some false :: some false :: some true :: some true ::
          some false :: some false :: outRev) [])
      (by rfl) rfl rfl (by rfl)) ?_
  exact leads_one .candidateDone3
    (tapeAtCells
      (some true :: some true :: some false :: some false :: none :: none ::
        left0) [])
    (tapeAtCells
      (some true :: some true :: some false :: some false :: none :: none ::
        left1) [])
    (tapeAtCells
      (some true :: some false :: some false :: some true :: some true ::
        some false :: some false :: outRev) [])
    ⟨.fuelBack1, keepS, keepS, writeBitR true⟩
    (tapeAtCells
      ([some true, some true, some false, some false, none, none] ++ left0) [])
    (tapeAtCells
      ([some true, some true, some false, some false, none, none] ++ left1) [])
    (tapeAtCells
      ([some true, some true, some false, some false,
        some true, some true, some false, some false] ++ outRev) [])
    (by rfl) rfl rfl (by rfl)

theorem leads_fuelBack
    (left0 left1 : List (Option Bool)) (bits : List Bool) :
    table.Leads
      (table.config .fuelBack1
        (tapeAtCells
          ([some true, some true, some false, some false, none, none] ++
            left0) [])
        (tapeAtCells
          ([some true, some true, some false, some false, none, none] ++
            left1) [])
        (tapeAtCells (bits.reverse.map some) []))
      (table.config .outputRewind
        (tapeAtCells (none :: left0)
          [none, some false, some false, some true, some true, none])
        (tapeAtCells (none :: left1)
          [none, some false, some false, some true, some true, none])
        (rawLeftScanTape bits.reverse [none])) := by
  refine TypedStateTable.Leads.trans
    (leads_one .fuelBack1
      (tapeAtCells
        ([some true, some true, some false, some false, none, none] ++ left0)
        [])
      (tapeAtCells
        ([some true, some true, some false, some false, none, none] ++ left1)
        [])
      (tapeAtCells (bits.reverse.map some) [])
      ⟨.fuelBack2, keepL, keepL, keepS⟩
      (tapeAtCells
        ([some true, some false, some false, none, none] ++ left0)
        [some true, none])
      (tapeAtCells
        ([some true, some false, some false, none, none] ++ left1)
        [some true, none])
      (tapeAtCells (bits.reverse.map some) [])
      (by rfl) (by rfl) (by rfl) rfl) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .fuelBack2
      (tapeAtCells
        ([some true, some false, some false, none, none] ++ left0)
        [some true, none])
      (tapeAtCells
        ([some true, some false, some false, none, none] ++ left1)
        [some true, none])
      (tapeAtCells (bits.reverse.map some) [])
      ⟨.fuelBack3, keepL, keepL, keepS⟩
      (tapeAtCells ([some false, some false, none, none] ++ left0)
        [some true, some true, none])
      (tapeAtCells ([some false, some false, none, none] ++ left1)
        [some true, some true, none])
      (tapeAtCells (bits.reverse.map some) [])
      (by rfl) (by rfl) (by rfl) rfl) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .fuelBack3
      (tapeAtCells ([some false, some false, none, none] ++ left0)
        [some true, some true, none])
      (tapeAtCells ([some false, some false, none, none] ++ left1)
        [some true, some true, none])
      (tapeAtCells (bits.reverse.map some) [])
      ⟨.fuelBack4, keepL, keepL, keepS⟩
      (tapeAtCells ([some false, none, none] ++ left0)
        [some false, some true, some true, none])
      (tapeAtCells ([some false, none, none] ++ left1)
        [some false, some true, some true, none])
      (tapeAtCells (bits.reverse.map some) [])
      (by rfl) (by rfl) (by rfl) rfl) ?_
  refine TypedStateTable.Leads.trans
    (leads_one .fuelBack4
      (tapeAtCells ([some false, none, none] ++ left0)
        [some false, some true, some true, none])
      (tapeAtCells ([some false, none, none] ++ left1)
        [some false, some true, some true, none])
      (tapeAtCells (bits.reverse.map some) [])
      ⟨.fuelBack5, keepL, keepL, keepS⟩
      (tapeAtCells ([none, none] ++ left0)
        [some false, some false, some true, some true, none])
      (tapeAtCells ([none, none] ++ left1)
        [some false, some false, some true, some true, none])
      (tapeAtCells (bits.reverse.map some) [])
      (by rfl) (by rfl) (by rfl) rfl) ?_
  apply leads_one .fuelBack5
    (tapeAtCells ([none, none] ++ left0)
      [some false, some false, some true, some true, none])
    (tapeAtCells ([none, none] ++ left1)
      [some false, some false, some true, some true, none])
    (tapeAtCells (bits.reverse.map some) [])
    ⟨.outputRewind, keepL, keepL, keepL⟩
    (tapeAtCells (none :: left0)
      [none, some false, some false, some true, some true, none])
    (tapeAtCells (none :: left1)
      [none, some false, some false, some true, some true, none])
    (rawLeftScanTape bits.reverse [none])
  · rfl
  · rfl
  · rfl
  · cases hrev : bits.reverse with
    | nil => rfl
    | cons bit rest => rfl

theorem leads_outputRewind_bit
    (bit : Bool) (rest : List Bool)
    (right : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .outputRewind T0 T1
        (rawLeftScanTape (bit :: rest) right))
      (table.config .outputRewind T0 T1
        (rawLeftScanTape rest (some bit :: right))) := by
  apply leads_one .outputRewind T0 T1
    (rawLeftScanTape (bit :: rest) right)
    ⟨.outputRewind, keepS, keepS, keepL⟩
    T0 T1 (rawLeftScanTape rest (some bit :: right))
  · rfl
  · rfl
  · rfl
  · cases rest <;> rfl

theorem leads_outputRewind_bits
    (bits : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .outputRewind T0 T1
        (rawLeftScanTape bits right))
      (table.config .halt T0 T1
        (tapeAtCells [none]
          (List.append (bits.reverse.map some) right))) := by
  induction bits generalizing right with
  | nil =>
      apply leads_one .outputRewind T0 T1
        (rawLeftScanTape [] right)
        ⟨.halt, keepS, keepS, keepR⟩
        T0 T1 (tapeAtCells [none] right)
      · rfl
      · rfl
      · rfl
      · cases right <;> rfl
  | cons bit rest ih =>
      refine (leads_outputRewind_bit bit rest right T0 T1).trans ?_
      simpa [List.map_reverse, List.append_assoc] using
        ih (some bit :: right)

def bootstrapBits (raw : List Bool) : List Bool :=
  List.append (lengthTicks raw.length)
    (List.append [false, false, true, true]
      (List.append (rawCellsBits raw)
        [false, false, true, true,
          false, false, true, true]))

def bootstrapFuelTape (padding : Nat) : Tape Bool :=
  tapeAtCells (List.replicate padding none)
    [none, some false, some false, some true, some true, none]

def bootstrapCandidateTape (raw : List Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append ((bootstrapBits raw).map some) [none])

theorem leads_closeout
    (rawPrefix : List Bool) (left0 left1 : List (Option Bool)) :
    table.Leads
      (table.config .rawCopy
        (tapeAtCells left0 [none]) (tapeAtCells left1 [none])
        (tapeAtCells (rawPrefix.reverse.map some) []))
      (table.config .halt
        (tapeAtCells (none :: left0)
          [none, some false, some false, some true, some true, none])
        (tapeAtCells (none :: left1)
          [none, some false, some false, some true, some true, none])
        (tapeAtCells [none]
          (List.append
            ((List.append rawPrefix
              [false, false, true, true,
                false, false, true, true]).map some)
            [none]))) := by
  let bits : List Bool :=
    List.append rawPrefix
      [false, false, true, true, false, false, true, true]
  have hwrites := leads_closeWrites_rev left0 left1
    (rawPrefix.reverse.map some)
  have hwrites' : table.Leads
      (table.config .rawCopy
        (tapeAtCells left0 [none]) (tapeAtCells left1 [none])
        (tapeAtCells (rawPrefix.reverse.map some) []))
      (table.config .fuelBack1
        (tapeAtCells
          ([some true, some true, some false, some false, none, none] ++
            left0) [])
        (tapeAtCells
          ([some true, some true, some false, some false, none, none] ++
            left1) [])
        (tapeAtCells (bits.reverse.map some) [])) := by
    simpa [bits, List.reverse_append, List.map_append,
      List.append_assoc] using hwrites
  refine hwrites'.trans ((leads_fuelBack left0 left1 bits).trans ?_)
  have hrewind := leads_outputRewind_bits bits.reverse [none]
    (tapeAtCells (none :: left0)
      [none, some false, some false, some true, some true, none])
    (tapeAtCells (none :: left1)
      [none, some false, some false, some true, some true, none])
  simpa [bits] using hrewind

theorem input_eq_tapeAtCells (raw : List Bool) :
    Tape.input (show Word Bool from raw) =
      tapeAtCells [] (raw.map some) := by
  cases raw <;> rfl

theorem bootstrap_left_padding (n : Nat) :
    none :: List.append (List.replicate n (none : Option Bool)) [none] =
      List.replicate (n + 2) none := by
  rw [← PersistentRestaging.replicate_succ_eq_append]
  rw [show n + 2 = (n + 1) + 1 by lia]
  simp [List.replicate_succ]

theorem leads_initialized_to_exact_bootstrap (raw : List Bool) :
    table.Leads
      (table.config .lengthScan
        (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)
      (table.config .halt
        (bootstrapFuelTape (raw.length + 2))
        (bootstrapFuelTape 1)
        (bootstrapCandidateTape raw)) := by
  let lengthPrefix : List Bool :=
    List.append (show List Bool from lengthTicks raw.length)
      [false, false, true, true]
  let rawPrefix : List Bool :=
    List.append lengthPrefix (rawCellsBits raw)
  have hscan := leads_lengthScan_word raw [] [] Tape.blank
  have hscan' : table.Leads
      (table.config .lengthScan
        (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)
      (table.config .lengthScan
        (tapeAtCells (raw.reverse.map some) []) Tape.blank
        (tapeAtCells ((lengthTicks raw.length).reverse.map some) [])) := by
    simpa [input_eq_tapeAtCells, Tape.blank, tapeAtCells] using hscan
  have hdone := leads_lengthDone (raw.reverse.map some)
    ((lengthTicks raw.length).reverse.map some) Tape.blank
  have hdone' : table.Leads
      (table.config .lengthScan
        (tapeAtCells (raw.reverse.map some) []) Tape.blank
        (tapeAtCells ((lengthTicks raw.length).reverse.map some) []))
      (table.config .rawTurn
        (tapeAtCells (raw.reverse.map some) []) Tape.blank
        (tapeAtCells (lengthPrefix.reverse.map some) [])) := by
    simpa [lengthPrefix, List.reverse_append, List.map_append,
      List.append_assoc] using hdone
  have hrewind := leads_rawTurn_rewind raw Tape.blank
    (tapeAtCells (lengthPrefix.reverse.map some) [])
  have hcopy := leads_rawCopy_word raw [none] [none]
    (lengthPrefix.reverse.map some) Tape.blank
  have hcopy' : table.Leads
      (table.config .rawCopy
        (tapeAtCells [none]
          (List.append (raw.map some) [none])) Tape.blank
        (tapeAtCells (lengthPrefix.reverse.map some) []))
      (table.config .rawCopy
        (tapeAtCells
          (List.append (List.replicate raw.length none) [none]) [none])
        Tape.blank
        (tapeAtCells (rawPrefix.reverse.map some) [])) := by
    simpa [rawPrefix, List.reverse_append, List.map_append,
      List.append_assoc] using hcopy
  have hclose := leads_closeout rawPrefix
    (List.append (List.replicate raw.length none) [none]) []
  have hall := hscan'.trans
    (hdone'.trans (hrewind.trans (hcopy'.trans hclose)))
  rw [bootstrap_left_padding raw.length] at hall
  simpa [bootstrapFuelTape, bootstrapCandidateTape, bootstrapBits,
    rawPrefix, lengthPrefix,
    Tape.blank, tapeAtCells, List.append_assoc] using hall

theorem rawCellsBits_eq_cellsBits (raw : List Bool) :
    rawCellsBits raw =
      (show List Bool from
        cellsBits (show Word Bool from raw)) := by
  induction raw with
  | nil => rfl
  | cons bit rest ih =>
      have hcells := cellsBits_cons bit (show Word Bool from rest)
      change
        (show List Bool from
          cellsBits (show Word Bool from bit :: rest)) =
          List.append (show List Bool from cellBits bit)
            (show List Bool from
              cellsBits (show Word Bool from rest)) at hcells
      rw [hcells, ← ih]
      cases bit <;> rfl

theorem bootstrapBits_eq_candidateInputBits (raw : List Bool) :
    bootstrapBits raw =
      (show List Bool from
        CandidateInputBits (show Word Bool from raw) 0 0) := by
  have hlength := lengthTicks_append_done raw.length
  change
    List.append (show List Bool from lengthTicks raw.length)
        [false, false, true, true] =
      (show List Bool from stageNatBits raw.length) at hlength
  have hfields := U12DiagonalAdvance.candidateInputBits_eq_fields
    (show Word Bool from raw) 0 0
  change
    (show List Bool from
      CandidateInputBits (show Word Bool from raw) 0 0) =
      List.append (show List Bool from stageNatBits raw.length)
        (List.append
          (show List Bool from
            cellsBits (show Word Bool from raw))
          (List.append (show List Bool from stageNatBits 0)
            (show List Bool from stageNatBits 0))) at hfields
  calc
    bootstrapBits raw =
        List.append
          (List.append (show List Bool from lengthTicks raw.length)
            [false, false, true, true])
          (List.append (rawCellsBits raw)
            (List.append [false, false, true, true]
              [false, false, true, true])) := by
        simp [bootstrapBits, List.append_assoc]
    _ = List.append (show List Bool from stageNatBits raw.length)
          (List.append (rawCellsBits raw)
            (List.append [false, false, true, true]
              [false, false, true, true])) :=
        congrArg
          (fun pfx : List Bool =>
            List.append pfx
              (List.append (rawCellsBits raw)
                (List.append [false, false, true, true]
                  [false, false, true, true]))) hlength
    _ = List.append (show List Bool from stageNatBits raw.length)
          (List.append
            (show List Bool from
              cellsBits (show Word Bool from raw))
            (List.append (show List Bool from stageNatBits 0)
              (show List Bool from stageNatBits 0))) := by
        rw [rawCellsBits_eq_cellsBits]
        rfl
    _ = (show List Bool from
          CandidateInputBits (show Word Bool from raw) 0 0) :=
        hfields.symm

theorem bootstrapFuelTape_equiv_cursorZero (padding : Nat) :
    Tape.Equiv (bootstrapFuelTape padding)
      (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
        0) := by
  simp [bootstrapFuelTape,
    StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape,
    tapeAtCells, Tape.Equiv, Tape.dropTrailingNone,
    FoC.Computability.dropTrailingNone_replicate_none]

theorem bootstrapCandidateTape_eq_restaged (raw : List Bool) :
    bootstrapCandidateTape raw =
      PersistentRestaging.restagedRawTape
        (CandidateInputBits (show Word Bool from raw) 0 0) := by
  have hbits := congrArg (List.map some)
    (bootstrapBits_eq_candidateInputBits raw)
  simp [bootstrapCandidateTape, PersistentRestaging.restagedRawTape,
    hbits]

theorem bootstrapCandidateTape_equiv_input (raw : List Bool) :
    Tape.Equiv (bootstrapCandidateTape raw)
      (Tape.input
        (CandidateInputBits (show Word Bool from raw) 0 0)) := by
  rw [bootstrapCandidateTape_eq_restaged]
  exact PersistentRestaging.restagedRawTape_equiv_input _

def PersistentOrigin
    (raw : Word Bool) (T0 T1 T2 : Tape Bool) : Prop :=
  Tape.Equiv T0
      (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
        0) ∧
    Tape.Equiv T1
      (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
        0) ∧
    Tape.Equiv T2 (Tape.input (CandidateInputBits raw 0 0))

theorem exact_bootstrap_persistentOrigin (raw : List Bool) :
    PersistentOrigin (show Word Bool from raw)
      (bootstrapFuelTape (raw.length + 2))
      (bootstrapFuelTape 1)
      (bootstrapCandidateTape raw) := by
  exact ⟨bootstrapFuelTape_equiv_cursorZero _,
    bootstrapFuelTape_equiv_cursorZero _,
    bootstrapCandidateTape_equiv_input raw⟩

end U12ZeroBootstrap
end BoundedFuelPairSearch

end Computability
end FoC
