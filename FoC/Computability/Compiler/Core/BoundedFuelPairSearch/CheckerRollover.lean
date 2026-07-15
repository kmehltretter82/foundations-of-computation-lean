import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.PersistentRestaging
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.RolloverTape

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
open RolloverTape
namespace U12CheckerRollover

inductive State where
  | seekRight
  | back7
  | back6
  | back5
  | back4
  | back3
  | back2
  | back1
  | startTick
  | emitTick1
  | emitTick2
  | emitTick3
  | scan0
  | scan1
  | scan2
  | scanKind
  | writeDone0
  | writeDone1
  | writeDone2
  | writeDone3
  | checkerRewind1
  | checkerRewind2
  | checkerRewind3
  | rewindT2
  | halt
deriving DecidableEq, Repr

private def step
    (action0 action1 action2 : TapeAction) (target : State) :=
  some (TypedStep.mk target action0 action1 action2)

def next : State -> Option Bool -> Option Bool -> Option Bool ->
    Option (TypedStep State)
  | .seekRight => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepS keepR .seekRight
      | none => step keepS keepS keepL .back7
  | .back7 => fun _ _ _ => step keepS keepS keepL .back6
  | .back6 => fun _ _ _ => step keepS keepS keepL .back5
  | .back5 => fun _ _ _ => step keepS keepS keepL .back4
  | .back4 => fun _ _ _ => step keepS keepS keepL .back3
  | .back3 => fun _ _ _ => step keepS keepS keepL .back2
  | .back2 => fun _ _ _ => step keepS keepS keepL .back1
  | .back1 => fun _ _ _ => step keepS keepS keepL .startTick
  | .startTick => fun _ _ _ =>
      step keepR keepS (writeBitR false) .emitTick1
  | .emitTick1 => fun _ _ _ =>
      step keepS keepS (writeBitR false) .emitTick2
  | .emitTick2 => fun _ _ _ =>
      step keepS keepS (writeBitR true) .emitTick3
  | .emitTick3 => fun _ _ _ =>
      step keepS keepS (writeBitR false) .scan0
  | .scan0 => fun r0 _ _ =>
      match r0 with
      | some false => step eraseR keepS (writeBitR false) .scan1
      | _ => none
  | .scan1 => fun r0 _ _ =>
      match r0 with
      | some false => step eraseR keepS (writeBitR false) .scan2
      | _ => none
  | .scan2 => fun r0 _ _ =>
      match r0 with
      | some true => step eraseR keepS (writeBitR true) .scanKind
      | _ => none
  | .scanKind => fun r0 _ _ =>
      match r0 with
      | some false => step eraseR keepS (writeBitR false) .scan0
      | some true => step eraseR keepS (writeBitR true) .writeDone0
      | none => none
  | .writeDone0 => fun _ _ _ =>
      step (writeBitR false) keepS (writeBitR false) .writeDone1
  | .writeDone1 => fun _ _ _ =>
      step (writeBitR false) keepS (writeBitR false) .writeDone2
  | .writeDone2 => fun _ _ _ =>
      step (writeBitR true) keepS (writeBitR true) .writeDone3
  | .writeDone3 => fun _ _ _ =>
      step (writeBitL true) keepS (writeBitR true) .checkerRewind1
  | .checkerRewind1 => fun _ _ _ =>
      step keepL keepS keepL .checkerRewind2
  | .checkerRewind2 => fun _ _ _ =>
      step keepL keepS keepS .checkerRewind3
  | .checkerRewind3 => fun _ _ _ =>
      step keepL keepS keepS .rewindT2
  | .rewindT2 => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepS keepL .rewindT2
      | none => step keepS keepS keepR .halt
  | .halt => fun _ _ _ => none

def states : List State :=
  [.seekRight,
    .back7, .back6, .back5, .back4, .back3, .back2, .back1,
    .startTick, .emitTick1, .emitTick2, .emitTick3,
    .scan0, .scan1, .scan2, .scanKind,
    .writeDone0, .writeDone1, .writeDone2, .writeDone3,
    .checkerRewind1, .checkerRewind2, .checkerRewind3,
    .rewindT2, .halt]

theorem next_target_mem :
    forall s : State, s ∈ states ->
      forall r0 r1 r2 st, next s r0 r1 r2 = some st ->
        st.target ∈ states := by
  intro s hs r0 r1 r2 st hnext
  cases s <;> simp only [next] at hnext
  all_goals repeat' first | split at hnext | simp only [step] at hnext
  all_goals try cases hnext
  all_goals simp [states]

def table : TypedStateTable State :=
  TypedStateTable.ofList states .seekRight .halt next
    (by simp [states]) (by simp [states])
    (by intros; rfl) next_target_mem

@[simp] theorem table_next_apply
    (s : State) (r0 r1 r2 : Option Bool) :
    table.next s r0 r1 r2 = next s r0 r1 r2 := rfl

theorem leads_action
    {s target : State} (hs : s ∈ states)
    (action0 action1 action2 : TapeAction)
    (T0 T1 T2 : Tape Bool)
    (hnext : next s (Tape.read T0) (Tape.read T1) (Tape.read T2) =
      step action0 action1 action2 target) :
    table.Leads
      (table.config s T0 T1 T2)
      (table.config target
        (action0.apply T0) (action1.apply T1) (action2.apply T2)) := by
  apply TypedStateTable.leads_step table hs
    (st := ⟨target, action0, action1, action2⟩)
  · rw [table_next_apply]
    exact hnext
  · rfl
  · rfl
  · rfl

theorem leads_seekRight_bits
    (bits : List Bool) (left right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .seekRight T0 T1
        (tapeAtCells left
          (List.append (bits.map some) (none :: right))))
      (table.config .seekRight T0 T1
        (tapeAtCells
          (List.append (bits.reverse.map some) left)
          (none :: right))) := by
  induction bits generalizing left with
  | nil => exact TypedStateTable.Leads.refl table _
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (d := table.config .seekRight T0 T1
          (tapeAtCells (some bit :: left)
            (List.append (rest.map some) (none :: right))))
      · apply TypedStateTable.leads_step table
          (by change State.seekRight ∈ states; simp [states])
          (st := ⟨State.seekRight, keepS, keepS, keepR⟩)
        · rw [table_next_apply]
          simp [next, step, tapeAtCells, Tape.read]
        · rfl
        · rfl
        · cases rest <;> rfl
      · simpa [List.map_reverse, List.append_assoc] using
          ih (some bit :: left)

theorem leads_back8
    (left right : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .seekRight T0 T1
        (tapeAtCells left (none :: right)))
      (table.config .startTick T0 T1
        (back8Transform (tapeAtCells left (none :: right)))) := by
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.seekRight) (target := State.back7)
      (by simp [states]) keepS keepS keepL T0 T1
      (tapeAtCells left (none :: right))
      (by simp [next, step, tapeAtCells, Tape.read]))
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.back7) (target := State.back6)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.back6) (target := State.back5)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.back5) (target := State.back4)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.back4) (target := State.back3)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.back3) (target := State.back2)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.back2) (target := State.back1)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  simpa [back8Transform, keepS, TapeAction.stay,
      TapeAction.apply, HeadMove.apply] using
    leads_action (s := State.back1) (target := State.startTick)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl

theorem leads_seekSuffix
    (pre : Word Bool) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .seekRight T0 T1
        (tapeAtCells [none]
          (List.append
            ((List.append pre
              (List.append (stageNatBits 0) (stageNatBits 0))).map some)
            [none])))
      (table.config .startTick T0 T1 (suffixCursorTape pre)) := by
  apply TypedStateTable.Leads.trans
    (leads_seekRight_bits
      (List.append pre
        (List.append (stageNatBits 0) (stageNatBits 0)))
      [none] [] T0 T1)
  have hback := leads_back8
    (List.append
      ((List.append pre
        (List.append (stageNatBits 0) (stageNatBits 0))).reverse.map some)
      [none]) [] T0 T1
  rw [back8Transform_atEnd pre] at hback
  exact hback

theorem leads_startTick
    (fuel : Nat) (left tail : List (Option Bool))
    (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .startTick
        (tapeAtCells left
          (none :: List.append ((stageNatBits fuel).map some) tail))
        T1 T2)
      (table.config .scan0
        (tapeAtCells (none :: left)
          (List.append ((stageNatBits fuel).map some) tail))
        T1 (rightWriteBits [false, false, true, false] T2)) := by
  let Tin := tapeAtCells left
    (none :: List.append ((stageNatBits fuel).map some) tail)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.startTick) (target := State.emitTick1)
      (by simp [states]) keepR keepS (writeBitR false) Tin T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.emitTick1) (target := State.emitTick2)
      (by simp [states]) keepS keepS (writeBitR false)
      (keepR.apply Tin) T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.emitTick2) (target := State.emitTick3)
      (by simp [states]) keepS keepS (writeBitR true)
      (keepR.apply Tin) T1 _ rfl)
  have hlast := leads_action
    (s := State.emitTick3) (target := State.scan0)
    (by simp [states]) keepS keepS (writeBitR false)
    (keepR.apply Tin) T1
    ((writeBitR true).apply
      ((writeBitR false).apply ((writeBitR false).apply T2))) rfl
  have hstay0 : keepS.apply (keepR.apply Tin) = keepR.apply Tin := rfl
  have hstay1 : keepS.apply T1 = T1 := rfl
  have hsource :
      keepR.apply Tin =
        tapeAtCells (none :: left)
          (List.append ((stageNatBits fuel).map some) tail) := by
    dsimp [Tin]
    cases fuel <;> rfl
  have htarget :
      (writeBitR false).apply ((writeBitR true).apply
        ((writeBitR false).apply ((writeBitR false).apply T2))) =
        rightWriteBits [false, false, true, false] T2 := by
    rfl
  rw [hstay0, hstay1, hsource, htarget] at hlast
  rw [hsource]
  simpa [Tin, keepS, TapeAction.stay,
    TapeAction.apply, HeadMove.apply] using hlast

theorem leads_scanTick
    (left tail : List (Option Bool)) (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .scan0
        (tapeAtCells left
          (some false :: some false :: some true :: some false :: tail))
        T1 T2)
      (table.config .scan0
        (tapeAtCells (none :: none :: none :: none :: left) tail)
        T1 (rightWriteBits [false, false, true, false] T2)) := by
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.scan0) (target := State.scan1)
      (by simp [states]) eraseR keepS (writeBitR false)
      (tapeAtCells left
        (some false :: some false :: some true :: some false :: tail))
      T1 T2 (by simp [next, step, tapeAtCells, Tape.read]))
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.scan1) (target := State.scan2)
      (by simp [states]) eraseR keepS (writeBitR false)
      (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some false :: tail)))
      T1 ((writeBitR false).apply T2)
      (by simp [next, step, tapeAtCells, Tape.read,
        eraseR, writeR, TapeAction.apply, HeadMove.apply,
        Tape.write, Tape.move, Tape.moveRight]))
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.scan2) (target := State.scanKind)
      (by simp [states]) eraseR keepS (writeBitR true)
      (eraseR.apply (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some false :: tail))))
      T1 ((writeBitR false).apply ((writeBitR false).apply T2))
      (by simp [next, step, tapeAtCells, Tape.read,
        eraseR, writeR, TapeAction.apply, HeadMove.apply,
        Tape.write, Tape.move, Tape.moveRight]))
  have hlast := leads_action
    (s := State.scanKind) (target := State.scan0)
    (by simp [states]) eraseR keepS (writeBitR false)
    (eraseR.apply (eraseR.apply (eraseR.apply
      (tapeAtCells left
        (some false :: some false :: some true :: some false :: tail)))))
    T1 ((writeBitR true).apply
      ((writeBitR false).apply ((writeBitR false).apply T2))) rfl
  have hstay : keepS.apply T1 = T1 := rfl
  have hsource :
      eraseR.apply (eraseR.apply (eraseR.apply (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some false :: tail))))) =
        tapeAtCells (none :: none :: none :: none :: left) tail := by
    cases tail <;> rfl
  have htarget :
      (writeBitR false).apply ((writeBitR true).apply
        ((writeBitR false).apply ((writeBitR false).apply T2))) =
        rightWriteBits [false, false, true, false] T2 := by
    rfl
  rw [hstay, hsource, htarget] at hlast
  exact hlast

theorem leads_scanDone
    (left tail : List (Option Bool)) (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .scan0
        (tapeAtCells left
          (some false :: some false :: some true :: some true :: tail))
        T1 T2)
      (table.config .writeDone0
        (tapeAtCells (none :: none :: none :: none :: left) tail)
        T1 (rightWriteBits [false, false, true, true] T2)) := by
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.scan0) (target := State.scan1)
      (by simp [states]) eraseR keepS (writeBitR false)
      (tapeAtCells left
        (some false :: some false :: some true :: some true :: tail))
      T1 T2 (by simp [next, step, tapeAtCells, Tape.read]))
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.scan1) (target := State.scan2)
      (by simp [states]) eraseR keepS (writeBitR false)
      (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some true :: tail)))
      T1 ((writeBitR false).apply T2)
      (by simp [next, step, tapeAtCells, Tape.read,
        eraseR, writeR, TapeAction.apply, HeadMove.apply,
        Tape.write, Tape.move, Tape.moveRight]))
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.scan2) (target := State.scanKind)
      (by simp [states]) eraseR keepS (writeBitR true)
      (eraseR.apply (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some true :: tail))))
      T1 ((writeBitR false).apply ((writeBitR false).apply T2))
      (by simp [next, step, tapeAtCells, Tape.read,
        eraseR, writeR, TapeAction.apply, HeadMove.apply,
        Tape.write, Tape.move, Tape.moveRight]))
  have hlast := leads_action
    (s := State.scanKind) (target := State.writeDone0)
    (by simp [states]) eraseR keepS (writeBitR true)
    (eraseR.apply (eraseR.apply (eraseR.apply
      (tapeAtCells left
        (some false :: some false :: some true :: some true :: tail)))))
    T1 ((writeBitR true).apply
      ((writeBitR false).apply ((writeBitR false).apply T2))) rfl
  have hstay : keepS.apply T1 = T1 := rfl
  have hsource :
      eraseR.apply (eraseR.apply (eraseR.apply (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some true :: tail))))) =
        tapeAtCells (none :: none :: none :: none :: left) tail := by
    cases tail <;> rfl
  have htarget :
      (writeBitR true).apply ((writeBitR true).apply
        ((writeBitR false).apply ((writeBitR false).apply T2))) =
        rightWriteBits [false, false, true, true] T2 := by
    rfl
  rw [hstay, hsource, htarget] at hlast
  exact hlast

theorem leads_scanNat
    (fuel : Nat) (left tail : List (Option Bool))
    (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .scan0
        (tapeAtCells left
          (List.append ((stageNatBits fuel).map some) tail))
        T1 T2)
      (table.config .writeDone0
        (tapeAtCells
          (List.append
            (List.replicate (stageNatBits fuel).length none) left)
          tail)
        T1 (rightWriteBits (stageNatBits fuel) T2)) := by
  induction fuel generalizing left T2 with
  | zero => simpa using leads_scanDone left tail T1 T2
  | succ fuel ih =>
      apply TypedStateTable.Leads.trans
        (leads_scanTick left
          (List.append ((stageNatBits fuel).map some) tail) T1 T2)
      have hrest := ih
        (none :: none :: none :: none :: left)
        (rightWriteBits [false, false, true, false] T2)
      have hleft :
          List.append
              (List.replicate
                ((stageNatBits fuel).length + 1 + 1 + 1 + 1) none)
              left =
            List.append
              (List.replicate (stageNatBits fuel).length none)
              (none :: none :: none :: none :: left) := by
        rw [show
          (stageNatBits fuel).length + 1 + 1 + 1 + 1 =
            (stageNatBits fuel).length + 4 by lia]
        simpa using
          (list_replicate_add_append
            (none : Option Bool) (stageNatBits fuel).length 4 left)
      rw [stageNatBits_succ]
      simp only [List.length_cons]
      rw [hleft]
      simpa [rightWriteBits, List.append_assoc] using hrest

theorem leads_finishDone (T0 T1 T2 : Tape Bool) :
    table.Leads
      (table.config .writeDone0 T0 T1 T2)
      (table.config .rewindT2
        (fuelDoneTransform T0) T1 (outputDoneTransform T2)) := by
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.writeDone0) (target := State.writeDone1)
      (by simp [states]) (writeBitR false) keepS (writeBitR false)
      T0 T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.writeDone1) (target := State.writeDone2)
      (by simp [states]) (writeBitR false) keepS (writeBitR false)
      _ T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.writeDone2) (target := State.writeDone3)
      (by simp [states]) (writeBitR true) keepS (writeBitR true)
      _ T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.writeDone3) (target := State.checkerRewind1)
      (by simp [states]) (writeBitL true) keepS (writeBitR true)
      _ T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerRewind1) (target := State.checkerRewind2)
      (by simp [states]) keepL keepS keepL _ T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerRewind2) (target := State.checkerRewind3)
      (by simp [states]) keepL keepS keepS _ T1 _ rfl)
  simpa [fuelDoneTransform, outputDoneTransform,
      keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply] using
    leads_action (s := State.checkerRewind3) (target := State.rewindT2)
      (by simp [states]) keepL keepS keepS _ T1 _ rfl

theorem leads_rewindT2
    (bits : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .rewindT2 T0 T1 (leftScanTape bits right))
      (table.config .halt T0 T1
        (tapeAtCells [none]
          (List.append (bits.reverse.map some) right))) := by
  induction bits generalizing right with
  | nil =>
      apply TypedStateTable.leads_step table
        (by change State.rewindT2 ∈ states; simp [states])
        (st := ⟨State.halt, keepS, keepS, keepR⟩)
      · rw [table_next_apply]
        simp [leftScanTape, next, step, tapeAtCells, Tape.read]
      · rfl
      · rfl
      · cases right <;> rfl
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (d := table.config .rewindT2 T0 T1
          (leftScanTape rest (some bit :: right)))
      · apply TypedStateTable.leads_step table
          (by change State.rewindT2 ∈ states; simp [states])
          (st := ⟨State.rewindT2, keepS, keepS, keepL⟩)
        · rw [table_next_apply]
          simp [leftScanTape, next, step, tapeAtCells, Tape.read]
        · rfl
        · rfl
        · cases rest <;> rfl
      · simpa [List.map_reverse, List.append_assoc] using
          ih (some bit :: right)

theorem outputDoneTransform_checker
    (pre : Word Bool) (checkerFuel : Nat) :
    outputDoneTransform
        (rightWriteBits (stageNatBits checkerFuel)
          (rightWriteBits [false, false, true, false]
            (suffixCursorTape pre))) =
      leftScanTape
        ((List.append pre
          (List.append (stageNatBits (checkerFuel + 1))
            (stageNatBits 0))).reverse)
        [none] := by
  rw [← rightWriteBits_append]
  rw [show
    List.append [false, false, true, false]
        (stageNatBits checkerFuel) =
      stageNatBits (checkerFuel + 1) by
    simp [stageNatBits_succ]]
  exact outputDoneTransform_fields pre (stageNatBits (checkerFuel + 1))
    (by simp [stageNatBits_length])

def checkerScanBlankTape
    (checkerFuel : Nat) (left : List (Option Bool)) : Tape Bool :=
  scanBlankTape 1 checkerFuel left

def checkerRolloverZeroTape
    (checkerFuel : Nat) (left : List (Option Bool)) : Tape Bool :=
  rolloverZeroTape 1 checkerFuel left

theorem leads_checkerFields
    (pre : Word Bool) (checkerFuel : Nat)
    (left : List (Option Bool)) (T1 : Tape Bool) :
    table.Leads
      (table.config .seekRight
        (tapeAtCells left
          (none :: List.append
            ((stageNatBits checkerFuel).map some) [none]))
        T1
        (tapeAtCells [none]
          (List.append
            ((List.append pre
              (List.append (stageNatBits 0) (stageNatBits 0))).map some)
            [none])))
      (table.config .halt
        (checkerRolloverZeroTape checkerFuel left) T1
        (tapeAtCells [none]
          (List.append
            ((List.append pre
              (List.append (stageNatBits (checkerFuel + 1))
                (stageNatBits 0))).map some)
            [none]))) := by
  let T0 := tapeAtCells left
    (none :: List.append ((stageNatBits checkerFuel).map some) [none])
  apply TypedStateTable.Leads.trans
    (by simpa [T0] using leads_seekSuffix pre T0 T1)
  apply TypedStateTable.Leads.trans
    (by
      simpa [T0] using
        leads_startTick checkerFuel left [none] T1
          (suffixCursorTape pre))
  apply TypedStateTable.Leads.trans
    (by
      simpa [checkerScanBlankTape] using
        leads_scanNat checkerFuel (none :: left) [none]
          T1
          (rightWriteBits [false, false, true, false]
            (suffixCursorTape pre)))
  apply TypedStateTable.Leads.trans
    (leads_finishDone
      (checkerScanBlankTape checkerFuel left) T1
      (rightWriteBits (stageNatBits checkerFuel)
        (rightWriteBits [false, false, true, false]
          (suffixCursorTape pre))))
  rw [outputDoneTransform_checker]
  simpa [checkerRolloverZeroTape, checkerScanBlankTape,
      rolloverZeroTape, List.map_reverse] using
    leads_rewindT2
      ((List.append pre
        (List.append (stageNatBits (checkerFuel + 1))
          (stageNatBits 0))).reverse)
      [none] (checkerRolloverZeroTape checkerFuel left) T1

def checkerRolloverCheckerTape
    (checkerRaw : Word Bool) (checkerFuel : Nat) : Tape Bool :=
  checkerRolloverZeroTape checkerFuel
    (List.replicate (checkerRaw.length + 1) none)

theorem leads_checkerRollover
    (checkerRaw w : Word Bool) (checkerFuel : Nat) :
    table.Leads
      (table.config .seekRight
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) 0)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w 0 0)))
      (table.config .halt
        (checkerRolloverCheckerTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) 0)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w (checkerFuel + 1) 0))) := by
  have h := leads_checkerFields (prefixBits w) checkerFuel
    (List.replicate (checkerRaw.length + 1) none)
    (PersistentRestaging.cleanedFuelTape (CandidateInputBits w 0 0) 0)
  simpa [checkerRolloverCheckerTape,
    PersistentRestaging.cleanedFuelTape,
    PersistentRestaging.restagedRawTape,
    candidateInputBits_eq_fields] using h

theorem checkerRolloverCheckerTape_equiv
    (checkerRaw : Word Bool) (checkerFuel : Nat) :
    Tape.Equiv (checkerRolloverCheckerTape checkerRaw checkerFuel)
      (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
        0) := by
  simpa [checkerRolloverCheckerTape, checkerRolloverZeroTape] using
    rolloverZeroTape_replicate_equiv_cursorZero 1 checkerFuel
      (checkerRaw.length + 1)

theorem checkerRollover_endpoint
    (checkerRaw w : Word Bool) (checkerFuel : Nat) :
    Tape.Equiv
        (checkerRolloverCheckerTape checkerRaw checkerFuel)
        (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
          0) ∧
      Tape.Equiv
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) 0)
        (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
          0) ∧
      Tape.Equiv
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w (checkerFuel + 1) 0))
        (Tape.input (CandidateInputBits w (checkerFuel + 1) 0)) := by
  exact ⟨checkerRolloverCheckerTape_equiv checkerRaw checkerFuel,
    PersistentRestaging.cleanedFuelTape_equiv _ _,
    PersistentRestaging.restagedRawTape_equiv_input _⟩

end U12CheckerRollover
end BoundedFuelPairSearch
end Computability
end FoC
