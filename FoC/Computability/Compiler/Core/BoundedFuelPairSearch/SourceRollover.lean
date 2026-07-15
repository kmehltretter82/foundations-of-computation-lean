import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.RolloverTape
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.PersistentRestaging

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
namespace U12SourceRollover

inductive State where
  | seekRight
  | back7
  | back6
  | back5
  | back4
  | back3
  | back2
  | back1
  | sourceTurn
  | dropTick0
  | dropTick1
  | dropTick2
  | dropTick3
  | scan0
  | scan1
  | scan2
  | scanKind
  | writeDone0
  | writeDone1
  | writeDone2
  | writeDone3
  | sourceRewind1
  | sourceRewind2
  | sourceRewind3
  | rewindT2
  | checkerMove1
  | checkerMove2
  | checkerMove3
  | checkerMove4
  | checkerTurn
  | checkerWrite0
  | checkerWrite1
  | checkerWrite2
  | checkerWrite3
  | checkerRewind1
  | checkerRewind2
  | checkerRewind3
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
  | .back1 => fun _ _ _ => step keepS keepS keepL .sourceTurn
  | .sourceTurn => fun _ _ _ => step keepS keepR keepS .dropTick0
  | .dropTick0 => fun _ _ _ => step keepS eraseR keepS .dropTick1
  | .dropTick1 => fun _ _ _ => step keepS eraseR keepS .dropTick2
  | .dropTick2 => fun _ _ _ => step keepS eraseR keepS .dropTick3
  | .dropTick3 => fun _ _ _ => step keepS eraseR keepS .scan0
  | .scan0 => fun _ r1 _ =>
      match r1 with
      | some false => step keepS eraseR (writeBitR false) .scan1
      | _ => none
  | .scan1 => fun _ r1 _ =>
      match r1 with
      | some false => step keepS eraseR (writeBitR false) .scan2
      | _ => none
  | .scan2 => fun _ r1 _ =>
      match r1 with
      | some true => step keepS eraseR (writeBitR true) .scanKind
      | _ => none
  | .scanKind => fun _ r1 _ =>
      match r1 with
      | some false => step keepS eraseR (writeBitR false) .scan0
      | some true => step keepS eraseR (writeBitR true) .writeDone0
      | none => none
  | .writeDone0 => fun _ _ _ =>
      step keepS (writeBitR false) (writeBitR false) .writeDone1
  | .writeDone1 => fun _ _ _ =>
      step keepS (writeBitR false) (writeBitR false) .writeDone2
  | .writeDone2 => fun _ _ _ =>
      step keepS (writeBitR true) (writeBitR true) .writeDone3
  | .writeDone3 => fun _ _ _ =>
      step keepS (writeBitL true) (writeBitR true) .sourceRewind1
  | .sourceRewind1 => fun _ _ _ =>
      step keepS keepL keepL .sourceRewind2
  | .sourceRewind2 => fun _ _ _ =>
      step keepS keepL keepS .sourceRewind3
  | .sourceRewind3 => fun _ _ _ =>
      step keepS keepL keepS .rewindT2
  | .rewindT2 => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepS keepL .rewindT2
      | none => step keepS keepS keepR .checkerMove1
  | .checkerMove1 => fun _ _ _ => step keepL keepS keepS .checkerMove2
  | .checkerMove2 => fun _ _ _ => step keepL keepS keepS .checkerMove3
  | .checkerMove3 => fun _ _ _ => step keepL keepS keepS .checkerMove4
  | .checkerMove4 => fun _ _ _ => step keepL keepS keepS .checkerTurn
  | .checkerTurn => fun _ _ _ => step keepR keepS keepS .checkerWrite0
  | .checkerWrite0 => fun _ _ _ =>
      step (writeBitR false) keepS keepS .checkerWrite1
  | .checkerWrite1 => fun _ _ _ =>
      step (writeBitR false) keepS keepS .checkerWrite2
  | .checkerWrite2 => fun _ _ _ =>
      step (writeBitR true) keepS keepS .checkerWrite3
  | .checkerWrite3 => fun _ _ _ =>
      step (writeBitL false) keepS keepS .checkerRewind1
  | .checkerRewind1 => fun _ _ _ => step keepL keepS keepS .checkerRewind2
  | .checkerRewind2 => fun _ _ _ => step keepL keepS keepS .checkerRewind3
  | .checkerRewind3 => fun _ _ _ => step keepL keepS keepS .halt
  | .halt => fun _ _ _ => none

def states : List State :=
  [.seekRight,
    .back7, .back6, .back5, .back4, .back3, .back2, .back1,
    .sourceTurn,
    .dropTick0, .dropTick1, .dropTick2, .dropTick3,
    .scan0, .scan1, .scan2, .scanKind,
    .writeDone0, .writeDone1, .writeDone2, .writeDone3,
    .sourceRewind1, .sourceRewind2, .sourceRewind3,
    .rewindT2,
    .checkerMove1, .checkerMove2, .checkerMove3, .checkerMove4,
    .checkerTurn,
    .checkerWrite0, .checkerWrite1, .checkerWrite2, .checkerWrite3,
    .checkerRewind1, .checkerRewind2, .checkerRewind3,
    .halt]

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

@[simp] theorem table_states : table.states = states := rfl

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
      (table.config .sourceTurn T0 T1
        (back8Transform (tapeAtCells left (none :: right)))) := by
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.seekRight) (target := State.back7)
      (by simp [states]) keepS keepS keepL
      T0 T1 (tapeAtCells left (none :: right))
      (by simp [next, step, tapeAtCells, Tape.read]))
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.back7) (target := State.back6)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.back6) (target := State.back5)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.back5) (target := State.back4)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.back4) (target := State.back3)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.back3) (target := State.back2)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.back2) (target := State.back1)
      (by simp [states]) keepS keepS keepL T0 T1 _ rfl)
  simpa [back8Transform, keepS, TapeAction.stay,
    TapeAction.apply, HeadMove.apply] using
    leads_action
      (s := State.back1) (target := State.sourceTurn)
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
      (table.config .sourceTurn T0 T1 (suffixCursorTape pre)) := by
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

theorem leads_scanTick
    (left tail : List (Option Bool)) (T0 T2 : Tape Bool) :
    table.Leads
      (table.config .scan0 T0
        (tapeAtCells left
          (some false :: some false :: some true :: some false :: tail))
        T2)
      (table.config .scan0 T0
        (tapeAtCells (none :: none :: none :: none :: left) tail)
        (rightWriteBits [false, false, true, false] T2)) := by
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.scan0) (target := State.scan1)
      (by simp [states]) keepS eraseR (writeBitR false)
      T0
      (tapeAtCells left
        (some false :: some false :: some true :: some false :: tail))
      T2 (by simp [next, step, tapeAtCells, Tape.read]))
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.scan1) (target := State.scan2)
      (by simp [states]) keepS eraseR (writeBitR false)
      T0
      (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some false :: tail)))
      ((writeBitR false).apply T2)
      (by simp [next, step, tapeAtCells, Tape.read,
        eraseR, writeR, TapeAction.apply, HeadMove.apply,
        Tape.write, Tape.move, Tape.moveRight]))
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.scan2) (target := State.scanKind)
      (by simp [states]) keepS eraseR (writeBitR true)
      T0
      (eraseR.apply (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some false :: tail))))
      ((writeBitR false).apply ((writeBitR false).apply T2))
      (by simp [next, step, tapeAtCells, Tape.read,
        eraseR, writeR, TapeAction.apply, HeadMove.apply,
        Tape.write, Tape.move, Tape.moveRight]))
  have hlast := leads_action
      (s := State.scanKind) (target := State.scan0)
      (by simp [states]) keepS eraseR (writeBitR false)
      T0
      (eraseR.apply (eraseR.apply (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some false :: tail)))))
      ((writeBitR true).apply
        ((writeBitR false).apply ((writeBitR false).apply T2)))
      (by rfl)
  have hstay : keepS.apply T0 = T0 := rfl
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
    (left tail : List (Option Bool)) (T0 T2 : Tape Bool) :
    table.Leads
      (table.config .scan0 T0
        (tapeAtCells left
          (some false :: some false :: some true :: some true :: tail))
        T2)
      (table.config .writeDone0 T0
        (tapeAtCells (none :: none :: none :: none :: left) tail)
        (rightWriteBits [false, false, true, true] T2)) := by
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.scan0) (target := State.scan1)
      (by simp [states]) keepS eraseR (writeBitR false)
      T0
      (tapeAtCells left
        (some false :: some false :: some true :: some true :: tail))
      T2 (by simp [next, step, tapeAtCells, Tape.read]))
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.scan1) (target := State.scan2)
      (by simp [states]) keepS eraseR (writeBitR false)
      T0
      (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some true :: tail)))
      ((writeBitR false).apply T2)
      (by simp [next, step, tapeAtCells, Tape.read,
        eraseR, writeR, TapeAction.apply, HeadMove.apply,
        Tape.write, Tape.move, Tape.moveRight]))
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.scan2) (target := State.scanKind)
      (by simp [states]) keepS eraseR (writeBitR true)
      T0
      (eraseR.apply (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some true :: tail))))
      ((writeBitR false).apply ((writeBitR false).apply T2))
      (by simp [next, step, tapeAtCells, Tape.read,
        eraseR, writeR, TapeAction.apply, HeadMove.apply,
        Tape.write, Tape.move, Tape.moveRight]))
  have hlast := leads_action
      (s := State.scanKind) (target := State.writeDone0)
      (by simp [states]) keepS eraseR (writeBitR true)
      T0
      (eraseR.apply (eraseR.apply (eraseR.apply
        (tapeAtCells left
          (some false :: some false :: some true :: some true :: tail)))))
      ((writeBitR true).apply
        ((writeBitR false).apply ((writeBitR false).apply T2)))
      (by rfl)
  have hstay : keepS.apply T0 = T0 := rfl
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
    (T0 T2 : Tape Bool) :
    table.Leads
      (table.config .scan0 T0
        (tapeAtCells left
          (List.append ((stageNatBits fuel).map some) tail))
        T2)
      (table.config .writeDone0 T0
        (tapeAtCells
          (List.append
            (List.replicate (stageNatBits fuel).length none) left)
          tail)
        (rightWriteBits (stageNatBits fuel) T2)) := by
  induction fuel generalizing left T2 with
  | zero =>
      simpa using leads_scanDone left tail T0 T2
  | succ fuel ih =>
      apply TypedStateTable.Leads.trans
        (leads_scanTick left
          (List.append ((stageNatBits fuel).map some) tail) T0 T2)
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

theorem leads_dropFirstTick
    (fuel : Nat) (left tail : List (Option Bool))
    (T0 T2 : Tape Bool) :
    table.Leads
      (table.config .sourceTurn T0
        (tapeAtCells left
          (none :: some false :: some false :: some true :: some false ::
            List.append ((stageNatBits fuel).map some) tail))
        T2)
      (table.config .scan0 T0
        (tapeAtCells
          (none :: none :: none :: none :: none :: left)
          (List.append ((stageNatBits fuel).map some) tail))
        T2) := by
  let Tin := tapeAtCells left
    (none :: some false :: some false :: some true :: some false ::
      List.append ((stageNatBits fuel).map some) tail)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.sourceTurn) (target := State.dropTick0)
      (by simp [states]) keepS keepR keepS T0 Tin T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.dropTick0) (target := State.dropTick1)
      (by simp [states]) keepS eraseR keepS
      T0 (keepR.apply Tin) T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.dropTick1) (target := State.dropTick2)
      (by simp [states]) keepS eraseR keepS
      T0 (eraseR.apply (keepR.apply Tin)) T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.dropTick2) (target := State.dropTick3)
      (by simp [states]) keepS eraseR keepS
      T0 (eraseR.apply (eraseR.apply (keepR.apply Tin))) T2 rfl)
  have hlast := leads_action
    (s := State.dropTick3) (target := State.scan0)
    (by simp [states]) keepS eraseR keepS
    T0 (eraseR.apply (eraseR.apply (eraseR.apply (keepR.apply Tin)))) T2 rfl
  have hstay0 : keepS.apply T0 = T0 := rfl
  have hstay2 : keepS.apply T2 = T2 := rfl
  have hsource :
      eraseR.apply
          (eraseR.apply (eraseR.apply (eraseR.apply (keepR.apply Tin)))) =
        tapeAtCells
          (none :: none :: none :: none :: none :: left)
          (List.append ((stageNatBits fuel).map some) tail) := by
    dsimp [Tin]
    cases fuel <;> rfl
  rw [hstay0, hstay2, hsource] at hlast
  simpa [Tin, keepS, TapeAction.stay, TapeAction.apply,
    HeadMove.apply] using hlast

theorem leads_finishDone (T0 T1 T2 : Tape Bool) :
    table.Leads
      (table.config .writeDone0 T0 T1 T2)
      (table.config .rewindT2 T0
        (fuelDoneTransform T1) (outputDoneTransform T2)) := by
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.writeDone0) (target := State.writeDone1)
      (by simp [states]) keepS (writeBitR false) (writeBitR false)
      T0 T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.writeDone1) (target := State.writeDone2)
      (by simp [states]) keepS (writeBitR false) (writeBitR false)
      T0 _ _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.writeDone2) (target := State.writeDone3)
      (by simp [states]) keepS (writeBitR true) (writeBitR true)
      T0 _ _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.writeDone3) (target := State.sourceRewind1)
      (by simp [states]) keepS (writeBitL true) (writeBitR true)
      T0 _ _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.sourceRewind1) (target := State.sourceRewind2)
      (by simp [states]) keepS keepL keepL T0 _ _ rfl)
  apply TypedStateTable.Leads.trans
    (leads_action
      (s := State.sourceRewind2) (target := State.sourceRewind3)
      (by simp [states]) keepS keepL keepS T0 _ _ rfl)
  simpa [fuelDoneTransform, outputDoneTransform,
      keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply] using
    leads_action
      (s := State.sourceRewind3) (target := State.rewindT2)
      (by simp [states]) keepS keepL keepS T0 _ _ rfl

theorem leads_rewindT2
    (bits : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .rewindT2 T0 T1 (leftScanTape bits right))
      (table.config .checkerMove1 T0 T1
        (tapeAtCells [none]
          (List.append (bits.reverse.map some) right))) := by
  induction bits generalizing right with
  | nil =>
      apply TypedStateTable.leads_step table
        (by change State.rewindT2 ∈ states; simp [states])
        (st := ⟨State.checkerMove1, keepS, keepS, keepR⟩)
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

def checkerTransform (T : Tape Bool) : Tape Bool :=
  let T := keepL.apply T
  let T := keepL.apply T
  let T := keepL.apply T
  let T := keepL.apply T
  let T := keepR.apply T
  let T := (writeBitR false).apply T
  let T := (writeBitR false).apply T
  let T := (writeBitR true).apply T
  let T := (writeBitL false).apply T
  let T := keepL.apply T
  let T := keepL.apply T
  keepL.apply T

theorem leads_checkerTransform (T0 T1 T2 : Tape Bool) :
    table.Leads
      (table.config .checkerMove1 T0 T1 T2)
      (table.config .halt (checkerTransform T0) T1 T2) := by
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerMove1) (target := State.checkerMove2)
      (by simp [states]) keepL keepS keepS T0 T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerMove2) (target := State.checkerMove3)
      (by simp [states]) keepL keepS keepS _ T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerMove3) (target := State.checkerMove4)
      (by simp [states]) keepL keepS keepS _ T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerMove4) (target := State.checkerTurn)
      (by simp [states]) keepL keepS keepS _ T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerTurn) (target := State.checkerWrite0)
      (by simp [states]) keepR keepS keepS _ T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerWrite0) (target := State.checkerWrite1)
      (by simp [states]) (writeBitR false) keepS keepS _ T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerWrite1) (target := State.checkerWrite2)
      (by simp [states]) (writeBitR false) keepS keepS _ T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerWrite2) (target := State.checkerWrite3)
      (by simp [states]) (writeBitR true) keepS keepS _ T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerWrite3) (target := State.checkerRewind1)
      (by simp [states]) (writeBitL false) keepS keepS _ T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerRewind1) (target := State.checkerRewind2)
      (by simp [states]) keepL keepS keepS _ T1 T2 rfl)
  apply TypedStateTable.Leads.trans
    (leads_action (s := State.checkerRewind2) (target := State.checkerRewind3)
      (by simp [states]) keepL keepS keepS _ T1 T2 rfl)
  simpa [checkerTransform, keepS, TapeAction.stay,
      TapeAction.apply, HeadMove.apply] using
    leads_action (s := State.checkerRewind3) (target := State.halt)
      (by simp [states]) keepL keepS keepS _ T1 T2 rfl

theorem outputDoneTransform_source
    (pre : Word Bool) (sourceFuel : Nat) :
    outputDoneTransform
        (rightWriteBits (stageNatBits sourceFuel)
          (suffixCursorTape pre)) =
      leftScanTape
        ((List.append pre
          (List.append (stageNatBits sourceFuel) (stageNatBits 0))).reverse)
        [none] := by
  exact outputDoneTransform_fields pre (stageNatBits sourceFuel)
    (by simp [stageNatBits_length])

def sourceScanBlankTape
    (sourceFuel : Nat) (left : List (Option Bool)) : Tape Bool :=
  scanBlankTape 5 sourceFuel left

def sourceRolloverTape
    (sourceFuel : Nat) (left : List (Option Bool)) : Tape Bool :=
  rolloverZeroTape 5 sourceFuel left

theorem leads_sourceFields
    (pre : Word Bool) (sourceFuel : Nat)
    (left : List (Option Bool)) (T0 : Tape Bool) :
    table.Leads
      (table.config .seekRight T0
        (tapeAtCells left
          (none :: List.append
            ((stageNatBits (sourceFuel + 1)).map some) [none]))
        (tapeAtCells [none]
          (List.append
            ((List.append pre
              (List.append (stageNatBits 0) (stageNatBits 0))).map some)
            [none])))
      (table.config .halt (checkerTransform T0)
        (sourceRolloverTape sourceFuel left)
        (tapeAtCells [none]
          (List.append
            ((List.append pre
              (List.append (stageNatBits sourceFuel) (stageNatBits 0))).map some)
            [none]))) := by
  let T1 := tapeAtCells left
    (none :: List.append
      ((stageNatBits (sourceFuel + 1)).map some) [none])
  apply TypedStateTable.Leads.trans
    (by
      simpa [T1] using leads_seekSuffix pre T0 T1)
  apply TypedStateTable.Leads.trans
    (by
      simpa [T1, stageNatBits_succ] using
        leads_dropFirstTick sourceFuel left [none] T0
          (suffixCursorTape pre))
  apply TypedStateTable.Leads.trans
    (by
      simpa [sourceScanBlankTape] using
        leads_scanNat sourceFuel
          (none :: none :: none :: none :: none :: left)
          [none] T0 (suffixCursorTape pre))
  apply TypedStateTable.Leads.trans
    (leads_finishDone T0
      (sourceScanBlankTape sourceFuel left)
      (rightWriteBits (stageNatBits sourceFuel) (suffixCursorTape pre)))
  rw [outputDoneTransform_source]
  apply TypedStateTable.Leads.trans
    (leads_rewindT2
      ((List.append pre
        (List.append (stageNatBits sourceFuel) (stageNatBits 0))).reverse)
      [none] T0 (sourceRolloverTape sourceFuel left))
  simpa [List.map_reverse] using
    leads_checkerTransform T0
      (sourceRolloverTape sourceFuel left)
      (tapeAtCells [none]
        (List.append
          (((List.append pre
            (List.append (stageNatBits sourceFuel) (stageNatBits 0))).reverse).reverse.map some)
          [none]))

def sourceRolloverCheckerTape
    (checkerRaw : Word Bool) (checkerFuel : Nat) : Tape Bool :=
  checkerTransform
    (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)

def sourceRolloverZeroTape
    (w : Word Bool) (sourceFuel : Nat) : Tape Bool :=
  sourceRolloverTape sourceFuel
    (List.replicate
      ((CandidateInputBits w 0 0).length + 1) none)

theorem leads_sourceRollover
    (checkerRaw w : Word Bool) (sourceFuel checkerFuel : Nat) :
    table.Leads
      (table.config .seekRight
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) (sourceFuel + 1))
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w 0 0)))
      (table.config .halt
        (sourceRolloverCheckerTape checkerRaw checkerFuel)
        (sourceRolloverZeroTape w sourceFuel)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w sourceFuel 0))) := by
  have h := leads_sourceFields (prefixBits w) sourceFuel
    (List.replicate
      ((CandidateInputBits w 0 0).length + 1) none)
    (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
  simpa [sourceRolloverCheckerTape, sourceRolloverZeroTape,
    PersistentRestaging.cleanedFuelTape,
    PersistentRestaging.restagedRawTape,
    candidateInputBits_eq_fields] using h

theorem checkerTransform_equiv
    {T U : Tape Bool} (h : Tape.Equiv T U) :
    Tape.Equiv (checkerTransform T) (checkerTransform U) := by
  have h1 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepL h
  have h2 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepL h1
  have h3 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepL h2
  have h4 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepL h3
  have h5 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepR h4
  have h6 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      (writeBitR false) h5
  have h7 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      (writeBitR false) h6
  have h8 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      (writeBitR true) h7
  have h9 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      (writeBitL false) h8
  have h10 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepL h9
  have h11 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepL h10
  have h12 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepL h11
  simpa [checkerTransform] using h12

theorem checkerTransform_cursorFuelSourceTape (fuel : Nat) :
    checkerTransform
        (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
          fuel) =
      StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
        (fuel + 1) := by
  rfl

theorem sourceRolloverCheckerTape_equiv
    (checkerRaw : Word Bool) (checkerFuel : Nat) :
    Tape.Equiv (sourceRolloverCheckerTape checkerRaw checkerFuel)
      (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
        (checkerFuel + 1)) := by
  have hclean :=
    PersistentRestaging.cleanedFuelTape_equiv checkerRaw checkerFuel
  have h := checkerTransform_equiv hclean
  rw [checkerTransform_cursorFuelSourceTape] at h
  exact h

theorem sourceRolloverZeroTape_equiv
    (w : Word Bool) (sourceFuel : Nat) :
    Tape.Equiv (sourceRolloverZeroTape w sourceFuel)
      (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
        0) := by
  simpa [sourceRolloverZeroTape, sourceRolloverTape] using
    rolloverZeroTape_replicate_equiv_cursorZero 5 sourceFuel
      ((CandidateInputBits w 0 0).length + 1)

theorem sourceRollover_endpoint
    (checkerRaw w : Word Bool) (sourceFuel checkerFuel : Nat) :
    Tape.Equiv
        (sourceRolloverCheckerTape checkerRaw checkerFuel)
        (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
          (checkerFuel + 1)) ∧
      Tape.Equiv
        (sourceRolloverZeroTape w sourceFuel)
        (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
          0) ∧
      Tape.Equiv
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w sourceFuel 0))
        (Tape.input (CandidateInputBits w sourceFuel 0)) := by
  exact ⟨sourceRolloverCheckerTape_equiv checkerRaw checkerFuel,
    sourceRolloverZeroTape_equiv w sourceFuel,
    PersistentRestaging.restagedRawTape_equiv_input _⟩

end U12SourceRollover
end BoundedFuelPairSearch
end Computability
end FoC
