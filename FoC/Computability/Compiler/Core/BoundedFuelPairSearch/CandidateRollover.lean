import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.DiagonalSchedule
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.PersistentRestaging
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.RolloverTape
import FoC.Computability.Compiler.Structured.Lowering.TypedStateRuns

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
namespace U12CandidateRollover

inductive State where
  | seekRight
  | eraseEnd1
  | eraseEnd2
  | eraseEnd3
  | eraseEnd4
  | promoteLastCandidateTick
  | afterLast1
  | afterLast2
  | afterLast3
  | previousProbe
  | secondDone1
  | secondDone2
  | secondDone3
  | seekLimitDone
  | skipTick1
  | skipTick2
  | skipTick3
  | rewindT2
  | fuelMove1
  | fuelMove2
  | fuelMove3
  | fuelMove4
  | fuelTurn
  | fuelWrite0
  | fuelWrite1
  | fuelWrite2
  | fuelWrite3
  | fuelRewind1
  | fuelRewind2
  | fuelRewind3
  | halt
deriving DecidableEq, Repr

private def step (action1 action2 : TapeAction) (target : State) :=
  some (TypedStep.mk target keepS action1 action2)

def next : State -> Option Bool -> Option Bool -> Option Bool ->
    Option (TypedStep State)
  | .seekRight => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepR .seekRight
      | none => step keepS keepL .eraseEnd1
  | .eraseEnd1 => fun _ _ _ => step keepS eraseL .eraseEnd2
  | .eraseEnd2 => fun _ _ _ => step keepS eraseL .eraseEnd3
  | .eraseEnd3 => fun _ _ _ => step keepS eraseL .eraseEnd4
  | .eraseEnd4 => fun _ _ _ =>
      step keepS eraseL .promoteLastCandidateTick
  | .promoteLastCandidateTick => fun _ _ r2 =>
      match r2 with
      | some false => step keepS (writeBitL true) .afterLast1
      | _ => none
  | .afterLast1 => fun _ _ _ => step keepS keepL .afterLast2
  | .afterLast2 => fun _ _ _ => step keepS keepL .afterLast3
  | .afterLast3 => fun _ _ _ => step keepS keepL .previousProbe
  | .previousProbe => fun _ _ r2 =>
      match r2 with
      | some false => step keepS (writeBitL true) .secondDone1
      | some true => step keepS keepL .rewindT2
      | none => none
  | .secondDone1 => fun _ _ _ => step keepS keepL .secondDone2
  | .secondDone2 => fun _ _ _ => step keepS keepL .secondDone3
  | .secondDone3 => fun _ _ _ => step keepS keepL .seekLimitDone
  | .seekLimitDone => fun _ _ r2 =>
      match r2 with
      | some false => step keepS keepL .skipTick1
      | some true => step keepS (writeBitL false) .rewindT2
      | none => none
  | .skipTick1 => fun _ _ _ => step keepS keepL .skipTick2
  | .skipTick2 => fun _ _ _ => step keepS keepL .skipTick3
  | .skipTick3 => fun _ _ _ => step keepS keepL .seekLimitDone
  | .rewindT2 => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepL .rewindT2
      | none => step keepS keepR .fuelMove1
  | .fuelMove1 => fun _ _ _ => step keepL keepS .fuelMove2
  | .fuelMove2 => fun _ _ _ => step keepL keepS .fuelMove3
  | .fuelMove3 => fun _ _ _ => step keepL keepS .fuelMove4
  | .fuelMove4 => fun _ _ _ => step keepL keepS .fuelTurn
  | .fuelTurn => fun _ _ _ => step keepR keepS .fuelWrite0
  | .fuelWrite0 => fun _ _ _ => step (writeBitR false) keepS .fuelWrite1
  | .fuelWrite1 => fun _ _ _ => step (writeBitR false) keepS .fuelWrite2
  | .fuelWrite2 => fun _ _ _ => step (writeBitR true) keepS .fuelWrite3
  | .fuelWrite3 => fun _ _ _ => step (writeBitL false) keepS .fuelRewind1
  | .fuelRewind1 => fun _ _ _ => step keepL keepS .fuelRewind2
  | .fuelRewind2 => fun _ _ _ => step keepL keepS .fuelRewind3
  | .fuelRewind3 => fun _ _ _ => step keepL keepS .halt
  | .halt => fun _ _ _ => none

def states : List State :=
  [.seekRight, .eraseEnd1, .eraseEnd2, .eraseEnd3, .eraseEnd4,
    .promoteLastCandidateTick, .afterLast1, .afterLast2, .afterLast3,
    .previousProbe,
    .secondDone1, .secondDone2, .secondDone3,
    .seekLimitDone, .skipTick1, .skipTick2, .skipTick3,
    .rewindT2, .fuelMove1, .fuelMove2, .fuelMove3, .fuelMove4,
    .fuelTurn, .fuelWrite0, .fuelWrite1, .fuelWrite2, .fuelWrite3,
    .fuelRewind1, .fuelRewind2, .fuelRewind3, .halt]

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

@[simp] theorem table_next : table.next = next := rfl

@[simp] theorem table_next_apply
    (s : State) (r0 r1 r2 : Option Bool) :
    table.next s r0 r1 r2 = next s r0 r1 r2 := rfl

def tickScanBits : Nat -> List Bool
  | 0 => []
  | n + 1 =>
      List.append [false, true, false, false] (tickScanBits n)

theorem tickScanBits_append_tick (n : Nat) :
    List.append (tickScanBits n) [false, true, false, false] =
      List.append [false, true, false, false] (tickScanBits n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        List.append
            (List.append [false, true, false, false] (tickScanBits n))
            [false, true, false, false] =
          List.append [false, true, false, false]
            (List.append [false, true, false, false] (tickScanBits n))
      exact congrArg
        (List.append [false, true, false, false]) ih

theorem stageNatBits_reverse_eq_done_tickScanBits (n : Nat) :
    (stageNatBits n).reverse =
      List.append [true, true, false, false] (tickScanBits n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [stageNatBits_succ]
      simp [ih, tickScanBits, List.append_assoc]
      exact tickScanBits_append_tick n
      done

theorem stageNatBits_eq_tickScanBits_reverse_done (n : Nat) :
    stageNatBits n =
      List.append (tickScanBits n).reverse [false, false, true, true] := by
  have h := congrArg List.reverse
    (stageNatBits_reverse_eq_done_tickScanBits n)
  unfold Languages.Word at *
  simpa [List.reverse_append] using h

theorem rolloverFields_reverse
    (pre : List Bool) (candidateFuel : Nat) :
    (List.append pre
      (List.append (stageNatBits 0)
        (stageNatBits (candidateFuel + 1)))).reverse =
      List.append [true, true, false, false]
        (List.append [false, true, false, false]
          (List.append (tickScanBits candidateFuel)
            (List.append [true, true, false, false] pre.reverse))) := by
  simp [List.reverse_append, stageNatBits_reverse_eq_done_tickScanBits,
    List.append_assoc]
  have h := congrArg
    (fun bits =>
      List.append bits
        (List.append [true, true, false, false] pre.reverse))
    (tickScanBits_append_tick candidateFuel)
  simpa [List.append_assoc] using h
  done

def leftScanTape (bits : List Bool)
    (right : List (Option Bool)) : Tape Bool :=
  match bits with
  | [] => tapeAtCells [] (none :: right)
  | bit :: rest =>
      tapeAtCells (List.append (rest.map some) [none])
        (some bit :: right)

theorem candidateInputBits_rollover_length
    (w : Word Bool) (candidateFuel : Nat) :
    (CandidateInputBits w 0 (candidateFuel + 1)).length =
      (CandidateInputBits w candidateFuel 0).length + 4 := by
  rw [RolloverTape.candidateInputBits_eq_fields,
    RolloverTape.candidateInputBits_eq_fields]
  simp [stageNatBits_length]
  lia

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
  | nil =>
      exact TypedStateTable.Leads.refl table _
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

theorem leads_seekRight_turn
    (bit : Bool) (rest : List Bool)
    (right : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .seekRight T0 T1
        (tapeAtCells
          (List.append ((bit :: rest).map some) [none])
          (none :: right)))
      (table.config .eraseEnd1 T0 T1
        (leftScanTape (bit :: rest) (none :: right))) := by
  apply TypedStateTable.leads_step table
    (by change State.seekRight ∈ states; simp [states])
    (st := ⟨State.eraseEnd1, keepS, keepS, keepL⟩)
  · rw [table_next_apply]
    simp [next, step, tapeAtCells, Tape.read]
  · rfl
  · rfl
  · rfl

theorem leads_fixed_keepL
    {s target : State}
    (hs : s ∈ states) (bit : Bool)
    (hnext : forall r0 r1,
      next s r0 r1 (some bit) = step keepS keepL target)
    (rest : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config s T0 T1 (leftScanTape (bit :: rest) right))
      (table.config target T0 T1
        (leftScanTape rest (some bit :: right))) := by
  apply TypedStateTable.leads_step table hs
    (st := ⟨target, keepS, keepS, keepL⟩)
  · rw [table_next_apply]
    exact hnext (Tape.read T0) (Tape.read T1)
  · rfl
  · rfl
  · cases rest <;> rfl

theorem leads_fixed_writeBitL
    {s target : State}
    (hs : s ∈ states) (readBit writeBit : Bool)
    (hnext : forall r0 r1,
      next s r0 r1 (some readBit) =
        step keepS (writeBitL writeBit) target)
    (rest : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config s T0 T1 (leftScanTape (readBit :: rest) right))
      (table.config target T0 T1
        (leftScanTape rest (some writeBit :: right))) := by
  apply TypedStateTable.leads_step table hs
    (st := ⟨target, keepS, keepS, writeBitL writeBit⟩)
  · rw [table_next_apply]
    exact hnext (Tape.read T0) (Tape.read T1)
  · rfl
  · rfl
  · cases rest <;> rfl

theorem leads_fixed_eraseL
    {s target : State}
    (hs : s ∈ states) (bit : Bool)
    (hnext : forall r0 r1,
      next s r0 r1 (some bit) = step keepS eraseL target)
    (rest : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config s T0 T1 (leftScanTape (bit :: rest) right))
      (table.config target T0 T1
        (leftScanTape rest (none :: right))) := by
  apply TypedStateTable.leads_step table hs
    (st := ⟨target, keepS, keepS, eraseL⟩)
  · rw [table_next_apply]
    exact hnext (Tape.read T0) (Tape.read T1)
  · rfl
  · rfl
  · cases rest <;> rfl

theorem leads_eraseEndAndPromote
    (tail : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .eraseEnd1 T0 T1
        (leftScanTape
          (true :: true :: false :: false ::
            false :: true :: false :: false :: tail)
          right))
      (table.config .previousProbe T0 T1
        (leftScanTape tail
          (some false :: some false :: some true :: some true ::
            none :: none :: none :: none :: right))) := by
  apply TypedStateTable.Leads.trans
    (leads_fixed_eraseL
      (s := State.eraseEnd1) (target := State.eraseEnd2)
      (by simp [states]) true (by intros; rfl)
      (true :: false :: false :: false :: true :: false :: false :: tail)
      right T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_eraseL
      (s := State.eraseEnd2) (target := State.eraseEnd3)
      (by simp [states]) true (by intros; rfl)
      (false :: false :: false :: true :: false :: false :: tail)
      (none :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_eraseL
      (s := State.eraseEnd3) (target := State.eraseEnd4)
      (by simp [states]) false (by intros; rfl)
      (false :: false :: true :: false :: false :: tail)
      (none :: none :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_eraseL
      (s := State.eraseEnd4) (target := State.promoteLastCandidateTick)
      (by simp [states]) false (by intros; rfl)
      (false :: true :: false :: false :: tail)
      (none :: none :: none :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_writeBitL
      (s := State.promoteLastCandidateTick) (target := State.afterLast1)
      (by simp [states]) false true (by intros; simp [next, step])
      (true :: false :: false :: tail)
      (none :: none :: none :: none :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.afterLast1) (target := State.afterLast2)
      (by simp [states]) true (by intros; rfl)
      (false :: false :: tail)
      (some true :: none :: none :: none :: none :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.afterLast2) (target := State.afterLast3)
      (by simp [states]) false (by intros; rfl)
      (false :: tail)
      (some true :: some true :: none :: none :: none :: none :: right)
      T0 T1)
  exact leads_fixed_keepL
    (s := State.afterLast3) (target := State.previousProbe)
    (by simp [states]) false (by intros; rfl) tail
    (some false :: some true :: some true ::
      none :: none :: none :: none :: right)
    T0 T1

theorem leads_previousZero
    (preRev : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .previousProbe T0 T1
        (leftScanTape (true :: true :: false :: false :: preRev) right))
      (table.config .rewindT2 T0 T1
        (leftScanTape (true :: false :: false :: preRev)
          (some true :: right))) := by
  exact leads_fixed_keepL
    (s := State.previousProbe) (target := State.rewindT2)
    (by simp [states]) true (by intros; simp [next, step])
    (true :: false :: false :: preRev) right T0 T1

theorem leads_secondDone
    (tail : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .previousProbe T0 T1
        (leftScanTape (false :: true :: false :: false :: tail) right))
      (table.config .seekLimitDone T0 T1
        (leftScanTape tail
          (some false :: some false :: some true :: some true :: right))) := by
  apply TypedStateTable.Leads.trans
    (leads_fixed_writeBitL
      (s := State.previousProbe) (target := State.secondDone1)
      (by simp [states]) false true (by intros; simp [next, step])
      (true :: false :: false :: tail) right T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.secondDone1) (target := State.secondDone2)
      (by simp [states]) true (by intros; rfl)
      (false :: false :: tail) (some true :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.secondDone2) (target := State.secondDone3)
      (by simp [states]) false (by intros; rfl)
      (false :: tail) (some true :: some true :: right) T0 T1)
  exact leads_fixed_keepL
    (s := State.secondDone3) (target := State.seekLimitDone)
    (by simp [states]) false (by intros; rfl) tail
    (some false :: some true :: some true :: right) T0 T1

theorem leads_seekTick
    (tail : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .seekLimitDone T0 T1
        (leftScanTape (false :: true :: false :: false :: tail) right))
      (table.config .seekLimitDone T0 T1
        (leftScanTape tail
          (some false :: some false :: some true :: some false :: right))) := by
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.seekLimitDone) (target := State.skipTick1)
      (by simp [states]) false (by intros; simp [next, step])
      (true :: false :: false :: tail) right T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.skipTick1) (target := State.skipTick2)
      (by simp [states]) true (by intros; rfl)
      (false :: false :: tail) (some false :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.skipTick2) (target := State.skipTick3)
      (by simp [states]) false (by intros; rfl)
      (false :: tail) (some true :: some false :: right) T0 T1)
  exact leads_fixed_keepL
    (s := State.skipTick3) (target := State.seekLimitDone)
    (by simp [states]) false (by intros; rfl) tail
    (some false :: some true :: some false :: right) T0 T1

theorem leads_seekTicks
    (n : Nat) (tail : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .seekLimitDone T0 T1
        (leftScanTape (List.append (tickScanBits n) tail) right))
      (table.config .seekLimitDone T0 T1
        (leftScanTape tail
          (List.append ((tickScanBits n).reverse.map some) right))) := by
  induction n generalizing right with
  | zero => exact TypedStateTable.Leads.refl table _
  | succ n ih =>
      have h := TypedStateTable.Leads.trans
        (leads_seekTick
          (List.append (tickScanBits n) tail) right T0 T1)
        (ih
          (some false :: some false :: some true :: some false :: right))
      simpa [tickScanBits, List.map_reverse, List.append_assoc,
        tickScanBits_append_tick] using h

theorem leads_limitDone
    (preRev : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .seekLimitDone T0 T1
        (leftScanTape (true :: true :: false :: false :: preRev) right))
      (table.config .rewindT2 T0 T1
        (leftScanTape (true :: false :: false :: preRev)
          (some false :: right))) := by
  exact leads_fixed_writeBitL
    (s := State.seekLimitDone) (target := State.rewindT2)
    (by simp [states]) true false (by intros; simp [next, step])
    (true :: false :: false :: preRev) right T0 T1

theorem leads_rewindT2
    (bits : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .rewindT2 T0 T1 (leftScanTape bits right))
      (table.config .fuelMove1 T0 T1
        (tapeAtCells [none]
          (List.append (bits.reverse.map some) right))) := by
  induction bits generalizing right with
  | nil =>
      apply TypedStateTable.leads_step table
        (by change State.rewindT2 ∈ states; simp [states])
        (st := ⟨State.fuelMove1, keepS, keepS, keepR⟩)
      · rw [table_next_apply]
        simp [leftScanTape, next, step, tapeAtCells, Tape.read]
      · rfl
      · rfl
      · cases right <;> rfl
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (leads_fixed_keepL
          (s := State.rewindT2) (target := State.rewindT2)
          (by simp [states]) bit (by intros; simp [next, step])
          rest right T0 T1)
      simpa [List.map_reverse, List.append_assoc] using
        ih (some bit :: right)

def fuelTransform (T : Tape Bool) : Tape Bool :=
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

theorem fuelTransform_source
    (left : List (Option Bool)) (fuel : Nat) :
    fuelTransform
        (tapeAtCells (none :: none :: none :: none :: left)
          (none :: List.append ((stageNatBits fuel).map some) [none])) =
      tapeAtCells left
        (none :: List.append ((stageNatBits (fuel + 1)).map some) [none]) := by
  rfl

theorem leads_fuelStep
    {s target : State} (hs : s ∈ states)
    (action1 : TapeAction)
    (hnext : forall r0 r1 r2,
      next s r0 r1 r2 = step action1 keepS target)
    (T0 T1 T2 : Tape Bool) :
    table.Leads
      (table.config s T0 T1 T2)
      (table.config target T0 (action1.apply T1) T2) := by
  apply TypedStateTable.leads_step table hs
    (st := ⟨target, keepS, action1, keepS⟩)
  · rw [table_next_apply]
    exact hnext (Tape.read T0) (Tape.read T1) (Tape.read T2)
  · rfl
  · rfl
  · rfl

theorem leads_fuelTransform (T0 T1 T2 : Tape Bool) :
    table.Leads
      (table.config .fuelMove1 T0 T1 T2)
      (table.config .halt T0 (fuelTransform T1) T2) := by
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelMove1) (target := State.fuelMove2)
      (by simp [states]) keepL (by intros; rfl) T0 T1 T2)
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelMove2) (target := State.fuelMove3)
      (by simp [states]) keepL (by intros; rfl) T0 _ T2)
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelMove3) (target := State.fuelMove4)
      (by simp [states]) keepL (by intros; rfl) T0 _ T2)
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelMove4) (target := State.fuelTurn)
      (by simp [states]) keepL (by intros; rfl) T0 _ T2)
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelTurn) (target := State.fuelWrite0)
      (by simp [states]) keepR (by intros; rfl) T0 _ T2)
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelWrite0) (target := State.fuelWrite1)
      (by simp [states]) (writeBitR false) (by intros; rfl) T0 _ T2)
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelWrite1) (target := State.fuelWrite2)
      (by simp [states]) (writeBitR false) (by intros; rfl) T0 _ T2)
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelWrite2) (target := State.fuelWrite3)
      (by simp [states]) (writeBitR true) (by intros; rfl) T0 _ T2)
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelWrite3) (target := State.fuelRewind1)
      (by simp [states]) (writeBitL false) (by intros; rfl) T0 _ T2)
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelRewind1) (target := State.fuelRewind2)
      (by simp [states]) keepL (by intros; rfl) T0 _ T2)
  apply TypedStateTable.Leads.trans
    (leads_fuelStep
      (s := State.fuelRewind2) (target := State.fuelRewind3)
      (by simp [states]) keepL (by intros; rfl) T0 _ T2)
  simpa [fuelTransform] using
    leads_fuelStep
      (s := State.fuelRewind3) (target := State.halt)
      (by simp [states]) keepL (by intros; rfl) T0 _ T2

theorem leads_rolloverFields
    (pre : List Bool) (candidateFuel fuel : Nat)
    (left : List (Option Bool)) (T0 : Tape Bool) :
    table.Leads
      (table.config .seekRight T0
        (tapeAtCells (none :: none :: none :: none :: left)
          (none :: List.append ((stageNatBits fuel).map some) [none]))
        (tapeAtCells [none]
          (List.append
            ((List.append pre
              (List.append (stageNatBits 0)
                (stageNatBits (candidateFuel + 1)))).map some)
            [none])))
      (table.config .halt T0
        (tapeAtCells left
          (none :: List.append
            ((stageNatBits (fuel + 1)).map some) [none]))
        (tapeAtCells [none]
          (List.append
            ((List.append pre
              (List.append (stageNatBits candidateFuel)
                (stageNatBits 0))).map some)
            (List.replicate 5 none)))) := by
  let T1 :=
    tapeAtCells (none :: none :: none :: none :: left)
      (none :: List.append ((stageNatBits fuel).map some) [none])
  apply TypedStateTable.Leads.trans
    (leads_seekRight_bits
      (List.append pre
        (List.append (stageNatBits 0)
          (stageNatBits (candidateFuel + 1))))
      [none] [] T0 T1)
  have hrev := congrArg (List.map some)
    (rolloverFields_reverse pre candidateFuel)
  rw [hrev]
  have hturn := leads_seekRight_turn true
    (true :: false :: false :: false :: true :: false :: false ::
      List.append (tickScanBits candidateFuel)
        (true :: true :: false :: false :: pre.reverse))
    [] T0 T1
  apply TypedStateTable.Leads.trans
    (by simpa [List.map_append, List.append_assoc] using hturn)
  apply TypedStateTable.Leads.trans
    (leads_eraseEndAndPromote
      (List.append (tickScanBits candidateFuel)
        (true :: true :: false :: false :: pre.reverse))
      [none] T0 T1)
  cases candidateFuel with
  | zero =>
      apply TypedStateTable.Leads.trans
        (by
          simpa [tickScanBits] using
            leads_previousZero pre.reverse
              [some false, some false, some true, some true,
                none, none, none, none, none]
              T0 T1)
      apply TypedStateTable.Leads.trans
        (leads_rewindT2
          (true :: false :: false :: pre.reverse)
          [some true, some false, some false, some true, some true,
            none, none, none, none, none]
          T0 T1)
      have hf := leads_fuelTransform T0 T1
        (tapeAtCells [none]
          (List.append
            ((true :: false :: false :: pre.reverse).reverse.map some)
            [some true, some false, some false, some true, some true,
              none, none, none, none, none]))
      have hfuel :
          fuelTransform T1 =
            tapeAtCells left
              (none :: List.append
                ((stageNatBits (fuel + 1)).map some) [none]) := by
        exact fuelTransform_source left fuel
      rw [hfuel] at hf
      simpa [stageNatBits_eq_tickScanBits_reverse_done, tickScanBits,
        List.map_reverse, List.map_append, List.append_assoc] using hf
  | succ n =>
      apply TypedStateTable.Leads.trans
        (by
          simpa [tickScanBits, List.append_assoc] using
            leads_secondDone
              (List.append (tickScanBits n)
                (true :: true :: false :: false :: pre.reverse))
              [some false, some false, some true, some true,
                none, none, none, none, none]
              T0 T1)
      apply TypedStateTable.Leads.trans
        (leads_seekTicks n
          (true :: true :: false :: false :: pre.reverse)
          [some false, some false, some true, some true,
            some false, some false, some true, some true,
            none, none, none, none, none]
          T0 T1)
      apply TypedStateTable.Leads.trans
        (leads_limitDone pre.reverse
          (List.append ((tickScanBits n).reverse.map some)
            [some false, some false, some true, some true,
              some false, some false, some true, some true,
              none, none, none, none, none])
          T0 T1)
      apply TypedStateTable.Leads.trans
        (leads_rewindT2
          (true :: false :: false :: pre.reverse)
          (some false ::
            List.append ((tickScanBits n).reverse.map some)
              [some false, some false, some true, some true,
                some false, some false, some true, some true,
                none, none, none, none, none])
          T0 T1)
      have hf := leads_fuelTransform T0 T1
          (tapeAtCells [none]
            (List.append
              ((true :: false :: false :: pre.reverse).reverse.map some)
              (some false ::
                List.append ((tickScanBits n).reverse.map some)
                  [some false, some false, some true, some true,
                    some false, some false, some true, some true,
                    none, none, none, none, none])))
      have hfuel :
          fuelTransform T1 =
            tapeAtCells left
              (none :: List.append
                ((stageNatBits (fuel + 1)).map some) [none]) := by
        exact fuelTransform_source left fuel
      rw [hfuel] at hf
      simpa [stageNatBits_eq_tickScanBits_reverse_done, tickScanBits,
        List.map_reverse, List.map_append, List.append_assoc] using hf
      done

def paddedRawTape (raw : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append (raw.map some) (List.replicate 5 none))

theorem paddedRawTape_equiv_restaged (raw : Word Bool) :
    Tape.Equiv (paddedRawTape raw)
      (PersistentRestaging.restagedRawTape raw) := by
  cases raw with
  | nil =>
      simp [paddedRawTape, PersistentRestaging.restagedRawTape,
        tapeAtCells, Tape.Equiv, Tape.dropTrailingNone]
  | cons head tail =>
      simp [paddedRawTape, PersistentRestaging.restagedRawTape,
        tapeAtCells, Tape.Equiv, Tape.dropTrailingNone,
        FoC.Computability.dropTrailingNone_append_none]
      simpa using
        FoC.Computability.dropTrailingNone_append_replicate_none
          (tail.map some) 5

theorem cleanedFuelTape_rollover_source
    (w : Word Bool) (candidateFuel fuel : Nat) :
    PersistentRestaging.cleanedFuelTape
        (CandidateInputBits w 0 (candidateFuel + 1)) fuel =
      tapeAtCells
        (none :: none :: none :: none ::
          List.replicate
            ((CandidateInputBits w candidateFuel 0).length + 1) none)
        (none :: List.append ((stageNatBits fuel).map some) [none]) := by
  unfold PersistentRestaging.cleanedFuelTape
  have hlen := candidateInputBits_rollover_length w candidateFuel
  have hleft :
      List.replicate
          ((CandidateInputBits w 0 (candidateFuel + 1)).length + 1)
          (none : Option Bool) =
        none :: none :: none :: none ::
          List.replicate
            ((CandidateInputBits w candidateFuel 0).length + 1) none := by
    rw [hlen]
    rw [show
        (CandidateInputBits w candidateFuel 0).length + 4 + 1 =
          4 + ((CandidateInputBits w candidateFuel 0).length + 1) by
      lia]
    simpa using
      list_replicate_add_append (none : Option Bool) 4
        ((CandidateInputBits w candidateFuel 0).length + 1) []
  rw [hleft]

theorem leads_candidateRollover
    (w : Word Bool) (candidateFuel sourceFuel : Nat)
    (T0 : Tape Bool) :
    table.Leads
      (table.config .seekRight T0
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 (candidateFuel + 1)) sourceFuel)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w 0 (candidateFuel + 1))))
      (table.config .halt T0
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w candidateFuel 0) (sourceFuel + 1))
        (paddedRawTape
          (CandidateInputBits w candidateFuel 0))) := by
  rw [cleanedFuelTape_rollover_source]
  simpa [PersistentRestaging.cleanedFuelTape,
    PersistentRestaging.restagedRawTape, paddedRawTape,
    RolloverTape.candidateInputBits_eq_fields, RolloverTape.prefixBits,
    List.map_append, List.append_assoc] using
      leads_rolloverFields
        (List.append (stageNatBits w.length) (cellsBits w))
        candidateFuel sourceFuel
        (List.replicate
          ((CandidateInputBits w candidateFuel 0).length + 1) none)
        T0

end U12CandidateRollover
end BoundedFuelPairSearch
end Computability
end FoC
