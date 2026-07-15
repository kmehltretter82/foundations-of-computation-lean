import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.DiagonalSchedule
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.PersistentRestaging
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
namespace U12DiagonalAdvance

theorem candidateCode_eq_fields
    (w : Word Bool) (limit candidateFuel : Nat) :
    CandidateCode w limit candidateFuel =
      List.append (encodeNat w.length)
        (List.append (encodeCellsAppend (w.map some) [])
          (List.append (encodeNat limit) (encodeNat candidateFuel))) := by
  unfold CandidateCode
  unfold PairedRecognizerDovetailControllerStageAttemptFuelInputCode
  unfold DovetailLayout.stageInputCodeAppend
  unfold encodeBoolWordAppend
  unfold encodeCellListAppend
  unfold encodeNatAppend
  simp only [List.length_map]
  have hcand :
      List.append (encodeNat candidateFuel) [] =
        encodeNat candidateFuel :=
    List.append_nil _
  rw [hcand]
  apply congrArg (List.append (encodeNat w.length))
  exact encodeCellsAppend_append (w.map some) []
    (List.append (encodeNat limit) (encodeNat candidateFuel))
  done

theorem candidateInputBits_eq_fields
    (w : Word Bool) (limit candidateFuel : Nat) :
    CandidateInputBits w limit candidateFuel =
      List.append (stageNatBits w.length)
        (List.append (cellsBits w)
          (List.append (stageNatBits limit)
            (stageNatBits candidateFuel))) := by
  unfold CandidateInputBits
  rw [candidateCode_eq_fields]
  rw [encodeCodeWordAsInput_append]
  rw [encodeCodeWordAsInput_append]
  rw [encodeCodeWordAsInput_append]
  rfl
  done

inductive State where
  | seekRight
  | endDone1
  | endDone2
  | endDone3
  | endDone4
  | candidateProbe
  | candidateTick1
  | candidateTick2
  | candidateTick3
  | boundary1
  | boundary2
  | boundary3
  | promoteLimitTick
  | rewindLeft
  | halt
deriving DecidableEq, Repr

private def step2 (action2 : TapeAction) (target : State) :=
  some (TypedStep.mk target keepS keepS action2)

def next : State -> Option Bool -> Option Bool -> Option Bool ->
    Option (TypedStep State)
  | .seekRight => fun _ _ r2 =>
      match r2 with
      | some _ => step2 keepR .seekRight
      | none => step2 keepL .endDone1
  | .endDone1 => fun _ _ _ => step2 keepL .endDone2
  | .endDone2 => fun _ _ _ => step2 keepL .endDone3
  | .endDone3 => fun _ _ _ => step2 keepL .endDone4
  | .endDone4 => fun _ _ _ => step2 keepL .candidateProbe
  | .candidateProbe => fun _ _ r2 =>
      match r2 with
      | some false => step2 keepL .candidateTick1
      | some true => step2 (writeBitL false) .boundary1
      | none => none
  | .candidateTick1 => fun _ _ _ => step2 keepL .candidateTick2
  | .candidateTick2 => fun _ _ _ => step2 keepL .candidateTick3
  | .candidateTick3 => fun _ _ _ => step2 keepL .candidateProbe
  | .boundary1 => fun _ _ _ => step2 keepL .boundary2
  | .boundary2 => fun _ _ _ => step2 keepL .boundary3
  | .boundary3 => fun _ _ _ => step2 keepL .promoteLimitTick
  | .promoteLimitTick => fun _ _ r2 =>
      match r2 with
      | some false => step2 (writeBitL true) .rewindLeft
      | _ => none
  | .rewindLeft => fun _ _ r2 =>
      match r2 with
      | some _ => step2 keepL .rewindLeft
      | none => step2 keepR .halt
  | .halt => fun _ _ _ => none

def states : List State :=
  [.seekRight, .endDone1, .endDone2, .endDone3, .endDone4,
    .candidateProbe, .candidateTick1, .candidateTick2, .candidateTick3,
    .boundary1, .boundary2, .boundary3, .promoteLimitTick,
    .rewindLeft, .halt]

theorem next_target_mem :
    forall s : State, s ∈ states ->
      forall r0 r1 r2 st, next s r0 r1 r2 = some st ->
        st.target ∈ states := by
  intro s hs r0 r1 r2 st hnext
  cases s <;> simp only [next] at hnext
  all_goals repeat' first | split at hnext | simp only [step2] at hnext
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
      List.append (tickScanBits n) [false, true, false, false]

theorem tickScanBits_append_tick (n : Nat) :
    List.append (tickScanBits n) [false, true, false, false] =
      List.append [false, true, false, false] (tickScanBits n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        List.append
            (List.append (tickScanBits n) [false, true, false, false])
            [false, true, false, false] =
          List.append [false, true, false, false]
            (List.append (tickScanBits n) [false, true, false, false])
      calc
        List.append
            (List.append (tickScanBits n) [false, true, false, false])
            [false, true, false, false] =
          List.append
            (List.append [false, true, false, false] (tickScanBits n))
            [false, true, false, false] :=
              congrArg
                (fun bits =>
                  List.append bits [false, true, false, false]) ih
        _ = List.append [false, true, false, false]
              (List.append (tickScanBits n)
                [false, true, false, false]) := by rfl
      done

theorem stageNatBits_reverse_eq_done_tickScanBits (n : Nat) :
    (stageNatBits n).reverse =
      List.append [true, true, false, false] (tickScanBits n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [stageNatBits_succ]
      simp [tickScanBits, ih, List.append_assoc]
      done

theorem stageNatBits_eq_tickScanBits_reverse_done (n : Nat) :
    stageNatBits n =
      List.append (tickScanBits n).reverse [false, false, true, true] := by
  have h := congrArg List.reverse
    (stageNatBits_reverse_eq_done_tickScanBits n)
  unfold Languages.Word at *
  simpa [List.reverse_append] using h

theorem positiveFields_reverse
    (pre : List Bool) (limit candidateFuel : Nat) :
    (List.append pre
      (List.append (stageNatBits (limit + 1))
        (stageNatBits candidateFuel))).reverse =
      List.append [true, true, false, false]
        (List.append (tickScanBits candidateFuel)
            (List.append [true, true, false, false]
            (List.append [false, true, false, false]
              (List.append (tickScanBits limit) pre.reverse)))) := by
  simp [List.reverse_append, stageNatBits_reverse_eq_done_tickScanBits,
    List.append_assoc]
  have h := congrArg
    (fun bits => List.append bits pre.reverse)
    (tickScanBits_append_tick limit)
  simpa [List.append_assoc] using h
  done

def leftScanTape (bits : List Bool)
    (right : List (Option Bool)) : Tape Bool :=
  match bits with
  | [] => tapeAtCells [] (none :: right)
  | bit :: rest =>
      tapeAtCells (List.append (rest.map some) [none])
        (some bit :: right)

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
          simp [next, step2, tapeAtCells, Tape.read]
          done
        · rfl
          done
        · rfl
          done
        · cases rest <;> rfl
          done
      · simpa [List.map_reverse, List.append_assoc] using
          ih (some bit :: left)
        done

theorem leads_seekRight_turn
    (bit : Bool) (rest : List Bool)
    (right : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .seekRight T0 T1
        (tapeAtCells
          (List.append ((bit :: rest).map some) [none])
          (none :: right)))
      (table.config .endDone1 T0 T1
        (leftScanTape (bit :: rest) (none :: right))) := by
  apply TypedStateTable.leads_step table
    (by change State.seekRight ∈ states; simp [states])
    (st := ⟨State.endDone1, keepS, keepS, keepL⟩)
  · rw [table_next_apply]
    simp [next, step2, tapeAtCells, Tape.read]
  · rfl
  · rfl
  · rfl
  done

theorem leads_fixed_keepL
    {s target : State}
    (hs : s ∈ states)
    (bit : Bool)
    (hnext : forall r0 r1,
      next s r0 r1 (some bit) = step2 keepL target)
    (rest : List Bool)
    (right : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config s T0 T1
        (leftScanTape (bit :: rest) right))
      (table.config target T0 T1
        (leftScanTape rest (some bit :: right))) := by
  apply TypedStateTable.leads_step table hs
    (st := ⟨target, keepS, keepS, keepL⟩)
  · rw [table_next_apply]
    exact hnext (Tape.read T0) (Tape.read T1)
  · rfl
  · rfl
  · cases rest <;> rfl
  done

theorem leads_endDone
    (tail : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .endDone1 T0 T1
        (leftScanTape (true :: true :: false :: false :: tail) right))
      (table.config .candidateProbe T0 T1
        (leftScanTape tail
          (some false :: some false :: some true :: some true :: right))) := by
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.endDone1) (target := State.endDone2)
      (by simp [states]) true (by intros; rfl)
      (true :: false :: false :: tail) right T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.endDone2) (target := State.endDone3)
      (by simp [states]) true (by intros; rfl)
      (false :: false :: tail) (some true :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.endDone3) (target := State.endDone4)
      (by simp [states]) false (by intros; rfl)
      (false :: tail) (some true :: some true :: right) T0 T1)
  exact leads_fixed_keepL
    (s := State.endDone4) (target := State.candidateProbe)
    (by simp [states]) false (by intros; rfl)
    tail
    (some false :: some true :: some true :: right) T0 T1

theorem leads_candidateTick
    (tail : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .candidateProbe T0 T1
        (leftScanTape (false :: true :: false :: false :: tail) right))
      (table.config .candidateProbe T0 T1
        (leftScanTape tail
          (some false :: some false :: some true :: some false :: right))) := by
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.candidateProbe) (target := State.candidateTick1)
      (by simp [states]) false (by intros; simp [next, step2])
      (true :: false :: false :: tail) right T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.candidateTick1) (target := State.candidateTick2)
      (by simp [states]) true (by intros; rfl)
      (false :: false :: tail) (some false :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.candidateTick2) (target := State.candidateTick3)
      (by simp [states]) false (by intros; rfl)
      (false :: tail) (some true :: some false :: right) T0 T1)
  exact leads_fixed_keepL
    (s := State.candidateTick3) (target := State.candidateProbe)
    (by simp [states]) false (by intros; rfl)
    tail
    (some false :: some true :: some false :: right) T0 T1

theorem leads_candidateTicks
    (n : Nat) (tail : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .candidateProbe T0 T1
        (leftScanTape
          (List.append (tickScanBits n) tail) right))
      (table.config .candidateProbe T0 T1
        (leftScanTape tail
          (List.append ((tickScanBits n).reverse.map some) right))) := by
  induction n generalizing tail right with
  | zero =>
      exact TypedStateTable.Leads.refl table _
  | succ n ih =>
      have h := TypedStateTable.Leads.trans
        (ih (List.append [false, true, false, false] tail) right)
        (leads_candidateTick tail
          (List.append ((tickScanBits n).reverse.map some) right)
          T0 T1)
      simpa [tickScanBits, List.map_reverse, List.append_assoc] using h

theorem leads_fixed_writeBitL
    {s target : State}
    (hs : s ∈ states)
    (readBit writeBit : Bool)
    (hnext : forall r0 r1,
      next s r0 r1 (some readBit) =
        step2 (writeBitL writeBit) target)
    (rest : List Bool)
    (right : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config s T0 T1
        (leftScanTape (readBit :: rest) right))
      (table.config target T0 T1
        (leftScanTape rest (some writeBit :: right))) := by
  apply TypedStateTable.leads_step table hs
    (st := ⟨target, keepS, keepS, writeBitL writeBit⟩)
  · rw [table_next_apply]
    exact hnext (Tape.read T0) (Tape.read T1)
  · rfl
  · rfl
  · cases rest <;> rfl
  done

theorem leads_positiveBoundary
    (prefixRev : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .candidateProbe T0 T1
        (leftScanTape
          (true :: true :: false :: false ::
            false :: true :: false :: false :: prefixRev)
          right))
      (table.config .rewindLeft T0 T1
        (leftScanTape (true :: false :: false :: prefixRev)
          (some true :: some false :: some false :: some true ::
            some false :: right))) := by
  apply TypedStateTable.Leads.trans
    (leads_fixed_writeBitL
      (s := State.candidateProbe) (target := State.boundary1)
      (by simp [states]) true false
      (by intros; simp [next, step2])
      (true :: false :: false ::
        false :: true :: false :: false :: prefixRev)
      right T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.boundary1) (target := State.boundary2)
      (by simp [states]) true (by intros; rfl)
      (false :: false :: false :: true :: false :: false :: prefixRev)
      (some false :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.boundary2) (target := State.boundary3)
      (by simp [states]) false (by intros; rfl)
      (false :: false :: true :: false :: false :: prefixRev)
      (some true :: some false :: right) T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_fixed_keepL
      (s := State.boundary3) (target := State.promoteLimitTick)
      (by simp [states]) false (by intros; rfl)
      (false :: true :: false :: false :: prefixRev)
      (some false :: some true :: some false :: right) T0 T1)
  exact leads_fixed_writeBitL
    (s := State.promoteLimitTick) (target := State.rewindLeft)
    (by simp [states]) false true
    (by intros; simp [next, step2])
    (true :: false :: false :: prefixRev)
    (some false :: some false :: some true :: some false :: right) T0 T1

theorem leads_rewindLeft
    (bits : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .rewindLeft T0 T1
        (leftScanTape bits right))
      (table.config .halt T0 T1
        (tapeAtCells [none]
          (List.append (bits.reverse.map some) right))) := by
  induction bits generalizing right with
  | nil =>
      apply TypedStateTable.leads_step table
        (by change State.rewindLeft ∈ states; simp [states])
        (st := ⟨State.halt, keepS, keepS, keepR⟩)
      · rw [table_next_apply]
        simp [leftScanTape, next, step2, tapeAtCells, Tape.read]
      · rfl
      · rfl
      · cases right <;> rfl
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (leads_fixed_keepL
          (s := State.rewindLeft) (target := State.rewindLeft)
          (by simp [states]) bit (by intros; simp [next, step2])
          rest right T0 T1)
      simpa [List.map_reverse, List.append_assoc] using
        ih (some bit :: right)

theorem leads_positiveFields
    (pre : List Bool) (limit candidateFuel : Nat)
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .seekRight T0 T1
        (tapeAtCells [none]
          (List.append
            ((List.append pre
              (List.append (stageNatBits (limit + 1))
                (stageNatBits candidateFuel))).map some)
            [none])))
      (table.config .halt T0 T1
        (tapeAtCells [none]
          (List.append
            ((List.append pre
              (List.append (stageNatBits limit)
                (stageNatBits (candidateFuel + 1)))).map some)
            [none]))) := by
  apply TypedStateTable.Leads.trans
    (leads_seekRight_bits
      (List.append pre
        (List.append (stageNatBits (limit + 1))
          (stageNatBits candidateFuel)))
      [none] [] T0 T1)
  have hrev := congrArg (List.map some)
    (positiveFields_reverse pre limit candidateFuel)
  rw [hrev]
  have hturn := leads_seekRight_turn true
    (true :: false :: false ::
      List.append (tickScanBits candidateFuel)
        (true :: true :: false :: false ::
          false :: true :: false :: false ::
          List.append (tickScanBits limit) pre.reverse))
    [] T0 T1
  apply TypedStateTable.Leads.trans
    (by
      simpa [List.map_append, List.append_assoc] using hturn)
  apply TypedStateTable.Leads.trans
    (leads_endDone
      (List.append (tickScanBits candidateFuel)
        (true :: true :: false :: false ::
          false :: true :: false :: false ::
          List.append (tickScanBits limit) pre.reverse))
      [none] T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_candidateTicks candidateFuel
      (true :: true :: false :: false ::
        false :: true :: false :: false ::
        List.append (tickScanBits limit) pre.reverse)
      [some false, some false, some true, some true, none]
      T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_positiveBoundary
      (List.append (tickScanBits limit) pre.reverse)
      (List.append ((tickScanBits candidateFuel).reverse.map some)
        [some false, some false, some true, some true, none])
      T0 T1)
  have hrewind := leads_rewindLeft
    (true :: false :: false ::
      List.append (tickScanBits limit) pre.reverse)
    (some true :: some false :: some false :: some true :: some false ::
      List.append ((tickScanBits candidateFuel).reverse.map some)
        [some false, some false, some true, some true, none])
    T0 T1
  simpa [stageNatBits_eq_tickScanBits_reverse_done,
    List.map_reverse, List.map_append, List.append_assoc] using hrewind
  done

theorem leads_positiveCandidate
    (w : Word Bool) (limit candidateFuel : Nat)
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .seekRight T0 T1
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w (limit + 1) candidateFuel)))
      (table.config .halt T0 T1
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w limit (candidateFuel + 1)))) := by
  simpa [PersistentRestaging.restagedRawTape,
    candidateInputBits_eq_fields, List.map_append,
    List.append_assoc] using
      leads_positiveFields
        (List.append (stageNatBits w.length) (cellsBits w))
        limit candidateFuel T0 T1

end U12DiagonalAdvance
end BoundedFuelPairSearch
end Computability
end FoC
