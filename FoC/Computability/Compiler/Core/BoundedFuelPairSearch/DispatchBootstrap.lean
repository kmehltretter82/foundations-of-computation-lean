import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SourceRollover
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.CheckerRollover
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.DiagonalAdvance
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.CandidateRollover
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.PhaseFusion

set_option doc.verso true

/-!
# Fuel-pair dispatch bootstrap

Finite dispatch over candidate, source, and checker rollover branches.
-/

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
namespace U12DispatchBootstrap

inductive Branch where
  | positive
  | candidate
  | source
  | checker
deriving DecidableEq, Repr

inductive State where
  | length0
  | length1
  | length2
  | lengthKind
  | cell0
  | cellKind
  | cell2
  | cell3
  | limit2
  | limitKind
  | candidate0
  | candidate1
  | candidate2
  | candidateKind
  | source0
  | source1
  | source2
  | sourceKind
  | sourceBack2 (branch : Branch)
  | sourceBack1 (branch : Branch)
  | sourceBack0 (branch : Branch)
  | rewind (branch : Branch)
  | positive (state : U12DiagonalAdvance.State)
  | candidate (state : U12CandidateRollover.State)
  | source (state : U12SourceRollover.State)
  | checker (state : U12CheckerRollover.State)
  | halt
deriving DecidableEq, Repr

private def step
    (action0 action1 action2 : TapeAction) (target : State) :
    Option (TypedStep State) :=
  some (TypedStep.mk target action0 action1 action2)

private def mapStep {sigma : Type}
    (f : sigma -> State) (st : TypedStep sigma) : TypedStep State :=
  TypedStep.mk (f st.target) st.action0 st.action1 st.action2

def positiveState : U12DiagonalAdvance.State -> State
  | .halt => .halt
  | state => .positive state

def candidateState : U12CandidateRollover.State -> State
  | .halt => .halt
  | state => .candidate state

def sourceState : U12SourceRollover.State -> State
  | .halt => .halt
  | state => .source state

def checkerState : U12CheckerRollover.State -> State
  | .halt => .halt
  | state => .checker state

def branchStart : Branch -> State
  | .positive => .positive .seekRight
  | .candidate => .candidate .seekRight
  | .source => .source .seekRight
  | .checker => .checker .seekRight

def next : State -> Option Bool -> Option Bool -> Option Bool ->
    Option (TypedStep State)
  | .length0 => fun _ _ r2 =>
      match r2 with
      | some false => step keepS keepS keepR .length1
      | _ => none
  | .length1 => fun _ _ r2 =>
      match r2 with
      | some false => step keepS keepS keepR .length2
      | _ => none
  | .length2 => fun _ _ r2 =>
      match r2 with
      | some true => step keepS keepS keepR .lengthKind
      | _ => none
  | .lengthKind => fun _ _ r2 =>
      match r2 with
      | some false => step keepS keepS keepR .length0
      | some true => step keepS keepS keepR .cell0
      | none => none
  | .cell0 => fun _ _ r2 =>
      match r2 with
      | some false => step keepS keepS keepR .cellKind
      | _ => none
  | .cellKind => fun _ _ r2 =>
      match r2 with
      | some true => step keepS keepS keepR .cell2
      | some false => step keepS keepS keepR .limit2
      | none => none
  | .cell2 => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepS keepR .cell3
      | none => none
  | .cell3 => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepS keepR .cell0
      | none => none
  | .limit2 => fun _ _ r2 =>
      match r2 with
      | some true => step keepS keepS keepR .limitKind
      | _ => none
  | .limitKind => fun _ _ r2 =>
      match r2 with
      | some false => step keepS keepS keepS (.rewind .positive)
      | some true => step keepS keepS keepR .candidate0
      | none => none
  | .candidate0 => fun _ _ r2 =>
      match r2 with
      | some false => step keepS keepS keepR .candidate1
      | _ => none
  | .candidate1 => fun _ _ r2 =>
      match r2 with
      | some false => step keepS keepS keepR .candidate2
      | _ => none
  | .candidate2 => fun _ _ r2 =>
      match r2 with
      | some true => step keepS keepS keepR .candidateKind
      | _ => none
  | .candidateKind => fun _ _ r2 =>
      match r2 with
      | some false => step keepS keepS keepS (.rewind .candidate)
      | some true => step keepS keepR keepS .source0
      | none => none
  | .source0 => fun _ r1 _ =>
      match r1 with
      | some false => step keepS keepR keepS .source1
      | _ => none
  | .source1 => fun _ r1 _ =>
      match r1 with
      | some false => step keepS keepR keepS .source2
      | _ => none
  | .source2 => fun _ r1 _ =>
      match r1 with
      | some true => step keepS keepR keepS .sourceKind
      | _ => none
  | .sourceKind => fun _ r1 _ =>
      match r1 with
      | some false => step keepS keepL keepS (.sourceBack2 .source)
      | some true => step keepS keepL keepS (.sourceBack2 .checker)
      | none => none
  | .sourceBack2 branch => fun _ _ _ =>
      step keepS keepL keepS (.sourceBack1 branch)
  | .sourceBack1 branch => fun _ _ _ =>
      step keepS keepL keepS (.sourceBack0 branch)
  | .sourceBack0 branch => fun _ _ _ =>
      step keepS keepL keepS (.rewind branch)
  | .rewind branch => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepS keepL (.rewind branch)
      | none => step keepS keepS keepR (branchStart branch)
  | .positive state => fun r0 r1 r2 =>
      (U12DiagonalAdvance.next state r0 r1 r2).map
        (mapStep positiveState)
  | .candidate state => fun r0 r1 r2 =>
      (U12CandidateRollover.next state r0 r1 r2).map
        (mapStep candidateState)
  | .source state => fun r0 r1 r2 =>
      (U12SourceRollover.next state r0 r1 r2).map
        (mapStep sourceState)
  | .checker state => fun r0 r1 r2 =>
      (U12CheckerRollover.next state r0 r1 r2).map
        (mapStep checkerState)
  | .halt => fun _ _ _ => none

def dispatchStates : List State :=
  [.length0, .length1, .length2, .lengthKind,
    .cell0, .cellKind, .cell2, .cell3,
    .limit2, .limitKind,
    .candidate0, .candidate1, .candidate2, .candidateKind,
    .source0, .source1, .source2, .sourceKind,
    .sourceBack2 .positive, .sourceBack1 .positive,
      .sourceBack0 .positive,
    .sourceBack2 .candidate, .sourceBack1 .candidate,
      .sourceBack0 .candidate,
    .sourceBack2 .source, .sourceBack1 .source, .sourceBack0 .source,
    .sourceBack2 .checker, .sourceBack1 .checker, .sourceBack0 .checker,
    .rewind .positive, .rewind .candidate, .rewind .source,
    .rewind .checker]

def states : List State :=
  List.append dispatchStates
    (List.append (U12DiagonalAdvance.states.map State.positive)
      (List.append (U12CandidateRollover.states.map State.candidate)
        (List.append (U12SourceRollover.states.map State.source)
          (List.append (U12CheckerRollover.states.map State.checker)
            [.halt]))))

theorem state_mem : forall state : State, state ∈ states
  | .length0 => by simp [states, dispatchStates]
  | .length1 => by simp [states, dispatchStates]
  | .length2 => by simp [states, dispatchStates]
  | .lengthKind => by simp [states, dispatchStates]
  | .cell0 => by simp [states, dispatchStates]
  | .cellKind => by simp [states, dispatchStates]
  | .cell2 => by simp [states, dispatchStates]
  | .cell3 => by simp [states, dispatchStates]
  | .limit2 => by simp [states, dispatchStates]
  | .limitKind => by simp [states, dispatchStates]
  | .candidate0 => by simp [states, dispatchStates]
  | .candidate1 => by simp [states, dispatchStates]
  | .candidate2 => by simp [states, dispatchStates]
  | .candidateKind => by simp [states, dispatchStates]
  | .source0 => by simp [states, dispatchStates]
  | .source1 => by simp [states, dispatchStates]
  | .source2 => by simp [states, dispatchStates]
  | .sourceKind => by simp [states, dispatchStates]
  | .sourceBack2 branch => by
      cases branch <;> simp [states, dispatchStates]
  | .sourceBack1 branch => by
      cases branch <;> simp [states, dispatchStates]
  | .sourceBack0 branch => by
      cases branch <;> simp [states, dispatchStates]
  | .rewind branch => by
      cases branch <;> simp [states, dispatchStates]
  | State.positive localState => by
      cases localState <;>
        simp [states, dispatchStates, U12DiagonalAdvance.states]
  | State.candidate localState => by
      cases localState <;>
        simp [states, dispatchStates, U12CandidateRollover.states]
  | State.source localState => by
      cases localState <;>
        simp [states, dispatchStates, U12SourceRollover.states]
  | State.checker localState => by
      cases localState <;>
        simp [states, dispatchStates, U12CheckerRollover.states]
  | .halt => by simp [states, dispatchStates]

theorem next_target_mem :
    forall s : State, s ∈ states ->
      forall r0 r1 r2 st, next s r0 r1 r2 = some st ->
        st.target ∈ states := by
  intro _s _hs _r0 _r1 _r2 st _hnext
  exact state_mem st.target

def table : TypedStateTable State :=
  TypedStateTable.ofList states .length0 .halt next
    (by simp [states, dispatchStates])
    (by simp [states])
    (by intros; rfl)
    next_target_mem

@[simp] theorem table_states : table.states = states := rfl

@[simp] theorem table_next : table.next = next := rfl

@[simp] theorem table_next_apply
    (s : State) (r0 r1 r2 : Option Bool) :
    table.next s r0 r1 r2 = next s r0 r1 r2 := rfl

theorem leads_action
    {s target : State}
    (action0 action1 action2 : TapeAction)
    (T0 T1 T2 : Tape Bool)
    (hnext :
      next s (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        step action0 action1 action2 target) :
    table.Leads
      (table.config s T0 T1 T2)
      (table.config target
        (action0.apply T0) (action1.apply T1) (action2.apply T2)) := by
  apply TypedStateTable.leads_step table (state_mem s)
    (st := ⟨target, action0, action1, action2⟩)
  · rw [table_next_apply]
    exact hnext
  · rfl
  · rfl
  · rfl

def cursorTape
    (leftRev rightBits : List Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (leftRev.map some) [none])
    (List.append (rightBits.map some) padding)

@[simp] theorem keepS_apply_self (T : Tape Bool) :
    keepS.apply T = T := rfl

@[simp] theorem keepR_apply_cursorTape
    (leftRev rest : List Bool) (bit : Bool)
    (padding : List (Option Bool)) :
    keepR.apply (cursorTape leftRev (bit :: rest) padding) =
      cursorTape (bit :: leftRev) rest padding := by
  unfold cursorTape
  change
    keepR.apply
        (tapeAtCells (List.append (leftRev.map some) [none])
          (some bit :: List.append (rest.map some) padding)) = _
  rw [keepR_apply_tapeAtCells]
  rfl

@[simp] theorem keepL_apply_cursorTape
    (leftRev rest : List Bool) (previous head : Bool)
    (padding : List (Option Bool)) :
    keepL.apply
        (cursorTape (previous :: leftRev) (head :: rest) padding) =
      cursorTape leftRev (previous :: head :: rest) padding := by
  unfold cursorTape
  change
    keepL.apply
        (tapeAtCells
          (some previous :: List.append (leftRev.map some) [none])
          (some head :: List.append (rest.map some) padding)) = _
  rw [keepL_apply_tapeAtCells]
  rfl

def sentinelTape
    (rightBits : List Bool) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells []
    (none :: List.append (rightBits.map some) padding)

@[simp] theorem keepL_apply_cursorTape_nil
    (head : Bool) (rest : List Bool)
    (padding : List (Option Bool)) :
    keepL.apply (cursorTape [] (head :: rest) padding) =
      sentinelTape (head :: rest) padding := by
  unfold cursorTape sentinelTape
  change
    keepL.apply
        (tapeAtCells [none]
          (some head :: List.append (rest.map some) padding)) = _
  rw [keepL_apply_tapeAtCells]
  rfl

@[simp] theorem keepR_apply_sentinelTape
    (head : Bool) (rest : List Bool)
    (padding : List (Option Bool)) :
    keepR.apply (sentinelTape (head :: rest) padding) =
      cursorTape [] (head :: rest) padding := by
  unfold sentinelTape cursorTape
  rw [keepR_apply_tapeAtCells]
  rfl

theorem leads_lengthTick
    (leftRev rest : List Bool) (padding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .length0 T0 T1
        (cursorTape leftRev
          (false :: false :: true :: false :: rest) padding))
      (table.config .length0 T0 T1
        (cursorTape
          (false :: true :: false :: false :: leftRev) rest padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape leftRev
            (false :: false :: true :: false :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (false :: leftRev)
            (false :: true :: false :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (false :: false :: leftRev)
            (true :: false :: rest) padding) rfl)
  simpa only [keepS_apply_self, keepR_apply_cursorTape] using
    leads_action (s := .lengthKind) (target := .length0)
      keepS keepS keepR T0 T1
      (cursorTape (true :: false :: false :: leftRev)
        (false :: rest) padding) rfl

theorem leads_lengthDone
    (leftRev rest : List Bool) (padding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .length0 T0 T1
        (cursorTape leftRev
          (false :: false :: true :: true :: rest) padding))
      (table.config .cell0 T0 T1
        (cursorTape
          (true :: true :: false :: false :: leftRev) rest padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape leftRev
            (false :: false :: true :: true :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (false :: leftRev)
            (false :: true :: true :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (false :: false :: leftRev)
            (true :: true :: rest) padding) rfl)
  simpa only [keepS_apply_self, keepR_apply_cursorTape] using
    leads_action (s := .lengthKind) (target := .cell0)
      keepS keepS keepR T0 T1
      (cursorTape (true :: false :: false :: leftRev)
        (true :: rest) padding) rfl

theorem leads_lengthField
    (count : Nat) (leftRev rest : List Bool)
    (padding : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .length0 T0 T1
        (cursorTape leftRev
          (List.append (stageNatBits count) rest) padding))
      (table.config .cell0 T0 T1
        (cursorTape
          (List.append (stageNatBits count).reverse leftRev)
          rest padding)) := by
  induction count generalizing leftRev with
  | zero =>
      simpa [stageNatBits, encodeNat, tickBits, doneBits,
        encodeCodeWordAsInput, encodeCodeSymbolAsInput] using
        leads_lengthDone leftRev rest padding T0 T1
  | succ count ih =>
      rw [stageNatBits_succ]
      apply TypedStateTable.Leads.trans
        (leads_lengthTick leftRev
          (List.append (stageNatBits count) rest) padding T0 T1)
      simpa [stageNatBits_succ, List.reverse_append,
        List.append_assoc] using
        ih (false :: true :: false :: false :: leftRev)

theorem leads_cellFalse
    (leftRev rest : List Bool) (padding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .cell0 T0 T1
        (cursorTape leftRev
          (false :: true :: false :: true :: rest) padding))
      (table.config .cell0 T0 T1
        (cursorTape
          (true :: false :: true :: false :: leftRev) rest padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape leftRev
            (false :: true :: false :: true :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (false :: leftRev)
            (true :: false :: true :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (true :: false :: leftRev)
            (false :: true :: rest) padding) rfl)
  simpa only [keepS_apply_self, keepR_apply_cursorTape] using
    leads_action (s := .cell3) (target := .cell0)
      keepS keepS keepR T0 T1
      (cursorTape (false :: true :: false :: leftRev)
        (true :: rest) padding) rfl

theorem leads_cellTrue
    (leftRev rest : List Bool) (padding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .cell0 T0 T1
        (cursorTape leftRev
          (false :: true :: true :: false :: rest) padding))
      (table.config .cell0 T0 T1
        (cursorTape
          (false :: true :: true :: false :: leftRev) rest padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape leftRev
            (false :: true :: true :: false :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (false :: leftRev)
            (true :: true :: false :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (true :: false :: leftRev)
            (true :: false :: rest) padding) rfl)
  simpa only [keepS_apply_self, keepR_apply_cursorTape] using
    leads_action (s := .cell3) (target := .cell0)
      keepS keepS keepR T0 T1
      (cursorTape (true :: true :: false :: leftRev)
        (false :: rest) padding) rfl

theorem leads_cell
    (bit : Bool) (leftRev rest : List Bool)
    (padding : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .cell0 T0 T1
        (cursorTape leftRev
          (List.append (cellBits bit) rest) padding))
      (table.config .cell0 T0 T1
        (cursorTape
          (List.append (cellBits bit).reverse leftRev) rest padding)) := by
  cases bit
  · simpa [cellBits, encodeCodeSymbolAsInput] using
      leads_cellFalse leftRev rest padding T0 T1
  · simpa [cellBits, encodeCodeSymbolAsInput] using
      leads_cellTrue leftRev rest padding T0 T1

theorem leads_cells
    (word : Word Bool) (leftRev rest : List Bool)
    (padding : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .cell0 T0 T1
        (cursorTape leftRev
          (List.append (cellsBits word) rest) padding))
      (table.config .cell0 T0 T1
        (cursorTape
          (List.append (cellsBits word).reverse leftRev) rest padding)) := by
  induction word generalizing leftRev with
  | nil => exact TypedStateTable.Leads.refl table _
  | cons bit word ih =>
      rw [cellsBits_cons]
      apply TypedStateTable.Leads.trans
        (by
          simpa [List.append_assoc] using
            leads_cell bit leftRev
              (List.append (cellsBits word) rest) padding T0 T1)
      simpa [List.reverse_append, List.append_assoc] using
        ih (List.append (cellBits bit).reverse leftRev)

theorem leads_cellBoundary
    (leftRev rest : List Bool) (padding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .cell0 T0 T1
        (cursorTape leftRev (false :: false :: rest) padding))
      (table.config .limit2 T0 T1
        (cursorTape (false :: false :: leftRev) rest padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape leftRev (false :: false :: rest) padding) rfl)
  simpa only [keepS_apply_self, keepR_apply_cursorTape] using
    leads_action (s := .cellKind) (target := .limit2)
      keepS keepS keepR T0 T1
      (cursorTape (false :: leftRev) (false :: rest) padding) rfl

theorem leads_limitPositive
    (leftRev rest : List Bool) (padding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .limit2 T0 T1
        (cursorTape leftRev (true :: false :: rest) padding))
      (table.config (.rewind .positive) T0 T1
        (cursorTape (true :: leftRev) (false :: rest) padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape leftRev (true :: false :: rest) padding) rfl)
  simpa only [keepS_apply_self] using
    leads_action (s := .limitKind) (target := .rewind .positive)
      keepS keepS keepS T0 T1
      (cursorTape (true :: leftRev) (false :: rest) padding) rfl

theorem leads_limitZero
    (leftRev rest : List Bool) (padding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .limit2 T0 T1
        (cursorTape leftRev (true :: true :: rest) padding))
      (table.config .candidate0 T0 T1
        (cursorTape (true :: true :: leftRev) rest padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape leftRev (true :: true :: rest) padding) rfl)
  simpa only [keepS_apply_self, keepR_apply_cursorTape] using
    leads_action (s := .limitKind) (target := .candidate0)
      keepS keepS keepR T0 T1
      (cursorTape (true :: leftRev) (true :: rest) padding) rfl

theorem leads_candidatePositive
    (leftRev rest : List Bool) (padding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .candidate0 T0 T1
        (cursorTape leftRev
          (false :: false :: true :: false :: rest) padding))
      (table.config (.rewind .candidate) T0 T1
        (cursorTape (true :: false :: false :: leftRev)
          (false :: rest) padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape leftRev
            (false :: false :: true :: false :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (false :: leftRev)
            (false :: true :: false :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (false :: false :: leftRev)
            (true :: false :: rest) padding) rfl)
  simpa only [keepS_apply_self] using
    leads_action (s := .candidateKind)
      (target := .rewind .candidate)
      keepS keepS keepS T0 T1
      (cursorTape (true :: false :: false :: leftRev)
        (false :: rest) padding) rfl

theorem leads_candidateZero
    (leftRev rest : List Bool) (padding : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .candidate0 T0 T1
        (cursorTape leftRev
          (false :: false :: true :: true :: rest) padding))
      (table.config .source0 T0 (keepR.apply T1)
        (cursorTape (true :: false :: false :: leftRev)
          (true :: rest) padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape leftRev
            (false :: false :: true :: true :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (false :: leftRev)
            (false :: true :: true :: rest) padding) rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_cursorTape] using
        leads_action keepS keepS keepR T0 T1
          (cursorTape (false :: false :: leftRev)
            (true :: true :: rest) padding) rfl)
  simpa only [keepS_apply_self] using
    leads_action (s := .candidateKind) (target := .source0)
      keepS keepR keepS T0 T1
      (cursorTape (true :: false :: false :: leftRev)
        (true :: rest) padding) rfl

def sourceBranch : Bool -> Branch
  | false => .source
  | true => .checker

theorem leads_sourceProbe
    (kind : Bool) (left right : List (Option Bool))
    (T0 T2 : Tape Bool) :
    table.Leads
      (table.config .source0 T0
        (tapeAtCells (none :: left)
          (some false :: some false :: some true :: some kind :: right))
        T2)
      (table.config (.rewind (sourceBranch kind)) T0
        (tapeAtCells left
          (none :: some false :: some false :: some true :: some kind :: right))
        T2) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_tapeAtCells] using
        leads_action (s := .source0) (target := .source1)
          keepS keepR keepS T0
          (tapeAtCells (none :: left)
            (some false :: some false :: some true :: some kind :: right))
          T2 rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_tapeAtCells] using
        leads_action (s := .source1) (target := .source2)
          keepS keepR keepS T0
          (tapeAtCells (some false :: none :: left)
            (some false :: some true :: some kind :: right)) T2 rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepR_apply_tapeAtCells] using
        leads_action (s := .source2) (target := .sourceKind)
          keepS keepR keepS T0
          (tapeAtCells (some false :: some false :: none :: left)
            (some true :: some kind :: right)) T2 rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepL_apply_tapeAtCells] using
        leads_action (s := .sourceKind)
          (target := .sourceBack2 (sourceBranch kind))
          keepS keepL keepS T0
          (tapeAtCells
            (some true :: some false :: some false :: none :: left)
            (some kind :: right)) T2 (by cases kind <;> rfl))
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepL_apply_tapeAtCells] using
        leads_action (s := .sourceBack2 (sourceBranch kind))
          (target := .sourceBack1 (sourceBranch kind))
          keepS keepL keepS T0
          (tapeAtCells
            (some false :: some false :: none :: left)
            (some true :: some kind :: right)) T2 rfl)
  apply TypedStateTable.Leads.trans
    (by
      simpa only [keepS_apply_self, keepL_apply_tapeAtCells] using
        leads_action (s := .sourceBack1 (sourceBranch kind))
          (target := .sourceBack0 (sourceBranch kind))
          keepS keepL keepS T0
          (tapeAtCells (some false :: none :: left)
            (some false :: some true :: some kind :: right)) T2 rfl)
  simpa only [keepS_apply_self, keepL_apply_tapeAtCells] using
    leads_action (s := .sourceBack0 (sourceBranch kind))
      (target := .rewind (sourceBranch kind))
      keepS keepL keepS T0
      (tapeAtCells (none :: left)
        (some false :: some false :: some true :: some kind :: right))
      T2 rfl

theorem leads_rewind
    (branch : Branch) (leftRev rest : List Bool) (head : Bool)
    (padding : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config (.rewind branch) T0 T1
        (cursorTape leftRev (head :: rest) padding))
      (table.config (branchStart branch) T0 T1
        (cursorTape []
          (List.append leftRev.reverse (head :: rest)) padding)) := by
  induction leftRev generalizing head rest with
  | nil =>
      apply TypedStateTable.Leads.trans
        (by
          simpa only [keepS_apply_self, keepL_apply_cursorTape_nil] using
            leads_action (s := .rewind branch)
              (target := .rewind branch)
              keepS keepS keepL T0 T1
              (cursorTape [] (head :: rest) padding) rfl)
      change
        table.Leads
          (table.config (.rewind branch) T0 T1
            (sentinelTape (head :: rest) padding))
          (table.config (branchStart branch) T0 T1
            (cursorTape [] (head :: rest) padding))
      simpa only [keepS_apply_self, keepR_apply_sentinelTape] using
        leads_action (s := .rewind branch)
          (target := branchStart branch)
          keepS keepS keepR T0 T1
          (sentinelTape (head :: rest) padding) rfl
  | cons previous leftRev ih =>
      apply TypedStateTable.Leads.trans
        (by
          simpa only [keepS_apply_self, keepL_apply_cursorTape] using
            leads_action (s := .rewind branch)
              (target := .rewind branch)
              keepS keepS keepL T0 T1
              (cursorTape (previous :: leftRev) (head :: rest) padding) rfl)
      simpa [List.reverse_cons, List.append_assoc] using
        ih (head :: rest) previous

def prefixLeftRev (w : Word Bool) : List Bool :=
  List.append (cellsBits w).reverse (stageNatBits w.length).reverse

theorem leads_prefixToLimit
    (w : Word Bool) (rest : List Bool)
    (padding : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .length0 T0 T1
        (cursorTape []
          (List.append (stageNatBits w.length)
            (List.append (cellsBits w) (false :: false :: rest)))
          padding))
      (table.config .limit2 T0 T1
        (cursorTape (false :: false :: prefixLeftRev w)
          rest padding)) := by
  apply TypedStateTable.Leads.trans
    (leads_lengthField w.length []
      (List.append (cellsBits w) (false :: false :: rest))
      padding T0 T1)
  apply TypedStateTable.Leads.trans
    (by
      simpa [List.append_assoc] using
        leads_cells w (stageNatBits w.length).reverse
          (false :: false :: rest) padding T0 T1)
  simpa [prefixLeftRev] using
    leads_cellBoundary
      (List.append (cellsBits w).reverse (stageNatBits w.length).reverse)
      rest padding T0 T1

theorem leads_dispatchPositive
    (w : Word Bool) (limit candidateFuel : Nat)
    (padding : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .length0 T0 T1
        (cursorTape []
          (CandidateInputBits w (limit + 1) candidateFuel) padding))
      (table.config (.positive .seekRight) T0 T1
        (cursorTape []
          (CandidateInputBits w (limit + 1) candidateFuel) padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa [RolloverTape.candidateInputBits_eq_fields,
        RolloverTape.prefixBits,
        stageNatBits_succ, List.append_assoc] using
        leads_prefixToLimit w
          (true :: false :: List.append (stageNatBits limit)
            (stageNatBits candidateFuel)) padding T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_limitPositive
      (false :: false :: prefixLeftRev w)
      (List.append (stageNatBits limit) (stageNatBits candidateFuel))
      padding T0 T1)
  simpa [branchStart, prefixLeftRev,
    RolloverTape.candidateInputBits_eq_fields, RolloverTape.prefixBits,
    stageNatBits_succ, List.reverse_append, List.append_assoc] using
    leads_rewind .positive
      (true :: false :: false :: prefixLeftRev w)
      (List.append (stageNatBits limit) (stageNatBits candidateFuel))
      false padding T0 T1

theorem leads_dispatchCandidate
    (w : Word Bool) (candidateFuel : Nat)
    (padding : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .length0 T0 T1
        (cursorTape []
          (CandidateInputBits w 0 (candidateFuel + 1)) padding))
      (table.config (.candidate .seekRight) T0 T1
        (cursorTape []
          (CandidateInputBits w 0 (candidateFuel + 1)) padding)) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa [RolloverTape.candidateInputBits_eq_fields,
        RolloverTape.prefixBits,
        stageNatBits_succ, List.append_assoc] using
        leads_prefixToLimit w
          (true :: true :: List.append
            (stageNatBits (candidateFuel + 1)) [])
          padding T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_limitZero
      (false :: false :: prefixLeftRev w)
      (stageNatBits (candidateFuel + 1)) padding T0 T1)
  apply TypedStateTable.Leads.trans
    (by
      simpa [stageNatBits_succ, List.append_assoc] using
        leads_candidatePositive
          (true :: true :: false :: false :: prefixLeftRev w)
          (stageNatBits candidateFuel) padding T0 T1)
  simpa [branchStart, prefixLeftRev,
    RolloverTape.candidateInputBits_eq_fields, RolloverTape.prefixBits,
    stageNatBits_succ, List.reverse_append, List.append_assoc] using
    leads_rewind .candidate
      (true :: false :: false :: true :: true :: false :: false ::
        prefixLeftRev w)
      (stageNatBits candidateFuel) false padding T0 T1

theorem leads_dispatchSource
    (checkerRaw w : Word Bool) (sourceFuel checkerFuel : Nat)
    (padding : List (Option Bool)) :
    table.Leads
      (table.config .length0
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) (sourceFuel + 1))
        (cursorTape [] (CandidateInputBits w 0 0) padding))
      (table.config (.source .seekRight)
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) (sourceFuel + 1))
        (cursorTape [] (CandidateInputBits w 0 0) padding)) := by
  let T0 := PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel
  let T1 := PersistentRestaging.cleanedFuelTape
    (CandidateInputBits w 0 0) (sourceFuel + 1)
  change
    table.Leads
      (table.config .length0 T0 T1
        (cursorTape [] (CandidateInputBits w 0 0) padding))
      (table.config (.source .seekRight) T0 T1
        (cursorTape [] (CandidateInputBits w 0 0) padding))
  apply TypedStateTable.Leads.trans
    (by
      simpa [RolloverTape.candidateInputBits_eq_fields,
        RolloverTape.prefixBits,
        List.append_assoc] using
        leads_prefixToLimit w
          (true :: true :: List.append (stageNatBits 0) [])
          padding T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_limitZero
      (false :: false :: prefixLeftRev w)
      (stageNatBits 0) padding T0 T1)
  apply TypedStateTable.Leads.trans
    (by
      simpa [stageNatBits, encodeNat, doneBits,
        encodeCodeWordAsInput, encodeCodeSymbolAsInput] using
        leads_candidateZero
          (true :: true :: false :: false :: prefixLeftRev w)
          [] padding T0 T1)
  apply TypedStateTable.Leads.trans
    (by
      let left : List (Option Bool) :=
        List.replicate ((CandidateInputBits w 0 0).length + 1) none
      let right : List (Option Bool) :=
        List.append ((stageNatBits sourceFuel).map some) [none]
      have hT1 :
          T1 = tapeAtCells left
            (none :: some false :: some false :: some true ::
              some false :: right) := by
        simp [T1, left, right, PersistentRestaging.cleanedFuelTape,
          stageNatBits_succ]
      have hmove :
          keepR.apply T1 =
            tapeAtCells (none :: left)
              (some false :: some false :: some true ::
                some false :: right) := by
        rw [hT1, keepR_apply_tapeAtCells]
      have hprobe :=
        leads_sourceProbe false left right T0
          (cursorTape
            (true :: false :: false :: true :: true :: false :: false ::
              prefixLeftRev w)
            [true] padding)
      rw [← hmove, ← hT1] at hprobe
      simpa only [sourceBranch, keepR, TapeAction.preserveMove] using hprobe)
  simpa [branchStart, prefixLeftRev,
    RolloverTape.candidateInputBits_eq_fields, RolloverTape.prefixBits,
    List.reverse_append, List.append_assoc] using
    leads_rewind .source
      (true :: false :: false :: true :: true :: false :: false ::
        prefixLeftRev w)
      [] true padding T0 T1

theorem leads_dispatchChecker
    (checkerRaw w : Word Bool) (checkerFuel : Nat)
    (padding : List (Option Bool)) :
    table.Leads
      (table.config .length0
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) 0)
        (cursorTape [] (CandidateInputBits w 0 0) padding))
      (table.config (.checker .seekRight)
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) 0)
        (cursorTape [] (CandidateInputBits w 0 0) padding)) := by
  let T0 := PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel
  let T1 := PersistentRestaging.cleanedFuelTape
    (CandidateInputBits w 0 0) 0
  change
    table.Leads
      (table.config .length0 T0 T1
        (cursorTape [] (CandidateInputBits w 0 0) padding))
      (table.config (.checker .seekRight) T0 T1
        (cursorTape [] (CandidateInputBits w 0 0) padding))
  apply TypedStateTable.Leads.trans
    (by
      simpa [RolloverTape.candidateInputBits_eq_fields,
        RolloverTape.prefixBits,
        List.append_assoc] using
        leads_prefixToLimit w
          (true :: true :: List.append (stageNatBits 0) [])
          padding T0 T1)
  apply TypedStateTable.Leads.trans
    (leads_limitZero
      (false :: false :: prefixLeftRev w)
      (stageNatBits 0) padding T0 T1)
  apply TypedStateTable.Leads.trans
    (by
      simpa [stageNatBits, encodeNat, doneBits,
        encodeCodeWordAsInput, encodeCodeSymbolAsInput] using
        leads_candidateZero
          (true :: true :: false :: false :: prefixLeftRev w)
          [] padding T0 T1)
  apply TypedStateTable.Leads.trans
    (by
      let left : List (Option Bool) :=
        List.replicate ((CandidateInputBits w 0 0).length + 1) none
      let right : List (Option Bool) := [none]
      have hT1 :
          T1 = tapeAtCells left
            (none :: some false :: some false :: some true ::
              some true :: right) := by
        simp [T1, left, right, PersistentRestaging.cleanedFuelTape,
          stageNatBits, encodeNat,
          encodeCodeWordAsInput, encodeCodeSymbolAsInput]
      have hmove :
          keepR.apply T1 =
            tapeAtCells (none :: left)
              (some false :: some false :: some true ::
                some true :: right) := by
        rw [hT1, keepR_apply_tapeAtCells]
      have hprobe :=
        leads_sourceProbe true left right T0
          (cursorTape
            (true :: false :: false :: true :: true :: false :: false ::
              prefixLeftRev w)
            [true] padding)
      rw [← hmove, ← hT1] at hprobe
      simpa only [sourceBranch, keepR, TapeAction.preserveMove] using hprobe)
  simpa [branchStart, prefixLeftRev,
    RolloverTape.candidateInputBits_eq_fields, RolloverTape.prefixBits,
    List.reverse_append, List.append_assoc] using
    leads_rewind .checker
      (true :: false :: false :: true :: true :: false :: false ::
        prefixLeftRev w)
      [] true padding T0 T1

namespace TypedEmbedding

structure Runtime (sigma : Type) where
  state : sigma
  tape0 : Tape Bool
  tape1 : Tape Bool
  tape2 : Tape Bool

def Runtime.toConfig {sigma : Type}
    (M : TypedStateTable sigma) (c : Runtime sigma) :
    CommonGround.FiniteTransducers.Structured.Configuration :=
  M.config c.state c.tape0 c.tape1 c.tape2

def run {sigma : Type} (M : TypedStateTable sigma) :
    Nat -> Runtime sigma -> Runtime sigma
  | 0, c => c
  | n + 1, c =>
      match M.next c.state
          (Tape.read c.tape0) (Tape.read c.tape1) (Tape.read c.tape2) with
      | none => c
      | some st =>
          run M n
            { state := st.target
              tape0 := st.action0.apply c.tape0
              tape1 := st.action1.apply c.tape1
              tape2 := st.action2.apply c.tape2 }

theorem run_state_mem {sigma : Type}
    (M : TypedStateTable sigma) (n : Nat) (c : Runtime sigma)
    (hc : c.state ∈ M.states) :
    (run M n c).state ∈ M.states := by
  induction n generalizing c with
  | zero => exact hc
  | succ n ih =>
      simp only [run]
      cases hnext : M.next c.state
          (Tape.read c.tape0) (Tape.read c.tape1) (Tape.read c.tape2) with
      | none => exact hc
      | some st =>
          apply ih
          exact M.next_target_mem c.state hc _ _ _ st hnext

theorem runConfig_eq_runtime {sigma : Type} [DecidableEq sigma]
    (M : TypedStateTable sigma) (n : Nat) (c : Runtime sigma)
    (hc : c.state ∈ M.states) :
    M.description.runConfig n (c.toConfig M) =
      (run M n c).toConfig M := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      cases hnext : M.next c.state
          (Tape.read c.tape0) (Tape.read c.tape1) (Tape.read c.tape2) with
      | none =>
          have hstep := M.stepConfig_config_none hc hnext
          change
            M.description.stepConfig
              (M.config c.state c.tape0 c.tape1 c.tape2) = none at hstep
          simp only [run, hnext]
          change
            (match
                M.description.stepConfig
                  (M.config c.state c.tape0 c.tape1 c.tape2) with
              | none => M.config c.state c.tape0 c.tape1 c.tape2
              | some next => M.description.runConfig n next) =
              M.config c.state c.tape0 c.tape1 c.tape2
          rw [hstep]
      | some st =>
          change
            M.description.runConfig (n + 1)
                (M.config c.state c.tape0 c.tape1 c.tape2) = _
          have hsucc := M.runConfig_succ_config hc hnext n
          change
            M.description.runConfig (n + 1)
                (M.config c.state c.tape0 c.tape1 c.tape2) =
              M.description.runConfig n
                (M.config st.target
                  (st.action0.apply c.tape0)
                  (st.action1.apply c.tape1)
                  (st.action2.apply c.tape2)) at hsucc
          rw [hsucc]
          simpa [run, hnext, Runtime.toConfig] using
            ih
              { state := st.target
                tape0 := st.action0.apply c.tape0
                tape1 := st.action1.apply c.tape1
                tape2 := st.action2.apply c.tape2 }
              (M.next_target_mem c.state hc _ _ _ st hnext)

def Runtime.map {sigma tau : Type}
    (f : sigma -> tau) (c : Runtime sigma) : Runtime tau :=
  { state := f c.state
    tape0 := c.tape0
    tape1 := c.tape1
    tape2 := c.tape2 }

def mapTypedStep {sigma tau : Type}
    (f : sigma -> tau) (st : TypedStep sigma) : TypedStep tau :=
  TypedStep.mk (f st.target) st.action0 st.action1 st.action2

def Embeds {sigma tau : Type}
    (small : TypedStateTable sigma) (big : TypedStateTable tau)
    (f : sigma -> tau) : Prop :=
  forall state r0 r1 r2,
    big.next (f state) r0 r1 r2 =
      (small.next state r0 r1 r2).map (mapTypedStep f)

theorem run_map {sigma tau : Type}
    (small : TypedStateTable sigma) (big : TypedStateTable tau)
    (f : sigma -> tau) (hembeds : Embeds small big f)
    (n : Nat) (c : Runtime sigma) :
    run big n (c.map f) = (run small n c).map f := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      change
        run big (n + 1)
            { state := f c.state
              tape0 := c.tape0
              tape1 := c.tape1
              tape2 := c.tape2 } =
          (run small (n + 1) c).map f
      simp only [run]
      rw [hembeds c.state
        (Tape.read c.tape0) (Tape.read c.tape1) (Tape.read c.tape2)]
      cases hnext : small.next c.state
          (Tape.read c.tape0) (Tape.read c.tape1) (Tape.read c.tape2) with
      | none => rfl
      | some st =>
          simp only [Option.map_some, mapTypedStep]
          exact ih
            { state := st.target
              tape0 := st.action0.apply c.tape0
              tape1 := st.action1.apply c.tape1
              tape2 := st.action2.apply c.tape2 }

theorem runtime_eq_of_toConfig_eq
    {sigma : Type} (M : TypedStateTable sigma)
    (c d : Runtime sigma)
    (hc : c.state ∈ M.states) (hd : d.state ∈ M.states)
    (hconfig : c.toConfig M = d.toConfig M) : c = d := by
  rcases c with ⟨cstate, c0, c1, c2⟩
  rcases d with ⟨dstate, d0, d1, d2⟩
  have hstateId := congrArg
    CommonGround.FiniteTransducers.Structured.Configuration.state hconfig
  change M.stateId cstate = M.stateId dstate at hstateId
  have hstate := M.stateId_inj cstate hc dstate hd hstateId
  subst dstate
  have htapes := congrArg
    CommonGround.FiniteTransducers.Structured.Configuration.tapes hconfig
  change [c0, c1, c2] = [d0, d1, d2] at htapes
  injection htapes with h0 htail
  injection htail with h1 htail2
  injection htail2 with h2 _hnil
  subst d0
  subst d1
  subst d2
  rfl

theorem lift_runConfig
    {sigma tau : Type} [DecidableEq sigma] [DecidableEq tau]
    (small : TypedStateTable sigma) (big : TypedStateTable tau)
    (f : sigma -> tau)
    (hembeds : Embeds small big f)
    (hmem : forall state, state ∈ small.states -> f state ∈ big.states)
    (n : Nat) (source target : sigma)
    (T0 T1 T2 U0 U1 U2 : Tape Bool)
    (hsource : source ∈ small.states)
    (htarget : target ∈ small.states)
    (hrun :
      small.description.runConfig n (small.config source T0 T1 T2) =
        small.config target U0 U1 U2) :
    big.description.runConfig n (big.config (f source) T0 T1 T2) =
      big.config (f target) U0 U1 U2 := by
  let c : Runtime sigma := ⟨source, T0, T1, T2⟩
  let d : Runtime sigma := ⟨target, U0, U1, U2⟩
  have hsmall := runConfig_eq_runtime small n c hsource
  have htypedConfig : (run small n c).toConfig small = d.toConfig small := by
    exact hsmall.symm.trans hrun
  have htyped : run small n c = d :=
    runtime_eq_of_toConfig_eq small _ _
      (run_state_mem small n c hsource) htarget htypedConfig
  have hbig := runConfig_eq_runtime big n (c.map f) (hmem source hsource)
  rw [run_map small big f hembeds n c, htyped] at hbig
  simpa [c, d, Runtime.map, Runtime.toConfig] using hbig

theorem lift_leads
    {sigma tau : Type} [DecidableEq sigma] [DecidableEq tau]
    (small : TypedStateTable sigma) (big : TypedStateTable tau)
    (f : sigma -> tau)
    (hembeds : Embeds small big f)
    (hmem : forall state, state ∈ small.states -> f state ∈ big.states)
    (source target : sigma)
    (T0 T1 T2 U0 U1 U2 : Tape Bool)
    (hsource : source ∈ small.states)
    (htarget : target ∈ small.states)
    (hleads :
      small.Leads
        (small.config source T0 T1 T2)
        (small.config target U0 U1 U2)) :
    big.Leads
      (big.config (f source) T0 T1 T2)
      (big.config (f target) U0 U1 U2) := by
  rcases TypedStateTable.Leads.to_runConfig hleads with ⟨n, hrun⟩
  apply U12PhaseFusion.leads_of_runConfig big
  exact lift_runConfig small big f hembeds hmem n
    source target T0 T1 T2 U0 U1 U2 hsource htarget hrun

end TypedEmbedding

theorem embedsPositive :
    TypedEmbedding.Embeds U12DiagonalAdvance.table table positiveState := by
  intro state r0 r1 r2
  cases state <;> rfl

theorem embedsCandidate :
    TypedEmbedding.Embeds U12CandidateRollover.table table candidateState := by
  intro state r0 r1 r2
  cases state <;> rfl

theorem embedsSource :
    TypedEmbedding.Embeds U12SourceRollover.table table sourceState := by
  intro state r0 r1 r2
  cases state <;> rfl

theorem embedsChecker :
    TypedEmbedding.Embeds U12CheckerRollover.table table checkerState := by
  intro state r0 r1 r2
  cases state <;> rfl

theorem liftPositiveLeads
    (source target : U12DiagonalAdvance.State)
    (T0 T1 T2 U0 U1 U2 : Tape Bool)
    (hleads :
      U12DiagonalAdvance.table.Leads
        (U12DiagonalAdvance.table.config source T0 T1 T2)
        (U12DiagonalAdvance.table.config target U0 U1 U2)) :
    table.Leads
      (table.config (positiveState source) T0 T1 T2)
      (table.config (positiveState target) U0 U1 U2) := by
  apply TypedEmbedding.lift_leads
    U12DiagonalAdvance.table table positiveState embedsPositive
    (fun state _hstate => state_mem (positiveState state))
    source target T0 T1 T2 U0 U1 U2
  · cases source <;> simp [U12DiagonalAdvance.states]
  · cases target <;> simp [U12DiagonalAdvance.states]
  · exact hleads

theorem liftCandidateLeads
    (source target : U12CandidateRollover.State)
    (T0 T1 T2 U0 U1 U2 : Tape Bool)
    (hleads :
      U12CandidateRollover.table.Leads
        (U12CandidateRollover.table.config source T0 T1 T2)
        (U12CandidateRollover.table.config target U0 U1 U2)) :
    table.Leads
      (table.config (candidateState source) T0 T1 T2)
      (table.config (candidateState target) U0 U1 U2) := by
  apply TypedEmbedding.lift_leads
    U12CandidateRollover.table table candidateState embedsCandidate
    (fun state _hstate => state_mem (candidateState state))
    source target T0 T1 T2 U0 U1 U2
  · cases source <;> simp [U12CandidateRollover.states]
  · cases target <;> simp [U12CandidateRollover.states]
  · exact hleads

theorem liftSourceLeads
    (source target : U12SourceRollover.State)
    (T0 T1 T2 U0 U1 U2 : Tape Bool)
    (hleads :
      U12SourceRollover.table.Leads
        (U12SourceRollover.table.config source T0 T1 T2)
        (U12SourceRollover.table.config target U0 U1 U2)) :
    table.Leads
      (table.config (sourceState source) T0 T1 T2)
      (table.config (sourceState target) U0 U1 U2) := by
  apply TypedEmbedding.lift_leads
    U12SourceRollover.table table sourceState embedsSource
    (fun state _hstate => state_mem (sourceState state))
    source target T0 T1 T2 U0 U1 U2
  · cases source <;> simp [U12SourceRollover.states]
  · cases target <;> simp [U12SourceRollover.states]
  · exact hleads

theorem liftCheckerLeads
    (source target : U12CheckerRollover.State)
    (T0 T1 T2 U0 U1 U2 : Tape Bool)
    (hleads :
      U12CheckerRollover.table.Leads
        (U12CheckerRollover.table.config source T0 T1 T2)
        (U12CheckerRollover.table.config target U0 U1 U2)) :
    table.Leads
      (table.config (checkerState source) T0 T1 T2)
      (table.config (checkerState target) U0 U1 U2) := by
  apply TypedEmbedding.lift_leads
    U12CheckerRollover.table table checkerState embedsChecker
    (fun state _hstate => state_mem (checkerState state))
    source target T0 T1 T2 U0 U1 U2
  · change source ∈ U12CheckerRollover.states
    cases source <;> simp [U12CheckerRollover.states]
  · change target ∈ U12CheckerRollover.states
    cases target <;> simp [U12CheckerRollover.states]
  · exact hleads

theorem cursorTape_singleton_eq_restagedRawTape (raw : Word Bool) :
    cursorTape [] raw [none] = PersistentRestaging.restagedRawTape raw := by
  rfl

theorem leads_positiveStep
    (checkerRaw w : Word Bool)
    (limit candidateFuel sourceFuel checkerFuel : Nat) :
    table.Leads
      (table.config .length0
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w (limit + 1) candidateFuel) sourceFuel)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w (limit + 1) candidateFuel)))
      (table.config .halt
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w (limit + 1) candidateFuel) sourceFuel)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w limit (candidateFuel + 1)))) := by
  let T0 := PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel
  let T1 := PersistentRestaging.cleanedFuelTape
    (CandidateInputBits w (limit + 1) candidateFuel) sourceFuel
  apply TypedStateTable.Leads.trans
    (by
      simpa [T0, T1, cursorTape_singleton_eq_restagedRawTape] using
        leads_dispatchPositive w limit candidateFuel [none] T0 T1)
  simpa [positiveState, T0, T1] using
    liftPositiveLeads .seekRight .halt T0 T1
      (PersistentRestaging.restagedRawTape
        (CandidateInputBits w (limit + 1) candidateFuel))
      T0 T1
      (PersistentRestaging.restagedRawTape
        (CandidateInputBits w limit (candidateFuel + 1)))
      (U12DiagonalAdvance.leads_positiveCandidate
        w limit candidateFuel T0 T1)

theorem leads_candidateStep
    (checkerRaw w : Word Bool)
    (candidateFuel sourceFuel checkerFuel : Nat) :
    table.Leads
      (table.config .length0
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 (candidateFuel + 1)) sourceFuel)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w 0 (candidateFuel + 1))))
      (table.config .halt
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w candidateFuel 0) (sourceFuel + 1))
        (U12CandidateRollover.paddedRawTape
          (CandidateInputBits w candidateFuel 0))) := by
  let T0 := PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel
  let T1 := PersistentRestaging.cleanedFuelTape
    (CandidateInputBits w 0 (candidateFuel + 1)) sourceFuel
  apply TypedStateTable.Leads.trans
    (by
      simpa [T0, T1, cursorTape_singleton_eq_restagedRawTape] using
        leads_dispatchCandidate w candidateFuel [none] T0 T1)
  simpa [candidateState, T0, T1] using
    liftCandidateLeads .seekRight .halt T0 T1
      (PersistentRestaging.restagedRawTape
        (CandidateInputBits w 0 (candidateFuel + 1)))
      T0
      (PersistentRestaging.cleanedFuelTape
        (CandidateInputBits w candidateFuel 0) (sourceFuel + 1))
      (U12CandidateRollover.paddedRawTape
        (CandidateInputBits w candidateFuel 0))
      (U12CandidateRollover.leads_candidateRollover
        w candidateFuel sourceFuel T0)

theorem leads_sourceStep
    (checkerRaw w : Word Bool) (sourceFuel checkerFuel : Nat) :
    table.Leads
      (table.config .length0
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) (sourceFuel + 1))
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w 0 0)))
      (table.config .halt
        (U12SourceRollover.sourceRolloverCheckerTape checkerRaw checkerFuel)
        (U12SourceRollover.sourceRolloverZeroTape w sourceFuel)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w sourceFuel 0))) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa [cursorTape_singleton_eq_restagedRawTape] using
        leads_dispatchSource checkerRaw w sourceFuel checkerFuel [none])
  simpa [sourceState] using
    liftSourceLeads .seekRight .halt
      (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
      (PersistentRestaging.cleanedFuelTape
        (CandidateInputBits w 0 0) (sourceFuel + 1))
      (PersistentRestaging.restagedRawTape (CandidateInputBits w 0 0))
      (U12SourceRollover.sourceRolloverCheckerTape checkerRaw checkerFuel)
      (U12SourceRollover.sourceRolloverZeroTape w sourceFuel)
      (PersistentRestaging.restagedRawTape
        (CandidateInputBits w sourceFuel 0))
      (U12SourceRollover.leads_sourceRollover
        checkerRaw w sourceFuel checkerFuel)

theorem leads_checkerStep
    (checkerRaw w : Word Bool) (checkerFuel : Nat) :
    table.Leads
      (table.config .length0
        (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) 0)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w 0 0)))
      (table.config .halt
        (U12CheckerRollover.checkerRolloverCheckerTape
          checkerRaw checkerFuel)
        (PersistentRestaging.cleanedFuelTape
          (CandidateInputBits w 0 0) 0)
        (PersistentRestaging.restagedRawTape
          (CandidateInputBits w (checkerFuel + 1) 0))) := by
  apply TypedStateTable.Leads.trans
    (by
      simpa [cursorTape_singleton_eq_restagedRawTape] using
        leads_dispatchChecker checkerRaw w checkerFuel [none])
  simpa [checkerState] using
    liftCheckerLeads .seekRight .halt
      (PersistentRestaging.cleanedFuelTape checkerRaw checkerFuel)
      (PersistentRestaging.cleanedFuelTape (CandidateInputBits w 0 0) 0)
      (PersistentRestaging.restagedRawTape (CandidateInputBits w 0 0))
      (U12CheckerRollover.checkerRolloverCheckerTape
        checkerRaw checkerFuel)
      (PersistentRestaging.cleanedFuelTape (CandidateInputBits w 0 0) 0)
      (PersistentRestaging.restagedRawTape
        (CandidateInputBits w (checkerFuel + 1) 0))
      (U12CheckerRollover.leads_checkerRollover
        checkerRaw w checkerFuel)

end U12DispatchBootstrap
end BoundedFuelPairSearch
end Computability
end FoC
