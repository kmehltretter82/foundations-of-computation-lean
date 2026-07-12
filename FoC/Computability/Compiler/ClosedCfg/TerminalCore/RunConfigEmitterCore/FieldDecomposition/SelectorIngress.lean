import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.ClassifiedBoundary

set_option doc.verso true

/-!
# Fixed-start classified selector ingress

The D-specific decomposer stores its finite state classification in the
preallocated scratch-marker reservoir.  This module implements the structured
scanner that reads that selector from one fixed start state, restores the
reservoir and saved hit exactly, and stops at a proof-relevant class-indexed
control state.  A later combined table splices those control states directly
into the existing loop dispatcher without an intervening halt.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition
namespace SelectorIngress

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open ClassifiedBoundary

/-!
## Finite typed scanner
-/

/-- A simple additive bound for a finite list of natural numbers. -/
def natListBound : List Nat -> Nat
  | [] => 0
  | value :: rest => value + natListBound rest

theorem le_natListBound_of_mem {value : Nat} :
    forall {values : List Nat}, value ∈ values -> value ≤ natListBound values := by
  intro values hmem
  induction values with
  | nil => cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hrest
      · simp [natListBound]
      · have := ih hrest
        simp only [natListBound]
        lia

/-- Bound large enough to enumerate every unary prefix of every known state. -/
def stateValueBound (D : MachineDescription) : Nat :=
  natListBound (fixedStepValues D)

theorem knownState_le_stateValueBound
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    state ≤ stateValueBound D := by
  exact le_natListBound_of_mem hstate

/-- Typed controls of the selector scanner.  The original hit bit is retained
in finite control until its temporarily marked cell is restored. -/
inductive State (D : MachineDescription) where
  | start
  | bool0 (hit : Bool)
  | bool1 (hit : Bool)
  | bool2 (hit : Bool)
  | bool3 (hit branch : Bool)
  | nat0 (hit : Bool) (value : Nat)
  | nat1 (hit : Bool) (value : Nat)
  | nat2 (hit : Bool) (value : Nat)
  | nat3 (hit : Bool) (value : Nat)
  | seekDelimiter (hit : Bool) (tag : StateClass D)
  | returnToHit (hit : Bool) (tag : StateClass D)
  | restoreHit (hit : Bool) (tag : StateClass D)
  | done (tag : StateClass D)
  | halt
deriving DecidableEq

/-- One transition acting only on logical tape 2. -/
private def step2 {D : MachineDescription}
    (action2 : TapeAction) (target : State D) :
    Option (TypedStep (State D)) :=
  some
    { target := target
      action0 := keepS
      action1 := keepS
      action2 := action2 }

/-- Fixed-start selector parser and exact marker-restoration transition. -/
def next (D : MachineDescription) :
    State D -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep (State D))
  | .start, _, _, some hit =>
      step2 (writeL (some false)) (.bool0 hit)
  | .start, _, _, none => none
  | .bool0 hit, _, _, some false =>
      step2 (writeL (some true)) (.bool1 hit)
  | .bool0 _, _, _, _ => none
  | .bool1 hit, _, _, some true =>
      step2 (writeL (some true)) (.bool2 hit)
  | .bool1 _, _, _, _ => none
  | .bool2 hit, _, _, some branch =>
      step2 (writeL (some true)) (.bool3 hit branch)
  | .bool2 _, _, _, none => none
  | .bool3 hit false, _, _, some true =>
      step2 (writeL (some true))
        (.seekDelimiter hit (StateClass.other : StateClass D))
  | .bool3 hit true, _, _, some false =>
      step2 (writeL (some true)) (.nat0 hit 0)
  | .bool3 _ _, _, _, _ => none
  | .nat0 hit value, _, _, some false =>
      if value ≤ stateValueBound D then
        step2 (writeL (some true)) (.nat1 hit value)
      else
        none
  | .nat0 _ _, _, _, _ => none
  | .nat1 hit value, _, _, some false =>
      if value ≤ stateValueBound D then
        step2 (writeL (some true)) (.nat2 hit value)
      else
        none
  | .nat1 _ _, _, _, _ => none
  | .nat2 hit value, _, _, some true =>
      if value ≤ stateValueBound D then
        step2 (writeL (some true)) (.nat3 hit value)
      else
        none
  | .nat2 _ _, _, _, _ => none
  | .nat3 hit value, _, _, some false =>
      if value < stateValueBound D then
        step2 (writeL (some true)) (.nat0 hit (value + 1))
      else
        none
  | .nat3 hit value, _, _, some true =>
      if hstate : value ∈ fixedStepValues D then
        step2 (writeL (some true))
          (.seekDelimiter hit (.known value hstate))
      else
        none
  | .nat3 _ _, _, _, none => none
  | .seekDelimiter hit tag, _, _, some true =>
      step2 keepL (.seekDelimiter hit tag)
  | .seekDelimiter hit tag, _, _, none =>
      step2 keepR (.returnToHit hit tag)
  | .seekDelimiter _ _, _, _, some false => none
  | .returnToHit hit tag, _, _, some true =>
      step2 keepR (.returnToHit hit tag)
  | .returnToHit hit tag, _, _, some false =>
      step2 (writeR (some hit)) (.restoreHit hit tag)
  | .returnToHit _ _, _, _, none => none
  | .restoreHit _ tag, _, _, none =>
      step2 keepL (.done tag)
  | .restoreHit _ _, _, _, some _ => none
  | .done _, _, _, _ => none
  | .halt, _, _, _ => none

/-!
## Finite state enumeration
-/

def boolStates (D : MachineDescription) : List (State D) :=
  [ .bool0 false, .bool0 true
  , .bool1 false, .bool1 true
  , .bool2 false, .bool2 true
  , .bool3 false false, .bool3 false true
  , .bool3 true false, .bool3 true true ]

def natStatesAt (D : MachineDescription) (value : Nat) : List (State D) :=
  [ .nat0 false value, .nat0 true value
  , .nat1 false value, .nat1 true value
  , .nat2 false value, .nat2 true value
  , .nat3 false value, .nat3 true value ]

def natStates (D : MachineDescription) : List (State D) :=
  (List.range (stateValueBound D + 1)).flatMap (natStatesAt D)

def tagStatesAt (D : MachineDescription)
    (tag : StateClass D) : List (State D) :=
  [ .seekDelimiter false tag, .seekDelimiter true tag
  , .returnToHit false tag, .returnToHit true tag
  , .restoreHit false tag, .restoreHit true tag
  , .done tag ]

def tagStates (D : MachineDescription) : List (State D) :=
  (stateClasses D).flatMap (tagStatesAt D)

def states (D : MachineDescription) : List (State D) :=
  .start ::
    List.append (boolStates D)
      (List.append (natStates D)
        (List.append (tagStates D) [.halt]))

theorem start_mem_states (D : MachineDescription) :
    State.start ∈ states D := by
  simp [states]

theorem halt_mem_states (D : MachineDescription) :
    State.halt ∈ states D := by
  simp [states]

theorem bool0_mem_states (D : MachineDescription) (hit : Bool) :
    State.bool0 hit ∈ states D := by
  cases hit <;> simp [states, boolStates]

theorem bool1_mem_states (D : MachineDescription) (hit : Bool) :
    State.bool1 hit ∈ states D := by
  cases hit <;> simp [states, boolStates]

theorem bool2_mem_states (D : MachineDescription) (hit : Bool) :
    State.bool2 hit ∈ states D := by
  cases hit <;> simp [states, boolStates]

theorem bool3_mem_states (D : MachineDescription) (hit branch : Bool) :
    State.bool3 hit branch ∈ states D := by
  cases hit <;> cases branch <;> simp [states, boolStates]

private theorem mem_states_of_natStates
    {D : MachineDescription} {state : State D}
    (hstate : state ∈ natStates D) : state ∈ states D := by
  unfold states
  apply List.mem_cons_of_mem
  apply List.mem_append_right (boolStates D)
  exact List.mem_append_left (List.append (tagStates D) [.halt]) hstate

private theorem mem_states_of_tagStates
    {D : MachineDescription} {state : State D}
    (hstate : state ∈ tagStates D) : state ∈ states D := by
  unfold states
  apply List.mem_cons_of_mem
  apply List.mem_append_right (boolStates D)
  apply List.mem_append_right (natStates D)
  exact List.mem_append_left [.halt] hstate

theorem nat0_mem_states
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hvalue : value ≤ stateValueBound D) :
    State.nat0 hit value ∈ states D := by
  apply mem_states_of_natStates
  unfold natStates
  apply List.mem_flatMap.mpr
  refine ⟨value, List.mem_range.mpr (by lia), ?_⟩
  cases hit <;> simp [natStatesAt]

theorem nat1_mem_states
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hvalue : value ≤ stateValueBound D) :
    State.nat1 hit value ∈ states D := by
  apply mem_states_of_natStates
  unfold natStates
  apply List.mem_flatMap.mpr
  refine ⟨value, List.mem_range.mpr (by lia), ?_⟩
  cases hit <;> simp [natStatesAt]

theorem nat2_mem_states
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hvalue : value ≤ stateValueBound D) :
    State.nat2 hit value ∈ states D := by
  apply mem_states_of_natStates
  unfold natStates
  apply List.mem_flatMap.mpr
  refine ⟨value, List.mem_range.mpr (by lia), ?_⟩
  cases hit <;> simp [natStatesAt]

theorem nat3_mem_states
    (D : MachineDescription) (hit : Bool) (value : Nat)
    (hvalue : value ≤ stateValueBound D) :
    State.nat3 hit value ∈ states D := by
  apply mem_states_of_natStates
  unfold natStates
  apply List.mem_flatMap.mpr
  refine ⟨value, List.mem_range.mpr (by lia), ?_⟩
  cases hit <;> simp [natStatesAt]

theorem seekDelimiter_mem_states
    (D : MachineDescription) (hit : Bool) (tag : StateClass D) :
    State.seekDelimiter hit tag ∈ states D := by
  apply mem_states_of_tagStates
  unfold tagStates
  apply List.mem_flatMap.mpr
  refine ⟨tag, mem_stateClasses D tag, ?_⟩
  cases hit <;> simp [tagStatesAt]

theorem returnToHit_mem_states
    (D : MachineDescription) (hit : Bool) (tag : StateClass D) :
    State.returnToHit hit tag ∈ states D := by
  apply mem_states_of_tagStates
  unfold tagStates
  apply List.mem_flatMap.mpr
  refine ⟨tag, mem_stateClasses D tag, ?_⟩
  cases hit <;> simp [tagStatesAt]

theorem restoreHit_mem_states
    (D : MachineDescription) (hit : Bool) (tag : StateClass D) :
    State.restoreHit hit tag ∈ states D := by
  apply mem_states_of_tagStates
  unfold tagStates
  apply List.mem_flatMap.mpr
  refine ⟨tag, mem_stateClasses D tag, ?_⟩
  cases hit <;> simp [tagStatesAt]

theorem done_mem_states
    (D : MachineDescription) (tag : StateClass D) :
    State.done tag ∈ states D := by
  apply mem_states_of_tagStates
  unfold tagStates
  exact List.mem_flatMap.mpr
    ⟨tag, mem_stateClasses D tag, by simp [tagStatesAt]⟩

theorem next_target_mem (D : MachineDescription) :
    forall s : State D, s ∈ states D ->
      forall (r0 r1 r2 : Option Bool) (step : TypedStep (State D)),
        next D s r0 r1 r2 = some step -> step.target ∈ states D := by
  intro s hs r0 r1 r2 step hnext
  cases s with
  | start =>
      cases r2 with
      | none => simp [next] at hnext
      | some hit => cases hnext; exact bool0_mem_states D hit
  | bool0 hit =>
      cases r2 with
      | none => simp [next] at hnext
      | some bit =>
          cases bit <;> simp [next] at hnext
          cases hnext
          exact bool1_mem_states D hit
  | bool1 hit =>
      cases r2 with
      | none => simp [next] at hnext
      | some bit =>
          cases bit <;> simp [next] at hnext
          cases hnext
          exact bool2_mem_states D hit
  | bool2 hit =>
      cases r2 with
      | none => simp [next] at hnext
      | some branch =>
          cases hnext
          exact bool3_mem_states D hit branch
  | bool3 hit branch =>
      cases branch with
      | false =>
          cases r2 with
          | none => simp [next] at hnext
          | some bit =>
              cases bit with
              | false => simp [next] at hnext
              | true =>
                  cases hnext
                  exact seekDelimiter_mem_states D hit .other
      | true =>
          cases r2 with
          | none => simp [next] at hnext
          | some bit =>
              cases bit with
              | false =>
                  cases hnext
                  exact nat0_mem_states D hit 0 (Nat.zero_le _)
              | true => simp [next] at hnext
  | nat0 hit value =>
      cases r2 with
      | none => simp [next] at hnext
      | some bit =>
          cases bit with
          | false =>
              simp only [next] at hnext
              split at hnext
              · rename_i hvalue
                cases hnext
                exact nat1_mem_states D hit value hvalue
              · cases hnext
          | true => simp [next] at hnext
  | nat1 hit value =>
      cases r2 with
      | none => simp [next] at hnext
      | some bit =>
          cases bit with
          | false =>
              simp only [next] at hnext
              split at hnext
              · rename_i hvalue
                cases hnext
                exact nat2_mem_states D hit value hvalue
              · cases hnext
          | true => simp [next] at hnext
  | nat2 hit value =>
      cases r2 with
      | none => simp [next] at hnext
      | some bit =>
          cases bit with
          | false => simp [next] at hnext
          | true =>
              simp only [next] at hnext
              split at hnext
              · rename_i hvalue
                cases hnext
                exact nat3_mem_states D hit value hvalue
              · cases hnext
  | nat3 hit value =>
      cases r2 with
      | none => simp [next] at hnext
      | some bit =>
          cases bit with
          | false =>
              simp only [next] at hnext
              split at hnext
              · cases hnext
                exact nat0_mem_states D hit (value + 1) (by lia)
              · cases hnext
          | true =>
              simp only [next] at hnext
              split at hnext
              · rename_i hstate
                cases hnext
                exact seekDelimiter_mem_states D hit (.known value hstate)
              · cases hnext
  | seekDelimiter hit tag =>
      cases r2 with
      | none =>
          cases hnext
          exact returnToHit_mem_states D hit tag
      | some bit =>
          cases bit <;> simp [next] at hnext
          cases hnext
          exact seekDelimiter_mem_states D hit tag
  | returnToHit hit tag =>
      cases r2 with
      | none => simp [next] at hnext
      | some bit =>
          cases bit <;> cases hnext
          · exact restoreHit_mem_states D hit tag
          · exact returnToHit_mem_states D hit tag
  | restoreHit hit tag =>
      cases r2 with
      | none => cases hnext; exact done_mem_states D tag
      | some bit => cases bit <;> simp [next] at hnext
  | done tag => simp [next] at hnext
  | halt => simp [next] at hnext

/-- Concrete typed table for the fixed-start selector scanner. -/
def table (D : MachineDescription) : TypedStateTable (State D) :=
  TypedStateTable.ofList
    (states D) .start .halt (next D)
    (start_mem_states D) (halt_mem_states D)
    (by intro r0 r1 r2; rfl)
    (next_target_mem D)

def description (D : MachineDescription) : Description :=
  (table D).description

theorem description_wellFormed (D : MachineDescription) :
    (description D).WellFormed :=
  (table D).description_wellFormed

theorem description_haltTransitionFree (D : MachineDescription) :
    (description D).HaltTransitionFree :=
  (table D).description_haltTransitionFree

theorem description_supportsReadWriteRows3 (D : MachineDescription) :
    SupportsReadWriteRows3 (description D) :=
  (table D).description_supportsReadWriteRows3

/-!
## Exact selector cell shapes

These helpers expose the self-delimiting selector layout used by the combined
selector/dispatcher execution proof.
-/

def natSelectorTail
    (state : Nat) (nextCell : Option Bool)
    (left : List (Option Bool)) : List (Option Bool) :=
  match state with
  | 0 => [some false, some true, some true, nextCell] ++ left
  | state + 1 =>
      [some false, some true, some false, some false] ++
        natSelectorTail state nextCell left

theorem encodeNatCells_eq_natSelectorTail
    (state : Nat) (nextCell : Option Bool)
    (left : List (Option Bool)) :
    (encodeCodeWordAsInput (encodeNat state)).map some ++ nextCell :: left =
      some false :: natSelectorTail state nextCell left := by
  induction state with
  | zero => rfl
  | succ state ih =>
      simp [encodeNat, natSelectorTail, ih]
  done

def restoredNatRight
    (state : Nat) (right : List (Option Bool)) : List (Option Bool) :=
  match state with
  | 0 => [some true, some true, some true, some true] ++ right
  | state + 1 =>
      restoredNatRight state
        ([some true, some true, some true, some true] ++ right)

theorem restoredNatRight_eq
    (state : Nat) (right : List (Option Bool)) :
    restoredNatRight state right =
      List.replicate (4 * (state + 1)) (some true) ++ right := by
  induction state generalizing right with
  | zero => rfl
  | succ state ih =>
      rw [restoredNatRight, ih]
      change
        List.replicate (4 * (state + 1)) (some true) ++
            (List.replicate 4 (some true) ++ right) =
          List.replicate (4 * (state + 1 + 1)) (some true) ++ right
      rw [← FoC.Computability.list_replicate_add_append
        (some true : Option Bool) (4 * (state + 1)) 4 right]
      congr 2
  done

theorem selectorBits_known_cells
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D)
    (nextCell : Option Bool) (left : List (Option Bool)) :
    (selectorBits (StateClass.known state hstate)).map some ++
        nextCell :: left =
      some false :: some true :: some true :: some false :: some false ::
        natSelectorTail state nextCell left := by
  rw [selectorBits_known hstate]
  have hcode :
      encodeBoolAppend true (encodeNatAppend state []) =
        MachineCodeSymbol.one :: encodeNat state := by
    simp [encodeBoolAppend, encodeCellAppend, encodeCell, encodeNatAppend]
  rw [hcode]
  change
    (List.append [false, true, true, false]
      (encodeCodeWordAsInput (encodeNat state))).map some ++
        nextCell :: left = _
  rw [CanonicalLayouts.DovetailLayoutScanner.map_some_append]
  change
    [some false, some true, some true, some false] ++
        ((encodeCodeWordAsInput (encodeNat state)).map some ++
          nextCell :: left) = _
  rw [encodeNatCells_eq_natSelectorTail]
  rfl
  done

theorem selectorBits_other_cells
    (D : MachineDescription) (nextCell : Option Bool)
    (left : List (Option Bool)) :
    (selectorBits (StateClass.other : StateClass D)).map some ++
        nextCell :: left =
      some false :: some true :: some false :: some true ::
        nextCell :: left := by
  rfl

def selectorTailCells
    {D : MachineDescription} (tag : StateClass D)
    (nextCell : Option Bool) (left : List (Option Bool)) :
    List (Option Bool) :=
  match tag with
  | .other => some true :: some false :: some true :: nextCell :: left
  | .known state _ =>
      some true :: some true :: some false :: some false ::
        natSelectorTail state nextCell left

theorem selectorBits_cells_eq
    {D : MachineDescription} (tag : StateClass D)
    (nextCell : Option Bool) (left : List (Option Bool)) :
    (selectorBits tag).map some ++ nextCell :: left =
      some false :: selectorTailCells tag nextCell left := by
  cases tag with
  | other => exact selectorBits_other_cells D nextCell left
  | known state hstate => exact selectorBits_known_cells hstate nextCell left

/-!
The standalone exact-run lattice was retired when the scanner was spliced into
the fixed-start selector/dispatcher table. Its {lit}`done` states are not
halting endpoints: the combined table bridges them directly into classified
dispatcher states, so execution proofs belong to that table.
-/

end SelectorIngress
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
