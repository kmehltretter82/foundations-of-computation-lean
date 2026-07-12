import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorCore.Shape
import FoC.Computability.Compiler.Structured.Lowering.DelayedLeftEmitter
import FoC.Computability.Compiler.Structured.Lowering.TypedStateTable

set_option doc.verso true

/-!
# Fuel-simulator structured-core table

The table copies the stage prefix and fuel to a blank-separated scratch tape,
then emits the exact initial simulator layout backwards through a one-bit hold
buffer. The final held bit is written without moving, so tape 2 becomes an
exact input tape before the required one-cell handoff move.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets
namespace FuelSimulatorCore

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

/-- The bit delayed by the backwards output emitter. -/
abbrev Hold := Option Bool

def emitAction : Hold -> TapeAction
  := delayedLeftEmitAction

def flushAction : Hold -> TapeAction
  := delayedLeftFlushAction

inductive State where
  | len0 | len1 | len2 | len3
  | cells0 | cells1 | cells2 | cells3 (third : Bool)
  | limit0 | limit1 | limit2 | limit3
  | gap | fuelCopy
  | outFalse0 (h : Hold) | outFalse1 (h : Hold)
  | outFalse2 (h : Hold) | outFalse3 (h : Hold)
  | seekFuelLast (h : Hold) | seekFuelSep (h : Hold)
  | tailTake (h : Hold) | tailPending (head : Bool) (h : Hold)
  | tailCell0 (bit next : Bool) (h : Hold)
  | tailCell1 (bit next : Bool) (h : Hold)
  | tailCell2 (bit next : Bool) (h : Hold)
  | tailCell3 (bit next : Bool) (h : Hold)
  | tailDone0 (head : Bool) (h : Hold)
  | tailDone1 (head : Bool) (h : Hold)
  | tailDone2 (head : Bool) (h : Hold)
  | tailDone3 (head : Bool) (h : Hold)
  | tailCountStart (head : Bool) (h : Hold)
  | tailCountSkip (head : Bool) (h : Hold)
  | tailCountLoop (head : Bool) (h : Hold)
  | tailTick0 (head : Bool) (h : Hold)
  | tailTick1 (head : Bool) (h : Hold)
  | tailTick2 (head : Bool) (h : Hold)
  | tailTick3 (head : Bool) (h : Hold)
  | headCell0 (head : Bool) (h : Hold)
  | headCell1 (head : Bool) (h : Hold)
  | headCell2 (head : Bool) (h : Hold)
  | headCell3 (head : Bool) (h : Hold)
  | emptyDone0 (h : Hold) | emptyDone1 (h : Hold)
  | emptyDone2 (h : Hold) | emptyDone3 (h : Hold)
  | startDone0 (h : Hold) | startDone1 (h : Hold)
  | startDone2 (h : Hold) | startDone3 (h : Hold)
  | startLoop (remaining : Nat) (h : Hold)
  | startTick0 (remaining : Nat) (h : Hold)
  | startTick1 (remaining : Nat) (h : Hold)
  | startTick2 (remaining : Nat) (h : Hold)
  | startTick3 (remaining : Nat) (h : Hold)
  | fuelSeekStart (h : Hold) | fuelSeekEnd (h : Hold)
  | fuelEmit (h : Hold)
  | xCellLoop (h : Hold) | xCell0 (bit : Bool) (h : Hold)
  | xCell1 (bit : Bool) (h : Hold)
  | xCell2 (bit : Bool) (h : Hold)
  | xCell3 (bit : Bool) (h : Hold)
  | xDone0 (h : Hold) | xDone1 (h : Hold)
  | xDone2 (h : Hold) | xDone3 (h : Hold)
  | xCountStart (h : Hold) | xCountLoop (h : Hold)
  | xTick0 (h : Hold) | xTick1 (h : Hold)
  | xTick2 (h : Hold) | xTick3 (h : Hold)
  | header0 (h : Hold) | header1 (h : Hold)
  | header2 (h : Hold) | header3 (h : Hold)
  | flush (h : Hold) | position | halt
deriving DecidableEq, Repr

private def step
    (a0 a1 a2 : TapeAction) (target : State) :
    Option (TypedStep State) :=
  some ⟨target, a0, a1, a2⟩

private def copyBit (bit : Bool) (target : State) :
    Option (TypedStep State) :=
  step keepR (writeBitR bit) keepS target

private def stream
    (h : Hold) (bit : Bool) (a1 : TapeAction)
    (target : Hold -> State) : Option (TypedStep State) :=
  step keepS a1 (emitAction h) (target (some bit))

def next (start : Nat) :
    State -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep State)
  | .len0 => fun r0 _ _ =>
      match r0 with | some false => copyBit false .len1 | _ => none
  | .len1 => fun r0 _ _ =>
      match r0 with | some false => copyBit false .len2 | _ => none
  | .len2 => fun r0 _ _ =>
      match r0 with | some true => copyBit true .len3 | _ => none
  | .len3 => fun r0 _ _ =>
      match r0 with
      | some false => copyBit false .len0
      | some true => copyBit true .cells0
      | none => none
  | .cells0 => fun r0 _ _ =>
      match r0 with | some false => copyBit false .cells1 | _ => none
  | .cells1 => fun r0 _ _ =>
      match r0 with
      | some true => copyBit true .cells2
      | some false => copyBit false .limit2
      | none => none
  | .cells2 => fun r0 _ _ =>
      match r0 with | some bit => copyBit bit (.cells3 bit) | none => none
  | .cells3 third => fun r0 _ _ =>
      match third, r0 with
      | false, some true => copyBit true .cells0
      | true, some false => copyBit false .cells0
      | _, _ => none
  | .limit0 => fun r0 _ _ =>
      match r0 with | some false => copyBit false .limit1 | _ => none
  | .limit1 => fun r0 _ _ =>
      match r0 with | some false => copyBit false .limit2 | _ => none
  | .limit2 => fun r0 _ _ =>
      match r0 with | some true => copyBit true .limit3 | _ => none
  | .limit3 => fun r0 _ _ =>
      match r0 with
      | some false => copyBit false .limit0
      | some true => copyBit true .gap
      | none => none
  | .gap => fun _ _ _ => step keepS keepR keepS .fuelCopy
  | .fuelCopy => fun r0 _ _ =>
      match r0 with
      | some bit => copyBit bit .fuelCopy
      | none => step keepS keepS keepS (.outFalse0 none)
  | .outFalse0 h => fun _ _ _ => stream h true keepS .outFalse1
  | .outFalse1 h => fun _ _ _ => stream h false keepS .outFalse2
  | .outFalse2 h => fun _ _ _ => stream h true keepS .outFalse3
  | .outFalse3 h => fun _ _ _ => stream h false keepS .seekFuelLast
  | .seekFuelLast h => fun _ r1 _ =>
      match r1 with
      | none => step keepS keepL keepS (.seekFuelSep h)
      | some _ => none
  | .seekFuelSep h => fun _ r1 _ =>
      match r1 with
      | some _ => step keepS keepL keepS (.seekFuelSep h)
      | none => step keepS keepL keepS (.tailTake h)
  | .tailTake h => fun _ r1 _ =>
      match r1 with
      | some bit => step keepS keepL keepS (.tailPending bit h)
      | none => none
  | .tailPending head h => fun _ r1 _ =>
      match r1 with
      | some nextBit => step keepS keepS keepS (.tailCell0 head nextBit h)
      | none => step keepS keepS keepS (.tailDone0 head h)
  | .tailCell0 bit nextBit h => fun _ _ _ =>
      stream h (!bit) keepS (.tailCell1 bit nextBit)
  | .tailCell1 bit nextBit h => fun _ _ _ =>
      stream h bit keepS (.tailCell2 bit nextBit)
  | .tailCell2 bit nextBit h => fun _ _ _ =>
      stream h true keepS (.tailCell3 bit nextBit)
  | .tailCell3 _ nextBit h => fun _ _ _ =>
      stream h false keepL (.tailPending nextBit)
  | .tailDone0 head h => fun _ _ _ => stream h true keepS (.tailDone1 head)
  | .tailDone1 head h => fun _ _ _ => stream h true keepS (.tailDone2 head)
  | .tailDone2 head h => fun _ _ _ => stream h false keepS (.tailDone3 head)
  | .tailDone3 head h => fun _ _ _ =>
      stream h false keepS (.tailCountStart head)
  | .tailCountStart head h => fun _ _ _ =>
      step keepS keepR keepS (.tailCountSkip head h)
  | .tailCountSkip head h => fun _ r1 _ =>
      match r1 with
      | some _ => step keepS keepR keepS (.tailCountLoop head h)
      | none => none
  | .tailCountLoop head h => fun _ r1 _ =>
      match r1 with
      | some _ => step keepS keepS keepS (.tailTick0 head h)
      | none => step keepS keepS keepS (.headCell0 head h)
  | .tailTick0 head h => fun _ _ _ => stream h false keepS (.tailTick1 head)
  | .tailTick1 head h => fun _ _ _ => stream h true keepS (.tailTick2 head)
  | .tailTick2 head h => fun _ _ _ => stream h false keepS (.tailTick3 head)
  | .tailTick3 head h => fun _ _ _ =>
      stream h false keepR (.tailCountLoop head)
  | .headCell0 head h => fun _ _ _ => stream h (!head) keepS (.headCell1 head)
  | .headCell1 head h => fun _ _ _ => stream h head keepS (.headCell2 head)
  | .headCell2 head h => fun _ _ _ => stream h true keepS (.headCell3 head)
  | .headCell3 _ h => fun _ _ _ => stream h false keepS .emptyDone0
  | .emptyDone0 h => fun _ _ _ => stream h true keepS .emptyDone1
  | .emptyDone1 h => fun _ _ _ => stream h true keepS .emptyDone2
  | .emptyDone2 h => fun _ _ _ => stream h false keepS .emptyDone3
  | .emptyDone3 h => fun _ _ _ => stream h false keepS .startDone0
  | .startDone0 h => fun _ _ _ => stream h true keepS .startDone1
  | .startDone1 h => fun _ _ _ => stream h true keepS .startDone2
  | .startDone2 h => fun _ _ _ => stream h false keepS .startDone3
  | .startDone3 h => fun _ _ _ => stream h false keepS (.startLoop start)
  | .startLoop remaining h => fun _ _ _ =>
      match remaining with
      | 0 => step keepS keepS keepS (.fuelSeekStart h)
      | j + 1 => step keepS keepS keepS (.startTick0 j h)
  | .startTick0 j h => fun _ _ _ => stream h false keepS (.startTick1 j)
  | .startTick1 j h => fun _ _ _ => stream h true keepS (.startTick2 j)
  | .startTick2 j h => fun _ _ _ => stream h false keepS (.startTick3 j)
  | .startTick3 j h => fun _ _ _ => stream h false keepS (.startLoop j)
  | .fuelSeekStart h => fun _ r1 _ =>
      match r1 with
      | none => step keepS keepR keepS (.fuelSeekEnd h)
      | some _ => none
  | .fuelSeekEnd h => fun _ r1 _ =>
      match r1 with
      | some _ => step keepS keepR keepS (.fuelSeekEnd h)
      | none => step keepS keepL keepS (.fuelEmit h)
  | .fuelEmit h => fun _ r1 _ =>
      match r1 with
      | some bit => stream h bit keepL .fuelEmit
      | none => step keepS keepL keepS (.xCellLoop h)
  | .xCellLoop h => fun _ r1 _ =>
      match r1 with
      | some bit => step keepS keepS keepS (.xCell0 bit h)
      | none => step keepS keepS keepS (.xDone0 h)
  | .xCell0 bit h => fun _ _ _ => stream h (!bit) keepS (.xCell1 bit)
  | .xCell1 bit h => fun _ _ _ => stream h bit keepS (.xCell2 bit)
  | .xCell2 bit h => fun _ _ _ => stream h true keepS (.xCell3 bit)
  | .xCell3 _ h => fun _ _ _ => stream h false keepL .xCellLoop
  | .xDone0 h => fun _ _ _ => stream h true keepS .xDone1
  | .xDone1 h => fun _ _ _ => stream h true keepS .xDone2
  | .xDone2 h => fun _ _ _ => stream h false keepS .xDone3
  | .xDone3 h => fun _ _ _ => stream h false keepS .xCountStart
  | .xCountStart h => fun _ _ _ => step keepS keepR keepS (.xCountLoop h)
  | .xCountLoop h => fun _ r1 _ =>
      match r1 with
      | some _ => step keepS keepS keepS (.xTick0 h)
      | none => step keepS keepS keepS (.header0 h)
  | .xTick0 h => fun _ _ _ => stream h false keepS .xTick1
  | .xTick1 h => fun _ _ _ => stream h true keepS .xTick2
  | .xTick2 h => fun _ _ _ => stream h false keepS .xTick3
  | .xTick3 h => fun _ _ _ => stream h false keepR .xCountLoop
  | .header0 h => fun _ _ _ => stream h false keepS .header1
  | .header1 h => fun _ _ _ => stream h false keepS .header2
  | .header2 h => fun _ _ _ => stream h false keepS .header3
  | .header3 h => fun _ _ _ => stream h false keepS .flush
  | .flush h => fun _ _ _ => step keepS keepS (flushAction h) .position
  | .position => fun _ _ _ => step keepS keepS keepR .halt
  | .halt => fun _ _ _ => none

def holdValues : List Hold := [none, some false, some true]
def boolValues : List Bool := [false, true]

def fixedStates : List State :=
  [ .len0, .len1, .len2, .len3
  , .cells0, .cells1, .cells2, .cells3 false, .cells3 true
  , .limit0, .limit1, .limit2, .limit3, .gap, .fuelCopy
  , .position, .halt ]

def emissionBlock (h : Hold) : List State :=
  [ .outFalse0 h, .outFalse1 h, .outFalse2 h, .outFalse3 h
  , .seekFuelLast h, .seekFuelSep h, .tailTake h
  , .emptyDone0 h, .emptyDone1 h, .emptyDone2 h, .emptyDone3 h
  , .startDone0 h, .startDone1 h, .startDone2 h, .startDone3 h
  , .fuelSeekStart h, .fuelSeekEnd h, .fuelEmit h, .xCellLoop h
  , .xDone0 h, .xDone1 h, .xDone2 h, .xDone3 h
  , .xCountStart h, .xCountLoop h
  , .xTick0 h, .xTick1 h, .xTick2 h, .xTick3 h
  , .header0 h, .header1 h, .header2 h, .header3 h
  , .flush h ] ++
  (boolValues.flatMap fun bit =>
    [ .tailPending bit h
    , .tailDone0 bit h, .tailDone1 bit h
    , .tailDone2 bit h, .tailDone3 bit h
    , .tailCountStart bit h, .tailCountSkip bit h, .tailCountLoop bit h
    , .tailTick0 bit h, .tailTick1 bit h
    , .tailTick2 bit h, .tailTick3 bit h
    , .headCell0 bit h, .headCell1 bit h
    , .headCell2 bit h, .headCell3 bit h
    , .xCell0 bit h, .xCell1 bit h, .xCell2 bit h, .xCell3 bit h ]) ++
  (boolValues.flatMap fun bit =>
    boolValues.flatMap fun nextBit =>
      [ .tailCell0 bit nextBit h, .tailCell1 bit nextBit h
      , .tailCell2 bit nextBit h, .tailCell3 bit nextBit h ])

def startBlock (start : Nat) (h : Hold) : List State :=
  (List.range (start + 1)).flatMap fun j =>
    [ .startLoop j h, .startTick0 j h, .startTick1 j h
    , .startTick2 j h, .startTick3 j h ]

def states (start : Nat) : List State :=
  fixedStates ++
    holdValues.flatMap fun h => emissionBlock h ++ startBlock start h

theorem mem_states_fixed {start : Nat} {s : State}
    (hs : s ∈ fixedStates) : s ∈ states start :=
  List.mem_append.mpr (Or.inl hs)

theorem mem_holdValues (h : Hold) : h ∈ holdValues := by
  cases h with
  | none => simp [holdValues]
  | some bit => cases bit <;> simp [holdValues]

theorem mem_states_emission {start : Nat} {s : State} {h : Hold}
    (hs : s ∈ emissionBlock h) : s ∈ states start := by
  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨h, ?_, ?_⟩))
  · exact mem_holdValues h
  · exact List.mem_append.mpr (Or.inl hs)

theorem mem_states_start {start : Nat} {s : State} {h : Hold}
    (hs : s ∈ startBlock start h) : s ∈ states start := by
  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨h, ?_, ?_⟩))
  · exact mem_holdValues h
  · exact List.mem_append.mpr (Or.inr hs)

set_option maxRecDepth 10000 in
theorem startLoop_pred_mem {start j : Nat} {h : Hold}
    (hs : State.startLoop (j + 1) h ∈ states start) :
    State.startTick0 j h ∈ states start := by
  simp [states, fixedStates, emissionBlock, startBlock, holdValues,
    boolValues] at hs ⊢
  rcases hs with
    ⟨a, ha, hja, hh⟩ | ⟨a, ha, hja, hh⟩ | ⟨a, ha, hja, hh⟩
  · left
    exact ⟨j, by lia, rfl, hh⟩
  · right; left
    exact ⟨j, by lia, rfl, hh⟩
  · right; right
    exact ⟨j, by lia, rfl, hh⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem next_target_mem (start : Nat) :
    forall s : State, s ∈ states start ->
      forall r0 r1 r2 : Option Bool, forall st : TypedStep State,
        next start s r0 r1 r2 = some st -> st.target ∈ states start := by
  intro s hs r0 r1 r2 st hnext
  cases s
  all_goals simp only [next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [copyBit, stream, step] at hnext
  all_goals try cases hnext
  all_goals try exact startLoop_pred_mem hs
  all_goals simp_all [states, fixedStates, emissionBlock, startBlock,
    holdValues, boolValues]
  all_goals grind
  done

def table (start : Nat) : TypedStateTable State :=
  TypedStateTable.ofList (states start) .len0 .halt (next start)
    (by simp [states, fixedStates])
    (by simp [states, fixedStates])
    (by intros; rfl)
    (next_target_mem start)

end FuelSimulatorCore
end StructuredConstructionTargets

end Computability
end FoC
