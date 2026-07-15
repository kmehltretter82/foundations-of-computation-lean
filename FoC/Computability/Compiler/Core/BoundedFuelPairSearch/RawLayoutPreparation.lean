import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorCore.Runs.Emission
import FoC.Computability.Compiler.Structured.Lowering.EncodedInjectivity

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets
namespace RawLayoutPreparation

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

inductive State where
  | seekRawEnd
  | copyRawBack
  | syncRawRight
  | seekFuelEnd
  | eraseRawBack
  | halt
deriving DecidableEq, Repr

private def step
    (a0 a1 a2 : TapeAction) (target : State) :
    Option (TypedStep State) :=
  some ⟨target, a0, a1, a2⟩

def next : State -> Option Bool -> Option Bool -> Option Bool ->
    Option (TypedStep State)
  | .seekRawEnd => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepS keepR .seekRawEnd
      | none => step keepS keepL keepL .copyRawBack
  | .copyRawBack => fun _ _ r2 =>
      match r2 with
      | some bit => step keepS (writeBitL bit) keepL .copyRawBack
      | none => step keepS keepR keepR .syncRawRight
  | .syncRawRight => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepR keepR .syncRawRight
      | none => step keepS keepR keepS .seekFuelEnd
  | .seekFuelEnd => fun _ r1 _ =>
      match r1 with
      | some _ => step keepS keepR keepS .seekFuelEnd
      | none => step keepS keepS keepL .eraseRawBack
  | .eraseRawBack => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepS eraseL .eraseRawBack
      | none => step keepS keepS keepS .halt
  | .halt => fun _ _ _ => none

def states : List State :=
  [ .seekRawEnd, .copyRawBack, .syncRawRight, .seekFuelEnd,
    .eraseRawBack, .halt ]

theorem next_target_mem :
    forall s : State, s ∈ states ->
      forall r0 r1 r2 : Option Bool, forall st : TypedStep State,
        next s r0 r1 r2 = some st -> st.target ∈ states := by
  intro s hs r0 r1 r2 st hnext
  cases s <;> simp only [next] at hnext
  all_goals repeat' split at hnext
  all_goals try simp only [step] at hnext
  all_goals try cases hnext
  all_goals simp [states]

def table : TypedStateTable State :=
  TypedStateTable.ofList states .seekRawEnd .halt next
    (by simp [states]) (by simp [states])
    (by intros; rfl) next_target_mem

def D : Description := table.description

def cfg (s : State) (T0 T1 T2 : Tape Bool) :
    CommonGround.FiniteTransducers.Structured.Configuration :=
  table.config s T0 T1 T2

def cursorFuelSourceTape (fuel : Nat) : Tape Bool :=
  tapeAtCells [] (none :: (stageNatBits fuel).map some)

def emitterEntryScratch (raw : Word Bool) (fuel : Nat) : Tape Bool :=
  tapeAtCells
    (List.append ((stageNatBits fuel).reverse.map some)
      (none :: raw.reverse.map some)) []

def preparedEntryScratch (raw : Word Bool) (fuel : Nat) : Tape Bool :=
  tapeAtCells
    (List.append ((stageNatBits fuel).reverse.map some)
      (none :: List.append (raw.reverse.map some) [none])) []

def erasedRawTape (raw : Word Bool) : Tape Bool :=
  tapeAtCells [] (List.replicate (raw.length + 2) none)

theorem preparedEntryScratch_equiv_rawEmissionEntry
    (raw : Word Bool) (fuel : Nat) :
    Tape.Equiv (preparedEntryScratch raw fuel)
      (emitterEntryScratch raw fuel) := by
  refine ⟨?_, rfl, rfl⟩
  simpa [preparedEntryScratch, emitterEntryScratch, tapeAtCells,
      List.map_reverse, List.append_assoc] using
    (dropTrailingNone_append_none
      (List.append ((stageNatBits fuel).reverse.map some)
        (none :: raw.reverse.map some)))

theorem erasedRawTape_equiv_blank (raw : Word Bool) :
    Tape.Equiv (erasedRawTape raw) Tape.blank := by
  simp [Tape.Equiv, erasedRawTape, Tape.blank, tapeAtCells,
    List.replicate_succ, Tape.dropTrailingNone,
    FoC.Computability.dropTrailingNone_replicate_none]

theorem leads_seekRawEnd_bit
    (bit : Bool) (left right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (cfg .seekRawEnd T0 T1
        (tapeAtCells left (some bit :: right)))
      (cfg .seekRawEnd T0 T1
        (tapeAtCells (some bit :: left) right)) := by
  simpa [cfg] using
    TypedStateTable.leads_step table
      (s := State.seekRawEnd)
      (T0 := T0) (T1 := T1)
      (T2 := tapeAtCells left (some bit :: right))
      (st := ⟨State.seekRawEnd, keepS, keepS, keepR⟩)
      (T0' := T0) (T1' := T1)
      (T2' := tapeAtCells (some bit :: left) right)
      (by simp [table, TypedStateTable.ofList, states]) (by rfl) rfl rfl
      (keepR_apply_tapeAtCells left (some bit) right)

theorem leads_seekRawEnd_word
    (bits : Word Bool) (left : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (cfg .seekRawEnd T0 T1
        (tapeAtCells left (bits.map some)))
      (cfg .seekRawEnd T0 T1
        (tapeAtCells
          (List.append (bits.reverse.map some) left) [])) := by
  induction bits generalizing left with
  | nil =>
      simpa using TypedStateTable.Leads.refl table
        (cfg .seekRawEnd T0 T1 (tapeAtCells left []))
  | cons bit rest ih =>
      refine (leads_seekRawEnd_bit bit left (rest.map some) T0 T1).trans ?_
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem leads_seekRawEnd_finish
    (bit : Bool) (left : List (Option Bool))
    (fuelCells : List (Option Bool)) (T0 : Tape Bool) :
    table.Leads
      (cfg .seekRawEnd T0
        (tapeAtCells [] (none :: fuelCells))
        (tapeAtCells (some bit :: left) []))
      (cfg .copyRawBack T0
        (tapeAtCells [] (none :: none :: fuelCells))
        (tapeAtCells left [some bit, none])) := by
  simpa [cfg] using
    TypedStateTable.leads_step table
      (s := State.seekRawEnd)
      (T0 := T0)
      (T1 := tapeAtCells [] (none :: fuelCells))
      (T2 := tapeAtCells (some bit :: left) [])
      (st := ⟨State.copyRawBack, keepS, keepL, keepL⟩)
      (T0' := T0)
      (T1' := tapeAtCells [] (none :: none :: fuelCells))
      (T2' := tapeAtCells left [some bit, none])
      (by simp [table, TypedStateTable.ofList, states]) (by rfl) rfl
      (keepL_apply_tapeAtCells_left_nil none fuelCells)
      (keepL_apply_tapeAtCells_nil left (some bit))

theorem leads_copyRawBack_bits
    (leftBits : Word Bool) (current : Bool)
    (suffix1 right2 : List (Option Bool)) (T0 : Tape Bool) :
    table.Leads
      (cfg .copyRawBack T0
        (tapeAtCells [] (none :: suffix1))
        (tapeAtCells (leftBits.map some) (some current :: right2)))
      (cfg .copyRawBack T0
        (tapeAtCells []
          (none :: List.append ((current :: leftBits).reverse.map some)
            suffix1))
        (tapeAtCells []
          (none :: List.append ((current :: leftBits).reverse.map some)
            right2))) := by
  induction leftBits generalizing current suffix1 right2 with
  | nil =>
      have h1 :
          (writeBitL current).apply (tapeAtCells [] (none :: suffix1)) =
            tapeAtCells [] (none :: some current :: suffix1) := by
        cases suffix1 <;> rfl
      simpa [cfg] using
        TypedStateTable.leads_step table
          (s := State.copyRawBack)
          (T0 := T0)
          (T1 := tapeAtCells [] (none :: suffix1))
          (T2 := tapeAtCells [] (some current :: right2))
          (st := ⟨State.copyRawBack, keepS, writeBitL current, keepL⟩)
          (T0' := T0)
          (T1' := tapeAtCells [] (none :: some current :: suffix1))
          (T2' := tapeAtCells [] (none :: some current :: right2))
          (by simp [table, TypedStateTable.ofList, states]) (by rfl) rfl h1
          (keepL_apply_tapeAtCells_left_nil (some current) right2)
  | cons previous rest ih =>
      have h1 :
          (writeBitL current).apply (tapeAtCells [] (none :: suffix1)) =
            tapeAtCells [] (none :: some current :: suffix1) := by
        cases suffix1 <;> rfl
      have hstep : table.Leads
          (cfg .copyRawBack T0
            (tapeAtCells [] (none :: suffix1))
            (tapeAtCells ((previous :: rest).map some)
              (some current :: right2)))
          (cfg .copyRawBack T0
            (tapeAtCells [] (none :: some current :: suffix1))
            (tapeAtCells (rest.map some)
              (some previous :: some current :: right2))) := by
        simpa [cfg] using
          TypedStateTable.leads_step table
            (s := State.copyRawBack)
            (T0 := T0)
            (T1 := tapeAtCells [] (none :: suffix1))
            (T2 := tapeAtCells ((previous :: rest).map some)
              (some current :: right2))
            (st := ⟨State.copyRawBack, keepS, writeBitL current, keepL⟩)
            (T0' := T0)
            (T1' := tapeAtCells [] (none :: some current :: suffix1))
            (T2' := tapeAtCells (rest.map some)
              (some previous :: some current :: right2))
            (by simp [table, TypedStateTable.ofList, states]) (by rfl) rfl h1
            (keepL_apply_tapeAtCells (rest.map some) (some previous)
              (some current) right2)
      refine hstep.trans ?_
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih previous (some current :: suffix1) (some current :: right2)

theorem leads_copyRawBack_finish
    (rawCells fuelCells : List (Option Bool)) (T0 : Tape Bool) :
    table.Leads
      (cfg .copyRawBack T0
        (tapeAtCells []
          (none :: List.append rawCells (none :: fuelCells)))
        (tapeAtCells []
          (none :: List.append rawCells [none])))
      (cfg .syncRawRight T0
        (tapeAtCells [none]
          (List.append rawCells (none :: fuelCells)))
        (tapeAtCells [none]
          (List.append rawCells [none]))) := by
  simpa [cfg] using
    TypedStateTable.leads_step table
      (s := State.copyRawBack)
      (T0 := T0)
      (T1 := tapeAtCells []
        (none :: List.append rawCells (none :: fuelCells)))
      (T2 := tapeAtCells []
        (none :: List.append rawCells [none]))
      (st := ⟨State.syncRawRight, keepS, keepR, keepR⟩)
      (T0' := T0)
      (T1' := tapeAtCells [none]
        (List.append rawCells (none :: fuelCells)))
      (T2' := tapeAtCells [none]
        (List.append rawCells [none]))
      (by simp [table, TypedStateTable.ofList, states]) (by rfl) rfl
      (keepR_apply_tapeAtCells [] none
        (List.append rawCells (none :: fuelCells)))
      (keepR_apply_tapeAtCells [] none
        (List.append rawCells [none]))

theorem leads_syncRawRight_bit
    (bit : Bool)
    (left1 left2 right1 right2 : List (Option Bool))
    (T0 : Tape Bool) :
    table.Leads
      (cfg .syncRawRight T0
        (tapeAtCells left1 (some bit :: right1))
        (tapeAtCells left2 (some bit :: right2)))
      (cfg .syncRawRight T0
        (tapeAtCells (some bit :: left1) right1)
        (tapeAtCells (some bit :: left2) right2)) := by
  simpa [cfg] using
    TypedStateTable.leads_step table
      (s := State.syncRawRight)
      (T0 := T0)
      (T1 := tapeAtCells left1 (some bit :: right1))
      (T2 := tapeAtCells left2 (some bit :: right2))
      (st := ⟨State.syncRawRight, keepS, keepR, keepR⟩)
      (T0' := T0)
      (T1' := tapeAtCells (some bit :: left1) right1)
      (T2' := tapeAtCells (some bit :: left2) right2)
      (by simp [table, TypedStateTable.ofList, states]) (by rfl) rfl
      (keepR_apply_tapeAtCells left1 (some bit) right1)
      (keepR_apply_tapeAtCells left2 (some bit) right2)

theorem leads_syncRawRight_word
    (bits : Word Bool)
    (left1 left2 tail1 tail2 : List (Option Bool))
    (T0 : Tape Bool) :
    table.Leads
      (cfg .syncRawRight T0
        (tapeAtCells left1
          (List.append (bits.map some) tail1))
        (tapeAtCells left2
          (List.append (bits.map some) tail2)))
      (cfg .syncRawRight T0
        (tapeAtCells
          (List.append (bits.reverse.map some) left1) tail1)
        (tapeAtCells
          (List.append (bits.reverse.map some) left2) tail2)) := by
  induction bits generalizing left1 left2 with
  | nil =>
      simpa using TypedStateTable.Leads.refl table
        (cfg .syncRawRight T0
          (tapeAtCells left1 tail1) (tapeAtCells left2 tail2))
  | cons bit rest ih =>
      refine (leads_syncRawRight_bit bit left1 left2
        (List.append (rest.map some) tail1)
        (List.append (rest.map some) tail2) T0).trans ?_
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left1) (some bit :: left2)

theorem leads_syncRawRight_finish
    (left1 left2 fuelCells right2 : List (Option Bool))
    (T0 : Tape Bool) :
    table.Leads
      (cfg .syncRawRight T0
        (tapeAtCells left1 (none :: fuelCells))
        (tapeAtCells left2 (none :: right2)))
      (cfg .seekFuelEnd T0
        (tapeAtCells (none :: left1) fuelCells)
        (tapeAtCells left2 (none :: right2))) := by
  simpa [cfg] using
    TypedStateTable.leads_step table
      (s := State.syncRawRight)
      (T0 := T0)
      (T1 := tapeAtCells left1 (none :: fuelCells))
      (T2 := tapeAtCells left2 (none :: right2))
      (st := ⟨State.seekFuelEnd, keepS, keepR, keepS⟩)
      (T0' := T0)
      (T1' := tapeAtCells (none :: left1) fuelCells)
      (T2' := tapeAtCells left2 (none :: right2))
      (by simp [table, TypedStateTable.ofList, states]) (by rfl) rfl
      (keepR_apply_tapeAtCells left1 none fuelCells) rfl

theorem leads_seekFuelEnd_bit
    (bit : Bool) (left right : List (Option Bool))
    (T0 T2 : Tape Bool) :
    table.Leads
      (cfg .seekFuelEnd T0
        (tapeAtCells left (some bit :: right)) T2)
      (cfg .seekFuelEnd T0
        (tapeAtCells (some bit :: left) right) T2) := by
  simpa [cfg] using
    TypedStateTable.leads_step table
      (s := State.seekFuelEnd)
      (T0 := T0)
      (T1 := tapeAtCells left (some bit :: right))
      (T2 := T2)
      (st := ⟨State.seekFuelEnd, keepS, keepR, keepS⟩)
      (T0' := T0)
      (T1' := tapeAtCells (some bit :: left) right)
      (T2' := T2)
      (by simp [table, TypedStateTable.ofList, states]) (by rfl) rfl
      (keepR_apply_tapeAtCells left (some bit) right) rfl

theorem leads_seekFuelEnd_word
    (bits : Word Bool) (left : List (Option Bool))
    (T0 T2 : Tape Bool) :
    table.Leads
      (cfg .seekFuelEnd T0
        (tapeAtCells left (bits.map some)) T2)
      (cfg .seekFuelEnd T0
        (tapeAtCells
          (List.append (bits.reverse.map some) left) []) T2) := by
  induction bits generalizing left with
  | nil =>
      simpa using TypedStateTable.Leads.refl table
        (cfg .seekFuelEnd T0 (tapeAtCells left []) T2)
  | cons bit rest ih =>
      refine (leads_seekFuelEnd_bit bit left (rest.map some) T0 T2).trans ?_
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem leads_seekFuelEnd_finish
    (previous : Option Bool)
    (left1 left2 right2 : List (Option Bool))
    (T0 : Tape Bool) :
    table.Leads
      (cfg .seekFuelEnd T0
        (tapeAtCells left1 [])
        (tapeAtCells (previous :: left2) (none :: right2)))
      (cfg .eraseRawBack T0
        (tapeAtCells left1 [])
        (tapeAtCells left2 (previous :: none :: right2))) := by
  simpa [cfg] using
    TypedStateTable.leads_step table
      (s := State.seekFuelEnd)
      (T0 := T0)
      (T1 := tapeAtCells left1 [])
      (T2 := tapeAtCells (previous :: left2) (none :: right2))
      (st := ⟨State.eraseRawBack, keepS, keepS, keepL⟩)
      (T0' := T0)
      (T1' := tapeAtCells left1 [])
      (T2' := tapeAtCells left2 (previous :: none :: right2))
      (by simp [table, TypedStateTable.ofList, states]) (by rfl)
      rfl rfl
      (keepL_apply_tapeAtCells left2 previous none right2)

theorem replicate_none_append_none
    (n : Nat) (right : List (Option Bool)) :
    List.append (List.replicate n none) (none :: right) =
      none :: List.append (List.replicate n none) right := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [List.replicate_succ] using congrArg (fun xs => none :: xs) ih

theorem leads_eraseRawBack_bits
    (bits : Word Bool) (current : Bool)
    (right : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (cfg .eraseRawBack T0 T1
        (tapeAtCells
          (List.append (bits.map some) [none])
          (some current :: right)))
      (cfg .eraseRawBack T0 T1
        (tapeAtCells []
          (none :: List.append
            (List.replicate (bits.length + 1) none) right))) := by
  induction bits generalizing current right with
  | nil =>
      have h2 :
          eraseL.apply (tapeAtCells [none] (some current :: right)) =
            tapeAtCells [] (none :: none :: right) := by
        cases right <;> rfl
      simpa [cfg] using
        TypedStateTable.leads_step table
          (s := State.eraseRawBack)
          (T0 := T0) (T1 := T1)
          (T2 := tapeAtCells [none] (some current :: right))
          (st := ⟨State.eraseRawBack, keepS, keepS, eraseL⟩)
          (T0' := T0) (T1' := T1)
          (T2' := tapeAtCells [] (none :: none :: right))
          (by simp [table, TypedStateTable.ofList, states]) (by rfl)
          rfl rfl h2
  | cons previous rest ih =>
      have h2 :
          eraseL.apply
              (tapeAtCells
                (some previous :: List.append (rest.map some) [none])
                (some current :: right)) =
            tapeAtCells (List.append (rest.map some) [none])
              (some previous :: none :: right) := by
        cases right <;> rfl
      have hstep : table.Leads
          (cfg .eraseRawBack T0 T1
            (tapeAtCells
              (List.append ((previous :: rest).map some) [none])
              (some current :: right)))
          (cfg .eraseRawBack T0 T1
            (tapeAtCells (List.append (rest.map some) [none])
              (some previous :: none :: right))) := by
        simpa [cfg] using
          TypedStateTable.leads_step table
            (s := State.eraseRawBack)
            (T0 := T0) (T1 := T1)
            (T2 := tapeAtCells
              (List.append ((previous :: rest).map some) [none])
              (some current :: right))
            (st := ⟨State.eraseRawBack, keepS, keepS, eraseL⟩)
            (T0' := T0) (T1' := T1)
            (T2' := tapeAtCells (List.append (rest.map some) [none])
              (some previous :: none :: right))
            (by simp [table, TypedStateTable.ofList, states]) (by rfl)
            rfl rfl h2
      refine hstep.trans ?_
      have hih := ih previous (none :: right)
      rw [replicate_none_append_none (rest.length + 1) right] at hih
      simpa [List.length_cons, List.replicate_succ,
        List.append_assoc] using hih

theorem leads_eraseRawBack_finish
    (right : List (Option Bool)) (T0 T1 : Tape Bool) :
    table.Leads
      (cfg .eraseRawBack T0 T1 (tapeAtCells [] (none :: right)))
      (cfg .halt T0 T1 (tapeAtCells [] (none :: right))) := by
  simpa [cfg] using
    TypedStateTable.leads_step table
      (s := State.eraseRawBack)
      (T0 := T0) (T1 := T1)
      (T2 := tapeAtCells [] (none :: right))
      (st := ⟨State.halt, keepS, keepS, keepS⟩)
      (T0' := T0) (T1' := T1)
      (T2' := tapeAtCells [] (none :: right))
      (by simp [table, TypedStateTable.ofList, states]) (by rfl)
      rfl rfl rfl

theorem erased_cells_shape
    (bits : Word Bool) :
    none :: List.append
        (List.replicate (bits.length + 1) (none : Option Bool)) [none] =
      List.replicate ((false :: bits).length + 2) none := by
  rw [replicate_none_append_none (bits.length + 1) []]
  simp [List.replicate_succ]

theorem leads_seekFuelEnd_through_erase_of_reverse_cons
    (last : Bool) (leftBits : Word Bool)
    (fuelLeft : List (Option Bool)) (T0 : Tape Bool) :
    table.Leads
      (cfg .seekFuelEnd T0 (tapeAtCells fuelLeft [])
        (tapeAtCells
          (List.append ((last :: leftBits).map some) [none]) [none]))
      (cfg .halt T0 (tapeAtCells fuelLeft [])
        (tapeAtCells []
          (List.replicate ((last :: leftBits).length + 2) none))) := by
  refine (leads_seekFuelEnd_finish (some last) fuelLeft
    (List.append (leftBits.map some) [none]) [] T0).trans ?_
  refine (leads_eraseRawBack_bits leftBits last [none]
    T0 (tapeAtCells fuelLeft [])).trans ?_
  have hfinish := leads_eraseRawBack_finish
    (List.append (List.replicate (leftBits.length + 1) none) [none])
    T0 (tapeAtCells fuelLeft [])
  rw [erased_cells_shape leftBits] at hfinish
  rw [erased_cells_shape leftBits]
  simpa using hfinish

theorem leads_seekFuelEnd_through_erase
    (raw : Word Bool) (hraw : raw ≠ [])
    (fuelLeft : List (Option Bool)) (T0 : Tape Bool) :
    table.Leads
      (cfg .seekFuelEnd T0 (tapeAtCells fuelLeft [])
        (tapeAtCells
          (List.append (raw.reverse.map some) [none]) [none]))
      (cfg .halt T0 (tapeAtCells fuelLeft []) (erasedRawTape raw)) := by
  cases hrev : raw.reverse with
  | nil =>
      have hnil : raw = [] := by
        have hr := congrArg List.reverse hrev
        simpa using! hr
      exact (hraw hnil).elim
  | cons last leftBits =>
      have hlen : raw.length = (last :: leftBits).length := by
        have hl := congrArg List.length hrev
        simpa [List.length_reverse] using hl
      have hrun :=
        leads_seekFuelEnd_through_erase_of_reverse_cons
          last leftBits fuelLeft T0
      simpa [hrev, erasedRawTape, hlen] using hrun

theorem tapeAtCells_map_some_eq_input (bits : Word Bool) :
    tapeAtCells [] (bits.map some) = Tape.input bits := by
  cases bits <;> rfl

theorem leads_prepare_raw_emission
    (raw : Word Bool) (hraw : raw ≠ [])
    (fuel : Nat) (T0 : Tape Bool) :
    table.Leads
      (cfg .seekRawEnd T0 (cursorFuelSourceTape fuel) (Tape.input raw))
      (cfg .halt T0 (preparedEntryScratch raw fuel)
        (erasedRawTape raw)) := by
  cases hrev : raw.reverse with
  | nil =>
      have hnil : raw = [] := by
        have hr := congrArg List.reverse hrev
        simpa using! hr
      exact (hraw hnil).elim
  | cons last leftBits =>
      have hshape : (last :: leftBits).reverse = raw := by
        have hr := congrArg List.reverse hrev
        simpa using! hr.symm
      have hseek : table.Leads
          (cfg .seekRawEnd T0 (cursorFuelSourceTape fuel) (Tape.input raw))
          (cfg .seekRawEnd T0 (cursorFuelSourceTape fuel)
            (tapeAtCells (some last :: leftBits.map some) [])) := by
        simpa [hrev, tapeAtCells_map_some_eq_input] using
          (leads_seekRawEnd_word raw [] T0 (cursorFuelSourceTape fuel))
      refine hseek.trans ?_
      have hfinishSeek : table.Leads
          (cfg .seekRawEnd T0 (cursorFuelSourceTape fuel)
            (tapeAtCells (some last :: leftBits.map some) []))
          (cfg .copyRawBack T0
            (tapeAtCells []
              (none :: none :: (stageNatBits fuel).map some))
            (tapeAtCells (leftBits.map some) [some last, none])) := by
        simpa [cursorFuelSourceTape] using
          (leads_seekRawEnd_finish last (leftBits.map some)
            ((stageNatBits fuel).map some) T0)
      refine hfinishSeek.trans ?_
      have hcopy :=
        leads_copyRawBack_bits leftBits last
          (none :: (stageNatBits fuel).map some) [none] T0
      rw [hshape] at hcopy
      refine hcopy.trans ?_
      refine (leads_copyRawBack_finish (raw.map some)
        ((stageNatBits fuel).map some) T0).trans ?_
      refine (leads_syncRawRight_word raw [none] [none]
        (none :: (stageNatBits fuel).map some) [none] T0).trans ?_
      refine (leads_syncRawRight_finish
        (List.append (raw.reverse.map some) [none])
        (List.append (raw.reverse.map some) [none])
        ((stageNatBits fuel).map some) [] T0).trans ?_
      refine (leads_seekFuelEnd_word (stageNatBits fuel)
        (none :: List.append (raw.reverse.map some) [none]) T0
        (tapeAtCells
          (List.append (raw.reverse.map some) [none]) [none])).trans ?_
      simpa [preparedEntryScratch] using
        (leads_seekFuelEnd_through_erase raw hraw
          (List.append ((stageNatBits fuel).reverse.map some)
            (none :: List.append (raw.reverse.map some) [none])) T0)

theorem erasedRawTape_ne_blank (raw : Word Bool) :
    erasedRawTape raw ≠ Tape.blank := by
  intro h
  have hright := congrArg Tape.right h
  simp [erasedRawTape, Tape.blank, tapeAtCells,
    List.replicate_succ] at hright

/-- The natural component boundary cannot be closed merely by transporting
the two logical tape equivalences above: guarded physical encodings remember
the exact padding representatives. -/
theorem prepared_guarded_not_equiv_rawEmission_guarded
    (raw : Word Bool) (fuel : Nat) (T0 : Tape Bool) :
    ¬ Tape.Equiv
      (encodedGuardedStructured3Tapes T0
        (preparedEntryScratch raw fuel) (erasedRawTape raw))
      (encodedGuardedStructured3Tapes T0
        (emitterEntryScratch raw fuel) Tape.blank) := by
  intro h
  have heq := encodedGuardedStructuredTapes_three_equiv_inj
    (by simpa [encodedGuardedStructured3Tapes] using h)
  exact erasedRawTape_ne_blank raw heq.2.2

end RawLayoutPreparation
end StructuredConstructionTargets

end Computability
end FoC
