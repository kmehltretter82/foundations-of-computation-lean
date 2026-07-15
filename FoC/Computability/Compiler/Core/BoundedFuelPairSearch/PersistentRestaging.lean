import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.RawLayoutEmission
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.RawLayoutPreparation
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh
import FoC.Computability.Compiler.Structured.Lowering.TypedStateRuns

set_option doc.verso true

/-!
# Persistent fuel-pair loop restaging

After the checker attempt fails, logical tape 0 contains the serialized source
run together with the checker fuel, while logical tape 1 contains the candidate
input together with the source fuel.  This finite table erases the obsolete
source run, copies the candidate back to logical tape 2, and restores the two
unary fuel-source tapes needed by the next pair of fused emissions.
-/

namespace FoC
namespace Computability

open Languages
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open StructuredConstructionTargets.FuelSimulatorCore.RawLayoutEmission
open StructuredConstructionTargets.RawLayoutPreparation
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace BoundedFuelPairSearch
namespace PersistentRestaging

inductive State where
  | checkerSeek
  | checkerScanLeft
  | checkerEraseRight
  | candidateSeek
  | candidateCopyLeft
  | candidateEraseRight
  | candidateRewindLeft
  | halt
deriving DecidableEq, Repr

private def step (a0 a1 a2 : TapeAction) (target : State) :=
  some (TypedStep.mk target a0 a1 a2)

def next : State -> Option Bool -> Option Bool -> Option Bool ->
    Option (TypedStep State)
  | .checkerSeek => fun _ _ _ => step keepL keepS keepS .checkerScanLeft
  | .checkerScanLeft => fun r0 _ _ =>
      match r0 with
      | some _ => step keepL keepS keepS .checkerScanLeft
      | none => step keepR keepS keepS .checkerEraseRight
  | .checkerEraseRight => fun r0 _ _ =>
      match r0 with
      | some _ => step eraseR keepS keepS .checkerEraseRight
      | none => step keepS keepS keepS .candidateSeek
  | .candidateSeek => fun _ _ _ =>
      step keepS keepL keepS .candidateCopyLeft
  | .candidateCopyLeft => fun _ r1 _ =>
      match r1 with
      | some bit => step keepS keepL (writeBitL bit) .candidateCopyLeft
      | none => step keepS keepR keepR .candidateEraseRight
  | .candidateEraseRight => fun _ r1 _ =>
      match r1 with
      | some _ => step keepS eraseR keepR .candidateEraseRight
      | none => step keepS keepS keepL .candidateRewindLeft
  | .candidateRewindLeft => fun _ _ r2 =>
      match r2 with
      | some _ => step keepS keepS keepL .candidateRewindLeft
      | none => step keepS keepS keepR .halt
  | .halt => fun _ _ _ => none

def states : List State :=
  [.checkerSeek, .checkerScanLeft, .checkerEraseRight,
    .candidateSeek, .candidateCopyLeft, .candidateEraseRight,
    .candidateRewindLeft, .halt]

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
  TypedStateTable.ofList states .checkerSeek .halt next
    (by simp [states]) (by simp [states])
    (by intros; rfl) next_target_mem

def D := table.description

@[simp] theorem table_states : table.states = states := rfl

@[simp] theorem table_next : table.next = next := rfl

@[simp] theorem table_next_apply
    (s : State) (r0 r1 r2 : Option Bool) :
    table.next s r0 r1 r2 = next s r0 r1 r2 := rfl

theorem replicate_succ_eq_append (n : Nat) (a : Option Bool) :
    List.replicate (n + 1) a = List.append (List.replicate n a) [a] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        a :: List.replicate (n + 1) a =
          a :: (List.replicate n a ++ [a])
      exact congrArg (List.cons a) ih

def checkerScanTape (bits : List Bool)
    (right : List (Option Bool)) : Tape Bool :=
  match bits with
  | [] => tapeAtCells [] (none :: right)
  | bit :: rest =>
      tapeAtCells (List.append (rest.map some) [none])
        (some bit :: right)

theorem leads_checkerSeek
    (bits : List Bool) (right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .checkerSeek
        (tapeAtCells (List.append (bits.map some) [none])
          (none :: right)) T1 T2)
      (table.config .checkerScanLeft
        (checkerScanTape bits (none :: right)) T1 T2) := by
  apply TypedStateTable.leads_step table
    (by change State.checkerSeek ∈ states; simp [states])
    (st := ⟨State.checkerScanLeft, keepL, keepS, keepS⟩)
  · rw [table_next_apply]
    simp [next, step]
  · cases bits <;> rfl
  · rfl
  · rfl

theorem leads_checkerScanLeft
    (bits : List Bool) (right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .checkerScanLeft (checkerScanTape bits right) T1 T2)
      (table.config .checkerEraseRight
        (tapeAtCells [none]
          (List.append (bits.reverse.map some) right)) T1 T2) := by
  induction bits generalizing right with
  | nil =>
      apply TypedStateTable.leads_step table
        (by change State.checkerScanLeft ∈ states; simp [states])
        (st := ⟨State.checkerEraseRight, keepR, keepS, keepS⟩)
      · rw [table_next_apply]
        simp [checkerScanTape, next, step, tapeAtCells, Tape.read]
      · cases right <;> rfl
      · rfl
      · rfl
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (d := table.config .checkerScanLeft
          (checkerScanTape rest (some bit :: right)) T1 T2)
      · apply TypedStateTable.leads_step table
          (by change State.checkerScanLeft ∈ states; simp [states])
          (st := ⟨State.checkerScanLeft, keepL, keepS, keepS⟩)
        · rw [table_next_apply]
          simp [checkerScanTape, next, step, tapeAtCells, Tape.read]
        · cases rest <;> rfl
        · rfl
        · rfl
      · simpa [List.map_reverse, List.append_assoc] using
          ih (some bit :: right)

theorem leads_checkerEraseRight
    (bits : List Bool) (left right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .checkerEraseRight
        (tapeAtCells left
          (List.append (bits.map some) (none :: right))) T1 T2)
      (table.config .candidateSeek
        (tapeAtCells
          (List.append (List.replicate bits.length none) left)
          (none :: right)) T1 T2) := by
  induction bits generalizing left with
  | nil =>
      apply TypedStateTable.leads_step table
        (by change State.checkerEraseRight ∈ states; simp [states])
        (st := ⟨State.candidateSeek, keepS, keepS, keepS⟩)
      · rw [table_next_apply]
        simp [next, step, tapeAtCells, Tape.read]
      · rfl
      · rfl
      · rfl
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (d := table.config .checkerEraseRight
          (tapeAtCells (none :: left)
            (List.append (rest.map some) (none :: right))) T1 T2)
      · apply TypedStateTable.leads_step table
          (by change State.checkerEraseRight ∈ states; simp [states])
          (st := ⟨State.checkerEraseRight, eraseR, keepS, keepS⟩)
        · rw [table_next_apply]
          simp [next, step, tapeAtCells, Tape.read]
        · cases rest <;> rfl
        · rfl
        · rfl
      · simp only [List.length_cons]
        rw [replicate_succ_eq_append]
        simpa [List.append_assoc] using ih (none :: left)

theorem leads_clean_checkerScratch
    (raw : Word Bool) (fuel : Nat) (T1 T2 : Tape Bool) :
    table.Leads
      (table.config .checkerSeek
        (rawEmissionFinalScratch raw fuel) T1 T2)
      (table.config .candidateSeek
        (tapeAtCells
          (List.replicate (raw.length + 1) none)
          (none :: List.append ((stageNatBits fuel).map some) [none]))
        T1 T2) := by
  apply TypedStateTable.Leads.trans
    (leads_checkerSeek raw.reverse
      (List.append ((stageNatBits fuel).map some) [none]) T1 T2)
  apply TypedStateTable.Leads.trans
    (leads_checkerScanLeft raw.reverse
      (none :: List.append ((stageNatBits fuel).map some) [none]) T1 T2)
  have h :=
    leads_checkerEraseRight raw [none]
      (List.append ((stageNatBits fuel).map some) [none]) T1 T2
  rw [replicate_succ_eq_append]
  simpa [rawEmissionFinalScratch, List.map_reverse,
    List.append_assoc] using h

theorem leads_candidateSeek
    (bits : List Bool) (right : List (Option Bool))
    (T0 : Tape Bool) :
    table.Leads
      (table.config .candidateSeek T0
        (tapeAtCells (List.append (bits.map some) [none])
          (none :: right)) Tape.blank)
      (table.config .candidateCopyLeft T0
        (checkerScanTape bits (none :: right)) Tape.blank) := by
  apply TypedStateTable.leads_step table
    (by change State.candidateSeek ∈ states; simp [states])
    (st := ⟨State.candidateCopyLeft, keepS, keepL, keepS⟩)
  · rw [table_next_apply]
    simp [next, step]
  · rfl
  · cases bits <;> rfl
  · rfl

theorem leads_candidateCopyLeft
    (bits : List Bool) (right out : List (Option Bool))
    (T0 : Tape Bool) :
    table.Leads
      (table.config .candidateCopyLeft T0
        (checkerScanTape bits right)
        (tapeAtCells [] (none :: out)))
      (table.config .candidateEraseRight T0
        (tapeAtCells [none]
          (List.append (bits.reverse.map some) right))
        (tapeAtCells [none]
          (List.append (bits.reverse.map some) out))) := by
  induction bits generalizing right out with
  | nil =>
      apply TypedStateTable.leads_step table
        (by change State.candidateCopyLeft ∈ states; simp [states])
        (st := ⟨State.candidateEraseRight, keepS, keepR, keepR⟩)
      · rw [table_next_apply]
        simp [checkerScanTape, next, step, tapeAtCells, Tape.read]
      · rfl
      · cases right <;> rfl
      · cases out <;> rfl
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (d := table.config .candidateCopyLeft T0
          (checkerScanTape rest (some bit :: right))
          (tapeAtCells [] (none :: some bit :: out)))
      · apply TypedStateTable.leads_step table
          (by change State.candidateCopyLeft ∈ states; simp [states])
          (st := ⟨State.candidateCopyLeft, keepS, keepL,
            writeBitL bit⟩)
        · rw [table_next_apply]
          simp [checkerScanTape, next, step, tapeAtCells, Tape.read]
        · rfl
        · cases rest <;> rfl
        · rfl
      · simpa [List.map_reverse, List.append_assoc] using
          ih (some bit :: right) (some bit :: out)

theorem leads_candidateEraseRight_bits
    (bits : List Bool)
    (left1 left2 right out : List (Option Bool))
    (T0 : Tape Bool) :
    table.Leads
      (table.config .candidateEraseRight T0
        (tapeAtCells left1
          (List.append (bits.map some) (none :: right)))
        (tapeAtCells left2
          (List.append (bits.map some) out)))
      (table.config .candidateEraseRight T0
        (tapeAtCells
          (List.append (List.replicate bits.length none) left1)
          (none :: right))
        (tapeAtCells
          (List.append (bits.reverse.map some) left2) out)) := by
  induction bits generalizing left1 left2 with
  | nil =>
      exact TypedStateTable.Leads.refl table _
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (d := table.config .candidateEraseRight T0
          (tapeAtCells (none :: left1)
            (List.append (rest.map some) (none :: right)))
          (tapeAtCells (some bit :: left2)
            (List.append (rest.map some) out)))
      · apply TypedStateTable.leads_step table
          (by change State.candidateEraseRight ∈ states; simp [states])
          (st := ⟨State.candidateEraseRight, keepS, eraseR, keepR⟩)
        · rw [table_next_apply]
          simp [next, step, tapeAtCells, Tape.read]
        · rfl
        · cases rest <;> rfl
        · cases rest <;> cases out <;> rfl
      · simp only [List.length_cons]
        rw [replicate_succ_eq_append]
        simpa [List.map_reverse, List.append_assoc] using
          ih (none :: left1) (some bit :: left2)

theorem leads_candidateEraseTurn
    (scanBits : List Bool) (left right : List (Option Bool))
    (T0 : Tape Bool) :
    table.Leads
      (table.config .candidateEraseRight T0
        (tapeAtCells left (none :: right))
        (tapeAtCells
          (List.append (scanBits.map some) [none]) []))
      (table.config .candidateRewindLeft T0
        (tapeAtCells left (none :: right))
        (checkerScanTape scanBits [none])) := by
  apply TypedStateTable.leads_step table
    (by change State.candidateEraseRight ∈ states; simp [states])
    (st := ⟨State.candidateRewindLeft, keepS, keepS, keepL⟩)
  · rw [table_next_apply]
    simp [next, step, tapeAtCells, Tape.read]
  · rfl
  · rfl
  · cases scanBits <;> rfl

theorem leads_candidateRewindLeft
    (bits : List Bool) (right : List (Option Bool))
    (T0 T1 : Tape Bool) :
    table.Leads
      (table.config .candidateRewindLeft T0 T1
        (checkerScanTape bits right))
      (table.config .halt T0 T1
        (tapeAtCells [none]
          (List.append (bits.reverse.map some) right))) := by
  induction bits generalizing right with
  | nil =>
      apply TypedStateTable.leads_step table
        (by change State.candidateRewindLeft ∈ states; simp [states])
        (st := ⟨State.halt, keepS, keepS, keepR⟩)
      · rw [table_next_apply]
        simp [checkerScanTape, next, step, tapeAtCells, Tape.read]
      · rfl
      · rfl
      · cases right <;> rfl
  | cons bit rest ih =>
      apply TypedStateTable.Leads.trans
        (d := table.config .candidateRewindLeft T0 T1
          (checkerScanTape rest (some bit :: right)))
      · apply TypedStateTable.leads_step table
          (by change State.candidateRewindLeft ∈ states; simp [states])
          (st := ⟨State.candidateRewindLeft, keepS, keepS, keepL⟩)
        · rw [table_next_apply]
          simp [checkerScanTape, next, step, tapeAtCells, Tape.read]
        · rfl
        · rfl
        · cases rest <;> rfl
      · simpa [List.map_reverse, List.append_assoc] using
          ih (some bit :: right)

def cleanedFuelTape (raw : Word Bool) (fuel : Nat) : Tape Bool :=
  tapeAtCells
    (List.replicate (raw.length + 1) none)
    (none :: List.append ((stageNatBits fuel).map some) [none])

def restagedRawTape (raw : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append (raw.map some) [none])

theorem leads_restages
    (checkerRaw candidateRaw : Word Bool)
    (checkerFuel sourceFuel : Nat) :
    table.Leads
      (table.config .checkerSeek
        (rawEmissionFinalScratch checkerRaw checkerFuel)
        (rawEmissionFinalScratch candidateRaw sourceFuel)
        Tape.blank)
      (table.config .halt
        (cleanedFuelTape checkerRaw checkerFuel)
        (cleanedFuelTape candidateRaw sourceFuel)
        (restagedRawTape candidateRaw)) := by
  apply TypedStateTable.Leads.trans
    (leads_clean_checkerScratch checkerRaw checkerFuel
      (rawEmissionFinalScratch candidateRaw sourceFuel) Tape.blank)
  apply TypedStateTable.Leads.trans
    (leads_candidateSeek candidateRaw.reverse
      (List.append ((stageNatBits sourceFuel).map some) [none])
      (cleanedFuelTape checkerRaw checkerFuel))
  apply TypedStateTable.Leads.trans
    (leads_candidateCopyLeft candidateRaw.reverse
      (none :: List.append ((stageNatBits sourceFuel).map some) [none]) []
      (cleanedFuelTape checkerRaw checkerFuel))
  apply TypedStateTable.Leads.trans
    (by
      simpa using
        (leads_candidateEraseRight_bits candidateRaw [none] [none]
          (List.append ((stageNatBits sourceFuel).map some) [none]) []
          (cleanedFuelTape checkerRaw checkerFuel)))
  apply TypedStateTable.Leads.trans
    (by
      simpa [List.map_reverse] using
        (leads_candidateEraseTurn candidateRaw.reverse
          (List.append (List.replicate candidateRaw.length none) [none])
          (List.append ((stageNatBits sourceFuel).map some) [none])
          (cleanedFuelTape checkerRaw checkerFuel)))
  rw [show
      cleanedFuelTape candidateRaw sourceFuel =
        tapeAtCells
          (List.append (List.replicate candidateRaw.length none) [none])
          (none :: List.append ((stageNatBits sourceFuel).map some) [none]) by
    unfold cleanedFuelTape
    rw [replicate_succ_eq_append]]
  have hrewind := leads_candidateRewindLeft candidateRaw.reverse [none]
    (cleanedFuelTape checkerRaw checkerFuel)
    (tapeAtCells
      (List.append (List.replicate candidateRaw.length none) [none])
      (none :: List.append ((stageNatBits sourceFuel).map some) [none]))
  simpa [restagedRawTape, List.map_reverse,
    List.append_assoc] using hrewind

theorem cleanedFuelTape_equiv
    (raw : Word Bool) (fuel : Nat) :
    Tape.Equiv (cleanedFuelTape raw fuel) (cursorFuelSourceTape fuel) := by
  simp [cleanedFuelTape, cursorFuelSourceTape, tapeAtCells, Tape.Equiv,
    Tape.dropTrailingNone,
    FoC.Computability.dropTrailingNone_replicate_none,
    FoC.Computability.dropTrailingNone_append_none]

theorem restagedRawTape_equiv_input (raw : Word Bool) :
    Tape.Equiv (restagedRawTape raw) (Tape.input raw) := by
  cases raw <;>
    simp [restagedRawTape, tapeAtCells, Tape.input, Tape.blank, Tape.Equiv,
      Tape.dropTrailingNone,
      FoC.Computability.dropTrailingNone_append_none]

end PersistentRestaging
end BoundedFuelPairSearch
end Computability
end FoC
