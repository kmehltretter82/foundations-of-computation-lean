import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorCore.Runs.Prefix

set_option doc.verso true

/-!
# Fuel-simulator emission and replay runs

Reverse-order output emission, fuel and stage replay, and the exact final
logical three-tape execution.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets
namespace FuelSimulatorCore

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

def tickStream : Nat -> Word Bool
  | 0 => []
  | n + 1 => List.append [false, true, false, false] (tickStream n)

theorem tickStream_append_tick (n : Nat) :
    List.append (tickStream n) [false, true, false, false] =
      List.append [false, true, false, false] (tickStream n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        List.append [false, true, false, false]
            (List.append (tickStream n) [false, true, false, false]) =
          List.append [false, true, false, false]
            (List.append [false, true, false, false] (tickStream n))
      exact congrArg (List.append [false, true, false, false]) ih

theorem stageNatBits_reverse (n : Nat) :
    (stageNatBits n).reverse =
      List.append [true, true, false, false] (tickStream n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [stageNatBits_succ, tickStream, ih, List.append_assoc]
      exact tickStream_append_tick n

theorem leads_tailDone (start : Nat) (head : Bool) (hold : Hold)
    (T0 T1 : Tape Bool) (emitted : Word Bool)
    (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.tailDone0 head hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.tailCountStart head (some false)) T0 T1
        (delayedLeftEmissionTape
          (List.append emitted [true, true, false, false]))) := by
  exact leads_emit4
    (start := start)
    (s0 := State.tailDone0 head hold)
    (s1 := State.tailDone1 head (some true))
    (s2 := State.tailDone2 head (some true))
    (s3 := State.tailDone3 head (some false))
    (s4 := State.tailCountStart head (some false))
    (hold := hold) (b0 := true) (b1 := true)
    (b2 := false) (b3 := false) (lastAction := keepS) (T1' := T1)
    (mem_states_emission (h := hold)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some true)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some true)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some false)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 rfl emitted hhold

theorem leads_tailTick (start : Nat) (head : Bool) (hold : Hold)
    (T0 T1 : Tape Bool) {T1' : Tape Bool}
    (hmove : keepR.apply T1 = T1')
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.tailTick0 head hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.tailCountLoop head (some false)) T0 T1'
        (delayedLeftEmissionTape
          (List.append emitted [false, true, false, false]))) := by
  exact leads_emit4
    (start := start)
    (s0 := State.tailTick0 head hold)
    (s1 := State.tailTick1 head (some false))
    (s2 := State.tailTick2 head (some true))
    (s3 := State.tailTick3 head (some false))
    (s4 := State.tailCountLoop head (some false))
    (hold := hold) (b0 := false) (b1 := true)
    (b2 := false) (b3 := false) (lastAction := keepR) (T1' := T1')
    (mem_states_emission (h := hold)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some false)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some true)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some false)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 hmove emitted hhold

theorem leads_tailCountLoop (start : Nat) (head : Bool)
    (bits : Word Bool) (hold : Hold)
    (left visited : List (Option Bool)) (T0 : Tape Bool)
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.tailCountLoop head hold) T0
        (tapeAtCells left
          (List.append (bits.map some) (none :: visited)))
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.headCell0 head
          ((List.append emitted (tickStream bits.length)).getLast?))
        T0
        (tapeAtCells
          (List.append (bits.reverse.map some) left) (none :: visited))
        (delayedLeftEmissionTape
          (List.append emitted (tickStream bits.length)))) := by
  induction bits generalizing hold left emitted with
  | nil =>
      have hstep :=
        leads_step
          (start := start) (s := State.tailCountLoop head hold)
          (T0 := T0) (T1 := tapeAtCells left (none :: visited))
          (T2 := delayedLeftEmissionTape emitted)
          (st := ⟨State.headCell0 head hold, keepS, keepS, keepS⟩)
          (T0' := T0) (T1' := tapeAtCells left (none :: visited))
          (T2' := delayedLeftEmissionTape emitted)
          (mem_states_emission (h := hold)
            (by cases head <;> simp [emissionBlock, boolValues]))
          (by rw [delayedLeftEmissionTape_read]; rfl) rfl rfl rfl
      simpa [tickStream, hhold] using hstep
  | cons bit rest ih =>
      let T1 :=
        tapeAtCells left
          (some bit :: List.append (rest.map some) (none :: visited))
      have henter :=
        leads_step
          (start := start) (s := State.tailCountLoop head hold)
          (T0 := T0) (T1 := T1) (T2 := delayedLeftEmissionTape emitted)
          (st := ⟨State.tailTick0 head hold, keepS, keepS, keepS⟩)
          (T0' := T0) (T1' := T1)
          (T2' := delayedLeftEmissionTape emitted)
          (mem_states_emission (h := hold)
            (by cases head <;> simp [emissionBlock, boolValues]))
          (by rw [delayedLeftEmissionTape_read]; rfl) rfl rfl rfl
      have hmove :
          keepR.apply T1 =
            tapeAtCells (some bit :: left)
              (List.append (rest.map some) (none :: visited)) := by
        exact keepR_apply_tapeAtCells left (some bit) _
      have hemit :=
        leads_tailTick start head hold T0 T1 hmove emitted hhold
      have hrec :=
        ih (some false) (some bit :: left)
          (List.append emitted [false, true, false, false]) (by simp)
      exact Leads.trans (by simpa [T1] using henter)
        (Leads.trans hemit (by
          simpa [tickStream, List.map_append, List.append_assoc] using hrec))

theorem leads_tailCount (start : Nat) (head : Bool) (tail : Word Bool)
    (hold : Hold) (visited : List (Option Bool)) (T0 : Tape Bool)
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.tailCountStart head hold) T0
        (tapeAtCells []
          (none :: some head ::
            List.append (tail.map some) (none :: visited)))
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.headCell0 head
          ((List.append emitted (tickStream tail.length)).getLast?))
        T0
        (tapeAtCells
          (List.append ((head :: tail).reverse.map some) [none])
          (none :: visited))
        (delayedLeftEmissionTape
          (List.append emitted (tickStream tail.length)))) := by
  have hstart :=
    leads_scratchR
      (start := start) (s := State.tailCountStart head hold)
      (target := State.tailCountSkip head hold) (current := none)
      (mem_states_emission (h := hold)
        (by cases head <;> simp [emissionBlock, boolValues]))
      (by intros; rfl) T0 []
      (some head :: List.append (tail.map some) (none :: visited))
      (delayedLeftEmissionTape emitted)
  have hskip :=
    leads_scratchR
      (start := start) (s := State.tailCountSkip head hold)
      (target := State.tailCountLoop head hold) (current := some head)
      (mem_states_emission (h := hold)
        (by cases head <;> simp [emissionBlock, boolValues]))
      (by intros; rfl) T0 [none]
      (List.append (tail.map some) (none :: visited))
      (delayedLeftEmissionTape emitted)
  have hloop :=
    leads_tailCountLoop start head tail hold [some head, none] visited T0
      emitted hhold
  exact Leads.trans hstart (Leads.trans hskip (by
    simpa [List.map_append, List.append_assoc] using hloop))

theorem leads_headCell (start : Nat) (head : Bool) (hold : Hold)
    (T0 T1 : Tape Bool) (emitted : Word Bool)
    (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.headCell0 head hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.emptyDone0 (some false)) T0 T1
        (delayedLeftEmissionTape
          (List.append emitted [!head, head, true, false]))) := by
  exact leads_emit4
    (start := start)
    (s0 := State.headCell0 head hold)
    (s1 := State.headCell1 head (some (!head)))
    (s2 := State.headCell2 head (some head))
    (s3 := State.headCell3 head (some true))
    (s4 := State.emptyDone0 (some false))
    (hold := hold) (b0 := !head) (b1 := head)
    (b2 := true) (b3 := false) (lastAction := keepS) (T1' := T1)
    (mem_states_emission (h := hold)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some (!head))
      (by cases head <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some head)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some true)
      (by cases head <;> simp [emissionBlock, boolValues]))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 rfl emitted hhold

theorem leads_emptyDone (start : Nat) (hold : Hold)
    (T0 T1 : Tape Bool) (emitted : Word Bool)
    (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.emptyDone0 hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.startDone0 (some false)) T0 T1
        (delayedLeftEmissionTape
          (List.append emitted [true, true, false, false]))) := by
  exact leads_emit4
    (start := start)
    (s0 := State.emptyDone0 hold)
    (s1 := State.emptyDone1 (some true))
    (s2 := State.emptyDone2 (some true))
    (s3 := State.emptyDone3 (some false))
    (s4 := State.startDone0 (some false))
    (hold := hold) (b0 := true) (b1 := true)
    (b2 := false) (b3 := false) (lastAction := keepS) (T1' := T1)
    (mem_states_emission (h := hold) (by simp [emissionBlock]))
    (mem_states_emission (h := some true) (by simp [emissionBlock]))
    (mem_states_emission (h := some true) (by simp [emissionBlock]))
    (mem_states_emission (h := some false) (by simp [emissionBlock]))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 rfl emitted hhold

theorem leads_startDone (start : Nat) (hold : Hold)
    (T0 T1 : Tape Bool) (emitted : Word Bool)
    (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.startDone0 hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.startLoop start (some false)) T0 T1
        (delayedLeftEmissionTape
          (List.append emitted [true, true, false, false]))) := by
  exact leads_emit4
    (start := start)
    (s0 := State.startDone0 hold)
    (s1 := State.startDone1 (some true))
    (s2 := State.startDone2 (some true))
    (s3 := State.startDone3 (some false))
    (s4 := State.startLoop start (some false))
    (hold := hold) (b0 := true) (b1 := true)
    (b2 := false) (b3 := false) (lastAction := keepS) (T1' := T1)
    (mem_states_emission (h := hold) (by simp [emissionBlock]))
    (mem_states_emission (h := some true) (by simp [emissionBlock]))
    (mem_states_emission (h := some true) (by simp [emissionBlock]))
    (mem_states_emission (h := some false) (by simp [emissionBlock]))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 rfl emitted hhold

theorem mem_startAt {start j : Nat} {hold : Hold} {s : State}
    (hj : j ≤ start)
    (hs : s ∈ [State.startLoop j hold, State.startTick0 j hold,
      State.startTick1 j hold, State.startTick2 j hold,
      State.startTick3 j hold]) : s ∈ states start := by
  apply mem_states_start
  apply List.mem_flatMap.mpr
  exact ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hj), hs⟩

theorem leads_startTick (start j : Nat) (hj : j ≤ start) (hold : Hold)
    (T0 T1 : Tape Bool) (emitted : Word Bool)
    (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.startTick0 j hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.startLoop j (some false)) T0 T1
        (delayedLeftEmissionTape
          (List.append emitted [false, true, false, false]))) := by
  exact leads_emit4
    (start := start)
    (s0 := State.startTick0 j hold)
    (s1 := State.startTick1 j (some false))
    (s2 := State.startTick2 j (some true))
    (s3 := State.startTick3 j (some false))
    (s4 := State.startLoop j (some false))
    (hold := hold) (b0 := false) (b1 := true)
    (b2 := false) (b3 := false) (lastAction := keepS) (T1' := T1)
    (mem_startAt (hold := hold) hj (by simp))
    (mem_startAt (hold := some false) hj (by simp))
    (mem_startAt (hold := some true) hj (by simp))
    (mem_startAt (hold := some false) hj (by simp))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 rfl emitted hhold

theorem leads_startLoop (start remaining : Nat) (hrem : remaining ≤ start)
    (hold : Hold) (T0 T1 : Tape Bool) (emitted : Word Bool)
    (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.startLoop remaining hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.fuelSeekStart
          ((List.append emitted (tickStream remaining)).getLast?))
        T0 T1
        (delayedLeftEmissionTape
          (List.append emitted (tickStream remaining)))) := by
  induction remaining generalizing hold emitted with
  | zero =>
      have hstep :=
        leads_step
          (start := start) (s := State.startLoop 0 hold)
          (T0 := T0) (T1 := T1) (T2 := delayedLeftEmissionTape emitted)
          (st := ⟨State.fuelSeekStart hold, keepS, keepS, keepS⟩)
          (T0' := T0) (T1' := T1) (T2' := delayedLeftEmissionTape emitted)
          (mem_startAt (hold := hold) (Nat.zero_le start) (by simp))
          (by rw [delayedLeftEmissionTape_read]; rfl) rfl rfl rfl
      simpa [tickStream, hhold] using hstep
  | succ j ih =>
      have hj : j ≤ start := Nat.le_trans (Nat.le_succ j) hrem
      have henter :=
        leads_step
          (start := start) (s := State.startLoop (j + 1) hold)
          (T0 := T0) (T1 := T1) (T2 := delayedLeftEmissionTape emitted)
          (st := ⟨State.startTick0 j hold, keepS, keepS, keepS⟩)
          (T0' := T0) (T1' := T1) (T2' := delayedLeftEmissionTape emitted)
          (mem_startAt (hold := hold) hrem (by simp))
          (by rw [delayedLeftEmissionTape_read]; rfl) rfl rfl rfl
      have htick := leads_startTick start j hj hold T0 T1 emitted hhold
      have hrec :=
        ih hj (some false)
          (List.append emitted [false, true, false, false]) (by simp)
      exact Leads.trans henter (Leads.trans htick (by
        simpa [tickStream, List.append_assoc] using hrec))

/-!
## Fuel replay
-/

theorem leads_fuelSeekEndScan (start : Nat) (hold : Hold)
    (bits : Word Bool) (left : List (Option Bool))
    (T0 T2 : Tape Bool) :
    Leads start
      (coreCfg start (.fuelSeekEnd hold) T0
        (tapeAtCells left (List.append (bits.map some) [none])) T2)
      (coreCfg start (.fuelSeekEnd hold) T0
        (tapeAtCells (List.append (bits.reverse.map some) left) [none]) T2) := by
  induction bits generalizing left with
  | nil => exact Leads.refl start _
  | cons bit rest ih =>
      have hstep :=
        leads_scratchR
          (start := start) (s := State.fuelSeekEnd hold)
          (target := State.fuelSeekEnd hold) (current := some bit)
          (mem_states_emission (h := hold) (by simp [emissionBlock]))
          (by intros; rfl) T0 left
          (List.append (rest.map some) [none]) T2
      exact Leads.trans hstep (by
        simpa [List.map_append, List.append_assoc] using
          (ih (some bit :: left)))

/-- Scratch shape while replaying fuel after the tail/start fields have been
emitted.  {name}`stageBase` retains the separator and any cells to the left of the
stage field. -/
def fuelReplayTape (fuelRev : Word Bool) (stageLast : Bool)
    (stageRest : Word Bool) (stageBase visited : List (Option Bool)) :
    Tape Bool :=
  match fuelRev with
  | [] =>
      tapeAtCells
        (List.append (some stageLast :: stageRest.map some) stageBase)
        (none :: visited)
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some)
          (none ::
            List.append (some stageLast :: stageRest.map some) stageBase))
        (some bit :: visited)

theorem leads_fuelEmitRev (start : Nat) (hold : Hold)
    (fuelRev : Word Bool) (stageLast : Bool) (stageRest : Word Bool)
    (stageBase visited : List (Option Bool)) (T0 : Tape Bool)
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.fuelEmit hold) T0
        (fuelReplayTape fuelRev stageLast stageRest stageBase visited)
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.xCellLoop
          ((List.append emitted fuelRev).getLast?))
        T0
        (tapeAtCells (List.append (stageRest.map some) stageBase)
          (some stageLast :: none ::
            List.append (fuelRev.reverse.map some) visited))
        (delayedLeftEmissionTape (List.append emitted fuelRev))) := by
  induction fuelRev generalizing hold visited emitted with
  | nil =>
      have hstep :=
        leads_scratchL
          (start := start) (s := State.fuelEmit hold)
          (target := State.xCellLoop hold) (current := none)
          (mem_states_emission (h := hold) (by simp [emissionBlock]))
          (by intros; rfl) T0
          (List.append (stageRest.map some) stageBase) (some stageLast)
          visited (delayedLeftEmissionTape emitted)
      simpa [fuelReplayTape, List.append_assoc, hhold] using hstep
  | cons bit rest ih =>
      have hmove :
          keepL.apply
              (fuelReplayTape (bit :: rest) stageLast stageRest stageBase visited) =
            fuelReplayTape rest stageLast stageRest stageBase
              (some bit :: visited) := by
        cases rest <;> rfl
      have hemit :=
        leads_emit
          (start := start) (s := State.fuelEmit hold)
          (target := State.fuelEmit (some bit))
          (hold := hold) (bit := bit) (action1 := keepL)
          (T1' := fuelReplayTape rest stageLast stageRest stageBase
            (some bit :: visited))
          (mem_states_emission (h := hold) (by simp [emissionBlock]))
          T0
          (fuelReplayTape (bit :: rest) stageLast stageRest stageBase visited)
          (by rfl)
          hmove emitted hhold
      have hrec :=
        ih (some bit) (some bit :: visited) (List.append emitted [bit])
          (by simp)
      exact Leads.trans hemit (by
        simpa [List.map_append, List.append_assoc] using hrec)

/-!
## Full input-word replay
-/

def xCellTape (bitsRev : Word Bool)
    (visited : List (Option Bool)) : Tape Bool :=
  match bitsRev with
  | [] => tapeAtCells [] (none :: visited)
  | bit :: rest =>
      tapeAtCells (List.append (rest.map some) [none])
        (some bit :: visited)

def cellStream : Word Bool -> Word Bool
  | [] => []
  | bit :: rest =>
      List.append [!bit, bit, true, false] (cellStream rest)

theorem cellsBits_append (left right : Word Bool) :
    cellsBits (Word.Concat left right) =
      Word.Concat (cellsBits left) (cellsBits right) := by
  induction left with
  | nil => rfl
  | cons bit rest ih =>
      have hfirst := cellsBits_cons bit (Word.Concat rest right)
      have hprefix := cellsBits_cons bit rest
      calc
        cellsBits (Word.Concat (bit :: rest) right) =
            Word.Concat (cellBits bit)
              (cellsBits (Word.Concat rest right)) := hfirst
        _ = Word.Concat (cellBits bit)
              (Word.Concat (cellsBits rest) (cellsBits right)) :=
          congrArg (Word.Concat (cellBits bit)) ih
        _ = Word.Concat
              (Word.Concat (cellBits bit) (cellsBits rest))
              (cellsBits right) :=
          (Word.concat_assoc _ _ _).symm
        _ = Word.Concat (cellsBits (bit :: rest)) (cellsBits right) :=
          congrArg (fun xs => Word.Concat xs (cellsBits right)) hprefix.symm

theorem cellStream_eq_cellsBits_reverse (bits : List Bool) :
    cellStream bits = (cellsBits bits.reverse).reverse := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      rw [cellStream, List.reverse_cons]
      calc
        Word.Concat [!bit, bit, true, false] (cellStream rest) =
            Word.Concat [!bit, bit, true, false]
              (cellsBits rest.reverse).reverse :=
          congrArg (Word.Concat [!bit, bit, true, false]) ih
        _ = (Word.Concat (cellsBits rest.reverse) (cellsBits [bit])).reverse := by
          cases bit with
          | false =>
              simp [Word.Concat, cellsBits, encodeCellsAppend,
                encodeCellAppend, encodeCell, encodeCodeWordAsInput,
                encodeCodeSymbolAsInput]
          | true =>
              simp [Word.Concat, cellsBits, encodeCellsAppend,
                encodeCellAppend, encodeCell, encodeCodeWordAsInput,
                encodeCodeSymbolAsInput]
        _ = (cellsBits (Word.Concat rest.reverse [bit])).reverse :=
          congrArg List.reverse (cellsBits_append rest.reverse [bit]).symm

theorem tailStream_eq_cellStream_dropLast
    (pending : Bool) (remaining : Word Bool) :
    tailStream pending remaining =
      cellStream (pending :: remaining).dropLast := by
  induction remaining generalizing pending with
  | nil => rfl
  | cons nextBit rest ih =>
      simp [tailStream, cellStream, ih]

theorem tailHead_getLast?
    (pending : Bool) (remaining : Word Bool) :
    (pending :: remaining).getLast? =
      some (tailHead pending remaining) := by
  induction remaining generalizing pending with
  | nil => rfl
  | cons nextBit rest ih =>
      simpa [tailHead] using ih nextBit

theorem tailHead_eq_of_reverse_eq
    {pending head : Bool} {remaining tail : Word Bool}
    (hreverse : (pending :: remaining).reverse = head :: tail) :
    tailHead pending remaining = head := by
  have hscan : pending :: remaining = (head :: tail).reverse := by
    rw [← hreverse, List.reverse_reverse]
  have hlast := tailHead_getLast? pending remaining
  rw [hscan] at hlast
  simpa using hlast.symm

theorem tailStream_eq_of_reverse_eq
    {pending head : Bool} {remaining tail : Word Bool}
    (hreverse : (pending :: remaining).reverse = head :: tail) :
    tailStream pending remaining = (cellsBits tail).reverse := by
  rw [tailStream_eq_cellStream_dropLast]
  have hscan : pending :: remaining = (head :: tail).reverse := by
    rw [← hreverse, List.reverse_reverse]
  rw [hscan]
  have hdrop : ((head :: tail).reverse).dropLast = tail.reverse := by
    simp
  rw [hdrop, cellStream_eq_cellsBits_reverse, List.reverse_reverse]

/-- Complete reverse-order stream accumulated by the delayed emitter. -/
def outputEmission (attempt : MachineDescription)
    (i : FuelSimulatorStructuredIndex) (head : Bool) (tail : Word Bool) :
    Word Bool :=
  List.append (cellBits false).reverse
    (List.append (cellsBits tail).reverse
      (List.append (stageNatBits tail.length).reverse
        (List.append (cellBits head).reverse
          (List.append (stageNatBits 0).reverse
            (List.append (stageNatBits attempt.start).reverse
              (List.append (stageNatBits i.fuel).reverse
                (List.append (cellsBits (head :: tail)).reverse
                  (List.append (stageNatBits (head :: tail).length).reverse
                    [false, false, false, false]))))))))

theorem outputEmission_reverse
    (attempt : MachineDescription) (i : FuelSimulatorStructuredIndex)
    (head : Bool) (tail : Word Bool)
    (hx : stageBits i = head :: tail) :
    (outputEmission attempt i head tail).reverse =
      encodeCodeWordAsInput
        (SimulatorLayout.encode
          (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorLayout
            attempt i.w i.limit i.fuel)) := by
  rw [outputBits_decomp attempt i head tail hx]
  simp [outputEmission, List.reverse_append, List.append_assoc]

theorem leads_xCellBlock (start : Nat) (bit : Bool) (hold : Hold)
    (T0 T1 : Tape Bool) {T1' : Tape Bool}
    (hmove : keepL.apply T1 = T1')
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.xCell0 bit hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.xCellLoop (some false)) T0 T1'
        (delayedLeftEmissionTape
          (List.append emitted [!bit, bit, true, false]))) := by
  exact leads_emit4
    (start := start)
    (s0 := State.xCell0 bit hold)
    (s1 := State.xCell1 bit (some (!bit)))
    (s2 := State.xCell2 bit (some bit))
    (s3 := State.xCell3 bit (some true))
    (s4 := State.xCellLoop (some false))
    (hold := hold) (b0 := !bit) (b1 := bit)
    (b2 := true) (b3 := false) (lastAction := keepL) (T1' := T1')
    (mem_states_emission (h := hold)
      (by cases bit <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some (!bit))
      (by cases bit <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some bit)
      (by cases bit <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some true)
      (by cases bit <;> simp [emissionBlock, boolValues]))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 hmove emitted hhold

theorem leads_xCells (start : Nat) (bitsRev : Word Bool) (hold : Hold)
    (visited : List (Option Bool)) (T0 : Tape Bool)
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.xCellLoop hold) T0 (xCellTape bitsRev visited)
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.xDone0
          ((List.append emitted (cellStream bitsRev)).getLast?))
        T0
        (tapeAtCells []
          (none :: List.append (bitsRev.reverse.map some) visited))
        (delayedLeftEmissionTape
          (List.append emitted (cellStream bitsRev)))) := by
  induction bitsRev generalizing hold visited emitted with
  | nil =>
      have hstep :=
        leads_step
          (start := start) (s := State.xCellLoop hold)
          (T0 := T0) (T1 := xCellTape [] visited)
          (T2 := delayedLeftEmissionTape emitted)
          (st := ⟨State.xDone0 hold, keepS, keepS, keepS⟩)
          (T0' := T0) (T1' := xCellTape [] visited)
          (T2' := delayedLeftEmissionTape emitted)
          (mem_states_emission (h := hold) (by simp [emissionBlock]))
          (by rw [delayedLeftEmissionTape_read]; rfl) rfl rfl rfl
      simpa [xCellTape, cellStream, hhold] using hstep
  | cons bit rest ih =>
      have henter :=
        leads_step
          (start := start) (s := State.xCellLoop hold)
          (T0 := T0) (T1 := xCellTape (bit :: rest) visited)
          (T2 := delayedLeftEmissionTape emitted)
          (st := ⟨State.xCell0 bit hold, keepS, keepS, keepS⟩)
          (T0' := T0) (T1' := xCellTape (bit :: rest) visited)
          (T2' := delayedLeftEmissionTape emitted)
          (mem_states_emission (h := hold) (by simp [emissionBlock]))
          (by rw [delayedLeftEmissionTape_read]; rfl) rfl rfl rfl
      have hmove :
          keepL.apply (xCellTape (bit :: rest) visited) =
            xCellTape rest (some bit :: visited) := by
        cases rest <;> rfl
      have hemit :=
        leads_xCellBlock start bit hold T0 (xCellTape (bit :: rest) visited)
          hmove emitted hhold
      have hrec :=
        ih (some false) (some bit :: visited)
          (List.append emitted [!bit, bit, true, false]) (by simp)
      exact Leads.trans henter (Leads.trans hemit (by
        simpa [cellStream, List.map_append, List.append_assoc] using hrec))

theorem leads_xDone (start : Nat) (hold : Hold)
    (T0 T1 : Tape Bool) (emitted : Word Bool)
    (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.xDone0 hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.xCountStart (some false)) T0 T1
        (delayedLeftEmissionTape
          (List.append emitted [true, true, false, false]))) := by
  exact leads_emit4
    (start := start)
    (s0 := State.xDone0 hold) (s1 := State.xDone1 (some true))
    (s2 := State.xDone2 (some true)) (s3 := State.xDone3 (some false))
    (s4 := State.xCountStart (some false))
    (hold := hold) (b0 := true) (b1 := true)
    (b2 := false) (b3 := false) (lastAction := keepS) (T1' := T1)
    (mem_states_emission (h := hold) (by simp [emissionBlock]))
    (mem_states_emission (h := some true) (by simp [emissionBlock]))
    (mem_states_emission (h := some true) (by simp [emissionBlock]))
    (mem_states_emission (h := some false) (by simp [emissionBlock]))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 rfl emitted hhold

theorem leads_xTick (start : Nat) (hold : Hold)
    (T0 T1 : Tape Bool) {T1' : Tape Bool}
    (hmove : keepR.apply T1 = T1')
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.xTick0 hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.xCountLoop (some false)) T0 T1'
        (delayedLeftEmissionTape
          (List.append emitted [false, true, false, false]))) := by
  exact leads_emit4
    (start := start)
    (s0 := State.xTick0 hold) (s1 := State.xTick1 (some false))
    (s2 := State.xTick2 (some true)) (s3 := State.xTick3 (some false))
    (s4 := State.xCountLoop (some false))
    (hold := hold) (b0 := false) (b1 := true)
    (b2 := false) (b3 := false) (lastAction := keepR) (T1' := T1')
    (mem_states_emission (h := hold) (by simp [emissionBlock]))
    (mem_states_emission (h := some false) (by simp [emissionBlock]))
    (mem_states_emission (h := some true) (by simp [emissionBlock]))
    (mem_states_emission (h := some false) (by simp [emissionBlock]))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 hmove emitted hhold

theorem leads_xCountLoop (start : Nat) (bits : Word Bool) (hold : Hold)
    (left visited : List (Option Bool)) (T0 : Tape Bool)
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.xCountLoop hold) T0
        (tapeAtCells left (List.append (bits.map some) (none :: visited)))
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.header0
          ((List.append emitted (tickStream bits.length)).getLast?))
        T0
        (tapeAtCells (List.append (bits.reverse.map some) left)
          (none :: visited))
        (delayedLeftEmissionTape
          (List.append emitted (tickStream bits.length)))) := by
  induction bits generalizing hold left emitted with
  | nil =>
      have hstep :=
        leads_step
          (start := start) (s := State.xCountLoop hold)
          (T0 := T0) (T1 := tapeAtCells left (none :: visited))
          (T2 := delayedLeftEmissionTape emitted)
          (st := ⟨State.header0 hold, keepS, keepS, keepS⟩)
          (T0' := T0) (T1' := tapeAtCells left (none :: visited))
          (T2' := delayedLeftEmissionTape emitted)
          (mem_states_emission (h := hold) (by simp [emissionBlock]))
          (by rw [delayedLeftEmissionTape_read]; rfl) rfl rfl rfl
      simpa [tickStream, hhold] using hstep
  | cons bit rest ih =>
      let T1 := tapeAtCells left
        (some bit :: List.append (rest.map some) (none :: visited))
      have henter :=
        leads_step
          (start := start) (s := State.xCountLoop hold)
          (T0 := T0) (T1 := T1) (T2 := delayedLeftEmissionTape emitted)
          (st := ⟨State.xTick0 hold, keepS, keepS, keepS⟩)
          (T0' := T0) (T1' := T1) (T2' := delayedLeftEmissionTape emitted)
          (mem_states_emission (h := hold) (by simp [emissionBlock]))
          (by rw [delayedLeftEmissionTape_read]; rfl) rfl rfl rfl
      have hmove : keepR.apply T1 =
          tapeAtCells (some bit :: left)
            (List.append (rest.map some) (none :: visited)) := by
        exact keepR_apply_tapeAtCells left (some bit) _
      have hemit := leads_xTick start hold T0 T1 hmove emitted hhold
      have hrec := ih (some false) (some bit :: left)
        (List.append emitted [false, true, false, false]) (by simp)
      exact Leads.trans (by simpa [T1] using henter)
        (Leads.trans hemit (by
          simpa [tickStream, List.map_append, List.append_assoc] using hrec))

theorem leads_xCount (start : Nat) (bits : Word Bool) (hold : Hold)
    (visited : List (Option Bool)) (T0 : Tape Bool)
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.xCountStart hold) T0
        (tapeAtCells []
          (none :: List.append (bits.map some) (none :: visited)))
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.header0
          ((List.append emitted (tickStream bits.length)).getLast?))
        T0
        (tapeAtCells (List.append (bits.reverse.map some) [none])
          (none :: visited))
        (delayedLeftEmissionTape
          (List.append emitted (tickStream bits.length)))) := by
  have hstart :=
    leads_scratchR
      (start := start) (s := State.xCountStart hold)
      (target := State.xCountLoop hold) (current := none)
      (mem_states_emission (h := hold) (by simp [emissionBlock]))
      (by intros; rfl) T0 []
      (List.append (bits.map some) (none :: visited))
      (delayedLeftEmissionTape emitted)
  have hloop :=
    leads_xCountLoop start bits hold [none] visited T0 emitted hhold
  exact Leads.trans hstart hloop

theorem leads_header (start : Nat) (hold : Hold)
    (T0 T1 : Tape Bool) (emitted : Word Bool)
    (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.header0 hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.flush (some false)) T0 T1
        (delayedLeftEmissionTape
          (List.append emitted [false, false, false, false]))) := by
  apply leads_emit4 (start := start)
    (s1 := State.header1 (some false)) (s2 := State.header2 (some false))
    (s3 := State.header3 (some false)) (lastAction := keepS) (T1' := T1)
    (hs0 := mem_states_emission (h := hold) (by simp [emissionBlock]))
    (hs1 := mem_states_emission (h := some false) (by simp [emissionBlock]))
    (hs2 := mem_states_emission (h := some false) (by simp [emissionBlock]))
    (hs3 := mem_states_emission (h := some false) (by simp [emissionBlock]))
  all_goals first
    | exact hhold
    | unfold EmitRow <;> intros <;> rfl
    | rfl

theorem leads_finish (start : Nat) (hold : Hold)
    (T0 T1 : Tape Bool) (emitted : Word Bool)
    (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.flush hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start .halt T0 T1
        (Tape.move Direction.right (Tape.input emitted.reverse))) := by
  have hflush :=
    leads_step
      (start := start) (s := State.flush hold)
      (T0 := T0) (T1 := T1) (T2 := delayedLeftEmissionTape emitted)
      (st := ⟨State.position, keepS, keepS, flushAction hold⟩)
      (T0' := T0) (T1' := T1) (T2' := Tape.input emitted.reverse)
      (mem_states_emission (h := hold) (by simp [emissionBlock]))
      (by rw [delayedLeftEmissionTape_read]; rfl) rfl rfl
      (by
        change
          (delayedLeftFlushAction hold).apply
              (delayedLeftEmissionTape emitted) = Tape.input emitted.reverse
        exact delayedLeftFlushAction_apply hhold)
  have hposition :=
    leads_step
      (start := start) (s := State.position)
      (T0 := T0) (T1 := T1) (T2 := Tape.input emitted.reverse)
      (st := ⟨State.halt, keepS, keepS, keepR⟩)
      (T0' := T0) (T1' := T1)
      (T2' := Tape.move Direction.right (Tape.input emitted.reverse))
      (mem_states_fixed (by decide)) (by rfl) rfl rfl rfl
  exact Leads.trans hflush hposition

/-- Concrete scratch representative left by the completed structured run. -/
def finalScratchTape (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  tapeAtCells
    (List.append ((stageBits i).reverse.map some) [none])
    (none :: List.append ((fuelBits i).map some) [none])

/-- Full exact logical three-tape run of the fuel-simulator core. -/
theorem leads_halt (attempt : MachineDescription)
    (i : FuelSimulatorStructuredIndex) :
    Leads attempt.start
      (coreCfg attempt.start .len0
        (Tape.input (fuelSimulatorInputBits i)) Tape.blank Tape.blank)
      (coreCfg attempt.start .halt
        (sourceAfterCopy i) (finalScratchTape i)
        (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
          attempt i.w i.limit i.fuel)) := by
  obtain ⟨head, tail, hx⟩ := stageBits_cons i
  cases hstageRev : (stageBits i).reverse with
  | nil =>
      have : stageBits i = [] := by
        rw [← List.reverse_reverse (stageBits i), hstageRev]
        rfl
      simp [hx] at this
  | cons stageLast stageRest =>
      have hreverse : (stageLast :: stageRest).reverse = head :: tail := by
        rw [← hstageRev, List.reverse_reverse, hx]
      have hscan : (head :: tail).reverse = stageLast :: stageRest := by
        rw [← hreverse, List.reverse_reverse]
      have hhead := tailHead_eq_of_reverse_eq hreverse
      have htail := tailStream_eq_of_reverse_eq hreverse
      refine Leads.trans (leads_inputCopy attempt.start i) ?_
      refine Leads.trans
        (leads_outFalse attempt.start (sourceAfterCopy i)
          (scratchAfterCopy i)) ?_
      have hseek :=
        leads_seekFuel attempt.start (some false) (fuelBits i).reverse
          stageLast stageRest (sourceAfterCopy i)
          (delayedLeftEmissionTape [true, false, true, false])
      refine Leads.trans (by
        simpa [scratchAfterCopy, hstageRev, List.append_assoc] using hseek) ?_
      have htailRun :=
        leads_tailTakeRun attempt.start stageLast stageRest (some false)
          (none :: List.append ((fuelBits i).map some) [none])
          (sourceAfterCopy i) [true, false, true, false] rfl
      refine Leads.trans (by
        simpa [hreverse, hhead, htail, List.append_assoc] using htailRun) ?_
      let eTail : Word Bool :=
        List.append [true, false, true, false] (cellsBits tail).reverse
      have htailDone :=
        leads_tailDone attempt.start head eTail.getLast?
          (sourceAfterCopy i)
          (tapeAtCells []
            (none :: some head ::
              List.append (tail.map some)
                (none :: List.append ((fuelBits i).map some) [none])))
          eTail rfl
      refine Leads.trans htailDone ?_
      have htailCount :=
        leads_tailCount attempt.start head tail (some false)
          (List.append ((fuelBits i).map some) [none])
          (sourceAfterCopy i)
          (List.append eTail [true, true, false, false]) (by simp)
      refine Leads.trans htailCount ?_
      let middleScratch : Tape Bool :=
        tapeAtCells
          (List.append ((head :: tail).reverse.map some) [none])
          (none :: List.append ((fuelBits i).map some) [none])
      let eTailLen : Word Bool :=
        List.append (List.append eTail [true, true, false, false])
          (tickStream tail.length)
      have hheadCell :=
        leads_headCell attempt.start head eTailLen.getLast?
          (sourceAfterCopy i) middleScratch eTailLen rfl
      refine Leads.trans hheadCell ?_
      let eHead : Word Bool :=
        List.append eTailLen [!head, head, true, false]
      have hemptyDone :=
        leads_emptyDone attempt.start (some false)
          (sourceAfterCopy i) middleScratch eHead (by simp [eHead])
      refine Leads.trans hemptyDone ?_
      let eEmpty : Word Bool :=
        List.append eHead [true, true, false, false]
      have hstartDone :=
        leads_startDone attempt.start (some false)
          (sourceAfterCopy i) middleScratch eEmpty (by simp [eEmpty])
      refine Leads.trans hstartDone ?_
      let eStartDone : Word Bool :=
        List.append eEmpty [true, true, false, false]
      have hstartLoop :=
        leads_startLoop attempt.start attempt.start (Nat.le_refl _)
          (some false) (sourceAfterCopy i) middleScratch eStartDone
          (by simp [eStartDone])
      refine Leads.trans hstartLoop ?_
      let eStart : Word Bool :=
        List.append eStartDone (tickStream attempt.start)
      have htoFuelEnd :=
        leads_scratchR
          (start := attempt.start)
          (s := State.fuelSeekStart eStart.getLast?)
          (target := State.fuelSeekEnd eStart.getLast?) (current := none)
          (mem_states_emission (h := eStart.getLast?)
            (by simp [emissionBlock]))
          (by intros; rfl) (sourceAfterCopy i)
          (List.append ((head :: tail).reverse.map some) [none])
          (List.append ((fuelBits i).map some) [none])
          (delayedLeftEmissionTape eStart)
      refine Leads.trans htoFuelEnd ?_
      have hfuelScan :=
        leads_fuelSeekEndScan attempt.start eStart.getLast?
          (fuelBits i)
          (none :: List.append ((head :: tail).reverse.map some) [none])
          (sourceAfterCopy i) (delayedLeftEmissionTape eStart)
      refine Leads.trans hfuelScan ?_
      have hfuelNe : fuelBits i ≠ [] := by
        obtain ⟨rest, hrest⟩ := stageNatBits_false_false_tail i.fuel
        change stageNatBits i.fuel ≠ []
        rw [hrest]
        simp
      cases hfuelRev : (fuelBits i).reverse with
      | nil =>
          exfalso
          apply hfuelNe
          rw [← List.reverse_reverse (fuelBits i), hfuelRev]
          rfl
      | cons fuelLast fuelRest =>
          have htoFuelEmit :=
            leads_scratchL
              (start := attempt.start)
              (s := State.fuelSeekEnd eStart.getLast?)
              (target := State.fuelEmit eStart.getLast?) (current := none)
              (mem_states_emission (h := eStart.getLast?)
                (by simp [emissionBlock]))
              (by intros; rfl) (sourceAfterCopy i)
              (List.append (fuelRest.map some)
                (none ::
                  List.append ((stageLast :: stageRest).map some) [none]))
              (some fuelLast) [] (delayedLeftEmissionTape eStart)
          refine Leads.trans (by
            simpa [hfuelRev, hscan, List.append_assoc] using htoFuelEmit) ?_
          have hfuelEmit :=
            leads_fuelEmitRev attempt.start eStart.getLast?
              (fuelLast :: fuelRest) stageLast stageRest [none] [none]
              (sourceAfterCopy i) eStart rfl
          refine Leads.trans (by
            simpa [fuelReplayTape, hscan, hfuelRev,
              List.append_assoc] using hfuelEmit) ?_
          have hfuel : fuelBits i = (fuelLast :: fuelRest).reverse := by
            rw [← hfuelRev, List.reverse_reverse]
          let eFuel : Word Bool :=
            List.append eStart (fuelLast :: fuelRest)
          have hxCells :=
            leads_xCells attempt.start (stageLast :: stageRest)
              eFuel.getLast?
              (none :: List.append ((fuelBits i).map some) [none])
              (sourceAfterCopy i) eFuel rfl
          have hcell :=
            cellStream_eq_cellsBits_reverse (stageLast :: stageRest)
          let eCells : Word Bool :=
            List.append eFuel (cellStream (stageLast :: stageRest))
          let afterCellsScratch : Tape Bool :=
            tapeAtCells []
              (none ::
                List.append ((stageLast :: stageRest).reverse.map some)
                  (none :: List.append ((fuelBits i).map some) [none]))
          refine Leads.trans
            (d := coreCfg attempt.start (.xDone0 eCells.getLast?)
              (sourceAfterCopy i) afterCellsScratch
              (delayedLeftEmissionTape eCells))
            (by
              simpa [xCellTape, eFuel, eCells, afterCellsScratch, hfuel,
                List.append_assoc] using hxCells) ?_
          have hxDone :=
            leads_xDone attempt.start eCells.getLast?
              (sourceAfterCopy i) afterCellsScratch eCells rfl
          refine Leads.trans hxDone ?_
          let eXDone : Word Bool :=
            List.append eCells [true, true, false, false]
          have hxCount :=
            leads_xCount attempt.start (stageLast :: stageRest).reverse
              (some false)
              (List.append ((fuelBits i).map some) [none])
              (sourceAfterCopy i) eXDone (by simp [eXDone])
          let eLength : Word Bool :=
            List.append eXDone
              (tickStream (stageLast :: stageRest).reverse.length)
          let afterCountScratch : Tape Bool :=
            tapeAtCells
              (List.append ((stageLast :: stageRest).map some) [none])
              (none :: List.append ((fuelBits i).map some) [none])
          refine Leads.trans
            (d := coreCfg attempt.start (.header0 eLength.getLast?)
              (sourceAfterCopy i) afterCountScratch
              (delayedLeftEmissionTape eLength))
            (by
              simpa [afterCellsScratch, eXDone, eLength,
                afterCountScratch, List.append_assoc] using hxCount) ?_
          have hheader :=
            leads_header attempt.start eLength.getLast?
              (sourceAfterCopy i) afterCountScratch eLength rfl
          refine Leads.trans hheader ?_
          let eAll : Word Bool :=
            List.append eLength [false, false, false, false]
          have heTail : eTail =
              List.append (cellBits false).reverse
                (cellsBits tail).reverse := by
            rfl
          have heTailLen : eTailLen =
              List.append eTail (stageNatBits tail.length).reverse := by
            rw [stageNatBits_reverse]
            simp [eTailLen, List.append_assoc]
          have heHead : eHead =
              List.append eTailLen (cellBits head).reverse := by
            cases head <;> rfl
          have heEmpty : eEmpty =
              List.append eHead (stageNatBits 0).reverse := by
            rfl
          have heStart : eStart =
              List.append eEmpty (stageNatBits attempt.start).reverse := by
            rw [stageNatBits_reverse]
            simp [eStart, eStartDone, List.append_assoc]
          have hfuelStream : fuelLast :: fuelRest =
              (stageNatBits i.fuel).reverse := by
            rw [← hfuelRev]
            rfl
          have heFuel : eFuel =
              List.append eStart (stageNatBits i.fuel).reverse := by
            simp [eFuel, hfuelStream]
          have heCells : eCells =
              List.append eFuel (cellsBits (head :: tail)).reverse := by
            simp [eCells, hcell, hreverse]
          have heLength : eLength =
              List.append eCells
                (stageNatBits (head :: tail).length).reverse := by
            rw [stageNatBits_reverse]
            simp [eLength, eXDone, hreverse, List.append_assoc]
          have hemission : eAll = outputEmission attempt i head tail := by
            rw [show eAll =
                List.append eLength [false, false, false, false] from rfl,
              heLength, heCells, heFuel, heStart, heEmpty, heHead,
              heTailLen, heTail]
            simp [outputEmission, List.append_assoc]
          have hfinish :=
            leads_finish attempt.start (some false)
              (sourceAfterCopy i) afterCountScratch eAll (by simp [eAll])
          have hscratch : afterCountScratch = finalScratchTape i := by
            simp [afterCountScratch, finalScratchTape, hstageRev]
          have hout :
              Tape.move Direction.right (Tape.input eAll.reverse) =
                PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
                  attempt i.w i.limit i.fuel := by
            unfold PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
            rw [hemission, outputEmission_reverse attempt i head tail hx]
          simpa only [hscratch, hout] using hfinish

end FuelSimulatorCore
end StructuredConstructionTargets

end Computability
end FoC
