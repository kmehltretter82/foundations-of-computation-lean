import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorCore.Machine
import FoC.Computability.Compiler.Structured.Lowering.TypedStateRuns

set_option doc.verso true

/-!
# Fuel-simulator structured-core runs

Forward execution of the typed table. The proofs use shared typed-table
reachability and delayed-emitter algebra; phase lemmas expose only logical tape
windows and never unfold the generated concrete transition list.
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

/-- Compiled structured description for an attempt start state. -/
def coreD (start : Nat) :
    CommonGround.FiniteTransducers.Structured.Description :=
  (table start).description

/-- A typed logical configuration of the core. -/
def coreCfg (start : Nat) (s : State)
    (T0 T1 T2 : Tape Bool) :
    CommonGround.FiniteTransducers.Structured.Configuration :=
  (table start).config s T0 T1 T2

/-- Step-count-free reachability through the typed table. -/
def Leads (start : Nat)
    (c d : CommonGround.FiniteTransducers.Structured.Configuration) : Prop :=
  (table start).Leads c d

namespace Leads

theorem refl (start : Nat)
    (c : CommonGround.FiniteTransducers.Structured.Configuration) :
    Leads start c c :=
  TypedStateTable.Leads.refl (table start) c

theorem trans {start : Nat}
    {c d e : CommonGround.FiniteTransducers.Structured.Configuration}
    (hcd : Leads start c d) (hde : Leads start d e) : Leads start c e :=
  TypedStateTable.Leads.trans hcd hde

theorem to_runConfig {start : Nat}
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (h : Leads start c d) :
    exists steps : Nat, (coreD start).runConfig steps c = d :=
  TypedStateTable.Leads.to_runConfig h

end Leads

/-- Execute one typed transition with explicit logical tape results. -/
theorem leads_step {start : Nat} {s : State} (hs : s ∈ states start)
    {T0 T1 T2 : Tape Bool} {st : TypedStep State}
    (hnext :
      next start s (Tape.read T0) (Tape.read T1) (Tape.read T2) = some st)
    {T0' T1' T2' : Tape Bool}
    (h0 : st.action0.apply T0 = T0')
    (h1 : st.action1.apply T1 = T1')
    (h2 : st.action2.apply T2 = T2') :
    Leads start (coreCfg start s T0 T1 T2)
      (coreCfg start st.target T0' T1' T2') := by
  have hnext' :
      (table start).next s (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some st := by
    change next start s (Tape.read T0) (Tape.read T1) (Tape.read T2) =
      some st
    exact hnext
  simpa [Leads, coreCfg] using
    (TypedStateTable.leads_step (table start) hs hnext' h0 h1 h2)

/-- Copy one source bit rightward onto the blank scratch frontier. -/
theorem leads_copyBit {start : Nat} {s target : State} {bit : Bool}
    (hs : s ∈ states start)
    (hnext : forall r2 : Option Bool,
      next start s (some bit) none r2 =
        some ⟨target, keepR, writeBitR bit, keepS⟩)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start s
        (tapeAtCells sourceLeft (some bit :: sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start target
        (tapeAtCells (some bit :: sourceLeft) sourceRight)
        (tapeAtCells (some bit :: scratchLeft) []) T2) := by
  refine leads_step
    (T0 := tapeAtCells sourceLeft (some bit :: sourceRight))
    (T1 := tapeAtCells scratchLeft []) (T2 := T2)
    (st := ⟨target, keepR, writeBitR bit, keepS⟩)
    hs (hnext (Tape.read T2)) ?_ ?_ ?_
  · exact keepR_apply_tapeAtCells sourceLeft (some bit) sourceRight
  · change
      (writeR (some bit)).apply (tapeAtCells scratchLeft [none]) =
        tapeAtCells (some bit :: scratchLeft) []
    exact writeR_apply_tapeAtCells (some bit) scratchLeft none []
  · rfl

/-- A table row that copies one known bit onto the scratch frontier. -/
def CopyRow (start : Nat) (source : State) (bit : Bool)
    (target : State) : Prop :=
  forall r2 : Option Bool,
    next start source (some bit) none r2 =
      some ⟨target, keepR, writeBitR bit, keepS⟩

/-- Compose four copy rows, the width of every code-symbol encoding. -/
theorem leads_copy4 {start : Nat}
    {s0 s1 s2 s3 s4 : State} {b0 b1 b2 b3 : Bool}
    (hs0 : s0 ∈ states start) (hs1 : s1 ∈ states start)
    (hs2 : s2 ∈ states start) (hs3 : s3 ∈ states start)
    (h0 : CopyRow start s0 b0 s1) (h1 : CopyRow start s1 b1 s2)
    (h2 : CopyRow start s2 b2 s3) (h3 : CopyRow start s3 b3 s4)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start s0
        (tapeAtCells sourceLeft
          (some b0 :: some b1 :: some b2 :: some b3 :: sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start s4
        (tapeAtCells
          (some b3 :: some b2 :: some b1 :: some b0 :: sourceLeft)
          sourceRight)
        (tapeAtCells
          (some b3 :: some b2 :: some b1 :: some b0 :: scratchLeft) [])
        T2) := by
  refine Leads.trans
    (leads_copyBit hs0 h0 sourceLeft
      (some b1 :: some b2 :: some b3 :: sourceRight) scratchLeft T2) ?_
  refine Leads.trans
    (leads_copyBit hs1 h1 (some b0 :: sourceLeft)
      (some b2 :: some b3 :: sourceRight) (some b0 :: scratchLeft) T2) ?_
  refine Leads.trans
    (leads_copyBit hs2 h2 (some b1 :: some b0 :: sourceLeft)
      (some b3 :: sourceRight) (some b1 :: some b0 :: scratchLeft) T2) ?_
  exact leads_copyBit hs3 h3
    (some b2 :: some b1 :: some b0 :: sourceLeft) sourceRight
    (some b2 :: some b1 :: some b0 :: scratchLeft) T2

/-!
## Source-prefix copy
-/

theorem leads_lenTick (start : Nat)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .len0
        (tapeAtCells sourceLeft
          (some false :: some false :: some true :: some false :: sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .len0
        (tapeAtCells
          (some false :: some true :: some false :: some false :: sourceLeft)
          sourceRight)
        (tapeAtCells
          (some false :: some true :: some false :: some false :: scratchLeft)
          []) T2) :=
  leads_copy4
    (s0 := .len0) (s1 := .len1) (s2 := .len2) (s3 := .len3)
    (s4 := .len0) (b0 := false) (b1 := false) (b2 := true)
    (b3 := false)
    (mem_states_fixed (by simp [fixedStates]))
    (mem_states_fixed (by simp [fixedStates]))
    (mem_states_fixed (by simp [fixedStates]))
    (mem_states_fixed (by simp [fixedStates]))
    (by intro; rfl) (by intro; rfl) (by intro; rfl) (by intro; rfl)
    sourceLeft sourceRight scratchLeft T2

theorem leads_lenDone (start : Nat)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .len0
        (tapeAtCells sourceLeft
          (some false :: some false :: some true :: some true :: sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .cells0
        (tapeAtCells
          (some true :: some true :: some false :: some false :: sourceLeft)
          sourceRight)
        (tapeAtCells
          (some true :: some true :: some false :: some false :: scratchLeft)
          []) T2) :=
  leads_copy4
    (s0 := .len0) (s1 := .len1) (s2 := .len2) (s3 := .len3)
    (s4 := .cells0) (b0 := false) (b1 := false) (b2 := true)
    (b3 := true)
    (mem_states_fixed (by simp [fixedStates]))
    (mem_states_fixed (by simp [fixedStates]))
    (mem_states_fixed (by simp [fixedStates]))
    (mem_states_fixed (by simp [fixedStates]))
    (by intro; rfl) (by intro; rfl) (by intro; rfl) (by intro; rfl)
    sourceLeft sourceRight scratchLeft T2

theorem leads_cell (start : Nat) (bit : Bool)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .cells0
        (tapeAtCells sourceLeft
          (some false :: some true :: some bit :: some (!bit) :: sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .cells0
        (tapeAtCells
          (some (!bit) :: some bit :: some true :: some false :: sourceLeft)
          sourceRight)
        (tapeAtCells
          (some (!bit) :: some bit :: some true :: some false :: scratchLeft)
          []) T2) :=
  leads_copy4
    (s0 := .cells0) (s1 := .cells1) (s2 := .cells2)
    (s3 := .cells3 bit) (s4 := .cells0)
    (b0 := false) (b1 := true) (b2 := bit) (b3 := !bit)
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (mem_states_fixed (by cases bit <;> decide))
    (by intro; rfl) (by intro; rfl) (by intro; rfl)
    (by intro; cases bit <;> rfl)
    sourceLeft sourceRight scratchLeft T2

theorem leads_firstLimitTick (start : Nat)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .cells0
        (tapeAtCells sourceLeft
          (some false :: some false :: some true :: some false :: sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .limit0
        (tapeAtCells
          (some false :: some true :: some false :: some false :: sourceLeft)
          sourceRight)
        (tapeAtCells
          (some false :: some true :: some false :: some false :: scratchLeft)
          []) T2) :=
  leads_copy4
    (s0 := .cells0) (s1 := .cells1) (s2 := .limit2)
    (s3 := .limit3) (s4 := .limit0)
    (b0 := false) (b1 := false) (b2 := true) (b3 := false)
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (by intro; rfl) (by intro; rfl) (by intro; rfl) (by intro; rfl)
    sourceLeft sourceRight scratchLeft T2

theorem leads_firstLimitDone (start : Nat)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .cells0
        (tapeAtCells sourceLeft
          (some false :: some false :: some true :: some true :: sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .gap
        (tapeAtCells
          (some true :: some true :: some false :: some false :: sourceLeft)
          sourceRight)
        (tapeAtCells
          (some true :: some true :: some false :: some false :: scratchLeft)
          []) T2) :=
  leads_copy4
    (s0 := .cells0) (s1 := .cells1) (s2 := .limit2)
    (s3 := .limit3) (s4 := .gap)
    (b0 := false) (b1 := false) (b2 := true) (b3 := true)
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (by intro; rfl) (by intro; rfl) (by intro; rfl) (by intro; rfl)
    sourceLeft sourceRight scratchLeft T2

theorem leads_limitTick (start : Nat)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .limit0
        (tapeAtCells sourceLeft
          (some false :: some false :: some true :: some false :: sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .limit0
        (tapeAtCells
          (some false :: some true :: some false :: some false :: sourceLeft)
          sourceRight)
        (tapeAtCells
          (some false :: some true :: some false :: some false :: scratchLeft)
          []) T2) :=
  leads_copy4
    (s0 := .limit0) (s1 := .limit1) (s2 := .limit2)
    (s3 := .limit3) (s4 := .limit0)
    (b0 := false) (b1 := false) (b2 := true) (b3 := false)
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (by intro; rfl) (by intro; rfl) (by intro; rfl) (by intro; rfl)
    sourceLeft sourceRight scratchLeft T2

theorem leads_limitDone (start : Nat)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .limit0
        (tapeAtCells sourceLeft
          (some false :: some false :: some true :: some true :: sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .gap
        (tapeAtCells
          (some true :: some true :: some false :: some false :: sourceLeft)
          sourceRight)
        (tapeAtCells
          (some true :: some true :: some false :: some false :: scratchLeft)
          []) T2) :=
  leads_copy4
    (s0 := .limit0) (s1 := .limit1) (s2 := .limit2)
    (s3 := .limit3) (s4 := .gap)
    (b0 := false) (b1 := false) (b2 := true) (b3 := true)
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (mem_states_fixed (by decide))
    (by intro; rfl) (by intro; rfl) (by intro; rfl) (by intro; rfl)
    sourceLeft sourceRight scratchLeft T2

theorem leads_lenNat (start n : Nat)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .len0
        (tapeAtCells sourceLeft
          (List.append ((stageNatBits n).map some) sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .cells0
        (tapeAtCells
          (List.append ((stageNatBits n).reverse.map some) sourceLeft)
          sourceRight)
        (tapeAtCells
          (List.append ((stageNatBits n).reverse.map some) scratchLeft) [])
        T2) := by
  induction n generalizing sourceLeft scratchLeft with
  | zero =>
      simpa using
        (leads_lenDone start sourceLeft sourceRight scratchLeft T2)
  | succ n ih =>
      refine Leads.trans
        (by
          simpa [List.append_assoc] using
            (leads_lenTick start sourceLeft
              (List.append ((stageNatBits n).map some) sourceRight)
              scratchLeft T2)) ?_
      simpa [List.append_assoc] using
        (ih
          (some false :: some true :: some false :: some false :: sourceLeft)
          (some false :: some true :: some false :: some false :: scratchLeft))

theorem leads_cells (start : Nat) (bits : Word Bool)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .cells0
        (tapeAtCells sourceLeft
          (List.append ((cellsBits bits).map some) sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .cells0
        (tapeAtCells
          (List.append ((cellsBits bits).reverse.map some) sourceLeft)
          sourceRight)
        (tapeAtCells
          (List.append ((cellsBits bits).reverse.map some) scratchLeft) [])
        T2) := by
  induction bits generalizing sourceLeft scratchLeft with
  | nil => exact Leads.refl start _
  | cons bit rest ih =>
      cases bit with
      | false =>
          refine Leads.trans
            (by
              simpa [cellBits, encodeCodeSymbolAsInput,
                List.map_append, List.append_assoc] using
                (leads_cell start false sourceLeft
                  (List.append ((cellsBits rest).map some) sourceRight)
                  scratchLeft T2)) ?_
          simpa [cellBits, encodeCodeSymbolAsInput,
            List.map_append, List.append_assoc] using
            (ih
              (some true :: some false :: some true :: some false :: sourceLeft)
              (some true :: some false :: some true :: some false :: scratchLeft))
      | true =>
          refine Leads.trans
            (by
              simpa [cellBits, encodeCodeSymbolAsInput,
                List.map_append, List.append_assoc] using
                (leads_cell start true sourceLeft
                  (List.append ((cellsBits rest).map some) sourceRight)
                  scratchLeft T2)) ?_
          simpa [cellBits, encodeCodeSymbolAsInput,
            List.map_append, List.append_assoc] using
            (ih
              (some false :: some true :: some true :: some false :: sourceLeft)
              (some false :: some true :: some true :: some false :: scratchLeft))

theorem leads_limitNat (start n : Nat)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .limit0
        (tapeAtCells sourceLeft
          (List.append ((stageNatBits n).map some) sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .gap
        (tapeAtCells
          (List.append ((stageNatBits n).reverse.map some) sourceLeft)
          sourceRight)
        (tapeAtCells
          (List.append ((stageNatBits n).reverse.map some) scratchLeft) [])
        T2) := by
  induction n generalizing sourceLeft scratchLeft with
  | zero =>
      simpa using
        (leads_limitDone start sourceLeft sourceRight scratchLeft T2)
  | succ n ih =>
      refine Leads.trans
        (by
          simpa [List.append_assoc] using
            (leads_limitTick start sourceLeft
              (List.append ((stageNatBits n).map some) sourceRight)
              scratchLeft T2)) ?_
      simpa [List.append_assoc] using
        (ih
          (some false :: some true :: some false :: some false :: sourceLeft)
          (some false :: some true :: some false :: some false :: scratchLeft))

theorem leads_firstLimitNat (start n : Nat)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .cells0
        (tapeAtCells sourceLeft
          (List.append ((stageNatBits n).map some) sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .gap
        (tapeAtCells
          (List.append ((stageNatBits n).reverse.map some) sourceLeft)
          sourceRight)
        (tapeAtCells
          (List.append ((stageNatBits n).reverse.map some) scratchLeft) [])
        T2) := by
  cases n with
  | zero =>
      simpa using
        (leads_firstLimitDone start sourceLeft sourceRight scratchLeft T2)
  | succ n =>
      refine Leads.trans
        (by
          simpa [List.append_assoc] using
            (leads_firstLimitTick start sourceLeft
              (List.append ((stageNatBits n).map some) sourceRight)
              scratchLeft T2)) ?_
      simpa [List.append_assoc] using
        (leads_limitNat start n
          (some false :: some true :: some false :: some false :: sourceLeft)
          sourceRight
          (some false :: some true :: some false :: some false :: scratchLeft)
          T2)

/-- Copy and parse the complete stage prefix, stopping before the fuel field. -/
theorem leads_stage (start : Nat) (i : FuelSimulatorStructuredIndex)
    (sourceLeft sourceRight scratchLeft : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start .len0
        (tapeAtCells sourceLeft
          (List.append ((stageBits i).map some) sourceRight))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start .gap
        (tapeAtCells
          (List.append ((stageBits i).reverse.map some) sourceLeft)
          sourceRight)
        (tapeAtCells
          (List.append ((stageBits i).reverse.map some) scratchLeft) [])
        T2) := by
  rw [stageBits_eq_length_cells_limit]
  refine Leads.trans
    (by
      simpa [List.map_append, List.append_assoc] using
        (leads_lenNat start i.w.length sourceLeft
          (List.append ((cellsBits i.w).map some)
            (List.append ((stageNatBits i.limit).map some) sourceRight))
          scratchLeft T2)) ?_
  refine Leads.trans
    (by
      simpa [List.map_append, List.append_assoc] using
        (leads_cells start i.w
          (List.append ((stageNatBits i.w.length).reverse.map some)
            sourceLeft)
          (List.append ((stageNatBits i.limit).map some) sourceRight)
          (List.append ((stageNatBits i.w.length).reverse.map some)
            scratchLeft)
          T2)) ?_
  simpa [List.map_append, List.append_assoc] using
    (leads_firstLimitNat start i.limit
      (List.append ((cellsBits i.w).reverse.map some)
        (List.append ((stageNatBits i.w.length).reverse.map some)
          sourceLeft))
      sourceRight
      (List.append ((cellsBits i.w).reverse.map some)
        (List.append ((stageNatBits i.w.length).reverse.map some)
          scratchLeft))
      T2)

theorem leads_gap (start : Nat) (T0 : Tape Bool)
    (scratchLeft : List (Option Bool)) (T2 : Tape Bool) :
    Leads start
      (coreCfg start .gap T0 (tapeAtCells scratchLeft []) T2)
      (coreCfg start .fuelCopy T0
        (tapeAtCells (none :: scratchLeft) []) T2) := by
  refine leads_step
    (start := start) (s := State.gap)
    (T0 := T0) (T1 := tapeAtCells scratchLeft []) (T2 := T2)
    (st := ⟨State.fuelCopy, keepS, keepR, keepS⟩)
    (T0' := T0) (T1' := tapeAtCells (none :: scratchLeft) [])
    (T2' := T2)
    (mem_states_fixed (by decide)) (by rfl) rfl ?_ rfl
  change keepR.apply (tapeAtCells scratchLeft [none]) =
    tapeAtCells (none :: scratchLeft) []
  exact keepR_apply_tapeAtCells scratchLeft none []

theorem leads_fuelCopy (start : Nat) (bits : Word Bool)
    (sourceLeft scratchLeft : List (Option Bool)) (T2 : Tape Bool) :
    Leads start
      (coreCfg start .fuelCopy
        (tapeAtCells sourceLeft (bits.map some))
        (tapeAtCells scratchLeft []) T2)
      (coreCfg start (.outFalse0 none)
        (tapeAtCells
          (List.append (bits.reverse.map some) sourceLeft) [])
        (tapeAtCells
          (List.append (bits.reverse.map some) scratchLeft) []) T2) := by
  induction bits generalizing sourceLeft scratchLeft with
  | nil =>
      simpa using
        (leads_step
          (start := start) (s := State.fuelCopy)
          (T0 := tapeAtCells sourceLeft [])
          (T1 := tapeAtCells scratchLeft []) (T2 := T2)
          (st := ⟨State.outFalse0 none, keepS, keepS, keepS⟩)
          (T0' := tapeAtCells sourceLeft [])
          (T1' := tapeAtCells scratchLeft []) (T2' := T2)
          (mem_states_fixed (by decide)) (by rfl) rfl rfl rfl)
  | cons bit rest ih =>
      refine Leads.trans
        (leads_copyBit (s := State.fuelCopy) (target := State.fuelCopy)
          (mem_states_fixed (by decide)) (by intro; rfl)
          sourceLeft (rest.map some) scratchLeft T2) ?_
      simpa [List.append_assoc] using
        (ih (some bit :: sourceLeft) (some bit :: scratchLeft))

theorem tapeAtCells_map_some_eq_input (bits : Word Bool) :
    tapeAtCells [] (bits.map some) = Tape.input bits := by
  cases bits <;> rfl

theorem tapeAtCells_single_blank_eq_nil
    (left : List (Option Bool)) :
    tapeAtCells left [none] = tapeAtCells left [] := rfl

private theorem map_some_append (left right : Word Bool) :
    (List.append left right).map some =
      List.append (left.map some) (right.map some) := by
  induction left with
  | nil => rfl
  | cons bit rest ih =>
      change some bit :: (List.append rest right).map some = _
      rw [ih]
      rfl

def sourceAfterCopy (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  tapeAtCells
    (List.append ((fuelBits i).reverse.map some)
      ((stageBits i).reverse.map some)) []

def scratchAfterCopy (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  tapeAtCells
    (List.append ((fuelBits i).reverse.map some)
      (none :: (stageBits i).reverse.map some)) []

theorem leads_inputCopy (start : Nat) (i : FuelSimulatorStructuredIndex) :
    Leads start
      (coreCfg start .len0
        (Tape.input (fuelSimulatorInputBits i)) Tape.blank Tape.blank)
      (coreCfg start (.outFalse0 none)
        (sourceAfterCopy i) (scratchAfterCopy i) Tape.blank) := by
  have hstage :=
    leads_stage start i [] ((fuelBits i).map some) [] Tape.blank
  have hgap :=
    leads_gap start
      (tapeAtCells ((stageBits i).reverse.map some)
        ((fuelBits i).map some))
      ((stageBits i).reverse.map some) Tape.blank
  have hfuel :=
    leads_fuelCopy start (fuelBits i)
      ((stageBits i).reverse.map some)
      (none :: (stageBits i).reverse.map some) Tape.blank
  have hrevNil :
      List.append ((stageBits i).reverse.map some) [] =
        (stageBits i).reverse.map some :=
    List.append_nil _
  rw [hrevNil,
    show tapeAtCells [] [] = Tape.blank from rfl] at hstage
  have h := Leads.trans hstage (Leads.trans hgap hfuel)
  have hinput :
      tapeAtCells []
          (List.append ((stageBits i).map some) ((fuelBits i).map some)) =
        Tape.input (fuelSimulatorInputBits i) := by
    rw [← map_some_append, ← inputBits_eq_stageBits_append_fuel]
    exact tapeAtCells_map_some_eq_input _
  rw [← hinput]
  simpa [sourceAfterCopy, scratchAfterCopy, List.append_assoc] using h

/-!
## Delayed output emission
-/

/-- One output event with an arbitrary scratch-tape action. -/
theorem leads_emit {start : Nat} {s target : State}
    {hold : Hold} {bit : Bool} {action1 : TapeAction}
    (hs : s ∈ states start)
    (T0 T1 : Tape Bool)
    (hnext : next start s (Tape.read T0) (Tape.read T1) none =
      some ⟨target, keepS, action1, emitAction hold⟩)
    {T1' : Tape Bool}
    (h1 : action1.apply T1 = T1')
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start s T0 T1 (delayedLeftEmissionTape emitted))
      (coreCfg start target T0 T1'
        (delayedLeftEmissionTape (List.append emitted [bit]))) := by
  refine leads_step
    (start := start) (s := s)
    (T0 := T0) (T1 := T1) (T2 := delayedLeftEmissionTape emitted)
    (st := ⟨target, keepS, action1, emitAction hold⟩)
    (T0' := T0) (T1' := T1')
    (T2' := delayedLeftEmissionTape (List.append emitted [bit]))
    hs ?_ rfl h1 ?_
  · rw [delayedLeftEmissionTape_read]
    exact hnext
  · change
      (delayedLeftEmitAction hold).apply
          (delayedLeftEmissionTape emitted) =
        delayedLeftEmissionTape (List.append emitted [bit])
    exact delayedLeftEmitAction_apply hhold bit

/-- A delayed-emitter row, stated independently of current tape reads. -/
def EmitRow (start : Nat) (source : State) (hold : Hold)
    (_bit : Bool) (action1 : TapeAction) (target : State) : Prop :=
  forall r0 r1 : Option Bool,
    next start source r0 r1 none =
      some ⟨target, keepS, action1, emitAction hold⟩

/-- Emit one four-bit code block; only its final row may move scratch. -/
theorem leads_emit4 {start : Nat}
    {s0 s1 s2 s3 s4 : State} {hold : Hold}
    {b0 b1 b2 b3 : Bool} {lastAction : TapeAction}
    (hs0 : s0 ∈ states start) (hs1 : s1 ∈ states start)
    (hs2 : s2 ∈ states start) (hs3 : s3 ∈ states start)
    (h0 : EmitRow start s0 hold b0 keepS s1)
    (h1 : EmitRow start s1 (some b0) b1 keepS s2)
    (h2 : EmitRow start s2 (some b1) b2 keepS s3)
    (h3 : EmitRow start s3 (some b2) b3 lastAction s4)
    (T0 T1 : Tape Bool) {T1' : Tape Bool}
    (hlast : lastAction.apply T1 = T1')
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start s0 T0 T1 (delayedLeftEmissionTape emitted))
      (coreCfg start s4 T0 T1'
        (delayedLeftEmissionTape
          (List.append emitted [b0, b1, b2, b3]))) := by
  refine Leads.trans
    (leads_emit (bit := b0) (T1' := T1)
      hs0 T0 T1 (h0 (Tape.read T0) (Tape.read T1)) rfl emitted hhold) ?_
  refine Leads.trans
    (leads_emit (bit := b1) (T1' := T1)
      hs1 T0 T1 (h1 (Tape.read T0) (Tape.read T1)) rfl
      (List.append emitted [b0]) (by simp)) ?_
  refine Leads.trans
    (leads_emit (bit := b2) (T1' := T1)
      hs2 T0 T1 (h2 (Tape.read T0) (Tape.read T1)) rfl
      (List.append (List.append emitted [b0]) [b1]) (by simp)) ?_
  have hfinal :=
    leads_emit (bit := b3) (T1' := T1') hs3 T0 T1
      (h3 (Tape.read T0) (Tape.read T1)) hlast
      (List.append (List.append (List.append emitted [b0]) [b1]) [b2])
      (by simp)
  simpa [List.append_assoc] using hfinal

theorem leads_outFalse (start : Nat) (T0 T1 : Tape Bool) :
    Leads start
      (coreCfg start (.outFalse0 none) T0 T1 Tape.blank)
      (coreCfg start (.seekFuelLast (some false)) T0 T1
        (delayedLeftEmissionTape [true, false, true, false])) := by
  have h := leads_emit4
    (start := start)
    (s0 := State.outFalse0 none)
    (s1 := State.outFalse1 (some true))
    (s2 := State.outFalse2 (some false))
    (s3 := State.outFalse3 (some true))
    (s4 := State.seekFuelLast (some false))
    (hold := none) (b0 := true) (b1 := false)
    (b2 := true) (b3 := false) (lastAction := keepS)
    (T1' := T1)
    (mem_states_emission (h := none) (by simp [emissionBlock]))
    (mem_states_emission (h := some true) (by simp [emissionBlock]))
    (mem_states_emission (h := some false) (by simp [emissionBlock]))
    (mem_states_emission (h := some true) (by simp [emissionBlock]))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 rfl [] rfl
  simpa using h

/-- One leftward scratch-tape step. -/
theorem leads_scratchL {start : Nat} {s target : State}
    (hs : s ∈ states start) {current : Option Bool}
    (hnext : forall r0 r2 : Option Bool,
      next start s r0 current r2 =
        some ⟨target, keepS, keepL, keepS⟩)
    (T0 : Tape Bool) (left : List (Option Bool))
    (previous : Option Bool) (right : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start s T0
        (tapeAtCells (previous :: left) (current :: right)) T2)
      (coreCfg start target T0
        (tapeAtCells left (previous :: current :: right)) T2) := by
  refine leads_step
    (start := start) (s := s)
    (T0 := T0)
    (T1 := tapeAtCells (previous :: left) (current :: right))
    (T2 := T2) (st := ⟨target, keepS, keepL, keepS⟩)
    (T0' := T0)
    (T1' := tapeAtCells left (previous :: current :: right))
    (T2' := T2)
    hs (hnext (Tape.read T0) (Tape.read T2)) rfl ?_ rfl
  exact keepL_apply_tapeAtCells left previous current right

/-- One rightward scratch-tape step. -/
theorem leads_scratchR {start : Nat} {s target : State}
    (hs : s ∈ states start) {current : Option Bool}
    (hnext : forall r0 r2 : Option Bool,
      next start s r0 current r2 =
        some ⟨target, keepS, keepR, keepS⟩)
    (T0 : Tape Bool) (left right : List (Option Bool))
    (T2 : Tape Bool) :
    Leads start
      (coreCfg start s T0 (tapeAtCells left (current :: right)) T2)
      (coreCfg start target T0 (tapeAtCells (current :: left) right) T2) := by
  refine leads_step
    (start := start) (s := s)
    (T0 := T0) (T1 := tapeAtCells left (current :: right)) (T2 := T2)
    (st := ⟨target, keepS, keepR, keepS⟩)
    (T0' := T0) (T1' := tapeAtCells (current :: left) right) (T2' := T2)
    hs (hnext (Tape.read T0) (Tape.read T2)) rfl ?_ rfl
  exact keepR_apply_tapeAtCells left current right

/-- Scratch shape while scanning a reversed fuel field toward its separator. -/
def seekFuelTape (fuelRev : Word Bool) (stageLast : Bool)
    (stageRest : Word Bool) (visited : List (Option Bool)) : Tape Bool :=
  match fuelRev with
  | [] =>
      tapeAtCells (some stageLast :: stageRest.map some) (none :: visited)
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some)
          (none :: some stageLast :: stageRest.map some))
        (some bit :: visited)

theorem leads_seekFuelSepRev (start : Nat) (hold : Hold)
    (fuelRev : Word Bool) (stageLast : Bool) (stageRest : Word Bool)
    (visited : List (Option Bool)) (T0 : Tape Bool) (T2 : Tape Bool) :
    Leads start
      (coreCfg start (.seekFuelSep hold) T0
        (seekFuelTape fuelRev stageLast stageRest visited) T2)
      (coreCfg start (.tailTake hold) T0
        (tapeAtCells (stageRest.map some)
          (some stageLast :: none ::
            List.append (fuelRev.reverse.map some) visited)) T2) := by
  induction fuelRev generalizing visited with
  | nil =>
      simpa [seekFuelTape] using
        (leads_scratchL (start := start)
          (s := State.seekFuelSep hold) (target := State.tailTake hold)
          (current := none)
          (mem_states_emission (h := hold) (by simp [emissionBlock]))
          (by intros; rfl) T0 (stageRest.map some) (some stageLast)
          visited T2)
  | cons bit rest ih =>
      cases rest with
      | nil =>
          have hstep :=
            leads_scratchL (start := start)
              (s := State.seekFuelSep hold)
              (target := State.seekFuelSep hold) (current := some bit)
              (mem_states_emission (h := hold) (by simp [emissionBlock]))
              (by intros; rfl) T0
              (some stageLast :: stageRest.map some) none visited T2
          refine Leads.trans (by simpa [seekFuelTape] using hstep) ?_
          simpa [seekFuelTape] using
            (ih (some bit :: visited))
      | cons next rest =>
          have hstep :=
            leads_scratchL (start := start)
              (s := State.seekFuelSep hold)
              (target := State.seekFuelSep hold) (current := some bit)
              (mem_states_emission (h := hold) (by simp [emissionBlock]))
              (by intros; rfl) T0
              (List.append (rest.map some)
                (none :: some stageLast :: stageRest.map some))
              (some next) visited T2
          refine Leads.trans (by simpa [seekFuelTape] using hstep) ?_
          simpa [seekFuelTape, List.append_assoc] using
            (ih (some bit :: visited))

theorem leads_seekFuel (start : Nat) (hold : Hold)
    (fuelRev : Word Bool) (stageLast : Bool) (stageRest : Word Bool)
    (T0 : Tape Bool) (T2 : Tape Bool) :
    Leads start
      (coreCfg start (.seekFuelLast hold) T0
        (tapeAtCells
          (List.append (fuelRev.map some)
            (none :: some stageLast :: stageRest.map some)) []) T2)
      (coreCfg start (.tailTake hold) T0
        (tapeAtCells (stageRest.map some)
          (some stageLast :: none ::
            List.append (fuelRev.reverse.map some) [none])) T2) := by
  cases fuelRev with
  | nil =>
      have hstep :=
        leads_scratchL (start := start)
          (s := State.seekFuelLast hold) (target := State.seekFuelSep hold)
          (current := none)
          (mem_states_emission (h := hold) (by simp [emissionBlock]))
          (by intros; rfl) T0
          (some stageLast :: stageRest.map some) none [] T2
      refine Leads.trans
        (by
          simpa [seekFuelTape, tapeAtCells_single_blank_eq_nil] using hstep) ?_
      exact leads_seekFuelSepRev start hold [] stageLast stageRest [none] T0 T2
  | cons bit rest =>
      have hstep :=
        leads_scratchL (start := start)
          (s := State.seekFuelLast hold) (target := State.seekFuelSep hold)
          (current := none)
          (mem_states_emission (h := hold) (by simp [emissionBlock]))
          (by intros; rfl) T0
          (List.append (rest.map some)
            (none :: some stageLast :: stageRest.map some))
          (some bit) [] T2
      refine Leads.trans
        (by
          simpa [seekFuelTape, tapeAtCells_single_blank_eq_nil] using hstep) ?_
      exact
        leads_seekFuelSepRev start hold (bit :: rest) stageLast stageRest
          [none] T0 T2

/-!
### Tail-cell emission
-/

def tailPendingTape (pending : Bool) (remaining : Word Bool)
    (visited : List (Option Bool)) : Tape Bool :=
  match remaining with
  | [] => tapeAtCells [] (none :: some pending :: visited)
  | nextBit :: rest =>
      tapeAtCells (rest.map some) (some nextBit :: some pending :: visited)

def tailHead (pending : Bool) : Word Bool -> Bool
  | [] => pending
  | nextBit :: rest => tailHead nextBit rest

def tailStream (pending : Bool) : Word Bool -> Word Bool
  | [] => []
  | nextBit :: rest =>
      List.append [!pending, pending, true, false]
        (tailStream nextBit rest)

theorem leads_tailPending_some (start : Nat)
    (pending nextBit : Bool) (hold : Hold)
    (T0 T1 T2 : Tape Bool) (hread : Tape.read T1 = some nextBit) :
    Leads start
      (coreCfg start (.tailPending pending hold) T0 T1 T2)
      (coreCfg start (.tailCell0 pending nextBit hold) T0 T1 T2) := by
  refine leads_step
    (start := start) (s := State.tailPending pending hold)
    (T0 := T0) (T1 := T1) (T2 := T2)
    (st := ⟨State.tailCell0 pending nextBit hold, keepS, keepS, keepS⟩)
    (T0' := T0) (T1' := T1) (T2' := T2)
    (mem_states_emission (h := hold)
      (by cases pending <;> simp [emissionBlock, boolValues]))
    (by rw [hread]; rfl)
    rfl rfl rfl

theorem leads_tailCellBlock (start : Nat)
    (pending nextBit : Bool) (hold : Hold)
    (T0 T1 : Tape Bool) {T1' : Tape Bool}
    (hmove : keepL.apply T1 = T1')
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.tailCell0 pending nextBit hold) T0 T1
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.tailPending nextBit (some false)) T0 T1'
        (delayedLeftEmissionTape
          (List.append emitted [!pending, pending, true, false]))) := by
  exact leads_emit4
    (start := start)
    (s0 := State.tailCell0 pending nextBit hold)
    (s1 := State.tailCell1 pending nextBit (some (!pending)))
    (s2 := State.tailCell2 pending nextBit (some pending))
    (s3 := State.tailCell3 pending nextBit (some true))
    (s4 := State.tailPending nextBit (some false))
    (hold := hold) (b0 := !pending) (b1 := pending)
    (b2 := true) (b3 := false) (lastAction := keepL)
    (T1' := T1')
    (mem_states_emission (h := hold)
      (by cases pending <;> cases nextBit <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some (!pending))
      (by cases pending <;> cases nextBit <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some pending)
      (by cases pending <;> cases nextBit <;> simp [emissionBlock, boolValues]))
    (mem_states_emission (h := some true)
      (by cases pending <;> cases nextBit <;> simp [emissionBlock, boolValues]))
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    (by unfold EmitRow; intros; rfl)
    T0 T1 hmove emitted hhold

theorem leads_tailPending (start : Nat)
    (pending : Bool) (remaining : Word Bool) (hold : Hold)
    (visited : List (Option Bool)) (T0 : Tape Bool)
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.tailPending pending hold) T0
        (tailPendingTape pending remaining visited)
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.tailDone0 (tailHead pending remaining)
          ((List.append emitted (tailStream pending remaining)).getLast?))
        T0
        (tapeAtCells []
          (none :: List.append ((pending :: remaining).reverse.map some)
            visited))
        (delayedLeftEmissionTape
          (List.append emitted (tailStream pending remaining)))) := by
  induction remaining generalizing pending hold visited emitted with
  | nil =>
      have hstep :=
        leads_step
          (start := start) (s := State.tailPending pending hold)
          (T0 := T0) (T1 := tailPendingTape pending [] visited)
          (T2 := delayedLeftEmissionTape emitted)
          (st := ⟨State.tailDone0 pending hold, keepS, keepS, keepS⟩)
          (T0' := T0) (T1' := tailPendingTape pending [] visited)
          (T2' := delayedLeftEmissionTape emitted)
          (mem_states_emission (h := hold)
            (by cases pending <;> simp [emissionBlock, boolValues]))
          (by rw [delayedLeftEmissionTape_read]; rfl) rfl rfl rfl
      simpa [tailPendingTape, tailHead, tailStream, hhold] using hstep
  | cons nextBit rest ih =>
      have henter :=
        leads_tailPending_some start pending nextBit hold T0
          (tailPendingTape pending (nextBit :: rest) visited)
          (delayedLeftEmissionTape emitted) rfl
      have hmove :
          keepL.apply (tailPendingTape pending (nextBit :: rest) visited) =
            tailPendingTape nextBit rest (some pending :: visited) := by
        cases rest <;> rfl
      have hemit :=
        leads_tailCellBlock start pending nextBit hold T0
          (tailPendingTape pending (nextBit :: rest) visited)
          hmove emitted hhold
      have hrec :=
        ih nextBit (some false) (some pending :: visited)
          (List.append emitted [!pending, pending, true, false]) (by simp)
      exact Leads.trans henter (Leads.trans hemit (by
        simpa [tailHead, tailStream, List.map_append,
          List.append_assoc] using hrec))

theorem leads_tailTakeRun (start : Nat)
    (pending : Bool) (remaining : Word Bool) (hold : Hold)
    (visited : List (Option Bool)) (T0 : Tape Bool)
    (emitted : Word Bool) (hhold : hold = emitted.getLast?) :
    Leads start
      (coreCfg start (.tailTake hold) T0
        (tapeAtCells (remaining.map some) (some pending :: visited))
        (delayedLeftEmissionTape emitted))
      (coreCfg start (.tailDone0 (tailHead pending remaining)
          ((List.append emitted (tailStream pending remaining)).getLast?))
        T0
        (tapeAtCells []
          (none :: List.append ((pending :: remaining).reverse.map some)
            visited))
        (delayedLeftEmissionTape
          (List.append emitted (tailStream pending remaining)))) := by
  have hmove :
      keepL.apply
          (tapeAtCells (remaining.map some) (some pending :: visited)) =
        tailPendingTape pending remaining visited := by
    cases remaining <;> rfl
  have hstep :=
    leads_step
      (start := start) (s := State.tailTake hold)
      (T0 := T0)
      (T1 := tapeAtCells (remaining.map some) (some pending :: visited))
      (T2 := delayedLeftEmissionTape emitted)
      (st := ⟨State.tailPending pending hold, keepS, keepL, keepS⟩)
      (T0' := T0) (T1' := tailPendingTape pending remaining visited)
      (T2' := delayedLeftEmissionTape emitted)
      (mem_states_emission (h := hold) (by simp [emissionBlock]))
      (by rw [delayedLeftEmissionTape_read]; rfl) rfl hmove rfl
  exact Leads.trans hstep
    (leads_tailPending start pending remaining hold visited T0 emitted hhold)


end FuelSimulatorCore
end StructuredConstructionTargets

end Computability
end FoC
