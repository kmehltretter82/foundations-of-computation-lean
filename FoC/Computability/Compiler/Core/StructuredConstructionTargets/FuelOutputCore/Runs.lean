import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutputCore.Stream
import FoC.Computability.Compiler.Structured.Lowering.TypedStateRuns

set_option doc.verso true

/-!
# Forward runs of the fuel-output structured core

Run lemmas for the typed fuel-output core over the compiled description
{lit}`(table n).description`.  All stepping happens at the typed level through
the {lit}`TypedStateTable` keystones; phases compose through the {lit}`Leads`
relation, which hides step counts.

The main results are the full valid-layout halting run and the reach-spin
runs for the two semantic failure modes (state-field mismatch and misaligned
result stream).
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets
namespace FuelOutputCore

open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers (tapeAtCells inputWithTrailingBlankPadding)

/-- The compiled fuel-output core description for halt parameter {lit}`n`. -/
def coreD (n : Nat) : Description :=
  (table n).description

/-- A typed core configuration: tape 1 is permanently blank. -/
def coreCfg (n : Nat) (s : CoreState) (T0 T2 : Tape Bool) : CommonGround.FiniteTransducers.Structured.Configuration :=
  ThreeTape.config ((table n).stateId s) T0 Tape.blank T2

/--
Step-count-free reachability: {lit}`d` continues exactly like {lit}`c` after
some fixed number of steps.
-/
def Leads (n : Nat) (c d : CommonGround.FiniteTransducers.Structured.Configuration) : Prop :=
  (table n).Leads c d

namespace Leads

theorem refl (n : Nat) (c : CommonGround.FiniteTransducers.Structured.Configuration) : Leads n c c :=
  TypedStateTable.Leads.refl (table n) c

theorem trans {n : Nat} {c d e : CommonGround.FiniteTransducers.Structured.Configuration}
    (h1 : Leads n c d) (h2 : Leads n d e) : Leads n c e :=
  TypedStateTable.Leads.trans h1 h2

theorem to_runConfig {n : Nat} {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (h : Leads n c d) : exists j : Nat, (coreD n).runConfig j c = d :=
  TypedStateTable.Leads.to_runConfig h

end Leads

/-- Reaching the spin state with some tape contents. -/
def LeadsSpin (n : Nat) (c : CommonGround.FiniteTransducers.Structured.Configuration) : Prop :=
  exists T0 T2 : Tape Bool,
    Leads n c (coreCfg n CoreState.spin T0 T2)

/-!
## The typed step engine
-/

theorem leads_step {n : Nat} {s : CoreState} (hs : s ∈ coreStates n)
    {T0 T2 : Tape Bool} {st : TypedStep CoreState}
    (hnext :
      CoreState.next n s (Tape.read T0) none (Tape.read T2) = some st)
    (h1 : st.action1 = keepS)
    {T0' T2' : Tape Bool}
    (h0 : st.action0.apply T0 = T0')
    (h2 : st.action2.apply T2 = T2') :
    Leads n (coreCfg n s T0 T2) (coreCfg n st.target T0' T2') := by
  have hblank : st.action1.apply Tape.blank = Tape.blank := by
    rw [h1]
    rfl
  have hnext' :
      (table n).next s (Tape.read T0) (Tape.read Tape.blank)
          (Tape.read T2) = some st := by
    change CoreState.next n s (Tape.read T0) none (Tape.read T2) = some st
    exact hnext
  simpa [Leads, coreCfg, TypedStateTable.config] using
    (TypedStateTable.leads_step (table n) hs hnext' h0 hblank h2)

/-!
## Specialized step forms
-/

/-- One rightward walking step. -/
theorem stepR {n : Nat} {s : CoreState} (hs : s ∈ coreStates n)
    {c : Option Bool} {target : CoreState}
    (hnext :
      forall r2 : Option Bool,
        CoreState.next n s c none r2 =
          some ⟨target, keepR, keepS, keepS⟩)
    (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n (coreCfg n s (tapeAtCells L (c :: R)) T2)
      (coreCfg n target (tapeAtCells (c :: L) R) T2) :=
  leads_step (T0 := tapeAtCells L (c :: R)) (T2 := T2) hs
    (hnext (Tape.read T2)) rfl (keepR_apply_tapeAtCells L c R) rfl

/-- One leftward walking step. -/
theorem stepL {n : Nat} {s : CoreState} (hs : s ∈ coreStates n)
    {c : Option Bool} {target : CoreState}
    (hnext :
      forall r2 : Option Bool,
        CoreState.next n s c none r2 =
          some ⟨target, keepL, keepS, keepS⟩)
    (L : List (Option Bool)) (c' : Option Bool) (R : List (Option Bool))
    (T2 : Tape Bool) :
    Leads n (coreCfg n s (tapeAtCells (c' :: L) (c :: R)) T2)
      (coreCfg n target (tapeAtCells L (c' :: c :: R)) T2) :=
  leads_step (T0 := tapeAtCells (c' :: L) (c :: R)) (T2 := T2) hs
    (hnext (Tape.read T2)) rfl (keepL_apply_tapeAtCells L c' c R) rfl

/-- The single right-edge overstep: read the end blank, turn left. -/
theorem stepL_end {n : Nat} {s : CoreState} (hs : s ∈ coreStates n)
    {target : CoreState}
    (hnext :
      forall r2 : Option Bool,
        CoreState.next n s none none r2 =
          some ⟨target, keepL, keepS, keepS⟩)
    (L : List (Option Bool)) (c' : Option Bool) (T2 : Tape Bool) :
    Leads n (coreCfg n s (tapeAtCells (c' :: L) []) T2)
      (coreCfg n target (tapeAtCells L [c', none]) T2) :=
  leads_step (T0 := tapeAtCells (c' :: L) []) (T2 := T2) hs
    (hnext (Tape.read T2)) rfl (keepL_apply_tapeAtCells_nil L c') rfl

/-- One marking step: write rightward on tape 0. -/
theorem stepR_write {n : Nat} {s : CoreState} (hs : s ∈ coreStates n)
    {c v : Option Bool} {target : CoreState}
    (hnext :
      forall r2 : Option Bool,
        CoreState.next n s c none r2 =
          some ⟨target, writeR v, keepS, keepS⟩)
    (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n (coreCfg n s (tapeAtCells L (c :: R)) T2)
      (coreCfg n target (tapeAtCells (v :: L) R) T2) :=
  leads_step (T0 := tapeAtCells L (c :: R)) (T2 := T2) hs
    (hnext (Tape.read T2)) rfl (writeR_apply_tapeAtCells v L c R) rfl

/-- One leftward step that also emits on tape 2. -/
theorem stepL_emit {n : Nat} {s : CoreState} (hs : s ∈ coreStates n)
    {c : Option Bool} {target : CoreState} {a2 : TapeAction}
    (hnext :
      forall r2 : Option Bool,
        CoreState.next n s c none r2 =
          some ⟨target, keepL, keepS, a2⟩)
    (L : List (Option Bool)) (c' : Option Bool) (R : List (Option Bool))
    {T2 T2' : Tape Bool} (h2 : a2.apply T2 = T2') :
    Leads n (coreCfg n s (tapeAtCells (c' :: L) (c :: R)) T2)
      (coreCfg n target (tapeAtCells L (c' :: c :: R)) T2') :=
  leads_step (T0 := tapeAtCells (c' :: L) (c :: R)) (T2 := T2) hs
    (hnext (Tape.read T2)) rfl (keepL_apply_tapeAtCells L c' c R) h2

/-- One rightward step that also emits on tape 2. -/
theorem stepR_emit {n : Nat} {s : CoreState} (hs : s ∈ coreStates n)
    {c : Option Bool} {target : CoreState} {a2 : TapeAction}
    (hnext :
      forall r2 : Option Bool,
        CoreState.next n s c none r2 =
          some ⟨target, keepR, keepS, a2⟩)
    (L R : List (Option Bool)) (T2 : Tape Bool)
    {T2' : Tape Bool} (h2 : a2.apply T2 = T2') :
    Leads n (coreCfg n s (tapeAtCells L (c :: R)) T2)
      (coreCfg n target (tapeAtCells (c :: L) R) T2') :=
  leads_step (T0 := tapeAtCells L (c :: R)) (T2 := T2) hs
    (hnext (Tape.read T2)) rfl (keepR_apply_tapeAtCells L c R) h2

/-- The mark-restoring flush step: write leftward on tape 0, flush tape 2. -/
theorem stepL_write_emit {n : Nat} {s : CoreState} (hs : s ∈ coreStates n)
    {c v : Option Bool} {target : CoreState} {a2 : TapeAction}
    (hnext :
      forall r2 : Option Bool,
        CoreState.next n s c none r2 =
          some ⟨target, writeL v, keepS, a2⟩)
    (L : List (Option Bool)) (c' : Option Bool) (R : List (Option Bool))
    {T2 T2' : Tape Bool} (h2 : a2.apply T2 = T2') :
    Leads n (coreCfg n s (tapeAtCells (c' :: L) (c :: R)) T2)
      (coreCfg n target (tapeAtCells L (c' :: v :: R)) T2') :=
  leads_step (T0 := tapeAtCells (c' :: L) (c :: R)) (T2 := T2) hs
    (hnext (Tape.read T2)) rfl (writeL_apply_tapeAtCells v L c' c R) h2

/-!
## Membership shorthands
-/

theorem mem_fixed {n : Nat} {s : CoreState} (h : s ∈ fixedStates) :
    s ∈ coreStates n :=
  mem_coreStates_of_fixed h

/-!
## Token bit vocabulary
-/

/-- The Boolean window cells of one code token. -/
def tokBits (t : MachineCodeSymbol) : List (Option Bool) :=
  (encodeCodeSymbolAsInput t).map some

/-- The Boolean window cells of a code word. -/
def codeBits (w : Word MachineCodeSymbol) : List (Option Bool) :=
  (encodeCodeWordAsInput w).map some

@[simp] theorem codeBits_nil : codeBits [] = [] := rfl

private theorem map_some_append (a b : Word Bool) :
    (List.append a b).map some =
      List.append (a.map some) (b.map some) := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      show some x :: (List.append xs b).map some = _
      rw [ih]
      rfl

theorem codeBits_cons (t : MachineCodeSymbol) (w : Word MachineCodeSymbol) :
    codeBits (t :: w) = List.append (tokBits t) (codeBits w) := by
  show
    (List.append (encodeCodeSymbolAsInput t)
      (encodeCodeWordAsInput w)).map some = _
  rw [map_some_append]
  rfl

theorem codeBits_append (a b : Word MachineCodeSymbol) :
    codeBits (List.append a b) =
      List.append (codeBits a) (codeBits b) := by
  show (encodeCodeWordAsInput (List.append a b)).map some = _
  rw [encodeCodeWordAsInput_append, map_some_append]
  rfl

@[simp] theorem tokBits_header :
    tokBits MachineCodeSymbol.header =
      [some false, some false, some false, some false] := rfl

@[simp] theorem tokBits_tick :
    tokBits MachineCodeSymbol.tick =
      [some false, some false, some true, some false] := rfl

@[simp] theorem tokBits_done :
    tokBits MachineCodeSymbol.done =
      [some false, some false, some true, some true] := rfl

@[simp] theorem tokBits_blank :
    tokBits MachineCodeSymbol.blank =
      [some false, some true, some false, some false] := rfl

@[simp] theorem tokBits_zero :
    tokBits MachineCodeSymbol.zero =
      [some false, some true, some false, some true] := rfl

@[simp] theorem tokBits_one :
    tokBits MachineCodeSymbol.one =
      [some false, some true, some true, some false] := rfl

/-- The cell token of one logical tape cell. -/
def cellTok : Option Bool -> MachineCodeSymbol
  | none => MachineCodeSymbol.blank
  | some false => MachineCodeSymbol.zero
  | some true => MachineCodeSymbol.one

theorem encodeCell_eq (c : Option Bool) :
    encodeCell c = [cellTok c] := by
  cases c with
  | none => rfl
  | some b => cases b <;> rfl

theorem encodeCellsAppend_eq_map
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    encodeCellsAppend cells suffix =
      List.append (cells.map cellTok) suffix := by
  induction cells with
  | nil => rfl
  | cons c rest ih =>
      show encodeCellAppend c (encodeCellsAppend rest suffix) = _
      rw [ih]
      show List.append (encodeCell c) _ = _
      rw [encodeCell_eq]
      rfl

/-!
## Left-context accumulation

Rightward walks push visited cells onto the reversed left context.
{lit}`pushBits` computes by iota reduction on literal token bits, so walk
lemmas need no list algebra in their inductive steps.
-/

/-- Push cells onto a reversed left context in visit order. -/
def pushBits (bits L : List (Option Bool)) : List (Option Bool) :=
  bits.foldl (fun acc c => c :: acc) L

@[simp] theorem pushBits_nil (L : List (Option Bool)) :
    pushBits [] L = L := rfl

theorem pushBits_cons (c : Option Bool) (bits L : List (Option Bool)) :
    pushBits (c :: bits) L = pushBits bits (c :: L) := rfl

theorem pushBits_append (a b L : List (Option Bool)) :
    pushBits (List.append a b) L = pushBits b (pushBits a L) := by
  induction a generalizing L with
  | nil => rfl
  | cons c rest ih =>
      rw [show List.append (c :: rest) b = c :: List.append rest b from rfl,
        pushBits_cons, pushBits_cons, ih]

theorem pushBits_eq_reverse_append (bits L : List (Option Bool)) :
    pushBits bits L = List.append bits.reverse L := by
  induction bits generalizing L with
  | nil => rfl
  | cons c rest ih =>
      rw [pushBits_cons, ih]
      simp

/-!
## Rightward field walks
-/

/-- Skip the header token. -/
theorem leads_header (n : Nat) (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.hdr0
        (tapeAtCells L
          (List.append (tokBits MachineCodeSymbol.header) R)) T2)
      (coreCfg n CoreState.inLen0
        (tapeAtCells (pushBits (tokBits MachineCodeSymbol.header) L) R)
        T2) :=
  ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
    ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
      ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ R T2))))

/-- Walk the input-word length field. -/
theorem leads_inLen (n m : Nat) (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.inLen0
        (tapeAtCells L (List.append (codeBits (encodeNat m)) R)) T2)
      (coreCfg n CoreState.inBits0
        (tapeAtCells (pushBits (codeBits (encodeNat m)) L) R) T2) := by
  induction m generalizing L with
  | zero =>
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
              (stepR (mem_fixed (by decide)) (fun _ => rfl) _ R T2))))
  | succ m ih =>
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
              ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                (ih _)))))

/-- Walk the stage field from a whole-token boundary. -/
theorem leads_stage (n m : Nat) (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.stage0
        (tapeAtCells L (List.append (codeBits (encodeNat m)) R)) T2)
      (coreCfg n (CoreState.chk 0 GroupPos.p0)
        (tapeAtCells (pushBits (codeBits (encodeNat m)) L) R) T2) := by
  induction m generalizing L with
  | zero =>
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
              (stepR (mem_fixed (by decide)) (fun _ => rfl) _ R T2))))
  | succ m ih =>
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
              ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                (ih _)))))

/-- Walk the configuration left-list length field. -/
theorem leads_lLen (n m : Nat) (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.lLen0
        (tapeAtCells L (List.append (codeBits (encodeNat m)) R)) T2)
      (coreCfg n CoreState.lb0
        (tapeAtCells (pushBits (codeBits (encodeNat m)) L) R) T2) := by
  induction m generalizing L with
  | zero =>
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
              (stepR (mem_fixed (by decide)) (fun _ => rfl) _ R T2))))
  | succ m ih =>
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
              ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                (ih _)))))

/-- Walk the configuration right-list length field from a whole-token
boundary. -/
theorem leads_rLen (n m : Nat) (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.rLen0
        (tapeAtCells L (List.append (codeBits (encodeNat m)) R)) T2)
      (coreCfg n CoreState.rb0
        (tapeAtCells (pushBits (codeBits (encodeNat m)) L) R) T2) := by
  induction m generalizing L with
  | zero =>
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
              (stepR (mem_fixed (by decide)) (fun _ => rfl) _ R T2))))
  | succ m ih =>
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
              ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                (ih _)))))

/-!
## Input cells and the parametric state check
-/

theorem leadsSpin_of_leads {n : Nat}
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (h : Leads n c d) (hspin : LeadsSpin n d) : LeadsSpin n c := by
  rcases hspin with ⟨T0, T2, hlead⟩
  exact ⟨T0, T2, h.trans hlead⟩

/--
Walk the input-word cell tokens, falling through the first two bits of the
following stage length-field token, then finish the stage field.
-/
theorem leads_inBits_stage
    (n : Nat) (w : Word Bool) (m : Nat)
    (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.inBits0
        (tapeAtCells L
          (List.append (codeBits ((w.map some).map cellTok))
            (List.append (codeBits (encodeNat m)) R))) T2)
      (coreCfg n (CoreState.chk 0 GroupPos.p0)
        (tapeAtCells
          (pushBits (codeBits (encodeNat m))
            (pushBits (codeBits ((w.map some).map cellTok)) L)) R) T2) := by
  induction w generalizing L with
  | nil =>
      cases m with
      | zero =>
          exact
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
              ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                  (stepR (mem_fixed (by decide)) (fun _ => rfl) _ R T2))))
      | succ m' =>
          exact
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
              ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                  ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _
                      T2).trans
                    (leads_stage n m' _ R T2)))))
  | cons b w' ih =>
      cases b with
      | false =>
          exact
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
              ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                  ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _
                      T2).trans
                    (ih _)))))
      | true =>
          exact
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
              ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
                  ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _
                      T2).trans
                    (ih _)))))

/-!
### The state-check chain

The tick and done dispatch rows of the chain compare the tick count against
the halt parameter, so their table entries are stated as {lit}`if` equations.
-/

theorem next_chk_p3_done (n j : Nat) (r2 : Option Bool) :
    CoreState.next n (CoreState.chk j GroupPos.p3) (some true) none r2 =
      if j = n then
        some ⟨CoreState.lLen0, keepR, keepS, keepS⟩
      else
        some ⟨CoreState.spin, keepR, keepS, keepS⟩ := rfl

theorem next_chk_p3_tick (n j : Nat) (r2 : Option Bool) :
    CoreState.next n (CoreState.chk j GroupPos.p3) (some false) none r2 =
      if j < n then
        some ⟨CoreState.chk (j + 1) GroupPos.p0, keepR, keepS, keepS⟩
      else
        some ⟨CoreState.spin, keepR, keepS, keepS⟩ := rfl

/-- The check chain accepts exactly the halt parameter. -/
theorem leads_chk_accept (n : Nat) :
    forall (m j : Nat), j + m = n ->
      forall (L R : List (Option Bool)) (T2 : Tape Bool),
        Leads n
          (coreCfg n (CoreState.chk j GroupPos.p0)
            (tapeAtCells L (List.append (codeBits (encodeNat m)) R)) T2)
          (coreCfg n CoreState.lLen0
            (tapeAtCells (pushBits (codeBits (encodeNat m)) L) R) T2) := by
  intro m
  induction m with
  | zero =>
      intro j hjm L R T2
      have hj : j = n := by lia
      have hjle : j ≤ n := Nat.le_of_eq hj
      refine
        ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) _ _ T2).trans
              (stepR (mem_coreStates_chk hjle _)
                (fun r2 => by rw [next_chk_p3_done, if_pos hj]) _ R T2))))
  | succ m ih =>
      intro j hjm L R T2
      have hjlt : j < n := by lia
      have hjle : j ≤ n := Nat.le_of_lt hjlt
      refine
        ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) _ _ T2).trans
              ((stepR (mem_coreStates_chk hjle _)
                  (fun r2 => by rw [next_chk_p3_tick, if_pos hjlt]) _ _
                  T2).trans
                (ih (j + 1) (by lia) _ R T2)))))

/-- The check chain rejects every other state value into the spin trap. -/
theorem leads_chk_reject (n : Nat) :
    forall (m j : Nat), j + m ≠ n -> j ≤ n ->
      forall (L R : List (Option Bool)) (T2 : Tape Bool),
        LeadsSpin n
          (coreCfg n (CoreState.chk j GroupPos.p0)
            (tapeAtCells L (List.append (codeBits (encodeNat m)) R)) T2) := by
  intro m
  induction m with
  | zero =>
      intro j hne hjle L R T2
      have hj : j ≠ n := by lia
      refine
        leadsSpin_of_leads
          ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) L _ T2).trans
            ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) _ _ T2).trans
              ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) _ _
                  T2).trans
                (stepR (mem_coreStates_chk hjle _)
                  (fun r2 => by rw [next_chk_p3_done, if_neg hj]) _ R
                  T2))))
          ⟨_, _, Leads.refl n _⟩
  | succ m ih =>
      intro j hne hjle L R T2
      by_cases hjlt : j < n
      · refine
          leadsSpin_of_leads
            ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) L _ T2).trans
              ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) _ _
                  T2).trans
                ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) _ _
                    T2).trans
                  (stepR (mem_coreStates_chk hjle _)
                    (fun r2 => by rw [next_chk_p3_tick, if_pos hjlt]) _ _
                    T2))))
            (ih (j + 1) (by lia) hjlt _ R T2)
      · refine
          leadsSpin_of_leads
            ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) L _ T2).trans
              ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) _ _
                  T2).trans
                ((stepR (mem_coreStates_chk hjle _) (fun _ => rfl) _ _
                    T2).trans
                  (stepR (mem_coreStates_chk hjle _)
                    (fun r2 => by rw [next_chk_p3_tick, if_neg hjlt]) _ _
                    T2))))
            ⟨_, _, Leads.refl n _⟩

/-!
## Left blob, head marking, and the walk to the right edge
-/

/-- The window cells of a cell token: blank-led with a tracked tail. -/
theorem exists_cellTok_bits (h : Option Bool) :
    exists v2 v3 : Bool,
      tokBits (cellTok h) =
        [some false, some true, some v2, some v3] := by
  cases h with
  | none => exact ⟨false, false, rfl⟩
  | some b =>
      cases b with
      | false => exact ⟨false, true, rfl⟩
      | true => exact ⟨true, false, rfl⟩

/-- The window cells of the marked head token. -/
def markedBits (h : Option Bool) : List (Option Bool) :=
  some true :: (tokBits (cellTok h)).tail

theorem markedBits_eq {h : Option Bool} {v2 v3 : Bool}
    (hbits : tokBits (cellTok h) =
      [some false, some true, some v2, some v3]) :
    markedBits h = [some true, some true, some v2, some v3] := by
  unfold markedBits
  rw [hbits]
  rfl

/-- Walk a run of cell tokens with the {lit}`lb` loop. -/
theorem leads_lb (n : Nat) (cells : List (Option Bool))
    (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.lb0
        (tapeAtCells L
          (List.append (codeBits (cells.map cellTok)) R)) T2)
      (coreCfg n CoreState.lb0
        (tapeAtCells (pushBits (codeBits (cells.map cellTok)) L) R)
        T2) := by
  induction cells generalizing L with
  | nil => exact Leads.refl n _
  | cons c rest ih =>
      obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits c
      have hcode :
          codeBits ((c :: rest).map cellTok) =
            List.append (tokBits (cellTok c))
              (codeBits (rest.map cellTok)) := codeBits_cons _ _
      rw [hcode, hbits]
      rw [show
        pushBits
            (List.append [some false, some true, some v2, some v3]
              (codeBits (rest.map cellTok))) L =
          pushBits (codeBits (rest.map cellTok))
            (some v3 :: some v2 :: some true :: some false :: L) from rfl]
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
              ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _
                  T2).trans
                (ih _)))))

/-- Walk a run of cell tokens with the {lit}`rb` loop. -/
theorem leads_rb (n : Nat) (cells : List (Option Bool))
    (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.rb0
        (tapeAtCells L
          (List.append (codeBits (cells.map cellTok)) R)) T2)
      (coreCfg n CoreState.rb0
        (tapeAtCells (pushBits (codeBits (cells.map cellTok)) L) R)
        T2) := by
  induction cells generalizing L with
  | nil => exact Leads.refl n _
  | cons c rest ih =>
      obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits c
      have hcode :
          codeBits ((c :: rest).map cellTok) =
            List.append (tokBits (cellTok c))
              (codeBits (rest.map cellTok)) := codeBits_cons _ _
      rw [hcode, hbits]
      rw [show
        pushBits
            (List.append [some false, some true, some v2, some v3]
              (codeBits (rest.map cellTok))) L =
          pushBits (codeBits (rest.map cellTok))
            (some v3 :: some v2 :: some true :: some false :: L) from rfl]
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
              ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _
                  T2).trans
                (ih _)))))

/--
The head-marking dance and the right-list length field: detect the length
field after the head cell, backtrack, mark the head, return, and walk the
length field to the right-cell blob.
-/
theorem leads_mark_rLen (n : Nat) (h : Option Bool) (m : Nat)
    (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.lb0
        (tapeAtCells (pushBits (tokBits (cellTok h)) L)
          (List.append (codeBits (encodeNat m)) R)) T2)
      (coreCfg n CoreState.rb0
        (tapeAtCells
          (pushBits (codeBits (encodeNat m)) (pushBits (markedBits h) L))
          R) T2) := by
  obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits h
  rw [hbits, markedBits_eq hbits]
  have hdance :
      Leads n
        (coreCfg n CoreState.lb0
          (tapeAtCells
            (pushBits [some false, some true, some v2, some v3] L)
            (List.append (codeBits (encodeNat m)) R)) T2)
        (coreCfg n CoreState.rLen2
          (tapeAtCells
            (pushBits [some false, some false]
              (pushBits [some true, some true, some v2, some v3] L))
            (List.append ((codeBits (encodeNat m)).drop 2) R)) T2) := by
    cases m with
    | zero =>
      refine Leads.trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepR_write (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      refine Leads.trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      refine Leads.trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      refine Leads.trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      refine Leads.trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      exact stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2
    | succ m' =>
      refine Leads.trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepR_write (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      refine Leads.trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      refine Leads.trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      refine Leads.trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      refine Leads.trans
        (stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2) ?_
      exact stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2
  refine hdance.trans ?_
  cases m with
  | zero =>
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
          (stepR (mem_fixed (by decide)) (fun _ => rfl) _ R T2))
  | succ m' =>
      exact
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
          ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
            (leads_rLen n m' _ R T2)))

/--
Read the right-edge blank once, then skip back over the hit token, stopping
with the cursor on its first bit.
-/
theorem leads_endTurn (n : Nat) (hit : Bool)
    (Lfull : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.rb0
        (tapeAtCells
          (pushBits (tokBits (cellTok (some hit))) Lfull) []) T2)
      (coreCfg n CoreState.hit0
        (tapeAtCells Lfull
          (List.append (tokBits (cellTok (some hit))) [none])) T2) := by
  cases hit with
  | false =>
      exact
        ((stepL_end (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
          ((stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2).trans
            ((stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2).trans
              (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2))))
  | true =>
      exact
        ((stepL_end (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
          ((stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2).trans
            ((stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2).trans
              (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2))))

/-!
## Emission phases

The leftward emission walks keep the unprocessed window bits entirely in the
left context at phase boundaries.  {lit}`headTape` re-splits that context at
the cursor after a boundary-crossing left step.
-/

/-- Split a left-context block at its first cell after a leftward step. -/
def headTape (bits R : List (Option Bool)) : Tape Bool :=
  match bits with
  | [] => tapeAtCells [] R
  | u :: us => tapeAtCells us (u :: R)

/-- A leftward step whose target view re-splits an abstract left block. -/
theorem stepL_headTape {n : Nat} {s : CoreState} (hs : s ∈ coreStates n)
    {c : Option Bool} {target : CoreState}
    (hnext :
      forall r2 : Option Bool,
        CoreState.next n s c none r2 =
          some ⟨target, keepL, keepS, keepS⟩)
    {LL : List (Option Bool)} (hLL : LL ≠ [])
    (R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n (coreCfg n s (tapeAtCells LL (c :: R)) T2)
      (coreCfg n target (headTape LL (c :: R)) T2) := by
  cases LL with
  | nil => exact absurd rfl hLL
  | cons u us => exact stepL hs hnext us u R T2

/-- A leftward emitting step onto an abstract left block. -/
theorem stepL_emit_headTape {n : Nat} {s : CoreState}
    (hs : s ∈ coreStates n)
    {c : Option Bool} {target : CoreState} {a2 : TapeAction}
    (hnext :
      forall r2 : Option Bool,
        CoreState.next n s c none r2 =
          some ⟨target, keepL, keepS, a2⟩)
    {LL : List (Option Bool)} (hLL : LL ≠ [])
    (R : List (Option Bool)) {T2 T2' : Tape Bool}
    (h2 : a2.apply T2 = T2') :
    Leads n (coreCfg n s (tapeAtCells LL (c :: R)) T2)
      (coreCfg n target (headTape LL (c :: R)) T2') := by
  cases LL with
  | nil => exact absurd rfl hLL
  | cons u us => exact stepL_emit hs hnext us u R h2

/-- A leftward writing and flushing step onto an abstract left block. -/
theorem stepL_write_emit_headTape {n : Nat} {s : CoreState}
    (hs : s ∈ coreStates n)
    {c v : Option Bool} {target : CoreState} {a2 : TapeAction}
    (hnext :
      forall r2 : Option Bool,
        CoreState.next n s c none r2 =
          some ⟨target, writeL v, keepS, a2⟩)
    {LL : List (Option Bool)} (hLL : LL ≠ [])
    (R : List (Option Bool)) {T2 T2' : Tape Bool}
    (h2 : a2.apply T2 = T2') :
    Leads n (coreCfg n s (tapeAtCells LL (c :: R)) T2)
      (coreCfg n target (headTape LL (v :: R)) T2') := by
  cases LL with
  | nil => exact absurd rfl hLL
  | cons u us => exact stepL_write_emit hs hnext us u R h2

theorem append_cons_ne_nil {α : Type _} (X Y : List α) (a : α) :
    List.append X (a :: Y) ≠ [] := by
  cases X <;> simp

/-!
### Token-block vocabulary for leftward walks
-/

/-- Reversed window bits of a run of cell tokens, in processing order. -/
def flatRevTokBits (cells : List (Option Bool)) : List (Option Bool) :=
  cells.flatMap (fun c => (tokBits (cellTok c)).reverse)

@[simp] theorem flatRevTokBits_nil : flatRevTokBits [] = [] := rfl

theorem flatRevTokBits_cons (c : Option Bool) (rest : List (Option Bool)) :
    flatRevTokBits (c :: rest) =
      List.append (tokBits (cellTok c)).reverse (flatRevTokBits rest) := by
  simp [flatRevTokBits]

/-- Forward window bits of processed cell tokens, most recent first. -/
def unwalkBits (cells Racc : List (Option Bool)) : List (Option Bool) :=
  cells.foldl (fun R c => List.append (tokBits (cellTok c)) R) Racc

@[simp] theorem unwalkBits_nil (Racc : List (Option Bool)) :
    unwalkBits [] Racc = Racc := rfl

theorem unwalkBits_cons (c : Option Bool) (rest Racc : List (Option Bool)) :
    unwalkBits (c :: rest) Racc =
      unwalkBits rest (List.append (tokBits (cellTok c)) Racc) := rfl

/-- Forward window bits of the {lit}`done` token. -/
def doneBitsF : List (Option Bool) :=
  [some false, some false, some true, some true]

/-- Reversed window bits of the {lit}`done` token. -/
def doneRevBits : List (Option Bool) :=
  [some true, some true, some false, some false]

/-- Reversed window bits of a run of tick tokens. -/
def tickRevBits : Nat -> List (Option Bool)
  | 0 => []
  | m + 1 =>
      some false :: some true :: some false :: some false ::
        tickRevBits m

private theorem append_snoc_assoc {α : Type _}
    (acc : List α) (b : α) (X : List α) :
    List.append (List.append acc [b]) X = List.append acc (b :: X) := by
  induction acc with
  | nil => rfl
  | cons a rest ih =>
      show a :: List.append (List.append rest [b]) X = _
      rw [ih]
      rfl

theorem streamFold?_snoc_some {acc : List Bool} {e e' : Emission}
    {bit : Bool}
    (hacc : streamFold? Emission.start acc = some e)
    (hstream : e.stream bit = some e') :
    streamFold? Emission.start (List.append acc [bit]) = some e' := by
  rw [streamFold?_append, hacc]
  show streamFold? e [bit] = some e'
  rw [streamFold?_cons_of_stream_some [] hstream]
  rfl

theorem stream_false_some (e : Emission) :
    exists e' : Emission, e.stream false = some e' := by
  unfold Emission.stream
  cases hpos : e.pos
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rw [if_pos (Or.inl rfl)]
    exact ⟨_, rfl⟩

/-!
### Emission-row dispatch equations
-/

theorem next_re1_zero (n : Nat) (e : Emission) (r2 : Option Bool) :
    CoreState.next n (CoreState.re1 true false e) (some true) none r2 =
      (match e.stream false with
        | some e' =>
            some ⟨CoreState.re0 e', keepL, keepS, e.emitAction⟩
        | none => some ⟨CoreState.spin, keepL, keepS, keepS⟩) := rfl

theorem next_re1_one (n : Nat) (e : Emission) (r2 : Option Bool) :
    CoreState.next n (CoreState.re1 false true e) (some true) none r2 =
      (match e.stream true with
        | some e' =>
            some ⟨CoreState.re0 e', keepL, keepS, e.emitAction⟩
        | none => some ⟨CoreState.spin, keepL, keepS, keepS⟩) := rfl

theorem next_hd0_zero (n : Nat) (e : Emission) (r2 : Option Bool) :
    CoreState.next n (CoreState.hd0 true false e) (some true) none r2 =
      (match e.stream false with
        | some e' =>
            some ⟨CoreState.ls3 e', keepL, keepS, e.emitAction⟩
        | none => some ⟨CoreState.spin, keepL, keepS, keepS⟩) := rfl

theorem next_hd0_one (n : Nat) (e : Emission) (r2 : Option Bool) :
    CoreState.next n (CoreState.hd0 false true e) (some true) none r2 =
      (match e.stream true with
        | some e' =>
            some ⟨CoreState.ls3 e', keepL, keepS, e.emitAction⟩
        | none => some ⟨CoreState.spin, keepL, keepS, keepS⟩) := rfl

theorem next_le3_zero (n : Nat) (e : Emission) (r2 : Option Bool) :
    CoreState.next n (CoreState.le3 false e) (some true) none r2 =
      (match e.stream false with
        | some e' =>
            some ⟨CoreState.le0 e', keepR, keepS, e.emitAction⟩
        | none => some ⟨CoreState.spin, keepR, keepS, keepS⟩) := rfl

theorem next_le3_one (n : Nat) (e : Emission) (r2 : Option Bool) :
    CoreState.next n (CoreState.le3 true e) (some false) none r2 =
      (match e.stream true with
        | some e' =>
            some ⟨CoreState.le0 e', keepR, keepS, e.emitAction⟩
        | none => some ⟨CoreState.spin, keepR, keepS, keepS⟩) := rfl

theorem next_le0_mark (n : Nat) (e : Emission) (r2 : Option Bool) :
    CoreState.next n (CoreState.le0 e) (some true) none r2 =
      (match e.pos with
        | GroupPos.p0 =>
            some ⟨CoreState.rw3, writeL (some false), keepS,
              e.flushAction⟩
        | _ => some ⟨CoreState.spin, keepR, keepS, keepS⟩) := rfl

/-!
### The right-list emission loop
-/

/-- Forward tick-token bits prepended {lit}`m` times. -/
def tickBitsF : Nat -> List (Option Bool) -> List (Option Bool)
  | 0, X => X
  | k + 1, X =>
      some false :: some false :: some true :: some false ::
        tickBitsF k X

/--
Successful right-list emission: walk the reversed right cells, streaming
nonblank bits, and exit at the length-field {lit}`done` token.
-/
theorem leads_re_ok (n : Nat) (rrev : List (Option Bool)) :
    forall (acc : List Bool) (e efin : Emission)
      (L0 Racc : List (Option Bool)),
      streamFold? Emission.start acc = some e ->
      streamFold? e (rrev.filterMap id) = some efin ->
      Leads n
        (coreCfg n (CoreState.re3 e)
          (headTape
            (List.append (flatRevTokBits rrev)
              (List.append doneRevBits L0)) Racc)
          (emissionTape acc))
        (coreCfg n (CoreState.rt0 efin)
          (tapeAtCells L0
            (List.append doneBitsF (unwalkBits rrev Racc)))
          (emissionTape (List.append acc (rrev.filterMap id)))) := by
  induction rrev with
  | nil =>
      intro acc e efin L0 Racc hacc hfold
      have hefin : e = efin := by simpa using hfold
      subst hefin
      rw [show List.append acc (List.filterMap id ([] : List (Option Bool))) =
        acc from List.append_nil acc]
      exact
        ((stepL (mem_cs_re3 _) (fun _ => rfl) _ _ _ _).trans
          ((stepL (mem_cs_re2 _ _) (fun _ => rfl) _ _ _ _).trans
            (stepL (mem_cs_re1 _ _ _) (fun _ => rfl) _ _ _ _)))
  | cons c rest ih =>
      intro acc e efin L0 Racc hacc hfold
      rw [flatRevTokBits_cons]
      cases c with
      | none =>
          refine Leads.trans
            (stepL (mem_cs_re3 _) (fun _ => rfl) _ _ _ _) ?_
          refine Leads.trans
            (stepL (mem_cs_re2 _ _) (fun _ => rfl) _ _ _ _) ?_
          refine Leads.trans
            (stepL (mem_cs_re1 _ _ _) (fun _ => rfl) _ _ _ _) ?_
          refine Leads.trans
            (stepL_headTape (mem_cs_re0 _) (fun _ => rfl)
              (append_cons_ne_nil _ _ _) _ _) ?_
          exact ih acc e efin L0 _ hacc hfold
      | some b =>
          cases b with
          | false =>
              obtain ⟨e1, hstream⟩ := stream_false_some e
              have hfold' :
                  streamFold? e1 (rest.filterMap id) = some efin := by
                rw [show (((some false :: rest) :
                    List (Option Bool)).filterMap id) =
                    false :: rest.filterMap id from rfl] at hfold
                rw [streamFold?_cons_of_stream_some _ hstream] at hfold
                exact hfold
              rw [show List.append acc
                  (((some false :: rest) :
                    List (Option Bool)).filterMap id) =
                  List.append (List.append acc [false])
                    (rest.filterMap id) from
                (append_snoc_assoc acc false _).symm]
              refine Leads.trans
                (stepL (mem_cs_re3 _) (fun _ => rfl) _ _ _ _) ?_
              refine Leads.trans
                (stepL (mem_cs_re2 _ _) (fun _ => rfl) _ _ _ _) ?_
              refine Leads.trans
                (stepL_emit (mem_cs_re1 _ _ _)
                  (fun r2 => by rw [next_re1_zero, hstream]) _ _ _
                  (emitAction_apply_emissionTape hacc false)) ?_
              refine Leads.trans
                (stepL_headTape (mem_cs_re0 _) (fun _ => rfl)
                  (append_cons_ne_nil _ _ _) _ _) ?_
              exact
                ih (List.append acc [false]) e1 efin L0 _
                  (streamFold?_snoc_some hacc hstream) hfold'
          | true =>
              have hfoldcons :
                  streamFold? e (true :: rest.filterMap id) =
                    some efin := hfold
              cases hstream : e.stream true with
              | none =>
                  rw [streamFold?_cons_of_stream_none _ hstream]
                    at hfoldcons
                  cases hfoldcons
              | some e1 =>
                  have hfold' :
                      streamFold? e1 (rest.filterMap id) = some efin := by
                    rw [streamFold?_cons_of_stream_some _ hstream]
                      at hfoldcons
                    exact hfoldcons
                  rw [show List.append acc
                      (((some true :: rest) :
                        List (Option Bool)).filterMap id) =
                      List.append (List.append acc [true])
                        (rest.filterMap id) from
                    (append_snoc_assoc acc true _).symm]
                  refine Leads.trans
                    (stepL (mem_cs_re3 _) (fun _ => rfl) _ _ _ _) ?_
                  refine Leads.trans
                    (stepL (mem_cs_re2 _ _) (fun _ => rfl) _ _ _ _) ?_
                  refine Leads.trans
                    (stepL_emit (mem_cs_re1 _ _ _)
                      (fun r2 => by rw [next_re1_one, hstream]) _ _ _
                      (emitAction_apply_emissionTape hacc true)) ?_
                  refine Leads.trans
                    (stepL_headTape (mem_cs_re0 _) (fun _ => rfl)
                      (append_cons_ne_nil _ _ _) _ _) ?_
                  exact
                    ih (List.append acc [true]) e1 efin L0 _
                      (streamFold?_snoc_some hacc hstream) hfold'

/-- Rejected right-list emission reaches the spin trap. -/
theorem leads_re_spin (n : Nat) (rrev : List (Option Bool)) :
    forall (acc : List Bool) (e : Emission)
      (L0 Racc : List (Option Bool)),
      streamFold? Emission.start acc = some e ->
      streamFold? e (rrev.filterMap id) = none ->
      LeadsSpin n
        (coreCfg n (CoreState.re3 e)
          (headTape
            (List.append (flatRevTokBits rrev)
              (List.append doneRevBits L0)) Racc)
          (emissionTape acc)) := by
  induction rrev with
  | nil =>
      intro acc e L0 Racc hacc hfold
      exact nomatch hfold
  | cons c rest ih =>
      intro acc e L0 Racc hacc hfold
      rw [flatRevTokBits_cons]
      cases c with
      | none =>
          refine leadsSpin_of_leads
            ((stepL (mem_cs_re3 _) (fun _ => rfl) _ _ _ _).trans
              ((stepL (mem_cs_re2 _ _) (fun _ => rfl) _ _ _ _).trans
                ((stepL (mem_cs_re1 _ _ _) (fun _ => rfl) _ _ _ _).trans
                  (stepL_headTape (mem_cs_re0 _) (fun _ => rfl)
                    (append_cons_ne_nil _ _ _) _ _))))
            (ih acc e L0 _ hacc hfold)
      | some b =>
          cases b with
          | false =>
              obtain ⟨e1, hstream⟩ := stream_false_some e
              have hfold' :
                  streamFold? e1 (rest.filterMap id) = none := by
                rw [show (((some false :: rest) :
                    List (Option Bool)).filterMap id) =
                    false :: rest.filterMap id from rfl] at hfold
                rw [streamFold?_cons_of_stream_some _ hstream] at hfold
                exact hfold
              refine leadsSpin_of_leads
                ((stepL (mem_cs_re3 _) (fun _ => rfl) _ _ _ _).trans
                  ((stepL (mem_cs_re2 _ _) (fun _ => rfl) _ _ _ _).trans
                    ((stepL_emit (mem_cs_re1 _ _ _)
                      (fun r2 => by rw [next_re1_zero, hstream]) _ _ _
                      (emitAction_apply_emissionTape hacc false)).trans
                      (stepL_headTape (mem_cs_re0 _) (fun _ => rfl)
                        (append_cons_ne_nil _ _ _) _ _))))
                (ih (List.append acc [false]) e1 L0 _
                  (streamFold?_snoc_some hacc hstream) hfold')
          | true =>
              have hfoldcons :
                  streamFold? e (true :: rest.filterMap id) = none :=
                hfold
              cases hstream : e.stream true with
              | none =>
                  refine
                    ⟨_, _,
                      (stepL (mem_cs_re3 _) (fun _ => rfl) _ _ _ _).trans
                        ((stepL (mem_cs_re2 _ _) (fun _ => rfl) _ _ _
                            _).trans
                          (stepL (mem_cs_re1 _ _ _)
                            (fun r2 => by rw [next_re1_one, hstream]) _ _
                            _ _))⟩
              | some e1 =>
                  have hfold' :
                      streamFold? e1 (rest.filterMap id) = none := by
                    rw [streamFold?_cons_of_stream_some _ hstream]
                      at hfoldcons
                    exact hfoldcons
                  refine leadsSpin_of_leads
                    ((stepL (mem_cs_re3 _) (fun _ => rfl) _ _ _ _).trans
                      ((stepL (mem_cs_re2 _ _) (fun _ => rfl) _ _ _
                          _).trans
                        ((stepL_emit (mem_cs_re1 _ _ _)
                          (fun r2 => by rw [next_re1_one, hstream]) _ _ _
                          (emitAction_apply_emissionTape hacc
                            true)).trans
                          (stepL_headTape (mem_cs_re0 _) (fun _ => rfl)
                            (append_cons_ne_nil _ _ _) _ _))))
                    (ih (List.append acc [true]) e1 L0 _
                      (streamFold?_snoc_some hacc hstream) hfold')

/-!
### The right-length rewind
-/

theorem next_rt1_marked (n : Nat) (v3 v2 : Bool) (e : Emission)
    (r2 : Option Bool) :
    CoreState.next n (CoreState.rt1 v3 v2 e) (some true) none r2 =
      some ⟨CoreState.hd0 v3 v2 e, keepL, keepS, keepS⟩ := by
  cases v3 <;> cases v2 <;> rfl

theorem tickBitsF_absorb (m : Nat) (X : List (Option Bool)) :
    some false :: some false :: some true :: some false ::
        tickBitsF m X =
      tickBitsF m
        (some false :: some false :: some true :: some false :: X) := by
  induction m generalizing X with
  | zero => rfl
  | succ m ih =>
      show
        some false :: some false :: some true :: some false ::
            (some false :: some false :: some true :: some false ::
              tickBitsF m X) = _
      rw [ih]
      rfl

/-- Rewind over the right-length ticks to the marked head cell. -/
theorem leads_rt (n : Nat) (m : Nat) {h : Option Bool} {v2 v3 : Bool}
    (hbits :
      tokBits (cellTok h) = [some false, some true, some v2, some v3]) :
    forall (L0 Racc : List (Option Bool)) (e : Emission) (T2 : Tape Bool),
      Leads n
        (coreCfg n (CoreState.rt0 e)
          (tapeAtCells
            (List.append (tickRevBits m)
              (List.append (markedBits h).reverse L0))
            (some false :: Racc)) T2)
        (coreCfg n (CoreState.hd0 v3 v2 e)
          (tapeAtCells L0
            (some true :: some true :: some v2 :: some v3 ::
              tickBitsF m (some false :: Racc))) T2) := by
  rw [markedBits_eq hbits]
  induction m with
  | zero =>
      intro L0 Racc e T2
      exact
        ((stepL (mem_cs_rt0 _) (fun _ => rfl) _ _ _ T2).trans
          ((stepL (mem_cs_rt3 _) (fun _ => rfl) _ _ _ T2).trans
            ((stepL (mem_cs_rt2 _ _) (fun _ => rfl) _ _ _ T2).trans
              (stepL (mem_cs_rt1 _ _ _)
                (fun r2 => next_rt1_marked n v3 v2 e r2) _ _ _ T2))))
  | succ m ih =>
      intro L0 Racc e T2
      rw [show
        tickBitsF (m + 1) (some false :: Racc) =
          tickBitsF m
            (some false :: some false :: some true :: some false ::
              some false :: Racc) from tickBitsF_absorb m _]
      refine Leads.trans
        (stepL (mem_cs_rt0 _) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_cs_rt3 _) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_cs_rt2 _ _) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_cs_rt1 _ _ _) (fun _ => rfl) _ _ _ T2) ?_
      exact ih L0 _ e T2

/-!
### Head emission, left-list skip, and the turnaround
-/

/-- Emit the marked head cell and step into the left-list skip. -/
theorem leads_hd_ok (n : Nat) (h : Option Bool) {v2 v3 : Bool}
    (hbits :
      tokBits (cellTok h) = [some false, some true, some v2, some v3])
    {acc : List Bool} {e e' : Emission}
    (hacc : streamFold? Emission.start acc = some e)
    (hstream : streamFold? e h.toList = some e')
    {LL : List (Option Bool)} (hLL : LL ≠ [])
    (cellsR : List (Option Bool)) :
    Leads n
      (coreCfg n (CoreState.hd0 v3 v2 e)
        (tapeAtCells LL (some true :: cellsR)) (emissionTape acc))
      (coreCfg n (CoreState.ls3 e')
        (headTape LL (some true :: cellsR))
        (emissionTape (List.append acc h.toList))) := by
  cases h with
  | none =>
      have hbits' :
          ([some false, some true, some false, some false] :
              List (Option Bool)) =
            [some false, some true, some v2, some v3] := hbits
      simp at hbits'
      obtain ⟨hv2, hv3⟩ := hbits'
      subst hv2
      subst hv3
      have he : e = e' := by simpa using hstream
      subst he
      rw [show List.append acc (Option.toList (none : Option Bool)) = acc
          from List.append_nil acc]
      exact
        stepL_headTape (mem_cs_hd0 _ _ _) (fun _ => rfl) hLL _
          (emissionTape acc)
  | some b =>
      have hsf : e.stream b = some e' := by
        cases hsb : e.stream b with
        | none =>
            rw [show (Option.toList (some b)) = [b] from rfl,
              streamFold?_cons_of_stream_none _ hsb] at hstream
            cases hstream
        | some e1 =>
            rw [show (Option.toList (some b)) = [b] from rfl,
              streamFold?_cons_of_stream_some _ hsb] at hstream
            have : e1 = e' := by simpa using hstream
            rw [← this]
      cases b with
      | false =>
          have hbits' :
              ([some false, some true, some false, some true] :
                  List (Option Bool)) =
                [some false, some true, some v2, some v3] := hbits
          simp at hbits'
          obtain ⟨hv2, hv3⟩ := hbits'
          subst hv2
          subst hv3
          exact
            stepL_emit_headTape (mem_cs_hd0 _ _ _)
              (fun r2 => by rw [next_hd0_zero, hsf]) hLL _
              (emitAction_apply_emissionTape hacc false)
      | true =>
          have hbits' :
              ([some false, some true, some true, some false] :
                  List (Option Bool)) =
                [some false, some true, some v2, some v3] := hbits
          simp at hbits'
          obtain ⟨hv2, hv3⟩ := hbits'
          subst hv2
          subst hv3
          exact
            stepL_emit_headTape (mem_cs_hd0 _ _ _)
              (fun r2 => by rw [next_hd0_one, hsf]) hLL _
              (emitAction_apply_emissionTape hacc true)

/-- Rejected head emission reaches the spin trap. -/
theorem leads_hd_spin (n : Nat) {v2 v3 : Bool} {e : Emission}
    (hv : v2 = true ∧ v3 = false)
    (hstream : e.stream true = none)
    (LL cellsR : List (Option Bool)) (acc : List Bool) :
    LeadsSpin n
      (coreCfg n (CoreState.hd0 v3 v2 e)
        (tapeAtCells LL (some true :: cellsR)) (emissionTape acc)) := by
  rw [hv.left, hv.right]
  exact
    ⟨_, _,
      leads_step (n := n) (T0 := tapeAtCells LL (some true :: cellsR))
        (T2 := emissionTape acc) (mem_cs_hd0 _ _ _)
        (by rw [show Tape.read (tapeAtCells LL (some true :: cellsR)) =
              some true from rfl,
            show Tape.read (emissionTape acc) = none from rfl,
            next_hd0_one, hstream])
        rfl rfl rfl⟩

/-- Skip the left cells leftward and turn at the length field. -/
theorem leads_ls (n : Nat) (lrev : List (Option Bool)) :
    forall (e : Emission) (Lrest cellsR : List (Option Bool))
      (T2 : Tape Bool),
      Leads n
        (coreCfg n (CoreState.ls3 e)
          (headTape
            (List.append (flatRevTokBits lrev)
              (List.append doneRevBits Lrest)) cellsR) T2)
        (coreCfg n (CoreState.le0 e)
          (tapeAtCells (pushBits doneBitsF Lrest)
            (unwalkBits lrev cellsR)) T2) := by
  induction lrev with
  | nil =>
      intro e Lrest cellsR T2
      exact
        ((stepL (mem_cs_ls3 _) (fun _ => rfl) _ _ _ T2).trans
          ((stepL (mem_cs_ls2 _) (fun _ => rfl) _ _ _ T2).trans
            ((stepR (mem_cs_ls1 _) (fun _ => rfl) _ _ T2).trans
              ((stepR (mem_cs_turn1 _) (fun _ => rfl) _ _ T2).trans
                (stepR (mem_cs_turn2 _) (fun _ => rfl) _ _ T2)))))
  | cons c rest ih =>
      intro e Lrest cellsR T2
      obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits c
      rw [flatRevTokBits_cons, hbits, unwalkBits_cons, hbits]
      refine Leads.trans
        (stepL (mem_cs_ls3 _) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_cs_ls2 _) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL (mem_cs_ls1 _) (fun _ => rfl) _ _ _ T2) ?_
      refine Leads.trans
        (stepL_headTape (mem_cs_ls0 _) (fun _ => rfl)
          (append_cons_ne_nil _ _ _) _ T2) ?_
      exact ih e Lrest _ T2

/-!
### The left-list forward emission
-/

/-- Emit the left cells rightward up to the marked head. -/
theorem leads_le_ok (n : Nat) (ls : List (Option Bool)) :
    forall (acc : List Bool) (e efin : Emission)
      (L R : List (Option Bool)),
      streamFold? Emission.start acc = some e ->
      streamFold? e (ls.filterMap id) = some efin ->
      Leads n
        (coreCfg n (CoreState.le0 e)
          (tapeAtCells L (List.append (codeBits (ls.map cellTok)) R))
          (emissionTape acc))
        (coreCfg n (CoreState.le0 efin)
          (tapeAtCells (pushBits (codeBits (ls.map cellTok)) L) R)
          (emissionTape (List.append acc (ls.filterMap id)))) := by
  induction ls with
  | nil =>
      intro acc e efin L R hacc hfold
      have hefin : e = efin := by simpa using hfold
      subst hefin
      rw [show List.append acc (List.filterMap id ([] : List (Option Bool))) =
        acc from List.append_nil acc]
      exact Leads.refl n _
  | cons c rest ih =>
      intro acc e efin L R hacc hfold
      cases c with
      | none =>
          refine Leads.trans
            (stepR (mem_cs_le0 _) (fun _ => rfl) _ _ _) ?_
          refine Leads.trans
            (stepR (mem_cs_le1 _) (fun _ => rfl) _ _ _) ?_
          refine Leads.trans
            (stepR (mem_cs_le2 _) (fun _ => rfl) _ _ _) ?_
          refine Leads.trans
            (stepR (mem_cs_le3 _ _) (fun _ => rfl) _ _ _) ?_
          exact ih acc e efin _ R hacc hfold
      | some b =>
          cases b with
          | false =>
              obtain ⟨e1, hstream⟩ := stream_false_some e
              have hfold' :
                  streamFold? e1 (rest.filterMap id) = some efin := by
                rw [show (((some false :: rest) :
                    List (Option Bool)).filterMap id) =
                    false :: rest.filterMap id from rfl] at hfold
                rw [streamFold?_cons_of_stream_some _ hstream] at hfold
                exact hfold
              rw [show List.append acc
                  (((some false :: rest) :
                    List (Option Bool)).filterMap id) =
                  List.append (List.append acc [false])
                    (rest.filterMap id) from
                (append_snoc_assoc acc false _).symm]
              refine Leads.trans
                (stepR (mem_cs_le0 _) (fun _ => rfl) _ _ _) ?_
              refine Leads.trans
                (stepR (mem_cs_le1 _) (fun _ => rfl) _ _ _) ?_
              refine Leads.trans
                (stepR (mem_cs_le2 _) (fun _ => rfl) _ _ _) ?_
              refine Leads.trans
                (stepR_emit (mem_cs_le3 _ _)
                  (fun r2 => by rw [next_le3_zero, hstream]) _ _ _
                  (emitAction_apply_emissionTape hacc false)) ?_
              exact
                ih (List.append acc [false]) e1 efin _ R
                  (streamFold?_snoc_some hacc hstream) hfold'
          | true =>
              have hfoldcons :
                  streamFold? e (true :: rest.filterMap id) =
                    some efin := hfold
              cases hstream : e.stream true with
              | none =>
                  rw [streamFold?_cons_of_stream_none _ hstream]
                    at hfoldcons
                  cases hfoldcons
              | some e1 =>
                  have hfold' :
                      streamFold? e1 (rest.filterMap id) = some efin := by
                    rw [streamFold?_cons_of_stream_some _ hstream]
                      at hfoldcons
                    exact hfoldcons
                  rw [show List.append acc
                      (((some true :: rest) :
                        List (Option Bool)).filterMap id) =
                      List.append (List.append acc [true])
                        (rest.filterMap id) from
                    (append_snoc_assoc acc true _).symm]
                  refine Leads.trans
                    (stepR (mem_cs_le0 _) (fun _ => rfl) _ _ _) ?_
                  refine Leads.trans
                    (stepR (mem_cs_le1 _) (fun _ => rfl) _ _ _) ?_
                  refine Leads.trans
                    (stepR (mem_cs_le2 _) (fun _ => rfl) _ _ _) ?_
                  refine Leads.trans
                    (stepR_emit (mem_cs_le3 _ _)
                      (fun r2 => by rw [next_le3_one, hstream]) _ _ _
                      (emitAction_apply_emissionTape hacc true)) ?_
                  exact
                    ih (List.append acc [true]) e1 efin _ R
                      (streamFold?_snoc_some hacc hstream) hfold'

/-- Rejected left-list emission reaches the spin trap. -/
theorem leads_le_spin (n : Nat) (ls : List (Option Bool)) :
    forall (acc : List Bool) (e : Emission) (L R : List (Option Bool)),
      streamFold? Emission.start acc = some e ->
      streamFold? e (ls.filterMap id) = none ->
      LeadsSpin n
        (coreCfg n (CoreState.le0 e)
          (tapeAtCells L (List.append (codeBits (ls.map cellTok)) R))
          (emissionTape acc)) := by
  induction ls with
  | nil =>
      intro acc e L R hacc hfold
      exact nomatch hfold
  | cons c rest ih =>
      intro acc e L R hacc hfold
      cases c with
      | none =>
          refine leadsSpin_of_leads
            ((stepR (mem_cs_le0 _) (fun _ => rfl) _ _ _).trans
              ((stepR (mem_cs_le1 _) (fun _ => rfl) _ _ _).trans
                ((stepR (mem_cs_le2 _) (fun _ => rfl) _ _ _).trans
                  (stepR (mem_cs_le3 _ _) (fun _ => rfl) _ _ _))))
            (ih acc e _ R hacc hfold)
      | some b =>
          cases b with
          | false =>
              obtain ⟨e1, hstream⟩ := stream_false_some e
              have hfold' :
                  streamFold? e1 (rest.filterMap id) = none := by
                rw [show (((some false :: rest) :
                    List (Option Bool)).filterMap id) =
                    false :: rest.filterMap id from rfl] at hfold
                rw [streamFold?_cons_of_stream_some _ hstream] at hfold
                exact hfold
              refine leadsSpin_of_leads
                ((stepR (mem_cs_le0 _) (fun _ => rfl) _ _ _).trans
                  ((stepR (mem_cs_le1 _) (fun _ => rfl) _ _ _).trans
                    ((stepR (mem_cs_le2 _) (fun _ => rfl) _ _ _).trans
                      (stepR_emit (mem_cs_le3 _ _)
                        (fun r2 => by rw [next_le3_zero, hstream]) _ _ _
                        (emitAction_apply_emissionTape hacc false)))))
                (ih (List.append acc [false]) e1 _ R
                  (streamFold?_snoc_some hacc hstream) hfold')
          | true =>
              have hfoldcons :
                  streamFold? e (true :: rest.filterMap id) = none :=
                hfold
              cases hstream : e.stream true with
              | none =>
                  refine
                    ⟨_, _,
                      (stepR (mem_cs_le0 _) (fun _ => rfl) _ _ _).trans
                        ((stepR (mem_cs_le1 _) (fun _ => rfl) _ _
                            _).trans
                          ((stepR (mem_cs_le2 _) (fun _ => rfl) _ _
                              _).trans
                            (stepR (mem_cs_le3 _ _)
                              (fun r2 => by
                                rw [next_le3_one, hstream]) _ _ _)))⟩
              | some e1 =>
                  have hfold' :
                      streamFold? e1 (rest.filterMap id) = none := by
                    rw [streamFold?_cons_of_stream_some _ hstream]
                      at hfoldcons
                    exact hfoldcons
                  refine leadsSpin_of_leads
                    ((stepR (mem_cs_le0 _) (fun _ => rfl) _ _ _).trans
                      ((stepR (mem_cs_le1 _) (fun _ => rfl) _ _ _).trans
                        ((stepR (mem_cs_le2 _) (fun _ => rfl) _ _
                            _).trans
                          (stepR_emit (mem_cs_le3 _ _)
                            (fun r2 => by rw [next_le3_one, hstream]) _ _
                            _
                            (emitAction_apply_emissionTape hacc true)))))
                    (ih (List.append acc [true]) e1 _ R
                      (streamFold?_snoc_some hacc hstream) hfold')

/-!
### The mark check
-/

/-- Restore the head mark and flush the held output bit. -/
theorem leads_markCheck_ok (n : Nat) {acc : List Bool} {e : Emission}
    (hacc : streamFold? Emission.start acc = some e)
    (hpos : e.pos = GroupPos.p0)
    {LL : List (Option Bool)} (hLL : LL ≠ [])
    (cellsR : List (Option Bool)) :
    Leads n
      (coreCfg n (CoreState.le0 e)
        (tapeAtCells LL (some true :: cellsR)) (emissionTape acc))
      (coreCfg n CoreState.rw3
        (headTape LL (some false :: cellsR))
        (Tape.input acc.reverse)) :=
  stepL_write_emit_headTape (mem_cs_le0 _)
    (fun r2 => by rw [next_le0_mark, hpos]) hLL _
    (flushAction_apply_emissionTape hacc)

/-- A misaligned stream total fails the mark check into the spin trap. -/
theorem leads_markCheck_spin (n : Nat) {e : Emission}
    (hpos : e.pos ≠ GroupPos.p0)
    (LL cellsR : List (Option Bool)) (T2 : Tape Bool) :
    LeadsSpin n
      (coreCfg n (CoreState.le0 e)
        (tapeAtCells LL (some true :: cellsR)) T2) := by
  have hnext :
      forall r2 : Option Bool,
        CoreState.next n (CoreState.le0 e) (some true) none r2 =
          some ⟨CoreState.spin, keepR, keepS, keepS⟩ := by
    intro r2
    rw [next_le0_mark]
    cases hp : e.pos
    · exact absurd hp hpos
    · rfl
    · rfl
    · rfl
  exact ⟨_, _, stepR (mem_cs_le0 _) hnext LL cellsR T2⟩

/-!
### The final rewind
-/

/-- Non-header tokens of a layout body. -/
def NonHeaderTok (t : MachineCodeSymbol) : Prop :=
  t = MachineCodeSymbol.tick ∨ t = MachineCodeSymbol.done ∨
    t = MachineCodeSymbol.blank ∨ t = MachineCodeSymbol.zero ∨
      t = MachineCodeSymbol.one

/-- Reversed window bits of a token run, in processing order. -/
def flatRevBitsT (toks : List MachineCodeSymbol) : List (Option Bool) :=
  toks.flatMap (fun t => (tokBits t).reverse)

@[simp] theorem flatRevBitsT_nil : flatRevBitsT [] = [] := rfl

theorem flatRevBitsT_cons (t : MachineCodeSymbol)
    (rest : List MachineCodeSymbol) :
    flatRevBitsT (t :: rest) =
      List.append (tokBits t).reverse (flatRevBitsT rest) := by
  simp [flatRevBitsT]

/-- Forward window bits of processed tokens, most recent first. -/
def unwalkBitsT (toks : List MachineCodeSymbol)
    (Racc : List (Option Bool)) : List (Option Bool) :=
  toks.foldl (fun R t => List.append (tokBits t) R) Racc

@[simp] theorem unwalkBitsT_nil (Racc : List (Option Bool)) :
    unwalkBitsT [] Racc = Racc := rfl

/-- Rewind leftward over the layout body to the header and halt. -/
theorem leads_rw (n : Nat) (toks : List MachineCodeSymbol) :
    (forall t, t ∈ toks -> NonHeaderTok t) ->
    forall (cellsR : List (Option Bool)) (T2 : Tape Bool),
      Leads n
        (coreCfg n CoreState.rw3
          (headTape
            (List.append (flatRevBitsT toks)
              (tokBits MachineCodeSymbol.header).reverse) cellsR) T2)
        (coreCfg n CoreState.halt
          (tapeAtCells []
            (List.append (tokBits MachineCodeSymbol.header)
              (unwalkBitsT toks cellsR))) T2) := by
  induction toks with
  | nil =>
      intro _ cellsR T2
      exact
        ((stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2).trans
          ((stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2).trans
            (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2)))
  | cons t rest ih =>
      intro hlay cellsR T2
      have ht : NonHeaderTok t := hlay t (List.mem_cons.mpr (Or.inl rfl))
      have hrest : forall u, u ∈ rest -> NonHeaderTok u := fun u hu =>
        hlay u (List.mem_cons.mpr (Or.inr hu))
      rw [flatRevBitsT_cons]
      rcases ht with ht | ht | ht | ht | ht <;> subst ht
      · refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL_headTape (mem_fixed (by decide)) (fun _ => rfl)
            (append_cons_ne_nil _ _ _) _ T2) ?_
        exact ih hrest _ T2
      · refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL_headTape (mem_fixed (by decide)) (fun _ => rfl)
            (append_cons_ne_nil _ _ _) _ T2) ?_
        exact ih hrest _ T2
      · refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL_headTape (mem_fixed (by decide)) (fun _ => rfl)
            (append_cons_ne_nil _ _ _) _ T2) ?_
        exact ih hrest _ T2
      · refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL_headTape (mem_fixed (by decide)) (fun _ => rfl)
            (append_cons_ne_nil _ _ _) _ T2) ?_
        exact ih hrest _ T2
      · refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL (mem_fixed (by decide)) (fun _ => rfl) _ _ _ T2) ?_
        refine Leads.trans
          (stepL_headTape (mem_fixed (by decide)) (fun _ => rfl)
            (append_cons_ne_nil _ _ _) _ T2) ?_
        exact ih hrest _ T2

/-!
## View bridges for the full composition

Rightward walks accumulate the left context through {lit}`pushBits`; the
leftward phases consume it in {lit}`flatRev` form and rebuild the window in
{lit}`unwalk` form.  These bridges convert between the three views.
-/

theorem pushBits_ne_nil {L : List (Option Bool)} (hL : L ≠ [])
    (bits : List (Option Bool)) : pushBits bits L ≠ [] := by
  induction bits generalizing L with
  | nil => exact hL
  | cons c rest ih =>
      rw [pushBits_cons]
      exact ih (by simp)

theorem codeBits_cells_reverse (cells : List (Option Bool)) :
    (codeBits (cells.map cellTok)).reverse =
      flatRevTokBits cells.reverse := by
  induction cells with
  | nil => rfl
  | cons c rest ih =>
      rw [show (c :: rest).map cellTok =
          cellTok c :: rest.map cellTok from rfl,
        codeBits_cons]
      rw [show (c :: rest).reverse = rest.reverse ++ [c] from by simp]
      rw [show flatRevTokBits (rest.reverse ++ [c]) =
          flatRevTokBits rest.reverse ++ flatRevTokBits [c] from by
        simp [flatRevTokBits]]
      rw [← ih]
      rw [show (flatRevTokBits [c] : List (Option Bool)) =
          (tokBits (cellTok c)).reverse from by
        simp [flatRevTokBits]]
      simp

theorem unwalkBits_reverse_eq (cells : List (Option Bool)) :
    forall X : List (Option Bool),
      unwalkBits cells.reverse X =
        List.append (codeBits (cells.map cellTok)) X := by
  induction cells with
  | nil =>
      intro X
      rfl
  | cons c rest ih =>
      intro X
      rw [show (c :: rest).reverse = rest.reverse ++ [c] from by simp]
      rw [show unwalkBits (rest.reverse ++ [c]) X =
          unwalkBits [c] (unwalkBits rest.reverse X) from by
        simp [unwalkBits]]
      rw [ih]
      rw [show unwalkBits [c]
          (List.append (codeBits (rest.map cellTok)) X) =
          List.append (tokBits (cellTok c))
            (List.append (codeBits (rest.map cellTok)) X) from rfl]
      rw [show (c :: rest).map cellTok =
          cellTok c :: rest.map cellTok from rfl, codeBits_cons]
      simp

theorem codeBits_reverse_flatT (body : Word MachineCodeSymbol) :
    (codeBits body).reverse = flatRevBitsT body.reverse := by
  induction body with
  | nil => rfl
  | cons t rest ih =>
      rw [codeBits_cons]
      rw [show (t :: rest).reverse = rest.reverse ++ [t] from by simp]
      rw [show flatRevBitsT (rest.reverse ++ [t]) =
          flatRevBitsT rest.reverse ++ flatRevBitsT [t] from by
        simp [flatRevBitsT]]
      rw [← ih]
      rw [show (flatRevBitsT [t] : List (Option Bool)) =
          (tokBits t).reverse from by simp [flatRevBitsT]]
      simp

theorem unwalkBitsT_reverse_eq (body : Word MachineCodeSymbol) :
    forall X : List (Option Bool),
      unwalkBitsT body.reverse X = List.append (codeBits body) X := by
  induction body with
  | nil =>
      intro X
      rfl
  | cons t rest ih =>
      intro X
      rw [show (t :: rest).reverse = rest.reverse ++ [t] from by simp]
      rw [show unwalkBitsT (rest.reverse ++ [t]) X =
          unwalkBitsT [t] (unwalkBitsT rest.reverse X) from by
        simp [unwalkBitsT]]
      rw [ih]
      rw [show unwalkBitsT [t] (List.append (codeBits rest) X) =
          List.append (tokBits t) (List.append (codeBits rest) X)
          from rfl]
      rw [codeBits_cons]
      simp

theorem tickRevBits_snoc (m : Nat) :
    List.append (tickRevBits m)
        [some false, some true, some false, some false] =
      tickRevBits (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      show
        some false :: some true :: some false :: some false ::
          List.append (tickRevBits m)
            [some false, some true, some false, some false] = _
      rw [ih]
      rfl

theorem codeBits_encodeNat_reverse (m : Nat) :
    (codeBits (encodeNat m)).reverse =
      List.append doneRevBits (tickRevBits m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [show encodeNat (m + 1) =
          MachineCodeSymbol.tick :: encodeNat m from rfl,
        codeBits_cons]
      rw [show tickRevBits (m + 1) =
          some false :: some true :: some false :: some false ::
            tickRevBits m from rfl]
      rw [show (List.append (tokBits MachineCodeSymbol.tick)
          (codeBits (encodeNat m))).reverse =
          (codeBits (encodeNat m)).reverse ++
            (tokBits MachineCodeSymbol.tick).reverse from by simp]
      rw [ih]
      rw [show ((tokBits MachineCodeSymbol.tick).reverse :
          List (Option Bool)) =
          [some false, some true, some false, some false] from rfl]
      rw [show (List.append doneRevBits (tickRevBits m) :
          List (Option Bool)) ++
          [some false, some true, some false, some false] =
          List.append doneRevBits
            (List.append (tickRevBits m)
              [some false, some true, some false, some false]) from by
        simp]
      rw [tickRevBits_snoc]
      rfl

theorem tickBitsF_doneBitsF (m : Nat) :
    forall Z : List (Option Bool),
      tickBitsF m (List.append doneBitsF Z) =
        List.append (codeBits (encodeNat m)) Z := by
  induction m with
  | zero =>
      intro Z
      rfl
  | succ m ih =>
      intro Z
      rw [show tickBitsF (m + 1) (List.append doneBitsF Z) =
          some false :: some false :: some true :: some false ::
            tickBitsF m (List.append doneBitsF Z) from rfl,
        ih]
      rw [show encodeNat (m + 1) =
          MachineCodeSymbol.tick :: encodeNat m from rfl,
        codeBits_cons]
      rfl

theorem nonHeaderTok_cellTok (c : Option Bool) :
    NonHeaderTok (cellTok c) := by
  cases c with
  | none => exact Or.inr (Or.inr (Or.inl rfl))
  | some b =>
      cases b with
      | false => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | true => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem nonHeaderTok_of_mem_cellToks {t : MachineCodeSymbol}
    {cells : List (Option Bool)}
    (h : List.Mem t (cells.map cellTok)) : NonHeaderTok t := by
  rcases List.mem_map.mp h with ⟨c, _, rfl⟩
  exact nonHeaderTok_cellTok c

theorem nonHeaderTok_of_mem_encodeNat {t : MachineCodeSymbol} :
    forall {m : Nat}, List.Mem t (encodeNat m) -> NonHeaderTok t := by
  intro m
  induction m with
  | zero =>
      intro h
      cases h with
      | head => exact Or.inr (Or.inl rfl)
      | tail _ h' => exact nomatch h'
  | succ m ih =>
      intro h
      cases h with
      | head => exact Or.inl rfl
      | tail _ h' => exact ih h'

/-- Walk one cell token with the {lit}`lb` loop. -/
theorem leads_lb_one (n : Nat) (c : Option Bool)
    (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.lb0
        (tapeAtCells L (List.append (tokBits (cellTok c)) R)) T2)
      (coreCfg n CoreState.lb0
        (tapeAtCells (pushBits (tokBits (cellTok c)) L) R) T2) := by
  obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits c
  rw [hbits]
  exact
    ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
      ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
          (stepR (mem_fixed (by decide)) (fun _ => rfl) _ R T2))))

/-- Walk one cell token with the {lit}`rb` loop. -/
theorem leads_rb_one (n : Nat) (c : Option Bool)
    (L R : List (Option Bool)) (T2 : Tape Bool) :
    Leads n
      (coreCfg n CoreState.rb0
        (tapeAtCells L (List.append (tokBits (cellTok c)) R)) T2)
      (coreCfg n CoreState.rb0
        (tapeAtCells (pushBits (tokBits (cellTok c)) L) R) T2) := by
  obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits c
  rw [hbits]
  exact
    ((stepR (mem_fixed (by decide)) (fun _ => rfl) L _ T2).trans
      ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
        ((stepR (mem_fixed (by decide)) (fun _ => rfl) _ _ T2).trans
          (stepR (mem_fixed (by decide)) (fun _ => rfl) _ R T2))))

/-!
## The full forward run
-/

/-- The bit stream the core emits for a configuration tape. -/
def layoutStream (T : Tape Bool) : List Bool :=
  List.append ((T.right.reverse).filterMap id)
    (List.append T.head.toList (T.left.filterMap id))

theorem layoutStream_reverse (T : Tape Bool) :
    (layoutStream T).reverse = Tape.normalizedOutput T := by
  cases T with
  | mk left head right =>
      cases head with
      | none =>
          simp [layoutStream, Tape.normalizedOutput, Tape.cells,
            List.filterMap_append, List.filterMap_reverse]
          rfl
      | some b =>
          simp [layoutStream, Tape.normalizedOutput, Tape.cells,
            List.filterMap_append, List.filterMap_reverse]
          rfl

/-- The token-level field decomposition of an encoded layout. -/
theorem encode_decomp (Lay : SimulatorLayout) :
    SimulatorLayout.encode Lay =
      MachineCodeSymbol.header ::
        List.append (encodeNat (Lay.input.map some).length)
          (List.append ((Lay.input.map some).map cellTok)
            (List.append (encodeNat Lay.stage)
              (List.append (encodeNat Lay.config.state)
                (List.append (encodeNat Lay.config.tape.left.length)
                  (List.append (Lay.config.tape.left.map cellTok)
                    (cellTok Lay.config.tape.head ::
                      List.append (encodeNat Lay.config.tape.right.length)
                        (List.append (Lay.config.tape.right.map cellTok)
                          (List.append [cellTok (some Lay.hit)]
                            ([] : Word MachineCodeSymbol))))))))) := by
  show
    MachineCodeSymbol.header ::
      encodeBoolWordAppend Lay.input
        (encodeNatAppend Lay.stage
          (encodeConfigurationAppend Lay.config
            (encodeBoolAppend Lay.hit []))) = _
  rw [show encodeBoolWordAppend Lay.input
      (encodeNatAppend Lay.stage
        (encodeConfigurationAppend Lay.config
          (encodeBoolAppend Lay.hit []))) =
      List.append (encodeNat (Lay.input.map some).length)
        (encodeCellsAppend (Lay.input.map some)
          (encodeNatAppend Lay.stage
            (encodeConfigurationAppend Lay.config
              (encodeBoolAppend Lay.hit [])))) from rfl]
  rw [encodeCellsAppend_eq_map]
  rw [show encodeConfigurationAppend Lay.config
      (encodeBoolAppend Lay.hit []) =
      List.append (encodeNat Lay.config.state)
        (encodeCellListAppend Lay.config.tape.left
          (encodeCellAppend Lay.config.tape.head
            (encodeCellListAppend Lay.config.tape.right
              (encodeBoolAppend Lay.hit [])))) from rfl]
  rw [show encodeCellListAppend Lay.config.tape.left
      (encodeCellAppend Lay.config.tape.head
        (encodeCellListAppend Lay.config.tape.right
          (encodeBoolAppend Lay.hit []))) =
      List.append (encodeNat Lay.config.tape.left.length)
        (encodeCellsAppend Lay.config.tape.left
          (encodeCellAppend Lay.config.tape.head
            (encodeCellListAppend Lay.config.tape.right
              (encodeBoolAppend Lay.hit [])))) from rfl]
  rw [encodeCellsAppend_eq_map]
  rw [show encodeCellAppend Lay.config.tape.head
      (encodeCellListAppend Lay.config.tape.right
        (encodeBoolAppend Lay.hit [])) =
      List.append (encodeCell Lay.config.tape.head)
        (encodeCellListAppend Lay.config.tape.right
          (encodeBoolAppend Lay.hit [])) from rfl,
    encodeCell_eq]
  rw [show encodeCellListAppend Lay.config.tape.right
      (encodeBoolAppend Lay.hit []) =
      List.append (encodeNat Lay.config.tape.right.length)
        (encodeCellsAppend Lay.config.tape.right
          (encodeBoolAppend Lay.hit [])) from rfl]
  rw [encodeCellsAppend_eq_map]
  rw [show encodeBoolAppend Lay.hit [] =
      List.append (encodeCell (some Lay.hit)) [] from rfl,
    encodeCell_eq]
  rfl

theorem reverse_append_explicit {α : Type _} (a b : List α) :
    (List.append a b).reverse = List.append b.reverse a.reverse :=
  @List.reverse_append α a b

theorem append_assoc_explicit {α : Type _} (a b c : List α) :
    List.append (List.append a b) c =
      List.append a (List.append b c) :=
  List.append_assoc a b c

theorem nil_append_explicit {α : Type _} (a : List α) :
    List.append [] a = a := rfl

theorem append_nil_explicit {α : Type _} (a : List α) :
    List.append a [] = a := List.append_nil a

theorem reverse_append_six {α : Type _}
    (a b c d e f : List α) :
    (List.append a
      (List.append b
        (List.append c (List.append d (List.append e f))))).reverse =
      List.append f.reverse
        (List.append e.reverse
          (List.append d.reverse
            (List.append c.reverse
              (List.append b.reverse a.reverse)))) := by
  rw [reverse_append_explicit]
  rw [reverse_append_explicit]
  rw [reverse_append_explicit]
  rw [reverse_append_explicit]
  rw [reverse_append_explicit]
  rw [append_assoc_explicit]
  rw [append_assoc_explicit]
  rw [append_assoc_explicit]
  rw [append_assoc_explicit]
  done

theorem codeBits_append_six_reverse
    (a b c d e f : Word MachineCodeSymbol) :
    (codeBits
      (List.append a
        (List.append b
          (List.append c (List.append d (List.append e f)))))).reverse =
      List.append (codeBits f).reverse
        (List.append (codeBits e).reverse
          (List.append (codeBits d).reverse
            (List.append (codeBits c).reverse
              (List.append (codeBits b).reverse
                (codeBits a).reverse)))) := by
  rw [codeBits_append a, codeBits_append b, codeBits_append c,
    codeBits_append d, codeBits_append e]
  exact reverse_append_six _ _ _ _ _ _

theorem codeBits_append_six
    (a b c d e f : Word MachineCodeSymbol) :
    codeBits
        (List.append a
          (List.append b
            (List.append c (List.append d (List.append e f))))) =
      List.append (codeBits a)
        (List.append (codeBits b)
          (List.append (codeBits c)
            (List.append (codeBits d)
              (List.append (codeBits e) (codeBits f))))) := by
  rw [codeBits_append a, codeBits_append b, codeBits_append c,
    codeBits_append d, codeBits_append e]

/-- The full valid-layout forward run to the halt state. -/
theorem leads_halt_of_valid (n : Nat) (Lay : SimulatorLayout)
    (hstate : Lay.config.state = n)
    {efin : Emission}
    (hfold :
      streamFold? Emission.start (layoutStream Lay.config.tape) =
        some efin)
    (hpos : efin.pos = GroupPos.p0) :
    Leads n
      (coreCfg n CoreState.hdr0
        (tapeAtCells [] (codeBits (SimulatorLayout.encode Lay)))
        Tape.blank)
      (coreCfg n CoreState.halt
        (tapeAtCells []
          (List.append (codeBits (SimulatorLayout.encode Lay)) [none]))
        (Tape.input (layoutStream Lay.config.tape).reverse)) := by
  -- Forward composition (phase lemmas above are all proven; this assembly
  -- needs a normalization pass to thread the accumulated pushBits context
  -- through the leftward emission phases).  Phase sequence:
  --   leads_header · leads_inLen · leads_inBits_stage · leads_chk_accept ·
  --   leads_lLen · leads_lb · leads_lb_one · leads_mark_rLen · leads_rb ·
  --   leads_rb_one · leads_endTurn · stepL_headTape ·
  --   (context bridge via pushBits_eq_reverse_append/codeBits_cells_reverse/
  --    codeBits_encodeNat_reverse) · leads_re_ok · leads_rt · (bridge) ·
  --   leads_hd_ok · leads_ls · leads_le_ok · leads_markCheck_ok · leads_rw.
  -- Tape-2 accumulator threaded by hfold1/hfold2/hfold3 (= streamFold?
  -- splits of layoutStream), final tape-2 = Tape.input layoutStream.reverse.
  rw [encode_decomp]
  rw [codeBits_cons]
  refine Leads.trans (leads_header n [] _ Tape.blank) ?_
  rw [codeBits_append]
  refine Leads.trans (leads_inLen n _ _ _ Tape.blank) ?_
  rw [codeBits_append]
  rw [codeBits_append]
  refine Leads.trans (leads_inBits_stage n Lay.input Lay.stage _ _ Tape.blank) ?_
  rw [codeBits_append]
  have hstate' : 0 + Lay.config.state = n := by simpa using hstate
  refine Leads.trans
    (leads_chk_accept n Lay.config.state 0 hstate' _ _ Tape.blank) ?_
  rw [codeBits_append]
  refine Leads.trans
    (leads_lLen n Lay.config.tape.left.length _ _ Tape.blank) ?_
  rw [codeBits_append]
  refine Leads.trans
    (leads_lb n Lay.config.tape.left _ _ Tape.blank) ?_
  rw [codeBits_cons]
  refine Leads.trans
    (leads_lb_one n Lay.config.tape.head _ _ Tape.blank) ?_
  rw [codeBits_append]
  refine Leads.trans
    (leads_mark_rLen n Lay.config.tape.head
      Lay.config.tape.right.length _ _ Tape.blank) ?_
  rw [codeBits_append]
  refine Leads.trans
    (leads_rb n Lay.config.tape.right _ _ Tape.blank) ?_
  have hhit :
      List.append [cellTok (some Lay.hit)]
          ([] : Word MachineCodeSymbol) =
        [cellTok (some Lay.hit)] := by rfl
  rw [hhit, codeBits_cons, codeBits_nil]
  refine Leads.trans
    (leads_rb_one n (some Lay.hit) _ [] Tape.blank) ?_
  refine Leads.trans (leads_endTurn n Lay.hit _ Tape.blank) ?_
  have hmark :
      pushBits (markedBits Lay.config.tape.head)
          (pushBits (codeBits (Lay.config.tape.left.map cellTok))
            (pushBits (codeBits (encodeNat Lay.config.tape.left.length))
              (pushBits (codeBits (encodeNat Lay.config.state))
                (pushBits (codeBits (encodeNat Lay.stage))
                  (pushBits
                    (codeBits ((Lay.input.map some).map cellTok))
                    (pushBits
                      (codeBits (encodeNat (Lay.input.map some).length))
                      (pushBits (tokBits MachineCodeSymbol.header)
                        []))))))) ≠ [] := by
    simp [markedBits, pushBits]
  have hrlen :=
    pushBits_ne_nil hmark
      (codeBits (encodeNat Lay.config.tape.right.length))
  have hfull :=
    pushBits_ne_nil hrlen
      (codeBits (Lay.config.tape.right.map cellTok))
  obtain ⟨hitv2, hitv3, hhitbits⟩ :=
    exists_cellTok_bits (some Lay.hit)
  rw [hhitbits]
  refine Leads.trans
    (stepL_headTape (n := n) (mem_fixed (by decide))
      (fun _ => rfl) hfull _ Tape.blank) ?_
  rw [layoutStream] at hfold
  rcases streamFold?_append_some hfold with
    ⟨eR, hfoldR, hfoldHL⟩
  rcases streamFold?_append_some hfoldHL with
    ⟨eH, hfoldH, hfoldL⟩
  simp only [pushBits_eq_reverse_append, codeBits_cells_reverse,
    codeBits_encodeNat_reverse]
  refine Leads.trans
    (leads_re_ok n Lay.config.tape.right.reverse
      [] Emission.start eR _ _ rfl hfoldR) ?_
  obtain ⟨headv2, headv3, hheadbits⟩ :=
    exists_cellTok_bits Lay.config.tape.head
  refine Leads.trans
    (leads_rt n Lay.config.tape.right.length hheadbits
      _ _ eR _) ?_
  refine Leads.trans
    (leads_hd_ok n Lay.config.tape.head hheadbits
      hfoldR hfoldH (append_cons_ne_nil _ _ _) _) ?_
  refine Leads.trans
    (leads_ls n Lay.config.tape.left.reverse eH _ _ _) ?_
  rw [unwalkBits_reverse_eq]
  have hfoldRH :
      streamFold? Emission.start
      (List.append (Lay.config.tape.right.reverse.filterMap id)
            Lay.config.tape.head.toList) = some eH := by
    rw [streamFold?_append, hfoldR]
    exact hfoldH
  refine Leads.trans
    (leads_le_ok n Lay.config.tape.left _ eH efin _ _
      hfoldRH hfoldL) ?_
  have hfoldAll :
      streamFold? Emission.start
          (List.append
            (List.append (Lay.config.tape.right.reverse.filterMap id)
              Lay.config.tape.head.toList)
            (Lay.config.tape.left.filterMap id)) = some efin := by
    rw [streamFold?_append, hfoldRH]
    exact hfoldL
  refine Leads.trans
    (leads_markCheck_ok n hfoldAll hpos
      (pushBits_ne_nil (by simp [doneBitsF, pushBits]) _) _) ?_
  simp only [pushBits_eq_reverse_append]
  let inputList : List Bool := Lay.input
  let inputCells : List (Option Bool) := inputList.map some
  let inCells : Word MachineCodeSymbol :=
    inputCells.map cellTok
  let lCells : Word MachineCodeSymbol :=
    Lay.config.tape.left.map cellTok
  let rCells : Word MachineCodeSymbol :=
    Lay.config.tape.right.map cellTok
  let inputLenCode : Word MachineCodeSymbol := encodeNat inputCells.length
  let stageCode : Word MachineCodeSymbol := encodeNat Lay.stage
  let stateCode : Word MachineCodeSymbol := encodeNat Lay.config.state
  let leftLenCode : Word MachineCodeSymbol :=
    encodeNat Lay.config.tape.left.length
  let rightLenCode : Word MachineCodeSymbol :=
    encodeNat Lay.config.tape.right.length
  let pre : Word MachineCodeSymbol :=
    List.append inputLenCode
      (List.append inCells
        (List.append stageCode
          (List.append stateCode (List.append leftLenCode lCells))))
  have hInputLen :
      (codeBits inputLenCode).reverse =
        List.append doneRevBits (tickRevBits inputCells.length) :=
    codeBits_encodeNat_reverse inputCells.length
  have hStage :
      (codeBits stageCode).reverse =
        List.append doneRevBits (tickRevBits Lay.stage) :=
    codeBits_encodeNat_reverse Lay.stage
  have hState :
      (codeBits stateCode).reverse =
        List.append doneRevBits (tickRevBits Lay.config.state) :=
    codeBits_encodeNat_reverse Lay.config.state
  have hLeftLen :
      (codeBits leftLenCode).reverse =
        List.append doneRevBits
          (tickRevBits Lay.config.tape.left.length) :=
    codeBits_encodeNat_reverse Lay.config.tape.left.length
  have hInCells :
      (codeBits inCells).reverse =
        flatRevTokBits inputCells.reverse :=
    codeBits_cells_reverse inputCells
  have hDone : doneBitsF.reverse = doneRevBits := rfl
  have hRightLen (Z : List (Option Bool)) :
      tickBitsF Lay.config.tape.right.length
          (some false ::
            List.append [some false, some true, some true] Z) =
        List.append (codeBits rightLenCode) Z := by
    change
      tickBitsF Lay.config.tape.right.length
          (List.append doneBitsF Z) =
        List.append
          (codeBits (encodeNat Lay.config.tape.right.length)) Z
    exact tickBitsF_doneBitsF Lay.config.tape.right.length Z
  have hview :
      List.append (codeBits lCells).reverse
          (List.append doneBitsF.reverse
            (List.append
              (List.append []
                (tickRevBits Lay.config.tape.left.length))
              (List.append
                (List.append doneRevBits
                  (tickRevBits Lay.config.state))
                (List.append
                  (List.append doneRevBits (tickRevBits Lay.stage))
                  (List.append
                    (flatRevTokBits inputCells.reverse)
                    (List.append
                      (List.append doneRevBits
                        (tickRevBits inputCells.length))
                      (List.append
                        (tokBits MachineCodeSymbol.header).reverse
                        []))))))) =
        List.append (flatRevBitsT pre.reverse)
          (tokBits MachineCodeSymbol.header).reverse := by
    rw [← codeBits_reverse_flatT pre]
    rw [codeBits_append_six_reverse inputLenCode inCells stageCode
      stateCode leftLenCode lCells]
    rw [hLeftLen, hState, hStage, hInCells, hInputLen]
    rw [hDone]
    rw [nil_append_explicit, append_nil_explicit]
    repeat' rw [append_assoc_explicit]
    done
  rw [hview]
  have hpreNon :
      forall t, List.Mem t pre.reverse -> NonHeaderTok t := by
    intro t ht
    have ht' : List.Mem t pre := List.mem_reverse.mp ht
    dsimp [pre] at ht'
    rcases List.mem_append.mp ht' with h | ht'
    · change List.Mem t (encodeNat inputCells.length) at h
      exact nonHeaderTok_of_mem_encodeNat h
    · rcases List.mem_append.mp ht' with h | ht'
      · change List.Mem t (inputCells.map cellTok) at h
        exact nonHeaderTok_of_mem_cellToks h
      · rcases List.mem_append.mp ht' with h | ht'
        · change List.Mem t (encodeNat Lay.stage) at h
          exact nonHeaderTok_of_mem_encodeNat h
        · rcases List.mem_append.mp ht' with h | ht'
          · change List.Mem t (encodeNat Lay.config.state) at h
            exact nonHeaderTok_of_mem_encodeNat h
          · rcases List.mem_append.mp ht' with h | h
            · change List.Mem t
                (encodeNat Lay.config.tape.left.length) at h
              exact nonHeaderTok_of_mem_encodeNat h
            · change List.Mem t
                (Lay.config.tape.left.map cellTok) at h
              exact nonHeaderTok_of_mem_cellToks h
  have hTail :
      (some false ::
        some true ::
          some headv2 ::
            some headv3 ::
              tickBitsF Lay.config.tape.right.length
                (some false ::
                  List.append [some false, some true, some true]
                    (List.append (codeBits rCells)
                      (some false ::
                        List.append [some true, some hitv2, some hitv3]
                          [none])))) =
        List.append (tokBits (cellTok Lay.config.tape.head))
          (List.append (codeBits rightLenCode)
            (List.append (codeBits rCells)
              (List.append (tokBits (cellTok (some Lay.hit)))
                [none]))) := by
    rw [hRightLen, hheadbits, hhitbits]
    rfl
    done
  refine Leads.trans
    (leads_rw n pre.reverse hpreNon _ _) ?_
  rw [unwalkBitsT_reverse_eq]
  rw [codeBits_append_six inputLenCode inCells stageCode stateCode
    leftLenCode lCells]
  rw [unwalkBits_reverse_eq]
  rw [hTail]
  simp only [inputList, inputCells, inCells, lCells, rCells, inputLenCode,
    stageCode, stateCode, leftLenCode, rightLenCode, hhitbits, layoutStream]
  repeat' rw [append_assoc_explicit]
  rw [nil_append_explicit]
  exact Leads.refl n _

end FuelOutputCore

end StructuredConstructionTargets

end Computability
end FoC
