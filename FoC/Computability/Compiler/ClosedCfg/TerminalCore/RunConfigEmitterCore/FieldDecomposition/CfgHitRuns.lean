import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.ConfigHit
import FoC.Computability.Compiler.Structured.Lowering.TypedStateRuns

set_option doc.verso true

/-!
# Exact configuration and hit materializer runs

Run proofs for the typed table in {lit}`ConfigHit.lean`.  The proof follows
the physical phases of the machine: erase the preserved prefix, copy the
configuration/hit suffix to tape 2, mark the encoded head, reconstruct the
exact logical configuration on tape 0, erase the temporary workspace, and
restore the saved hit.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition
namespace MetadataPrefix
namespace ConfigTapeAndHit

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open StructuredConstructionTargets.FuelOutputCore

def cfg (s : State) (T0 T1 T2 : Tape Bool) :
    CommonGround.FiniteTransducers.Structured.Configuration :=
  table.config s T0 T1 T2

def Leads
    (c d : CommonGround.FiniteTransducers.Structured.Configuration) : Prop :=
  table.Leads c d

namespace Leads

theorem refl
    (c : CommonGround.FiniteTransducers.Structured.Configuration) :
    Leads c c :=
  TypedStateTable.Leads.refl table c

theorem trans
    {c d e : CommonGround.FiniteTransducers.Structured.Configuration}
    (hcd : Leads c d) (hde : Leads d e) : Leads c e :=
  TypedStateTable.Leads.trans hcd hde

theorem to_runConfig
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (h : Leads c d) :
    exists steps : Nat, description.runConfig steps c = d :=
  TypedStateTable.Leads.to_runConfig h

end Leads

theorem leads_step
    {s target : State} (hs : s ∈ states)
    {T0 T1 T2 : Tape Bool} {a0 a1 a2 : TapeAction}
    (hnext :
      next s (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some ⟨target, a0, a1, a2⟩)
    {T0' T1' T2' : Tape Bool}
    (h0 : a0.apply T0 = T0')
    (h1 : a1.apply T1 = T1')
    (h2 : a2.apply T2 = T2') :
    Leads (cfg s T0 T1 T2) (cfg target T0' T1' T2') :=
  TypedStateTable.leads_step table hs hnext h0 h1 h2

/-- Blanks accumulated on tape 0 while a Boolean prefix is erased. -/
def pushBlanks
    (bits left : List (Option Bool)) : List (Option Bool) :=
  bits.foldl (fun acc _ => none :: acc) left

theorem pushBlanks_cons
    (bit : Option Bool) (bits left : List (Option Bool)) :
    pushBlanks (bit :: bits) left = pushBlanks bits (none :: left) := rfl

theorem pushBlanks_eq_replicate_append
    (bits left : List (Option Bool)) :
    pushBlanks bits left =
      List.append (List.replicate bits.length none) left := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit rest ih =>
      rw [pushBlanks_cons, ih]
      simpa [List.replicate_succ, List.append_assoc] using
        (FoC.Computability.list_replicate_append_self
          (none : Option Bool) rest.length left)

/-- Erase the current tape-0 cell and move right, preserving tapes 1 and 2. -/
theorem stepR_erase
    {s target : State} (hs : s ∈ states) {cell : Option Bool}
    (hnext : forall r1 r2 : Option Bool,
      next s cell r1 r2 =
        some ⟨target, writeR none, keepS, keepS⟩)
    (left right : List (Option Bool)) (T1 T2 : Tape Bool) :
    Leads
      (cfg s (tapeAtCells left (cell :: right)) T1 T2)
      (cfg target (tapeAtCells (none :: left) right) T1 T2) :=
  leads_step (s := s) (target := target) hs
    (T0 := tapeAtCells left (cell :: right)) (T1 := T1) (T2 := T2)
    (a0 := writeR (none : Option Bool)) (a1 := keepS) (a2 := keepS)
    (hnext (Tape.read T1) (Tape.read T2))
    (writeR_apply_tapeAtCells none left cell right) rfl rfl

/-!
## Prefix erasure
-/

/-- Erase the fixed header token. -/
theorem leads_header
    (left right : List (Option Bool)) (T1 T2 : Tape Bool) :
    Leads
      (cfg .hdr0
        (tapeAtCells left
          (List.append (tokBits MachineCodeSymbol.header) right)) T1 T2)
      (cfg .inLen0
        (tapeAtCells
          (pushBlanks (tokBits MachineCodeSymbol.header) left) right) T1 T2) :=
  (stepR_erase (state_mem .hdr0) (fun _ _ => rfl) left _ T1 T2).trans
    ((stepR_erase (state_mem .hdr1) (fun _ _ => rfl) _ _ T1 T2).trans
      ((stepR_erase (state_mem .hdr2) (fun _ _ => rfl) _ _ T1 T2).trans
        (stepR_erase (state_mem .hdr3) (fun _ _ => rfl) _ right T1 T2)))

/-- Erase one unary natural field. -/
theorem leads_inLen
    (n : Nat) (left right : List (Option Bool)) (T1 T2 : Tape Bool) :
    Leads
      (cfg .inLen0
        (tapeAtCells left (List.append (codeBits (encodeNat n)) right)) T1 T2)
      (cfg .inBits0
        (tapeAtCells (pushBlanks (codeBits (encodeNat n)) left) right) T1 T2) := by
  induction n generalizing left with
  | zero =>
      exact
        (stepR_erase (state_mem .inLen0) (fun _ _ => rfl) left _ T1 T2).trans
          ((stepR_erase (state_mem .inLen1) (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_erase (state_mem .inLen2) (fun _ _ => rfl) _ _ T1 T2).trans
              (stepR_erase (state_mem .inLen3) (fun _ _ => rfl) _ right T1 T2)))
  | succ n ih =>
      exact
        (stepR_erase (state_mem .inLen0) (fun _ _ => rfl) left _ T1 T2).trans
          ((stepR_erase (state_mem .inLen1) (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_erase (state_mem .inLen2) (fun _ _ => rfl) _ _ T1 T2).trans
              ((stepR_erase (state_mem .inLen3) (fun _ _ => rfl) _ _ T1 T2).trans
                (ih _))))

/-- Erase the stage field from a whole-token boundary. -/
theorem leads_stage
    (n : Nat) (left right : List (Option Bool)) (T1 T2 : Tape Bool) :
    Leads
      (cfg .stage0
        (tapeAtCells left (List.append (codeBits (encodeNat n)) right)) T1 T2)
      (cfg .rawState0
        (tapeAtCells (pushBlanks (codeBits (encodeNat n)) left) right) T1 T2) := by
  induction n generalizing left with
  | zero =>
      exact
        (stepR_erase (state_mem .stage0) (fun _ _ => rfl) left _ T1 T2).trans
          ((stepR_erase (state_mem .stage1) (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_erase (state_mem .stage2) (fun _ _ => rfl) _ _ T1 T2).trans
              (stepR_erase (state_mem .stage3) (fun _ _ => rfl) _ right T1 T2)))
  | succ n ih =>
      exact
        (stepR_erase (state_mem .stage0) (fun _ _ => rfl) left _ T1 T2).trans
          ((stepR_erase (state_mem .stage1) (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_erase (state_mem .stage2) (fun _ _ => rfl) _ _ T1 T2).trans
              ((stepR_erase (state_mem .stage3) (fun _ _ => rfl) _ _ T1 T2).trans
                (ih _))))

/-- Erase the raw configuration-state field. -/
theorem leads_rawState
    (n : Nat) (left right : List (Option Bool)) (T1 T2 : Tape Bool) :
    Leads
      (cfg .rawState0
        (tapeAtCells left (List.append (codeBits (encodeNat n)) right)) T1 T2)
      (cfg .gap1
        (tapeAtCells (pushBlanks (codeBits (encodeNat n)) left) right) T1 T2) := by
  induction n generalizing left with
  | zero =>
      exact
        (stepR_erase (state_mem .rawState0) (fun _ _ => rfl) left _ T1 T2).trans
          ((stepR_erase (state_mem .rawState1) (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_erase (state_mem .rawState2) (fun _ _ => rfl) _ _ T1 T2).trans
              (stepR_erase (state_mem .rawState3) (fun _ _ => rfl) _ right T1 T2)))
  | succ n ih =>
      exact
        (stepR_erase (state_mem .rawState0) (fun _ _ => rfl) left _ T1 T2).trans
          ((stepR_erase (state_mem .rawState1) (fun _ _ => rfl) _ _ T1 T2).trans
            ((stepR_erase (state_mem .rawState2) (fun _ _ => rfl) _ _ T1 T2).trans
              ((stepR_erase (state_mem .rawState3) (fun _ _ => rfl) _ _ T1 T2).trans
                (ih _))))

/-- Erase the input cell tokens, fall through the first two stage-token bits,
and finish erasing the stage field. -/
theorem leads_inBits_stage
    (input : Word Bool) (stage : Nat)
    (left right : List (Option Bool)) (T1 T2 : Tape Bool) :
    Leads
      (cfg .inBits0
        (tapeAtCells left
          (List.append (codeBits ((input.map some).map cellTok))
            (List.append (codeBits (encodeNat stage)) right))) T1 T2)
      (cfg .rawState0
        (tapeAtCells
          (pushBlanks (codeBits (encodeNat stage))
            (pushBlanks (codeBits ((input.map some).map cellTok)) left))
          right) T1 T2) := by
  induction input generalizing left with
  | nil =>
      cases stage with
      | zero =>
          exact
            (stepR_erase (state_mem .inBits0) (fun _ _ => rfl) left _ T1 T2).trans
              ((stepR_erase (state_mem .inBits1) (fun _ _ => rfl) _ _ T1 T2).trans
                ((stepR_erase (state_mem .stage2) (fun _ _ => rfl) _ _ T1 T2).trans
                  (stepR_erase (state_mem .stage3) (fun _ _ => rfl) _ right T1 T2)))
      | succ n =>
          exact
            (stepR_erase (state_mem .inBits0) (fun _ _ => rfl) left _ T1 T2).trans
              ((stepR_erase (state_mem .inBits1) (fun _ _ => rfl) _ _ T1 T2).trans
                ((stepR_erase (state_mem .stage2) (fun _ _ => rfl) _ _ T1 T2).trans
                  ((stepR_erase (state_mem .stage3) (fun _ _ => rfl) _ _ T1 T2).trans
                    (leads_stage n _ right T1 T2))))
  | cons bit rest ih =>
      cases bit with
      | false =>
          exact
            (stepR_erase (state_mem .inBits0) (fun _ _ => rfl) left _ T1 T2).trans
              ((stepR_erase (state_mem .inBits1) (fun _ _ => rfl) _ _ T1 T2).trans
                ((stepR_erase (state_mem .inBits2) (fun _ _ => rfl) _ _ T1 T2).trans
                  ((stepR_erase (state_mem .inBits3) (fun _ _ => rfl) _ _ T1 T2).trans
                    (ih _))))
      | true =>
          exact
            (stepR_erase (state_mem .inBits0) (fun _ _ => rfl) left _ T1 T2).trans
              ((stepR_erase (state_mem .inBits1) (fun _ _ => rfl) _ _ T1 T2).trans
                ((stepR_erase (state_mem .inBits2) (fun _ _ => rfl) _ _ T1 T2).trans
                  ((stepR_erase (state_mem .inBits3) (fun _ _ => rfl) _ _ T1 T2).trans
                    (ih _))))

/-- Tape-0 left context after erasing the header, input, stage, and raw state. -/
def erasedPrefixLeft (L : SimulatorLayout) : List (Option Bool) :=
  pushBlanks (codeBits (encodeNat L.config.state))
    (pushBlanks (codeBits (encodeNat L.stage))
      (pushBlanks (codeBits ((L.input.map some).map cellTok))
        (pushBlanks (codeBits (encodeNat (L.input.map some).length))
          (pushBlanks (tokBits MachineCodeSymbol.header) [none]))))

/-- Reach the first configuration-field bit with the encoded prefix erased. -/
theorem leads_prefix_layout
    (L : SimulatorLayout) (T1 T2 : Tape Bool) :
    Leads
      (cfg .hdr0 (headerStartTape L) T1 T2)
      (cfg .gap1
        (tapeAtCells (erasedPrefixLeft L)
          (List.append (codeBits (StateSelector.postStateTokens L)) [none]))
        T1 T2) := by
  rw [headerStartTape]
  rw [StageCounter.rightEdgeTape_eq_decomposed]
  rw [StateSelector.postStageTokens_eq_state_append]
  rw [codeBits_append]
  have hstateSuffix :
      List.append
          (List.append (codeBits (encodeNat L.config.state))
            (codeBits (StateSelector.postStateTokens L)))
          [none] =
        List.append (codeBits (encodeNat L.config.state))
          (List.append (codeBits (StateSelector.postStateTokens L))
            [none]) :=
    List.append_assoc _ _ _
  rw [hstateSuffix]
  refine Leads.trans (leads_header [none] _ T1 T2) ?_
  refine Leads.trans
    (leads_inLen (L.input.map some).length _ _ T1 T2) ?_
  refine Leads.trans (leads_inBits_stage L.input L.stage _ _ T1 T2) ?_
  exact leads_rawState L.config.state _ _ T1 T2

/-!
## Configuration-suffix workspace
-/

/-- Move tape 2 right once, preserving tapes 0 and 1. -/
theorem step2R
    {s target : State} (hs : s ∈ states) {cell : Option Bool}
    (hnext : forall r0 r1 : Option Bool,
      next s r0 r1 cell =
        some ⟨target, keepS, keepS, keepR⟩)
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    Leads
      (cfg s T0 T1 (tapeAtCells left (cell :: right)))
      (cfg target T0 T1 (tapeAtCells (cell :: left) right)) :=
  leads_step (s := s) (target := target) hs
    (T0 := T0) (T1 := T1) (T2 := tapeAtCells left (cell :: right))
    (a0 := keepS) (a1 := keepS) (a2 := keepR)
    (hnext (Tape.read T0) (Tape.read T1)) rfl rfl
    (keepR_apply_tapeAtCells left cell right)

/-- Write the current tape-2 cell and move right. -/
theorem step2R_write
    {s target : State} (hs : s ∈ states)
    {cell value : Option Bool}
    (hnext : forall r0 r1 : Option Bool,
      next s r0 r1 cell =
        some ⟨target, keepS, keepS, writeR value⟩)
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    Leads
      (cfg s T0 T1 (tapeAtCells left (cell :: right)))
      (cfg target T0 T1 (tapeAtCells (value :: left) right)) :=
  leads_step (s := s) (target := target) hs
    (T0 := T0) (T1 := T1) (T2 := tapeAtCells left (cell :: right))
    (a0 := keepS) (a1 := keepS) (a2 := writeR value)
    (hnext (Tape.read T0) (Tape.read T1)) rfl rfl
    (writeR_apply_tapeAtCells value left cell right)

/-- Move tape 2 left once from a represented left cell. -/
theorem step2L
    {s target : State} (hs : s ∈ states) {cell : Option Bool}
    (hnext : forall r0 r1 : Option Bool,
      next s r0 r1 cell =
        some ⟨target, keepS, keepS, keepL⟩)
    (T0 T1 : Tape Bool) (left : List (Option Bool))
    (previous : Option Bool) (right : List (Option Bool)) :
    Leads
      (cfg s T0 T1
        (tapeAtCells (previous :: left) (cell :: right)))
      (cfg target T0 T1
        (tapeAtCells left (previous :: cell :: right))) :=
  leads_step (s := s) (target := target) hs
    (T0 := T0) (T1 := T1)
    (T2 := tapeAtCells (previous :: left) (cell :: right))
    (a0 := keepS) (a1 := keepS) (a2 := keepL)
    (hnext (Tape.read T0) (Tape.read T1)) rfl rfl
    (keepL_apply_tapeAtCells left previous cell right)

/-- Move tape 2 left and re-split an abstract nonempty left block at the
target cursor. -/
theorem step2L_headTape
    {s target : State} (hs : s ∈ states) {cell : Option Bool}
    (hnext : forall r0 r1 : Option Bool,
      next s r0 r1 cell =
        some ⟨target, keepS, keepS, keepL⟩)
    (T0 T1 : Tape Bool) {leftFull : List (Option Bool)}
    (hleft : leftFull ≠ []) (right : List (Option Bool)) :
    Leads
      (cfg s T0 T1 (tapeAtCells leftFull (cell :: right)))
      (cfg target T0 T1 (headTape leftFull (cell :: right))) := by
  cases leftFull with
  | nil => exact False.elim (hleft rfl)
  | cons previous left =>
      exact step2L hs hnext T0 T1 left previous right

/-- Write the current tape-2 cell and move left. -/
theorem step2L_write
    {s target : State} (hs : s ∈ states)
    {cell value : Option Bool}
    (hnext : forall r0 r1 : Option Bool,
      next s r0 r1 cell =
        some ⟨target, keepS, keepS, writeL value⟩)
    (T0 T1 : Tape Bool) (left : List (Option Bool))
    (previous : Option Bool) (right : List (Option Bool)) :
    Leads
      (cfg s T0 T1
        (tapeAtCells (previous :: left) (cell :: right)))
      (cfg target T0 T1
        (tapeAtCells left (previous :: value :: right))) :=
  leads_step (s := s) (target := target) hs
    (T0 := T0) (T1 := T1)
    (T2 := tapeAtCells (previous :: left) (cell :: right))
    (a0 := keepS) (a1 := keepS) (a2 := writeL value)
    (hnext (Tape.read T0) (Tape.read T1)) rfl rfl
    (writeL_apply_tapeAtCells value left previous cell right)

/-- Write and move left on tapes 0 and 2 in the same typed row. -/
theorem step02L_write
    {s target : State} (hs : s ∈ states)
    {cell0 value0 cell2 value2 : Option Bool}
    (hnext : forall r1 : Option Bool,
      next s cell0 r1 cell2 =
        some ⟨target, writeL value0, keepS, writeL value2⟩)
    (left0 : List (Option Bool)) (previous0 : Option Bool)
    (right0 : List (Option Bool)) (T1 : Tape Bool)
    (left2 : List (Option Bool)) (previous2 : Option Bool)
    (right2 : List (Option Bool)) :
    Leads
      (cfg s
        (tapeAtCells (previous0 :: left0) (cell0 :: right0)) T1
        (tapeAtCells (previous2 :: left2) (cell2 :: right2)))
      (cfg target
        (tapeAtCells left0 (previous0 :: value0 :: right0)) T1
        (tapeAtCells left2 (previous2 :: value2 :: right2))) :=
  leads_step (s := s) (target := target) hs
    (T0 := tapeAtCells (previous0 :: left0) (cell0 :: right0))
    (T1 := T1)
    (T2 := tapeAtCells (previous2 :: left2) (cell2 :: right2))
    (a0 := writeL value0) (a1 := keepS) (a2 := writeL value2)
    (hnext (Tape.read T1))
    (writeL_apply_tapeAtCells value0 left0 previous0 cell0 right0) rfl
    (writeL_apply_tapeAtCells value2 left2 previous2 cell2 right2)

/-- Simultaneously write left on tapes 0 and 2 while re-splitting an
abstract nonempty tape-2 left block at the target cursor. -/
theorem step02L_write_headTape
    {s target : State} (hs : s ∈ states)
    {cell0 value0 cell2 value2 : Option Bool}
    (hnext : forall r1 : Option Bool,
      next s cell0 r1 cell2 =
        some ⟨target, writeL value0, keepS, writeL value2⟩)
    (left0 : List (Option Bool)) (previous0 : Option Bool)
    (right0 : List (Option Bool)) (T1 : Tape Bool)
    {left2Full : List (Option Bool)} (hleft2 : left2Full ≠ [])
    (right2 : List (Option Bool)) :
    Leads
      (cfg s
        (tapeAtCells (previous0 :: left0) (cell0 :: right0)) T1
        (tapeAtCells left2Full (cell2 :: right2)))
      (cfg target
        (tapeAtCells left0 (previous0 :: value0 :: right0)) T1
        (headTape left2Full (value2 :: right2))) := by
  cases left2Full with
  | nil => exact False.elim (hleft2 rfl)
  | cons previous2 left2 =>
      exact step02L_write hs hnext left0 previous0 right0 T1
        left2 previous2 right2

/-- Write and move left on tape 0 while moving tape 2 right. -/
theorem step0L2R_write
    {s target : State} (hs : s ∈ states)
    {cell0 value0 cell2 : Option Bool}
    (hnext : forall r1 : Option Bool,
      next s cell0 r1 cell2 =
        some ⟨target, writeL value0, keepS, keepR⟩)
    (left0 : List (Option Bool)) (previous0 : Option Bool)
    (right0 : List (Option Bool)) (T1 : Tape Bool)
    (left2 right2 : List (Option Bool)) :
    Leads
      (cfg s
        (tapeAtCells (previous0 :: left0) (cell0 :: right0)) T1
        (tapeAtCells left2 (cell2 :: right2)))
      (cfg target
        (tapeAtCells left0 (previous0 :: value0 :: right0)) T1
        (tapeAtCells (cell2 :: left2) right2)) :=
  leads_step (s := s) (target := target) hs
    (T0 := tapeAtCells (previous0 :: left0) (cell0 :: right0))
    (T1 := T1) (T2 := tapeAtCells left2 (cell2 :: right2))
    (a0 := writeL value0) (a1 := keepS) (a2 := keepR)
    (hnext (Tape.read T1))
    (writeL_apply_tapeAtCells value0 left0 previous0 cell0 right0) rfl
    (keepR_apply_tapeAtCells left2 cell2 right2)

/-- Move tape 0 right and tape 2 left, re-splitting an abstract nonempty
tape-2 left block. -/
theorem step0R2L_headTape
    {s target : State} (hs : s ∈ states)
    {cell0 cell2 : Option Bool}
    (hnext : forall r1 : Option Bool,
      next s cell0 r1 cell2 =
        some ⟨target, keepR, keepS, keepL⟩)
    (left0 right0 : List (Option Bool)) (T1 : Tape Bool)
    {left2Full : List (Option Bool)} (hleft2 : left2Full ≠ [])
    (right2 : List (Option Bool)) :
    Leads
      (cfg s
        (tapeAtCells left0 (cell0 :: right0)) T1
        (tapeAtCells left2Full (cell2 :: right2)))
      (cfg target
        (tapeAtCells (cell0 :: left0) right0) T1
        (headTape left2Full (cell2 :: right2))) := by
  cases left2Full with
  | nil => exact False.elim (hleft2 rfl)
  | cons previous2 left2 =>
      exact
        leads_step (s := s) (target := target) hs
          (T0 := tapeAtCells left0 (cell0 :: right0)) (T1 := T1)
          (T2 := tapeAtCells (previous2 :: left2) (cell2 :: right2))
          (a0 := keepR) (a1 := keepS) (a2 := keepL)
          (hnext (Tape.read T1))
          (keepR_apply_tapeAtCells left0 cell0 right0) rfl
          (keepL_apply_tapeAtCells left2 previous2 cell2 right2)

/-- Write while moving tape 0 right and move tape 2 left, re-splitting an
abstract nonempty tape-2 left block. -/
theorem step0R_write2L_headTape
    {s target : State} (hs : s ∈ states)
    {cell0 value0 cell2 : Option Bool}
    (hnext : forall r1 : Option Bool,
      next s cell0 r1 cell2 =
        some ⟨target, writeR value0, keepS, keepL⟩)
    (left0 right0 : List (Option Bool)) (T1 : Tape Bool)
    {left2Full : List (Option Bool)} (hleft2 : left2Full ≠ [])
    (right2 : List (Option Bool)) :
    Leads
      (cfg s
        (tapeAtCells left0 (cell0 :: right0)) T1
        (tapeAtCells left2Full (cell2 :: right2)))
      (cfg target
        (tapeAtCells (value0 :: left0) right0) T1
        (headTape left2Full (cell2 :: right2))) := by
  cases left2Full with
  | nil => exact False.elim (hleft2 rfl)
  | cons previous2 left2 =>
      exact
        leads_step (s := s) (target := target) hs
          (T0 := tapeAtCells left0 (cell0 :: right0)) (T1 := T1)
          (T2 := tapeAtCells (previous2 :: left2) (cell2 :: right2))
          (a0 := writeR value0) (a1 := keepS) (a2 := keepL)
          (hnext (Tape.read T1))
          (writeR_apply_tapeAtCells value0 left0 cell0 right0) rfl
          (keepL_apply_tapeAtCells left2 previous2 cell2 right2)

/-- Move tape 0 right while erasing leftward on tape 2, re-splitting the
remaining abstract tape-2 left block. -/
theorem step0R2L_write_headTape
    {s target : State} (hs : s ∈ states)
    {cell0 cell2 value2 : Option Bool}
    (hnext : forall r1 : Option Bool,
      next s cell0 r1 cell2 =
        some ⟨target, keepR, keepS, writeL value2⟩)
    (left0 right0 : List (Option Bool)) (T1 : Tape Bool)
    {left2Full : List (Option Bool)} (hleft2 : left2Full ≠ [])
    (right2 : List (Option Bool)) :
    Leads
      (cfg s
        (tapeAtCells left0 (cell0 :: right0)) T1
        (tapeAtCells left2Full (cell2 :: right2)))
      (cfg target
        (tapeAtCells (cell0 :: left0) right0) T1
        (headTape left2Full (value2 :: right2))) := by
  cases left2Full with
  | nil => exact False.elim (hleft2 rfl)
  | cons previous2 left2 =>
      exact
        leads_step (s := s) (target := target) hs
          (T0 := tapeAtCells left0 (cell0 :: right0)) (T1 := T1)
          (T2 := tapeAtCells (previous2 :: left2) (cell2 :: right2))
          (a0 := keepR) (a1 := keepS) (a2 := writeL value2)
          (hnext (Tape.read T1))
          (keepR_apply_tapeAtCells left0 cell0 right0) rfl
          (writeL_apply_tapeAtCells value2 left2 previous2 cell2 right2)

/-- Write the current tape-2 cell without moving. -/
theorem step2S_write
    {s target : State} (hs : s ∈ states)
    {cell value : Option Bool}
    (hnext : forall r0 r1 : Option Bool,
      next s r0 r1 cell =
        some ⟨target, keepS, keepS, writeS value⟩)
    (T0 T1 : Tape Bool) (left right : List (Option Bool)) :
    Leads
      (cfg s T0 T1 (tapeAtCells left (cell :: right)))
      (cfg target T0 T1 (tapeAtCells left (value :: right))) :=
  leads_step (s := s) (target := target) hs
    (T0 := T0) (T1 := T1) (T2 := tapeAtCells left (cell :: right))
    (a0 := keepS) (a1 := keepS) (a2 := writeS value)
    (hnext (Tape.read T0) (Tape.read T1)) rfl rfl rfl

/-- Move tape 2 left once from its implicit right blank. -/
theorem step2L_nil
    {s target : State} (hs : s ∈ states)
    (T0 T1 : Tape Bool)
    (hnext :
      next s (Tape.read T0) (Tape.read T1) none =
        some ⟨target, keepS, keepS, keepL⟩)
    (left : List (Option Bool))
    (previous : Option Bool) :
    Leads
      (cfg s T0 T1 (tapeAtCells (previous :: left) []))
      (cfg target T0 T1 (tapeAtCells left [previous, none])) :=
  leads_step (s := s) (target := target) hs
    (T0 := T0) (T1 := T1) (T2 := tapeAtCells (previous :: left) [])
    (a0 := keepS) (a1 := keepS) (a2 := keepL)
    hnext rfl rfl
    (keepL_apply_tapeAtCells_nil left previous)

/-- Copy one Boolean suffix bit from tape 0 to fresh tape-2 workspace while
erasing it from tape 0. -/
theorem step_copy
    (bit : Bool) (left0 right0 : List (Option Bool))
    (T1 : Tape Bool) (left2 : List (Option Bool)) :
    Leads
      (cfg .copy
        (tapeAtCells left0 (some bit :: right0)) T1
        (tapeAtCells left2 []))
      (cfg .copy
        (tapeAtCells (none :: left0) right0) T1
        (tapeAtCells (some bit :: left2) [])) :=
  leads_step (s := .copy) (target := .copy) (state_mem .copy)
    (T0 := tapeAtCells left0 (some bit :: right0)) (T1 := T1)
    (T2 := tapeAtCells left2 [])
    (a0 := writeR (none : Option Bool)) (a1 := keepS)
    (a2 := writeR (some bit)) rfl
    (writeR_apply_tapeAtCells none left0 (some bit) right0) rfl rfl

/-- Copy and erase an arbitrary Boolean suffix into fresh tape-2 cells. -/
theorem leads_copy_bits
    (bits : List Bool) (left0 : List (Option Bool))
    (T1 : Tape Bool) (left2 : List (Option Bool)) :
    Leads
      (cfg .copy
        (tapeAtCells left0 (List.append (bits.map some) [none])) T1
        (tapeAtCells left2 []))
      (cfg .copy
        (tapeAtCells (pushBlanks (bits.map some) left0) [none]) T1
        (tapeAtCells (pushBits (bits.map some) left2) [])) := by
  induction bits generalizing left0 left2 with
  | nil => exact Leads.refl _
  | cons bit rest ih =>
      exact
        (step_copy bit left0
          (List.append (rest.map some) [none]) T1 left2).trans
          (ih (none :: left0) (some bit :: left2))

/-- Tape-2 left context retained immediately before the copied workspace. -/
def workspaceBaseLeft
    (D : MachineDescription) (L : SimulatorLayout) :
    List (Option Bool) :=
  none :: some false :: ClassifiedBoundary.classifiedMetadataLeft D L

/-- Tape-2 view at the first copied configuration bit. -/
def workspaceStartTape
    (D : MachineDescription) (L : SimulatorLayout) (bits : List Bool) :
    Tape Bool :=
  tapeAtCells (workspaceBaseLeft D L)
    (List.append (bits.map some) [none])

/-- Cross the retained blank after the marked hit and open fresh workspace. -/
theorem leads_open_workspace
    (D : MachineDescription) (L : SimulatorLayout)
    (T0 T1 : Tape Bool) :
    Leads
      (cfg .gap1 T0 T1
        (ClassifiedBoundary.metadataHitTapeWithSelectorMarked D L))
      (cfg .copy T0 T1 (tapeAtCells (workspaceBaseLeft D L) [])) := by
  change
    Leads
      (cfg .gap1 T0 T1
        (tapeAtCells (ClassifiedBoundary.classifiedMetadataLeft D L)
          [some false, none]))
      (cfg .copy T0 T1
        (tapeAtCells
          (none :: some false ::
            ClassifiedBoundary.classifiedMetadataLeft D L) []))
  refine Leads.trans
    (step2R (state_mem .gap1) (fun _ _ => rfl) T0 T1
      (ClassifiedBoundary.classifiedMetadataLeft D L) [none]) ?_
  exact step2R (state_mem .gap2) (fun _ _ => rfl) T0 T1
    (some false :: ClassifiedBoundary.classifiedMetadataLeft D L) []

/-- Tape-2 view while rewinding left through the copied Boolean suffix. -/
def rewindWorkspaceTape
    (baseTail : List (Option Bool))
    (remaining scanned : List Bool) : Tape Bool :=
  match remaining with
  | [] =>
      tapeAtCells baseTail
        (none :: List.append (scanned.map some) [none])
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some) (none :: baseTail))
        (some bit :: List.append (scanned.map some) [none])

/-- Rewind all copied bits to the retained workspace delimiter. -/
theorem leads_rewind_workspace
    (baseTail : List (Option Bool)) (remaining scanned : List Bool)
    (T0 T1 : Tape Bool) :
    Leads
      (cfg .rewind T0 T1
        (rewindWorkspaceTape baseTail remaining scanned))
      (cfg .rewind T0 T1
        (rewindWorkspaceTape baseTail []
          (List.append remaining.reverse scanned))) := by
  induction remaining generalizing scanned with
  | nil => exact Leads.refl _
  | cons bit rest ih =>
      cases rest with
      | nil =>
          exact
            step2L (state_mem .rewind) (fun _ _ => rfl) T0 T1
              baseTail none (List.append (scanned.map some) [none])
      | cons next tail =>
          refine
            (step2L (state_mem .rewind) (fun _ _ => rfl) T0 T1
              (List.append (tail.map some) (none :: baseTail))
              (some next) (List.append (scanned.map some) [none])).trans ?_
          simpa [rewindWorkspaceTape, List.reverse_cons,
            List.append_assoc] using ih (bit :: scanned)

/-- Finish copying at the terminal blank, rewind to the retained delimiter,
and enter the configuration decoder on the first copied bit. -/
theorem leads_copy_end_rewind
    (bits : List Bool) (hbits : bits ≠ [])
    (baseTail left0 : List (Option Bool)) (T1 : Tape Bool) :
    Leads
      (cfg .copy (tapeAtCells left0 [none]) T1
        (tapeAtCells
          (pushBits (bits.map some) (none :: baseTail)) []))
      (cfg .lLen0 (tapeAtCells left0 [none]) T1
        (tapeAtCells (none :: baseTail)
          (List.append (bits.map some) [none]))) := by
  rw [pushBits_eq_reverse_append]
  have hmap :
      (bits.map some).reverse = bits.reverse.map some :=
    List.map_reverse.symm
  rw [hmap]
  cases hrev : bits.reverse with
  | nil =>
      exact False.elim (hbits (by simpa using congrArg List.reverse hrev))
  | cons last rest =>
      refine Leads.trans
        (step2L_nil (state_mem .copy)
          (tapeAtCells left0 [none]) T1 rfl
          (List.append (rest.map some) (none :: baseTail))
          (some last)) ?_
      refine Leads.trans
        (leads_rewind_workspace baseTail (last :: rest) []
          (tapeAtCells left0 [none]) T1) ?_
      have hscan : (last :: rest).reverse = bits := by
        simpa using (congrArg List.reverse hrev).symm
      rw [hscan]
      have hnil : List.append bits [] = bits := List.append_nil bits
      rw [hnil]
      exact step2R (state_mem .rewind) (fun _ _ => rfl)
        (tapeAtCells left0 [none]) T1 baseTail
        (List.append (bits.map some) [none])

/-- Boolean suffix copied by the configuration/hit phase. -/
def configurationSuffixBits (L : SimulatorLayout) : List Bool :=
  encodeCodeWordAsInput (StateSelector.postStateTokens L)

theorem configurationSuffixBits_ne_nil (L : SimulatorLayout) :
    configurationSuffixBits L ≠ [] := by
  intro hempty
  have hlen := congrArg List.length hempty
  rw [configurationSuffixBits, encodeCodeWordAsInput_length] at hlen
  have hnat :
      0 < (encodeNat L.config.tape.left.length).length := by
    cases L.config.tape.left.length <;> simp [encodeNat]
  have hlenPost :
      (show List MachineCodeSymbol from
          StateSelector.postStateTokens L).length =
        (show List MachineCodeSymbol from
          encodeNat L.config.tape.left.length).length +
          (List.append (L.config.tape.left.map cellTok)
            (cellTok L.config.tape.head ::
              List.append
                (show List MachineCodeSymbol from
                  encodeNat L.config.tape.right.length)
                (List.append (L.config.tape.right.map cellTok)
                  [cellTok (some L.hit)]))).length := by
    unfold StateSelector.postStateTokens
    exact List.length_append
  have hpost : 0 < (StateSelector.postStateTokens L).length := by
    rw [hlenPost]
    lia
  have hzero : 4 * (StateSelector.postStateTokens L).length = 0 := by
    simpa using hlen
  lia

/-- Tape 0 after the complete encoded layout has been erased. -/
def erasedLayoutTape (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells
    (pushBlanks ((configurationSuffixBits L).map some)
      (erasedPrefixLeft L))
    [none]

/-- Reach the first copied configuration bit on tape 2. -/
theorem leads_to_configuration_suffix
    (D : MachineDescription) (L : SimulatorLayout) (T1 : Tape Bool) :
    Leads
      (cfg .hdr0 (headerStartTape L) T1
        (ClassifiedBoundary.metadataHitTapeWithSelectorMarked D L))
      (cfg .lLen0 (erasedLayoutTape L) T1
        (workspaceStartTape D L (configurationSuffixBits L))) := by
  refine Leads.trans
    (leads_prefix_layout L T1
      (ClassifiedBoundary.metadataHitTapeWithSelectorMarked D L)) ?_
  refine Leads.trans (leads_open_workspace D L _ T1) ?_
  refine Leads.trans
    (leads_copy_bits (configurationSuffixBits L)
      (erasedPrefixLeft L) T1 (workspaceBaseLeft D L)) ?_
  exact leads_copy_end_rewind (configurationSuffixBits L)
    (configurationSuffixBits_ne_nil L)
    (some false :: ClassifiedBoundary.classifiedMetadataLeft D L)
    (pushBlanks ((configurationSuffixBits L).map some)
      (erasedPrefixLeft L)) T1

/-!
## Encoded configuration navigation
-/

/-- Walk the copied left-list length field. -/
theorem leads_lLen
    (n : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    Leads
      (cfg .lLen0 T0 T1
        (tapeAtCells left (List.append (codeBits (encodeNat n)) right)))
      (cfg .lb0 T0 T1
        (tapeAtCells (pushBits (codeBits (encodeNat n)) left) right)) := by
  induction n generalizing left with
  | zero =>
      exact
        (step2R (state_mem .lLen0) (fun _ _ => rfl) T0 T1 left _).trans
          ((step2R (state_mem .lLen1) (fun _ _ => rfl) T0 T1 _ _).trans
            ((step2R (state_mem .lLen2) (fun _ _ => rfl) T0 T1 _ _).trans
              (step2R (state_mem .lLen3) (fun _ _ => rfl) T0 T1 _ right)))
  | succ n ih =>
      exact
        (step2R (state_mem .lLen0) (fun _ _ => rfl) T0 T1 left _).trans
          ((step2R (state_mem .lLen1) (fun _ _ => rfl) T0 T1 _ _).trans
            ((step2R (state_mem .lLen2) (fun _ _ => rfl) T0 T1 _ _).trans
              ((step2R (state_mem .lLen3) (fun _ _ => rfl) T0 T1 _ _).trans
                (ih _))))

/-- Walk the copied right-list length field. -/
theorem leads_rLen
    (n : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    Leads
      (cfg .rLen0 T0 T1
        (tapeAtCells left (List.append (codeBits (encodeNat n)) right)))
      (cfg .rb0 T0 T1
        (tapeAtCells (pushBits (codeBits (encodeNat n)) left) right)) := by
  induction n generalizing left with
  | zero =>
      exact
        (step2R (state_mem .rLen0) (fun _ _ => rfl) T0 T1 left _).trans
          ((step2R (state_mem .rLen1) (fun _ _ => rfl) T0 T1 _ _).trans
            ((step2R (state_mem .rLen2) (fun _ _ => rfl) T0 T1 _ _).trans
              (step2R (state_mem .rLen3) (fun _ _ => rfl) T0 T1 _ right)))
  | succ n ih =>
      exact
        (step2R (state_mem .rLen0) (fun _ _ => rfl) T0 T1 left _).trans
          ((step2R (state_mem .rLen1) (fun _ _ => rfl) T0 T1 _ _).trans
            ((step2R (state_mem .rLen2) (fun _ _ => rfl) T0 T1 _ _).trans
              ((step2R (state_mem .rLen3) (fun _ _ => rfl) T0 T1 _ _).trans
                (ih _))))

/-- Walk the copied left-cell tokens. -/
theorem leads_lb
    (cells : List (Option Bool)) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    Leads
      (cfg .lb0 T0 T1
        (tapeAtCells left
          (List.append (codeBits (cells.map cellTok)) right)))
      (cfg .lb0 T0 T1
        (tapeAtCells
          (pushBits (codeBits (cells.map cellTok)) left) right)) := by
  induction cells generalizing left with
  | nil => exact Leads.refl _
  | cons cell rest ih =>
      obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits cell
      have hcode :
          codeBits ((cell :: rest).map cellTok) =
            List.append (tokBits (cellTok cell))
              (codeBits (rest.map cellTok)) :=
        codeBits_cons _ _
      rw [hcode, hbits]
      rw [show
        pushBits
            (List.append [some false, some true, some v2, some v3]
              (codeBits (rest.map cellTok))) left =
          pushBits (codeBits (rest.map cellTok))
            (some v3 :: some v2 :: some true :: some false :: left) from rfl]
      exact
        (step2R (state_mem .lb0) (fun _ _ => rfl) T0 T1 left _).trans
          ((step2R (state_mem .lb1) (fun _ _ => rfl) T0 T1 _ _).trans
            ((step2R (state_mem .lb2) (fun _ _ => rfl) T0 T1 _ _).trans
              ((step2R (state_mem .lb3) (fun _ _ => rfl) T0 T1 _ _).trans
                (ih _))))

/-- Walk one copied cell token with the left-blob scanner. -/
theorem leads_lb_one
    (cell : Option Bool) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    Leads
      (cfg .lb0 T0 T1
        (tapeAtCells left
          (List.append (tokBits (cellTok cell)) right)))
      (cfg .lb0 T0 T1
        (tapeAtCells (pushBits (tokBits (cellTok cell)) left) right)) := by
  obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits cell
  rw [hbits]
  exact
    (step2R (state_mem .lb0) (fun _ _ => rfl) T0 T1 left _).trans
      ((step2R (state_mem .lb1) (fun _ _ => rfl) T0 T1 _ _).trans
        ((step2R (state_mem .lb2) (fun _ _ => rfl) T0 T1 _ _).trans
          (step2R (state_mem .lb3) (fun _ _ => rfl) T0 T1 _ right)))

/-- Walk the copied right-cell tokens. -/
theorem leads_rb
    (cells : List (Option Bool)) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    Leads
      (cfg .rb0 T0 T1
        (tapeAtCells left
          (List.append (codeBits (cells.map cellTok)) right)))
      (cfg .rb0 T0 T1
        (tapeAtCells
          (pushBits (codeBits (cells.map cellTok)) left) right)) := by
  induction cells generalizing left with
  | nil => exact Leads.refl _
  | cons cell rest ih =>
      obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits cell
      have hcode :
          codeBits ((cell :: rest).map cellTok) =
            List.append (tokBits (cellTok cell))
              (codeBits (rest.map cellTok)) :=
        codeBits_cons _ _
      rw [hcode, hbits]
      rw [show
        pushBits
            (List.append [some false, some true, some v2, some v3]
              (codeBits (rest.map cellTok))) left =
          pushBits (codeBits (rest.map cellTok))
            (some v3 :: some v2 :: some true :: some false :: left) from rfl]
      exact
        (step2R (state_mem .rb0) (fun _ _ => rfl) T0 T1 left _).trans
          ((step2R (state_mem .rb1) (fun _ _ => rfl) T0 T1 _ _).trans
            ((step2R (state_mem .rb2) (fun _ _ => rfl) T0 T1 _ _).trans
              ((step2R (state_mem .rb3) (fun _ _ => rfl) T0 T1 _ _).trans
                (ih _))))

/-- Walk one copied cell token with the right-blob scanner. -/
theorem leads_rb_one
    (cell : Option Bool) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    Leads
      (cfg .rb0 T0 T1
        (tapeAtCells left
          (List.append (tokBits (cellTok cell)) right)))
      (cfg .rb0 T0 T1
        (tapeAtCells (pushBits (tokBits (cellTok cell)) left) right)) := by
  obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits cell
  rw [hbits]
  exact
    (step2R (state_mem .rb0) (fun _ _ => rfl) T0 T1 left _).trans
      ((step2R (state_mem .rb1) (fun _ _ => rfl) T0 T1 _ _).trans
        ((step2R (state_mem .rb2) (fun _ _ => rfl) T0 T1 _ _).trans
          (step2R (state_mem .rb3) (fun _ _ => rfl) T0 T1 _ right)))

/-- Detect the right-length token after the encoded head, backtrack to mark
the head token, and resume at the right-cell blob. -/
theorem leads_mark_rLen
    (head : Option Bool) (n : Nat) (T0 T1 : Tape Bool)
    (left right : List (Option Bool)) :
    Leads
      (cfg .lb0 T0 T1
        (tapeAtCells (pushBits (tokBits (cellTok head)) left)
          (List.append (codeBits (encodeNat n)) right)))
      (cfg .rb0 T0 T1
        (tapeAtCells
          (pushBits (codeBits (encodeNat n))
            (pushBits (markedBits head) left)) right)) := by
  obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits head
  rw [hbits, markedBits_eq hbits]
  have hdance :
      Leads
        (cfg .lb0 T0 T1
          (tapeAtCells
            (pushBits [some false, some true, some v2, some v3] left)
            (List.append (codeBits (encodeNat n)) right)))
        (cfg .rLen2 T0 T1
          (tapeAtCells
            (pushBits [some false, some false]
              (pushBits [some true, some true, some v2, some v3] left))
            (List.append ((codeBits (encodeNat n)).drop 2) right))) := by
    cases n with
    | zero =>
        refine Leads.trans
          (step2R (state_mem .lb0) (fun _ _ => rfl) T0 T1 _ _) ?_
        refine Leads.trans
          (step2L (state_mem .lb1) (fun _ _ => rfl) T0 T1 _ _ _) ?_
        refine Leads.trans
          (step2L (state_mem .lbB1) (fun _ _ => rfl) T0 T1 _ _ _) ?_
        refine Leads.trans
          (step2L (state_mem .lbB2) (fun _ _ => rfl) T0 T1 _ _ _) ?_
        refine Leads.trans
          (step2L (state_mem .lbB3) (fun _ _ => rfl) T0 T1 _ _ _) ?_
        refine Leads.trans
          (step2L (state_mem .lbB4) (fun _ _ => rfl) T0 T1 _ _ _) ?_
        refine Leads.trans
          (step2R_write (state_mem .lbMark) (fun _ _ => rfl)
            T0 T1 _ _) ?_
        refine Leads.trans
          (step2R (state_mem .lbR1) (fun _ _ => rfl) T0 T1 _ _) ?_
        refine Leads.trans
          (step2R (state_mem .lbR2) (fun _ _ => rfl) T0 T1 _ _) ?_
        refine Leads.trans
          (step2R (state_mem .lbR3) (fun _ _ => rfl) T0 T1 _ _) ?_
        refine Leads.trans
          (step2R (state_mem .lbR4) (fun _ _ => rfl) T0 T1 _ _) ?_
        exact step2R (state_mem .lbR5) (fun _ _ => rfl) T0 T1 _ _
    | succ n =>
        refine Leads.trans
          (step2R (state_mem .lb0) (fun _ _ => rfl) T0 T1 _ _) ?_
        refine Leads.trans
          (step2L (state_mem .lb1) (fun _ _ => rfl) T0 T1 _ _ _) ?_
        refine Leads.trans
          (step2L (state_mem .lbB1) (fun _ _ => rfl) T0 T1 _ _ _) ?_
        refine Leads.trans
          (step2L (state_mem .lbB2) (fun _ _ => rfl) T0 T1 _ _ _) ?_
        refine Leads.trans
          (step2L (state_mem .lbB3) (fun _ _ => rfl) T0 T1 _ _ _) ?_
        refine Leads.trans
          (step2L (state_mem .lbB4) (fun _ _ => rfl) T0 T1 _ _ _) ?_
        refine Leads.trans
          (step2R_write (state_mem .lbMark) (fun _ _ => rfl)
            T0 T1 _ _) ?_
        refine Leads.trans
          (step2R (state_mem .lbR1) (fun _ _ => rfl) T0 T1 _ _) ?_
        refine Leads.trans
          (step2R (state_mem .lbR2) (fun _ _ => rfl) T0 T1 _ _) ?_
        refine Leads.trans
          (step2R (state_mem .lbR3) (fun _ _ => rfl) T0 T1 _ _) ?_
        refine Leads.trans
          (step2R (state_mem .lbR4) (fun _ _ => rfl) T0 T1 _ _) ?_
        exact step2R (state_mem .lbR5) (fun _ _ => rfl) T0 T1 _ _
  refine hdance.trans ?_
  cases n with
  | zero =>
      exact
        (step2R (state_mem .rLen2) (fun _ _ => rfl) T0 T1 _ _).trans
          (step2R (state_mem .rLen3) (fun _ _ => rfl) T0 T1 _ right)
  | succ n =>
      exact
        (step2R (state_mem .rLen2) (fun _ _ => rfl) T0 T1 _ _).trans
          ((step2R (state_mem .rLen3) (fun _ _ => rfl) T0 T1 _ _).trans
            (leads_rLen n T0 T1 _ right))

/-- Decode and erase the final hit token, retaining its value in control. -/
theorem leads_hit_decode
    (hit : Bool) (T0 T1 : Tape Bool)
    (leftFull : List (Option Bool)) (hleft : leftFull ≠ []) :
    Leads
      (cfg .rb0 T0 T1
        (tapeAtCells
          (pushBits (tokBits (cellTok (some hit))) leftFull) []))
      (cfg (.re3 hit) T0 T1
        (headTape leftFull [none, none, none, none, none])) := by
  cases leftFull with
  | nil => exact False.elim (hleft rfl)
  | cons previous left =>
      cases hit with
      | false =>
          exact
            (step2L_nil (state_mem .rb0) T0 T1 rfl
              (some false :: some true :: some false :: previous :: left)
              (some true)).trans
              ((step2L_write (state_mem .hit3) (fun _ _ => rfl)
                T0 T1 (some true :: some false :: previous :: left)
                (some false) [none]).trans
                ((step2L_write (state_mem (.hit2 true)) (fun _ _ => rfl)
                  T0 T1 (some false :: previous :: left)
                  (some true) [none, none]).trans
                  ((step2L_write (state_mem (.hit1 true false))
                    (fun _ _ => rfl) T0 T1 (previous :: left)
                    (some false) [none, none, none]).trans
                    (step2L_write (state_mem (.hit0 false))
                      (fun _ _ => rfl) T0 T1 left previous
                      [none, none, none, none]))))

      | true =>
          exact
            (step2L_nil (state_mem .rb0) T0 T1 rfl
              (some true :: some true :: some false :: previous :: left)
              (some false)).trans
              ((step2L_write (state_mem .hit3) (fun _ _ => rfl)
                T0 T1 (some true :: some false :: previous :: left)
                (some true) [none]).trans
                ((step2L_write (state_mem (.hit2 false)) (fun _ _ => rfl)
                  T0 T1 (some false :: previous :: left)
                  (some true) [none, none]).trans
                  ((step2L_write (state_mem (.hit1 false true))
                    (fun _ _ => rfl) T0 T1 (previous :: left)
                    (some false) [none, none, none]).trans
                    (step2L_write (state_mem (.hit0 true))
                      (fun _ _ => rfl) T0 T1 left previous
                      [none, none, none, none]))))

end ConfigTapeAndHit
end MetadataPrefix
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
