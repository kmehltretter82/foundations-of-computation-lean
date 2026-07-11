import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.SourceCounter
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.ClassifiedBoundary

set_option doc.verso true

/-!
# Stage-field parser and exact unary counter

This is the second executable phase of the #18 field decomposer.  Starting at
the parser-ready endpoint of the source-counter phase, it walks the header, input
length, input cells, and stage field on logical tape 0.  The source is preserved
exactly.  While reading the stage field it materializes the raw unary counter
required by the execution loops on logical tape 1, and it leaves the original
scratch-width block on logical tape 2 unchanged.

The counter construction deliberately delays its first write.  The first stage
tick moves left over the initial blank, later ticks write left, and the done
token writes the pending final marker in place.  Thus stage zero remains the
canonical blank tape and every positive stage ends at the first marker with an
explicit trailing blank, exactly matching the loop-stage counter contract.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition
namespace StageCounter

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open StructuredConstructionTargets.FuelOutputCore

/-!
## Exact counter-builder tapes
-/

/-- Tape-1 cursor after the first tick has been seen.  The blank head is the
pending final marker; {lit}`committed` markers and an explicit trailing blank
are already to its right. -/
def pendingCounterTape (committed : Nat) : Tape Bool :=
  tapeAtCells []
    (none ::
      List.append
        (List.replicate committed (some true : Option Bool)) [none])

theorem keepL_blank_eq_pendingCounterTape_zero :
    keepL.apply (Tape.blank : Tape Bool) = pendingCounterTape 0 := by
  rfl

theorem writeL_pendingCounterTape
    (committed : Nat) :
    (writeL (some true)).apply (pendingCounterTape committed) =
      pendingCounterTape (committed + 1) := by
  simp [pendingCounterTape, writeL, TapeAction.apply, HeadMove.apply,
    Tape.write, Tape.move, Tape.moveLeft, tapeAtCells,
    List.replicate_succ]

theorem writeS_pendingCounterTape
    (committed : Nat) :
    (writeS (some true)).apply (pendingCounterTape committed) =
      FieldDecomposition.stageCounterTape (committed + 1) := by
  simp [pendingCounterTape, FieldDecomposition.stageCounterTape,
    writeS, TapeAction.apply, HeadMove.apply, Tape.write,
    tapeAtCells, List.replicate_succ]

/-!
## Typed finite-control table
-/

inductive State where
  | hdr0 | hdr1 | hdr2 | hdr3
  | inLen0 | inLen1 | inLen2 | inLen3
  | inBits0 | inBits1 | inBits2 | inBits3
  | stageE0 | stageE1 | stageE2 | stageE3
  | stageP0 | stageP1 | stageP2 | stageP3
  | halt
deriving DecidableEq, Repr

def states : List State :=
  [ .hdr0, .hdr1, .hdr2, .hdr3
  , .inLen0, .inLen1, .inLen2, .inLen3
  , .inBits0, .inBits1, .inBits2, .inBits3
  , .stageE0, .stageE1, .stageE2, .stageE3
  , .stageP0, .stageP1, .stageP2, .stageP3
  , .halt ]

theorem state_mem (s : State) : s ∈ states := by
  cases s <;> simp [states]

/-- Parse through the stage field while preserving tapes 0 and 2.  Empty and
pending stage modes distinguish zero from a positive unary counter without
adding padding to the zero tape. -/
def next :
    State -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep State)
  | .hdr0, some false, _, _ =>
      some ⟨.hdr1, keepR, keepS, keepS⟩
  | .hdr1, some false, _, _ =>
      some ⟨.hdr2, keepR, keepS, keepS⟩
  | .hdr2, some false, _, _ =>
      some ⟨.hdr3, keepR, keepS, keepS⟩
  | .hdr3, some false, _, _ =>
      some ⟨.inLen0, keepR, keepS, keepS⟩
  | .inLen0, some false, _, _ =>
      some ⟨.inLen1, keepR, keepS, keepS⟩
  | .inLen1, some false, _, _ =>
      some ⟨.inLen2, keepR, keepS, keepS⟩
  | .inLen2, some true, _, _ =>
      some ⟨.inLen3, keepR, keepS, keepS⟩
  | .inLen3, some false, _, _ =>
      some ⟨.inLen0, keepR, keepS, keepS⟩
  | .inLen3, some true, _, _ =>
      some ⟨.inBits0, keepR, keepS, keepS⟩
  | .inBits0, some false, _, _ =>
      some ⟨.inBits1, keepR, keepS, keepS⟩
  | .inBits1, some true, _, _ =>
      some ⟨.inBits2, keepR, keepS, keepS⟩
  | .inBits1, some false, _, _ =>
      some ⟨.stageE2, keepR, keepS, keepS⟩
  | .inBits2, some _, _, _ =>
      some ⟨.inBits3, keepR, keepS, keepS⟩
  | .inBits3, some _, _, _ =>
      some ⟨.inBits0, keepR, keepS, keepS⟩
  | .stageE0, some false, _, _ =>
      some ⟨.stageE1, keepR, keepS, keepS⟩
  | .stageE1, some false, _, _ =>
      some ⟨.stageE2, keepR, keepS, keepS⟩
  | .stageE2, some true, _, _ =>
      some ⟨.stageE3, keepR, keepS, keepS⟩
  | .stageE3, some false, _, _ =>
      some ⟨.stageP0, keepR, keepL, keepS⟩
  | .stageE3, some true, _, _ =>
      some ⟨.halt, keepR, keepS, keepS⟩
  | .stageP0, some false, _, _ =>
      some ⟨.stageP1, keepR, keepS, keepS⟩
  | .stageP1, some false, _, _ =>
      some ⟨.stageP2, keepR, keepS, keepS⟩
  | .stageP2, some true, _, _ =>
      some ⟨.stageP3, keepR, keepS, keepS⟩
  | .stageP3, some false, _, _ =>
      some ⟨.stageP0, keepR, writeL (some true), keepS⟩
  | .stageP3, some true, _, _ =>
      some ⟨.halt, keepR, writeS (some true), keepS⟩
  | _, _, _, _ => none

theorem next_target_mem :
    forall s : State, s ∈ states ->
      forall (r0 r1 r2 : Option Bool) (st : TypedStep State),
        next s r0 r1 r2 = some st -> st.target ∈ states := by
  intro _s _hs _r0 _r1 _r2 st _hnext
  exact state_mem st.target

def table : TypedStateTable State :=
  TypedStateTable.ofList
    states
    .hdr0
    .halt
    next
    (state_mem .hdr0)
    (state_mem .halt)
    (by intro r0 r1 r2; rfl)
    next_target_mem

def description : Description :=
  table.description

theorem description_wellFormed : description.WellFormed :=
  table.description_wellFormed

theorem description_haltTransitionFree :
    description.HaltTransitionFree :=
  table.description_haltTransitionFree

theorem description_supportsReadWriteRows3 :
    SupportsReadWriteRows3 description :=
  table.description_supportsReadWriteRows3

theorem description_subroutineReady :
    description.SubroutineReady :=
  table.description_subroutineReady

/-!
## Step-count-free exact execution
-/

def cfg (s : State) (T0 T1 T2 : Tape Bool) :
    CommonGround.FiniteTransducers.Structured.Configuration :=
  ThreeTape.config (table.stateId s) T0 T1 T2

/-- Exact reachability with a fixed, hidden step count. -/
def Leads
    (c d : CommonGround.FiniteTransducers.Structured.Configuration) : Prop :=
  exists j : Nat,
    forall k : Nat,
      description.runConfig (k + j) c = description.runConfig k d

namespace Leads

theorem refl
    (c : CommonGround.FiniteTransducers.Structured.Configuration) :
    Leads c c :=
  ⟨0, fun _ => rfl⟩

theorem trans
    {c d e : CommonGround.FiniteTransducers.Structured.Configuration}
    (hcd : Leads c d) (hde : Leads d e) : Leads c e := by
  rcases hcd with ⟨j1, hj1⟩
  rcases hde with ⟨j2, hj2⟩
  refine ⟨j2 + j1, fun k => ?_⟩
  rw [show k + (j2 + j1) = (k + j2) + j1 by lia]
  rw [hj1 (k + j2), hj2 k]

theorem to_runConfig
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (h : Leads c d) :
    exists j : Nat, description.runConfig j c = d := by
  rcases h with ⟨j, hj⟩
  exact ⟨j, by simpa [Description.runConfig] using hj 0⟩

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
    Leads (cfg s T0 T1 T2) (cfg target T0' T1' T2') := by
  refine ⟨1, fun k => ?_⟩
  have hstep := table.runConfig_succ_config hs hnext k
  change
    table.description.runConfig (k + 1)
        (ThreeTape.config (table.stateId s) T0 T1 T2) =
      table.description.runConfig k
        (ThreeTape.config (table.stateId target) T0' T1' T2')
  rw [hstep, h0, h1, h2]

theorem stepR_keep
    {s target : State} (hs : s ∈ states)
    {cell : Option Bool}
    (hnext :
      forall r1 r2 : Option Bool,
        next s cell r1 r2 =
          some ⟨target, keepR, keepS, keepS⟩)
    (leftRev right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    Leads
      (cfg s (tapeAtCells leftRev (cell :: right)) T1 T2)
      (cfg target (tapeAtCells (cell :: leftRev) right) T1 T2) := by
  apply leads_step
    (s := s) (target := target)
    (T0 := tapeAtCells leftRev (cell :: right))
    (T1 := T1) (T2 := T2)
    hs (hnext (Tape.read T1) (Tape.read T2))
  · exact keepR_apply_tapeAtCells leftRev cell right
  · rfl
  · rfl

theorem stepR_firstTick
    (leftRev right : List (Option Bool)) (T2 : Tape Bool) :
    Leads
      (cfg .stageE3
        (tapeAtCells leftRev (some false :: right)) Tape.blank T2)
      (cfg .stageP0
        (tapeAtCells (some false :: leftRev) right)
        (pendingCounterTape 0) T2) := by
  apply leads_step
    (s := .stageE3) (target := .stageP0)
    (T0 := tapeAtCells leftRev (some false :: right))
    (T1 := Tape.blank) (T2 := T2)
    (state_mem .stageE3) (by rfl)
  · exact keepR_apply_tapeAtCells leftRev (some false) right
  · exact keepL_blank_eq_pendingCounterTape_zero
  · rfl

theorem stepR_moreTick
    (committed : Nat)
    (leftRev right : List (Option Bool)) (T2 : Tape Bool) :
    Leads
      (cfg .stageP3
        (tapeAtCells leftRev (some false :: right))
        (pendingCounterTape committed) T2)
      (cfg .stageP0
        (tapeAtCells (some false :: leftRev) right)
        (pendingCounterTape (committed + 1)) T2) := by
  apply leads_step
    (s := .stageP3) (target := .stageP0)
    (T0 := tapeAtCells leftRev (some false :: right))
    (T1 := pendingCounterTape committed) (T2 := T2)
    (state_mem .stageP3) (by rfl)
  · exact keepR_apply_tapeAtCells leftRev (some false) right
  · exact writeL_pendingCounterTape committed
  · rfl

theorem stepR_zeroDone
    (leftRev right : List (Option Bool)) (T2 : Tape Bool) :
    Leads
      (cfg .stageE3
        (tapeAtCells leftRev (some true :: right)) Tape.blank T2)
      (cfg .halt
        (tapeAtCells (some true :: leftRev) right)
        (FieldDecomposition.stageCounterTape 0) T2) := by
  apply leads_step
    (s := .stageE3) (target := .halt)
    (T0 := tapeAtCells leftRev (some true :: right))
    (T1 := Tape.blank) (T2 := T2)
    (state_mem .stageE3) (by rfl)
  · exact keepR_apply_tapeAtCells leftRev (some true) right
  · rfl
  · rfl

theorem stepR_pendingDone
    (committed : Nat)
    (leftRev right : List (Option Bool)) (T2 : Tape Bool) :
    Leads
      (cfg .stageP3
        (tapeAtCells leftRev (some true :: right))
        (pendingCounterTape committed) T2)
      (cfg .halt
        (tapeAtCells (some true :: leftRev) right)
        (FieldDecomposition.stageCounterTape (committed + 1)) T2) := by
  apply leads_step
    (s := .stageP3) (target := .halt)
    (T0 := tapeAtCells leftRev (some true :: right))
    (T1 := pendingCounterTape committed) (T2 := T2)
    (state_mem .stageP3) (by rfl)
  · exact keepR_apply_tapeAtCells leftRev (some true) right
  · exact writeS_pendingCounterTape committed
  · rfl

/-!
## Canonical field walks
-/

@[simp] theorem codeBits_encodeNat_zero :
    codeBits (encodeNat 0) = tokBits MachineCodeSymbol.done := by
  rfl

theorem codeBits_encodeNat_succ (n : Nat) :
    codeBits (encodeNat (n + 1)) =
      List.append (tokBits MachineCodeSymbol.tick) (codeBits (encodeNat n)) := by
  rfl

theorem pushBits_encodeNat_succ
    (n : Nat) (leftRev : List (Option Bool)) :
    pushBits (codeBits (encodeNat (n + 1))) leftRev =
      pushBits (codeBits (encodeNat n))
        (pushBits (tokBits MachineCodeSymbol.tick) leftRev) := by
  rw [codeBits_encodeNat_succ, pushBits_append]

theorem leads_header
    (leftRev right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    Leads
      (cfg .hdr0
        (tapeAtCells leftRev
          (List.append (tokBits MachineCodeSymbol.header) right)) T1 T2)
      (cfg .inLen0
        (tapeAtCells
          (pushBits (tokBits MachineCodeSymbol.header) leftRev) right)
        T1 T2) :=
  (stepR_keep (state_mem .hdr0) (fun _ _ => rfl) leftRev _ T1 T2).trans
    ((stepR_keep (state_mem .hdr1) (fun _ _ => rfl) _ _ T1 T2).trans
      ((stepR_keep (state_mem .hdr2) (fun _ _ => rfl) _ _ T1 T2).trans
        (stepR_keep (state_mem .hdr3) (fun _ _ => rfl) _ right T1 T2)))

theorem leads_inLen
    (lengthValue : Nat)
    (leftRev right : List (Option Bool))
    (T1 T2 : Tape Bool) :
    Leads
      (cfg .inLen0
        (tapeAtCells leftRev
          (List.append (codeBits (encodeNat lengthValue)) right)) T1 T2)
      (cfg .inBits0
        (tapeAtCells
          (pushBits (codeBits (encodeNat lengthValue)) leftRev) right)
        T1 T2) := by
  induction lengthValue generalizing leftRev with
  | zero =>
      exact
        (stepR_keep (state_mem .inLen0) (fun _ _ => rfl)
          leftRev _ T1 T2).trans
          ((stepR_keep (state_mem .inLen1) (fun _ _ => rfl)
            _ _ T1 T2).trans
            ((stepR_keep (state_mem .inLen2) (fun _ _ => rfl)
              _ _ T1 T2).trans
              (stepR_keep (state_mem .inLen3) (fun _ _ => rfl)
                _ right T1 T2)))
  | succ n ih =>
      exact
        (stepR_keep (state_mem .inLen0) (fun _ _ => rfl)
          leftRev _ T1 T2).trans
          ((stepR_keep (state_mem .inLen1) (fun _ _ => rfl)
            _ _ T1 T2).trans
            ((stepR_keep (state_mem .inLen2) (fun _ _ => rfl)
              _ _ T1 T2).trans
              ((stepR_keep (state_mem .inLen3) (fun _ _ => rfl)
                _ _ T1 T2).trans
                (ih _))))

/-- Finish a positive stage after its first tick has established the pending
counter cursor. -/
theorem leads_stage_pending
    (remaining committed : Nat)
    (leftRev right : List (Option Bool)) (T2 : Tape Bool) :
    Leads
      (cfg .stageP0
        (tapeAtCells leftRev
          (List.append (codeBits (encodeNat remaining)) right))
        (pendingCounterTape committed) T2)
      (cfg .halt
        (tapeAtCells
          (pushBits (codeBits (encodeNat remaining)) leftRev) right)
        (FieldDecomposition.stageCounterTape
          (committed + remaining + 1)) T2) := by
  induction remaining generalizing leftRev committed with
  | zero =>
      simpa [pushBits] using
        (stepR_keep (state_mem .stageP0) (fun _ _ => rfl)
          leftRev _ (pendingCounterTape committed) T2).trans
          ((stepR_keep (state_mem .stageP1) (fun _ _ => rfl)
            _ _ (pendingCounterTape committed) T2).trans
            ((stepR_keep (state_mem .stageP2) (fun _ _ => rfl)
              _ _ (pendingCounterTape committed) T2).trans
              (stepR_pendingDone committed _ right T2)))
  | succ n ih =>
      have hwalk :
          Leads
            (cfg .stageP0
              (tapeAtCells leftRev
                (List.append (codeBits (encodeNat (n + 1))) right))
              (pendingCounterTape committed) T2)
            (cfg .stageP0
              (tapeAtCells
                (pushBits (tokBits MachineCodeSymbol.tick) leftRev)
                (List.append (codeBits (encodeNat n)) right))
              (pendingCounterTape (committed + 1)) T2) :=
        (stepR_keep (state_mem .stageP0) (fun _ _ => rfl)
          leftRev _ (pendingCounterTape committed) T2).trans
          ((stepR_keep (state_mem .stageP1) (fun _ _ => rfl)
            _ _ (pendingCounterTape committed) T2).trans
            ((stepR_keep (state_mem .stageP2) (fun _ _ => rfl)
              _ _ (pendingCounterTape committed) T2).trans
              (stepR_moreTick committed _ _ T2)))
      refine hwalk.trans ?_
      rw [pushBits_encodeNat_succ]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih
          (committed + 1)
          (pushBits (tokBits MachineCodeSymbol.tick) leftRev)

/-- Walk the whole stage field and construct its exact raw counter. -/
theorem leads_stage
    (stage : Nat)
    (leftRev right : List (Option Bool)) (T2 : Tape Bool) :
    Leads
      (cfg .stageE0
        (tapeAtCells leftRev
          (List.append (codeBits (encodeNat stage)) right))
        Tape.blank T2)
      (cfg .halt
        (tapeAtCells
          (pushBits (codeBits (encodeNat stage)) leftRev) right)
        (FieldDecomposition.stageCounterTape stage) T2) := by
  cases stage with
  | zero =>
      exact
        (stepR_keep (state_mem .stageE0) (fun _ _ => rfl)
          leftRev _ Tape.blank T2).trans
          ((stepR_keep (state_mem .stageE1) (fun _ _ => rfl)
            _ _ Tape.blank T2).trans
            ((stepR_keep (state_mem .stageE2) (fun _ _ => rfl)
              _ _ Tape.blank T2).trans
              (stepR_zeroDone _ right T2)))
  | succ n =>
      have hfirst :
          Leads
            (cfg .stageE0
              (tapeAtCells leftRev
                (List.append (codeBits (encodeNat (n + 1))) right))
              Tape.blank T2)
            (cfg .stageP0
              (tapeAtCells
                (pushBits (tokBits MachineCodeSymbol.tick) leftRev)
                (List.append (codeBits (encodeNat n)) right))
              (pendingCounterTape 0) T2) :=
        (stepR_keep (state_mem .stageE0) (fun _ _ => rfl)
          leftRev _ Tape.blank T2).trans
          ((stepR_keep (state_mem .stageE1) (fun _ _ => rfl)
            _ _ Tape.blank T2).trans
            ((stepR_keep (state_mem .stageE2) (fun _ _ => rfl)
              _ _ Tape.blank T2).trans
              (stepR_firstTick _ _ T2)))
      refine hfirst.trans ?_
      rw [pushBits_encodeNat_succ]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        leads_stage_pending n 0
          (pushBits (tokBits MachineCodeSymbol.tick) leftRev) right T2

/-- Walk the input cell tokens, fall through the first two bits of the stage
field, and materialize the stage counter. -/
theorem leads_inBits_stage
    (input : Word Bool) (stage : Nat)
    (leftRev right : List (Option Bool)) (T2 : Tape Bool) :
    Leads
      (cfg .inBits0
        (tapeAtCells leftRev
          (List.append (codeBits ((input.map some).map cellTok))
            (List.append (codeBits (encodeNat stage)) right)))
        Tape.blank T2)
      (cfg .halt
        (tapeAtCells
          (pushBits (codeBits (encodeNat stage))
            (pushBits (codeBits ((input.map some).map cellTok)) leftRev))
          right)
        (FieldDecomposition.stageCounterTape stage) T2) := by
  induction input generalizing leftRev with
  | nil =>
      cases stage with
      | zero =>
          exact
            (stepR_keep (state_mem .inBits0) (fun _ _ => rfl)
              leftRev _ Tape.blank T2).trans
              ((stepR_keep (state_mem .inBits1) (fun _ _ => rfl)
                _ _ Tape.blank T2).trans
                ((stepR_keep (state_mem .stageE2) (fun _ _ => rfl)
                  _ _ Tape.blank T2).trans
                  (stepR_zeroDone _ right T2)))
      | succ n =>
          have hfirst :
              Leads
                (cfg .inBits0
                  (tapeAtCells leftRev
                    (List.append
                      (codeBits ((([] : Word Bool).map some).map cellTok))
                      (List.append (codeBits (encodeNat (n + 1))) right)))
                  Tape.blank T2)
                (cfg .stageP0
                  (tapeAtCells
                    (pushBits (tokBits MachineCodeSymbol.tick) leftRev)
                    (List.append (codeBits (encodeNat n)) right))
                  (pendingCounterTape 0) T2) :=
            (stepR_keep (state_mem .inBits0) (fun _ _ => rfl)
              leftRev _ Tape.blank T2).trans
              ((stepR_keep (state_mem .inBits1) (fun _ _ => rfl)
                _ _ Tape.blank T2).trans
                ((stepR_keep (state_mem .stageE2) (fun _ _ => rfl)
                  _ _ Tape.blank T2).trans
                  (stepR_firstTick _ _ T2)))
          refine hfirst.trans ?_
          rw [pushBits_encodeNat_succ]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            leads_stage_pending n 0
              (pushBits (tokBits MachineCodeSymbol.tick) leftRev) right T2
  | cons bit rest ih =>
      cases bit <;>
        exact
          (stepR_keep (state_mem .inBits0) (fun _ _ => rfl)
            leftRev _ Tape.blank T2).trans
            ((stepR_keep (state_mem .inBits1) (fun _ _ => rfl)
              _ _ Tape.blank T2).trans
              ((stepR_keep (state_mem .inBits2) (fun _ _ => rfl)
                _ _ Tape.blank T2).trans
                ((stepR_keep (state_mem .inBits3) (fun _ _ => rfl)
                  _ _ Tape.blank T2).trans
                  (ih _))))

theorem leads_prefix
    (input : Word Bool) (stage : Nat)
    (leftRev right : List (Option Bool)) (T2 : Tape Bool) :
    Leads
      (cfg .hdr0
        (tapeAtCells leftRev
          (List.append (tokBits MachineCodeSymbol.header)
            (List.append (codeBits (encodeNat (input.map some).length))
              (List.append (codeBits ((input.map some).map cellTok))
                (List.append (codeBits (encodeNat stage)) right)))))
        Tape.blank T2)
      (cfg .halt
        (tapeAtCells
          (pushBits (codeBits (encodeNat stage))
            (pushBits (codeBits ((input.map some).map cellTok))
              (pushBits (codeBits (encodeNat (input.map some).length))
                (pushBits (tokBits MachineCodeSymbol.header) leftRev))))
          right)
        (FieldDecomposition.stageCounterTape stage) T2) :=
  (leads_header leftRev _ Tape.blank T2).trans
    ((leads_inLen (input.map some).length _ _ Tape.blank T2).trans
      (leads_inBits_stage input stage _ right T2))

/-!
## Simulator-layout specialization
-/

/-- Token suffix beginning at the raw configuration-state field. -/
def postStageTokens (L : SimulatorLayout) : Word MachineCodeSymbol :=
  List.append (encodeNat L.config.state)
    (List.append (encodeNat L.config.tape.left.length)
      (List.append (L.config.tape.left.map cellTok)
        (cellTok L.config.tape.head ::
          List.append (encodeNat L.config.tape.right.length)
            (List.append (L.config.tape.right.map cellTok)
              [cellTok (some L.hit)]))))

/-- Exact tape-0 cursor at the first bit of the raw state field. -/
def postStageTape (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells
    (pushBits (codeBits (encodeNat L.stage))
      (pushBits (codeBits ((L.input.map some).map cellTok))
        (pushBits (codeBits (encodeNat (L.input.map some).length))
          (pushBits (tokBits MachineCodeSymbol.header) [none]))))
    (List.append (codeBits (postStageTokens L)) [none])

theorem codeBits_layout_decomp (L : SimulatorLayout) :
    codeBits (SimulatorLayout.encode L) =
      List.append (tokBits MachineCodeSymbol.header)
        (List.append (codeBits (encodeNat (L.input.map some).length))
          (List.append (codeBits ((L.input.map some).map cellTok))
            (List.append (codeBits (encodeNat L.stage))
              (codeBits (postStageTokens L))))) := by
  rw [FieldDecomposition.source_encode_decomp]
  simp only
    [ StructuredConstructionTargets.FuelOutputCore.codeBits_cons
    , StructuredConstructionTargets.FuelOutputCore.codeBits_append
    , StructuredConstructionTargets.FuelOutputCore.codeBits_nil ]
  unfold postStageTokens
  simp only
    [ StructuredConstructionTargets.FuelOutputCore.codeBits_cons
    , StructuredConstructionTargets.FuelOutputCore.codeBits_append
    , StructuredConstructionTargets.FuelOutputCore.codeBits_nil ]
  simp

theorem rightEdgeTape_eq_decomposed (L : SimulatorLayout) :
    rightEdgeRewindTargetTape (SimulatorLayout.asBoolInput L) [] =
      tapeAtCells [none]
        (List.append (tokBits MachineCodeSymbol.header)
          (List.append (codeBits (encodeNat (L.input.map some).length))
            (List.append (codeBits ((L.input.map some).map cellTok))
              (List.append (codeBits (encodeNat L.stage))
                (List.append (codeBits (postStageTokens L)) [none]))))) := by
  change
    tapeAtCells [none]
        (List.append (codeBits (SimulatorLayout.encode L)) [none]) = _
  rw [codeBits_layout_decomp]
  simp [List.append_assoc]

theorem leads_layout (L : SimulatorLayout) :
    Leads
      (cfg .hdr0
        (rightEdgeRewindTargetTape (SimulatorLayout.asBoolInput L) [])
        Tape.blank (SourceCounter.layoutMarkerTape L))
      (cfg .halt (postStageTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (SourceCounter.layoutMarkerTape L)) := by
  rw [rightEdgeTape_eq_decomposed]
  exact leads_prefix L.input L.stage [none]
    (List.append (codeBits (postStageTokens L)) [none])
    (SourceCounter.layoutMarkerTape L)

theorem haltsWithTapes_layout (L : SimulatorLayout) :
    description.HaltsWithTapes
      (ThreeTape.config description.start
        (rightEdgeRewindTargetTape (SimulatorLayout.asBoolInput L) [])
        Tape.blank (SourceCounter.layoutMarkerTape L))
      [ postStageTape L
      , FieldDecomposition.stageCounterTape L.stage
      , SourceCounter.layoutMarkerTape L ] := by
  rcases (leads_layout L).to_runConfig with ⟨steps, hrun⟩
  exact ⟨steps, hrun⟩

/-!
## Lowered physical phase
-/

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_wellFormed :
    loweredDescription.WellFormed :=
  lowerStructured3Description_wellFormed
    description_wellFormed description_supportsReadWriteRows3

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady :=
  lowerStructured3Description_subroutineReady
    description_wellFormed description_supportsReadWriteRows3

/-- Exact guarded physical boundary after stage parsing. -/
def targetTape (L : SimulatorLayout) : Tape Bool :=
  encodedGuardedStructuredTapes
    [ postStageTape L
    , FieldDecomposition.stageCounterTape L.stage
    , SourceCounter.layoutMarkerTape L ]

theorem loweredDescription_haltsFromTapeEquiv (L : SimulatorLayout) :
    loweredDescription.HaltsFromTapeEquiv
      (SourceCounter.targetTape L) (targetTape L) := by
  unfold loweredDescription SourceCounter.targetTape targetTape
  apply lowerStructured3Description_haltsFromConfigWithTapes
    description_wellFormed
    description_haltTransitionFree
    description_supportsReadWriteRows3
    (c :=
      ThreeTape.config description.start
        (rightEdgeRewindTargetTape (SimulatorLayout.asBoolInput L) [])
        Tape.blank (SourceCounter.layoutMarkerTape L))
  · rfl
  · rfl
  · exact haltsWithTapes_layout L

def Spec (counter : MachineDescription) : Prop :=
  counter.SubroutineReady ∧
    forall L : SimulatorLayout,
      counter.HaltsFromTapeEquiv
        (SourceCounter.targetTape L) (targetTape L)

def Construction : Prop :=
  exists counter : MachineDescription, Spec counter

/-- Completed stage-parser/counter phase of the integrated field decomposer. -/
theorem construction_core : Construction :=
  ⟨loweredDescription,
    loweredDescription_subroutineReady,
    loweredDescription_haltsFromTapeEquiv⟩

/-!
## Exact next phase
-/

/-- Remaining D-specific state/configuration parser and metadata materializer.

Tape 0 is positioned at the first bit of the raw state field, tape 1 already
is the exact loop-stage counter, and tape 2 still holds the original source
scratch-width markers.  The remaining phase must preserve tape 1, decode the
state and exact configuration tape, prepend canonical input/stage/state
metadata behind the scratch block, put the hit bit at the tape-2 head, and
reserve the finite D-specific classification selector in the markers nearest
the hit.  A plain unclassified {name}`FieldDecomposition.loopTargetTape`
handoff would lose the input-dependent dispatcher control. -/
def PostStageSpec
    (D : MachineDescription) (parser : MachineDescription) : Prop :=
  parser.SubroutineReady ∧
    forall L : SimulatorLayout,
      parser.HaltsFromTapeEquiv
        (targetTape L)
        (ClassifiedBoundary.classifiedLoopTargetTape D L)

def PostStageConstruction (D : MachineDescription) : Prop :=
  exists parser : MachineDescription, PostStageSpec D parser

end StageCounter
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
