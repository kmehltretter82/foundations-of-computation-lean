import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.MetadataPrefix

set_option doc.verso true

/-!
# Exact runs around the metadata-copy kernel

The scratch positioning, canonical forward reparse, and exact return to the
temporary hit marker are independent of the four-cell lag kernel.  This module
proves those reusable pieces and names the lag execution as the sole remaining
obligation for {lit}`MetadataPrefix.RunObligation`.
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

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open StructuredConstructionTargets.FuelOutputCore
open ClassifiedBoundary

/-!
## Step-count-free execution
-/

def cfg (s : State) (T0 T1 T2 : Tape Bool) :
    CommonGround.FiniteTransducers.Structured.Configuration :=
  ThreeTape.config (table.stateId s) T0 T1 T2

def Leads
    (c d : CommonGround.FiniteTransducers.Structured.Configuration) : Prop :=
  exists steps : Nat,
    forall tail : Nat,
      description.runConfig (tail + steps) c = description.runConfig tail d

namespace Leads

theorem refl
    (c : CommonGround.FiniteTransducers.Structured.Configuration) :
    Leads c c :=
  ⟨0, fun _ => rfl⟩

theorem trans
    {c d e : CommonGround.FiniteTransducers.Structured.Configuration}
    (hcd : Leads c d) (hde : Leads d e) : Leads c e := by
  rcases hcd with ⟨first, hfirst⟩
  rcases hde with ⟨second, hsecond⟩
  refine ⟨second + first, fun tail => ?_⟩
  rw [show tail + (second + first) = (tail + second) + first by lia]
  rw [hfirst (tail + second), hsecond tail]

theorem to_runConfig
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (h : Leads c d) :
    exists steps : Nat, description.runConfig steps c = d := by
  rcases h with ⟨steps, hsteps⟩
  exact ⟨steps, by simpa [Description.runConfig] using hsteps 0⟩

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
  refine ⟨1, fun tail => ?_⟩
  have hstep := table.runConfig_succ_config hs hnext tail
  change
    table.description.runConfig (tail + 1)
        (ThreeTape.config (table.stateId s) T0 T1 T2) =
      table.description.runConfig tail
        (ThreeTape.config (table.stateId target) T0' T1' T2')
  rw [hstep, h0, h1, h2]

theorem leads_tape2
    {s target : State} (hs : s ∈ states)
    {T0 T1 T2 : Tape Bool} {a2 : TapeAction}
    (hnext :
      next s (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some ⟨target, keepS, keepS, a2⟩)
    {T2' : Tape Bool} (h2 : a2.apply T2 = T2') :
    Leads (cfg s T0 T1 T2) (cfg target T0 T1 T2') := by
  apply leads_step hs hnext
  · rfl
  · rfl
  · exact h2

theorem stepR0
    {s target : State} (hs : s ∈ states)
    {cell : Option Bool}
    (hnext :
      forall r1 r2 : Option Bool,
        next s cell r1 r2 = some ⟨target, keepR, keepS, keepS⟩)
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

/-!
## Selector/scratch positioning
-/

/-- Boolean view of the nonblank selector and scratch block, nearest-first. -/
def scratchBits
    (D : MachineDescription) (L : SimulatorLayout) : Word Bool :=
  List.append
    (selectorBits (classifyState D L.config.state))
    (List.replicate (remainingScratchMarkers D L).length true)

theorem scratchBits_map_some
    (D : MachineDescription) (L : SimulatorLayout) :
    (scratchBits D L).map some =
      List.append
        ((selectorBits (classifyState D L.config.state)).map some)
        (remainingScratchMarkers D L) := by
  simp [scratchBits, remainingScratchMarkers, List.map_append]

theorem scratchBits_ne_nil
    (D : MachineDescription) (L : SimulatorLayout) :
    scratchBits D L ≠ [] := by
  have hpos :=
    StateSelector.selectorBits_length_pos
      (classifyState D L.config.state)
  intro hnil
  rw [scratchBits] at hnil
  cases hs : selectorBits (classifyState D L.config.state) with
  | nil => rw [hs] at hpos; simp at hpos
  | cons x xs => rw [hs] at hnil; simp at hnil

theorem selectorScratchTape_eq_bits
    (D : MachineDescription) (L : SimulatorLayout) :
    StateSelector.selectorScratchTape D L =
      tapeAtCells ((scratchBits D L).map some) [] := by
  unfold StateSelector.selectorScratchTape
  rw [scratchBits_map_some]

/-- Cursor while walking left across the nonblank scratch block. -/
def scratchLeftTape
    (remaining scanned : Word Bool) : Tape Bool :=
  match remaining with
  | [] =>
      tapeAtCells []
        (none :: List.append (scanned.map some) [some false])
  | bit :: rest =>
      tapeAtCells (rest.map some)
        (some bit :: List.append (scanned.map some) [some false])

/-- Blank output cursor immediately left of the preserved delimiter. -/
def metadataOutputStartTape (scratchPhysical : Word Bool) : Tape Bool :=
  tapeAtCells []
    (none ::
      none ::
        List.append (scratchPhysical.map some) [some false])

theorem writeL_mark_scratch
    (first : Bool) (rest : Word Bool) :
    (writeL (some false)).apply
        (tapeAtCells ((first :: rest).map some) []) =
      scratchLeftTape (first :: rest) [] := by
  cases rest <;>
    rfl

theorem keepL_scratchLeftTape
    (bit : Bool) (rest scanned : Word Bool) :
    keepL.apply (scratchLeftTape (bit :: rest) scanned) =
      scratchLeftTape rest (bit :: scanned) := by
  cases rest <;>
    rfl

theorem keepL_scratchLeftTape_done (scanned : Word Bool) :
    keepL.apply (scratchLeftTape [] scanned) =
      metadataOutputStartTape scanned := by
  rfl

theorem leads_scratchLeft
    (remaining scanned : Word Bool)
    (T0 T1 : Tape Bool) :
    Leads
      (cfg .scratchLeft T0 T1 (scratchLeftTape remaining scanned))
      (cfg .copyEnter T0 T1
        (metadataOutputStartTape
          (List.append remaining.reverse scanned))) := by
  induction remaining generalizing scanned with
  | nil =>
      apply leads_tape2 (a2 := keepL) (state_mem _)
        (by rfl)
      exact keepL_scratchLeftTape_done scanned
  | cons bit rest ih =>
      have hone :
          Leads
            (cfg .scratchLeft T0 T1
              (scratchLeftTape (bit :: rest) scanned))
            (cfg .scratchLeft T0 T1
              (scratchLeftTape rest (bit :: scanned))) := by
        apply leads_tape2 (a2 := keepL) (state_mem _)
          (by rfl)
        exact keepL_scratchLeftTape bit rest scanned
      refine hone.trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        ih (bit :: scanned)

theorem leads_position_scratch
    (bits : Word Bool) (hbits : bits ≠ [])
    (T0 T1 : Tape Bool) :
    Leads
      (cfg .start T0 T1 (tapeAtCells (bits.map some) []))
      (cfg .copyEnter T0 T1
        (metadataOutputStartTape bits.reverse)) := by
  cases bits with
  | nil => contradiction
  | cons first rest =>
      have hmark :
          Leads
            (cfg .start T0 T1
              (tapeAtCells ((first :: rest).map some) []))
            (cfg .scratchLeft T0 T1
              (scratchLeftTape (first :: rest) [])) := by
        apply leads_tape2 (a2 := writeL (some false)) (state_mem _)
          (by rfl)
        exact writeL_mark_scratch first rest
      simpa using
        hmark.trans (leads_scratchLeft (first :: rest) [] T0 T1)

/-!
## Exact rightward return
-/

/-- Tape 2 after backward metadata copying and before the return scan. -/
def metadataCopiedTape
    (metadata scratchPhysical : Word Bool) : Tape Bool :=
  tapeAtCells []
    (none ::
      List.append (metadata.map some)
        (none ::
          List.append (scratchPhysical.map some) [some false]))

theorem keepR_metadataCopiedTape
    (first : Bool) (rest scratchPhysical : Word Bool) :
    keepR.apply
        (metadataCopiedTape (first :: rest) scratchPhysical) =
      tapeAtCells [none]
        (some first ::
          List.append (rest.map some)
            (none ::
              List.append (scratchPhysical.map some) [some false])) := by
  rfl

theorem leads_metadataRight
    (remaining : Word Bool) (leftRev : List (Option Bool))
    (scratchPhysical : Word Bool) (T0 T1 : Tape Bool) :
    Leads
      (cfg .metadataRight T0 T1
        (tapeAtCells leftRev
          (List.append (remaining.map some)
            (none ::
              List.append (scratchPhysical.map some) [some false]))))
      (cfg .scratchRight T0 T1
        (tapeAtCells
          (none :: List.append (remaining.reverse.map some) leftRev)
          (List.append (scratchPhysical.map some) [some false]))) := by
  induction remaining generalizing leftRev with
  | nil =>
      apply leads_tape2 (a2 := keepR) (state_mem _)
        (by rfl)
      exact keepR_apply_tapeAtCells leftRev none _
  | cons bit rest ih =>
      have hone :
          Leads
            (cfg .metadataRight T0 T1
              (tapeAtCells leftRev
                (some bit ::
                  List.append (rest.map some)
                    (none ::
                      List.append (scratchPhysical.map some)
                        [some false]))))
            (cfg .metadataRight T0 T1
              (tapeAtCells (some bit :: leftRev)
                (List.append (rest.map some)
                  (none ::
                    List.append (scratchPhysical.map some)
                      [some false])))) := by
        apply leads_tape2 (a2 := keepR) (state_mem _)
          (by rfl)
        exact keepR_apply_tapeAtCells leftRev (some bit) _
      refine hone.trans ?_
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: leftRev)

theorem leads_scratchRight
    (remaining : Word Bool) (leftRev : List (Option Bool))
    (T0 T1 : Tape Bool) :
    Leads
      (cfg .scratchRight T0 T1
        (tapeAtCells leftRev
          (List.append (remaining.map some) [some false])))
      (cfg .halt T0 T1
        (tapeAtCells
          (List.append (remaining.reverse.map some) leftRev)
          [some false, none])) := by
  induction remaining generalizing leftRev with
  | nil =>
      have hmark :
          Leads
            (cfg .scratchRight T0 T1
              (tapeAtCells leftRev [some false]))
            (cfg .scratchRight T0 T1
              (tapeAtCells (some false :: leftRev) [])) := by
        apply leads_tape2 (a2 := keepR) (state_mem _)
          (by rfl)
        exact keepR_apply_tapeAtCells leftRev (some false) []
      have hback :
          Leads
            (cfg .scratchRight T0 T1
              (tapeAtCells (some false :: leftRev) []))
            (cfg .halt T0 T1
              (tapeAtCells leftRev [some false, none])) := by
        apply leads_tape2 (a2 := keepL) (state_mem _)
          (by rfl)
        exact keepL_apply_tapeAtCells_nil leftRev (some false)
      simpa using hmark.trans hback
  | cons bit rest ih =>
      have hone :
          Leads
            (cfg .scratchRight T0 T1
              (tapeAtCells leftRev
                (some bit ::
                  List.append (rest.map some) [some false])))
            (cfg .scratchRight T0 T1
              (tapeAtCells (some bit :: leftRev)
                (List.append (rest.map some) [some false]))) := by
        apply leads_tape2 (a2 := keepR) (state_mem _)
          (by rfl)
        exact keepR_apply_tapeAtCells leftRev (some bit) _
      refine hone.trans ?_
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: leftRev)

theorem leads_return_to_mark
    (metadata scratchPhysical : Word Bool)
    (hmetadata : metadata ≠ [])
    (T0 T1 : Tape Bool) :
    Leads
      (cfg .outputEnter T0 T1
        (metadataCopiedTape metadata scratchPhysical))
      (cfg .halt T0 T1
        (tapeAtCells
          (List.append (scratchPhysical.reverse.map some)
            (none :: List.append (metadata.reverse.map some) [none]))
          [some false, none])) := by
  cases metadata with
  | nil => contradiction
  | cons first rest =>
      have henter :
          Leads
            (cfg .outputEnter T0 T1
              (metadataCopiedTape (first :: rest) scratchPhysical))
            (cfg .metadataRight T0 T1
              (tapeAtCells [none]
                (some first ::
                  List.append (rest.map some)
                    (none ::
                      List.append (scratchPhysical.map some)
                        [some false])))) := by
        apply leads_tape2 (a2 := keepR) (state_mem _)
          (by rfl)
        exact keepR_metadataCopiedTape first rest scratchPhysical
      have hmeta :=
        leads_metadataRight (first :: rest) [none]
          scratchPhysical T0 T1
      have hscratch :=
        leads_scratchRight scratchPhysical
          (none :: List.append ((first :: rest).reverse.map some) [none])
          T0 T1
      have hfull := henter.trans (hmeta.trans hscratch)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using hfull

end MetadataPrefix
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
