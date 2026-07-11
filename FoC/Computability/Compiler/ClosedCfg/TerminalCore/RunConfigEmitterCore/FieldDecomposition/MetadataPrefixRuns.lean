import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.MetadataPrefix

set_option doc.verso true

/-!
# Exact runs around the metadata-copy kernel

The scratch positioning and exact return to the temporary hit marker are
independent of the four-cell lag kernel.  This module proves those reusable
pieces and isolates the lag execution needed by
{lit}`MetadataPrefix.RunObligation`.
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
    (List.append (metadata.map some)
      (none ::
        List.append (scratchPhysical.map some) [some false]))

theorem keepR_metadataCopiedTape
    (first : Bool) (rest scratchPhysical : Word Bool) :
    keepR.apply
        (metadataCopiedTape (first :: rest) scratchPhysical) =
      tapeAtCells [some first]
        (List.append (rest.map some)
          (none ::
            List.append (scratchPhysical.map some) [some false])) := by
  cases rest <;> rfl

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
            (none :: metadata.reverse.map some))
          [some false, none])) := by
  cases metadata with
  | nil => contradiction
  | cons first rest =>
      have henter :
          Leads
            (cfg .outputEnter T0 T1
              (metadataCopiedTape (first :: rest) scratchPhysical))
            (cfg .metadataRight T0 T1
              (tapeAtCells [some first]
                (List.append (rest.map some)
                  (none ::
                    List.append (scratchPhysical.map some)
                      [some false])))) := by
        apply leads_tape2 (a2 := keepR) (state_mem _)
          (by rfl)
        exact keepR_metadataCopiedTape first rest scratchPhysical
      have hmeta :=
        leads_metadataRight rest [some first]
          scratchPhysical T0 T1
      have hscratch :=
        leads_scratchRight scratchPhysical
          (none :: List.append (rest.reverse.map some) [some first])
          T0 T1
      have hfull := henter.trans (hmeta.trans hscratch)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using hfull

private def lagHeader : Word Bool := [false, false, false, false]

/-- Tape 0 while the lag kernel walks left.  {lean}`remaining` is in read order;
{lean}`scannedRight` is the already-scanned context nearest-first. -/
private def lagScanTape (remaining : Word Bool)
    (scannedRight : List (Option Bool)) : Tape Bool :=
  match remaining with
  | [] => tapeAtCells [] (none :: scannedRight)
  | bit :: rest => tapeAtCells
      (List.append (rest.map some) [none]) (some bit :: scannedRight)

/-- Tape 2 while emitted cells accumulate to the right of a fresh blank. -/
private def lagOutputCursor (writtenRev suffix : List (Option Bool)) : Tape Bool :=
  tapeAtCells [] (none :: List.append writtenRev suffix)

private def lagEntryTape
    (stream : Word Bool) (boundaryCell : Option Bool)
    (boundaryRight : List (Option Bool)) : Tape Bool :=
  tapeAtCells (List.append (stream.map some) [none])
    (boundaryCell :: boundaryRight)

private theorem keepL_lagScanTape
    (bit : Bool) (rest : Word Bool) (scannedRight : List (Option Bool)) :
    keepL.apply (lagScanTape (bit :: rest) scannedRight) =
      lagScanTape rest (some bit :: scannedRight) := by
  cases rest <;> rfl

private theorem keepL_lagEntryTape
    (bit : Bool) (rest : Word Bool) (boundaryCell : Option Bool)
    (boundaryRight : List (Option Bool)) :
    keepL.apply (lagEntryTape (bit :: rest) boundaryCell boundaryRight) =
      lagScanTape (bit :: rest) (boundaryCell :: boundaryRight) := by
  cases rest <;> rfl

private theorem writeL_lagOutputCursor
    (pending : Bool) (writtenRev suffix : List (Option Bool)) :
    (writeL (some pending)).apply (lagOutputCursor writtenRev suffix) =
      lagOutputCursor (some pending :: writtenRev) suffix := by
  rfl

private theorem leads_copy4p_bit
    (a b c d pending bit : Bool) (rest : Word Bool)
    (scannedRight writtenRev suffix : List (Option Bool))
    (T1 : Tape Bool) :
    Leads
      (cfg (.copy4p a b c d pending)
        (lagScanTape (bit :: rest) scannedRight)
        T1 (lagOutputCursor writtenRev suffix))
      (cfg (.copy4p b c d bit a)
        (lagScanTape rest (some bit :: scannedRight))
        T1 (lagOutputCursor (some pending :: writtenRev) suffix)) := by
  apply leads_step (state_mem _)
  · rfl
  · exact keepL_lagScanTape bit rest scannedRight
  · rfl
  · exact writeL_lagOutputCursor pending writtenRev suffix

private theorem leads_lagScan_keepL
    {s target : State} (hs : s ∈ states)
    (bit : Bool) (rest : Word Bool)
    (scannedRight : List (Option Bool))
    (T1 T2 : Tape Bool)
    (hnext : forall r1 r2 : Option Bool,
      next s (some bit) r1 r2 =
        some ⟨target, keepL, keepS, keepS⟩) :
    Leads
      (cfg s (lagScanTape (bit :: rest) scannedRight) T1 T2)
      (cfg target (lagScanTape rest (some bit :: scannedRight)) T1 T2) := by
  apply leads_step
    (s := s) (target := target)
    (T0 := lagScanTape (bit :: rest) scannedRight)
    (T1 := T1) (T2 := T2)
    (a0 := keepL) (a1 := keepS) (a2 := keepS)
    hs (hnext (Tape.read T1) (Tape.read T2))
  · exact keepL_lagScanTape bit rest scannedRight
  · rfl
  · rfl

private theorem leads_copyEnter_first
    (bit : Bool) (rest : Word Bool) (boundaryCell : Option Bool)
    (boundaryRight : List (Option Bool))
    (T1 T2 : Tape Bool) :
    Leads
      (cfg .copyEnter
        (lagEntryTape (bit :: rest) boundaryCell boundaryRight) T1 T2)
      (cfg .copy0 (lagScanTape (bit :: rest)
        (boundaryCell :: boundaryRight)) T1 T2) := by
  apply leads_step
    (s := .copyEnter) (target := .copy0)
    (T0 := lagEntryTape (bit :: rest) boundaryCell boundaryRight)
    (T1 := T1) (T2 := T2)
    (a0 := keepL) (a1 := keepS) (a2 := keepS)
    (state_mem _) (by rfl)
  · exact keepL_lagEntryTape bit rest boundaryCell boundaryRight
  · rfl
  · rfl

private theorem leads_copy4p_done
    (pending : Bool) (scannedRight writtenRev suffix : List (Option Bool))
    (T1 : Tape Bool) :
    Leads
      (cfg (.copy4p false false false false pending)
        (lagScanTape [] scannedRight)
        T1 (lagOutputCursor writtenRev suffix))
      (cfg .outputEnter (tapeAtCells [none] scannedRight) T1
        (tapeAtCells [] (some pending :: List.append writtenRev suffix))) := by
  apply leads_step (state_mem _)
  · rfl
  · exact keepR_apply_tapeAtCells [] none scannedRight
  · rfl
  · rfl

private def lagFiveTail (pending a b c d : Bool) (tail : Word Bool) : Word Bool :=
  pending :: a :: b :: c :: d :: tail

private theorem leads_copy4p_tail
    (tail : Word Bool) (a b c d pending : Bool)
    (scannedRight writtenRev suffix : List (Option Bool))
    (T1 : Tape Bool) :
    Leads
      (cfg (.copy4p a b c d pending)
        (lagScanTape (List.append tail lagHeader) scannedRight)
        T1 (lagOutputCursor writtenRev suffix))
      (cfg .outputEnter
        (tapeAtCells [none]
          (List.append (lagHeader.map some)
            (List.append (tail.reverse.map some) scannedRight)))
        T1
        (tapeAtCells []
          (List.append
            ((lagFiveTail pending a b c d tail).reverse.map some)
            (List.append writtenRev suffix)))) := by
  induction tail generalizing a b c d pending scannedRight writtenRev with
  | nil =>
      have h1 :=
        leads_copy4p_bit a b c d pending false
          [false, false, false] scannedRight writtenRev suffix T1
      have h2 :=
        leads_copy4p_bit b c d false a false
          [false, false] (some false :: scannedRight)
          (some pending :: writtenRev) suffix T1
      have h3 :=
        leads_copy4p_bit c d false false b false
          [false] (some false :: some false :: scannedRight)
          (some a :: some pending :: writtenRev) suffix T1
      have h4 :=
        leads_copy4p_bit d false false false c false
          []
          (some false :: some false :: some false :: scannedRight)
          (some b :: some a :: some pending :: writtenRev) suffix T1
      have hdone :=
        leads_copy4p_done d
          (some false :: some false :: some false :: some false ::
            scannedRight)
          (some c :: some b :: some a :: some pending :: writtenRev)
          suffix T1
      have hfull := h1.trans (h2.trans (h3.trans (h4.trans hdone)))
      simpa [lagHeader, lagFiveTail, lagScanTape, lagOutputCursor,
        List.append_assoc] using hfull
  | cons bit rest ih =>
      have hone :=
        leads_copy4p_bit a b c d pending bit
          (List.append rest lagHeader)
          scannedRight writtenRev suffix T1
      have htail :=
        ih b c d bit a
          (some bit :: scannedRight)
          (some pending :: writtenRev)
      have hfull := hone.trans htail
      simpa [lagFiveTail, List.reverse_cons, List.map_append,
        List.append_assoc] using hfull

private theorem leads_copyEnter_fiveTail
    (p0 p1 p2 p3 p4 : Bool) (tail : Word Bool)
    (boundaryCell : Option Bool)
    (boundaryRight suffix : List (Option Bool))
    (T1 : Tape Bool) :
    Leads
      (cfg .copyEnter
        (lagEntryTape
          (List.append (lagFiveTail p0 p1 p2 p3 p4 tail) lagHeader)
          boundaryCell boundaryRight)
        T1 (lagOutputCursor [] suffix))
      (cfg .outputEnter
        (tapeAtCells [none]
          (List.append (lagHeader.map some)
            (List.append
              ((lagFiveTail p0 p1 p2 p3 p4 tail).reverse.map some)
              (boundaryCell :: boundaryRight))))
        T1
        (tapeAtCells []
          (List.append
            ((lagFiveTail p0 p1 p2 p3 p4 tail).reverse.map some)
            suffix))) := by
  have henter :=
    leads_copyEnter_first p0
      (p1 :: p2 :: p3 :: p4 :: List.append tail lagHeader)
      boundaryCell boundaryRight T1 (lagOutputCursor [] suffix)
  have h0 :=
    leads_lagScan_keepL
      (s := .copy0) (target := .copy1 p0) (state_mem _)
      p0 (p1 :: p2 :: p3 :: p4 :: List.append tail lagHeader)
      (boundaryCell :: boundaryRight)
      T1 (lagOutputCursor [] suffix) (by intro _ _; rfl)
  have h1 :=
    leads_lagScan_keepL
      (s := .copy1 p0) (target := .copy2 p0 p1) (state_mem _)
      p1 (p2 :: p3 :: p4 :: List.append tail lagHeader)
      (some p0 :: boundaryCell :: boundaryRight)
      T1 (lagOutputCursor [] suffix) (by intro _ _; rfl)
  have h2 :=
    leads_lagScan_keepL
      (s := .copy2 p0 p1) (target := .copy3 p0 p1 p2) (state_mem _)
      p2 (p3 :: p4 :: List.append tail lagHeader)
      (some p1 :: some p0 :: boundaryCell :: boundaryRight)
      T1 (lagOutputCursor [] suffix) (by intro _ _; rfl)
  have h3 :=
    leads_lagScan_keepL
      (s := .copy3 p0 p1 p2) (target := .copy4 p0 p1 p2 p3)
      (state_mem _)
      p3 (p4 :: List.append tail lagHeader)
      (some p2 :: some p1 :: some p0 :: boundaryCell :: boundaryRight)
      T1 (lagOutputCursor [] suffix) (by intro _ _; rfl)
  have h4 :=
    leads_lagScan_keepL
      (s := .copy4 p0 p1 p2 p3)
      (target := .copy4p p1 p2 p3 p4 p0) (state_mem _)
      p4 (List.append tail lagHeader)
      (some p3 :: some p2 :: some p1 :: some p0 ::
        boundaryCell :: boundaryRight)
      T1 (lagOutputCursor [] suffix) (by intro _ _; rfl)
  have htail :=
    leads_copy4p_tail tail p1 p2 p3 p4 p0
      (some p4 :: some p3 :: some p2 :: some p1 :: some p0 ::
        boundaryCell :: boundaryRight)
      [] suffix T1
  have hfull :=
    henter.trans (h0.trans (h1.trans (h2.trans (h3.trans (h4.trans htail)))))
  simpa [lagFiveTail, List.reverse_cons, List.map_append,
    List.append_assoc] using hfull

private theorem leads_copyEnter_lag
    (metadata scratchPhysical : Word Bool)
    (hlen : 5 ≤ metadata.length)
    (boundaryCell : Option Bool)
    (boundaryRight : List (Option Bool))
    (T1 : Tape Bool) :
    Leads
      (cfg .copyEnter
        (tapeAtCells
          (List.append (metadata.reverse.map some)
            [some false, some false, some false, some false, none])
          (boundaryCell :: boundaryRight))
        T1 (metadataOutputStartTape scratchPhysical))
      (cfg .outputEnter
        (tapeAtCells [none]
          (List.append (tokBits MachineCodeSymbol.header)
            (List.append (metadata.map some)
              (boundaryCell :: boundaryRight))))
        T1 (metadataCopiedTape metadata scratchPhysical)) := by
  have hlenrev : 5 ≤ metadata.reverse.length := by
    simpa using hlen
  cases hrev : metadata.reverse with
  | nil => simp [hrev] at hlenrev
  | cons p0 r0 =>
      cases hr0 : r0 with
      | nil => simp [hrev, hr0] at hlenrev
      | cons p1 r1 =>
          cases hr1 : r1 with
          | nil => simp [hrev, hr0, hr1] at hlenrev
          | cons p2 r2 =>
              cases hr2 : r2 with
              | nil => simp [hrev, hr0, hr1, hr2] at hlenrev
              | cons p3 r3 =>
                  cases hr3 : r3 with
                  | nil => simp [hrev, hr0, hr1, hr2, hr3] at hlenrev
                  | cons p4 tail =>
                      have hshape : metadata.reverse =
                          lagFiveTail p0 p1 p2 p3 p4 tail := by
                        rw [hrev, hr0, hr1, hr2, hr3]
                        rfl
                      have hmetadataList :
                          (List.reverse metadata.reverse : List Bool) =
                            List.reverse (lagFiveTail p0 p1 p2 p3 p4 tail) :=
                        congrArg List.reverse hshape
                      rw [List.reverse_reverse] at hmetadataList
                      have hrun :=
                        leads_copyEnter_fiveTail p0 p1 p2 p3 p4 tail
                          boundaryCell boundaryRight
                          (none :: List.append (scratchPhysical.map some) [some false])
                          T1
                      simpa [hshape, hmetadataList, lagEntryTape,
                        lagOutputCursor, metadataOutputStartTape,
                        metadataCopiedTape, lagHeader, lagFiveTail,
                        List.map_append, List.append_assoc] using hrun

private theorem metadataBits_length_ge_five (L : SimulatorLayout) :
    5 ≤ (FieldDecomposition.metadataBits L).length := by
  rw [FieldDecomposition.metadataBits, encodeCodeWordAsInput_length]
  unfold FieldDecomposition.Metadata.encode FieldDecomposition.Metadata.encodeAppend
    FieldDecomposition.metadata
  simp [encodeBoolWordAppend, encodeCellListAppend, encodeNatAppend,
    encodeCellsAppend_length, ClassifiedBoundary.encodeNat_length]
  lia

private theorem postStateTape_eq_metadataShape (L : SimulatorLayout) :
    StateSelector.postStateTape L =
      tapeAtCells (List.append
          ((FieldDecomposition.metadataBits L).map some).reverse
          [some false, some false, some false, some false, none])
        (List.append (codeBits (StateSelector.postStateTokens L)) [none]) := by
  unfold StateSelector.postStateTape FieldDecomposition.metadataBits
    FieldDecomposition.metadata FieldDecomposition.Metadata.encode
    FieldDecomposition.Metadata.encodeAppend
  congr 1
  simp only [pushBits_eq_reverse_append]
  change _ = (codeBits (encodeBoolWordAppend L.input
        (encodeNatAppend L.stage
          (encodeNatAppend L.config.state [])))).reverse ++ _
  simp only [encodeBoolWordAppend, encodeCellListAppend,
    encodeNatAppend, encodeCellsAppend_eq_map, codeBits_append,
    tokBits_header]
  simp [codeBits_nil, List.reverse_append, List.append_assoc]

private theorem metadata_encode_eq_fields (L : SimulatorLayout) :
    (FieldDecomposition.metadata L).encode =
      List.append (encodeNat (L.input.map some).length)
        (List.append ((L.input.map some).map cellTok)
          (List.append (encodeNat L.stage) (encodeNat L.config.state))) := by
  unfold FieldDecomposition.metadata FieldDecomposition.Metadata.encode
    FieldDecomposition.Metadata.encodeAppend
  simp [encodeBoolWordAppend, encodeCellListAppend, encodeNatAppend,
    encodeCellsAppend_eq_map]

private theorem metadataBits_map_some_eq_fields (L : SimulatorLayout) :
    (FieldDecomposition.metadataBits L).map some =
      List.append (codeBits (encodeNat (L.input.map some).length))
        (List.append (codeBits ((L.input.map some).map cellTok))
          (List.append (codeBits (encodeNat L.stage))
            (codeBits (encodeNat L.config.state)))) := by
  change codeBits (FieldDecomposition.metadata L).encode = _
  rw [metadata_encode_eq_fields]
  simpa using
    (codeBits_append_six
      (encodeNat (L.input.map some).length)
      ((L.input.map some).map cellTok)
      (encodeNat L.stage)
      (encodeNat L.config.state)
      ([] : Word MachineCodeSymbol) ([] : Word MachineCodeSymbol))

private theorem headerStartTape_eq_metadataShape (L : SimulatorLayout) :
    headerStartTape L =
      tapeAtCells [none]
        (List.append (tokBits MachineCodeSymbol.header)
          (List.append ((FieldDecomposition.metadataBits L).map some)
            (List.append (codeBits (StateSelector.postStateTokens L))
              [none]))) := by
  unfold headerStartTape
  rw [StageCounter.rightEdgeTape_eq_decomposed,
    StateSelector.postStageTokens_eq_state_append, codeBits_append,
    metadataBits_map_some_eq_fields]
  simp [List.append_assoc]

private theorem leads_copyEnter_layout
    (L : SimulatorLayout) (scratchPhysical : Word Bool) (T1 : Tape Bool) :
    Leads
      (cfg .copyEnter
        (StateSelector.postStateTape L)
        T1 (metadataOutputStartTape scratchPhysical))
      (cfg .outputEnter (headerStartTape L) T1 (metadataCopiedTape
          (FieldDecomposition.metadataBits L) scratchPhysical)) := by
  rw [postStateTape_eq_metadataShape, headerStartTape_eq_metadataShape]
  cases hcode : codeBits (StateSelector.postStateTokens L) with
  | nil =>
      simpa [hcode, List.map_reverse] using
        leads_copyEnter_lag
          (FieldDecomposition.metadataBits L) scratchPhysical
          (metadataBits_length_ge_five L) none [] T1
  | cons boundaryCell boundaryRight =>
      simpa [hcode, List.map_reverse, List.append_assoc] using
        leads_copyEnter_lag
          (FieldDecomposition.metadataBits L) scratchPhysical
          (metadataBits_length_ge_five L) boundaryCell
          (List.append boundaryRight [none]) T1

private theorem leads_layout
    (D : MachineDescription) (L : SimulatorLayout) :
    Leads
      (cfg .start
        (StateSelector.postStateTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (StateSelector.selectorScratchTape D L))
      (cfg .halt
        (headerStartTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (ClassifiedBoundary.metadataHitTapeWithSelectorMarked D L)) := by
  have hmetadata : FieldDecomposition.metadataBits L ≠ [] := by
    intro hempty
    have hlen := metadataBits_length_ge_five L
    rw [hempty] at hlen
    simp at hlen
  have hposition :=
    leads_position_scratch
      (scratchBits D L) (scratchBits_ne_nil D L)
      (StateSelector.postStateTape L)
      (FieldDecomposition.stageCounterTape L.stage)
  have hcopy :=
    leads_copyEnter_layout L (scratchBits D L).reverse
      (FieldDecomposition.stageCounterTape L.stage)
  have hreturn :=
    leads_return_to_mark
      (FieldDecomposition.metadataBits L) (scratchBits D L).reverse
      hmetadata (headerStartTape L)
      (FieldDecomposition.stageCounterTape L.stage)
  have hfull := hposition.trans (hcopy.trans hreturn)
  rw [selectorScratchTape_eq_bits]
  simpa [ClassifiedBoundary.metadataHitTapeWithSelectorMarked,
    ClassifiedBoundary.classifiedMetadataLeft, scratchBits_map_some,
    List.map_reverse, List.append_assoc] using hfull

/-- The concrete metadata-prefix table reaches its exact logical target. -/
theorem runObligation : RunObligation := by
  intro D L
  rcases (leads_layout D L).to_runConfig with ⟨steps, hrun⟩
  exact ⟨steps, hrun⟩

/-!
## Physical lowering
-/

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady :=
  lowerStructured3Description_subroutineReady
    description_wellFormed description_supportsReadWriteRows3

theorem loweredDescription_haltsFromTapeEquiv
    (D : MachineDescription) (L : SimulatorLayout) :
    loweredDescription.HaltsFromTapeEquiv
      (sourceTape D L) (targetTape D L) := by
  unfold loweredDescription sourceTape targetTape
  apply lowerStructured3Description_haltsFromConfigWithTapes
    description_wellFormed description_haltTransitionFree
    description_supportsReadWriteRows3
    (c := ThreeTape.config description.start
      (StateSelector.postStateTape L)
      (FieldDecomposition.stageCounterTape L.stage)
      (StateSelector.selectorScratchTape D L))
  · rfl
  · rfl
  · exact runObligation D L
  done

end MetadataPrefix
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
