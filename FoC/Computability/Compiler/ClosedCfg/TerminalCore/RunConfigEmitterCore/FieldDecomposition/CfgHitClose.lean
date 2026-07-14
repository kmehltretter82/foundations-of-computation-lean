import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.CfgHitRuns

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore.FieldDecomposition.MetadataPrefix.ConfigTapeAndHit

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open StructuredConstructionTargets.FuelOutputCore

/-!
## Exact right-cell reconstruction
-/

/-- Cells accumulated on tape 0 by successive leftward writes. -/
def emittedCells
    (cells : List (Option Bool)) (right : List (Option Bool)) :
    List (Option Bool) :=
  cells.foldl (fun acc cell => cell :: acc) right

theorem emittedCells_eq_reverse_append
    (cells right : List (Option Bool)) :
    emittedCells cells right = List.append cells.reverse right := by
  induction cells generalizing right with
  | nil => rfl
  | cons cell rest ih =>
      rw [show emittedCells (cell :: rest) right =
        emittedCells rest (cell :: right) from rfl, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Tape-2 erased tail after backward cell decoding and entry into the
right-length rewind. -/
def erasedRightTail
    (cells : List (Option Bool)) (right : List (Option Bool)) :
    List (Option Bool) :=
  cells.foldl
    (fun acc _ => none :: none :: none :: none :: acc)
    (none :: none :: none :: right)

/-- Decode copied right-cell tokens backward, writing exact logical cells on
tape 0 and erasing every consumed workspace bit. -/
theorem leads_re_cells
    (hit : Bool) (cells : List (Option Bool)) (T1 : Tape Bool)
    (outputBaseLeft outputRight sourceBaseLeft erasedRight :
      List (Option Bool)) :
    Leads
      (cfg (.re3 hit)
        (tapeAtCells
          (List.append
            (List.replicate cells.length (none : Option Bool))
            outputBaseLeft)
          (none :: outputRight))
        T1
        (headTape
          (List.append (flatRevTokBits cells)
            (List.append doneRevBits sourceBaseLeft)) erasedRight))
      (cfg (.rt0 hit)
        (tapeAtCells outputBaseLeft
          (none :: emittedCells cells outputRight))
        T1
        (tapeAtCells sourceBaseLeft
          (some false :: erasedRightTail cells erasedRight))) := by
  induction cells generalizing outputRight erasedRight with
  | nil =>
      exact
        (step2L_write (state_mem (.re3 hit)) (fun _ _ => rfl)
          (tapeAtCells outputBaseLeft (none :: outputRight)) T1
          (some false :: some false :: sourceBaseLeft) (some true)
          erasedRight).trans
          ((step2L_write (state_mem (.re2 hit true)) (fun _ _ => rfl)
            (tapeAtCells outputBaseLeft (none :: outputRight)) T1
            (some false :: sourceBaseLeft) (some false)
            (none :: erasedRight)).trans
            (step2L_write (state_mem (.re1 hit true true))
              (fun _ _ => rfl)
              (tapeAtCells outputBaseLeft (none :: outputRight)) T1
              sourceBaseLeft (some false) (none :: none :: erasedRight)))
  | cons cell rest ih =>
      rw [flatRevTokBits_cons]
      cases cell with
      | none =>
          refine Leads.trans
            (step2L_write (state_mem (.re3 hit)) (fun _ _ => rfl)
              (tapeAtCells
                (none :: List.append
                  (List.replicate rest.length none) outputBaseLeft)
                (none :: outputRight)) T1 _ _ erasedRight) ?_
          refine Leads.trans
            (step2L_write (state_mem (.re2 hit false)) (fun _ _ => rfl)
              (tapeAtCells
                (none :: List.append
                  (List.replicate rest.length none) outputBaseLeft)
                (none :: outputRight)) T1 _ _ (none :: erasedRight)) ?_
          refine Leads.trans
            (step2L_write (state_mem (.re1 hit false false))
              (fun _ _ => rfl)
              (tapeAtCells
                (none :: List.append
                  (List.replicate rest.length none) outputBaseLeft)
                (none :: outputRight)) T1 _ _
              (none :: none :: erasedRight)) ?_
          refine Leads.trans
            (step02L_write_headTape (state_mem (.re0 hit none))
              (fun _ => rfl)
              (List.append (List.replicate rest.length none) outputBaseLeft)
              none outputRight T1
              (by simp [doneRevBits])
              (none :: none :: none :: erasedRight)) ?_
          exact ih (none :: outputRight)
            (none :: none :: none :: none :: erasedRight)
      | some bit =>
          cases bit with
          | false =>
              refine Leads.trans
                (step2L_write (state_mem (.re3 hit)) (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 _ _ erasedRight) ?_
              refine Leads.trans
                (step2L_write (state_mem (.re2 hit true))
                  (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 _ _
                  (none :: erasedRight)) ?_
              refine Leads.trans
                (step2L_write (state_mem (.re1 hit true false))
                  (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 _ _
                  (none :: none :: erasedRight)) ?_
              refine Leads.trans
                (step02L_write_headTape
                  (state_mem (.re0 hit (some false)))
                  (fun _ => rfl)
                  (List.append
                    (List.replicate rest.length none) outputBaseLeft)
                  none outputRight T1
                  (by simp [doneRevBits])
                  (none :: none :: none :: erasedRight)) ?_
              exact ih (some false :: outputRight)
                (none :: none :: none :: none :: erasedRight)
          | true =>
              refine Leads.trans
                (step2L_write (state_mem (.re3 hit)) (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 _ _ erasedRight) ?_
              refine Leads.trans
                (step2L_write (state_mem (.re2 hit false))
                  (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 _ _
                  (none :: erasedRight)) ?_
              refine Leads.trans
                (step2L_write (state_mem (.re1 hit false true))
                  (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 _ _
                  (none :: none :: erasedRight)) ?_
              refine Leads.trans
                (step02L_write_headTape
                  (state_mem (.re0 hit (some true)))
                  (fun _ => rfl)
                  (List.append
                    (List.replicate rest.length none) outputBaseLeft)
                  none outputRight T1
                  (by simp [doneRevBits])
                  (none :: none :: none :: erasedRight)) ?_
              exact ih (some true :: outputRight)
                (none :: none :: none :: none :: erasedRight)

/-!
## Right-length rewind and exact head reconstruction
-/

/-- Erased tape-2 tail accumulated while rewinding the right-length ticks. -/
def erasedRightLengthTail :
    Nat → List (Option Bool) → List (Option Bool)
  | 0, right => none :: none :: none :: none :: right
  | n + 1, right =>
      erasedRightLengthTail n
        (none :: none :: none :: none :: right)

/-- Rewind the right-length ticks and stop on the marked first bit of the
encoded head token. -/
theorem leads_rt
    (hit : Bool) (n : Nat) {head : Option Bool} {v2 v3 : Bool}
    (hbits :
      tokBits (cellTok head) =
        [some false, some true, some v2, some v3]) :
    forall (sourceBaseLeft erasedRight : List (Option Bool))
      (T0 T1 : Tape Bool),
      Leads
        (cfg (.rt0 hit) T0 T1
          (tapeAtCells
            (List.append (tickRevBits n)
              (List.append (markedBits head).reverse sourceBaseLeft))
            (some false :: erasedRight)))
        (cfg (.hd0 hit v3 v2) T0 T1
          (tapeAtCells sourceBaseLeft
            (some true :: erasedRightLengthTail n erasedRight))) := by
  rw [markedBits_eq hbits]
  induction n with
  | zero =>
      intro sourceBaseLeft erasedRight T0 T1
      exact
        (step2L_write (state_mem (.rt0 hit)) (fun _ _ => rfl)
          T0 T1 (some v2 :: some true :: some true :: sourceBaseLeft)
          (some v3) erasedRight).trans
          ((step2L_write (state_mem (.rt3 hit)) (fun _ _ => rfl)
            T0 T1 (some true :: some true :: sourceBaseLeft)
            (some v2) (none :: erasedRight)).trans
            ((step2L_write (state_mem (.rt2 hit v3)) (fun _ _ => rfl)
              T0 T1 (some true :: sourceBaseLeft)
              (some true) (none :: none :: erasedRight)).trans
              (step2L_write (state_mem (.rt1 hit v3 v2))
                (fun _ _ => rfl) T0 T1 sourceBaseLeft (some true)
                (none :: none :: none :: erasedRight))))
  | succ n ih =>
      intro sourceBaseLeft erasedRight T0 T1
      refine Leads.trans
        (step2L_write (state_mem (.rt0 hit)) (fun _ _ => rfl)
          T0 T1 _ _ erasedRight) ?_
      refine Leads.trans
        (step2L_write (state_mem (.rt3 hit)) (fun _ _ => rfl)
          T0 T1 _ _ (none :: erasedRight)) ?_
      refine Leads.trans
        (step2L_write (state_mem (.rt2 hit false)) (fun _ _ => rfl)
          T0 T1 _ _ (none :: none :: erasedRight)) ?_
      refine Leads.trans
        (step2L_write (state_mem (.rt1 hit false true))
          (fun _ _ => rfl) T0 T1 _ _
          (none :: none :: none :: erasedRight)) ?_
      exact ih sourceBaseLeft
        (none :: none :: none :: none :: erasedRight) T0 T1

/-- Decode the marked head tail, write the exact head cell on tape 0, and
enter the left-list scan. -/
theorem leads_hd
    (hit : Bool) {head : Option Bool} {v2 v3 : Bool}
    (hbits :
      tokBits (cellTok head) =
        [some false, some true, some v2, some v3])
    (outputBaseLeft outputRight sourceLeft : List (Option Bool))
    (hsourceLeft : sourceLeft ≠ [])
    (erasedRight : List (Option Bool)) (T1 : Tape Bool) :
    Leads
      (cfg (.hd0 hit v3 v2)
        (tapeAtCells (none :: outputBaseLeft) (none :: outputRight)) T1
        (tapeAtCells sourceLeft (some true :: erasedRight)))
      (cfg (.ls3 hit)
        (tapeAtCells outputBaseLeft (none :: head :: outputRight)) T1
        (headTape sourceLeft (none :: erasedRight))) := by
  cases head with
  | none =>
      have hbits' :
          ([some false, some true, some false, some false] :
              List (Option Bool)) =
            [some false, some true, some v2, some v3] := hbits
      simp at hbits'
      obtain ⟨hv2, hv3⟩ := hbits'
      subst hv2
      subst hv3
      exact
        step02L_write_headTape (state_mem (.hd0 hit false false))
          (fun _ => rfl) outputBaseLeft none outputRight T1
          hsourceLeft erasedRight
  | some bit =>
      cases bit with
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
            step02L_write_headTape (state_mem (.hd0 hit true false))
              (fun _ => rfl) outputBaseLeft none outputRight T1
              hsourceLeft erasedRight
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
            step02L_write_headTape (state_mem (.hd0 hit false true))
              (fun _ => rfl) outputBaseLeft none outputRight T1
              hsourceLeft erasedRight

/-!
## Left-list turnaround and reconstruction
-/

/-- Skip the copied left-cell tokens leftward and turn around at the encoded
left-length done token. -/
theorem leads_ls
    (hit : Bool) (leftCells : List (Option Bool)) :
    forall (sourceBaseLeft cellsRight : List (Option Bool))
      (T0 T1 : Tape Bool),
      Leads
        (cfg (.ls3 hit) T0 T1
          (headTape
            (List.append (flatRevTokBits leftCells)
              (List.append doneRevBits sourceBaseLeft)) cellsRight))
        (cfg (.le0 hit) T0 T1
          (tapeAtCells (pushBits doneBitsF sourceBaseLeft)
            (unwalkBits leftCells cellsRight))) := by
  induction leftCells with
  | nil =>
      intro sourceBaseLeft cellsRight T0 T1
      exact
        (step2L (state_mem (.ls3 hit)) (fun _ _ => rfl)
          T0 T1 (some false :: some false :: sourceBaseLeft)
          (some true) cellsRight).trans
          ((step2L (state_mem (.ls2 hit)) (fun _ _ => rfl)
            T0 T1 (some false :: sourceBaseLeft)
            (some false) (some true :: cellsRight)).trans
            ((step2R (state_mem (.ls1 hit)) (fun _ _ => rfl)
              T0 T1 (some false :: sourceBaseLeft)
              (some true :: some true :: cellsRight)).trans
              ((step2R (state_mem (.turn1 hit)) (fun _ _ => rfl)
                T0 T1 (some false :: some false :: sourceBaseLeft)
                (some true :: cellsRight)).trans
                (step2R (state_mem (.turn2 hit)) (fun _ _ => rfl)
                  T0 T1
                  (some true :: some false :: some false :: sourceBaseLeft)
                  cellsRight))))
  | cons cell rest ih =>
      intro sourceBaseLeft cellsRight T0 T1
      obtain ⟨v2, v3, hbits⟩ := exists_cellTok_bits cell
      rw [flatRevTokBits_cons, hbits, unwalkBits_cons, hbits]
      refine Leads.trans
        (step2L (state_mem (.ls3 hit)) (fun _ _ => rfl)
          T0 T1 _ _ cellsRight) ?_
      refine Leads.trans
        (step2L (state_mem (.ls2 hit)) (fun _ _ => rfl)
          T0 T1 _ _ (some v3 :: cellsRight)) ?_
      refine Leads.trans
        (step2L (state_mem (.ls1 hit)) (fun _ _ => rfl)
          T0 T1 _ _ (some v2 :: some v3 :: cellsRight)) ?_
      refine Leads.trans
        (step2L_headTape (state_mem (.ls0 hit)) (fun _ _ => rfl)
          T0 T1 (append_cons_ne_nil _ _ _)
          (some true :: some v2 :: some v3 :: cellsRight)) ?_
      exact ih sourceBaseLeft _ T0 T1

/-- Scan the left-cell tokens forward, writing the exact logical cells on
tape 0 while preserving the copied token bits on tape 2. -/
theorem leads_le
    (hit : Bool) (leftCells : List (Option Bool)) :
    forall (outputBaseLeft outputRight sourceLeft sourceRight :
      List (Option Bool)) (T1 : Tape Bool),
      Leads
        (cfg (.le0 hit)
          (tapeAtCells
            (List.append
              (List.replicate leftCells.length (none : Option Bool))
              outputBaseLeft)
            (none :: outputRight)) T1
          (tapeAtCells sourceLeft
            (List.append (codeBits (leftCells.map cellTok)) sourceRight)))
        (cfg (.le0 hit)
          (tapeAtCells outputBaseLeft
            (none :: emittedCells leftCells outputRight)) T1
          (tapeAtCells
            (pushBits (codeBits (leftCells.map cellTok)) sourceLeft)
            sourceRight)) := by
  induction leftCells with
  | nil =>
      intro outputBaseLeft outputRight sourceLeft sourceRight T1
      exact Leads.refl _
  | cons cell rest ih =>
      intro outputBaseLeft outputRight sourceLeft sourceRight T1
      have hcode :
          codeBits ((cell :: rest).map cellTok) =
            List.append (tokBits (cellTok cell))
              (codeBits (rest.map cellTok)) :=
        codeBits_cons _ _
      rw [hcode]
      cases cell with
      | none =>
          refine Leads.trans
            (step2R (state_mem (.le0 hit)) (fun _ _ => rfl)
              (tapeAtCells
                (none :: List.append
                  (List.replicate rest.length none) outputBaseLeft)
                (none :: outputRight)) T1 sourceLeft _) ?_
          refine Leads.trans
            (step2R (state_mem (.le1 hit)) (fun _ _ => rfl)
              (tapeAtCells
                (none :: List.append
                  (List.replicate rest.length none) outputBaseLeft)
                (none :: outputRight)) T1 _ _) ?_
          refine Leads.trans
            (step2R (state_mem (.le2 hit)) (fun _ _ => rfl)
              (tapeAtCells
                (none :: List.append
                  (List.replicate rest.length none) outputBaseLeft)
                (none :: outputRight)) T1 _ _) ?_
          refine Leads.trans
            (step0L2R_write (state_mem (.le3 hit false))
              (fun _ => rfl)
              (List.append (List.replicate rest.length none) outputBaseLeft)
              none outputRight T1 _ _) ?_
          exact ih outputBaseLeft (none :: outputRight) _ sourceRight T1
      | some bit =>
          cases bit with
          | false =>
              refine Leads.trans
                (step2R (state_mem (.le0 hit)) (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 sourceLeft _) ?_
              refine Leads.trans
                (step2R (state_mem (.le1 hit)) (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 _ _) ?_
              refine Leads.trans
                (step2R (state_mem (.le2 hit)) (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 _ _) ?_
              refine Leads.trans
                (step0L2R_write (state_mem (.le3 hit false))
                  (fun _ => rfl)
                  (List.append
                    (List.replicate rest.length none) outputBaseLeft)
                  none outputRight T1 _ _) ?_
              exact ih outputBaseLeft (some false :: outputRight)
                _ sourceRight T1
          | true =>
              refine Leads.trans
                (step2R (state_mem (.le0 hit)) (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 sourceLeft _) ?_
              refine Leads.trans
                (step2R (state_mem (.le1 hit)) (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 _ _) ?_
              refine Leads.trans
                (step2R (state_mem (.le2 hit)) (fun _ _ => rfl)
                  (tapeAtCells
                    (none :: List.append
                      (List.replicate rest.length none) outputBaseLeft)
                    (none :: outputRight)) T1 _ _) ?_
              refine Leads.trans
                (step0L2R_write (state_mem (.le3 hit true))
                  (fun _ => rfl)
                  (List.append
                    (List.replicate rest.length none) outputBaseLeft)
                  none outputRight T1 _ _) ?_
              exact ih outputBaseLeft (some true :: outputRight)
                _ sourceRight T1

/-!
## Head repositioning and workspace cleanup
-/

/-- Mark the first surplus tape-0 workspace cell, advance to the first
reconstructed left cell, and turn tape 2 back toward the copied fields.  The
temporary marker makes the semantic left boundary detectable after physical
three-tape lowering. -/
theorem leads_position_start
    (hit : Bool) (tape0Left tape0Right : List (Option Bool))
    (T1 : Tape Bool) (sourceLeft : List (Option Bool))
    (hsourceLeft : sourceLeft ≠ [])
    (erasedRight : List (Option Bool)) :
    Leads
      (cfg (.le0 hit)
        (tapeAtCells tape0Left (none :: tape0Right)) T1
        (tapeAtCells sourceLeft (none :: erasedRight)))
      (cfg (.pos3 hit)
        (tapeAtCells (some false :: tape0Left) tape0Right) T1
        (headTape sourceLeft (none :: erasedRight))) :=
  step0R_write2L_headTape (state_mem (.le0 hit)) (fun _ => rfl)
    tape0Left tape0Right T1 hsourceLeft erasedRight

/-- Erase the copied left-cell tokens backward while moving tape 0 right once
per reconstructed cell, stopping on the left-length done token. -/
theorem leads_pos_cells
    (hit : Bool) (leftCells : List (Option Bool)) :
    forall (tape0Left tape0Right sourceBaseLeft erasedRight :
      List (Option Bool)) (T1 : Tape Bool),
      Leads
        (cfg (.pos3 hit)
          (tapeAtCells tape0Left
            (List.append leftCells tape0Right)) T1
          (headTape
            (List.append (flatRevTokBits leftCells)
              (List.append doneRevBits sourceBaseLeft)) erasedRight))
        (cfg (.eraseLen hit)
          (tapeAtCells (emittedCells leftCells tape0Left) tape0Right) T1
          (tapeAtCells sourceBaseLeft
            (some false :: erasedRightTail leftCells erasedRight))) := by
  induction leftCells with
  | nil =>
      intro tape0Left tape0Right sourceBaseLeft erasedRight T1
      exact
        (step2L_write (state_mem (.pos3 hit)) (fun _ _ => rfl)
          (tapeAtCells tape0Left tape0Right) T1
          (some false :: some false :: sourceBaseLeft)
          (some true) erasedRight).trans
          ((step2L_write (state_mem (.pos2 hit true)) (fun _ _ => rfl)
            (tapeAtCells tape0Left tape0Right) T1
            (some false :: sourceBaseLeft)
            (some false) (none :: erasedRight)).trans
            (step2L_write (state_mem (.pos1 hit true true))
              (fun _ _ => rfl) (tapeAtCells tape0Left tape0Right) T1
              sourceBaseLeft (some false)
              (none :: none :: erasedRight)))
  | cons cell rest ih =>
      intro tape0Left tape0Right sourceBaseLeft erasedRight T1
      rw [flatRevTokBits_cons]
      cases cell with
      | none =>
          refine Leads.trans
            (step2L_write (state_mem (.pos3 hit)) (fun _ _ => rfl)
              (tapeAtCells tape0Left
                (none :: List.append rest tape0Right)) T1
              _ _ erasedRight) ?_
          refine Leads.trans
            (step2L_write (state_mem (.pos2 hit false))
              (fun _ _ => rfl)
              (tapeAtCells tape0Left
                (none :: List.append rest tape0Right)) T1
              _ _ (none :: erasedRight)) ?_
          refine Leads.trans
            (step2L_write (state_mem (.pos1 hit false false))
              (fun _ _ => rfl)
              (tapeAtCells tape0Left
                (none :: List.append rest tape0Right)) T1
              _ _ (none :: none :: erasedRight)) ?_
          refine Leads.trans
            (step0R2L_write_headTape (state_mem (.pos0 hit))
              (fun _ => rfl) tape0Left (List.append rest tape0Right) T1
              (by simp [doneRevBits])
              (none :: none :: none :: erasedRight)) ?_
          exact ih (none :: tape0Left) tape0Right sourceBaseLeft
            (none :: none :: none :: none :: erasedRight) T1
      | some bit =>
          cases bit with
          | false =>
              refine Leads.trans
                (step2L_write (state_mem (.pos3 hit)) (fun _ _ => rfl)
                  (tapeAtCells tape0Left
                    (some false :: List.append rest tape0Right)) T1
                  _ _ erasedRight) ?_
              refine Leads.trans
                (step2L_write (state_mem (.pos2 hit true))
                  (fun _ _ => rfl)
                  (tapeAtCells tape0Left
                    (some false :: List.append rest tape0Right)) T1
                  _ _ (none :: erasedRight)) ?_
              refine Leads.trans
                (step2L_write (state_mem (.pos1 hit true false))
                  (fun _ _ => rfl)
                  (tapeAtCells tape0Left
                    (some false :: List.append rest tape0Right)) T1
                  _ _ (none :: none :: erasedRight)) ?_
              refine Leads.trans
                (step0R2L_write_headTape (state_mem (.pos0 hit))
                  (fun _ => rfl) tape0Left
                  (List.append rest tape0Right) T1
                  (by simp [doneRevBits])
                  (none :: none :: none :: erasedRight)) ?_
              exact ih (some false :: tape0Left) tape0Right sourceBaseLeft
                (none :: none :: none :: none :: erasedRight) T1
          | true =>
              refine Leads.trans
                (step2L_write (state_mem (.pos3 hit)) (fun _ _ => rfl)
                  (tapeAtCells tape0Left
                    (some true :: List.append rest tape0Right)) T1
                  _ _ erasedRight) ?_
              refine Leads.trans
                (step2L_write (state_mem (.pos2 hit false))
                  (fun _ _ => rfl)
                  (tapeAtCells tape0Left
                    (some true :: List.append rest tape0Right)) T1
                  _ _ (none :: erasedRight)) ?_
              refine Leads.trans
                (step2L_write (state_mem (.pos1 hit false true))
                  (fun _ _ => rfl)
                  (tapeAtCells tape0Left
                    (some true :: List.append rest tape0Right)) T1
                  _ _ (none :: none :: erasedRight)) ?_
              refine Leads.trans
                (step0R2L_write_headTape (state_mem (.pos0 hit))
                  (fun _ => rfl) tape0Left
                  (List.append rest tape0Right) T1
                  (by simp [doneRevBits])
                  (none :: none :: none :: erasedRight)) ?_
              exact ih (some true :: tape0Left) tape0Right sourceBaseLeft
                (none :: none :: none :: none :: erasedRight) T1

/-- Erased tape-2 tail accumulated while removing the left-length ticks and
crossing the workspace delimiter. -/
def erasedLeftLengthTail :
    Nat → List (Option Bool) → List (Option Bool)
  | 0, right => none :: none :: right
  | n + 1, right =>
      erasedLeftLengthTail n
        (none :: none :: none :: none :: right)

/-- Erase the remaining left-length field, cross the retained workspace
delimiter, restore the saved hit, and halt. -/
theorem leads_erase_length_restore
    (hit : Bool) (n : Nat) :
    forall (metadataLeft erasedRight : List (Option Bool))
      (T0 T1 : Tape Bool),
      Leads
        (cfg (.eraseLen hit) T0 T1
          (tapeAtCells
            (List.append (tickRevBits n)
              (none :: some false :: metadataLeft))
            (some false :: erasedRight)))
        (cfg .halt T0 T1
          (tapeAtCells metadataLeft
            (some hit :: erasedLeftLengthTail n erasedRight))) := by
  induction n with
  | zero =>
      intro metadataLeft erasedRight T0 T1
      exact
        (step2L_write (state_mem (.eraseLen hit)) (fun _ _ => rfl)
          T0 T1 (some false :: metadataLeft) none erasedRight).trans
          ((step2L (state_mem (.eraseLen hit)) (fun _ _ => rfl)
            T0 T1 metadataLeft (some false)
            (none :: erasedRight)).trans
            (step2S_write (state_mem (.restore hit)) (fun _ _ => rfl)
              T0 T1 metadataLeft (none :: none :: erasedRight)))
  | succ n ih =>
      intro metadataLeft erasedRight T0 T1
      refine Leads.trans
        (step2L_write (state_mem (.eraseLen hit)) (fun _ _ => rfl)
          T0 T1 _ _ erasedRight) ?_
      refine Leads.trans
        (step2L_write (state_mem (.eraseLen hit)) (fun _ _ => rfl)
          T0 T1 _ _ (none :: erasedRight)) ?_
      refine Leads.trans
        (step2L_write (state_mem (.eraseLen hit)) (fun _ _ => rfl)
          T0 T1 _ _ (none :: none :: erasedRight)) ?_
      refine Leads.trans
        (step2L_write (state_mem (.eraseLen hit)) (fun _ _ => rfl)
          T0 T1 _ _ (none :: none :: none :: erasedRight)) ?_
      exact ih metadataLeft
        (none :: none :: none :: none :: erasedRight) T0 T1

/-!
## Full layout composition
-/

/-- One tape-0 blank is consumed for each reconstructed right cell, the head,
and each reconstructed left cell. -/
def reconstructionCellCount (L : SimulatorLayout) : Nat :=
  L.config.tape.right.length + 1 + L.config.tape.left.length

theorem configurationSuffixCells_eq
    (L : SimulatorLayout) :
    (configurationSuffixBits L).map some =
      List.append (codeBits (encodeNat L.config.tape.left.length))
        (List.append (codeBits (L.config.tape.left.map cellTok))
          (List.append (tokBits (cellTok L.config.tape.head))
            (List.append
              (codeBits (encodeNat L.config.tape.right.length))
              (List.append
                (codeBits (L.config.tape.right.map cellTok))
                (tokBits (cellTok (some L.hit))))))) := by
  unfold configurationSuffixBits
  change codeBits (StateSelector.postStateTokens L) = _
  unfold StateSelector.postStateTokens
  rw [codeBits_append]
  rw [codeBits_append]
  rw [codeBits_cons]
  rw [codeBits_append]
  rw [codeBits_append]
  rw [codeBits_cons, codeBits_nil]
  have hnil :
      List.append (tokBits (cellTok (some L.hit))) [] =
        tokBits (cellTok (some L.hit)) :=
    List.append_nil _
  rw [hnil]

theorem configurationSuffixCells_append_none_eq
    (L : SimulatorLayout) :
    List.append ((configurationSuffixBits L).map some) [none] =
      List.append (codeBits (encodeNat L.config.tape.left.length))
        (List.append (codeBits (L.config.tape.left.map cellTok))
          (List.append (tokBits (cellTok L.config.tape.head))
            (List.append
              (codeBits (encodeNat L.config.tape.right.length))
              (List.append
                (codeBits (L.config.tape.right.map cellTok))
                (List.append (tokBits (cellTok (some L.hit))) [none]))))) := by
  let leftLengthCells : List (Option Bool) :=
    codeBits (encodeNat L.config.tape.left.length)
  let leftCells : List (Option Bool) :=
    codeBits (L.config.tape.left.map cellTok)
  let headCells : List (Option Bool) :=
    tokBits (cellTok L.config.tape.head)
  let rightLengthCells : List (Option Bool) :=
    codeBits (encodeNat L.config.tape.right.length)
  let rightCells : List (Option Bool) :=
    codeBits (L.config.tape.right.map cellTok)
  let hitCells : List (Option Bool) :=
    tokBits (cellTok (some L.hit))
  have hcells := configurationSuffixCells_eq L
  change
    (configurationSuffixBits L).map some =
      leftLengthCells ++
        (leftCells ++
          (headCells ++
            (rightLengthCells ++ (rightCells ++ hitCells)))) at hcells
  change
    (configurationSuffixBits L).map some ++ [none] =
      leftLengthCells ++
        (leftCells ++
          (headCells ++
            (rightLengthCells ++ (rightCells ++ (hitCells ++ [none])))))
  rw [hcells]
  simp only [List.append_assoc]

theorem reconstructionCellCount_le_suffix
    (L : SimulatorLayout) :
    reconstructionCellCount L ≤ (configurationSuffixBits L).length := by
  rw [configurationSuffixBits, encodeCodeWordAsInput_length]
  have hpost :
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
  have htail :
      (List.append (L.config.tape.left.map cellTok)
          (cellTok L.config.tape.head ::
            List.append
              (show List MachineCodeSymbol from
                encodeNat L.config.tape.right.length)
              (List.append (L.config.tape.right.map cellTok)
                [cellTok (some L.hit)]))).length =
        L.config.tape.left.length + 1 +
          (show List MachineCodeSymbol from
            encodeNat L.config.tape.right.length).length +
          L.config.tape.right.length + 1 := by
    let leftCells : List MachineCodeSymbol :=
      L.config.tape.left.map cellTok
    let rightLength : List MachineCodeSymbol :=
      encodeNat L.config.tape.right.length
    let rightCells : List MachineCodeSymbol :=
      L.config.tape.right.map cellTok
    change
      (leftCells ++
        (cellTok L.config.tape.head ::
          rightLength ++ (rightCells ++ [cellTok (some L.hit)]))).length =
        L.config.tape.left.length + 1 + rightLength.length +
          L.config.tape.right.length + 1
    simp [leftCells, rightCells]
    lia
  rw [hpost, htail]
  unfold reconstructionCellCount
  lia

/-- Far-left blank residue not needed as one-cell work slots during logical
configuration reconstruction. -/
def reconstructionBaseLeft (L : SimulatorLayout) :
    List (Option Bool) :=
  List.append
    (List.replicate
      ((configurationSuffixBits L).length - reconstructionCellCount L)
      (none : Option Bool))
    (erasedPrefixLeft L)

theorem erasedLayoutTape_eq_reconstructionSlots
    (L : SimulatorLayout) :
    erasedLayoutTape L =
      tapeAtCells
        (List.append
          (List.replicate L.config.tape.right.length
            (none : Option Bool))
          (none :: List.append
            (List.replicate L.config.tape.left.length none)
            (reconstructionBaseLeft L)))
        [none] := by
  unfold erasedLayoutTape reconstructionBaseLeft
  rw [pushBlanks_eq_replicate_append]
  simp only [List.length_map]
  have hcapacity := reconstructionCellCount_le_suffix L
  have houter :=
    FoC.Computability.list_replicate_add_append
      (none : Option Bool) (reconstructionCellCount L)
      ((configurationSuffixBits L).length - reconstructionCellCount L)
      (erasedPrefixLeft L)
  rw [Nat.add_sub_of_le hcapacity] at houter
  have hslots :=
    FoC.Computability.list_replicate_add_append
      (none : Option Bool) L.config.tape.right.length
      (1 + L.config.tape.left.length)
      (List.append
        (List.replicate
          ((configurationSuffixBits L).length - reconstructionCellCount L)
          (none : Option Bool))
        (erasedPrefixLeft L))
  apply congrArg (fun left : List (Option Bool) => tapeAtCells left [none])
  calc
    List.append
        (List.replicate (configurationSuffixBits L).length none)
        (erasedPrefixLeft L) =
      List.append
        (List.replicate (reconstructionCellCount L) none)
        (List.append
          (List.replicate
            ((configurationSuffixBits L).length - reconstructionCellCount L)
            none)
          (erasedPrefixLeft L)) := houter
    _ = _ := by
      simpa [reconstructionCellCount, Nat.add_assoc, Nat.one_add,
        List.replicate_succ, List.append_assoc] using hslots

/-- Final all-blank tape-2 residue after reconstruction and cleanup. -/
def finalErasedRight
    (L : SimulatorLayout) : List (Option Bool) :=
  erasedLeftLengthTail L.config.tape.left.length
    (erasedRightTail L.config.tape.left.reverse
      (none ::
        erasedRightLengthTail L.config.tape.right.length
          (erasedRightTail L.config.tape.right.reverse
            [none, none, none, none, none])))

/-- Physical configuration tape produced by the concrete table.  Its only
difference from the logical configuration is far-left blank residue. -/
def actualConfigTape (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells
    (emittedCells L.config.tape.left.reverse
      (none :: reconstructionBaseLeft L))
    (L.config.tape.head :: List.append L.config.tape.right [])

/-- Exact configuration tape produced after the CfgHit table marks the first
surplus reconstruction cell.  A later physical repair phase consumes this
sentinel and restores the canonical guarded boundary. -/
def markedActualConfigTape (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells
    (emittedCells L.config.tape.left.reverse
      (some false :: reconstructionBaseLeft L))
    (L.config.tape.head :: List.append L.config.tape.right [])

/-- Physical metadata tape produced by the concrete table.  Its only
difference from the classified target is far-right blank residue. -/
def actualMetadataTape
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells (ClassifiedBoundary.classifiedMetadataLeft D L)
    (some L.hit :: finalErasedRight L)

private theorem leads_layout
    (D : MachineDescription) (L : SimulatorLayout) :
    Leads
      (cfg .hdr0 (headerStartTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (ClassifiedBoundary.metadataHitTapeWithSelectorMarked D L))
      (cfg .halt (markedActualConfigTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (actualMetadataTape D L)) := by
  refine Leads.trans
    (leads_to_configuration_suffix D L
      (FieldDecomposition.stageCounterTape L.stage)) ?_
  rw [erasedLayoutTape_eq_reconstructionSlots]
  unfold workspaceStartTape
  rw [configurationSuffixCells_append_none_eq]
  refine Leads.trans
    (leads_lLen L.config.tape.left.length _ _
      (workspaceBaseLeft D L) _) ?_
  refine Leads.trans
    (leads_lb L.config.tape.left _ _ _ _) ?_
  refine Leads.trans
    (leads_lb_one L.config.tape.head _ _ _ _) ?_
  refine Leads.trans
    (leads_mark_rLen L.config.tape.head L.config.tape.right.length
      _ _ _ _) ?_
  refine Leads.trans
    (leads_rb L.config.tape.right _ _ _ _) ?_
  refine Leads.trans
    (leads_rb_one (some L.hit) _ _ _ [none]) ?_
  refine Leads.trans
    (leads_hit_decode L.hit _ _ _ (by simp [pushBits, markedBits])) ?_
  simp only [pushBits_eq_reverse_append, codeBits_cells_reverse,
    codeBits_encodeNat_reverse]
  have hre :=
    leads_re_cells L.hit L.config.tape.right.reverse
      (FieldDecomposition.stageCounterTape L.stage)
      (none :: List.append
        (List.replicate L.config.tape.left.length none)
        (reconstructionBaseLeft L)) []
      (List.append (tickRevBits L.config.tape.right.length)
        (List.append (markedBits L.config.tape.head).reverse
          (List.append (flatRevTokBits L.config.tape.left.reverse)
            (List.append doneRevBits
              (List.append (tickRevBits L.config.tape.left.length)
                (workspaceBaseLeft D L))))))
      [none, none, none, none, none]
  have hre' := hre
  simp only [List.length_reverse] at hre'
  refine hre'.trans ?_
  obtain ⟨headv2, headv3, hheadbits⟩ :=
    exists_cellTok_bits L.config.tape.head
  refine Leads.trans
    (leads_rt L.hit L.config.tape.right.length hheadbits _ _ _ _) ?_
  refine Leads.trans
    (leads_hd L.hit hheadbits _ _ _
      (by simp [doneRevBits]) _ _) ?_
  refine Leads.trans
    (leads_ls L.hit L.config.tape.left.reverse _ _ _ _) ?_
  rw [unwalkBits_reverse_eq, emittedCells_eq_reverse_append]
  simp only [List.reverse_reverse]
  refine Leads.trans
    (leads_le L.hit L.config.tape.left _ _ _ _ _) ?_
  refine Leads.trans
    (leads_position_start L.hit _ _ _ _
      (by simp [pushBits, doneBitsF]) _) ?_
  rw [emittedCells_eq_reverse_append]
  simp only [pushBits_eq_reverse_append, codeBits_cells_reverse]
  rw [show doneBitsF.reverse = doneRevBits from rfl]
  refine Leads.trans
    (leads_pos_cells L.hit L.config.tape.left.reverse _ _ _ _ _) ?_
  unfold markedActualConfigTape actualMetadataTape finalErasedRight
  unfold workspaceBaseLeft
  exact leads_erase_length_restore L.hit L.config.tape.left.length
    _ _ _ _

/-!
## Represented-target equivalence and physical lowering
-/

def AllNone (cells : List (Option Bool)) : Prop :=
  forall cell, cell ∈ cells → cell = none

theorem allNone_nil : AllNone [] := by
  intro cell hcell
  cases hcell

theorem allNone_cons
    {cells : List (Option Bool)} (h : AllNone cells) :
    AllNone (none :: cells) := by
  intro cell hcell
  rcases List.mem_cons.mp hcell with hhead | htail
  · exact hhead
  · exact h cell htail

theorem allNone_append
    {first second : List (Option Bool)}
    (hfirst : AllNone first) (hsecond : AllNone second) :
    AllNone (List.append first second) := by
  intro cell hcell
  rcases List.mem_append.mp hcell with hleft | hright
  · exact hfirst cell hleft
  · exact hsecond cell hright

theorem allNone_replicate (n : Nat) :
    AllNone (List.replicate n (none : Option Bool)) := by
  intro cell hcell
  simp only [List.mem_replicate] at hcell
  exact hcell.2

theorem allNone_pushBlanks
    (bits left : List (Option Bool)) (hleft : AllNone left) :
    AllNone (pushBlanks bits left) := by
  rw [pushBlanks_eq_replicate_append]
  exact allNone_append (allNone_replicate bits.length) hleft

theorem erasedPrefixLeft_allNone (L : SimulatorLayout) :
    AllNone (erasedPrefixLeft L) := by
  unfold erasedPrefixLeft
  apply allNone_pushBlanks
  apply allNone_pushBlanks
  apply allNone_pushBlanks
  apply allNone_pushBlanks
  apply allNone_pushBlanks
  exact allNone_cons allNone_nil

theorem reconstructionBaseLeft_allNone (L : SimulatorLayout) :
    AllNone (reconstructionBaseLeft L) := by
  unfold reconstructionBaseLeft
  exact allNone_append (allNone_replicate _) (erasedPrefixLeft_allNone L)

theorem erasedRightTail_allNone
    (cells right : List (Option Bool)) (hright : AllNone right) :
    AllNone (erasedRightTail cells right) := by
  induction cells generalizing right with
  | nil =>
      exact allNone_cons (allNone_cons (allNone_cons hright))
  | cons cell rest ih =>
      exact ih _
        (allNone_cons (allNone_cons (allNone_cons (allNone_cons hright))))

theorem erasedRightLengthTail_allNone
    (n : Nat) (right : List (Option Bool)) (hright : AllNone right) :
    AllNone (erasedRightLengthTail n right) := by
  induction n generalizing right with
  | zero =>
      exact allNone_cons (allNone_cons (allNone_cons (allNone_cons hright)))
  | succ n ih =>
      exact ih _
        (allNone_cons (allNone_cons (allNone_cons (allNone_cons hright))))

theorem erasedLeftLengthTail_allNone
    (n : Nat) (right : List (Option Bool)) (hright : AllNone right) :
    AllNone (erasedLeftLengthTail n right) := by
  induction n generalizing right with
  | zero => exact allNone_cons (allNone_cons hright)
  | succ n ih =>
      exact ih _
        (allNone_cons (allNone_cons (allNone_cons (allNone_cons hright))))

theorem finalErasedRight_allNone (L : SimulatorLayout) :
    AllNone (finalErasedRight L) := by
  unfold finalErasedRight
  apply erasedLeftLengthTail_allNone
  apply erasedRightTail_allNone
  apply allNone_cons
  apply erasedRightLengthTail_allNone
  apply erasedRightTail_allNone
  exact
    allNone_cons
      (allNone_cons
        (allNone_cons
          (allNone_cons
            (allNone_cons allNone_nil))))

theorem dropTrailingNone_eq_nil_of_allNone
    (cells : List (Option Bool)) (h : AllNone cells) :
    Tape.dropTrailingNone cells = [] := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      have hcell : cell = none := h cell (List.mem_cons.mpr (Or.inl rfl))
      have hrest : AllNone rest := by
        intro other hother
        exact h other (List.mem_cons.mpr (Or.inr hother))
      subst cell
      simp [Tape.dropTrailingNone, ih hrest]

theorem eq_replicate_of_allNone
    (cells : List (Option Bool)) (h : AllNone cells) :
    cells = List.replicate cells.length none := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      have hcell : cell = none := h cell (List.mem_cons.mpr (Or.inl rfl))
      have hrest : AllNone rest := by
        intro other hother
        exact h other (List.mem_cons.mpr (Or.inr hother))
      subst cell
      simp only [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons (none : Option Bool)) (ih hrest)

theorem dropTrailingNone_append_of_allNone
    (cells padding : List (Option Bool)) (hpadding : AllNone padding) :
    Tape.dropTrailingNone (List.append cells padding) =
      Tape.dropTrailingNone cells := by
  rw [eq_replicate_of_allNone padding hpadding]
  exact dropTrailingNone_append_replicate_none cells padding.length

theorem actualConfigTape_equiv (L : SimulatorLayout) :
    Tape.Equiv (actualConfigTape L) L.config.tape := by
  unfold actualConfigTape
  rw [emittedCells_eq_reverse_append, List.reverse_reverse]
  change
    Tape.dropTrailingNone
          (List.append L.config.tape.left
            (none :: reconstructionBaseLeft L)) =
        Tape.dropTrailingNone L.config.tape.left ∧
      L.config.tape.head = L.config.tape.head ∧
      Tape.dropTrailingNone (List.append L.config.tape.right []) =
        Tape.dropTrailingNone L.config.tape.right
  refine ⟨?_, rfl, ?_⟩
  · exact dropTrailingNone_append_of_allNone _ _
      (allNone_cons (reconstructionBaseLeft_allNone L))
  · exact congrArg Tape.dropTrailingNone (List.append_nil _)

theorem actualMetadataTape_equiv
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.Equiv (actualMetadataTape D L)
      (ClassifiedBoundary.metadataHitTapeWithSelector D L) := by
  unfold actualMetadataTape
  unfold ClassifiedBoundary.metadataHitTapeWithSelector
  change
    Tape.dropTrailingNone
          (ClassifiedBoundary.classifiedMetadataLeft D L) =
        Tape.dropTrailingNone
          (ClassifiedBoundary.classifiedMetadataLeft D L) ∧
      some L.hit = some L.hit ∧
      Tape.dropTrailingNone (finalErasedRight L) =
        Tape.dropTrailingNone [none]
  refine ⟨rfl, rfl, ?_⟩
  rw [dropTrailingNone_eq_nil_of_allNone _ (finalErasedRight_allNone L)]
  rfl

def representedTapes
    (D : MachineDescription) (L : SimulatorLayout) : List (Tape Bool) :=
  [ actualConfigTape L
  , FieldDecomposition.stageCounterTape L.stage
  , actualMetadataTape D L ]

/-- Exact logical-tape representatives returned by the marked CfgHit table.
Unlike {name}`representedTapes`, this family is an internal physical-repair
boundary and is not logically equivalent to the canonical family: tape 0
still contains the temporary nonblank sentinel. -/
def markedRepresentedTapes
    (D : MachineDescription) (L : SimulatorLayout) : List (Tape Bool) :=
  [ markedActualConfigTape L
  , FieldDecomposition.stageCounterTape L.stage
  , actualMetadataTape D L ]

theorem representedTapes_equiv
    (D : MachineDescription) (L : SimulatorLayout) :
    LogicalTapeListEquiv (representedTapes D L)
      (ClassifiedBoundary.classifiedLoopTapes D L) := by
  unfold representedTapes ClassifiedBoundary.classifiedLoopTapes
  unfold LogicalTapeListEquiv
  exact ⟨actualConfigTape_equiv L,
    Tape.Equiv.refl _, actualMetadataTape_equiv D L, trivial⟩

theorem haltsWithTapes_layout
    (D : MachineDescription) (L : SimulatorLayout) :
    description.HaltsWithTapes
      (ThreeTape.config description.start
        (headerStartTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (ClassifiedBoundary.metadataHitTapeWithSelectorMarked D L))
      (markedRepresentedTapes D L) := by
  rcases (leads_layout D L).to_runConfig with ⟨steps, hrun⟩
  exact ⟨steps, hrun⟩

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady :=
  lowerStructured3Description_subroutineReady
    description_wellFormed description_supportsReadWriteRows3

theorem loweredDescription_haltsFromMarkedTapeEquiv
    (D : MachineDescription) (L : SimulatorLayout) :
    loweredDescription.HaltsFromTapeEquiv
      (targetTape D L)
      (encodedGuardedStructuredTapes (markedRepresentedTapes D L)) := by
  unfold loweredDescription targetTape
  apply lowerStructured3Description_haltsFromConfigWithTapes
    description_wellFormed description_haltTransitionFree
    description_supportsReadWriteRows3
    (c := ThreeTape.config description.start
      (headerStartTape L)
      (FieldDecomposition.stageCounterTape L.stage)
      (ClassifiedBoundary.metadataHitTapeWithSelectorMarked D L))
  · rfl
  · rfl
  · exact haltsWithTapes_layout D L
  done

end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore.FieldDecomposition.MetadataPrefix.ConfigTapeAndHit
