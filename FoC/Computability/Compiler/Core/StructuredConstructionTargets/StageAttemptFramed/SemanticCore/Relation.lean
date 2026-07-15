import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Cleanup

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

def CellCovered (work marker : Option Bool) : Prop :=
  marker = some false ∨ (work = none ∧ marker = none)

inductive ExactCovers :
    List (Option Bool) → List (Option Bool) → Prop where
  | nil : ExactCovers [] []
  | cons {work marker : Option Bool} {works markers : List (Option Bool)} :
      CellCovered work marker → ExactCovers works markers →
        ExactCovers (work :: works) (marker :: markers)

def AllNone (cells : List (Option Bool)) : Prop :=
  ∀ cell : Option Bool, cell ∈ cells → cell = none

inductive RightCovers :
    List (Option Bool) → List (Option Bool) → Prop where
  | extra (works : List (Option Bool)) :
      AllNone works → RightCovers works []
  | cons {work marker : Option Bool} {works markers : List (Option Bool)} :
      CellCovered work marker → RightCovers works markers →
        RightCovers (work :: works) (marker :: markers)

inductive MarkerSide : List (Option Bool) → Prop where
  | nil : MarkerSide []
  | boundary : MarkerSide [none]
  | marked {rest : List (Option Bool)} :
      MarkerSide rest → MarkerSide (some false :: rest)

structure CoveredTapes (work marker : Tape Bool) : Prop where
  left : ExactCovers work.left marker.left
  head : CellCovered work.head marker.head
  right : RightCovers work.right marker.right
  markerLeft : MarkerSide marker.left
  markerHead : marker.head = none ∨ marker.head = some false
  markerRight : MarkerSide marker.right

theorem cellCovered_false (work : Option Bool) :
    CellCovered work (some false) := Or.inl rfl

theorem cellCovered_none : CellCovered none none :=
  Or.inr ⟨rfl, rfl⟩

theorem allNone_nil : AllNone [] := by simp [AllNone]

theorem allNone_replicate (n : Nat) :
    AllNone (List.replicate n (none : Option Bool)) := by
  intro cell hcell
  exact (List.mem_replicate.mp hcell).2

theorem allNone_tail {cell : Option Bool} {rest : List (Option Bool)}
    (h : AllNone (cell :: rest)) : AllNone rest := by
  intro x hx
  exact h x (by simp [hx])

theorem markerSide_tail {cell : Option Bool} {rest : List (Option Bool)}
    (h : MarkerSide (cell :: rest)) : MarkerSide rest := by
  cases h with
  | boundary => exact MarkerSide.nil
  | marked hrest => exact hrest

theorem markerSide_head {cell : Option Bool} {rest : List (Option Bool)}
    (h : MarkerSide (cell :: rest)) :
    cell = none ∨ cell = some false := by
  cases h with
  | boundary => exact Or.inl rfl
  | marked _ => exact Or.inr rfl

theorem markerSide_replicate_boundary (n : Nat) :
    MarkerSide
      (List.append (List.replicate n (some false : Option Bool)) [none]) := by
  induction n with
  | zero => exact MarkerSide.boundary
  | succ n ih =>
      change MarkerSide
        (some false :: List.append (List.replicate n (some false)) [none])
      exact MarkerSide.marked ih

theorem rightCovers_cells_padding (bits : Word Bool) (padding : Nat) :
    RightCovers
      (List.append (cells bits)
        (List.replicate (padding + 1) none))
      (List.append (List.replicate bits.length (some false)) [none]) := by
  induction bits with
  | nil =>
      change RightCovers
        (none :: List.replicate padding none) [none]
      exact RightCovers.cons cellCovered_none
        (RightCovers.extra _ (allNone_replicate padding))
  | cons bit rest ih =>
      change RightCovers
        (some bit :: List.append (cells rest)
          (List.replicate (padding + 1) none))
        (some false :: List.append
          (List.replicate rest.length (some false)) [none])
      exact RightCovers.cons (cellCovered_false _) ih

theorem covered_reconstructed_marker
    (bits sourceResult : Word Bool) (hbits : bits ≠ []) :
    CoveredTapes
      (reconstructedTape bits sourceResult) (markerTape bits) := by
  cases bits with
  | nil => exact False.elim (hbits rfl)
  | cons bit rest =>
      change Word Bool at rest
      refine {
        left := ExactCovers.cons cellCovered_none ExactCovers.nil
        head := cellCovered_false _
        right := ?_
        markerLeft := MarkerSide.boundary
        markerHead := Or.inr rfl
        markerRight := ?_
      }
      · change RightCovers
          (List.append (cells rest)
            (List.replicate (sourceResult.length + 5) none))
          (List.append (List.replicate rest.length (some false)) [none])
        simpa only [show sourceResult.length + 5 =
            (sourceResult.length + 4) + 1 by lia] using
          (rightCovers_cells_padding rest (sourceResult.length + 4))
      · exact markerSide_replicate_boundary rest.length

theorem covered_write_move_left
    (work marker : Tape Bool) (write : Option Bool)
    (h : CoveredTapes work marker) :
    CoveredTapes
      (Tape.move Direction.left (Tape.write write work))
      (Tape.move Direction.left (Tape.write (some false) marker)) := by
  rcases work with ⟨workLeft, workHead, workRight⟩
  rcases marker with ⟨markerLeft, markerHead, markerRight⟩
  rcases h with ⟨hleft, hhead, hright, hmleft, hmhead, hmright⟩
  cases hleft with
  | nil =>
      refine {
        left := ExactCovers.nil
        head := cellCovered_none
        right := RightCovers.cons (cellCovered_false _) hright
        markerLeft := MarkerSide.nil
        markerHead := Or.inl rfl
        markerRight := MarkerSide.marked hmright
      }
  | @cons workCell markerCell workTail markerTail hcell htail =>
      refine {
        left := htail
        head := hcell
        right := RightCovers.cons (cellCovered_false _) hright
        markerLeft := markerSide_tail hmleft
        markerHead := markerSide_head hmleft
        markerRight := MarkerSide.marked hmright
      }

theorem covered_write_move_right
    (work marker : Tape Bool) (write : Option Bool)
    (h : CoveredTapes work marker) :
    CoveredTapes
      (Tape.move Direction.right (Tape.write write work))
      (Tape.move Direction.right (Tape.write (some false) marker)) := by
  rcases work with ⟨workLeft, workHead, workRight⟩
  rcases marker with ⟨markerLeft, markerHead, markerRight⟩
  rcases h with ⟨hleft, hhead, hright, hmleft, hmhead, hmright⟩
  cases hright with
  | extra _ hall =>
      cases workRight with
      | nil =>
          refine {
            left := ExactCovers.cons (cellCovered_false _) hleft
            head := cellCovered_none
            right := RightCovers.extra [] allNone_nil
            markerLeft := MarkerSide.marked hmleft
            markerHead := Or.inl rfl
            markerRight := MarkerSide.nil
          }
      | cons cell rest =>
          have hcell : cell = none := hall cell (by simp)
          subst cell
          refine {
            left := ExactCovers.cons (cellCovered_false _) hleft
            head := cellCovered_none
            right := RightCovers.extra rest (allNone_tail hall)
            markerLeft := MarkerSide.marked hmleft
            markerHead := Or.inl rfl
            markerRight := MarkerSide.nil
          }
  | @cons workCell markerCell workTail markerTail hcell htail =>
      refine {
        left := ExactCovers.cons (cellCovered_false _) hleft
        head := hcell
        right := htail
        markerLeft := MarkerSide.marked hmleft
        markerHead := markerSide_head hmright
        markerRight := markerSide_tail hmright
      }

theorem leads_attempt_first_halt_covered
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    {n : Nat} {c : MachineDescription.Configuration}
    {Tout T1 T2 : Tape Bool}
    (hc : c.state < attempt.stateCount)
    (hrun : attempt.runConfig n c =
      { state := attempt.halt, tape := Tout })
    (hfirst : ∀ k : Nat, k < n →
      (attempt.runConfig k c).state ≠ attempt.halt)
    (hcovered : CoveredTapes c.tape T1) :
    ∃ T1' : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt (.run c.state) c.tape T1 T2)
        (cfg attempt hattempt (.run attempt.halt) Tout T1' T2) ∧
      CoveredTapes Tout T1' := by
  induction n generalizing c T1 with
  | zero =>
      simp [MachineDescription.runConfig] at hrun
      subst c
      exact ⟨T1, Leads.refl attempt hattempt _, hcovered⟩
  | succ n ih =>
      have hne : c.state ≠ attempt.halt := by
        simpa [MachineDescription.runConfig] using
          hfirst 0 (Nat.zero_lt_succ n)
      cases hstep : attempt.stepConfig c with
      | none =>
          have hcHalt : c.state = attempt.halt := by
            have hstates := congrArg MachineDescription.Configuration.state hrun
            simpa [MachineDescription.runConfig, hstep] using hstates
          exact (hne hcHalt).elim
      | some nextCfg =>
          cases hlookup : attempt.lookupTransition c.state
              (Tape.read c.tape) with
          | none =>
              simp [MachineDescription.stepConfig, hlookup] at hstep
          | some t =>
              simp [MachineDescription.stepConfig, hlookup] at hstep
              subst nextCfg
              have hs : StateBounded attempt (.run c.state) := by
                simpa [StateBounded] using hc
              have hnext :
                  next attempt (.run c.state) (Tape.read c.tape)
                      (Tape.read T1) (Tape.read T2) =
                    some
                      { target := .run t.target
                        action0 := workAction t
                        action1 := markerAction t.move
                        action2 := keepS } := by
                simp [next, hne, hlookup, someStep]
              have hlead := leads_step (attempt := attempt) (hattempt := hattempt)
                (T0 := c.tape) (T1 := T1) (T2 := T2) hs hnext
              have hstep' :
                  attempt.stepConfig c =
                    some
                      { state := t.target
                        tape := Tape.move t.move
                          (Tape.write t.write c.tape) } := by
                simp [MachineDescription.stepConfig, hlookup]
              have hcnext : t.target < attempt.stateCount :=
                MachineDescription.stepConfig_state_bound
                  hattempt.left hstep'
              have hrunnext :
                  attempt.runConfig n
                      { state := t.target
                        tape := Tape.move t.move
                          (Tape.write t.write c.tape) } =
                    { state := attempt.halt, tape := Tout } := by
                simpa [MachineDescription.runConfig, hstep'] using hrun
              have hfirstnext : ∀ k : Nat, k < n →
                  (attempt.runConfig k
                    { state := t.target
                      tape := Tape.move t.move
                        (Tape.write t.write c.tape) }).state ≠
                    attempt.halt := by
                intro k hk
                simpa [MachineDescription.runConfig, hstep'] using
                  hfirst (k + 1) (Nat.succ_lt_succ hk)
              have hcoveredNext :
                  CoveredTapes
                    (Tape.move t.move (Tape.write t.write c.tape))
                    ((markerAction t.move).apply T1) := by
                cases t with
                | mk source read write move target =>
                    cases move with
                    | left =>
                        simpa [workAction, markerAction, headMoveOfDirection,
                          TapeAction.apply, HeadMove.apply] using
                          (covered_write_move_left c.tape T1 write hcovered)
                    | right =>
                        simpa [workAction, markerAction, headMoveOfDirection,
                          TapeAction.apply, HeadMove.apply] using
                          (covered_write_move_right c.tape T1 write hcovered)
              rcases ih
                  (c :=
                    { state := t.target
                      tape := Tape.move t.move
                        (Tape.write t.write c.tape) })
                  (T1 := (markerAction t.move).apply T1)
                  hcnext hrunnext hfirstnext hcoveredNext with
                ⟨T1', htail, hcoveredFinal⟩
              have hwork :
                  (workAction t).apply c.tape =
                    Tape.move t.move (Tape.write t.write c.tape) := by
                cases t with
                | mk source read write move target =>
                    cases move <;> rfl
              rw [hwork] at hlead
              exact ⟨T1', hlead.trans htail, hcoveredFinal⟩

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
