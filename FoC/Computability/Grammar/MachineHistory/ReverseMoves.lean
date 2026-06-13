import FoC.Computability.Grammar.MachineHistory.Locked

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open Grammars

namespace MachineDescriptionHistoryGrammar

theorem reverseRightMoveCell_active_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (c : MachineDescription.Configuration)
    (hstate : c.state < D.stateCount) (hc : ReachesHalt D c)
    (t : TransitionDescription) (ht : t ∈ D.transitions)
    (hmove : t.move = Direction.right) (d : Option Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : configForm D c =
      u ++ [cell t.write, state (D.stateOfNat t.target), cell d] ++ v)
    (hy : y =
      u ++ [state (D.stateOfNat t.source), cell t.read, cell d] ++ v) :
    HistorySoundForm D y := by
  subst y
  rcases c with ⟨qcur, T⟩
  rcases T with ⟨leftTape, headCur, rightTape⟩
  let cur : MachineDescription.Configuration :=
    { state := qcur,
      tape := { left := leftTape, head := headCur, right := rightTape } }
  have hxState :
      configForm D cur =
        (u ++ [cell t.write]) ++ [state (D.stateOfNat t.target)] ++
          (cell d :: v) := by
    simpa [cur, List.append_assoc] using hx
  rcases state_config_context cur (D.stateOfNat t.target) hxState with
    ⟨hprefix, hq, hsuffix⟩
  simp [cur] at hprefix hq hsuffix
  have hqnat : t.target = qcur := by
    have htTarget : t.target < D.stateCount :=
      (hD.right.right.right.left t ht).right
    exact stateOfNat_injective_of_state_bound
      (D := D) htTarget hstate hq
  subst qcur
  simp [cellForm] at hsuffix
  rcases hsuffix with ⟨hhead, hv⟩
  cases hhead
  subst v
  cases leftTape with
  | nil =>
      cases u <;> simp [cellForm, leftBoundary, cell, nt] at hprefix
  | cons l restLeft =>
      have hprefix' :
          u ++ [cell t.write] =
            ([leftBoundary] ++ cellForm (D := D) restLeft.reverse) ++
              [cell l] := by
        simpa [cellForm, List.map_append, List.append_assoc] using hprefix
      rcases append_singleton_eq_append_singleton hprefix' with ⟨hu, hcell⟩
      cases hcell
      subst u
      rcases lookupTransition_action_of_mem_matches
          (D := D) hD (source := t.source) (read := t.read) ht rfl rfl with
        ⟨actual, hlookup, hwrite, hmoveActual, htarget⟩
      let pred : MachineDescription.Configuration :=
        { state := t.source
          tape := { left := restLeft, head := t.read, right := d :: rightTape } }
      let current : MachineDescription.Configuration :=
        { state := t.target
          tape := { left := t.write :: restLeft, head := d, right := rightTape } }
      have hstep : D.stepConfig pred = some current := by
        simp [MachineDescription.stepConfig, pred, current, Tape.read, hlookup,
          Tape.write, Tape.move, Tape.moveRight, hwrite, hmoveActual, htarget,
          hmove]
      have hsourceState : pred.state < D.stateCount :=
        (hD.right.right.right.left t ht).left
      have hpredReach : ReachesHalt D pred := reachesHalt_step hstep hc
      simpa [configForm, pred, current, cellForm, List.map_reverse,
        List.reverse_cons, List.map_append, List.append_assoc] using
        (HistorySoundForm.active (D := D) pred hsourceState hpredReach)

theorem reverseRightMoveBoundary_active_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (c : MachineDescription.Configuration)
    (hstate : c.state < D.stateCount) (hc : ReachesHalt D c)
    (t : TransitionDescription) (ht : t ∈ D.transitions)
    (hmove : t.move = Direction.right)
    {u v y : SententialForm Bool (NT D)}
    (hx : configForm D c =
      u ++ [cell t.write, state (D.stateOfNat t.target), cell none,
        rightBoundary] ++ v)
    (hy : y =
      u ++ [state (D.stateOfNat t.source), cell t.read,
        rightBoundary] ++ v) :
    HistorySoundForm D y := by
  subst y
  rcases c with ⟨qcur, T⟩
  rcases T with ⟨leftTape, headCur, rightTape⟩
  let cur : MachineDescription.Configuration :=
    { state := qcur,
      tape := { left := leftTape, head := headCur, right := rightTape } }
  have hxState :
      configForm D cur =
        (u ++ [cell t.write]) ++ [state (D.stateOfNat t.target)] ++
          ([cell none, rightBoundary] ++ v) := by
    simpa [cur, List.append_assoc] using hx
  rcases state_config_context cur (D.stateOfNat t.target) hxState with
    ⟨hprefix, hq, hsuffix⟩
  simp [cur] at hprefix hq hsuffix
  have hqnat : t.target = qcur := by
    have htTarget : t.target < D.stateCount :=
      (hD.right.right.right.left t ht).right
    exact stateOfNat_injective_of_state_bound
      (D := D) htTarget hstate hq
  subst qcur
  simp [cellForm] at hsuffix
  rcases hsuffix with ⟨hhead, htail⟩
  cases hhead
  cases rightTape with
  | nil =>
      simp at htail
      subst v
      cases leftTape with
      | nil =>
          cases u <;> simp [cellForm, leftBoundary, cell, nt] at hprefix
      | cons l restLeft =>
          have hprefix' :
              u ++ [cell t.write] =
                ([leftBoundary] ++ cellForm (D := D) restLeft.reverse) ++
                  [cell l] := by
            simpa [cellForm, List.map_append, List.append_assoc] using hprefix
          rcases append_singleton_eq_append_singleton hprefix' with
            ⟨hu, hcell⟩
          cases hcell
          subst u
          rcases lookupTransition_action_of_mem_matches
              (D := D) hD (source := t.source) (read := t.read) ht
              rfl rfl with
            ⟨actual, hlookup, hwrite, hmoveActual, htarget⟩
          let pred : MachineDescription.Configuration :=
            { state := t.source
              tape := { left := restLeft, head := t.read, right := [] } }
          let current : MachineDescription.Configuration :=
            { state := t.target
              tape := { left := t.write :: restLeft, head := none, right := [] } }
          have hstep : D.stepConfig pred = some current := by
            simp [MachineDescription.stepConfig, pred, current, Tape.read,
              hlookup, Tape.write, Tape.move, Tape.moveRight, hwrite,
              hmoveActual, htarget, hmove]
          have hsourceState : pred.state < D.stateCount :=
            (hD.right.right.right.left t ht).left
          have hpredReach : ReachesHalt D pred := reachesHalt_step hstep hc
          simpa [configForm, pred, current, cellForm, List.map_reverse,
            List.reverse_cons, List.map_append, List.append_assoc] using
            (HistorySoundForm.active (D := D) pred hsourceState hpredReach)
  | cons r restRight =>
      cases r <;> simp [cell, rightBoundary, nt] at htail

theorem reverseLeftMoveCell_active_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (c : MachineDescription.Configuration)
    (hstate : c.state < D.stateCount) (hc : ReachesHalt D c)
    (t : TransitionDescription) (ht : t ∈ D.transitions)
    (hmove : t.move = Direction.left) (l : Option Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : configForm D c =
      u ++ [state (D.stateOfNat t.target), cell l, cell t.write] ++ v)
    (hy : y =
      u ++ [cell l, state (D.stateOfNat t.source), cell t.read] ++ v) :
    HistorySoundForm D y := by
  subst y
  rcases c with ⟨qcur, T⟩
  rcases T with ⟨leftTape, headCur, rightTape⟩
  let cur : MachineDescription.Configuration :=
    { state := qcur,
      tape := { left := leftTape, head := headCur, right := rightTape } }
  have hxState :
      configForm D cur =
        u ++ [state (D.stateOfNat t.target)] ++
          (cell l :: cell t.write :: v) := by
    simpa [cur, List.append_assoc] using hx
  rcases state_config_context cur (D.stateOfNat t.target) hxState with
    ⟨hu, hq, hsuffix⟩
  simp [cur] at hu hq hsuffix
  have hqnat : t.target = qcur := by
    have htTarget : t.target < D.stateCount :=
      (hD.right.right.right.left t ht).right
    exact stateOfNat_injective_of_state_bound
      (D := D) htTarget hstate hq
  subst qcur
  subst u
  simp [cellForm] at hsuffix
  rcases hsuffix with ⟨hhead, htail⟩
  cases hhead
  cases rightTape with
  | nil =>
      cases v <;> simp [cell, nt, rightBoundary] at htail
  | cons r restRight =>
      simp at htail
      rcases htail with ⟨hcell, hv⟩
      cases hcell
      subst v
      rcases lookupTransition_action_of_mem_matches
          (D := D) hD (source := t.source) (read := t.read) ht rfl rfl with
        ⟨actual, hlookup, hwrite, hmoveActual, htarget⟩
      let pred : MachineDescription.Configuration :=
        { state := t.source
          tape := { left := l :: leftTape, head := t.read, right := restRight } }
      let current : MachineDescription.Configuration :=
        { state := t.target
          tape := { left := leftTape, head := l, right := t.write :: restRight } }
      have hstep : D.stepConfig pred = some current := by
        simp [MachineDescription.stepConfig, pred, current, Tape.read, hlookup,
          Tape.write, Tape.move, Tape.moveLeft, hwrite, hmoveActual, htarget,
          hmove]
      have hsourceState : pred.state < D.stateCount :=
        (hD.right.right.right.left t ht).left
      have hpredReach : ReachesHalt D pred := reachesHalt_step hstep hc
      simpa [configForm, pred, current, cellForm, List.map_reverse,
        List.reverse_cons, List.map_append, List.append_assoc] using
        (HistorySoundForm.active (D := D) pred hsourceState hpredReach)

theorem reverseLeftMoveBoundary_active_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (c : MachineDescription.Configuration)
    (hstate : c.state < D.stateCount) (hc : ReachesHalt D c)
    (t : TransitionDescription) (ht : t ∈ D.transitions)
    (hmove : t.move = Direction.left)
    {u v y : SententialForm Bool (NT D)}
    (hx : configForm D c =
      u ++ [leftBoundary, state (D.stateOfNat t.target), cell none,
        cell t.write] ++ v)
    (hy : y =
      u ++ [leftBoundary, state (D.stateOfNat t.source),
        cell t.read] ++ v) :
    HistorySoundForm D y := by
  subst y
  rcases c with ⟨qcur, T⟩
  rcases T with ⟨leftTape, headCur, rightTape⟩
  let cur : MachineDescription.Configuration :=
    { state := qcur,
      tape := { left := leftTape, head := headCur, right := rightTape } }
  have hxLB :
      configForm D cur =
        u ++ [leftBoundary] ++
          ([state (D.stateOfNat t.target), cell none, cell t.write] ++ v) := by
    simpa [cur, List.append_assoc] using hx
  rcases leftBoundary_config_context cur hxLB with ⟨hu, htail⟩
  simp [cur] at hu htail
  subst u
  have hxState :
      cellForm (D := D) leftTape.reverse ++
          [state (D.stateOfNat qcur), cell headCur] ++
          cellForm rightTape ++ [rightBoundary] =
        [] ++ [state (D.stateOfNat t.target)] ++
          (cell none :: cell t.write :: v) := by
    simpa [List.append_assoc] using htail.symm
  rcases state_cellForm_context leftTape.reverse (D.stateOfNat qcur)
      headCur rightTape (D.stateOfNat t.target) hxState with
    ⟨hleft, hq, hsuffix⟩
  have hqnat : t.target = qcur := by
    have htTarget : t.target < D.stateCount :=
      (hD.right.right.right.left t ht).right
    exact stateOfNat_injective_of_state_bound
      (D := D) htTarget hstate hq
  subst qcur
  cases leftTape with
  | nil =>
      simp [cellForm] at hsuffix
      rcases hsuffix with ⟨hhead, htail2⟩
      cases hhead
      cases rightTape with
      | nil =>
          cases v <;> simp [cell, nt, rightBoundary] at htail2
      | cons r restRight =>
          simp at htail2
          rcases htail2 with ⟨hcell, hv⟩
          cases hcell
          subst v
          rcases lookupTransition_action_of_mem_matches
              (D := D) hD (source := t.source) (read := t.read) ht
              rfl rfl with
            ⟨actual, hlookup, hwrite, hmoveActual, htarget⟩
          let pred : MachineDescription.Configuration :=
            { state := t.source
              tape := { left := [], head := t.read, right := restRight } }
          let current : MachineDescription.Configuration :=
            { state := t.target
              tape := { left := [], head := none, right := t.write :: restRight } }
          have hstep : D.stepConfig pred = some current := by
            simp [MachineDescription.stepConfig, pred, current, Tape.read,
              hlookup, Tape.write, Tape.move, Tape.moveLeft, hwrite,
              hmoveActual, htarget, hmove]
          have hsourceState : pred.state < D.stateCount :=
            (hD.right.right.right.left t ht).left
          have hpredReach : ReachesHalt D pred := reachesHalt_step hstep hc
          simpa [configForm, pred, current, cellForm, List.map_reverse,
            List.reverse_cons, List.map_append, List.append_assoc] using
            (HistorySoundForm.active (D := D) pred hsourceState hpredReach)
  | cons l restLeft =>
      simp [cellForm, List.map_append] at hleft


end MachineDescriptionHistoryGrammar

end Computability
end FoC
