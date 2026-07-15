import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpointCore

/-! Static well-formedness and lowering facts for direct joined closeout. -/

set_option maxRecDepth 10000

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf
namespace DirectJoinedCloseout

open Structured.MultiTapeLowering.ThreeTape

private def transitionChunks : List (List Structured.Transition) :=
  [ allReadRows3 0 1 keepL keepS keepS
  , rowsForTape0Read 1 (some false) keepL keepS keepS 1
  , rowsForTape0Read 1 (some true) keepL keepS keepS 1
  , rowsForTape0Read 1 none keepR keepR keepS 3
  , rowsForTape0Read 20 (some false) keepL keepS keepS 20
  , rowsForTape0Read 20 (some true) keepL keepS keepS 20
  , rowsForTape0Read 20 none keepR keepS keepS 21
  , rowsForTape0Read 3 (some false) keepR (writeBitR true) keepS 4
  , rowsForTape0Read 3 (some true) keepR (writeBitR true) keepS 4
  , rowsForTape0Read 3 none keepS keepS keepS 11
  , allReadRows3 4 5 keepS (writeBitR true) keepS
  , allReadRows3 5 6 keepS (writeBitR true) keepS
  , allReadRows3 6 7 keepS (writeBitR true) keepS
  , allReadRows3 7 8 keepS (writeBitR true) keepS
  , allReadRows3 8 9 keepS (writeBitR true) keepS
  , allReadRows3 9 10 keepS (writeBitR true) keepS
  , allReadRows3 10 3 keepS (writeBitR true) keepS
  , allReadRows3 21 22 keepR keepS keepS
  , allReadRows3 22 23 keepR keepS keepS
  , allReadRows3 23 24 keepR keepS keepS
  , allReadRows3 24 25 keepR keepS keepS
  , allReadRows3 25 26 keepR keepS keepS
  , allReadRows3 26 27 keepR keepS keepS
  , allReadRows3 11 12 keepS (writeBitR true) keepS
  , allReadRows3 12 13 keepS (writeBitR true) keepS
  , allReadRows3 13 14 keepS (writeBitR true) keepS
  , allReadRows3 14 15 keepS (writeBitR true) keepS
  , allReadRows3 15 16 keepS (writeBitR true) keepS
  , allReadRows3 16 17 keepS (writeBitR true) keepS
  , allReadRows3 17 18 keepS (writeBitR true) keepS
  , allReadRows3 18 19 keepS (writeBitR true) keepS
  , allReadRows3 19 20 keepL keepR keepS
  , rowsForTape0Read 27 (some true) keepR keepS keepS 28
  , rowsForTape0Read 28 (some true) keepR keepL keepS 40
  , rowsForTape0Read 28 (some false) keepR keepS keepS 29
  , rowsForTape0Read 29 (some false) keepR keepS keepS 30
  , rowsForTape0Read 30 (some false) keepR keepS keepS 31
  , rowsForTape0Read 31 (some true) keepR keepS keepS 32
  , rowsForTape0Read 32 (some false) keepR (writeBitR false) keepS 29
  , rowsForTape0Read 32 (some true) keepR (writeBitR false) keepS 33
  , allReadRows3 33 34 keepS keepL keepS
  , rowsForTape1Read 34 (some false) keepR eraseL keepS 35
  , rowsForTape1Read 34 none keepS keepS keepS 40
  , allReadRows3 35 36 keepR keepS keepS
  , allReadRows3 36 37 keepR keepS keepS
  , allReadRows3 37 34 keepR keepS keepS
  , rowsForTape0Read 40 (some false)
      keepR (writeBitR true) (writeBitR false) 40
  , rowsForTape0Read 40 (some true)
      keepR (writeBitR true) (writeBitR true) 40
  , rowsForTape0Read 40 none keepS keepL keepL 41
  , rowsForTape1Read 41 (some true) keepS eraseL keepS 42
  , rowsForTape1Read 42 (some true) keepS eraseL keepL 42
  , rowsForTape1Read 42 none keepS keepS keepS 43 ]

private theorem transitionChunks_flatten :
    transitionChunks.flatten = rows := by
  rfl

private def groupA : List Structured.Transition :=
  (transitionChunks.take 17).flatten

private def groupB : List Structured.Transition :=
  ((transitionChunks.drop 17).take 6).flatten

private def groupC : List Structured.Transition :=
  ((transitionChunks.drop 23).take 9).flatten

private def groupD : List Structured.Transition :=
  ((transitionChunks.drop 32).take 9).flatten

private def groupE : List Structured.Transition :=
  ((transitionChunks.drop 41).take 5).flatten

private def groupF : List Structured.Transition :=
  (transitionChunks.drop 46).flatten

private theorem groups_append :
    groupA ++ groupB ++ groupC ++ groupD ++ groupE ++ groupF = rows := by
  rfl

set_option maxHeartbeats 1000000 in
private theorem groupA_deterministicBool :
    structuredTransitionTableDeterministicBool groupA = true := by
  decide

set_option maxHeartbeats 1000000 in
private theorem remainingGroups_deterministicBool :
    structuredTransitionTableDeterministicBool groupB = true ∧
    structuredTransitionTableDeterministicBool groupC = true ∧
    structuredTransitionTableDeterministicBool groupD = true ∧
    structuredTransitionTableDeterministicBool groupE = true ∧
    structuredTransitionTableDeterministicBool groupF = true := by
  decide

private def sourcesA : List Nat := [0, 1, 20, 3, 4, 5, 6, 7, 8, 9, 10]
private def sourcesB : List Nat := [21, 22, 23, 24, 25, 26]
private def sourcesC : List Nat := [11, 12, 13, 14, 15, 16, 17, 18, 19]
private def sourcesD : List Nat := [27, 28, 29, 30, 31, 32, 33]
private def sourcesE : List Nat := [34, 35, 36, 37]
private def sourcesF : List Nat := [40, 41, 42]

private theorem groupSourcesBool :
    groupA.all (fun t => decide (t.source ∈ sourcesA)) = true ∧
    groupB.all (fun t => decide (t.source ∈ sourcesB)) = true ∧
    groupC.all (fun t => decide (t.source ∈ sourcesC)) = true ∧
    groupD.all (fun t => decide (t.source ∈ sourcesD)) = true ∧
    groupE.all (fun t => decide (t.source ∈ sourcesE)) = true ∧
    groupF.all (fun t => decide (t.source ∈ sourcesF)) = true := by
  decide

private def natSourcesDisjointBool (left right : List Nat) : Bool :=
  left.all fun source => right.all fun target => decide (source ≠ target)

private theorem progressiveSourcesDisjointBool :
    natSourcesDisjointBool sourcesA sourcesB = true ∧
    natSourcesDisjointBool (sourcesA ++ sourcesB) sourcesC = true ∧
    natSourcesDisjointBool (sourcesA ++ sourcesB ++ sourcesC) sourcesD = true ∧
    natSourcesDisjointBool
        (sourcesA ++ sourcesB ++ sourcesC ++ sourcesD) sourcesE = true ∧
    natSourcesDisjointBool
        (sourcesA ++ sourcesB ++ sourcesC ++ sourcesD ++ sourcesE)
        sourcesF = true := by
  decide

private theorem progressiveGroupSourcesBool :
    (groupA ++ groupB).all
        (fun t => decide (t.source ∈ sourcesA ++ sourcesB)) = true ∧
    (groupA ++ groupB ++ groupC).all
        (fun t => decide (t.source ∈ sourcesA ++ sourcesB ++ sourcesC)) =
      true ∧
    (groupA ++ groupB ++ groupC ++ groupD).all
        (fun t =>
          decide (t.source ∈ sourcesA ++ sourcesB ++ sourcesC ++ sourcesD)) =
      true ∧
    (groupA ++ groupB ++ groupC ++ groupD ++ groupE).all
        (fun t =>
          decide
            (t.source ∈
              sourcesA ++ sourcesB ++ sourcesC ++ sourcesD ++ sourcesE)) =
      true := by
  decide

private theorem source_mem_of_all
    {transitions : List Structured.Transition} {sources : List Nat}
    (h : transitions.all (fun t => decide (t.source ∈ sources)) = true)
    {t : Structured.Transition} (ht : t ∈ transitions) :
    t.source ∈ sources := by
  have hrow := List.all_eq_true.mp h t ht
  exact of_decide_eq_true hrow

private theorem source_ne_of_disjoint
    {left right : List Nat}
    (h : natSourcesDisjointBool left right = true)
    {source target : Nat} (hsource : source ∈ left) (htarget : target ∈ right) :
    source ≠ target := by
  unfold natSourcesDisjointBool at h
  have hleft := List.all_eq_true.mp h source hsource
  have hright := List.all_eq_true.mp hleft target htarget
  exact of_decide_eq_true hright

private theorem deterministic_append_of_source_disjoint
    {left right : List Structured.Transition}
    {leftSources rightSources : List Nat}
    (hleft : ∀ t u, t ∈ left -> u ∈ left ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u)
    (hright : ∀ t u, t ∈ right -> u ∈ right ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u)
    (hleftSources :
      left.all (fun t => decide (t.source ∈ leftSources)) = true)
    (hrightSources :
      right.all (fun t => decide (t.source ∈ rightSources)) = true)
    (hdisjoint : natSourcesDisjointBool leftSources rightSources = true) :
    ∀ t u, t ∈ left ++ right -> u ∈ left ++ right ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u := by
  intro t u ht hu hkey
  rw [List.mem_append] at ht hu
  rcases ht with ht | ht
  all_goals rcases hu with hu | hu
  case inl.inl => exact hleft t u ht hu hkey
  case inr.inr => exact hright t u ht hu hkey
  case inr.inl =>
    have huSource := source_mem_of_all hleftSources hu
    have htSource := source_mem_of_all hrightSources ht
    have hne := source_ne_of_disjoint hdisjoint huSource htSource
    exact (hne hkey.left.symm).elim
  case inl.inr =>
    have htSource := source_mem_of_all hleftSources ht
    have huSource := source_mem_of_all hrightSources hu
    have hne := source_ne_of_disjoint hdisjoint htSource huSource
    exact (hne hkey.left).elim

private def groupB_deterministicBool :=
  remainingGroups_deterministicBool.left
private def groupC_deterministicBool :=
  remainingGroups_deterministicBool.right.left
private def groupD_deterministicBool :=
  remainingGroups_deterministicBool.right.right.left
private def groupE_deterministicBool :=
  remainingGroups_deterministicBool.right.right.right.left
private def groupF_deterministicBool :=
  remainingGroups_deterministicBool.right.right.right.right

private def groupA_sourcesBool := groupSourcesBool.left
private def groupB_sourcesBool := groupSourcesBool.right.left
private def groupC_sourcesBool := groupSourcesBool.right.right.left
private def groupD_sourcesBool := groupSourcesBool.right.right.right.left
private def groupE_sourcesBool :=
  groupSourcesBool.right.right.right.right.left
private def groupF_sourcesBool :=
  groupSourcesBool.right.right.right.right.right

private def sourcesAB_disjointBool := progressiveSourcesDisjointBool.left
private def sourcesABC_disjointBool :=
  progressiveSourcesDisjointBool.right.left
private def sourcesABCD_disjointBool :=
  progressiveSourcesDisjointBool.right.right.left
private def sourcesABCDE_disjointBool :=
  progressiveSourcesDisjointBool.right.right.right.left
private def sourcesABCDEF_disjointBool :=
  progressiveSourcesDisjointBool.right.right.right.right

private def groupsAB_sourcesBool := progressiveGroupSourcesBool.left
private def groupsABC_sourcesBool := progressiveGroupSourcesBool.right.left
private def groupsABCD_sourcesBool :=
  progressiveGroupSourcesBool.right.right.left
private def groupsABCDE_sourcesBool :=
  progressiveGroupSourcesBool.right.right.right

private theorem groupsAB_deterministic :
    ∀ t u, t ∈ groupA ++ groupB -> u ∈ groupA ++ groupB ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u := by
  exact deterministic_append_of_source_disjoint
    (structuredTransition_deterministic_of_all groupA_deterministicBool)
    (structuredTransition_deterministic_of_all groupB_deterministicBool)
    groupA_sourcesBool groupB_sourcesBool sourcesAB_disjointBool

private theorem groupsABC_deterministic :
    ∀ t u, t ∈ groupA ++ groupB ++ groupC ->
      u ∈ groupA ++ groupB ++ groupC ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u := by
  exact deterministic_append_of_source_disjoint
    groupsAB_deterministic
    (structuredTransition_deterministic_of_all groupC_deterministicBool)
    groupsAB_sourcesBool groupC_sourcesBool sourcesABC_disjointBool

private theorem groupsABCD_deterministic :
    ∀ t u, t ∈ groupA ++ groupB ++ groupC ++ groupD ->
      u ∈ groupA ++ groupB ++ groupC ++ groupD ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u := by
  exact deterministic_append_of_source_disjoint
    groupsABC_deterministic
    (structuredTransition_deterministic_of_all groupD_deterministicBool)
    groupsABC_sourcesBool groupD_sourcesBool sourcesABCD_disjointBool

private theorem groupsABCDE_deterministic :
    ∀ t u, t ∈ groupA ++ groupB ++ groupC ++ groupD ++ groupE ->
      u ∈ groupA ++ groupB ++ groupC ++ groupD ++ groupE ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u := by
  exact deterministic_append_of_source_disjoint
    groupsABCD_deterministic
    (structuredTransition_deterministic_of_all groupE_deterministicBool)
    groupsABCD_sourcesBool groupE_sourcesBool sourcesABCDE_disjointBool

private theorem groupsABCDEF_deterministic :
    ∀ t u, t ∈ groupA ++ groupB ++ groupC ++ groupD ++ groupE ++ groupF ->
      u ∈ groupA ++ groupB ++ groupC ++ groupD ++ groupE ++ groupF ->
      Structured.Transition.SameKey t u ->
        Structured.Transition.SameAction t u := by
  exact deterministic_append_of_source_disjoint
    groupsABCDE_deterministic
    (structuredTransition_deterministic_of_all groupF_deterministicBool)
    groupsABCDE_sourcesBool groupF_sourcesBool sourcesABCDEF_disjointBool

private theorem description_deterministic : description.Deterministic := by
  unfold Structured.Description.Deterministic
  intro t u ht hu hkey
  have ht' : t ∈ rows := by
    simpa [description, Structured.MultiTapeLowering.ThreeTape.description] using ht
  have hu' : u ∈ rows := by
    simpa [description, Structured.MultiTapeLowering.ThreeTape.description] using hu
  rw [← groups_append] at ht' hu'
  exact groupsABCDEF_deterministic t u ht' hu' hkey

private theorem description_rowsWellFormedBool :
    structuredDescriptionRowsWellFormedBool description = true := by
  decide

theorem description_wellFormed : description.WellFormed := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, description_deterministic⟩
  exact structuredTransition_wellFormed_of_all
    (by simpa [structuredDescriptionRowsWellFormedBool] using
      description_rowsWellFormedBool)

theorem description_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3 description := by
  exact Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    (by decide)

theorem description_haltTransitionFree : description.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_transition_checks description
    (by decide)

theorem description_subroutineReady : description.SubroutineReady :=
  ⟨description_wellFormed, description_haltTransitionFree⟩

def loweredDescription : MachineDescription :=
  Structured.MultiTapeLowering.lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady :=
  Structured.MultiTapeLowering.lowerStructured3Description_subroutineReady
    description_wellFormed description_supported

end DirectJoinedCloseout
end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
