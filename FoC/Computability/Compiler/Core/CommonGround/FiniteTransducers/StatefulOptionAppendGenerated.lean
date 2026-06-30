import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StatefulOptionAppend

set_option doc.verso true

/-!
# Generated arbitrary-state optional-output tables

This module builds the range-generated transition table for the stateful
optional-output append compiler.  It proves the generic table-level readiness
facts; lookup/run facts over the generated range table are layered on top of
these structural facts.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

namespace FiniteTransducer

def statefulOptionAppendWriterStart (scanStateCount : Nat) : Nat :=
  scanStateCount

def statefulOptionAppendHalt
    (scanStateCount : Nat) (final : Word Bool) : Nat :=
  statefulOptionAppendWriterStart scanStateCount + final.length

def statefulOptionAppendStateTransitions
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (state : Nat) :
    List TransitionDescription :=
  [ { source := state
      read := none
      write := none
      move := Direction.right
      target := statefulOptionAppendWriterStart scanStateCount }
  , { source := state
      read := some false
      write := emit state false
      move := Direction.right
      target := next state false }
  , { source := state
      read := some true
      write := emit state true
      move := Direction.right
      target := next state true } ]

def statefulOptionAppendPrefixTransitions
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool) :
    List TransitionDescription :=
  (List.range scanStateCount).map
    (statefulOptionAppendStateTransitions scanStateCount next emit)
    |>.flatten

def statefulOptionAppendTransitions
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool) :
    List TransitionDescription :=
  List.append
    (statefulOptionAppendPrefixTransitions scanStateCount next emit)
    (copyAppendWordWriteTransitionsFrom
      (statefulOptionAppendWriterStart scanStateCount)
      (statefulOptionAppendHalt scanStateCount final) final)

theorem statefulOptionAppendStateTransitions_source_eq
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (state : Nat) :
    forall t : TransitionDescription,
      t ∈ statefulOptionAppendStateTransitions
          scanStateCount next emit state ->
        t.source = state := by
  intro t ht
  simp [statefulOptionAppendStateTransitions] at ht
  rcases ht with ht | ht | ht <;> subst t <;> rfl

theorem statefulOptionAppendStateTransitions_wellFormed
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    forall state t,
      state < scanStateCount ->
      t ∈ statefulOptionAppendStateTransitions
          scanStateCount next emit state ->
        TransitionDescription.WellFormed
          (statefulOptionAppendHalt scanStateCount final + 1) t := by
  intro state t hstate ht
  simp [statefulOptionAppendStateTransitions] at ht
  rcases ht with ht | ht | ht
  · subst t
    constructor <;>
      simp [statefulOptionAppendHalt,
        statefulOptionAppendWriterStart] <;> omega
  · subst t
    constructor
    · simp [statefulOptionAppendHalt,
        statefulOptionAppendWriterStart]
      omega
    · have hlt := hnext state false hstate
      simp [statefulOptionAppendHalt,
        statefulOptionAppendWriterStart]
      omega
  · subst t
    constructor
    · simp [statefulOptionAppendHalt,
        statefulOptionAppendWriterStart]
      omega
    · have hlt := hnext state true hstate
      simp [statefulOptionAppendHalt,
        statefulOptionAppendWriterStart]
      omega

theorem statefulOptionAppendPrefix_source_lt_writerStart
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool) :
    forall t : TransitionDescription,
      t ∈ statefulOptionAppendPrefixTransitions
          scanStateCount next emit ->
        t.source < statefulOptionAppendWriterStart scanStateCount := by
  intro t ht
  rw [statefulOptionAppendPrefixTransitions, List.mem_flatten] at ht
  rcases ht with ⟨rows, hrows, ht⟩
  rw [List.mem_map] at hrows
  rcases hrows with ⟨state, hstateRange, hrows⟩
  subst rows
  have hsource :=
    statefulOptionAppendStateTransitions_source_eq
      scanStateCount next emit state t ht
  have hstate : state < scanStateCount := by
    simpa using List.mem_range.mp hstateRange
  rw [hsource]
  simpa [statefulOptionAppendWriterStart] using hstate

theorem statefulOptionAppendPrefix_mem_of_state_mem
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    {state : Nat} {t : TransitionDescription}
    (hstate : state < scanStateCount)
    (ht :
      t ∈ statefulOptionAppendStateTransitions
        scanStateCount next emit state) :
    t ∈ statefulOptionAppendPrefixTransitions
        scanStateCount next emit := by
  rw [statefulOptionAppendPrefixTransitions, List.mem_flatten]
  refine
    ⟨statefulOptionAppendStateTransitions
      scanStateCount next emit state, ?_, ht⟩
  rw [List.mem_map]
  exact ⟨state, List.mem_range.mpr hstate, rfl⟩

theorem statefulOptionAppendPrefix_wellFormed
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    forall t : TransitionDescription,
      t ∈ statefulOptionAppendPrefixTransitions
          scanStateCount next emit ->
        TransitionDescription.WellFormed
          (statefulOptionAppendHalt scanStateCount final + 1) t := by
  intro t ht
  rw [statefulOptionAppendPrefixTransitions, List.mem_flatten] at ht
  rcases ht with ⟨rows, hrows, ht⟩
  rw [List.mem_map] at hrows
  rcases hrows with ⟨state, hstateRange, hrows⟩
  subst rows
  have hstate : state < scanStateCount := by
    simpa using List.mem_range.mp hstateRange
  have htwf :=
    statefulOptionAppendStateTransitions_wellFormed
      scanStateCount next emit final hnext state t hstate ht
  simpa using htwf

theorem statefulOptionAppendStateTransitions_deterministic
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (state : Nat) :
    forall t u : TransitionDescription,
      t ∈ statefulOptionAppendStateTransitions
          scanStateCount next emit state ->
      u ∈ statefulOptionAppendStateTransitions
          scanStateCount next emit state ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u := by
  intro t u ht hu hkey
  simp [statefulOptionAppendStateTransitions] at ht hu
  rcases ht with ht | ht | ht <;>
    rcases hu with hu | hu | hu <;>
    subst t <;> subst u <;>
    simp [TransitionDescription.SameKey,
      TransitionDescription.SameAction] at hkey ⊢

theorem statefulOptionAppendPrefix_deterministic
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool) :
    forall t u : TransitionDescription,
      t ∈ statefulOptionAppendPrefixTransitions
          scanStateCount next emit ->
      u ∈ statefulOptionAppendPrefixTransitions
          scanStateCount next emit ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u := by
  intro t u ht hu hkey
  rw [statefulOptionAppendPrefixTransitions, List.mem_flatten] at ht hu
  rcases ht with ⟨rowsT, hrowsT, ht⟩
  rcases hu with ⟨rowsU, hrowsU, hu⟩
  rw [List.mem_map] at hrowsT hrowsU
  rcases hrowsT with ⟨stateT, _hstateTRange, hrowsT⟩
  rcases hrowsU with ⟨stateU, _hstateURange, hrowsU⟩
  subst rowsT
  subst rowsU
  simp [statefulOptionAppendStateTransitions] at ht hu
  rcases ht with ht | ht | ht <;>
    rcases hu with hu | hu | hu <;>
    subst t <;> subst u <;>
    simp [TransitionDescription.SameKey,
      TransitionDescription.SameAction] at hkey ⊢ <;>
    rw [hkey] <;>
    simp

theorem statefulOptionAppendTransitions_wellFormed
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    forall t : TransitionDescription,
      t ∈ statefulOptionAppendTransitions
          scanStateCount next emit final ->
        TransitionDescription.WellFormed
          (statefulOptionAppendHalt scanStateCount final + 1) t := by
  intro t ht
  simp [statefulOptionAppendTransitions] at ht
  rcases ht with ht | ht
  · exact statefulOptionAppendPrefix_wellFormed
      scanStateCount next emit final hnext t ht
  · have htwf :=
      copyAppendWordWriteTransitionsFrom_wellFormed
        (statefulOptionAppendWriterStart scanStateCount) final t ht
    simpa [statefulOptionAppendHalt, statefulOptionAppendWriterStart,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htwf

theorem statefulOptionAppendTransitions_deterministic
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool) :
    forall t u : TransitionDescription,
      t ∈ statefulOptionAppendTransitions
          scanStateCount next emit final ->
      u ∈ statefulOptionAppendTransitions
          scanStateCount next emit final ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u := by
  intro t u ht hu hkey
  simp [statefulOptionAppendTransitions] at ht hu
  rcases ht with ht | ht <;> rcases hu with hu | hu
  · exact statefulOptionAppendPrefix_deterministic
      scanStateCount next emit t u ht hu hkey
  · have hubounds :=
      copyAppendWordWriteTransitionsFrom_source_bounds
        (statefulOptionAppendWriterStart scanStateCount)
        (statefulOptionAppendHalt scanStateCount final) final u hu
    have htsource :=
      statefulOptionAppendPrefix_source_lt_writerStart
        scanStateCount next emit t ht
    have husource : u.source = t.source := hkey.left.symm
    simp [statefulOptionAppendWriterStart] at htsource hubounds
    omega
  · have htbounds :=
      copyAppendWordWriteTransitionsFrom_source_bounds
        (statefulOptionAppendWriterStart scanStateCount)
        (statefulOptionAppendHalt scanStateCount final) final t ht
    have husourceLt :=
      statefulOptionAppendPrefix_source_lt_writerStart
        scanStateCount next emit u hu
    have htsource : t.source = u.source := hkey.left
    simp [statefulOptionAppendWriterStart] at husourceLt htbounds
    omega
  · exact
      copyAppendWordWriteTransitionsFrom_deterministic
        (statefulOptionAppendWriterStart scanStateCount) final
        t u
        (by
          simpa [statefulOptionAppendHalt, statefulOptionAppendWriterStart,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht)
        (by
          simpa [statefulOptionAppendHalt, statefulOptionAppendWriterStart,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu)
        hkey

theorem statefulOptionAppendTransitions_haltTransitionFree
    (scanStateCount : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool) :
    forall t : TransitionDescription,
      t ∈ statefulOptionAppendTransitions
          scanStateCount next emit final ->
      t.source = statefulOptionAppendHalt scanStateCount final ->
        False := by
  intro t ht hsource
  simp [statefulOptionAppendTransitions] at ht
  rcases ht with ht | ht
  · have hlt :=
      statefulOptionAppendPrefix_source_lt_writerStart
        scanStateCount next emit t ht
    simp [statefulOptionAppendHalt,
      statefulOptionAppendWriterStart] at hsource hlt
    omega
  · have hbounds :=
      copyAppendWordWriteTransitionsFrom_source_bounds
        (statefulOptionAppendWriterStart scanStateCount)
        (statefulOptionAppendHalt scanStateCount final) final t ht
    simp [statefulOptionAppendHalt,
      statefulOptionAppendWriterStart] at hsource hbounds
    omega

end FiniteTransducer

def generatedStatefulOptionAppendDescription
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool) : MachineDescription where
  stateCount :=
    FiniteTransducer.statefulOptionAppendHalt scanStateCount final + 1
  start := start
  halt := FiniteTransducer.statefulOptionAppendHalt scanStateCount final
  transitions :=
    FiniteTransducer.statefulOptionAppendTransitions
      scanStateCount next emit final

theorem generatedStatefulOptionAppendDescription_wellFormed
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (hstart : start < scanStateCount)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    (generatedStatefulOptionAppendDescription
      scanStateCount start next emit final).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [generatedStatefulOptionAppendDescription]
  · simp [generatedStatefulOptionAppendDescription,
      FiniteTransducer.statefulOptionAppendHalt,
      FiniteTransducer.statefulOptionAppendWriterStart]
    omega
  · simp [generatedStatefulOptionAppendDescription]
  · intro t ht
    exact
      FiniteTransducer.statefulOptionAppendTransitions_wellFormed
        scanStateCount next emit final hnext t ht
  · intro t u ht hu hkey
    exact
      FiniteTransducer.statefulOptionAppendTransitions_deterministic
        scanStateCount next emit final t u ht hu hkey

theorem generatedStatefulOptionAppendDescription_haltTransitionFree
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool) :
    (generatedStatefulOptionAppendDescription
      scanStateCount start next emit final).HaltTransitionFree := by
  intro t ht hsource
  exact
    FiniteTransducer.statefulOptionAppendTransitions_haltTransitionFree
      scanStateCount next emit final t ht hsource

theorem generatedStatefulOptionAppendDescription_subroutineReady
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (hstart : start < scanStateCount)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    (generatedStatefulOptionAppendDescription
      scanStateCount start next emit final).SubroutineReady :=
  ⟨generatedStatefulOptionAppendDescription_wellFormed
      scanStateCount start next emit final hstart hnext,
    generatedStatefulOptionAppendDescription_haltTransitionFree
      scanStateCount start next emit final⟩

theorem find?_some_predicate_true
    {α : Type} {p : α -> Bool} {l : List α} {x : α}
    (hfind : l.find? p = some x) : p x = true := by
  induction l with
  | nil =>
      simp at hfind
  | cons head tail ih =>
      rw [List.find?_cons] at hfind
      cases hhead : p head
      · simp [hhead] at hfind
        exact ih hfind
      · simp [hhead] at hfind
        cases hfind
        exact hhead

theorem sameKey_of_matches_same
    {source : Nat} {read : Option Bool}
    {t u : TransitionDescription}
    (ht : Matches source read t = true)
    (hu : Matches source read u = true) :
    TransitionDescription.SameKey t u := by
  simp [Matches] at ht hu
  exact ⟨ht.left.trans hu.left.symm, ht.right.trans hu.right.symm⟩

theorem lookupTransition_sameAction_of_candidate
    (D : MachineDescription)
    (source : Nat) (read : Option Bool)
    (candidate : TransitionDescription)
    (hdet : D.Deterministic)
    (hmem : candidate ∈ D.transitions)
    (hmatch : Matches source read candidate = true) :
    exists found : TransitionDescription,
      D.lookupTransition source read = some found ∧
        TransitionDescription.SameAction candidate found := by
  cases hlookup : D.lookupTransition source read with
  | none =>
      unfold lookupTransition at hlookup
      have hnone :=
        List.find?_eq_none.mp hlookup candidate hmem
      rw [hmatch] at hnone
      contradiction
  | some found =>
      have hfoundMem :
          found ∈ D.transitions :=
        MachineDescription.lookupTransition_mem hlookup
      have hfoundMatch : Matches source read found = true := by
        unfold lookupTransition at hlookup
        exact find?_some_predicate_true hlookup
      have hkey :=
        sameKey_of_matches_same hmatch hfoundMatch
      exact ⟨found, rfl, hdet candidate found hmem hfoundMem hkey⟩

theorem generatedStatefulOptionAppendDescription_step_bit
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (state : Nat) (bit : Bool)
    (left right : List (Option Bool))
    (hstate : state < scanStateCount) :
    (generatedStatefulOptionAppendDescription
      scanStateCount start next emit final).runConfig 1
        { state := state
          tape := tapeAtCells left (some bit :: right) } =
      { state := next state bit
        tape := tapeAtCells (emit state bit :: left) right } := by
  let candidate : TransitionDescription :=
    { source := state
      read := some bit
      write := emit state bit
      move := Direction.right
      target := next state bit }
  have hstateMem :
      candidate ∈
        FiniteTransducer.statefulOptionAppendStateTransitions
          scanStateCount next emit state := by
    cases bit <;>
      simp [candidate,
        FiniteTransducer.statefulOptionAppendStateTransitions]
  have hprefixMem :
      candidate ∈
        FiniteTransducer.statefulOptionAppendPrefixTransitions
          scanStateCount next emit :=
    FiniteTransducer.statefulOptionAppendPrefix_mem_of_state_mem
      scanStateCount next emit hstate hstateMem
  have hmem :
      candidate ∈
        (generatedStatefulOptionAppendDescription
          scanStateCount start next emit final).transitions := by
    simp [generatedStatefulOptionAppendDescription,
      FiniteTransducer.statefulOptionAppendTransitions, hprefixMem]
  have hmatch :
      Matches state (some bit) candidate = true := by
    cases bit <;> simp [candidate, Matches]
  have hdet :
      (generatedStatefulOptionAppendDescription
        scanStateCount start next emit final).Deterministic := by
    intro t u ht hu hkey
    exact
      FiniteTransducer.statefulOptionAppendTransitions_deterministic
        scanStateCount next emit final t u ht hu hkey
  rcases lookupTransition_sameAction_of_candidate
      (generatedStatefulOptionAppendDescription
        scanStateCount start next emit final)
      state (some bit) candidate hdet hmem hmatch with
    ⟨found, hlookup, haction⟩
  rcases haction with ⟨hwrite, hmove, htarget⟩
  cases bit <;> cases right <;>
    simp [runConfig, stepConfig, hlookup, candidate, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight] at hwrite hmove htarget ⊢ <;>
    rw [← hwrite, ← hmove, ← htarget] <;>
    constructor <;> rfl

theorem generatedStatefulOptionAppendDescription_step_blank
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (state : Nat) (left : List (Option Bool))
    (hstate : state < scanStateCount) :
    (generatedStatefulOptionAppendDescription
      scanStateCount start next emit final).runConfig 1
        { state := state
          tape := tapeAtCells left [none] } =
      { state := FiniteTransducer.statefulOptionAppendWriterStart
          scanStateCount
        tape := tapeAtCells (none :: left) [none] } := by
  let candidate : TransitionDescription :=
    { source := state
      read := none
      write := none
      move := Direction.right
      target :=
        FiniteTransducer.statefulOptionAppendWriterStart scanStateCount }
  have hstateMem :
      candidate ∈
        FiniteTransducer.statefulOptionAppendStateTransitions
          scanStateCount next emit state := by
    simp [candidate,
      FiniteTransducer.statefulOptionAppendStateTransitions]
  have hprefixMem :
      candidate ∈
        FiniteTransducer.statefulOptionAppendPrefixTransitions
          scanStateCount next emit :=
    FiniteTransducer.statefulOptionAppendPrefix_mem_of_state_mem
      scanStateCount next emit hstate hstateMem
  have hmem :
      candidate ∈
        (generatedStatefulOptionAppendDescription
          scanStateCount start next emit final).transitions := by
    simp [generatedStatefulOptionAppendDescription,
      FiniteTransducer.statefulOptionAppendTransitions, hprefixMem]
  have hmatch :
      Matches state none candidate = true := by
    simp [candidate, Matches]
  have hdet :
      (generatedStatefulOptionAppendDescription
        scanStateCount start next emit final).Deterministic := by
    intro t u ht hu hkey
    exact
      FiniteTransducer.statefulOptionAppendTransitions_deterministic
        scanStateCount next emit final t u ht hu hkey
  rcases lookupTransition_sameAction_of_candidate
      (generatedStatefulOptionAppendDescription
        scanStateCount start next emit final)
      state none candidate hdet hmem hmatch with
    ⟨found, hlookup, haction⟩
  rcases haction with ⟨hwrite, hmove, htarget⟩
  simp [runConfig, stepConfig, hlookup, candidate, tapeAtCells,
    Tape.read, Tape.write, Tape.move, Tape.moveRight] at hwrite hmove htarget ⊢
  rw [← hwrite, ← hmove, ← htarget]
  constructor <;> rfl

theorem generatedStatefulOptionAppendDescription_step_blank_withPadding
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (state : Nat) (left padding : List (Option Bool))
    (hstate : state < scanStateCount) :
    (generatedStatefulOptionAppendDescription
      scanStateCount start next emit final).runConfig 1
        { state := state
          tape := tapeAtCells left (none :: padding) } =
      { state := FiniteTransducer.statefulOptionAppendWriterStart
          scanStateCount
        tape := tapeAtCells (none :: left) padding } := by
  let candidate : TransitionDescription :=
    { source := state
      read := none
      write := none
      move := Direction.right
      target :=
        FiniteTransducer.statefulOptionAppendWriterStart scanStateCount }
  have hstateMem :
      candidate ∈
        FiniteTransducer.statefulOptionAppendStateTransitions
          scanStateCount next emit state := by
    simp [candidate,
      FiniteTransducer.statefulOptionAppendStateTransitions]
  have hprefixMem :
      candidate ∈
        FiniteTransducer.statefulOptionAppendPrefixTransitions
          scanStateCount next emit :=
    FiniteTransducer.statefulOptionAppendPrefix_mem_of_state_mem
      scanStateCount next emit hstate hstateMem
  have hmem :
      candidate ∈
        (generatedStatefulOptionAppendDescription
          scanStateCount start next emit final).transitions := by
    simp [generatedStatefulOptionAppendDescription,
      FiniteTransducer.statefulOptionAppendTransitions, hprefixMem]
  have hmatch :
      Matches state none candidate = true := by
    simp [candidate, Matches]
  have hdet :
      (generatedStatefulOptionAppendDescription
        scanStateCount start next emit final).Deterministic := by
    intro t u ht hu hkey
    exact
      FiniteTransducer.statefulOptionAppendTransitions_deterministic
        scanStateCount next emit final t u ht hu hkey
  rcases lookupTransition_sameAction_of_candidate
      (generatedStatefulOptionAppendDescription
        scanStateCount start next emit final)
      state none candidate hdet hmem hmatch with
    ⟨found, hlookup, haction⟩
  rcases haction with ⟨hwrite, hmove, htarget⟩
  cases padding <;>
    simp [runConfig, stepConfig, hlookup, candidate, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight] at hwrite hmove htarget ⊢ <;>
    rw [← hwrite, ← hmove, ← htarget] <;>
    constructor <;> rfl

theorem generatedStatefulOptionAppendDescription_writerRuns
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (left : List (Option Bool)) :
    (generatedStatefulOptionAppendDescription
      scanStateCount start next emit final).runConfig
        final.length
        { state :=
            FiniteTransducer.statefulOptionAppendWriterStart scanStateCount
          tape := tapeAtCells left [none] } =
      { state :=
          (generatedStatefulOptionAppendDescription
            scanStateCount start next emit final).halt
        tape := statefulOptionAppendWriteTargetTapeAtBlank left final } := by
  have hpre :
      forall t : TransitionDescription,
        t ∈ FiniteTransducer.statefulOptionAppendPrefixTransitions
            scanStateCount next emit ->
          t.source <
            FiniteTransducer.statefulOptionAppendWriterStart
              scanStateCount :=
    FiniteTransducer.statefulOptionAppendPrefix_source_lt_writerStart
      scanStateCount next emit
  have hrun :=
    copyAppendWordWriteTransitionsFrom_run_with_pre
      (FiniteTransducer.statefulOptionAppendPrefixTransitions
        scanStateCount next emit)
      (FiniteTransducer.statefulOptionAppendWriterStart scanStateCount)
      start final left hpre
  simpa [generatedStatefulOptionAppendDescription,
    FiniteTransducer.statefulOptionAppendTransitions,
    FiniteTransducer.statefulOptionAppendHalt,
    statefulOptionAppendWriteTargetTapeAtBlank] using hrun

theorem generatedStatefulOptionAppendDescription_statefulContract
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool) :
    StatefulOptionAppendMachineContract
      (generatedStatefulOptionAppendDescription
        scanStateCount start next emit final)
      scanStateCount
      next
      emit
      final := by
  constructor
  · intro state bit left right hstate
    exact generatedStatefulOptionAppendDescription_step_bit
      scanStateCount start next emit final state bit left right hstate
  · intro state left hstate
    simpa [FiniteTransducer.statefulOptionAppendWriterStart] using
      generatedStatefulOptionAppendDescription_step_blank
        scanStateCount start next emit final state left hstate
  · intro left
    simpa [FiniteTransducer.statefulOptionAppendWriterStart] using
      generatedStatefulOptionAppendDescription_writerRuns
        scanStateCount start next emit final left

theorem statefulOptionAppendTransducer_compiledByGeneratedDescription
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final : Word Bool)
    (hstart : start < scanStateCount)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    ExactCompiledByDescription
      (statefulOptionAppendTransducer
        scanStateCount start next emit final)
      (generatedStatefulOptionAppendDescription
        scanStateCount start next emit final)
      (fun input _output leftScratch =>
        FSTStatefulOptionAppendTargetTape
          next emit start input final leftScratch) := by
  exact
    statefulOptionAppendTransducer_compiledByMachineContract
      (generatedStatefulOptionAppendDescription
        scanStateCount start next emit final)
      scanStateCount start next emit final
      (generatedStatefulOptionAppendDescription_subroutineReady
        scanStateCount start next emit final hstart hnext)
      (generatedStatefulOptionAppendDescription_statefulContract
        scanStateCount start next emit final)
      hstart
      rfl
      hnext

theorem generatedStatefulOptionAppendDescription_haltsFrom_tapeAtCells
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final input : Word Bool)
    (left : List (Option Bool))
    (hstart : start < scanStateCount)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    (generatedStatefulOptionAppendDescription
      scanStateCount start next emit final).HaltsFromTape
      (tapeAtCells left (List.append (input.map some) [none]))
      (FSTStatefulOptionAppendTargetTapeFromLeft
        next emit start input final left) := by
  exact
    (generatedStatefulOptionAppendDescription_statefulContract
      scanStateCount start next emit final).haltsFrom_tapeAtCells
        hnext start input left hstart rfl

theorem generatedStatefulOptionAppendDescription_haltsFrom_tapeAtCells_nil_withPadding
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (input : Word Bool)
    (left padding : List (Option Bool))
    (hstart : start < scanStateCount)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    (generatedStatefulOptionAppendDescription
      scanStateCount start next emit []).HaltsFromTape
      (tapeAtCells left (List.append (input.map some) (none :: padding)))
      (FSTStatefulOptionAppendTargetTapeFromLeftWithPadding
        next emit start input left padding) := by
  let D :=
    generatedStatefulOptionAppendDescription
      scanStateCount start next emit []
  have hscan :=
    (generatedStatefulOptionAppendDescription_statefulContract
      scanStateCount start next emit []).run_scan_withPadding
        hnext input start left padding hstart
  have hblank :=
    generatedStatefulOptionAppendDescription_step_blank_withPadding
      scanStateCount start next emit []
      (statefulOptionAfter next start input)
      (List.append
        (statefulOptionCellsFrom next emit start input).reverse
        left)
      padding
      (statefulOptionAfter_lt scanStateCount next hnext
        start input hstart)
  have hrun :
      D.runConfig (input.length + 1)
          { state := D.start
            tape :=
              tapeAtCells left
                (List.append (input.map some) (none :: padding)) } =
        { state := D.halt
          tape :=
            FSTStatefulOptionAppendTargetTapeFromLeftWithPadding
              next emit start input left padding } := by
    rw [show input.length + 1 = input.length + 1 by rfl]
    rw [runConfig_add]
    simpa [D, generatedStatefulOptionAppendDescription,
      FSTStatefulOptionAppendTargetTapeFromLeftWithPadding,
      FiniteTransducer.statefulOptionAppendHalt,
      FiniteTransducer.statefulOptionAppendWriterStart] using
      congrArg (fun cfg =>
        (generatedStatefulOptionAppendDescription
          scanStateCount start next emit []).runConfig 1 cfg) hscan ▸
        hblank
  refine ⟨input.length + 1, ?_⟩
  constructor
  · exact congrArg MachineDescription.Configuration.state hrun
  · exact congrArg MachineDescription.Configuration.tape hrun

theorem generatedStatefulOptionAppendDescription_haltsFrom_prefixedSourceTape
    (scanStateCount start : Nat)
    (next : Nat -> Bool -> Nat)
    (emit : Nat -> Bool -> Option Bool)
    (final pref input : Word Bool)
    (leftScratch : Nat)
    (hstart : start < scanStateCount)
    (hnext :
      forall state bit, state < scanStateCount ->
        next state bit < scanStateCount) :
    (generatedStatefulOptionAppendDescription
      scanStateCount start next emit final).HaltsFromTape
      (FSTStatefulOptionAppendPrefixedSourceTape
        pref input leftScratch)
      (FSTStatefulOptionAppendPrefixedTargetTape
        next emit start pref input final leftScratch) := by
  exact
    (generatedStatefulOptionAppendDescription_statefulContract
      scanStateCount start next emit final).haltsFrom_prefixedSourceTape
        hnext start pref input leftScratch hstart rfl

end FiniteTransducers
end CommonGround

end Computability
end FoC
