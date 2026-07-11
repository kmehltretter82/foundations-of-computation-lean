import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeHelpers

set_option doc.verso true

/-!
# Typed state tables for structured three-tape machines

Large structured cores are easier to build and verify as a total transition
function over a typed control-state alphabet than as a literal row list.
This module compiles such a typed table into a concrete
{name (full := FoC.Computability.CommonGround.FiniteTransducers.Structured.Description)}`Description`
and proves the table facts once: well-formedness, determinism, halt-freeness,
lowerer row support, and the lookup/step keystone that lets every run proof
happen at the typed level without ever unfolding the generated row list.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

open ThreeTape

/-- All cells a Boolean logical tape can read. -/
def readCells : List (Option Bool) :=
  [none, some false, some true]

theorem mem_readCells (r : Option Bool) : r ∈ readCells := by
  cases r with
  | none => simp [readCells]
  | some bit => cases bit <;> simp [readCells]

/-- All read triples of a three-tape structured machine. -/
def readTriples : List (Option Bool × Option Bool × Option Bool) :=
  readCells.flatMap fun r0 =>
    readCells.flatMap fun r1 =>
      readCells.map fun r2 => (r0, r1, r2)

theorem mem_readTriples (r0 r1 r2 : Option Bool) :
    (r0, r1, r2) ∈ readTriples :=
  List.mem_flatMap.mpr
    ⟨r0, mem_readCells r0,
      List.mem_flatMap.mpr
        ⟨r1, mem_readCells r1,
          List.mem_map.mpr ⟨r2, mem_readCells r2, rfl⟩⟩⟩

/-- One typed step: the typed target state and the three tape actions. -/
structure TypedStep (σ : Type) where
  target : σ
  action0 : TapeAction
  action1 : TapeAction
  action2 : TapeAction

/--
First-occurrence index of an element in a list.

Unlike a bare position count this indexer needs no duplicate-freeness for
injectivity on members: two members with the same first occurrence are equal.
-/
def listIndexOf {σ : Type} [DecidableEq σ] : List σ -> σ -> Nat
  | [], _ => 0
  | x :: xs, s => if x = s then 0 else listIndexOf xs s + 1

theorem listIndexOf_lt_length {σ : Type} [DecidableEq σ] :
    forall {l : List σ} {s : σ}, s ∈ l ->
      listIndexOf l s < l.length := by
  intro l
  induction l with
  | nil =>
      intro s hs
      cases hs
  | cons x xs ih =>
      intro s hs
      by_cases hx : x = s
      · simp [listIndexOf, hx]
      · have hs' : s ∈ xs := by
          rcases List.mem_cons.mp hs with heq | hmem
          · exact absurd heq.symm hx
          · exact hmem
        have := ih hs'
        simp [listIndexOf, hx]
        exact this

theorem listIndexOf_inj {σ : Type} [DecidableEq σ] :
    forall {l : List σ} {s t : σ}, s ∈ l -> t ∈ l ->
      listIndexOf l s = listIndexOf l t -> s = t := by
  intro l
  induction l with
  | nil =>
      intro s t hs
      cases hs
  | cons x xs ih =>
      intro s t hs ht hid
      by_cases hxs : x = s
      · by_cases hxt : x = t
        · rw [← hxs, hxt]
        · rw [show listIndexOf (x :: xs) s = 0 by
              simp [listIndexOf, hxs]] at hid
          rw [show listIndexOf (x :: xs) t =
              listIndexOf xs t + 1 by
              simp [listIndexOf, hxt]] at hid
          cases hid
      · by_cases hxt : x = t
        · rw [show listIndexOf (x :: xs) t = 0 by
              simp [listIndexOf, hxt]] at hid
          rw [show listIndexOf (x :: xs) s =
              listIndexOf xs s + 1 by
              simp [listIndexOf, hxs]] at hid
          cases hid
        · have hs' : s ∈ xs := by
            rcases List.mem_cons.mp hs with heq | hmem
            · exact absurd heq.symm hxs
            · exact hmem
          have ht' : t ∈ xs := by
            rcases List.mem_cons.mp ht with heq | hmem
            · exact absurd heq.symm hxt
            · exact hmem
          have hid' :
              listIndexOf xs s = listIndexOf xs t := by
            have h1 : listIndexOf (x :: xs) s =
                listIndexOf xs s + 1 := by
              simp [listIndexOf, hxs]
            have h2 : listIndexOf (x :: xs) t =
                listIndexOf xs t + 1 := by
              simp [listIndexOf, hxt]
            rw [h1, h2] at hid
            exact Nat.succ.inj hid
          exact ih hs' ht' hid'

/--
A typed three-tape state table.

{lit}`next` is the semantic transition function; {lit}`states` enumerates the
control states realized in the compiled row list, and {lit}`stateId` embeds
them injectively below {lit}`stateCount`.  The compiled machine is total
exactly where {lit}`next` is defined.
-/
structure TypedStateTable (σ : Type) where
  states : List σ
  stateCount : Nat
  stateId : σ -> Nat
  start : σ
  halt : σ
  next :
    σ -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep σ)
  start_mem : start ∈ states
  halt_mem : halt ∈ states
  stateId_lt :
    forall s : σ, s ∈ states -> stateId s < stateCount
  stateId_inj :
    forall s : σ, s ∈ states ->
      forall t : σ, t ∈ states ->
        stateId s = stateId t -> s = t
  halt_next :
    forall r0 r1 r2 : Option Bool, next halt r0 r1 r2 = none
  next_target_mem :
    forall s : σ, s ∈ states ->
      forall r0 r1 r2 : Option Bool, forall st : TypedStep σ,
        next s r0 r1 r2 = some st -> st.target ∈ states

namespace TypedStateTable

variable {σ : Type} (M : TypedStateTable σ)

/-- Compile one typed step into a concrete transition row. -/
def rowOf (s : σ) (r0 r1 r2 : Option Bool) (st : TypedStep σ) :
    Transition :=
  ThreeTape.row (M.stateId s) r0 r1 r2
    st.action0 st.action1 st.action2 (M.stateId st.target)

/-- All rows compiled for one typed source state. -/
def rowsFor (s : σ) : List Transition :=
  readTriples.filterMap fun t =>
    (M.next s t.1 t.2.1 t.2.2).map (M.rowOf s t.1 t.2.1 t.2.2)

/-- The compiled structured three-tape description. -/
def description : Description where
  tapeCount := 3
  stateCount := M.stateCount
  start := M.stateId M.start
  halt := M.stateId M.halt
  transitions := M.states.flatMap M.rowsFor

@[simp] theorem description_tapeCount :
    M.description.tapeCount = 3 := rfl

@[simp] theorem description_stateCount :
    M.description.stateCount = M.stateCount := rfl

@[simp] theorem description_start :
    M.description.start = M.stateId M.start := rfl

@[simp] theorem description_halt :
    M.description.halt = M.stateId M.halt := rfl

theorem mem_rowsFor {s : σ} {tr : Transition}
    (h : tr ∈ M.rowsFor s) :
    exists r0 r1 r2 : Option Bool, exists st : TypedStep σ,
      M.next s r0 r1 r2 = some st ∧
        tr = M.rowOf s r0 r1 r2 st := by
  rcases List.mem_filterMap.mp h with ⟨t, _ht, hmap⟩
  cases hnext : M.next s t.1 t.2.1 t.2.2 with
  | none =>
      rw [hnext] at hmap
      cases hmap
  | some st =>
      rw [hnext] at hmap
      injection hmap with hmap'
      exact ⟨t.1, t.2.1, t.2.2, st, hnext, hmap'.symm⟩

theorem mem_transitions {tr : Transition}
    (h : tr ∈ M.description.transitions) :
    exists s : σ, s ∈ M.states ∧ tr ∈ M.rowsFor s := by
  rcases List.mem_flatMap.mp h with ⟨s, hs, hrow⟩
  exact ⟨s, hs, hrow⟩

/-!
## Table facts
-/

theorem description_wellFormed : M.description.WellFormed := by
  refine
    ⟨Nat.succ_pos 2,
      Nat.lt_of_le_of_lt (Nat.zero_le _)
        (M.stateId_lt M.start M.start_mem),
      M.stateId_lt M.start M.start_mem,
      M.stateId_lt M.halt M.halt_mem,
      ?_, ?_⟩
  · intro t ht
    rcases M.mem_transitions ht with ⟨s, hs, hrow⟩
    rcases M.mem_rowsFor hrow with ⟨r0, r1, r2, st, hnext, rfl⟩
    exact
      ⟨M.stateId_lt s hs,
        M.stateId_lt st.target
          (M.next_target_mem s hs r0 r1 r2 st hnext),
        rfl, rfl⟩
  · intro t u ht hu hkey
    rcases M.mem_transitions ht with ⟨s1, hs1, hrow1⟩
    rcases M.mem_rowsFor hrow1 with ⟨r0, r1, r2, st1, hnext1, rfl⟩
    rcases M.mem_transitions hu with ⟨s2, hs2, hrow2⟩
    rcases M.mem_rowsFor hrow2 with ⟨p0, p1, p2, st2, hnext2, rfl⟩
    rcases hkey with ⟨hsource, hreads⟩
    have hs12 : s1 = s2 :=
      M.stateId_inj s1 hs1 s2 hs2 hsource
    subst hs12
    have hr0 : r0 = p0 := by injection hreads
    have hreads1 :
        ([r1, r2] : List (Option Bool)) = [p1, p2] := by
      injection hreads
    have hr1 : r1 = p1 := by injection hreads1
    have hreads2 : ([r2] : List (Option Bool)) = [p2] := by
      injection hreads1
    have hr2 : r2 = p2 := by injection hreads2
    subst hr0
    subst hr1
    subst hr2
    have hst : st1 = st2 := by
      have := hnext1.symm.trans hnext2
      injection this
    subst hst
    exact ⟨rfl, rfl⟩

theorem description_haltTransitionFree :
    M.description.HaltTransitionFree := by
  intro t ht hsource
  rcases M.mem_transitions ht with ⟨s, hs, hrow⟩
  rcases M.mem_rowsFor hrow with ⟨r0, r1, r2, st, hnext, rfl⟩
  have hshalt : s = M.halt :=
    M.stateId_inj s hs M.halt M.halt_mem hsource
  subst hshalt
  rw [M.halt_next r0 r1 r2] at hnext
  cases hnext

theorem description_supportsReadWriteRows3 :
    SupportsReadWriteRows3 M.description := by
  refine ⟨rfl, ?_⟩
  intro t ht
  rcases M.mem_transitions ht with ⟨s, hs, hrow⟩
  rcases M.mem_rowsFor hrow with ⟨r0, r1, r2, st, hnext, rfl⟩
  exact
    ThreeTape.row_supportsReadWriteRow3
      (M.stateId s) (M.stateId st.target) r0 r1 r2
      st.action0 st.action1 st.action2

theorem description_subroutineReady :
    M.description.SubroutineReady :=
  ⟨M.description_wellFormed, M.description_haltTransitionFree⟩

/-!
## Lookup keystone
-/

private theorem matches_rowOf_self
    (s : σ) (r0 r1 r2 : Option Bool) (st : TypedStep σ) :
    Description.Matches (M.stateId s) [r0, r1, r2]
        (M.rowOf s r0 r1 r2 st) = true := by
  simp [Description.Matches, rowOf, ThreeTape.row]

private theorem matches_rowOf_of_ne_reads
    {s : σ} {r0 r1 r2 p0 p1 p2 : Option Bool} {st : TypedStep σ}
    (hne : (p0, p1, p2) ≠ (r0, r1, r2)) :
    Description.Matches (M.stateId s) [r0, r1, r2]
        (M.rowOf s p0 p1 p2 st) = false := by
  cases hmatch :
      Description.Matches (M.stateId s) [r0, r1, r2] (M.rowOf s p0 p1 p2 st) with
  | false => rfl
  | true =>
      exfalso
      have hpair := hmatch
      simp [Description.Matches, rowOf, ThreeTape.row] at hpair
      exact hne (by simp [hpair.left, hpair.right.left, hpair.right.right])

private theorem find?_rowsFor_self
    (s : σ) (r0 r1 r2 : Option Bool) :
    (M.rowsFor s).find? (Description.Matches (M.stateId s) [r0, r1, r2]) =
      (M.next s r0 r1 r2).map (M.rowOf s r0 r1 r2) := by
  have hgeneral :
      forall l : List (Option Bool × Option Bool × Option Bool),
        (l.filterMap fun t =>
            (M.next s t.1 t.2.1 t.2.2).map
              (M.rowOf s t.1 t.2.1 t.2.2)).find?
            (Description.Matches (M.stateId s) [r0, r1, r2]) =
          if (r0, r1, r2) ∈ l then
            (M.next s r0 r1 r2).map (M.rowOf s r0 r1 r2)
          else none := by
    intro l
    induction l with
    | nil => simp
    | cons t ts ih =>
        by_cases hteq : t = (r0, r1, r2)
        · subst hteq
          have hmemhead : (r0, r1, r2) ∈ (r0, r1, r2) :: ts :=
            List.mem_cons.mpr (Or.inl rfl)
          cases hnext : M.next s r0 r1 r2 with
          | none =>
              rw [List.filterMap_cons]
              simp only [hnext, Option.map_none]
              rw [ih]
              simp [hmemhead, hnext]
          | some st =>
              rw [List.filterMap_cons]
              simp only [hnext, Option.map_some]
              rw [List.find?_cons_of_pos
                (M.matches_rowOf_self s r0 r1 r2 st)]
              simp [hmemhead]
        · have hmemtail :
              ((r0, r1, r2) ∈ t :: ts) -> ((r0, r1, r2) ∈ ts) := by
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · exact absurd heq.symm hteq
            · exact hmem'
          have hcond :
              (if (r0, r1, r2) ∈ t :: ts then
                  (M.next s r0 r1 r2).map (M.rowOf s r0 r1 r2)
                else none) =
                if (r0, r1, r2) ∈ ts then
                  (M.next s r0 r1 r2).map (M.rowOf s r0 r1 r2)
                else none := by
            by_cases hmem : (r0, r1, r2) ∈ ts
            · rw [if_pos hmem,
                if_pos (List.mem_cons.mpr (Or.inr hmem))]
            · rw [if_neg hmem,
                if_neg (fun hc => hmem (hmemtail hc))]
          cases hnext : M.next s t.1 t.2.1 t.2.2 with
          | none =>
              rw [List.filterMap_cons]
              simp only [hnext, Option.map_none]
              rw [ih, hcond]
          | some st =>
              rw [List.filterMap_cons]
              simp only [hnext, Option.map_some]
              rw [List.find?_cons_of_neg (by
                rw [M.matches_rowOf_of_ne_reads
                  (s := s) (st := st) (by
                    intro hcontra
                    apply hteq
                    cases t with
                    | mk t0 trest =>
                        cases trest with
                        | mk t1 t2 =>
                            simpa using hcontra)]
                simp)]
              rw [ih, hcond]
  rw [show M.rowsFor s =
      readTriples.filterMap fun t =>
        (M.next s t.1 t.2.1 t.2.2).map
          (M.rowOf s t.1 t.2.1 t.2.2) from rfl,
    hgeneral readTriples]
  simp [mem_readTriples]

private theorem find?_rowsFor_of_ne
    {s s' : σ} (hne : M.stateId s' ≠ M.stateId s)
    (reads : List (Option Bool)) :
    (M.rowsFor s').find? (Description.Matches (M.stateId s) reads) = none := by
  apply List.find?_eq_none.mpr
  intro tr htr hmatch
  rcases M.mem_rowsFor htr with ⟨r0, r1, r2, st, _hnext, rfl⟩
  have hsource : M.stateId s' = M.stateId s := by
    have := hmatch
    simp [Description.Matches, rowOf, ThreeTape.row] at this
    exact this.left
  exact hne hsource

private theorem find?_flatMap
    {s : σ} (hs : s ∈ M.states) (r0 r1 r2 : Option Bool)
    [DecidableEq σ] :
    forall l : List σ, (forall x : σ, x ∈ l -> x ∈ M.states) ->
      (l.flatMap M.rowsFor).find?
          (Description.Matches (M.stateId s) [r0, r1, r2]) =
        if s ∈ l then
          (M.next s r0 r1 r2).map (M.rowOf s r0 r1 r2)
        else none := by
  intro l
  induction l with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro hsub
      rw [List.flatMap_cons]
      by_cases hxs : x = s
      · subst hxs
        have hmemhead : x ∈ x :: xs := List.mem_cons.mpr (Or.inl rfl)
        cases hval :
            (M.next x r0 r1 r2).map (M.rowOf x r0 r1 r2) with
        | none =>
            rw [ThreeTape.find?_append_of_find?_eq_none
              (by rw [M.find?_rowsFor_self x r0 r1 r2, hval])]
            rw [ih (fun y hy => hsub y (List.mem_cons_of_mem x hy))]
            simp [hmemhead, hval]
        | some tr =>
            rw [ThreeTape.find?_append_of_find?_eq_some
              (by rw [M.find?_rowsFor_self x r0 r1 r2, hval])]
            simp [hmemhead]
      · have hid : M.stateId x ≠ M.stateId s := by
          intro hcontra
          exact hxs
            (M.stateId_inj x (hsub x (List.mem_cons.mpr (Or.inl rfl)))
              s hs hcontra)
        rw [ThreeTape.find?_append_of_find?_eq_none
          (M.find?_rowsFor_of_ne hid [r0, r1, r2])]
        rw [ih (fun y hy => hsub y (List.mem_cons_of_mem x hy))]
        have hmemtail : (s ∈ x :: xs) -> (s ∈ xs) := by
          intro hmem
          rcases List.mem_cons.mp hmem with heq | hmem'
          · exact absurd heq.symm hxs
          · exact hmem'
        by_cases hmem : s ∈ xs
        · rw [if_pos hmem, if_pos (List.mem_cons.mpr (Or.inr hmem))]
        · rw [if_neg hmem, if_neg (fun hc => hmem (hmemtail hc))]

/--
Lookup keystone: on a typed state, the compiled machine looks up exactly the
typed transition function on the current reads.
-/
theorem lookupTransition_config [DecidableEq σ]
    {s : σ} (hs : s ∈ M.states) (T0 T1 T2 : Tape Bool) :
    M.description.lookupTransition
        (ThreeTape.config (M.stateId s) T0 T1 T2) =
      (M.next s (Tape.read T0) (Tape.read T1) (Tape.read T2)).map
        (M.rowOf s (Tape.read T0) (Tape.read T1) (Tape.read T2)) := by
  unfold Description.lookupTransition
  rw [ThreeTape.currentReads_config M.description rfl]
  rw [show (ThreeTape.config (M.stateId s) T0 T1 T2).state =
      M.stateId s from rfl]
  rw [show M.description.transitions =
      M.states.flatMap M.rowsFor from rfl]
  rw [M.find?_flatMap hs (Tape.read T0) (Tape.read T1) (Tape.read T2)
    M.states (fun x hx => hx)]
  rw [if_pos hs]

/--
Step keystone: one machine step from a typed state is one typed transition.
-/
theorem stepConfig_config [DecidableEq σ]
    {s : σ} (hs : s ∈ M.states) (T0 T1 T2 : Tape Bool) :
    M.description.stepConfig
        (ThreeTape.config (M.stateId s) T0 T1 T2) =
      (M.next s (Tape.read T0) (Tape.read T1) (Tape.read T2)).map
        fun st =>
          ThreeTape.config (M.stateId st.target)
            (st.action0.apply T0)
            (st.action1.apply T1)
            (st.action2.apply T2) := by
  unfold Description.stepConfig
  rw [M.lookupTransition_config hs T0 T1 T2]
  cases hnext :
      M.next s (Tape.read T0) (Tape.read T1) (Tape.read T2) with
  | none => rfl
  | some st =>
      show some _ = some _
      have happly :
          M.description.applyActions
              [st.action0, st.action1, st.action2]
              [T0, T1, T2] =
            [st.action0.apply T0, st.action1.apply T1,
              st.action2.apply T2] :=
        Description.applyActions_three M.description rfl
          st.action0 st.action1 st.action2 T0 T1 T2
      simp only [rowOf, ThreeTape.row]
      rw [show (ThreeTape.config (M.stateId s) T0 T1 T2).tapes =
        [T0, T1, T2] from rfl]
      rw [happly]
      rfl

/--
Run keystone: unfold one step of {lit}`runConfig` at a typed state with a
defined transition.
-/
theorem runConfig_succ_config [DecidableEq σ]
    {s : σ} (hs : s ∈ M.states) {T0 T1 T2 : Tape Bool}
    {st : TypedStep σ}
    (hnext :
      M.next s (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some st)
    (n : Nat) :
    M.description.runConfig (n + 1)
        (ThreeTape.config (M.stateId s) T0 T1 T2) =
      M.description.runConfig n
        (ThreeTape.config (M.stateId st.target)
          (st.action0.apply T0)
          (st.action1.apply T1)
          (st.action2.apply T2)) := by
  show
    (match
        M.description.stepConfig
          (ThreeTape.config (M.stateId s) T0 T1 T2) with
      | none => ThreeTape.config (M.stateId s) T0 T1 T2
      | some next => M.description.runConfig n next) = _
  rw [M.stepConfig_config hs T0 T1 T2, hnext]
  rfl

/--
Stall keystone: a typed state with no defined transition on the current
reads leaves the compiled machine stuck.
-/
theorem stepConfig_config_none [DecidableEq σ]
    {s : σ} (hs : s ∈ M.states) {T0 T1 T2 : Tape Bool}
    (hnext :
      M.next s (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        none) :
    M.description.stepConfig
        (ThreeTape.config (M.stateId s) T0 T1 T2) = none := by
  rw [M.stepConfig_config hs T0 T1 T2, hnext]
  rfl

/--
Build a typed state table from an enumeration list, indexing states by first
occurrence.  Duplicates in the enumeration are harmless: they compile to
duplicate identical rows.
-/
def ofList {σ : Type} [DecidableEq σ]
    (states : List σ) (start halt : σ)
    (next :
      σ -> Option Bool -> Option Bool -> Option Bool ->
        Option (TypedStep σ))
    (start_mem : start ∈ states)
    (halt_mem : halt ∈ states)
    (halt_next :
      forall r0 r1 r2 : Option Bool, next halt r0 r1 r2 = none)
    (next_target_mem :
      forall s : σ, s ∈ states ->
        forall r0 r1 r2 : Option Bool, forall st : TypedStep σ,
          next s r0 r1 r2 = some st -> st.target ∈ states) :
    TypedStateTable σ where
  states := states
  stateCount := states.length
  stateId := listIndexOf states
  start := start
  halt := halt
  next := next
  start_mem := start_mem
  halt_mem := halt_mem
  stateId_lt := fun _s hs => listIndexOf_lt_length hs
  stateId_inj := fun _s hs _t ht hid => listIndexOf_inj hs ht hid
  halt_next := halt_next
  next_target_mem := next_target_mem

end TypedStateTable

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
