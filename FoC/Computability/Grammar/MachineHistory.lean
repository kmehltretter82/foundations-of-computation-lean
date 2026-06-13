import FoC.Computability.Grammar.SemanticAndTraceTables

set_option doc.verso true

/-!
# Machine-history grammars
-/

namespace FoC
namespace Computability

open Languages
open Grammars

/-!
# Finite machine-history grammars

The finite trace-table grammar handles finite evidence.  The textbook
recognizer-to-grammar construction needs finite productions that can simulate
arbitrarily long computations.  The following grammar data is the concrete
semi-Thue system used for that construction: it generates halting
configurations, runs machine transitions backward, and cleans an initial
configuration to the input word.
-/

inductive MachineHistoryNonterminal (D : MachineDescription) where
  | start : MachineHistoryNonterminal D
  | genLeft : MachineHistoryNonterminal D
  | genHead : MachineHistoryNonterminal D
  | genRight : MachineHistoryNonterminal D
  | cleanup : MachineHistoryNonterminal D
  | leftBoundary : MachineHistoryNonterminal D
  | rightBoundary : MachineHistoryNonterminal D
  | cell : Option Bool -> MachineHistoryNonterminal D
  | lockedState : Fin (D.stateCount + 1) -> MachineHistoryNonterminal D
  | state : Fin (D.stateCount + 1) -> MachineHistoryNonterminal D
deriving DecidableEq

namespace MachineHistoryNonterminal

def optionBoolValues : List (Option Bool) :=
  [none, some false, some true]

def finite (D : MachineDescription) :
    Foundation.FiniteType (MachineHistoryNonterminal D) where
  elems :=
    [ start, genLeft, genHead, genRight, cleanup,
      leftBoundary, rightBoundary ] ++
      optionBoolValues.map cell ++
      (List.finRange (D.stateCount + 1)).map lockedState ++
      (List.finRange (D.stateCount + 1)).map state
  complete := by
    intro x
    cases x with
    | start => simp [optionBoolValues]
    | genLeft => simp [optionBoolValues]
    | genHead => simp [optionBoolValues]
    | genRight => simp [optionBoolValues]
    | cleanup => simp [optionBoolValues]
    | leftBoundary => simp [optionBoolValues]
    | rightBoundary => simp [optionBoolValues]
    | cell c =>
        cases c with
        | none => simp [optionBoolValues]
        | some b =>
            cases b <;> simp [optionBoolValues]
    | lockedState q =>
        simp [optionBoolValues, List.mem_finRange]
    | state q =>
        simp [optionBoolValues, List.mem_finRange]

end MachineHistoryNonterminal

namespace MachineDescriptionHistoryGrammar

abbrev NT (D : MachineDescription) := MachineHistoryNonterminal D

def nt {D : MachineDescription} (A : NT D) :
    Symbol Bool (NT D) :=
  Symbol.nonterminal A

def tm {D : MachineDescription} (b : Bool) :
    Symbol Bool (NT D) :=
  Symbol.terminal b

def cell {D : MachineDescription} (c : Option Bool) :
    Symbol Bool (NT D) :=
  nt (MachineHistoryNonterminal.cell c)

def state {D : MachineDescription} (q : Fin (D.stateCount + 1)) :
    Symbol Bool (NT D) :=
  nt (MachineHistoryNonterminal.state q)

def lockedState {D : MachineDescription} (q : Fin (D.stateCount + 1)) :
    Symbol Bool (NT D) :=
  nt (MachineHistoryNonterminal.lockedState q)

def leftBoundary {D : MachineDescription} : Symbol Bool (NT D) :=
  nt MachineHistoryNonterminal.leftBoundary

def rightBoundary {D : MachineDescription} : Symbol Bool (NT D) :=
  nt MachineHistoryNonterminal.rightBoundary

def prod {D : MachineDescription}
    (lhs rhs : SententialForm Bool (NT D)) :
    GeneralGrammar.Production Bool (NT D) where
  lhs := lhs
  rhs := rhs

def startProduction (D : MachineDescription) :
    GeneralGrammar.Production Bool (NT D) :=
  prod
    [nt MachineHistoryNonterminal.start]
    [leftBoundary,
      nt MachineHistoryNonterminal.genLeft,
      lockedState (D.stateOfNat D.halt),
      rightBoundary]

def leftGeneratorProductions (D : MachineDescription) :
    List (GeneralGrammar.Production Bool (NT D)) :=
  MachineHistoryNonterminal.optionBoolValues.map
      (fun c =>
        prod
          [nt MachineHistoryNonterminal.genLeft]
          [cell c, nt MachineHistoryNonterminal.genLeft])

def headGeneratorProductions (D : MachineDescription) :
    List (GeneralGrammar.Production Bool (NT D)) :=
  MachineHistoryNonterminal.optionBoolValues.map
    (fun c =>
      prod [nt MachineHistoryNonterminal.genHead] [cell c])

def headSelectionProductions (D : MachineDescription) :
    List (GeneralGrammar.Production Bool (NT D)) :=
  (List.finRange (D.stateCount + 1)).flatMap
    (fun q =>
      MachineHistoryNonterminal.optionBoolValues.map
        (fun h =>
          prod
            [nt MachineHistoryNonterminal.genLeft, lockedState q]
            [lockedState q, cell h, nt MachineHistoryNonterminal.genRight]))

def rightGeneratorProductions (D : MachineDescription) :
    List (GeneralGrammar.Production Bool (NT D)) :=
  MachineHistoryNonterminal.optionBoolValues.map
      (fun c =>
        prod
          [nt MachineHistoryNonterminal.genRight]
          [nt MachineHistoryNonterminal.genRight, cell c])

def activationProductions (D : MachineDescription) :
    List (GeneralGrammar.Production Bool (NT D)) :=
  (List.finRange (D.stateCount + 1)).flatMap
    (fun q =>
      MachineHistoryNonterminal.optionBoolValues.map
        (fun h =>
          prod
            [lockedState q, cell h, nt MachineHistoryNonterminal.genRight]
            [state q, cell h]))

def reverseRightMoveProductions (D : MachineDescription)
    (t : TransitionDescription) :
    List (GeneralGrammar.Production Bool (NT D)) :=
  MachineHistoryNonterminal.optionBoolValues.map
      (fun d =>
        prod
          [cell t.write, state (D.stateOfNat t.target), cell d]
          [state (D.stateOfNat t.source), cell t.read, cell d]) ++
    [prod
      [cell t.write, state (D.stateOfNat t.target), cell none,
        rightBoundary]
      [state (D.stateOfNat t.source), cell t.read, rightBoundary]]

def reverseLeftMoveProductions (D : MachineDescription)
    (t : TransitionDescription) :
    List (GeneralGrammar.Production Bool (NT D)) :=
  MachineHistoryNonterminal.optionBoolValues.map
      (fun l =>
        prod
          [state (D.stateOfNat t.target), cell l, cell t.write]
          [cell l, state (D.stateOfNat t.source), cell t.read]) ++
    [prod
      [leftBoundary, state (D.stateOfNat t.target), cell none,
        cell t.write]
      [leftBoundary, state (D.stateOfNat t.source), cell t.read]]

def reverseStepProductions (D : MachineDescription)
    (t : TransitionDescription) :
    List (GeneralGrammar.Production Bool (NT D)) :=
  match t.move with
  | Direction.right => reverseRightMoveProductions D t
  | Direction.left => reverseLeftMoveProductions D t

def cleanupProductions (D : MachineDescription) :
    List (GeneralGrammar.Production Bool (NT D)) :=
  [ prod
      [leftBoundary, state (D.stateOfNat D.start), cell none,
        rightBoundary]
      []
  , prod
      [leftBoundary, state (D.stateOfNat D.start), cell (some false)]
      [tm false, nt MachineHistoryNonterminal.cleanup]
  , prod
      [leftBoundary, state (D.stateOfNat D.start), cell (some true)]
      [tm true, nt MachineHistoryNonterminal.cleanup]
  , prod
      [nt MachineHistoryNonterminal.cleanup, cell (some false)]
      [tm false, nt MachineHistoryNonterminal.cleanup]
  , prod
      [nt MachineHistoryNonterminal.cleanup, cell (some true)]
      [tm true, nt MachineHistoryNonterminal.cleanup]
  , prod
      [nt MachineHistoryNonterminal.cleanup, rightBoundary]
      []
  ]

def productions (D : MachineDescription) :
    List (GeneralGrammar.Production Bool (NT D)) :=
    [startProduction D] ++
    leftGeneratorProductions D ++
    headSelectionProductions D ++
    rightGeneratorProductions D ++
    activationProductions D ++
    D.transitions.flatMap (reverseStepProductions D) ++
    cleanupProductions D

def grammar (D : MachineDescription) :
    GeneralGrammar Bool (NT D) where
  start := MachineHistoryNonterminal.start
  produces := GeneralGrammar.ProductionListProduces (productions D)
  lhsContainsNonterminal := by
    intro lhs rhs h
    rcases h with ⟨rule, hrule, hlhs, _hrhs⟩
    rw [← hlhs]
    simp [productions, startProduction, leftGeneratorProductions,
      headSelectionProductions, rightGeneratorProductions,
      activationProductions,
      reverseStepProductions, reverseRightMoveProductions,
      reverseLeftMoveProductions, cleanupProductions, prod,
      MachineHistoryNonterminal.optionBoolValues] at hrule ⊢
    rcases hrule with h | h | h | h | hselection | h | h | h |
      hactivation | htrans | h | h | h | h | h | h
    · cases h
      exact trivial
    · cases h
      exact trivial
    · cases h
      exact trivial
    · cases h
      exact trivial
    · rcases hselection with ⟨q, hmem⟩
      rcases hmem with h | h | h
      · cases h
        exact trivial
      · cases h
        exact trivial
      · cases h
        exact trivial
    · cases h
      exact trivial
    · cases h
      exact trivial
    · cases h
      exact trivial
    · rcases hactivation with ⟨q, hmem⟩
      rcases hmem with h | h | h
      · cases h
        exact trivial
      · cases h
        exact trivial
      · cases h
        exact trivial
    · rcases htrans with ⟨t, _ht, hmem⟩
      cases hmove : t.move <;> simp [hmove] at hmem
      · rcases hmem with h | h | h | h
        · cases h
          exact trivial
        · cases h
          exact trivial
        · cases h
          exact trivial
        · cases h
          exact trivial
      · rcases hmem with h | h | h | h
        · cases h
          exact trivial
        · cases h
          exact trivial
        · cases h
          exact trivial
        · cases h
          exact trivial
    · cases h
      exact trivial
    · cases h
      exact trivial
    · cases h
      exact trivial
    · cases h
      exact trivial
    · cases h
      exact trivial
    · cases h
      exact trivial
  nonterminalsFinite := MachineHistoryNonterminal.finite D

theorem hasFiniteProductions (D : MachineDescription) :
    GeneralGrammar.HasFiniteProductions (grammar D) := by
  exists productions D
  intro lhs rhs
  rfl

def configForm (D : MachineDescription)
    (c : MachineDescription.Configuration) :
    SententialForm Bool (NT D) :=
  [leftBoundary] ++
    c.tape.left.reverse.map cell ++
    [state (D.stateOfNat c.state), cell c.tape.head] ++
    c.tape.right.map cell ++
    [rightBoundary]

def cellForm {D : MachineDescription} (xs : List (Option Bool)) :
    SententialForm Bool (NT D) :=
  xs.map cell

theorem production_derives_context {D : MachineDescription}
    {rule : GeneralGrammar.Production Bool (NT D)}
    (hrule : rule ∈ productions D)
    (pre suf : SententialForm Bool (NT D)) :
    GeneralGrammar.Derives (grammar D)
      (pre ++ rule.lhs ++ suf)
      (pre ++ rule.rhs ++ suf) := by
  apply GeneralGrammar.yields_derives
  exact ⟨pre, suf, rule.lhs, rule.rhs,
    ⟨rule, hrule, rfl, rfl⟩, rfl, rfl⟩

theorem startProduction_mem (D : MachineDescription) :
    startProduction D ∈ productions D := by
  simp [productions]

theorem leftGeneratorCell_mem (D : MachineDescription)
    (c : Option Bool) :
    prod
      [nt MachineHistoryNonterminal.genLeft]
      [cell c, nt MachineHistoryNonterminal.genLeft] ∈
        productions D := by
  cases c with
  | none =>
      simp [productions, leftGeneratorProductions,
        MachineHistoryNonterminal.optionBoolValues]
  | some b =>
      cases b <;>
        simp [productions, leftGeneratorProductions,
          MachineHistoryNonterminal.optionBoolValues]

theorem headSelection_mem (D : MachineDescription)
    (q : Fin (D.stateCount + 1)) (c : Option Bool) :
    prod
      [nt MachineHistoryNonterminal.genLeft, lockedState q]
      [lockedState q, cell c, nt MachineHistoryNonterminal.genRight] ∈
        productions D := by
  simp [productions]
  refine Or.inr (Or.inr (Or.inl ?_))
  unfold headSelectionProductions
  apply List.mem_flatMap.mpr
  refine ⟨q, List.mem_finRange q, ?_⟩
  cases c with
  | none =>
      simp [MachineHistoryNonterminal.optionBoolValues]
  | some b =>
      cases b <;>
        simp [MachineHistoryNonterminal.optionBoolValues]

theorem rightGeneratorCell_mem (D : MachineDescription)
    (c : Option Bool) :
    prod
      [nt MachineHistoryNonterminal.genRight]
      [nt MachineHistoryNonterminal.genRight, cell c] ∈
        productions D := by
  cases c with
  | none =>
      simp [productions, rightGeneratorProductions,
        MachineHistoryNonterminal.optionBoolValues]
  | some b =>
      cases b <;>
        simp [productions, rightGeneratorProductions,
          MachineHistoryNonterminal.optionBoolValues]

theorem activation_mem (D : MachineDescription)
    (q : Fin (D.stateCount + 1)) (h : Option Bool) :
    prod
      [lockedState q, cell h, nt MachineHistoryNonterminal.genRight]
      [state q, cell h] ∈ productions D := by
  simp [productions]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
  unfold activationProductions
  apply List.mem_flatMap.mpr
  refine ⟨q, List.mem_finRange q, ?_⟩
  cases h with
  | none =>
      simp [MachineHistoryNonterminal.optionBoolValues]
  | some b =>
      cases b <;>
        simp [MachineHistoryNonterminal.optionBoolValues]

theorem reverseRightMoveCell_mem {D : MachineDescription}
    {t : TransitionDescription}
    (ht : t ∈ D.transitions) (hmove : t.move = Direction.right)
    (d : Option Bool) :
    prod
      [cell t.write, state (D.stateOfNat t.target), cell d]
      [state (D.stateOfNat t.source), cell t.read, cell d] ∈
        productions D := by
  simp [productions]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
  refine ⟨t, ht, ?_⟩
  cases d with
  | none =>
      simp [reverseStepProductions, reverseRightMoveProductions, hmove,
        MachineHistoryNonterminal.optionBoolValues]
  | some b =>
      cases b <;>
        simp [reverseStepProductions, reverseRightMoveProductions, hmove,
          MachineHistoryNonterminal.optionBoolValues]

theorem reverseRightMoveBoundary_mem {D : MachineDescription}
    {t : TransitionDescription}
    (ht : t ∈ D.transitions) (hmove : t.move = Direction.right) :
    prod
      [cell t.write, state (D.stateOfNat t.target), cell none,
        rightBoundary]
      [state (D.stateOfNat t.source), cell t.read, rightBoundary] ∈
        productions D := by
  simp [productions]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
  refine ⟨t, ht, ?_⟩
  simp [reverseStepProductions, reverseRightMoveProductions, hmove,
    MachineHistoryNonterminal.optionBoolValues]

theorem reverseLeftMoveCell_mem {D : MachineDescription}
    {t : TransitionDescription}
    (ht : t ∈ D.transitions) (hmove : t.move = Direction.left)
    (l : Option Bool) :
    prod
      [state (D.stateOfNat t.target), cell l, cell t.write]
      [cell l, state (D.stateOfNat t.source), cell t.read] ∈
        productions D := by
  simp [productions]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
  refine ⟨t, ht, ?_⟩
  cases l with
  | none =>
      simp [reverseStepProductions, reverseLeftMoveProductions, hmove,
        MachineHistoryNonterminal.optionBoolValues]
  | some b =>
      cases b <;>
        simp [reverseStepProductions, reverseLeftMoveProductions, hmove,
          MachineHistoryNonterminal.optionBoolValues]

theorem reverseLeftMoveBoundary_mem {D : MachineDescription}
    {t : TransitionDescription}
    (ht : t ∈ D.transitions) (hmove : t.move = Direction.left) :
    prod
      [leftBoundary, state (D.stateOfNat t.target), cell none,
        cell t.write]
      [leftBoundary, state (D.stateOfNat t.source), cell t.read] ∈
        productions D := by
  simp [productions]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
  refine ⟨t, ht, ?_⟩
  simp [reverseStepProductions, reverseLeftMoveProductions, hmove,
    MachineHistoryNonterminal.optionBoolValues]

theorem cleanupEmpty_mem (D : MachineDescription) :
    prod
      [leftBoundary, state (D.stateOfNat D.start), cell none,
        rightBoundary]
      [] ∈ productions D := by
  simp [productions, cleanupProductions]

theorem cleanupStart_mem (D : MachineDescription) (b : Bool) :
    prod
      [leftBoundary, state (D.stateOfNat D.start), cell (some b)]
      [tm b, nt MachineHistoryNonterminal.cleanup] ∈
        productions D := by
  cases b <;> simp [productions, cleanupProductions]

theorem cleanupCell_mem (D : MachineDescription) (b : Bool) :
    prod
      [nt MachineHistoryNonterminal.cleanup, cell (some b)]
      [tm b, nt MachineHistoryNonterminal.cleanup] ∈
        productions D := by
  cases b <;> simp [productions, cleanupProductions]

theorem cleanupEnd_mem (D : MachineDescription) :
    prod
      [nt MachineHistoryNonterminal.cleanup, rightBoundary]
      [] ∈ productions D := by
  simp [productions, cleanupProductions]

theorem lookupTransition_matches {D : MachineDescription}
    {source : Nat} {read : Option Bool} {t : TransitionDescription}
    (h : D.lookupTransition source read = some t) :
    t.source = source ∧ t.read = read := by
  unfold MachineDescription.lookupTransition at h
  let p := MachineDescription.Matches source read
  have hmatches :
      forall l : List TransitionDescription,
        l.find? p = some t -> p t = true := by
    intro l
    induction l with
    | nil =>
        intro hnil
        simp at hnil
    | cons a rest ih =>
        intro hfind
        rw [List.find?_cons] at hfind
        cases hm : p a
        · simp [hm] at hfind
          exact ih hfind
        · simp [hm] at hfind
          cases hfind
          exact hm
  have ht : MachineDescription.Matches source read t = true :=
    hmatches D.transitions h
  simp [MachineDescription.Matches] at ht
  exact ⟨ht.left, ht.right⟩

theorem lookupTransition_exists_of_mem_matches
    {D : MachineDescription} {source : Nat} {read : Option Bool}
    {t : TransitionDescription}
    (ht : t ∈ D.transitions)
    (hsource : t.source = source) (hread : t.read = read) :
    exists u : TransitionDescription,
      D.lookupTransition source read = some u ∧
        u ∈ D.transitions ∧ u.source = source ∧ u.read = read := by
  unfold MachineDescription.lookupTransition
  let p := MachineDescription.Matches source read
  have hmatch : p t = true := by
    simp [p, MachineDescription.Matches, hsource, hread]
  have hfind :
      forall l : List TransitionDescription,
        t ∈ l ->
          exists u : TransitionDescription,
            l.find? p = some u ∧ u ∈ l ∧ p u = true := by
    intro l
    induction l with
    | nil =>
        intro hnil
        simp at hnil
    | cons a rest ih =>
        intro hmem
        rw [List.find?_cons]
        cases hp : p a
        · simp at hmem ⊢
          rcases hmem with hhead | htail
          · subst a
            simp [hmatch] at hp
          · rcases ih htail with ⟨u, hfind, humem, humatch⟩
            exact ⟨u, hfind, Or.inr humem, humatch⟩
        · simp [hp]
  rcases hfind D.transitions ht with ⟨u, hlookup, humem, humatch⟩
  have hkeys : u.source = source ∧ u.read = read := by
    simp [p, MachineDescription.Matches] at humatch
    exact ⟨humatch.left, humatch.right⟩
  exact ⟨u, hlookup, humem, hkeys.left, hkeys.right⟩

theorem lookupTransition_action_of_mem_matches
    {D : MachineDescription} (hD : D.WellFormed)
    {source : Nat} {read : Option Bool} {t : TransitionDescription}
    (ht : t ∈ D.transitions)
    (hsource : t.source = source) (hread : t.read = read) :
    exists u : TransitionDescription,
      D.lookupTransition source read = some u ∧
        u.write = t.write ∧ u.move = t.move ∧ u.target = t.target := by
  rcases lookupTransition_exists_of_mem_matches
    (D := D) (source := source) (read := read)
    ht hsource hread with
    ⟨u, hlookup, humem, husource, huread⟩
  have hsameKey : TransitionDescription.SameKey u t := by
    constructor
    · exact husource.trans hsource.symm
    · exact huread.trans hread.symm
  have haction :=
    hD.right.right.right.right u t humem ht hsameKey
  exact ⟨u, hlookup, haction.left, haction.right.left,
    haction.right.right⟩

theorem stateOfNat_injective_of_lt {D : MachineDescription}
    {a b : Nat}
    (ha : a < D.stateCount + 1) (hb : b < D.stateCount + 1)
    (h : D.stateOfNat a = D.stateOfNat b) :
    a = b := by
  have hval := congrArg Fin.val h
  simpa [MachineDescription.stateOfNat_val_of_lt ha,
    MachineDescription.stateOfNat_val_of_lt hb] using hval

theorem stateOfNat_injective_of_state_bound
    {D : MachineDescription}
    {a b : Nat}
    (ha : a < D.stateCount) (hb : b < D.stateCount)
    (h : D.stateOfNat a = D.stateOfNat b) :
    a = b :=
  stateOfNat_injective_of_lt
    (D := D)
    (Nat.lt_trans ha (Nat.lt_succ_self D.stateCount))
    (Nat.lt_trans hb (Nat.lt_succ_self D.stateCount))
    h

def ReachesHalt (D : MachineDescription)
    (c : MachineDescription.Configuration) : Prop :=
  exists n : Nat, (D.runConfig n c).state = D.halt

theorem reachesHalt_of_state_halt {D : MachineDescription}
    {c : MachineDescription.Configuration}
    (h : c.state = D.halt) :
    ReachesHalt D c :=
  ⟨0, h⟩

theorem reachesHalt_step {D : MachineDescription}
    {c d : MachineDescription.Configuration}
    (hstep : D.stepConfig c = some d)
    (hd : ReachesHalt D d) :
    ReachesHalt D c := by
  rcases hd with ⟨n, hn⟩
  exact ⟨n + 1, by simpa [MachineDescription.runConfig, hstep] using hn⟩

theorem haltsOnInput_of_initial_reachesHalt
    {D : MachineDescription} {w : Word Bool}
    (h : ReachesHalt D (D.initial w)) :
    D.HaltsOnInput w :=
  h

def lockedLeftForm (D : MachineDescription)
    (left : List (Option Bool)) :
    SententialForm Bool (NT D) :=
  [leftBoundary] ++ cellForm left ++
    [nt MachineHistoryNonterminal.genLeft,
      lockedState (D.stateOfNat D.halt), rightBoundary]

def lockedRightForm (D : MachineDescription)
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) :
    SententialForm Bool (NT D) :=
  [leftBoundary] ++ cellForm left ++
    [lockedState (D.stateOfNat D.halt), cell head,
      nt MachineHistoryNonterminal.genRight] ++
    cellForm right ++ [rightBoundary]

def inputCellForm {D : MachineDescription} (w : Word Bool) :
    SententialForm Bool (NT D) :=
  w.map (fun b => cell (some b))

def cleanupForm {D : MachineDescription}
    (pref : Word Bool) (rest : List (Option Bool)) :
    SententialForm Bool (NT D) :=
  SententialForm.terminalWord pref ++
    [nt MachineHistoryNonterminal.cleanup] ++
    cellForm rest ++ [rightBoundary]

inductive HistorySoundForm (D : MachineDescription) :
    SententialForm Bool (NT D) -> Prop where
  | start :
      HistorySoundForm D [nt MachineHistoryNonterminal.start]
  | lockedLeft (left : List (Option Bool)) :
      HistorySoundForm D (lockedLeftForm D left)
  | lockedRight
      (left : List (Option Bool)) (head : Option Bool)
      (right : List (Option Bool)) :
      HistorySoundForm D (lockedRightForm D left head right)
  | active (c : MachineDescription.Configuration)
      (hstate : c.state < D.stateCount)
      (hc : ReachesHalt D c) :
      HistorySoundForm D (configForm D c)
  | cleanup (pref : Word Bool) (rest : List (Option Bool))
      (h : forall suffix : Word Bool,
        rest = suffix.map some ->
          D.HaltsOnInput (Word.Concat pref suffix)) :
      HistorySoundForm D (cleanupForm (D := D) pref rest)
  | terminal (w : Word Bool)
      (h : D.HaltsOnInput w) :
      HistorySoundForm D (SententialForm.terminalWord w)

theorem nonterminal_not_mem_terminalWord {D : MachineDescription}
    (A : NT D) (w : Word Bool) :
    Symbol.nonterminal A ∉ SententialForm.terminalWord w := by
  induction w with
  | nil =>
      simp [SententialForm.terminalWord]
  | cons _ _ ih =>
      simp [SententialForm.terminalWord]

theorem containsNonterminal_ne_nil {D : MachineDescription}
    {xs : SententialForm Bool (NT D)}
    (h : SententialForm.containsNonterminal xs) :
    xs ≠ [] := by
  cases xs with
  | nil =>
      simp [SententialForm.containsNonterminal] at h
  | cons _ _ =>
      simp

theorem singleton_context_eq_of_containsNonterminal
    {D : MachineDescription} {s : Symbol Bool (NT D)}
    {u lhs v : SententialForm Bool (NT D)}
    (hcontains : SententialForm.containsNonterminal lhs)
    (hx : [s] = u ++ lhs ++ v) :
    u = [] ∧ v = [] ∧ lhs = [s] := by
  have hne : lhs ≠ [] := containsNonterminal_ne_nil hcontains
  cases lhs with
  | nil =>
      exact False.elim (hne rfl)
  | cons a rest =>
      have hlen := congrArg List.length hx
      simp at hlen
      have huLen : u.length = 0 := by omega
      have hvLen : v.length = 0 := by omega
      have hrestLen : rest.length = 0 := by omega
      have hu : u = [] := List.eq_nil_of_length_eq_zero huLen
      have hv : v = [] := List.eq_nil_of_length_eq_zero hvLen
      have hrest : rest = [] := List.eq_nil_of_length_eq_zero hrestLen
      subst u
      subst v
      subst rest
      simp at hx
      cases hx
      exact ⟨rfl, rfl, rfl⟩

theorem containsNonterminal_exists_mem {D : MachineDescription}
    {xs : SententialForm Bool (NT D)}
    (h : SententialForm.containsNonterminal xs) :
    exists A : NT D, Symbol.nonterminal A ∈ xs := by
  induction xs with
  | nil =>
      simp [SententialForm.containsNonterminal] at h
  | cons s rest ih =>
      cases s with
      | terminal b =>
          simp [SententialForm.containsNonterminal] at h
          rcases ih h with ⟨A, hA⟩
          exact ⟨A, by simp [hA]⟩
      | nonterminal A =>
          exact ⟨A, by simp⟩

theorem historySoundForm_terminal {D : MachineDescription}
    {sf : SententialForm Bool (NT D)} {w : Word Bool}
    (hshape : HistorySoundForm D sf)
    (hsf : sf = SententialForm.terminalWord w) :
    D.HaltsOnInput w := by
  induction hshape with
  | start =>
      have hmem :
          Symbol.nonterminal MachineHistoryNonterminal.start ∈
            SententialForm.terminalWord (nt := NT D) w := by
        rw [← hsf]
        simp [nt]
      exact False.elim (nonterminal_not_mem_terminalWord _ w hmem)
  | lockedLeft left =>
      have hmem :
          Symbol.nonterminal MachineHistoryNonterminal.leftBoundary ∈
            SententialForm.terminalWord (nt := NT D) w := by
        rw [← hsf]
        simp [lockedLeftForm, leftBoundary, nt]
      exact False.elim (nonterminal_not_mem_terminalWord _ w hmem)
  | lockedRight left head right =>
      have hmem :
          Symbol.nonterminal MachineHistoryNonterminal.leftBoundary ∈
            SententialForm.terminalWord (nt := NT D) w := by
        rw [← hsf]
        simp [lockedRightForm, leftBoundary, nt]
      exact False.elim (nonterminal_not_mem_terminalWord _ w hmem)
  | active c hstate hc =>
      have hmem :
          Symbol.nonterminal MachineHistoryNonterminal.leftBoundary ∈
            SententialForm.terminalWord (nt := NT D) w := by
        rw [← hsf]
        simp [configForm, leftBoundary, nt]
      exact False.elim (nonterminal_not_mem_terminalWord _ w hmem)
  | cleanup pref rest hclean =>
      have hmem :
          Symbol.nonterminal MachineHistoryNonterminal.cleanup ∈
            SententialForm.terminalWord (nt := NT D) w := by
        rw [← hsf]
        simp [cleanupForm, nt]
      exact False.elim (nonterminal_not_mem_terminalWord _ w hmem)
  | terminal w0 h =>
      have hword := congrArg SententialForm.toWord? hsf
      simp [SententialForm.terminalWord_toWord] at hword
      cases hword
      exact h

theorem historySoundForm_start_yields {D : MachineDescription}
    {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D)
      [nt MachineHistoryNonterminal.start] y) :
    HistorySoundForm D y := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  have hcontains := (grammar D).lhsContainsNonterminal lhs rhs hprod
  rcases singleton_context_eq_of_containsNonterminal hcontains hx with
    ⟨hu, hv, hlhs⟩
  subst u
  subst v
  subst lhs
  rcases hprod with ⟨rule, hrule, hlhsRule, hrhsRule⟩
  simp at hy
  subst y
  rw [← hrhsRule]
  simp [productions, startProduction, leftGeneratorProductions,
    headSelectionProductions, rightGeneratorProductions,
    activationProductions, reverseStepProductions,
    reverseRightMoveProductions, reverseLeftMoveProductions,
    cleanupProductions, prod,
    MachineHistoryNonterminal.optionBoolValues] at hrule
  rcases hrule with h | h | h | h | hselection | h | h | h |
    hactivation | htrans | h | h | h | h | h | h
  · subst rule
    simp
    exact HistorySoundForm.lockedLeft []
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · rcases hselection with ⟨q, hq | hq | hq⟩ <;>
      subst rule <;> simp at hlhsRule
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · subst rule
    simp at hlhsRule
    cases hlhsRule
  · rcases hactivation with ⟨q, hq | hq | hq⟩ <;>
      subst rule <;> simp at hlhsRule
  · rcases htrans with ⟨t, ht, hmem⟩
    cases hmove : t.move <;> simp [hmove] at hmem
    all_goals
      rcases hmem with hmem | hmem | hmem | hmem <;>
        subst rule <;> simp at hlhsRule
  · subst rule
    simp at hlhsRule
  · subst rule
    simp at hlhsRule
  · subst rule
    simp at hlhsRule
  · subst rule
    simp at hlhsRule
  · subst rule
    simp at hlhsRule
  · subst rule
    simp at hlhsRule

theorem genLeft_not_mem_cellForm {D : MachineDescription}
    (xs : List (Option Bool)) :
    nt MachineHistoryNonterminal.genLeft ∉ cellForm (D := D) xs := by
  induction xs with
  | nil =>
      simp [cellForm]
  | cons x xs ih =>
      cases x <;> simp [cellForm, cell, nt]

theorem genLeft_not_mem_tail {D : MachineDescription} :
    nt MachineHistoryNonterminal.genLeft ∉
      ([lockedState (D.stateOfNat D.halt), rightBoundary] :
        SententialForm Bool (NT D)) := by
  simp [nt, lockedState, rightBoundary]

theorem genLeft_cellForm_context {D : MachineDescription}
    (left : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : cellForm (D := D) left ++
        [nt MachineHistoryNonterminal.genLeft,
          lockedState (D.stateOfNat D.halt), rightBoundary] =
      u ++ [nt MachineHistoryNonterminal.genLeft] ++ v) :
    u = cellForm (D := D) left ∧
      v = [lockedState (D.stateOfNat D.halt), rightBoundary] := by
  induction left generalizing u with
  | nil =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          exact ⟨rfl, hx.symm⟩
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have hmem : nt MachineHistoryNonterminal.genLeft ∈
              ([lockedState (D.stateOfNat D.halt), rightBoundary] :
                SententialForm Bool (NT D)) := by
            rw [htail]
            simp
          exact False.elim (genLeft_not_mem_tail hmem)
  | cons x xs ih =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          rcases hx with ⟨hbad, _⟩
          cases x <;> simp [cell, nt] at hbad
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have htailForm :
              cellForm (D := D) xs ++
                  [nt MachineHistoryNonterminal.genLeft,
                    lockedState (D.stateOfNat D.halt), rightBoundary] =
                us ++ [nt MachineHistoryNonterminal.genLeft] ++ v := by
            simpa [cellForm] using htail
          rcases ih htailForm with ⟨hus, hv⟩
          rw [hus, hv]
          exact ⟨rfl, rfl⟩

theorem genLeft_lockedLeft_context {D : MachineDescription}
    (left : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : lockedLeftForm D left =
      u ++ [nt MachineHistoryNonterminal.genLeft] ++ v) :
    u = [leftBoundary] ++ cellForm (D := D) left ∧
      v = [lockedState (D.stateOfNat D.halt), rightBoundary] := by
  cases u with
  | nil =>
      simp [lockedLeftForm, leftBoundary, nt] at hx
  | cons a us =>
      simp [lockedLeftForm] at hx
      rcases hx with ⟨ha, htail⟩
      subst a
      have htailForm :
          cellForm (D := D) left ++
              [nt MachineHistoryNonterminal.genLeft,
                lockedState (D.stateOfNat D.halt), rightBoundary] =
            us ++ [nt MachineHistoryNonterminal.genLeft] ++ v := by
        simpa [lockedLeftForm] using htail
      rcases genLeft_cellForm_context left htailForm with ⟨hus, hv⟩
      subst us
      subst v
      simp

theorem genLeft_lockedLeft_pair_context {D : MachineDescription}
    (left : List (Option Bool)) (q : Fin (D.stateCount + 1))
    {u v : SententialForm Bool (NT D)}
    (hx : lockedLeftForm D left =
      u ++ [nt MachineHistoryNonterminal.genLeft, lockedState q] ++ v) :
    u = [leftBoundary] ++ cellForm (D := D) left ∧
      q = D.stateOfNat D.halt ∧ v = [rightBoundary] := by
  have hxSingle :
      lockedLeftForm D left =
        u ++ [nt MachineHistoryNonterminal.genLeft] ++
          (lockedState q :: v) := by
    simpa [List.append_assoc] using hx
  rcases genLeft_lockedLeft_context left hxSingle with ⟨hu, hv⟩
  subst u
  simp at hv
  rcases hv with ⟨hq, hv⟩
  cases hq
  exact ⟨rfl, rfl, hv⟩

theorem genRight_not_mem_cellForm {D : MachineDescription}
    (xs : List (Option Bool)) :
    nt MachineHistoryNonterminal.genRight ∉ cellForm (D := D) xs := by
  induction xs with
  | nil =>
      simp [cellForm]
  | cons x xs ih =>
      cases x <;> simp [cellForm, cell, nt]

theorem genRight_not_mem_tail {D : MachineDescription} :
    nt MachineHistoryNonterminal.genRight ∉
      ([rightBoundary] : SententialForm Bool (NT D)) := by
  simp [nt, rightBoundary]

theorem genRight_cellForm_context {D : MachineDescription}
    (right : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : cellForm (D := D) right ++ [rightBoundary] =
      u ++ [nt MachineHistoryNonterminal.genRight] ++ v) :
    False := by
  induction right generalizing u with
  | nil =>
      simp [cellForm] at hx
      cases u with
      | nil =>
          simp [rightBoundary, nt] at hx
      | cons a us =>
          simp at hx
  | cons x xs ih =>
      simp [cellForm] at hx
      cases u with
      | nil =>
          simp at hx
          rcases hx with ⟨hbad, _⟩
          cases x <;> simp [cell, nt] at hbad
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have htailForm :
              cellForm (D := D) xs ++ [rightBoundary] =
                us ++ [nt MachineHistoryNonterminal.genRight] ++ v := by
            simpa [cellForm] using htail
          exact ih htailForm

theorem genRight_cellForm_locked_context {D : MachineDescription}
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : cellForm (D := D) left ++
        [lockedState (D.stateOfNat D.halt), cell head,
          nt MachineHistoryNonterminal.genRight] ++
        cellForm right ++ [rightBoundary] =
      u ++ [nt MachineHistoryNonterminal.genRight] ++ v) :
    u = cellForm (D := D) left ++
        [lockedState (D.stateOfNat D.halt), cell head] ∧
      v = cellForm (D := D) right ++ [rightBoundary] := by
  induction left generalizing u with
  | nil =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp [lockedState, nt] at hx
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          cases us with
          | nil =>
              simp [cell, nt] at htail
          | cons b us =>
              simp at htail
              rcases htail with ⟨hb, htail⟩
              subst b
              cases us with
              | nil =>
                  simp at htail
                  exact ⟨rfl, htail.symm⟩
              | cons c us =>
                  simp at htail
                  rcases htail with ⟨hc, htail⟩
                  subst c
                  exact False.elim
                    (genRight_cellForm_context right
                      (by simpa [cellForm] using htail))
  | cons x xs ih =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          rcases hx with ⟨hbad, _⟩
          cases x <;> simp [cell, nt] at hbad
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have htailForm :
              cellForm (D := D) xs ++
                  [lockedState (D.stateOfNat D.halt), cell head,
                    nt MachineHistoryNonterminal.genRight] ++
                  cellForm right ++ [rightBoundary] =
                us ++ [nt MachineHistoryNonterminal.genRight] ++ v := by
            simpa [cellForm, List.append_assoc] using htail
          rcases ih htailForm with ⟨hus, hv⟩
          subst us
          subst v
          simp [cellForm]

theorem genRight_lockedRight_context {D : MachineDescription}
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : lockedRightForm D left head right =
      u ++ [nt MachineHistoryNonterminal.genRight] ++ v) :
    u = [leftBoundary] ++ cellForm (D := D) left ++
        [lockedState (D.stateOfNat D.halt), cell head] ∧
      v = cellForm (D := D) right ++ [rightBoundary] := by
  cases u with
  | nil =>
      simp [lockedRightForm, leftBoundary, nt] at hx
  | cons a us =>
      simp [lockedRightForm] at hx
      rcases hx with ⟨ha, htail⟩
      subst a
      have htailForm :
          cellForm (D := D) left ++
              [lockedState (D.stateOfNat D.halt), cell head,
                nt MachineHistoryNonterminal.genRight] ++
              cellForm right ++ [rightBoundary] =
            us ++ [nt MachineHistoryNonterminal.genRight] ++ v := by
        simpa [lockedRightForm, List.append_assoc] using htail
      rcases genRight_cellForm_locked_context left head right htailForm with
        ⟨hus, hv⟩
      subst us
      subst v
      simp [cellForm]

theorem genRight_lockedRight_triple_context {D : MachineDescription}
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (q : Fin (D.stateCount + 1))
    (h : Option Bool)
    {u v : SententialForm Bool (NT D)}
    (hx : lockedRightForm D left head right =
      u ++ [lockedState q, cell h, nt MachineHistoryNonterminal.genRight] ++
        v) :
    u = [leftBoundary] ++ cellForm (D := D) left ∧
      q = D.stateOfNat D.halt ∧ h = head ∧
      v = cellForm (D := D) right ++ [rightBoundary] := by
  have hxSingle :
      lockedRightForm D left head right =
        (u ++ [lockedState q, cell h]) ++
          [nt MachineHistoryNonterminal.genRight] ++ v := by
    simpa using hx
  rcases genRight_lockedRight_context left head right hxSingle with
    ⟨hu, hv⟩
  have hprefix :
      u ++ [lockedState q, cell h] =
        [leftBoundary] ++ cellForm (D := D) left ++
          [lockedState (D.stateOfNat D.halt), cell head] := hu
  have hlen := congrArg List.length hprefix
  simp at hlen
  have huLen : u.length =
      ([leftBoundary] ++ cellForm (D := D) left).length := by
    simpa using hlen
  have hu :
      u = [leftBoundary] ++ cellForm (D := D) left := by
    have htakeLeft :
        (u ++ [lockedState q, cell h]).take
            ([leftBoundary] ++ cellForm (D := D) left).length = u := by
      rw [← huLen]
      simp
    have htakeRight :
        (([leftBoundary] ++ cellForm (D := D) left) ++
            [lockedState (D.stateOfNat D.halt), cell head]).take
            ([leftBoundary] ++ cellForm (D := D) left).length =
          [leftBoundary] ++ cellForm (D := D) left := by
      simp
    have htaken := congrArg
      (fun xs => xs.take
        ([leftBoundary] ++ cellForm (D := D) left).length) hprefix
    have htaken' :
        (u ++ [lockedState q, cell h]).take
            ([leftBoundary] ++ cellForm (D := D) left).length =
          (([leftBoundary] ++ cellForm (D := D) left) ++
              [lockedState (D.stateOfNat D.halt), cell head]).take
            ([leftBoundary] ++ cellForm (D := D) left).length := by
      simpa using htaken
    rw [← htakeLeft]
    exact htaken'.trans htakeRight
  subst u
  simp at hprefix
  rcases hprefix with ⟨hq, hh⟩
  cases hq
  cases hh
  exact ⟨rfl, rfl, rfl, hv⟩

theorem append_singleton_eq_append_singleton {α : Type}
    {u p : List α} {x y : α}
    (h : u ++ [x] = p ++ [y]) :
    u = p ∧ x = y := by
  have hlen := congrArg List.length h
  simp at hlen
  have huLen : u.length = p.length := by omega
  have hu : u = p := by
    have htakeLeft : (u ++ [x]).take p.length = u := by
      rw [← huLen]
      simp
    have htakeRight : (p ++ [y]).take p.length = p := by
      simp
    have htaken := congrArg (fun xs => xs.take p.length) h
    have htaken' : (u ++ [x]).take p.length =
        (p ++ [y]).take p.length := by
      simpa using htaken
    rw [← htakeLeft]
    exact htaken'.trans htakeRight
  subst u
  simp at h
  exact ⟨rfl, h⟩

theorem state_cellForm_context {D : MachineDescription}
    (left : List (Option Bool)) (q0 : Fin (D.stateCount + 1))
    (head : Option Bool) (right : List (Option Bool))
    {u v : SententialForm Bool (NT D)} (q : Fin (D.stateCount + 1))
    (hx : cellForm (D := D) left ++ [state q0, cell head] ++
        cellForm right ++ [rightBoundary] =
      u ++ [state q] ++ v) :
    u = cellForm (D := D) left ∧ q = q0 ∧
      v = [cell head] ++ cellForm (D := D) right ++ [rightBoundary] := by
  induction left generalizing u with
  | nil =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          rcases hx with ⟨hq, hv⟩
          cases hq
          exact ⟨rfl, rfl, hv.symm⟩
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have hmem :
              state q ∈
                cell head :: (List.map cell right ++ [rightBoundary]) := by
            rw [htail]
            simp
          simp [cell, state, nt, rightBoundary] at hmem
  | cons x xs ih =>
      simp [cellForm] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          rcases hx with ⟨hbad, _⟩
          cases x <;> simp [cell, state, nt] at hbad
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have htailForm :
              cellForm (D := D) xs ++ [state q0, cell head] ++
                  cellForm right ++ [rightBoundary] =
                us ++ [state q] ++ v := by
            simpa [cellForm, List.append_assoc] using htail
          rcases ih htailForm with ⟨hus, hq, hv⟩
          subst us
          subst q
          subst v
          simp [cellForm]

theorem state_config_context {D : MachineDescription}
    (c : MachineDescription.Configuration)
    {u v : SententialForm Bool (NT D)} (q : Fin (D.stateCount + 1))
    (hx : configForm D c = u ++ [state q] ++ v) :
    u = [leftBoundary] ++ cellForm (D := D) c.tape.left.reverse ∧
      q = D.stateOfNat c.state ∧
      v = [cell c.tape.head] ++ cellForm (D := D) c.tape.right ++
        [rightBoundary] := by
  cases u with
  | nil =>
      simp [configForm, leftBoundary, state, nt] at hx
  | cons a us =>
      simp [configForm] at hx
      rcases hx with ⟨ha, htail⟩
      subst a
      have htailForm :
          cellForm (D := D) c.tape.left.reverse ++
              [state (D.stateOfNat c.state), cell c.tape.head] ++
              cellForm c.tape.right ++ [rightBoundary] =
            us ++ [state q] ++ v := by
        simpa [configForm, cellForm, List.append_assoc] using htail
      rcases state_cellForm_context c.tape.left.reverse
          (D.stateOfNat c.state) c.tape.head c.tape.right q htailForm with
        ⟨hus, hq, hv⟩
      subst us
      subst q
      subst v
      simp [cellForm]

theorem leftBoundary_config_context {D : MachineDescription}
    (c : MachineDescription.Configuration)
    {u v : SententialForm Bool (NT D)}
    (hx : configForm D c = u ++ [leftBoundary] ++ v) :
    u = [] ∧
      v = cellForm (D := D) c.tape.left.reverse ++
        [state (D.stateOfNat c.state), cell c.tape.head] ++
        cellForm c.tape.right ++ [rightBoundary] := by
  cases u with
  | nil =>
      simp [configForm, cellForm] at hx ⊢
      exact hx.symm
  | cons a us =>
      simp [configForm] at hx
      rcases hx with ⟨ha, htail⟩
      subst a
      have hmem :
          leftBoundary ∈
            (List.map cell c.tape.left).reverse ++
              state (D.stateOfNat c.state) ::
              cell c.tape.head ::
              (List.map cell c.tape.right ++ [rightBoundary]) := by
        rw [htail]
        simp
      simp [cell, state, nt, leftBoundary, rightBoundary] at hmem

theorem lockedLeft_leftGenerator_yields {D : MachineDescription}
    (left : List (Option Bool)) (c : Option Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : lockedLeftForm D left =
      u ++ [nt MachineHistoryNonterminal.genLeft] ++ v)
    (hy : y = u ++ [cell c, nt MachineHistoryNonterminal.genLeft] ++ v) :
    HistorySoundForm D y := by
  rcases genLeft_lockedLeft_context left hx with ⟨hu, hv⟩
  subst u
  subst v
  subst y
  simpa [lockedLeftForm, cellForm, List.map_append, List.append_assoc] using
    (HistorySoundForm.lockedLeft (D := D) (left ++ [c]))

theorem lockedLeft_headSelection_yields {D : MachineDescription}
    (left : List (Option Bool)) (q : Fin (D.stateCount + 1))
    (h : Option Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : lockedLeftForm D left =
      u ++ [nt MachineHistoryNonterminal.genLeft, lockedState q] ++ v)
    (hy : y = u ++
      [lockedState q, cell h, nt MachineHistoryNonterminal.genRight] ++ v) :
    HistorySoundForm D y := by
  rcases genLeft_lockedLeft_pair_context left q hx with ⟨hu, hq, hv⟩
  subst u
  subst q
  subst v
  subst y
  simpa [lockedRightForm, cellForm, List.append_assoc] using
    (HistorySoundForm.lockedRight (D := D) left h [])

theorem lockedRight_rightGenerator_yields {D : MachineDescription}
    (left : List (Option Bool)) (head c : Option Bool)
    (right : List (Option Bool))
    {u v y : SententialForm Bool (NT D)}
    (hx : lockedRightForm D left head right =
      u ++ [nt MachineHistoryNonterminal.genRight] ++ v)
    (hy : y = u ++ [nt MachineHistoryNonterminal.genRight, cell c] ++ v) :
    HistorySoundForm D y := by
  rcases genRight_lockedRight_context left head right hx with ⟨hu, hv⟩
  subst u
  subst v
  subst y
  simpa [lockedRightForm, cellForm, List.append_assoc] using
    (HistorySoundForm.lockedRight (D := D) left head (c :: right))

theorem lockedRight_activation_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool)) (q : Fin (D.stateCount + 1))
    (h : Option Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : lockedRightForm D left head right =
      u ++ [lockedState q, cell h, nt MachineHistoryNonterminal.genRight] ++ v)
    (hy : y = u ++ [state q, cell h] ++ v) :
    HistorySoundForm D y := by
  rcases genRight_lockedRight_triple_context left head right q h hx with
    ⟨hu, hq, hh, hv⟩
  subst u
  subst q
  subst h
  subst v
  subst y
  let c : MachineDescription.Configuration :=
    { state := D.halt
      tape := { left := left.reverse, head := head, right := right } }
  have hstate : c.state < D.stateCount := hD.right.right.left
  have hc : ReachesHalt D c := reachesHalt_of_state_halt (D := D) rfl
  simpa [configForm, lockedRightForm, cellForm, c, List.map_reverse,
    List.reverse_reverse, List.append_assoc] using
    (HistorySoundForm.active (D := D) c hstate hc)

theorem historySoundForm_lockedLeft_yields {D : MachineDescription}
    (left : List (Option Bool))
    {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D) (lockedLeftForm D left) y) :
    HistorySoundForm D y := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  rcases hprod with ⟨rule, hrule, hlhsRule, hrhsRule⟩
  simp at hy
  subst y
  rw [← hrhsRule]
  rw [← hlhsRule] at hx
  simp [productions, startProduction, leftGeneratorProductions,
    headSelectionProductions, rightGeneratorProductions,
    activationProductions, reverseStepProductions,
    reverseRightMoveProductions, reverseLeftMoveProductions,
    cleanupProductions, prod,
    MachineHistoryNonterminal.optionBoolValues] at hrule
  rcases hrule with h | h | h | h | hselection | h | h | h |
    hactivation | htrans | h | h | h | h | h | h
  · subst rule
    have hmem : nt MachineHistoryNonterminal.start ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    simpa [prod] using
      lockedLeft_leftGenerator_yields (D := D) left none hx rfl
  · subst rule
    simpa [prod] using
      lockedLeft_leftGenerator_yields (D := D) left (some false) hx rfl
  · subst rule
    simpa [prod] using
      lockedLeft_leftGenerator_yields (D := D) left (some true) hx rfl
  · rcases hselection with ⟨q, hq | hq | hq⟩
    · subst rule
      simpa [prod] using
        lockedLeft_headSelection_yields (D := D) left q none hx rfl
    · subst rule
      simpa [prod] using
        lockedLeft_headSelection_yields (D := D) left q (some false) hx rfl
    · subst rule
      simpa [prod] using
        lockedLeft_headSelection_yields (D := D) left q (some true) hx rfl
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · rcases hactivation with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem :
          nt MachineHistoryNonterminal.genRight ∈
            lockedLeftForm D left := by
        rw [hx]
        simp [nt]
      simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
        lockedState] at hmem
  · rcases htrans with ⟨t, ht, hmemRule⟩
    cases hmove : t.move <;> simp [hmove] at hmemRule
    all_goals
      rcases hmemRule with hmemRule | hmemRule | hmemRule | hmemRule <;>
        subst rule
      all_goals
        have hmem :
            state (D.stateOfNat t.target) ∈ lockedLeftForm D left := by
          rw [hx]
          simp [state, nt]
        simp [lockedLeftForm, cellForm, cell, state, nt, leftBoundary,
          rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈ lockedLeftForm D left := by
      rw [hx]
      simp [state, nt]
    simp [lockedLeftForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈ lockedLeftForm D left := by
      rw [hx]
      simp [state, nt]
    simp [lockedLeftForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈ lockedLeftForm D left := by
      rw [hx]
      simp [state, nt]
    simp [lockedLeftForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈ lockedLeftForm D left := by
      rw [hx]
      simp [nt]
    simp [lockedLeftForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem

theorem historySoundForm_lockedRight_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (left : List (Option Bool)) (head : Option Bool)
    (right : List (Option Bool))
    {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D)
      (lockedRightForm D left head right) y) :
    HistorySoundForm D y := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  rcases hprod with ⟨rule, hrule, hlhsRule, hrhsRule⟩
  simp at hy
  subst y
  rw [← hrhsRule]
  rw [← hlhsRule] at hx
  simp [productions, startProduction, leftGeneratorProductions,
    headSelectionProductions, rightGeneratorProductions,
    activationProductions, reverseStepProductions,
    reverseRightMoveProductions, reverseLeftMoveProductions,
    cleanupProductions, prod,
    MachineHistoryNonterminal.optionBoolValues] at hrule
  rcases hrule with h | h | h | h | hselection | h | h | h |
    hactivation | htrans | h | h | h | h | h | h
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.start ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · rcases hselection with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem :
          nt MachineHistoryNonterminal.genLeft ∈
            lockedRightForm D left head right := by
        rw [hx]
        simp [nt]
      simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
        lockedState] at hmem
  · subst rule
    simpa [prod] using
      lockedRight_rightGenerator_yields
        (D := D) left head none right hx rfl
  · subst rule
    simpa [prod] using
      lockedRight_rightGenerator_yields
        (D := D) left head (some false) right hx rfl
  · subst rule
    simpa [prod] using
      lockedRight_rightGenerator_yields
        (D := D) left head (some true) right hx rfl
  · rcases hactivation with ⟨q, hq | hq | hq⟩
    · subst rule
      simpa [prod] using
        lockedRight_activation_yields
          (D := D) hD left head right q none hx rfl
    · subst rule
      simpa [prod] using
        lockedRight_activation_yields
          (D := D) hD left head right q (some false) hx rfl
    · subst rule
      simpa [prod] using
        lockedRight_activation_yields
          (D := D) hD left head right q (some true) hx rfl
  · rcases htrans with ⟨t, ht, hmemRule⟩
    cases hmove : t.move <;> simp [hmove] at hmemRule
    all_goals
      rcases hmemRule with hmemRule | hmemRule | hmemRule | hmemRule <;>
        subst rule
      all_goals
        have hmem :
            state (D.stateOfNat t.target) ∈
              lockedRightForm D left head right := by
          rw [hx]
          simp [state, nt]
        simp [lockedRightForm, cellForm, cell, state, nt, leftBoundary,
          rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [state, nt]
    simp [lockedRightForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [state, nt]
    simp [lockedRightForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        state (D.stateOfNat D.start) ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [state, nt]
    simp [lockedRightForm, cellForm, cell, state, nt, leftBoundary,
      rightBoundary, lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.cleanup ∈
          lockedRightForm D left head right := by
      rw [hx]
      simp [nt]
    simp [lockedRightForm, cellForm, cell, nt, leftBoundary, rightBoundary,
      lockedState] at hmem

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

theorem cleanupEmpty_active_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (c : MachineDescription.Configuration)
    (hstate : c.state < D.stateCount) (hc : ReachesHalt D c)
    {u v y : SententialForm Bool (NT D)}
    (hx : configForm D c =
      u ++ [leftBoundary, state (D.stateOfNat D.start), cell none,
        rightBoundary] ++ v)
    (hy : y = u ++ ([] : SententialForm Bool (NT D)) ++ v) :
    HistorySoundForm D y := by
  subst y
  rcases c with ⟨qcur, T⟩
  rcases T with ⟨leftTape, headCur, rightTape⟩
  let cur : MachineDescription.Configuration :=
    { state := qcur,
      tape := { left := leftTape, head := headCur, right := rightTape } }
  have hxLB :
      configForm D cur = u ++ [leftBoundary] ++
        ([state (D.stateOfNat D.start), cell none, rightBoundary] ++ v) := by
    simpa [cur, List.append_assoc] using hx
  rcases leftBoundary_config_context cur hxLB with ⟨hu, htail⟩
  simp [cur] at hu htail
  subst u
  have hxState :
      cellForm (D := D) leftTape.reverse ++
          [state (D.stateOfNat qcur), cell headCur] ++
          cellForm rightTape ++ [rightBoundary] =
        [] ++ [state (D.stateOfNat D.start)] ++
          (cell none :: rightBoundary :: v) := by
    simpa [List.append_assoc] using htail.symm
  rcases state_cellForm_context leftTape.reverse (D.stateOfNat qcur)
      headCur rightTape (D.stateOfNat D.start) hxState with
    ⟨hleft, hq, hsuffix⟩
  have hqnat : D.start = qcur :=
    stateOfNat_injective_of_state_bound
      (D := D) hD.right.left hstate hq
  subst qcur
  cases leftTape with
  | nil =>
      simp [cellForm] at hsuffix
      rcases hsuffix with ⟨hhead, htail2⟩
      cases hhead
      cases rightTape with
      | nil =>
          simp at htail2
          subst v
          have hinitReach : ReachesHalt D (D.initial []) := by
            simpa [MachineDescription.initial, Tape.input, Tape.blank] using hc
          simpa [SententialForm.terminalWord] using
            (HistorySoundForm.terminal (D := D) []
              (haltsOnInput_of_initial_reachesHalt hinitReach))
      | cons r restRight =>
          cases r <;> simp [cell, nt, rightBoundary] at htail2
  | cons l restLeft =>
      simp [cellForm, List.map_append] at hleft

theorem cleanupStart_active_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (c : MachineDescription.Configuration)
    (hstate : c.state < D.stateCount) (hc : ReachesHalt D c)
    (b : Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : configForm D c =
      u ++ [leftBoundary, state (D.stateOfNat D.start), cell (some b)] ++ v)
    (hy : y = u ++ [tm b, nt MachineHistoryNonterminal.cleanup] ++ v) :
    HistorySoundForm D y := by
  subst y
  rcases c with ⟨qcur, T⟩
  rcases T with ⟨leftTape, headCur, rightTape⟩
  let cur : MachineDescription.Configuration :=
    { state := qcur,
      tape := { left := leftTape, head := headCur, right := rightTape } }
  have hxLB :
      configForm D cur = u ++ [leftBoundary] ++
        ([state (D.stateOfNat D.start), cell (some b)] ++ v) := by
    simpa [cur, List.append_assoc] using hx
  rcases leftBoundary_config_context cur hxLB with ⟨hu, htail⟩
  simp [cur] at hu htail
  subst u
  have hxState :
      cellForm (D := D) leftTape.reverse ++
          [state (D.stateOfNat qcur), cell headCur] ++
          cellForm rightTape ++ [rightBoundary] =
        [] ++ [state (D.stateOfNat D.start)] ++
          (cell (some b) :: v) := by
    simpa [List.append_assoc] using htail.symm
  rcases state_cellForm_context leftTape.reverse (D.stateOfNat qcur)
      headCur rightTape (D.stateOfNat D.start) hxState with
    ⟨hleft, hq, hsuffix⟩
  have hqnat : D.start = qcur :=
    stateOfNat_injective_of_state_bound
      (D := D) hD.right.left hstate hq
  subst qcur
  cases leftTape with
  | nil =>
      simp [cellForm] at hsuffix
      rcases hsuffix with ⟨hhead, hv⟩
      cases hhead
      subst v
      refine HistorySoundForm.cleanup (D := D) [b] rightTape ?_
      intro suffix hrest
      have hinitReach : ReachesHalt D (D.initial (b :: suffix)) := by
        simpa [MachineDescription.initial, Tape.input, hrest] using hc
      simpa [Word.Concat] using
        haltsOnInput_of_initial_reachesHalt hinitReach
  | cons l restLeft =>
      simp [cellForm, List.map_append] at hleft

theorem cleanup_context {D : MachineDescription}
    (pref : Word Bool) (rest : List (Option Bool))
    {u v : SententialForm Bool (NT D)}
    (hx : cleanupForm (D := D) pref rest =
      u ++ [nt MachineHistoryNonterminal.cleanup] ++ v) :
    u = SententialForm.terminalWord pref ∧
      v = cellForm (D := D) rest ++ [rightBoundary] := by
  induction pref generalizing u with
  | nil =>
      simp [cleanupForm, SententialForm.terminalWord] at hx ⊢
      cases u with
      | nil =>
          simp at hx
          exact ⟨rfl, hx.symm⟩
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have hmem :
              nt MachineHistoryNonterminal.cleanup ∈
                cellForm (D := D) rest ++ [rightBoundary] := by
            rw [htail]
            simp
          simp [cellForm, cell, nt, rightBoundary] at hmem
  | cons b pref ih =>
      simp [cleanupForm, SententialForm.terminalWord] at hx ⊢
      cases u with
      | nil =>
          simp [nt] at hx
      | cons a us =>
          simp at hx
          rcases hx with ⟨ha, htail⟩
          subst a
          have htailForm :
              SententialForm.terminalWord pref ++
                  [nt MachineHistoryNonterminal.cleanup] ++
                  cellForm rest ++ [rightBoundary] =
                us ++ [nt MachineHistoryNonterminal.cleanup] ++ v := by
            simpa [cleanupForm, SententialForm.terminalWord,
              List.append_assoc] using htail
          rcases ih htailForm with ⟨hus, hv⟩
          subst us
          subst v
          simp [SententialForm.terminalWord]

theorem cleanupCell_yields {D : MachineDescription}
    (pref : Word Bool) (rest : List (Option Bool))
    (hclean : forall suffix : Word Bool,
      rest = suffix.map some ->
        D.HaltsOnInput (Word.Concat pref suffix))
    (b : Bool)
    {u v y : SententialForm Bool (NT D)}
    (hx : cleanupForm (D := D) pref rest =
      u ++ [nt MachineHistoryNonterminal.cleanup, cell (some b)] ++ v)
    (hy : y = u ++ [tm b, nt MachineHistoryNonterminal.cleanup] ++ v) :
    HistorySoundForm D y := by
  subst y
  have hxCleanup :
      cleanupForm (D := D) pref rest =
        u ++ [nt MachineHistoryNonterminal.cleanup] ++
          (cell (some b) :: v) := by
    simpa [List.append_assoc] using hx
  rcases cleanup_context pref rest hxCleanup with ⟨hu, hv⟩
  subst u
  cases rest with
  | nil =>
      simp [cellForm, cell, nt, rightBoundary] at hv
  | cons r restTail =>
      simp [cellForm] at hv
      rcases hv with ⟨hcell, hv⟩
      cases r with
      | none =>
          simp [cell, nt] at hcell
      | some rb =>
          cases hcell
          subst v
          have hnext : HistorySoundForm D
              (cleanupForm (D := D) (Word.Concat pref [b]) restTail) := by
            refine
              HistorySoundForm.cleanup
                (D := D) (Word.Concat pref [b]) restTail ?_
            intro suffix hrest
            have horig : some b :: restTail = (b :: suffix).map some := by
              simp [hrest]
            have hh := hclean (b :: suffix) horig
            simpa [Word.Concat, List.append_assoc] using hh
          simpa [cleanupForm, SententialForm.terminalWord, Word.Concat,
            List.append_assoc] using hnext

theorem cleanupEnd_yields {D : MachineDescription}
    (pref : Word Bool) (rest : List (Option Bool))
    (hclean : forall suffix : Word Bool,
      rest = suffix.map some ->
        D.HaltsOnInput (Word.Concat pref suffix))
    {u v y : SententialForm Bool (NT D)}
    (hx : cleanupForm (D := D) pref rest =
      u ++ [nt MachineHistoryNonterminal.cleanup, rightBoundary] ++ v)
    (hy : y = u ++ ([] : SententialForm Bool (NT D)) ++ v) :
    HistorySoundForm D y := by
  subst y
  have hxCleanup :
      cleanupForm (D := D) pref rest =
        u ++ [nt MachineHistoryNonterminal.cleanup] ++
          (rightBoundary :: v) := by
    simpa [List.append_assoc] using hx
  rcases cleanup_context pref rest hxCleanup with ⟨hu, hv⟩
  subst u
  cases rest with
  | nil =>
      simp [cellForm] at hv
      subst v
      have hh := hclean [] rfl
      simpa using
        (HistorySoundForm.terminal (D := D) pref
          (by simpa [Word.Concat] using hh))
  | cons r restTail =>
      cases r <;> simp [cellForm, cell, nt, rightBoundary] at hv

theorem historySoundForm_active_yields {D : MachineDescription}
    (hD : D.WellFormed)
    (c : MachineDescription.Configuration)
    (hstate : c.state < D.stateCount) (hc : ReachesHalt D c)
    {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D) (configForm D c) y) :
    HistorySoundForm D y := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  rcases hprod with ⟨rule, hrule, hlhsRule, hrhsRule⟩
  simp at hy
  subst y
  rw [← hrhsRule]
  rw [← hlhsRule] at hx
  simp [productions, startProduction, leftGeneratorProductions,
    headSelectionProductions, rightGeneratorProductions,
    activationProductions, reverseStepProductions,
    reverseRightMoveProductions, reverseLeftMoveProductions,
    cleanupProductions, prod,
    MachineHistoryNonterminal.optionBoolValues] at hrule
  rcases hrule with h | h | h | h | hselection | h | h | h |
    hactivation | htrans | h | h | h | h | h | h
  · subst rule
    have hmem : nt MachineHistoryNonterminal.start ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genLeft ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genLeft ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genLeft ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · rcases hselection with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem : nt MachineHistoryNonterminal.genLeft ∈ configForm D c := by
        rw [hx]
        simp [nt]
      simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genRight ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genRight ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.genRight ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · rcases hactivation with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem : lockedState q ∈ configForm D c := by
        rw [hx]
        simp [lockedState, nt]
      simp [configForm, cell, state, lockedState, nt, leftBoundary,
        rightBoundary] at hmem
  · rcases htrans with ⟨t, ht, hmemRule⟩
    cases hmove : t.move <;> simp [hmove] at hmemRule
    · rcases hmemRule with hnone | hfalse | htrue | hboundary
      · subst rule
        simpa [prod] using
          reverseLeftMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove none hx rfl
      · subst rule
        simpa [prod] using
          reverseLeftMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove (some false) hx rfl
      · subst rule
        simpa [prod] using
          reverseLeftMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove (some true) hx rfl
      · subst rule
        simpa [prod] using
          reverseLeftMoveBoundary_active_yields
            (D := D) hD c hstate hc t ht hmove hx rfl
    · rcases hmemRule with hnone | hfalse | htrue | hboundary
      · subst rule
        simpa [prod] using
          reverseRightMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove none hx rfl
      · subst rule
        simpa [prod] using
          reverseRightMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove (some false) hx rfl
      · subst rule
        simpa [prod] using
          reverseRightMoveCell_active_yields
            (D := D) hD c hstate hc t ht hmove (some true) hx rfl
      · subst rule
        simpa [prod] using
          reverseRightMoveBoundary_active_yields
            (D := D) hD c hstate hc t ht hmove hx rfl
  · subst rule
    simpa [prod] using
      cleanupEmpty_active_yields (D := D) hD c hstate hc hx rfl
  · subst rule
    simpa [prod] using
      cleanupStart_active_yields (D := D) hD c hstate hc false hx rfl
  · subst rule
    simpa [prod] using
      cleanupStart_active_yields (D := D) hD c hstate hc true hx rfl
  · subst rule
    have hmem : nt MachineHistoryNonterminal.cleanup ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.cleanup ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem
  · subst rule
    have hmem : nt MachineHistoryNonterminal.cleanup ∈ configForm D c := by
      rw [hx]
      simp [nt]
    simp [configForm, cell, state, nt, leftBoundary, rightBoundary] at hmem

theorem historySoundForm_cleanup_yields {D : MachineDescription}
    (pref : Word Bool) (rest : List (Option Bool))
    (hclean : forall suffix : Word Bool,
      rest = suffix.map some ->
        D.HaltsOnInput (Word.Concat pref suffix))
    {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D)
      (cleanupForm (D := D) pref rest) y) :
    HistorySoundForm D y := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  rcases hprod with ⟨rule, hrule, hlhsRule, hrhsRule⟩
  simp at hy
  subst y
  rw [← hrhsRule]
  rw [← hlhsRule] at hx
  simp [productions, startProduction, leftGeneratorProductions,
    headSelectionProductions, rightGeneratorProductions,
    activationProductions, reverseStepProductions,
    reverseRightMoveProductions, reverseLeftMoveProductions,
    cleanupProductions, prod,
    MachineHistoryNonterminal.optionBoolValues] at hrule
  rcases hrule with h | h | h | h | hselection | h | h | h |
    hactivation | htrans | h | h | h | h | h | h
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.start ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genLeft ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · rcases hselection with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem :
          nt MachineHistoryNonterminal.genLeft ∈
            cleanupForm (D := D) pref rest := by
        rw [hx]
        simp [nt]
      simp [cleanupForm, cellForm, cell, nt, rightBoundary,
        nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem :
        nt MachineHistoryNonterminal.genRight ∈
          cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [nt]
    simp [cleanupForm, cellForm, cell, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · rcases hactivation with ⟨q, hq | hq | hq⟩ <;> subst rule
    all_goals
      have hmem :
          lockedState q ∈ cleanupForm (D := D) pref rest := by
        rw [hx]
        simp [lockedState, nt]
      simp [cleanupForm, cellForm, cell, lockedState, nt, rightBoundary,
        nonterminal_not_mem_terminalWord] at hmem
  · rcases htrans with ⟨t, ht, hmemRule⟩
    cases hmove : t.move <;> simp [hmove] at hmemRule
    all_goals
      rcases hmemRule with hmemRule | hmemRule | hmemRule | hmemRule <;>
        subst rule
      all_goals
        have hmem :
            state (D.stateOfNat t.target) ∈
              cleanupForm (D := D) pref rest := by
          rw [hx]
          simp [state, nt]
        simp [cleanupForm, cellForm, cell, state, nt, rightBoundary,
          nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem : leftBoundary ∈ cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [leftBoundary, nt]
    simp [cleanupForm, cellForm, cell, leftBoundary, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem : leftBoundary ∈ cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [leftBoundary, nt]
    simp [cleanupForm, cellForm, cell, leftBoundary, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    have hmem : leftBoundary ∈ cleanupForm (D := D) pref rest := by
      rw [hx]
      simp [leftBoundary, nt]
    simp [cleanupForm, cellForm, cell, leftBoundary, nt, rightBoundary,
      nonterminal_not_mem_terminalWord] at hmem
  · subst rule
    simpa [prod] using
      cleanupCell_yields (D := D) pref rest hclean false hx rfl
  · subst rule
    simpa [prod] using
      cleanupCell_yields (D := D) pref rest hclean true hx rfl
  · subst rule
    simpa [prod] using
      cleanupEnd_yields (D := D) pref rest hclean hx rfl

theorem terminalWord_no_yields {D : MachineDescription}
    (w : Word Bool) {y : SententialForm Bool (NT D)}
    (h : GeneralGrammar.Yields (grammar D) (SententialForm.terminalWord w) y) :
    False := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  have hcontains := (grammar D).lhsContainsNonterminal lhs rhs hprod
  rcases containsNonterminal_exists_mem (D := D) hcontains with ⟨A, hA⟩
  have hmem : Symbol.nonterminal A ∈ SententialForm.terminalWord w := by
    rw [hx]
    simp [hA]
  exact nonterminal_not_mem_terminalWord A w hmem

theorem historySoundForm_yields {D : MachineDescription}
    (hD : D.WellFormed)
    {x y : SententialForm Bool (NT D)}
    (hshape : HistorySoundForm D x)
    (h : GeneralGrammar.Yields (grammar D) x y) :
    HistorySoundForm D y := by
  cases hshape with
  | start =>
      exact historySoundForm_start_yields h
  | lockedLeft left =>
      exact historySoundForm_lockedLeft_yields left h
  | lockedRight left head right =>
      exact historySoundForm_lockedRight_yields hD left head right h
  | active c hstate hc =>
      exact historySoundForm_active_yields hD c hstate hc h
  | cleanup pref rest hclean =>
      exact historySoundForm_cleanup_yields pref rest hclean h
  | terminal w hw =>
      exact False.elim (terminalWord_no_yields w h)

theorem historySoundForm_derives {D : MachineDescription}
    (hD : D.WellFormed)
    {x y : SententialForm Bool (NT D)}
    (hshape : HistorySoundForm D x)
    (h : GeneralGrammar.Derives (grammar D) x y) :
    HistorySoundForm D y := by
  induction h with
  | refl x =>
      exact hshape
  | step hstep hrest ih =>
      exact ih (historySoundForm_yields hD hshape hstep)

theorem sound {D : MachineDescription} {w : Word Bool}
    (hD : D.WellFormed)
    (h : w ∈ GeneralGrammar.GeneratedLanguage (grammar D)) :
    D.HaltsOnInput w := by
  have hshape :
      HistorySoundForm D (SententialForm.terminalWord w) :=
    historySoundForm_derives (D := D) hD
      (HistorySoundForm.start (D := D)) h
  exact historySoundForm_terminal hshape rfl

theorem leftGenerator_derives (D : MachineDescription)
    (xs : List (Option Bool)) :
    GeneralGrammar.Derives (grammar D)
      [nt MachineHistoryNonterminal.genLeft]
      (cellForm xs ++ [nt MachineHistoryNonterminal.genLeft]) := by
  induction xs with
  | nil =>
      simpa [cellForm] using
        (GeneralGrammar.Derives.refl
          [nt MachineHistoryNonterminal.genLeft] :
          GeneralGrammar.Derives (grammar D)
            [nt MachineHistoryNonterminal.genLeft]
            [nt MachineHistoryNonterminal.genLeft])
  | cons x xs ih =>
      have hhead :
          GeneralGrammar.Derives (grammar D)
            [nt MachineHistoryNonterminal.genLeft]
            [cell x, nt MachineHistoryNonterminal.genLeft] := by
        simpa using
          production_derives_context
            (D := D) (rule :=
              prod
                [nt MachineHistoryNonterminal.genLeft]
                [cell x, nt MachineHistoryNonterminal.genLeft])
            (leftGeneratorCell_mem D x) [] []
      have htail :
          GeneralGrammar.Derives (grammar D)
            [cell x, nt MachineHistoryNonterminal.genLeft]
            (cell x :: (cellForm xs ++
              [nt MachineHistoryNonterminal.genLeft])) := by
        simpa [cellForm, List.append_assoc] using
          GeneralGrammar.derives_context
            (G := grammar D)
            [cell x] [] ih
      exact GeneralGrammar.derives_trans hhead htail

theorem rightGenerator_derives (D : MachineDescription)
    (xs : List (Option Bool)) :
    GeneralGrammar.Derives (grammar D)
      [nt MachineHistoryNonterminal.genRight]
      ([nt MachineHistoryNonterminal.genRight] ++ cellForm xs) := by
  induction xs with
  | nil =>
      simpa [cellForm] using
        (GeneralGrammar.Derives.refl
          [nt MachineHistoryNonterminal.genRight] :
          GeneralGrammar.Derives (grammar D)
            [nt MachineHistoryNonterminal.genRight]
            [nt MachineHistoryNonterminal.genRight])
  | cons x xs ih =>
      have htail :
          GeneralGrammar.Derives (grammar D)
            [nt MachineHistoryNonterminal.genRight]
            ([nt MachineHistoryNonterminal.genRight] ++ cellForm xs) :=
        ih
      have hadd :
          GeneralGrammar.Derives (grammar D)
            ([nt MachineHistoryNonterminal.genRight] ++ cellForm xs)
            ([nt MachineHistoryNonterminal.genRight, cell x] ++
              cellForm xs) := by
        simpa using
          production_derives_context
            (D := D) (rule :=
              prod
                [nt MachineHistoryNonterminal.genRight]
                [nt MachineHistoryNonterminal.genRight, cell x])
            (rightGeneratorCell_mem D x) [] (cellForm xs)
      simpa [cellForm, List.append_assoc] using
        GeneralGrammar.derives_trans htail hadd

theorem start_derives_halting_config
    (D : MachineDescription)
    (c : MachineDescription.Configuration)
    (hstate : c.state = D.halt) :
    GeneralGrammar.Derives (grammar D)
      [nt MachineHistoryNonterminal.start]
      (configForm D c) := by
  have hstart :
      GeneralGrammar.Derives (grammar D)
        [nt MachineHistoryNonterminal.start]
        [leftBoundary,
          nt MachineHistoryNonterminal.genLeft,
          lockedState (D.stateOfNat D.halt),
          rightBoundary] := by
    simpa [startProduction] using
      production_derives_context
        (D := D) (rule := startProduction D)
        (startProduction_mem D) [] []
  have hleft :
      GeneralGrammar.Derives (grammar D)
        [leftBoundary,
          nt MachineHistoryNonterminal.genLeft,
          lockedState (D.stateOfNat D.halt),
          rightBoundary]
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [nt MachineHistoryNonterminal.genLeft,
            lockedState (D.stateOfNat D.halt),
            rightBoundary]) := by
    simpa [cellForm, List.append_assoc] using
      GeneralGrammar.derives_context
        (G := grammar D)
        [leftBoundary]
        [lockedState (D.stateOfNat D.halt),
          rightBoundary]
        (leftGenerator_derives D c.tape.left.reverse)
  have hhead :
      GeneralGrammar.Derives (grammar D)
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [nt MachineHistoryNonterminal.genLeft,
            lockedState (D.stateOfNat D.halt),
            rightBoundary])
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [lockedState (D.stateOfNat D.halt), cell c.tape.head,
            nt MachineHistoryNonterminal.genRight,
            rightBoundary]) := by
    have hraw :=
      production_derives_context
        (D := D)
        (rule :=
          prod
            [nt MachineHistoryNonterminal.genLeft,
              lockedState (D.stateOfNat D.halt)]
            [lockedState (D.stateOfNat D.halt), cell c.tape.head,
              nt MachineHistoryNonterminal.genRight])
        (headSelection_mem D (D.stateOfNat D.halt) c.tape.head)
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [])
        [rightBoundary]
    have hsrc :
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [nt MachineHistoryNonterminal.genLeft,
            lockedState (D.stateOfNat D.halt),
            rightBoundary]) =
          (([leftBoundary] ++ cellForm c.tape.left.reverse ++ []) ++
            [nt MachineHistoryNonterminal.genLeft,
              lockedState (D.stateOfNat D.halt)] ++
            [rightBoundary]) := by
      simp [List.append_assoc]
    have htgt :
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [lockedState (D.stateOfNat D.halt), cell c.tape.head,
            nt MachineHistoryNonterminal.genRight,
            rightBoundary]) =
          (([leftBoundary] ++ cellForm c.tape.left.reverse ++ []) ++
            [lockedState (D.stateOfNat D.halt), cell c.tape.head,
              nt MachineHistoryNonterminal.genRight] ++
            [rightBoundary]) := by
      simp [List.append_assoc]
    rw [hsrc, htgt]
    simpa [List.append_assoc] using hraw
  have hright :
      GeneralGrammar.Derives (grammar D)
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [lockedState (D.stateOfNat D.halt), cell c.tape.head,
            nt MachineHistoryNonterminal.genRight,
            rightBoundary])
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [lockedState (D.stateOfNat D.halt), cell c.tape.head,
            nt MachineHistoryNonterminal.genRight] ++
          cellForm c.tape.right ++ [rightBoundary]) := by
    have hraw :=
      GeneralGrammar.derives_context
        (G := grammar D)
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [lockedState (D.stateOfNat D.halt), cell c.tape.head])
        [rightBoundary]
        (rightGenerator_derives D c.tape.right)
    have hsrc :
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [lockedState (D.stateOfNat D.halt), cell c.tape.head,
            nt MachineHistoryNonterminal.genRight,
            rightBoundary]) =
          (([leftBoundary] ++ cellForm c.tape.left.reverse ++
            [lockedState (D.stateOfNat D.halt), cell c.tape.head]) ++
            [nt MachineHistoryNonterminal.genRight] ++ [rightBoundary]) := by
      simp [List.append_assoc]
    have htgt :
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [lockedState (D.stateOfNat D.halt), cell c.tape.head,
            nt MachineHistoryNonterminal.genRight] ++
          cellForm c.tape.right ++ [rightBoundary]) =
          (([leftBoundary] ++ cellForm c.tape.left.reverse ++
            [lockedState (D.stateOfNat D.halt), cell c.tape.head]) ++
            [nt MachineHistoryNonterminal.genRight] ++
            cellForm c.tape.right ++ [rightBoundary]) := by
      simp [List.append_assoc]
    rw [hsrc, htgt]
    simpa [List.append_assoc] using hraw
  have hactivate :
      GeneralGrammar.Derives (grammar D)
        ([leftBoundary] ++ cellForm c.tape.left.reverse ++
          [lockedState (D.stateOfNat D.halt), cell c.tape.head,
            nt MachineHistoryNonterminal.genRight] ++
          cellForm c.tape.right ++ [rightBoundary])
        (configForm D c) := by
    have hraw :=
      production_derives_context
        (D := D)
        (rule :=
          prod
            [lockedState (D.stateOfNat D.halt), cell c.tape.head,
              nt MachineHistoryNonterminal.genRight]
            [state (D.stateOfNat D.halt), cell c.tape.head])
        (activation_mem D (D.stateOfNat D.halt) c.tape.head)
        ([leftBoundary] ++ cellForm c.tape.left.reverse)
        (cellForm c.tape.right ++ [rightBoundary])
    simpa [configForm, cellForm, hstate, List.append_assoc] using hraw
  exact GeneralGrammar.derives_trans hstart
    (GeneralGrammar.derives_trans hleft
      (GeneralGrammar.derives_trans hhead
        (GeneralGrammar.derives_trans hright hactivate)))

theorem reverse_step_derives {D : MachineDescription}
    {c d : MachineDescription.Configuration}
    (hstep : D.stepConfig c = some d) :
    GeneralGrammar.Derives (grammar D)
      (configForm D d) (configForm D c) := by
  rcases c with ⟨q, T⟩
  rcases T with ⟨left, head, right⟩
  unfold MachineDescription.stepConfig at hstep
  cases hlookup :
      D.lookupTransition q (Tape.read { left := left, head := head, right := right }) with
  | none =>
      rw [hlookup] at hstep
      cases hstep
  | some t =>
      rw [hlookup] at hstep
      have hmatches := lookupTransition_matches hlookup
      have htmem : t ∈ D.transitions :=
        MachineDescription.lookupTransition_mem hlookup
      cases hstep
      cases hmove : t.move with
      | left =>
          cases left with
          | nil =>
              have hprod :=
                production_derives_context
                  (D := D)
                  (rule :=
                    prod
                      [leftBoundary, state (D.stateOfNat t.target),
                        cell none, cell t.write]
                      [leftBoundary, state (D.stateOfNat t.source),
                        cell t.read])
                  (reverseLeftMoveBoundary_mem htmem hmove)
                  []
                  (right.map cell ++ [rightBoundary])
              simpa [configForm, Tape.move, Tape.moveLeft, Tape.write,
                hmatches.left, hmatches.right, cellForm,
                List.append_assoc] using hprod
          | cons l rest =>
              have hprod :=
                production_derives_context
                  (D := D)
                  (rule :=
                    prod
                      [state (D.stateOfNat t.target), cell l, cell t.write]
                      [cell l, state (D.stateOfNat t.source), cell t.read])
                  (reverseLeftMoveCell_mem htmem hmove l)
                  ([leftBoundary] ++ rest.reverse.map cell)
                  (right.map cell ++ [rightBoundary])
              simpa [configForm, Tape.move, Tape.moveLeft, Tape.write,
                hmatches.left, hmatches.right, List.map_append,
                List.append_assoc] using hprod
      | right =>
          cases right with
          | nil =>
              have hprod :=
                production_derives_context
                  (D := D)
                  (rule :=
                    prod
                      [cell t.write, state (D.stateOfNat t.target),
                        cell none, rightBoundary]
                      [state (D.stateOfNat t.source), cell t.read,
                        rightBoundary])
                  (reverseRightMoveBoundary_mem htmem hmove)
                  ([leftBoundary] ++ left.reverse.map cell)
                  []
              simpa [configForm, Tape.move, Tape.moveRight, Tape.write,
                hmatches.left, hmatches.right, List.map_append,
                List.append_assoc] using hprod
          | cons r rest =>
              have hprod :=
                production_derives_context
                  (D := D)
                  (rule :=
                    prod
                      [cell t.write, state (D.stateOfNat t.target), cell r]
                      [state (D.stateOfNat t.source), cell t.read, cell r])
                  (reverseRightMoveCell_mem htmem hmove r)
                  ([leftBoundary] ++ left.reverse.map cell)
                  (rest.map cell ++ [rightBoundary])
              simpa [configForm, Tape.move, Tape.moveRight, Tape.write,
                hmatches.left, hmatches.right, List.map_append,
                List.append_assoc] using hprod

theorem reverse_run_derives (D : MachineDescription)
    (n : Nat) (c : MachineDescription.Configuration) :
    GeneralGrammar.Derives (grammar D)
      (configForm D (D.runConfig n c)) (configForm D c) := by
  induction n generalizing c with
  | zero =>
      exact GeneralGrammar.Derives.refl _
  | succ n ih =>
      change
        GeneralGrammar.Derives (grammar D)
          (configForm D
            (match D.stepConfig c with
            | none => c
            | some next => D.runConfig n next))
          (configForm D c)
      cases hstep : D.stepConfig c with
      | none =>
          exact GeneralGrammar.Derives.refl _
      | some next =>
          exact GeneralGrammar.derives_trans
            (ih next)
            (reverse_step_derives hstep)

theorem cleanup_tail_derives (D : MachineDescription)
    (w : Word Bool) :
    GeneralGrammar.Derives (grammar D)
      ([nt MachineHistoryNonterminal.cleanup] ++
        inputCellForm (D := D) w ++ [rightBoundary])
      (SententialForm.terminalWord w) := by
  induction w with
  | nil =>
      simpa [inputCellForm, SententialForm.terminalWord] using
        production_derives_context
          (D := D) (rule :=
            prod [nt MachineHistoryNonterminal.cleanup, rightBoundary] [])
          (cleanupEnd_mem D) [] []
  | cons b rest ih =>
      have hfirst :
          GeneralGrammar.Derives (grammar D)
            ([nt MachineHistoryNonterminal.cleanup] ++
              inputCellForm (D := D) (b :: rest) ++ [rightBoundary])
            ([tm b, nt MachineHistoryNonterminal.cleanup] ++
              inputCellForm (D := D) rest ++ [rightBoundary]) := by
        simpa [inputCellForm, List.append_assoc] using
          production_derives_context
            (D := D) (rule :=
              prod
                [nt MachineHistoryNonterminal.cleanup, cell (some b)]
                [tm b, nt MachineHistoryNonterminal.cleanup])
            (cleanupCell_mem D b)
            []
            (inputCellForm (D := D) rest ++ [rightBoundary])
      have hrest :
          GeneralGrammar.Derives (grammar D)
            ([tm b, nt MachineHistoryNonterminal.cleanup] ++
              inputCellForm (D := D) rest ++ [rightBoundary])
            (SententialForm.terminalWord (b :: rest)) := by
        simpa [inputCellForm, SententialForm.terminalWord,
          List.append_assoc] using
          GeneralGrammar.derives_context
            (G := grammar D)
            [tm b] [] ih
      exact GeneralGrammar.derives_trans hfirst hrest

theorem cleanup_initial_derives (D : MachineDescription)
    (w : Word Bool) :
    GeneralGrammar.Derives (grammar D)
      (configForm D (D.initial w))
      (SententialForm.terminalWord w) := by
  cases w with
  | nil =>
      simpa [MachineDescription.initial, Tape.input, Tape.blank,
        configForm, SententialForm.terminalWord] using
        production_derives_context
          (D := D) (rule :=
            prod
              [leftBoundary, state (D.stateOfNat D.start), cell none,
                rightBoundary]
              [])
          (cleanupEmpty_mem D) [] []
  | cons b rest =>
      have hfirst :
          GeneralGrammar.Derives (grammar D)
            (configForm D (D.initial (b :: rest)))
            ([tm b, nt MachineHistoryNonterminal.cleanup] ++
              inputCellForm (D := D) rest ++ [rightBoundary]) := by
        simpa [MachineDescription.initial, Tape.input, configForm,
          inputCellForm, List.append_assoc] using
          production_derives_context
            (D := D) (rule :=
              prod
                [leftBoundary, state (D.stateOfNat D.start),
                  cell (some b)]
                [tm b, nt MachineHistoryNonterminal.cleanup])
            (cleanupStart_mem D b)
            []
            (inputCellForm (D := D) rest ++ [rightBoundary])
      have hrest :
          GeneralGrammar.Derives (grammar D)
            ([tm b, nt MachineHistoryNonterminal.cleanup] ++
              inputCellForm (D := D) rest ++ [rightBoundary])
            (SententialForm.terminalWord (b :: rest)) := by
        simpa [SententialForm.terminalWord, List.append_assoc] using
          GeneralGrammar.derives_context
            (G := grammar D)
            [tm b] []
            (cleanup_tail_derives D rest)
      exact GeneralGrammar.derives_trans hfirst hrest

theorem complete {D : MachineDescription} {w : Word Bool}
    (h : D.HaltsOnInput w) :
    w ∈ GeneralGrammar.GeneratedLanguage (grammar D) := by
  rcases h with ⟨n, hhalt⟩
  let final := D.runConfig n (D.initial w)
  have hstart :
      GeneralGrammar.Derives (grammar D)
        [nt MachineHistoryNonterminal.start]
        (configForm D final) :=
    start_derives_halting_config D final hhalt
  have hrun :
      GeneralGrammar.Derives (grammar D)
        (configForm D final)
        (configForm D (D.initial w)) := by
    simpa [final] using reverse_run_derives D n (D.initial w)
  exact GeneralGrammar.derives_trans hstart
    (GeneralGrammar.derives_trans hrun
      (cleanup_initial_derives D w))

theorem generated_language {D : MachineDescription}
    (hD : D.WellFormed) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage (grammar D))
      (fun w : Word Bool => D.HaltsOnInput w) := by
  intro w
  constructor
  · exact sound hD
  · exact complete

end MachineDescriptionHistoryGrammar

def MachineDescriptionToFiniteGeneralGrammarConstruction : Prop :=
  forall D : MachineDescription,
    D.WellFormed ->
    exists nonterminal : Type, exists G : GeneralGrammar Bool nonterminal,
      GeneralGrammar.HasFiniteProductions G ∧
        Language.Equal
          (GeneralGrammar.GeneratedLanguage G)
          (fun w : Word Bool => D.HaltsOnInput w)

theorem machineDescriptionToFiniteGeneralGrammarConstruction :
    MachineDescriptionToFiniteGeneralGrammarConstruction := by
  intro D hD
  exact ⟨MachineDescriptionHistoryGrammar.NT D,
    MachineDescriptionHistoryGrammar.grammar D,
    MachineDescriptionHistoryGrammar.hasFiniteProductions D,
    MachineDescriptionHistoryGrammar.generated_language hD⟩

def MachineDescriptionAcceptsToFiniteGeneralGrammarConstruction : Prop :=
  forall {D : MachineDescription}, forall {L : Language Bool},
    MachineDescriptionAcceptsLanguage D L ->
      GeneralGrammar.FiniteProductionGenerated L

def DescriptionRecognizerToFiniteGeneralGrammarConstruction : Prop :=
  MachineDescriptionAcceptsToFiniteGeneralGrammarConstruction

def BooleanRecognizerToFiniteGeneralGrammarConstruction : Prop :=
  DescriptionRecognizerToFiniteGeneralGrammarConstruction

def ProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction : Prop :=
  forall L : Language Bool,
    ProgramAcceptableByDescription L ->
      GeneralGrammar.FiniteProductionGenerated L

theorem programAcceptableByDescriptionToFiniteGeneralGrammarConstruction_of_descriptionRecognizer
    (hconstruct : DescriptionRecognizerToFiniteGeneralGrammarConstruction) :
    ProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction := by
  intro L hL
  rcases hL with ⟨P, D, hP, hD⟩
  exact hconstruct
    (programCompiledByDescription_acceptsLanguage hP hD)

theorem machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
    (hconstruct : MachineDescriptionToFiniteGeneralGrammarConstruction) :
    MachineDescriptionAcceptsToFiniteGeneralGrammarConstruction := by
  intro D L hD
  rcases hconstruct D hD.left with ⟨nonterminal, G, hG⟩
  exists nonterminal
  exists G
  exact ⟨hG.left, Language.equal_trans hG.right hD.right⟩


end Computability
end FoC
