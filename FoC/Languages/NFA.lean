import FoC.Foundation.Finite
import FoC.Languages.DFA

set_option doc.verso true

/-!
# Nondeterministic finite automata

## Epsilon transitions and reachable sets

The book's NFAs allow transitions labeled by either an input symbol or the
empty string.  We model that by using {lit}`Option alpha`, where {lit}`none` is
an epsilon transition and {lit}`some a` consumes the symbol {lit}`a`.

## Book coordinates

Used by:
- Chapter 3, Section 3.5: NFA definition, acceptance, and subset construction
- Chapter 3, Section 3.6: comparison between automata and regular languages
-/

namespace FoC
namespace Languages

open Foundation

/-!
# NFA structure

An NFA has a start state, finite state space, accepting states, and a transition
function that may consume a symbol or take an epsilon transition.
-/

structure NFA (alpha : Type u) (state : Type v) where
  start : state
  step : state -> Option alpha -> FSet state
  accept : state -> Prop
  statesFinite : FiniteType state

namespace NFA

/-!
# Epsilon closure and reachability

Reachable-state sets are built from epsilon closure, symbol moves, and the
recursive extension of the transition relation to input words.
-/

inductive EpsilonReach (M : NFA alpha state) : state -> state -> Prop where
  | refl (q : state) : EpsilonReach M q q
  | step {q r s : state} :
      r ∈ M.step q none -> EpsilonReach M r s -> EpsilonReach M q s

def EpsilonClosure (M : NFA alpha state) (S : FSet state) : FSet state :=
  fun r => exists q, q ∈ S ∧ EpsilonReach M q r

def SymbolMove (M : NFA alpha state) (S : FSet state) (a : alpha) : FSet state :=
  fun r => exists q, q ∈ S ∧ r ∈ M.step q (some a)

def Next (M : NFA alpha state) (S : FSet state) (a : alpha) : FSet state :=
  EpsilonClosure M (SymbolMove M S a)

def StartSet (M : NFA alpha state) : FSet state :=
  EpsilonClosure M (FSet.Singleton M.start)

def ReachFromSet (M : NFA alpha state) : FSet state -> Word alpha -> FSet state
  | S, [] => S
  | S, a :: w => ReachFromSet M (Next M S a) w

def Reach (M : NFA alpha state) (w : Word alpha) : FSet state :=
  ReachFromSet M (StartSet M) w

def Accepts (M : NFA alpha state) (w : Word alpha) : Prop :=
  exists q, q ∈ Reach M w ∧ M.accept q

def AcceptedLanguage (M : NFA alpha state) : FoC.Languages.Language alpha :=
  fun w => Accepts M w

def Recognizable (L : FoC.Languages.Language alpha) : Prop :=
  exists state : Type, exists M : NFA alpha state, FoC.Languages.Language.Equal (AcceptedLanguage M) L

/-!
# Subset construction

The deterministic machine whose states are sets of NFA states recognizes the
same language, provided the set-of-states type is finite.
-/

def SubsetDFA (M : NFA alpha state) (subsetsFinite : FiniteType (FSet state)) :
    DFA alpha (FSet state) where
  start := StartSet M
  step := fun S a => Next M S a
  accept := fun S => exists q, q ∈ S ∧ M.accept q
  statesFinite := subsetsFinite

theorem epsilonClosure_contains {M : NFA alpha state} {S : FSet state} {q : state}
    (hq : q ∈ S) : q ∈ EpsilonClosure M S := by
  exists q
  exact And.intro hq (EpsilonReach.refl q)

theorem subsetDFA_runFrom (M : NFA alpha state)
    (subsetsFinite : FiniteType (FSet state)) (S : FSet state) (w : Word alpha) :
    DFA.RunFrom (SubsetDFA M subsetsFinite) S w = ReachFromSet M S w := by
  induction w generalizing S with
  | nil => rfl
  | cons a rest ih =>
      exact ih (Next M S a)

theorem subsetDFA_accepts (M : NFA alpha state)
    (subsetsFinite : FiniteType (FSet state)) (w : Word alpha) :
    DFA.Accepts (SubsetDFA M subsetsFinite) w <-> Accepts M w := by
  unfold DFA.Accepts DFA.Run Accepts Reach
  change (SubsetDFA M subsetsFinite).accept
      (DFA.RunFrom (SubsetDFA M subsetsFinite) (StartSet M) w) ↔
    exists q, q ∈ ReachFromSet M (StartSet M) w ∧ M.accept q
  rw [subsetDFA_runFrom M subsetsFinite (StartSet M) w]
  rfl

theorem subsetDFA_language (M : NFA alpha state)
    (subsetsFinite : FiniteType (FSet state)) :
    FoC.Languages.Language.Equal (DFA.Language (SubsetDFA M subsetsFinite)) (AcceptedLanguage M) := by
  intro w
  exact subsetDFA_accepts M subsetsFinite w

/-!
# Deterministic automata as NFAs

A DFA embeds into an NFA by using no epsilon transitions and a singleton symbol
move. The following lemmas prove that the accepted language is unchanged.
-/

def FromDFA (M : DFA alpha state) : NFA alpha state where
  start := M.start
  step := fun q input =>
    match input with
    | none => FSet.Empty
    | some a => FSet.Singleton (M.step q a)
  accept := M.accept
  statesFinite := M.statesFinite

theorem reachFromSet_of_equal {M : NFA alpha state} {S T : FSet state}
    (hST : FSet.Equal S T) (w : Word alpha) :
    FSet.Equal (ReachFromSet M S w) (ReachFromSet M T w) := by
  induction w generalizing S T with
  | nil =>
      exact hST
  | cons a rest ih =>
      apply ih
      intro r
      constructor
      · intro hr
        cases hr with
        | intro p hp =>
            cases hp with
            | intro hpMove hreach =>
                cases hpMove with
                | intro q hq =>
                    exists p
                    constructor
                    · exists q
                      exact And.intro ((hST q).mp hq.left) hq.right
                    · exact hreach
      · intro hr
        cases hr with
        | intro p hp =>
            cases hp with
            | intro hpMove hreach =>
                cases hpMove with
                | intro q hq =>
                    exists p
                    constructor
                    · exists q
                      exact And.intro ((hST q).mpr hq.left) hq.right
                    · exact hreach

theorem fromDFA_epsilonReach_eq (M : DFA alpha state)
    {q r : state} (h : EpsilonReach (FromDFA M) q r) : r = q := by
  cases h with
  | refl _ => rfl
  | step hstep _ => cases hstep

theorem fromDFA_epsilonClosure_singleton (M : DFA alpha state) (q : state) :
    FSet.Equal (EpsilonClosure (FromDFA M) (FSet.Singleton q)) (FSet.Singleton q) := by
  intro r
  constructor
  · intro hr
    cases hr with
    | intro p hp =>
        cases hp with
        | intro hpq hreach =>
            cases hpq
            exact fromDFA_epsilonReach_eq M hreach
  · intro hr
    exact epsilonClosure_contains hr

theorem fromDFA_startSet (M : DFA alpha state) :
    FSet.Equal (StartSet (FromDFA M)) (FSet.Singleton M.start) :=
  fromDFA_epsilonClosure_singleton M M.start

theorem fromDFA_symbolMove_singleton (M : DFA alpha state) (q : state) (a : alpha) :
    FSet.Equal
      (SymbolMove (FromDFA M) (FSet.Singleton q) a)
      (FSet.Singleton (M.step q a)) := by
  intro r
  constructor
  · intro hr
    cases hr with
    | intro p hp =>
        cases hp with
        | intro hpq hstep =>
            cases hpq
            exact hstep
  · intro hr
    exact Exists.intro q (And.intro rfl hr)

theorem fromDFA_next_singleton (M : DFA alpha state) (q : state) (a : alpha) :
    FSet.Equal
      (Next (FromDFA M) (FSet.Singleton q) a)
      (FSet.Singleton (M.step q a)) := by
  intro r
  constructor
  · intro hr
    cases hr with
    | intro p hp =>
        cases hp with
        | intro hpMove hreach =>
            have hpStep : p ∈ FSet.Singleton (M.step q a) :=
              (fromDFA_symbolMove_singleton M q a p).mp hpMove
            cases hpStep
            exact fromDFA_epsilonReach_eq M hreach
  · intro hr
    exact epsilonClosure_contains ((fromDFA_symbolMove_singleton M q a r).mpr hr)

theorem fromDFA_reachFromSet_singleton (M : DFA alpha state)
    (q : state) (w : Word alpha) :
    FSet.Equal
      (ReachFromSet (FromDFA M) (FSet.Singleton q) w)
      (FSet.Singleton (DFA.RunFrom M q w)) := by
  induction w generalizing q with
  | nil =>
      exact FSet.equal_refl _
  | cons a rest ih =>
      exact FSet.equal_trans
        (reachFromSet_of_equal (M := FromDFA M) (fromDFA_next_singleton M q a) rest)
        (ih (M.step q a))

theorem fromDFA_language (M : DFA alpha state) :
    FoC.Languages.Language.Equal (AcceptedLanguage (FromDFA M)) (DFA.Language M) := by
  intro w
  have hReach : FSet.Equal (Reach (FromDFA M) w) (FSet.Singleton (DFA.Run M w)) := by
    unfold Reach DFA.Run
    exact FSet.equal_trans
      (reachFromSet_of_equal (M := FromDFA M) (fromDFA_startSet M) w)
      (fromDFA_reachFromSet_singleton M M.start w)
  constructor
  · intro hw
    cases hw with
    | intro q hq =>
        cases hq with
        | intro hqReach hAccept =>
            have hqRun : q = DFA.Run M w := (hReach q).mp hqReach
            rw [hqRun] at hAccept
            exact hAccept
  · intro hw
    exists DFA.Run M w
    constructor
    · exact (hReach (DFA.Run M w)).mpr rfl
    · exact hw

theorem dfa_language_nfa_recognizable {L : FoC.Languages.Language alpha}
    (hL : DFA.Recognizable L) : Recognizable L := by
  cases hL with
  | intro state hstate =>
      cases hstate with
      | intro M hM =>
          exists state
          exists FromDFA M
          exact FoC.Languages.Language.equal_trans (fromDFA_language M) hM

theorem nfa_language_dfa_recognizable {state : Type} (M : NFA alpha state)
    (subsetsFinite : FiniteType (FSet state)) :
    DFA.Recognizable (AcceptedLanguage M) := by
  exists FSet state
  exists SubsetDFA M subsetsFinite
  exact subsetDFA_language M subsetsFinite

end NFA
end Languages
end FoC
