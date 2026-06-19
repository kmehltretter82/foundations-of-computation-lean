import FoC.Foundation.Cardinality
import FoC.Languages.RegularExpression
import FoC.Languages.NFA
import FoC.Languages.Thompson

set_option doc.verso true

/-!
# Regular languages

## Regular-language predicates

This module collects the reusable predicates and closure theorems for regular
languages.  It relates regular-expression generation, DFA recognizability, and
NFA recognizability, then packages the constructions needed by the chapter
statements.

## Book coordinates

Used by:
- Chapter 3, Section 3.2: definition of regular language
- Chapter 3, Section 3.6: closure properties and automata comparison
-/

namespace FoC
namespace Languages

namespace RegularLanguage

def Regular (L : Language alpha) : Prop :=
  RegExp.Regular L

def DFARecognizable (L : Language alpha) : Prop :=
  DFA.Recognizable L

def NFARecognizable (L : Language alpha) : Prop :=
  NFA.Recognizable L

/-!
# Finite subsets of states

The subset construction needs a finite type of state sets. This section builds
finite set witnesses from sublists of the original finite state list.
-/

def FSetOfList (xs : List state) : Foundation.FSet state :=
  fun x => x ∈ xs

theorem filter_mem_sublists (xs : List state) (p : state -> Prop)
    [DecidablePred p] :
    xs.filter (fun x => decide (p x)) ∈ Foundation.ListCard.Sublists xs := by
  induction xs with
  | nil =>
      simp [Foundation.ListCard.Sublists]
  | cons x rest ih =>
      by_cases hx : p x
      · apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_map.mpr
        exists rest.filter (fun y => decide (p y))
        constructor
        · exact ih
        · simp [hx]
      · apply List.mem_append.mpr
        apply Or.inl
        simpa [hx] using ih

noncomputable def finiteFSetType (finite : Foundation.FiniteType state) :
    Foundation.FiniteType (Foundation.FSet state) := by
  classical
  exact
    { elems := (Foundation.ListCard.Sublists finite.elems).map FSetOfList
      complete := by
        intro A
        let xs := finite.elems.filter (fun x => decide (x ∈ A))
        have hxs : xs ∈ Foundation.ListCard.Sublists finite.elems := by
          exact filter_mem_sublists finite.elems (fun x => x ∈ A)
        have hA : A = FSetOfList xs := by
          funext x
          apply propext
          constructor
          · intro hxA
            have hxElems : x ∈ finite.elems := finite.complete x
            show x ∈ xs
            have hxFilter : x ∈ finite.elems ∧ x ∈ A :=
              And.intro hxElems hxA
            simpa [xs] using hxFilter
          · intro hx
            change x ∈ xs at hx
            have hxFilter : x ∈ finite.elems ∧ x ∈ A := by
              simpa [xs] using hx
            exact hxFilter.right
        rw [hA]
        apply List.mem_map.mpr
        exists xs }

/-!
# State-elimination regexes

The DFA-to-regular-expression direction is formalized by expressions for paths
whose intermediate states are restricted to a finite allowed list.
-/

noncomputable def StepRegex (alphabet : List alpha) (M : DFA alpha state)
    (q r : state) : RegExp alpha := by
  classical
  exact RegExp.CharClass (alphabet.filter fun a => M.step q a = r)

noncomputable def PathRegex (alphabet : List alpha) (M : DFA alpha state) :
    List state -> state -> state -> RegExp alpha
  | [], q, r =>
      by
        classical
        exact RegExp.alt (if q = r then RegExp.eps else RegExp.empty)
          (StepRegex alphabet M q r)
  | s :: rest, q, r =>
      RegExp.alt (PathRegex alphabet M rest q r)
        (RegExp.seq
          (RegExp.seq (PathRegex alphabet M rest q s)
            (RegExp.star (PathRegex alphabet M rest s s)))
          (PathRegex alphabet M rest s r))

noncomputable def DFARegex (alphabet : List alpha) (M : DFA alpha state) :
    RegExp alpha := by
  classical
  exact RegExp.AltList
    ((M.statesFinite.elems.filter fun q => M.accept q).map
      (fun q => PathRegex alphabet M M.statesFinite.elems M.start q))

/-!
# Alphabet-restricted paths

The state-elimination proof tracks that each input symbol belongs to the chosen
finite alphabet and relates restricted paths to DFA runs.
-/

def AllSymbolsIn (alphabet : List alpha) (w : Word alpha) : Prop :=
  forall a, List.Mem a w -> a ∈ alphabet

inductive PathVia (M : DFA alpha state) (allowed : List state) :
    state -> Word alpha -> state -> Prop where
  | empty (q : state) : PathVia M allowed q Word.Empty q
  | symbol (q : state) (a : alpha) : PathVia M allowed q (Word.Symbol a) (M.step q a)
  | cons {q mid r : state} {a : alpha} {tail : Word alpha} :
      tail ≠ Word.Empty ->
      mid ∈ allowed ->
      M.step q a = mid ->
      PathVia M allowed mid tail r ->
      PathVia M allowed q (a :: tail) r

theorem allSymbolsIn_concat_left {alphabet : List alpha} {x y : Word alpha}
    (h : AllSymbolsIn alphabet (Word.Concat x y)) :
    AllSymbolsIn alphabet x := by
  intro a ha
  exact h a (List.mem_append.mpr (Or.inl ha))

theorem allSymbolsIn_concat_right {alphabet : List alpha} {x y : Word alpha}
    (h : AllSymbolsIn alphabet (Word.Concat x y)) :
    AllSymbolsIn alphabet y := by
  intro a ha
  exact h a (List.mem_append.mpr (Or.inr ha))

theorem allSymbolsIn_concatWords {alphabet : List alpha}
    {pieces : List (Word alpha)} {p : Word alpha}
    (h : AllSymbolsIn alphabet (Language.ConcatWords pieces))
    (hp : p ∈ pieces) :
    AllSymbolsIn alphabet p := by
  induction pieces with
  | nil =>
      cases hp
  | cons x rest ih =>
      cases hp with
      | head =>
          exact allSymbolsIn_concat_left h
      | tail _ htail =>
          exact ih (allSymbolsIn_concat_right h) htail

theorem pathVia_prepend (M : DFA alpha state) (allowed : List state)
    {q mid r : state} {a : alpha} {tail : Word alpha}
    (hmid : mid ∈ allowed)
    (hstep : M.step q a = mid)
    (hpath : PathVia M allowed mid tail r) :
    PathVia M allowed q (a :: tail) r := by
  cases tail with
  | nil =>
      cases hpath with
      | empty _ =>
          simpa [hstep] using PathVia.symbol (M := M) (allowed := allowed) q a
  | cons b rest =>
      exact PathVia.cons (by intro h; cases h) hmid hstep hpath

theorem pathVia_allStates (M : DFA alpha state) (q : state) (w : Word alpha) :
    PathVia M M.statesFinite.elems q w (DFA.RunFrom M q w) := by
  induction w generalizing q with
  | nil =>
      exact PathVia.empty q
  | cons a rest ih =>
      cases rest with
      | nil =>
          exact PathVia.symbol q a
      | cons b tail =>
          exact PathVia.cons (by intro h; cases h)
            (M.statesFinite.complete (M.step q a)) rfl
            (ih (M.step q a))

theorem pathVia_cons_decomp (M : DFA alpha state)
    (s : state) (rest : List state) {q r : state} {w : Word alpha}
    (h : PathVia M (s :: rest) q w r) :
    PathVia M rest q w r ∨
      exists x loops z,
        w = Word.Concat x (Word.Concat (Language.ConcatWords loops) z) ∧
        PathVia M rest q x s ∧
        (forall p, p ∈ loops -> PathVia M rest s p s) ∧
        PathVia M rest s z r := by
  induction h with
  | empty q =>
      exact Or.inl (PathVia.empty q)
  | symbol q a =>
      exact Or.inl (PathVia.symbol q a)
  | cons htailNonempty hmidMem hstep htail ih =>
      rename_i q mid r a tail
      cases hmidMem with
      | head =>
          cases ih with
          | inl htailRest =>
              apply Or.inr
              exists Word.Symbol a
              exists []
              exists tail
              constructor
              · rfl
              constructor
              · simpa [hstep] using
                  PathVia.symbol (M := M) (allowed := rest) q a
              constructor
              · intro p hp
                cases hp
              · exact htailRest
          | inr hsplit =>
              cases hsplit with
              | intro x hx =>
                  cases hx with
                  | intro loops hloops =>
                      cases hloops with
                      | intro z hz =>
                          apply Or.inr
                          exists Word.Symbol a
                          exists x :: loops
                          exists z
                          constructor
                          · rw [hz.left]
                            simp [Word.Concat, Word.Symbol, Language.ConcatWords,
                              List.append_assoc]
                          constructor
                          · simpa [hstep] using
                              PathVia.symbol (M := M) (allowed := rest) q a
                          constructor
                          · intro p hp
                            cases hp with
                            | head =>
                                exact hz.right.left
                            | tail _ htail =>
                                exact hz.right.right.left p htail
                          · exact hz.right.right.right
      | tail _ hmidRest =>
          cases ih with
          | inl htailRest =>
              exact Or.inl (PathVia.cons htailNonempty hmidRest hstep htailRest)
          | inr hsplit =>
              cases hsplit with
              | intro x hx =>
                  cases hx with
                  | intro loops hloops =>
                      cases hloops with
                      | intro z hz =>
                          apply Or.inr
                          exists a :: x
                          exists loops
                          exists z
                          constructor
                          · rw [hz.left]
                            simp [Word.Concat]
                          constructor
                          · exact pathVia_prepend M rest hmidRest hstep hz.right.left
                          constructor
                          · exact hz.right.right.left
                          · exact hz.right.right.right

theorem stepRegex_denote (alphabet : List alpha) (M : DFA alpha state)
    (q r : state) (w : Word alpha) :
    w ∈ RegExp.Denote (StepRegex alphabet M q r) <->
      exists a, a ∈ alphabet ∧ M.step q a = r ∧ w = Word.Symbol a := by
  classical
  unfold StepRegex
  rw [RegExp.charClass_denote]
  constructor
  · intro hw
    cases hw with
    | intro a ha =>
        exists a
        constructor
        · exact (List.mem_filter.mp ha.left).left
        constructor
        · simpa using (List.mem_filter.mp ha.left).right
        · exact ha.right
  · intro hw
    cases hw with
    | intro a ha =>
        exists a
        constructor
        · exact List.mem_filter.mpr
            (And.intro ha.left (by simp [ha.right.left]))
        · exact ha.right.right

theorem pathRegex_complete (alphabet : List alpha) (M : DFA alpha state)
    (states : List state) {q r : state} {w : Word alpha}
    (hall : AllSymbolsIn alphabet w)
    (hpath : PathVia M states q w r) :
    w ∈ RegExp.Denote (PathRegex alphabet M states q r) := by
  induction states generalizing q r w with
  | nil =>
      cases hpath with
      | empty q =>
          unfold PathRegex
          classical
          apply Or.inl
          simp
          rfl
      | symbol q a =>
          unfold PathRegex
          apply Or.inr
          apply (stepRegex_denote alphabet M q (M.step q a) (Word.Symbol a)).mpr
          exists a
          constructor
          · exact hall a (List.Mem.head [])
          constructor <;> rfl
      | cons _ hmid _ _ =>
          cases hmid
  | cons s rest ih =>
      unfold PathRegex
      cases pathVia_cons_decomp M s rest hpath with
      | inl hrest =>
          exact Or.inl (ih hall hrest)
      | inr hsplit =>
          cases hsplit with
          | intro x hx =>
              cases hx with
              | intro loops hloops =>
                  cases hloops with
                  | intro z hz =>
                      have hallSplit :
                          AllSymbolsIn alphabet
                            (Word.Concat x (Word.Concat (Language.ConcatWords loops) z)) := by
                        rw [← hz.left]
                        exact hall
                      have hxAll : AllSymbolsIn alphabet x :=
                        allSymbolsIn_concat_left hallSplit
                      have htailAll :
                          AllSymbolsIn alphabet
                            (Word.Concat (Language.ConcatWords loops) z) :=
                        allSymbolsIn_concat_right hallSplit
                      have hloopsAll : AllSymbolsIn alphabet (Language.ConcatWords loops) :=
                        allSymbolsIn_concat_left htailAll
                      have hzAll : AllSymbolsIn alphabet z :=
                        allSymbolsIn_concat_right htailAll
                      have hxMem :
                          x ∈ RegExp.Denote (PathRegex alphabet M rest q s) :=
                        ih hxAll hz.right.left
                      have hloopsMem :
                          Language.ConcatWords loops ∈
                            Language.Star (RegExp.Denote (PathRegex alphabet M rest s s)) := by
                        exists loops
                        constructor
                        · intro p hp
                          exact ih (allSymbolsIn_concatWords hloopsAll hp)
                            (hz.right.right.left p hp)
                        · rfl
                      have hzMem :
                          z ∈ RegExp.Denote (PathRegex alphabet M rest s r) :=
                        ih hzAll hz.right.right.right
                      apply Or.inr
                      exists Word.Concat x (Language.ConcatWords loops)
                      exists z
                      constructor
                      · exact Exists.intro x
                          (Exists.intro (Language.ConcatWords loops)
                            (And.intro hxMem (And.intro hloopsMem rfl)))
                      constructor
                      · exact hzMem
                      · calc
                          w = Word.Concat x
                              (Word.Concat (Language.ConcatWords loops) z) := hz.left
                          _ = Word.Concat
                              (Word.Concat x (Language.ConcatWords loops)) z := by
                                rw [← Word.concat_assoc]

theorem pathRegex_sound (alphabet : List alpha) (M : DFA alpha state)
    (states : List state) {q r : state} {w : Word alpha}
    (hw : w ∈ RegExp.Denote (PathRegex alphabet M states q r)) :
    DFA.RunFrom M q w = r := by
  classical
  induction states generalizing q r w with
  | nil =>
      unfold PathRegex at hw
      cases hw with
      | inl hbase =>
          by_cases hqr : q = r
          · simp [hqr] at hbase
            rw [hbase]
            exact hqr
          · simp [hqr] at hbase
            cases hbase
      | inr hstep =>
          cases (stepRegex_denote alphabet M q r w).mp hstep with
          | intro a ha =>
              rw [ha.right.right]
              exact ha.right.left
  | cons s rest ih =>
      unfold PathRegex at hw
      cases hw with
      | inl hrest =>
          exact ih hrest
      | inr hthrough =>
          cases hthrough with
          | intro xy hxy =>
              cases hxy with
              | intro z hz =>
                  cases hz.left with
                  | intro x hx =>
                      cases hx with
                      | intro y hy =>
                          have hxRun : DFA.RunFrom M q x = s := ih hy.left
                          have hyRun : DFA.RunFrom M s y = s := by
                            cases hy.right.left with
                            | intro pieces hpieces =>
                                rw [← hpieces.right]
                                exact DFA.runFrom_concatWords_loop M s pieces (by
                                  intro p hp
                                  exact ih (hpieces.left p hp))
                          have hzRun : DFA.RunFrom M s z = r := ih hz.right.left
                          rw [hz.right.right, hy.right.right,
                            DFA.runFrom_append, DFA.runFrom_append, hxRun,
                            hyRun]
                          exact hzRun

theorem dfaRegex_sound (alphabet : List alpha) (M : DFA alpha state)
    {w : Word alpha}
    (hw : w ∈ RegExp.Denote (DFARegex alphabet M)) :
    DFA.Accepts M w := by
  classical
  unfold DFARegex at hw
  cases (RegExp.altList_denote
      ((M.statesFinite.elems.filter fun q => M.accept q).map
        (fun q => PathRegex alphabet M M.statesFinite.elems M.start q)) w).mp hw with
  | intro r hr =>
      cases List.mem_map.mp hr.left with
      | intro q hq =>
          have haccept : M.accept q := by
            simpa using (List.mem_filter.mp hq.left).right
          rw [← hq.right] at hr
          unfold DFA.Accepts DFA.Run
          rw [pathRegex_sound alphabet M M.statesFinite.elems hr.right]
          exact haccept

theorem dfaRegex_complete (alphabet : List alpha) (M : DFA alpha state)
    (halphabet : forall a, a ∈ alphabet) {w : Word alpha}
    (hw : DFA.Accepts M w) :
    w ∈ RegExp.Denote (DFARegex alphabet M) := by
  classical
  unfold DFARegex
  apply (RegExp.altList_denote
      ((M.statesFinite.elems.filter fun q => M.accept q).map
        (fun q => PathRegex alphabet M M.statesFinite.elems M.start q)) w).mpr
  exists PathRegex alphabet M M.statesFinite.elems M.start (DFA.Run M w)
  constructor
  · apply List.mem_map.mpr
    exists DFA.Run M w
    constructor
    · apply List.mem_filter.mpr
      constructor
      · exact M.statesFinite.complete (DFA.Run M w)
      · simpa using hw
    · rfl
  · exact pathRegex_complete alphabet M M.statesFinite.elems
      (by
        intro a _ha
        exact halphabet a)
      (by
        unfold DFA.Run
        exact pathVia_allStates M M.start w)

/-!
# Basic regular constructions

These theorems expose the regular-expression closure facts as language-level
regularity statements.
-/

theorem union_regular {L M : Language alpha}
    (hL : Regular L) (hM : Regular M) : Regular (Language.Union L M) :=
  RegExp.regular_union hL hM

theorem concat_regular {L M : Language alpha}
    (hL : Regular L) (hM : Regular M) : Regular (Language.Concat L M) :=
  RegExp.regular_concat hL hM

theorem star_regular {L : Language alpha} (hL : Regular L) : Regular (Language.Star L) :=
  RegExp.regular_star hL

theorem reverse_regular {L : Language alpha} (hL : Regular L) :
    Regular (Language.Reverse L) :=
  RegExp.regular_reverse hL

theorem finite_list_regular (ws : List (Word alpha)) :
    Regular (fun w => w ∈ ws) :=
  RegExp.finite_language_regular ws

theorem finite_alphabet_universal_regular (alphabet : List alpha)
    (halphabet : forall a, a ∈ alphabet) :
    Regular (Language.Universal : Language alpha) := by
  exists RegExp.star (RegExp.CharClass alphabet)
  intro w
  constructor
  · intro _hw
    exact True.intro
  · intro _hw
    induction w with
    | nil =>
        exact Language.star_empty_word (RegExp.Denote (RegExp.CharClass alphabet))
    | cons a rest ih =>
        have hhead : Word.Symbol a ∈ RegExp.Denote (RegExp.CharClass alphabet) :=
          (RegExp.charClass_denote alphabet (Word.Symbol a)).mpr
            (Exists.intro a (And.intro (halphabet a) rfl))
        have hconcat := Language.star_concat
          (Language.star_of_mem (RegExp.Denote (RegExp.CharClass alphabet)) hhead)
          (ih True.intro)
        simpa [Word.Concat] using hconcat

/-!
# Regular expressions and automata

Thompson construction gives NFAs from regular expressions, and the subset
construction gives DFAs from NFAs.
-/

theorem dfa_recognizable_is_nfa_recognizable {L : Language alpha}
    (hL : DFARecognizable L) : NFARecognizable L :=
  NFA.dfa_language_nfa_recognizable hL

theorem regular_expression_nfa_recognizable (r : RegExp alpha) :
    NFARecognizable (RegExp.Denote r) :=
  Thompson.regularExpression_nfa r

theorem regular_is_nfa_recognizable {L : Language alpha}
    (hL : Regular L) : NFARecognizable L := by
  cases hL with
  | intro r hr =>
      cases regular_expression_nfa_recognizable r with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              exists state
              exists M
              exact Language.equal_trans hM hr

theorem regular_is_dfa_recognizable {L : Language alpha}
    (hL : Regular L) : DFARecognizable L := by
  cases regular_is_nfa_recognizable hL with
  | intro state hstate =>
      cases hstate with
      | intro M hM =>
          exists Foundation.FSet state
          exists NFA.SubsetDFA M (finiteFSetType M.statesFinite)
          exact Language.equal_trans
            (NFA.subsetDFA_language M (finiteFSetType M.statesFinite)) hM

theorem dfa_recognizable_complement {L : Language alpha}
    (hL : DFARecognizable L) : DFARecognizable (Language.Compl L) :=
  DFA.recognizable_complement hL

theorem dfa_recognizable_union {L M : Language alpha}
    (hL : DFARecognizable L) (hM : DFARecognizable M) :
    DFARecognizable (Language.Union L M) :=
  DFA.recognizable_union hL hM

theorem dfa_recognizable_intersection {L M : Language alpha}
    (hL : DFARecognizable L) (hM : DFARecognizable M) :
    DFARecognizable (Language.Inter L M) :=
  DFA.recognizable_intersection hL hM

theorem dfa_recognizable_difference {L M : Language alpha}
    (hL : DFARecognizable L) (hM : DFARecognizable M) :
    DFARecognizable (Language.Diff L M) := by
  change DFARecognizable (Language.Inter L (Language.Compl M))
  exact dfa_recognizable_intersection hL (dfa_recognizable_complement hM)

theorem nfa_subset_construction {state : Type} (M : NFA alpha state)
    (subsetsFinite : Foundation.FiniteType (Foundation.FSet state)) :
    DFARecognizable (NFA.AcceptedLanguage M) :=
  NFA.nfa_language_dfa_recognizable M subsetsFinite

theorem nfa_subset_construction_auto {state : Type} (M : NFA alpha state) :
    DFARecognizable (NFA.AcceptedLanguage M) :=
  nfa_subset_construction M (finiteFSetType M.statesFinite)

/-!
# Automata to regular expressions

For a finite alphabet, state-elimination turns DFA-recognizable languages back
into regular-expression languages, completing the equivalence.
-/

theorem dfa_recognizable_regular (alphabet : List alpha)
    (halphabet : forall a, a ∈ alphabet) {L : Language alpha}
    (hL : DFARecognizable L) :
    Regular L := by
  cases hL with
  | intro state hstate =>
      cases hstate with
      | intro M hM =>
          exists DFARegex alphabet M
          intro w
          constructor
          · intro hw
            exact (hM w).mp (dfaRegex_sound alphabet M hw)
          · intro hw
            exact dfaRegex_complete alphabet M halphabet ((hM w).mpr hw)

theorem nfa_language_regular (alphabet : List alpha)
    (halphabet : forall a, a ∈ alphabet)
    {state : Type} (M : NFA alpha state) :
    Regular (NFA.AcceptedLanguage M) :=
  dfa_recognizable_regular alphabet halphabet
    (nfa_subset_construction_auto M)

theorem nfa_recognizable_regular (alphabet : List alpha)
    (halphabet : forall a, a ∈ alphabet) {L : Language alpha}
    (hL : NFARecognizable L) :
    Regular L := by
  cases hL with
  | intro state hstate =>
      cases hstate with
      | intro M hM =>
          cases nfa_language_regular alphabet halphabet M with
          | intro r hr =>
              exists r
              exact Language.equal_trans hr hM

theorem dfa_recognizable_complement_regular (alphabet : List alpha)
    (halphabet : forall a, a ∈ alphabet) {L : Language alpha}
    (hL : DFARecognizable L) :
    Regular (Language.Compl L) :=
  dfa_recognizable_regular alphabet halphabet
    (dfa_recognizable_complement hL)

theorem dfa_recognizable_intersection_regular (alphabet : List alpha)
    (halphabet : forall a, a ∈ alphabet) {L M : Language alpha}
    (hL : DFARecognizable L) (hM : DFARecognizable M) :
    Regular (Language.Inter L M) :=
  dfa_recognizable_regular alphabet halphabet
    (dfa_recognizable_intersection hL hM)

theorem dfa_recognizable_difference_regular (alphabet : List alpha)
    (halphabet : forall a, a ∈ alphabet) {L M : Language alpha}
    (hL : DFARecognizable L) (hM : DFARecognizable M) :
    Regular (Language.Diff L M) :=
  dfa_recognizable_regular alphabet halphabet
    (dfa_recognizable_difference hL hM)

theorem complement_regular (alphabet : List alpha)
    (halphabet : forall a, a ∈ alphabet) {L : Language alpha}
    (hL : Regular L) :
    Regular (Language.Compl L) :=
  dfa_recognizable_complement_regular alphabet halphabet
    (regular_is_dfa_recognizable hL)

theorem intersection_regular (alphabet : List alpha)
    (halphabet : forall a, a ∈ alphabet) {L M : Language alpha}
    (hL : Regular L) (hM : Regular M) :
    Regular (Language.Inter L M) :=
  dfa_recognizable_intersection_regular alphabet halphabet
    (regular_is_dfa_recognizable hL) (regular_is_dfa_recognizable hM)

theorem difference_regular (alphabet : List alpha)
    (halphabet : forall a, a ∈ alphabet) {L M : Language alpha}
    (hL : Regular L) (hM : Regular M) :
    Regular (Language.Diff L M) :=
  dfa_recognizable_difference_regular alphabet halphabet
    (regular_is_dfa_recognizable hL) (regular_is_dfa_recognizable hM)

/-!
The state-elimination bridge is proved for DFA-recognizable languages over an
explicit finite alphabet list.  The corresponding NFA bridge uses a classical
finite powerset-state witness built from the NFA's finite state list.
-/

end RegularLanguage
end Languages
end FoC
