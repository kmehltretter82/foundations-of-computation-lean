import FoC.Languages.NFAPath
import FoC.Languages.RegularExpression

namespace FoC
namespace Languages

/-!
Thompson-style NFA constructions for regular expressions.

Used by:
- Chapter 3, Section 3.6, Theorem 3.3: every regular-expression language can
  be recognized by an NFA.
-/

open Foundation

namespace Thompson

def BoolFinite : FiniteType Bool where
  elems := [false, true]
  complete := by
    intro b
    cases b <;> simp

def EmptyNFA (alpha : Type u) : NFA alpha Bool where
  start := false
  step := fun _ _ => FSet.Empty
  accept := fun q => q = true
  statesFinite := BoolFinite

def EpsilonNFA (alpha : Type u) : NFA alpha Bool where
  start := false
  step := fun q input r => q = false ∧ input = none ∧ r = true
  accept := fun q => q = true
  statesFinite := BoolFinite

def SymbolNFA (a : alpha) : NFA alpha Bool where
  start := false
  step := fun q input r => q = false ∧ input = some a ∧ r = true
  accept := fun q => q = true
  statesFinite := BoolFinite

theorem empty_path_no_accept {w : Word alpha} {q : Bool}
    (hpath : NFA.Path (EmptyNFA alpha) false w q) :
    q ≠ true := by
  intro hq
  cases hpath with
  | nil _ =>
      cases hq
  | eps hstep _ =>
      cases hstep
  | sym hstep _ =>
      cases hstep

theorem emptyNFA_language :
    Language.Equal (NFA.AcceptedLanguage (EmptyNFA alpha)) (Language.Empty : Language alpha) := by
  intro w
  constructor
  · intro hw
    have hp := (NFA.pathAccepts_iff_accepts (EmptyNFA alpha) w).mpr hw
    cases hp with
    | intro q hq =>
        exact empty_path_no_accept hq.left hq.right
  · intro hw
    cases hw

theorem epsilon_path_word_empty {w : Word alpha} {q : Bool}
    (hpath : NFA.Path (EpsilonNFA alpha) true w q) : w = Word.Empty ∧ q = true := by
  cases hpath with
  | nil _ =>
      exact And.intro rfl rfl
  | eps hstep _ =>
      cases hstep.left
  | sym hstep _ =>
      cases hstep.left

theorem epsilonNFA_language :
    Language.Equal (NFA.AcceptedLanguage (EpsilonNFA alpha))
      (Language.Singleton (Word.Empty : Word alpha)) := by
  intro w
  constructor
  · intro hw
    have hp := (NFA.pathAccepts_iff_accepts (EpsilonNFA alpha) w).mpr hw
    cases hp with
    | intro q hq =>
        cases hq.left with
        | nil _ =>
            cases hq.right
        | eps hstep htail =>
            cases hstep.right.right
            have htail_empty := epsilon_path_word_empty htail
            exact htail_empty.left
        | sym hstep _ =>
            cases hstep.right.left
  · intro hw
    rw [hw]
    apply (NFA.pathAccepts_iff_accepts (EpsilonNFA alpha) Word.Empty).mp
    exists true
    constructor
    · exact NFA.Path.eps (And.intro rfl (And.intro rfl rfl)) (NFA.Path.nil true)
    · rfl

theorem symbol_path_from_true_empty {a : alpha} {w : Word alpha} {q : Bool}
    (hpath : NFA.Path (SymbolNFA a) true w q) : w = Word.Empty ∧ q = true := by
  cases hpath with
  | nil _ =>
      exact And.intro rfl rfl
  | eps hstep _ =>
      cases hstep.left
  | sym hstep _ =>
      cases hstep.left

theorem symbolNFA_language (a : alpha) :
    Language.Equal (NFA.AcceptedLanguage (SymbolNFA a))
      (Language.Singleton (Word.Symbol a)) := by
  intro w
  constructor
  · intro hw
    have hp := (NFA.pathAccepts_iff_accepts (SymbolNFA a) w).mpr hw
    cases hp with
    | intro q hq =>
        cases hq.left with
        | nil _ =>
            cases hq.right
        | eps hstep _ =>
            cases hstep.right.left
        | sym hstep htail =>
            cases hstep.left
            cases hstep.right.left
            cases hstep.right.right
            have htail_empty := symbol_path_from_true_empty htail
            cases htail_empty.left
            rfl
  · intro hw
    rw [hw]
    apply (NFA.pathAccepts_iff_accepts (SymbolNFA a) (Word.Symbol a)).mp
    exists true
    constructor
    · exact NFA.Path.sym (And.intro rfl (And.intro rfl rfl)) (NFA.Path.nil true)
    · rfl

inductive UnionState (leftState rightState : Type) where
  | start : UnionState leftState rightState
  | left : leftState -> UnionState leftState rightState
  | right : rightState -> UnionState leftState rightState

namespace UnionState

def finite (leftFinite : FiniteType leftState) (rightFinite : FiniteType rightState) :
    FiniteType (UnionState leftState rightState) where
  elems := [UnionState.start] ++
    (leftFinite.elems.map UnionState.left) ++
    (rightFinite.elems.map UnionState.right)
  complete := by
    intro q
    cases q with
    | start =>
        simp
    | left q =>
        simp [leftFinite.complete q]
    | right q =>
        simp [rightFinite.complete q]

end UnionState

def UnionNFA (M : NFA alpha leftState) (N : NFA alpha rightState) :
    NFA alpha (UnionState leftState rightState) where
  start := UnionState.start
  step := fun q input next =>
    match q with
    | UnionState.start =>
        input = none ∧
          (next = UnionState.left M.start ∨ next = UnionState.right N.start)
    | UnionState.left q =>
        exists r, r ∈ M.step q input ∧ next = UnionState.left r
    | UnionState.right q =>
        exists r, r ∈ N.step q input ∧ next = UnionState.right r
  accept := fun q =>
    match q with
    | UnionState.start => False
    | UnionState.left q => M.accept q
    | UnionState.right q => N.accept q
  statesFinite := UnionState.finite M.statesFinite N.statesFinite

theorem union_left_path {M : NFA alpha leftState} {N : NFA alpha rightState}
    {q r : leftState} {w : Word alpha}
    (hpath : NFA.Path M q w r) :
    NFA.Path (UnionNFA M N) (UnionState.left q) w (UnionState.left r) := by
  induction hpath with
  | nil _ =>
      exact NFA.Path.nil _
  | eps hstep _ ih =>
      exact NFA.Path.eps (Exists.intro _ (And.intro hstep rfl)) ih
  | sym hstep _ ih =>
      exact NFA.Path.sym (Exists.intro _ (And.intro hstep rfl)) ih

theorem union_right_path {M : NFA alpha leftState} {N : NFA alpha rightState}
    {q r : rightState} {w : Word alpha}
    (hpath : NFA.Path N q w r) :
    NFA.Path (UnionNFA M N) (UnionState.right q) w (UnionState.right r) := by
  induction hpath with
  | nil _ =>
      exact NFA.Path.nil _
  | eps hstep _ ih =>
      exact NFA.Path.eps (Exists.intro _ (And.intro hstep rfl)) ih
  | sym hstep _ ih =>
      exact NFA.Path.sym (Exists.intro _ (And.intro hstep rfl)) ih

theorem union_left_path_inv_aux {M : NFA alpha leftState} {N : NFA alpha rightState}
    {startState s : UnionState leftState rightState} {w : Word alpha}
    (hpath : NFA.Path (UnionNFA M N) startState w s) :
    forall q : leftState, startState = UnionState.left q ->
      exists r, s = UnionState.left r ∧ NFA.Path M q w r := by
  induction hpath with
  | nil _ =>
      intro q hstart
      cases hstart
      exists q
      exact And.intro rfl (NFA.Path.nil q)
  | eps hstep _ ih =>
      intro q hstart
      cases hstart
      cases hstep with
      | intro r hr =>
          cases hr with
          | intro hrStep hs =>
              cases hs
              cases ih r rfl with
              | intro t ht =>
                  exists t
                  exact And.intro ht.left (NFA.Path.eps hrStep ht.right)
  | sym hstep _ ih =>
      intro q hstart
      cases hstart
      cases hstep with
      | intro r hr =>
          cases hr with
          | intro hrStep hs =>
              cases hs
              cases ih r rfl with
              | intro t ht =>
                  exists t
                  exact And.intro ht.left (NFA.Path.sym hrStep ht.right)

theorem union_left_path_inv {M : NFA alpha leftState} {N : NFA alpha rightState}
    {q : leftState} {s : UnionState leftState rightState} {w : Word alpha}
    (hpath : NFA.Path (UnionNFA M N) (UnionState.left q) w s) :
    exists r, s = UnionState.left r ∧ NFA.Path M q w r :=
  union_left_path_inv_aux hpath q rfl

theorem union_right_path_inv_aux {M : NFA alpha leftState} {N : NFA alpha rightState}
    {startState s : UnionState leftState rightState} {w : Word alpha}
    (hpath : NFA.Path (UnionNFA M N) startState w s) :
    forall q : rightState, startState = UnionState.right q ->
      exists r, s = UnionState.right r ∧ NFA.Path N q w r := by
  induction hpath with
  | nil _ =>
      intro q hstart
      cases hstart
      exists q
      exact And.intro rfl (NFA.Path.nil q)
  | eps hstep _ ih =>
      intro q hstart
      cases hstart
      cases hstep with
      | intro r hr =>
          cases hr with
          | intro hrStep hs =>
              cases hs
              cases ih r rfl with
              | intro t ht =>
                  exists t
                  exact And.intro ht.left (NFA.Path.eps hrStep ht.right)
  | sym hstep _ ih =>
      intro q hstart
      cases hstart
      cases hstep with
      | intro r hr =>
          cases hr with
          | intro hrStep hs =>
              cases hs
              cases ih r rfl with
              | intro t ht =>
                  exists t
                  exact And.intro ht.left (NFA.Path.sym hrStep ht.right)

theorem union_right_path_inv {M : NFA alpha leftState} {N : NFA alpha rightState}
    {q : rightState} {s : UnionState leftState rightState} {w : Word alpha}
    (hpath : NFA.Path (UnionNFA M N) (UnionState.right q) w s) :
    exists r, s = UnionState.right r ∧ NFA.Path N q w r :=
  union_right_path_inv_aux hpath q rfl

theorem unionNFA_pathAccepts {M : NFA alpha leftState} {N : NFA alpha rightState}
    (w : Word alpha) :
    NFA.PathAccepts (UnionNFA M N) w <->
      NFA.PathAccepts M w ∨ NFA.PathAccepts N w := by
  constructor
  · intro h
    cases h with
    | intro q hq =>
        cases hq.left with
        | nil _ =>
            cases hq.right
        | eps hstep htail =>
            cases hstep.right with
            | inl hleft =>
                cases hleft
                cases union_left_path_inv htail with
                | intro r hr =>
                    cases hr.left
                    exact Or.inl (Exists.intro r (And.intro hr.right hq.right))
            | inr hright =>
                cases hright
                cases union_right_path_inv htail with
                | intro r hr =>
                    cases hr.left
                    exact Or.inr (Exists.intro r (And.intro hr.right hq.right))
        | sym hstep _ =>
            cases hstep.left
  · intro h
    cases h with
    | inl hM =>
        cases hM with
        | intro q hq =>
            exists UnionState.left q
            constructor
            · exact NFA.Path.eps
                (And.intro rfl (Or.inl rfl))
                (union_left_path (N := N) hq.left)
            · exact hq.right
    | inr hN =>
        cases hN with
        | intro q hq =>
            exists UnionState.right q
            constructor
            · exact NFA.Path.eps
                (And.intro rfl (Or.inr rfl))
                (union_right_path (M := M) hq.left)
            · exact hq.right

theorem unionNFA_language (M : NFA alpha leftState) (N : NFA alpha rightState) :
    Language.Equal (NFA.AcceptedLanguage (UnionNFA M N))
      (Language.Union (NFA.AcceptedLanguage M) (NFA.AcceptedLanguage N)) := by
  intro w
  constructor
  · intro hw
    have hp := (NFA.pathAccepts_iff_accepts (UnionNFA M N) w).mpr hw
    cases (unionNFA_pathAccepts (M := M) (N := N) w).mp hp with
    | inl hM => exact Or.inl ((NFA.pathAccepts_iff_accepts M w).mp hM)
    | inr hN => exact Or.inr ((NFA.pathAccepts_iff_accepts N w).mp hN)
  · intro hw
    apply (NFA.pathAccepts_iff_accepts (UnionNFA M N) w).mp
    apply (unionNFA_pathAccepts (M := M) (N := N) w).mpr
    cases hw with
    | inl hM => exact Or.inl ((NFA.pathAccepts_iff_accepts M w).mpr hM)
    | inr hN => exact Or.inr ((NFA.pathAccepts_iff_accepts N w).mpr hN)

def SumFinite (leftFinite : FiniteType leftState) (rightFinite : FiniteType rightState) :
    FiniteType (Sum leftState rightState) where
  elems := (leftFinite.elems.map Sum.inl) ++ (rightFinite.elems.map Sum.inr)
  complete := by
    intro q
    cases q with
    | inl q =>
        simp [leftFinite.complete q]
    | inr q =>
        simp [rightFinite.complete q]

def ConcatNFA (M : NFA alpha leftState) (N : NFA alpha rightState) :
    NFA alpha (Sum leftState rightState) where
  start := Sum.inl M.start
  step := fun q input next =>
    match q with
    | Sum.inl q =>
        (exists r, r ∈ M.step q input ∧ next = Sum.inl r) ∨
          (input = none ∧ M.accept q ∧ next = Sum.inr N.start)
    | Sum.inr q =>
        exists r, r ∈ N.step q input ∧ next = Sum.inr r
  accept := fun q =>
    match q with
    | Sum.inl _ => False
    | Sum.inr q => N.accept q
  statesFinite := SumFinite M.statesFinite N.statesFinite

theorem concat_left_path {M : NFA alpha leftState} {N : NFA alpha rightState}
    {q r : leftState} {w : Word alpha}
    (hpath : NFA.Path M q w r) :
    NFA.Path (ConcatNFA M N) (Sum.inl q) w (Sum.inl r) := by
  induction hpath with
  | nil _ =>
      exact NFA.Path.nil _
  | eps hstep _ ih =>
      exact NFA.Path.eps (Or.inl (Exists.intro _ (And.intro hstep rfl))) ih
  | sym hstep _ ih =>
      exact NFA.Path.sym (Or.inl (Exists.intro _ (And.intro hstep rfl))) ih

theorem concat_right_path {M : NFA alpha leftState} {N : NFA alpha rightState}
    {q r : rightState} {w : Word alpha}
    (hpath : NFA.Path N q w r) :
    NFA.Path (ConcatNFA M N) (Sum.inr q) w (Sum.inr r) := by
  induction hpath with
  | nil _ =>
      exact NFA.Path.nil _
  | eps hstep _ ih =>
      exact NFA.Path.eps (Exists.intro _ (And.intro hstep rfl)) ih
  | sym hstep _ ih =>
      exact NFA.Path.sym (Exists.intro _ (And.intro hstep rfl)) ih

theorem concat_right_path_inv_aux {M : NFA alpha leftState} {N : NFA alpha rightState}
    {startState s : Sum leftState rightState} {w : Word alpha}
    (hpath : NFA.Path (ConcatNFA M N) startState w s) :
    forall q : rightState, startState = Sum.inr q ->
      exists r, s = Sum.inr r ∧ NFA.Path N q w r := by
  induction hpath with
  | nil _ =>
      intro q hstart
      cases hstart
      exists q
      exact And.intro rfl (NFA.Path.nil q)
  | eps hstep _ ih =>
      intro q hstart
      cases hstart
      cases hstep with
      | intro r hr =>
          cases hr with
          | intro hrStep hs =>
              cases hs
              cases ih r rfl with
              | intro t ht =>
                  exists t
                  exact And.intro ht.left (NFA.Path.eps hrStep ht.right)
  | sym hstep _ ih =>
      intro q hstart
      cases hstart
      cases hstep with
      | intro r hr =>
          cases hr with
          | intro hrStep hs =>
              cases hs
              cases ih r rfl with
              | intro t ht =>
                  exists t
                  exact And.intro ht.left (NFA.Path.sym hrStep ht.right)

theorem concat_right_path_inv {M : NFA alpha leftState} {N : NFA alpha rightState}
    {q : rightState} {s : Sum leftState rightState} {w : Word alpha}
    (hpath : NFA.Path (ConcatNFA M N) (Sum.inr q) w s) :
    exists r, s = Sum.inr r ∧ NFA.Path N q w r :=
  concat_right_path_inv_aux hpath q rfl

theorem concat_left_to_right_inv_aux {M : NFA alpha leftState} {N : NFA alpha rightState}
    {startState s : Sum leftState rightState} {w : Word alpha}
    (hpath : NFA.Path (ConcatNFA M N) startState w s) :
    forall (q : leftState) (r : rightState),
      startState = Sum.inl q -> s = Sum.inr r ->
      exists x y qf,
        w = Word.Concat x y ∧
        NFA.Path M q x qf ∧ M.accept qf ∧ NFA.Path N N.start y r := by
  induction hpath with
  | nil _ =>
      intro q r hstart hend
      cases hstart
      cases hend
  | eps hstep htail ih =>
      rename_i pathWord
      intro q r hstart hend
      cases hstart
      cases hstep with
      | inl hleft =>
          cases hleft with
          | intro moved hmoved =>
              cases hmoved with
              | intro hmovedStep hnext =>
                  cases hnext
                  cases ih moved r rfl hend with
                  | intro x hx =>
                      cases hx with
                      | intro y hy =>
                          cases hy with
                          | intro qf hqf =>
                              exists x
                              exists y
                              exists qf
                              constructor
                              · exact hqf.left
                              constructor
                              · exact NFA.Path.eps hmovedStep hqf.right.left
                              · exact hqf.right.right
      | inr hcross =>
          cases hcross with
          | intro hinput hrest =>
              cases hrest with
              | intro haccept hnext =>
                  cases hnext
                  cases concat_right_path_inv htail with
                  | intro nr hnr =>
                      cases hnr.left
                      cases hend
                      exists Word.Empty
                      exists pathWord
                      exists q
                      constructor
                      · rfl
                      constructor
                      · exact NFA.Path.nil q
                      constructor
                      · exact haccept
                      · exact hnr.right
  | sym hstep htail ih =>
      rename_i input rest
      intro q r hstart hend
      cases hstart
      cases hstep with
      | inl hleft =>
          cases hleft with
          | intro moved hmoved =>
              cases hmoved with
              | intro hmovedStep hnext =>
                  cases hnext
                  cases ih moved r rfl hend with
                  | intro x hx =>
                      cases hx with
                      | intro y hy =>
                          cases hy with
                          | intro qf hqf =>
                              exists (input :: x)
                              exists y
                              exists qf
                              constructor
                              · rw [hqf.left]
                                rfl
                              constructor
                              · exact NFA.Path.sym hmovedStep hqf.right.left
                              · exact hqf.right.right
      | inr hcross =>
          cases hcross.left

theorem concat_left_to_right_inv {M : NFA alpha leftState} {N : NFA alpha rightState}
    {q : leftState} {r : rightState} {w : Word alpha}
    (hpath : NFA.Path (ConcatNFA M N) (Sum.inl q) w (Sum.inr r)) :
    exists x y qf,
      w = Word.Concat x y ∧
      NFA.Path M q x qf ∧ M.accept qf ∧ NFA.Path N N.start y r :=
  concat_left_to_right_inv_aux hpath q r rfl rfl

theorem concatNFA_pathAccepts {M : NFA alpha leftState} {N : NFA alpha rightState}
    (w : Word alpha) :
    NFA.PathAccepts (ConcatNFA M N) w <->
      w ∈ Language.Concat (NFA.AcceptedLanguage M) (NFA.AcceptedLanguage N) := by
  constructor
  · intro h
    cases h with
    | intro q hq =>
        cases q with
        | inl q =>
            cases hq.right
        | inr q =>
            cases concat_left_to_right_inv hq.left with
            | intro x hx =>
                cases hx with
                | intro y hy =>
                    cases hy with
                    | intro qf hqf =>
                        exists x
                        exists y
                        constructor
                        · exact (NFA.pathAccepts_iff_accepts M x).mp
                            (Exists.intro qf (And.intro hqf.right.left hqf.right.right.left))
                        constructor
                        · exact (NFA.pathAccepts_iff_accepts N y).mp
                            (Exists.intro q (And.intro hqf.right.right.right hq.right))
                        · exact hqf.left
  · intro h
    cases h with
    | intro x hx =>
        cases hx with
        | intro y hy =>
            cases hy with
            | intro hxM hrest =>
                cases hrest with
                | intro hyN hwEq =>
                    have hMx := (NFA.pathAccepts_iff_accepts M x).mpr hxM
                    have hNy := (NFA.pathAccepts_iff_accepts N y).mpr hyN
                    cases hMx with
                    | intro qf hqf =>
                        cases hNy with
                        | intro rf hrf =>
                            rw [hwEq]
                            exists Sum.inr rf
                            constructor
                            · exact NFA.path_append
                                (concat_left_path (N := N) hqf.left)
                                (NFA.Path.eps
                                  (Or.inr (And.intro rfl (And.intro hqf.right rfl)))
                                  (concat_right_path (M := M) hrf.left))
                            · exact hrf.right

theorem concatNFA_language (M : NFA alpha leftState) (N : NFA alpha rightState) :
    Language.Equal (NFA.AcceptedLanguage (ConcatNFA M N))
      (Language.Concat (NFA.AcceptedLanguage M) (NFA.AcceptedLanguage N)) := by
  intro w
  constructor
  · intro hw
    exact (concatNFA_pathAccepts (M := M) (N := N) w).mp
      ((NFA.pathAccepts_iff_accepts (ConcatNFA M N) w).mpr hw)
  · intro hw
    exact (NFA.pathAccepts_iff_accepts (ConcatNFA M N) w).mp
      ((concatNFA_pathAccepts (M := M) (N := N) w).mpr hw)

def OptionFinite (stateFinite : FiniteType state) : FiniteType (Option state) where
  elems := none :: stateFinite.elems.map some
  complete := by
    intro q
    cases q with
    | none =>
        simp
    | some q =>
        simp [stateFinite.complete q]

def StarNFA (M : NFA alpha state) : NFA alpha (Option state) where
  start := none
  step := fun q input next =>
    match q with
    | none => input = none ∧ next = some M.start
    | some q =>
        (exists r, r ∈ M.step q input ∧ next = some r) ∨
          (input = none ∧ M.accept q ∧ next = none)
  accept := fun q => q = none
  statesFinite := OptionFinite M.statesFinite

theorem star_inner_path {M : NFA alpha state} {q r : state} {w : Word alpha}
    (hpath : NFA.Path M q w r) :
    NFA.Path (StarNFA M) (some q) w (some r) := by
  induction hpath with
  | nil _ =>
      exact NFA.Path.nil _
  | eps hstep _ ih =>
      exact NFA.Path.eps (Or.inl (Exists.intro _ (And.intro hstep rfl))) ih
  | sym hstep _ ih =>
      exact NFA.Path.sym (Or.inl (Exists.intro _ (And.intro hstep rfl))) ih

theorem star_sound_aux {M : NFA alpha state}
    {startState endState : Option state} {w : Word alpha}
    (hpath : NFA.Path (StarNFA M) startState w endState) :
    (startState = none -> endState = none ->
      w ∈ Language.Star (NFA.AcceptedLanguage M)) ∧
    (forall q : state, startState = some q -> endState = none ->
      exists x y qf,
        w = Word.Concat x y ∧
        NFA.Path M q x qf ∧ M.accept qf ∧
        y ∈ Language.Star (NFA.AcceptedLanguage M)) := by
  induction hpath with
  | nil _ =>
      constructor
      · intro hstart hend
        cases hstart
        exact Language.star_empty_word _
      · intro q hstart hend
        cases hstart
        cases hend
  | eps hstep htail ih =>
      rename_i pathWord
      constructor
      · intro hstart hend
        cases hstart
        cases hstep with
        | intro _ hnext =>
            cases hnext
            cases ih.right M.start rfl hend with
            | intro x hx =>
                cases hx with
                | intro y hy =>
                    cases hy with
                    | intro qf hqf =>
                        have hxMem : x ∈ NFA.AcceptedLanguage M :=
                          (NFA.pathAccepts_iff_accepts M x).mp
                            (Exists.intro qf (And.intro hqf.right.left hqf.right.right.left))
                        have hxyStar :
                            Word.Concat x y ∈ Language.Star (NFA.AcceptedLanguage M) :=
                          Language.star_concat
                            (Language.star_of_mem (NFA.AcceptedLanguage M) hxMem)
                            hqf.right.right.right
                        rw [hqf.left]
                        exact hxyStar
      · intro q hstart hend
        cases hstart
        cases hstep with
        | inl hinner =>
            cases hinner with
            | intro moved hmoved =>
                cases hmoved with
                | intro hmovedStep hnext =>
                    cases hnext
                    cases ih.right moved rfl hend with
                    | intro x hx =>
                        cases hx with
                        | intro y hy =>
                            cases hy with
                            | intro qf hqf =>
                                exists x
                                exists y
                                exists qf
                                constructor
                                · exact hqf.left
                                constructor
                                · exact NFA.Path.eps hmovedStep hqf.right.left
                                · exact hqf.right.right
        | inr hreturn =>
            cases hreturn with
            | intro hinput hrest =>
                cases hrest with
                | intro haccept hnext =>
                    cases hnext
                    exists Word.Empty
                    exists pathWord
                    exists q
                    constructor
                    · rfl
                    constructor
                    · exact NFA.Path.nil q
                    constructor
                    · exact haccept
                    · exact ih.left rfl hend
  | sym hstep htail ih =>
      constructor
      · intro hstart hend
        cases hstart
        cases hstep.left
      · intro q hstart hend
        cases hstart
        cases hstep with
        | inl hinner =>
            cases hinner with
            | intro moved hmoved =>
                cases hmoved with
                | intro hmovedStep hnext =>
                    cases hnext
                    cases ih.right moved rfl hend with
                    | intro x hx =>
                        cases hx with
                        | intro y hy =>
                            cases hy with
                            | intro qf hqf =>
                                rename_i input rest
                                exists (input :: x)
                                exists y
                                exists qf
                                constructor
                                · rw [hqf.left]
                                  rfl
                                constructor
                                · exact NFA.Path.sym hmovedStep hqf.right.left
                                · exact hqf.right.right
        | inr hreturn =>
            cases hreturn.left

theorem star_path_of_pieces {M : NFA alpha state}
    (pieces : List (Word alpha))
    (hall : forall p, p ∈ pieces -> p ∈ NFA.AcceptedLanguage M) :
    NFA.Path (StarNFA M) none (Language.ConcatWords pieces) none := by
  induction pieces with
  | nil =>
      exact NFA.Path.nil none
  | cons piece rest ih =>
      have hpiece := (NFA.pathAccepts_iff_accepts M piece).mpr
        (hall piece (List.Mem.head rest))
      cases hpiece with
      | intro qf hqf =>
          have hreturn :
              NFA.Path (StarNFA M) (some M.start) piece none := by
            have hinner := star_inner_path (M := M) hqf.left
            have hback : NFA.Path (StarNFA M) (some qf) Word.Empty none :=
              NFA.Path.eps (Or.inr (And.intro rfl (And.intro hqf.right rfl)))
                (NFA.Path.nil none)
            have happ := NFA.path_append hinner hback
            rw [Word.concat_empty_right] at happ
            exact happ
          exact NFA.Path.eps (And.intro rfl rfl)
            (NFA.path_append hreturn (ih (by
              intro p hp
              exact hall p (List.Mem.tail piece hp))))

theorem starNFA_pathAccepts {M : NFA alpha state} (w : Word alpha) :
    NFA.PathAccepts (StarNFA M) w <->
      w ∈ Language.Star (NFA.AcceptedLanguage M) := by
  constructor
  · intro h
    cases h with
    | intro q hq =>
        cases hq.right
        exact (star_sound_aux hq.left).left rfl rfl
  · intro hw
    cases hw with
    | intro pieces hpieces =>
        rw [← hpieces.right]
        exists none
        constructor
        · exact star_path_of_pieces pieces hpieces.left
        · rfl

theorem starNFA_language (M : NFA alpha state) :
    Language.Equal (NFA.AcceptedLanguage (StarNFA M))
      (Language.Star (NFA.AcceptedLanguage M)) := by
  intro w
  constructor
  · intro hw
    exact (starNFA_pathAccepts (M := M) w).mp
      ((NFA.pathAccepts_iff_accepts (StarNFA M) w).mpr hw)
  · intro hw
    exact (NFA.pathAccepts_iff_accepts (StarNFA M) w).mp
      ((starNFA_pathAccepts (M := M) w).mpr hw)

theorem union_equal_of_equal {L₁ L₂ M₁ M₂ : Language alpha}
    (hL : Language.Equal L₁ L₂) (hM : Language.Equal M₁ M₂) :
    Language.Equal (Language.Union L₁ M₁) (Language.Union L₂ M₂) := by
  intro w
  constructor
  · intro hw
    cases hw with
    | inl h => exact Or.inl ((hL w).mp h)
    | inr h => exact Or.inr ((hM w).mp h)
  · intro hw
    cases hw with
    | inl h => exact Or.inl ((hL w).mpr h)
    | inr h => exact Or.inr ((hM w).mpr h)

theorem concat_equal_of_equal {L₁ L₂ M₁ M₂ : Language alpha}
    (hL : Language.Equal L₁ L₂) (hM : Language.Equal M₁ M₂) :
    Language.Equal (Language.Concat L₁ M₁) (Language.Concat L₂ M₂) := by
  intro w
  constructor
  · intro hw
    cases hw with
    | intro x hx =>
        cases hx with
        | intro y hy =>
            cases hy with
            | intro hxL hrest =>
                cases hrest with
                | intro hyM hwEq =>
                    exists x
                    exists y
                    exact And.intro ((hL x).mp hxL) (And.intro ((hM y).mp hyM) hwEq)
  · intro hw
    cases hw with
    | intro x hx =>
        cases hx with
        | intro y hy =>
            cases hy with
            | intro hxL hrest =>
                cases hrest with
                | intro hyM hwEq =>
                    exists x
                    exists y
                    exact And.intro ((hL x).mpr hxL) (And.intro ((hM y).mpr hyM) hwEq)

theorem star_equal_of_equal {L M : Language alpha}
    (h : Language.Equal L M) :
    Language.Equal (Language.Star L) (Language.Star M) := by
  intro w
  constructor
  · intro hw
    cases hw with
    | intro pieces hpieces =>
        exists pieces
        constructor
        · intro p hp
          exact (h p).mp (hpieces.left p hp)
        · exact hpieces.right
  · intro hw
    cases hw with
    | intro pieces hpieces =>
        exists pieces
        constructor
        · intro p hp
          exact (h p).mpr (hpieces.left p hp)
        · exact hpieces.right

structure RegexNFA (r : RegExp alpha) where
  state : Type
  machine : NFA alpha state
  correct : Language.Equal (NFA.AcceptedLanguage machine) (RegExp.Denote r)

def Compile : (r : RegExp alpha) -> RegexNFA r
  | RegExp.empty =>
      { state := Bool
        machine := EmptyNFA alpha
        correct := emptyNFA_language }
  | RegExp.eps =>
      { state := Bool
        machine := EpsilonNFA alpha
        correct := epsilonNFA_language }
  | RegExp.sym a =>
      { state := Bool
        machine := SymbolNFA a
        correct := symbolNFA_language a }
  | RegExp.alt r s =>
      let cr := Compile r
      let cs := Compile s
      { state := UnionState cr.state cs.state
        machine := UnionNFA cr.machine cs.machine
        correct := Language.equal_trans
          (unionNFA_language cr.machine cs.machine)
          (union_equal_of_equal cr.correct cs.correct) }
  | RegExp.seq r s =>
      let cr := Compile r
      let cs := Compile s
      { state := Sum cr.state cs.state
        machine := ConcatNFA cr.machine cs.machine
        correct := Language.equal_trans
          (concatNFA_language cr.machine cs.machine)
          (concat_equal_of_equal cr.correct cs.correct) }
  | RegExp.star r =>
      let cr := Compile r
      { state := Option cr.state
        machine := StarNFA cr.machine
        correct := Language.equal_trans
          (starNFA_language cr.machine)
          (star_equal_of_equal cr.correct) }

theorem regularExpression_nfa (r : RegExp alpha) :
    NFA.Recognizable (RegExp.Denote r) := by
  let compiled := Compile r
  exists compiled.state
  exists compiled.machine
  exact compiled.correct

end Thompson
end Languages
end FoC
