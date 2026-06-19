import FoC.Languages.Regular

set_option doc.verso true

/-!
# Pumping regular languages

## Pumping decompositions

## Book coordinates

Used by:
- Chapter 3, Section 3.7: Non-regular Languages

This file records the precise quantified property used by the book's pumping
lemma, proves it for DFA-recognizable languages by a finite-state repetition
argument, and transports it to regular languages through the DFA/regular bridge.
-/

namespace FoC
namespace Languages

namespace Pumping

/-!
# Pumping vocabulary

A decomposition splits a long word into prefix, nonempty loop, and suffix, with
the loop repeatable any number of times.
-/

def Decomposition (L : Language alpha) (n : Nat) (w : Word alpha) : Prop :=
  exists x y z : Word alpha,
    w = Word.Concat x (Word.Concat y z) ∧
    Word.Length (Word.Concat x y) <= n ∧
    Word.Length y > 0 ∧
    forall k : Nat, Word.Concat x (Word.Concat (Word.RepeatWord y k) z) ∈ L

def PumpingLength (L : Language alpha) (n : Nat) : Prop :=
  n > 0 ∧ forall w, w ∈ L -> n <= Word.Length w -> Decomposition L n w

def HasPumpingProperty (L : Language alpha) : Prop :=
  exists n, PumpingLength L n

def PumpingLemmaConclusion (L : Language alpha) : Prop :=
  RegularLanguage.Regular L -> HasPumpingProperty L

/-!
# Prefix states

For a DFA run, the list of prefix states has one more entry than the input word
has symbols. A long enough word therefore repeats a state.
-/

def PrefixStatesFrom (M : DFA alpha state) : state -> Word alpha -> List state
  | q, [] => [q]
  | q, a :: w => q :: PrefixStatesFrom M (M.step q a) w

theorem prefixStatesFrom_length (M : DFA alpha state) (q : state) (w : Word alpha) :
    (PrefixStatesFrom M q w).length = Word.Length w + 1 := by
  induction w generalizing q with
  | nil => rfl
  | cons a rest ih =>
      simp [PrefixStatesFrom, Word.Length, ih]

theorem prefixStatesFrom_all_mem (M : DFA alpha state)
    (q : state) (w : Word alpha) {r : state}
    (hr : r ∈ PrefixStatesFrom M q w) : r ∈ M.statesFinite.elems := by
  induction w generalizing q with
  | nil =>
      simp [PrefixStatesFrom] at hr
      rw [hr]
      exact M.statesFinite.complete q
  | cons a rest ih =>
      simp [PrefixStatesFrom] at hr
      cases hr with
      | inl h =>
          rw [h]
          exact M.statesFinite.complete q
      | inr htail =>
          exact ih (M.step q a) htail

theorem prefixStatesFrom_get?_runFrom (M : DFA alpha state)
    (q : state) (w : Word alpha) {i : Nat}
    (hi : i <= Word.Length w) :
    (PrefixStatesFrom M q w)[i]? = some (DFA.RunFrom M q (List.take i w)) := by
  induction w generalizing q i with
  | nil =>
      have hi0 : i = 0 := by simpa [Word.Length] using hi
      rw [hi0]
      rfl
  | cons a rest ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hiRest : i <= Word.Length rest := by
            simpa [Word.Length] using hi
          simpa [PrefixStatesFrom, DFA.RunFrom] using ih (M.step q a) hiRest

theorem duplicate_indices_of_length_gt {α : Type u} [DecidableEq α]
    {xs elems : List α}
    (hlen : elems.length < xs.length)
    (hall : forall a, a ∈ xs -> a ∈ elems) :
    exists i j a, i < j ∧ j < xs.length ∧ xs[i]? = some a ∧ xs[j]? = some a :=
  Foundation.list_duplicate_indices_of_length_gt hlen hall

/-!
# Word splitting at repeated states

Repeated prefix states determine the pumping split. These lemmas reconstruct
the word around the repeated segment and prove the repeated segment is nonempty.
-/

theorem word_split_reconstruct (w : Word alpha) {i j : Nat}
    (hij : i <= j) :
    w = Word.Concat (List.take i w)
      (Word.Concat (List.take (j - i) (List.drop i w)) (List.drop j w)) := by
  have hdrop : List.drop i w =
      Word.Concat (List.take (j - i) (List.drop i w)) (List.drop j w) := by
    calc
      List.drop i w = Word.Concat (List.take (j - i) (List.drop i w))
          (List.drop (j - i) (List.drop i w)) := by
        exact (List.take_append_drop (j - i) (List.drop i w)).symm
      _ = Word.Concat (List.take (j - i) (List.drop i w)) (List.drop j w) := by
        rw [List.drop_drop]
        have hsum : i + (j - i) = j := by omega
        rw [hsum]
  calc
    w = Word.Concat (List.take i w) (List.drop i w) := by
      exact (List.take_append_drop i w).symm
    _ = Word.Concat (List.take i w)
        (Word.Concat (List.take (j - i) (List.drop i w)) (List.drop j w)) := by
      exact congrArg (Word.Concat (List.take i w)) hdrop

theorem word_split_middle_length (w : Word alpha) {i j : Nat}
    (hj : j <= Word.Length w) :
    Word.Length (List.take (j - i) (List.drop i w)) = j - i := by
  have hj' : j <= List.length w := by simpa [Word.Length] using hj
  change (List.take (j - i) (List.drop i w)).length = j - i
  rw [List.length_take, List.length_drop]
  have hle : j - i <= List.length w - i := by omega
  exact Nat.min_eq_left hle

theorem word_split_prefix_length (w : Word alpha) {i j : Nat}
    (hij : i <= j) (hj : j <= Word.Length w) :
    Word.Length (Word.Concat (List.take i w) (List.take (j - i) (List.drop i w))) = j := by
  have hj' : j <= List.length w := by simpa [Word.Length] using hj
  rw [Word.length_concat, word_split_middle_length w hj]
  change (List.take i w).length + (j - i) = j
  rw [List.length_take]
  have hi : i <= List.length w := by omega
  rw [Nat.min_eq_left hi]
  omega

theorem word_split_prefix_eq_take (w : Word alpha) {i j : Nat}
    (hij : i <= j) (hj : j <= Word.Length w) :
    List.take j w =
      Word.Concat (List.take i w) (List.take (j - i) (List.drop i w)) := by
  have hiw : i <= List.length w := by
    have hj' : j <= List.length w := by simpa [Word.Length] using hj
    omega
  calc
    List.take j w = List.take j (List.take i w ++ List.drop i w) := by
      rw [List.take_append_drop i w]
    _ = Word.Concat (List.take i w) (List.take (j - i) (List.drop i w)) := by
      rw [List.take_append]
      rw [List.length_take]
      have hmini : min i (List.length w) = i := by omega
      rw [hmini]
      rw [List.take_take]
      have hminji : min j i = i := by omega
      rw [hminji]
      rfl

theorem runFrom_repeatWord_loop (M : DFA alpha state) (q : state)
    (y : Word alpha) (hloop : DFA.RunFrom M q y = q) (k : Nat) :
    DFA.RunFrom M q (Word.RepeatWord y k) = q := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [Word.repeatWord_succ, DFA.runFrom_append, hloop, ih]

/-!
# DFA pumping lemma

The repeated state in a long DFA run yields a loop that can be traversed any
number of times without changing the accepting state.
-/

theorem dfa_pumpingLength (M : DFA alpha state) :
    PumpingLength (DFA.Language M) (M.statesFinite.elems.length + 1) := by
  classical
  constructor
  · omega
  · intro w hw hlen
    let n := M.statesFinite.elems.length + 1
    let pref : Word alpha := List.take n w
    let states := PrefixStatesFrom M M.start pref
    have hprefLen : Word.Length pref = n := by
      change (List.take n w).length = n
      rw [List.length_take]
      have hnle : n <= List.length w := by
        simpa [n, Word.Length] using hlen
      rw [Nat.min_eq_left hnle]
    have hstatesLen : states.length = n + 1 := by
      simp [states, prefixStatesFrom_length, hprefLen]
    have hmore : M.statesFinite.elems.length < states.length := by
      rw [hstatesLen]
      simp [n]
      omega
    have hall : forall q, q ∈ states -> q ∈ M.statesFinite.elems := by
      intro q hq
      exact prefixStatesFrom_all_mem M M.start pref hq
    cases duplicate_indices_of_length_gt hmore hall with
    | intro i hi =>
        cases hi with
        | intro j hj =>
            cases hj with
            | intro q hq =>
                have hij : i < j := hq.left
                have hjStates : j < states.length := hq.right.left
                have hgeti : states[i]? = some q := hq.right.right.left
                have hgetj : states[j]? = some q := hq.right.right.right
                have hjLeN : j <= n := by
                  rw [hstatesLen] at hjStates
                  omega
                have hiLeN : i <= n := by omega
                have hjLePref : j <= Word.Length pref := by
                  rw [hprefLen]
                  exact hjLeN
                have hiLePref : i <= Word.Length pref := by
                  rw [hprefLen]
                  exact hiLeN
                have hgetiRun :=
                  prefixStatesFrom_get?_runFrom M M.start pref hiLePref
                have hrunIPref : DFA.RunFrom M M.start (List.take i pref) = q := by
                  have hs : some (DFA.RunFrom M M.start (List.take i pref)) = some q := by
                    rw [← hgetiRun]
                    exact hgeti
                  injection hs
                have hgetjRun :=
                  prefixStatesFrom_get?_runFrom M M.start pref hjLePref
                have hrunJPref : DFA.RunFrom M M.start (List.take j pref) = q := by
                  have hs : some (DFA.RunFrom M M.start (List.take j pref)) = some q := by
                    rw [← hgetjRun]
                    exact hgetj
                  injection hs
                have htakeI : List.take i pref = List.take i w := by
                  unfold pref
                  rw [List.take_take]
                  have hmin : min i n = i := by omega
                  rw [hmin]
                have htakeJ : List.take j pref = List.take j w := by
                  unfold pref
                  rw [List.take_take]
                  have hmin : min j n = j := by omega
                  rw [hmin]
                have hrunI : DFA.RunFrom M M.start (List.take i w) = q := by
                  simpa [htakeI] using hrunIPref
                have hrunJ : DFA.RunFrom M M.start (List.take j w) = q := by
                  simpa [htakeJ] using hrunJPref
                let x : Word alpha := List.take i w
                let y : Word alpha := List.take (j - i) (List.drop i w)
                let z : Word alpha := List.drop j w
                have hjLeW : j <= Word.Length w := by
                  have hnle : n <= Word.Length w := hlen
                  omega
                have hxyTake :
                    List.take j w = Word.Concat x y := by
                  simpa [x, y] using
                    word_split_prefix_eq_take (alpha := alpha) w
                      (Nat.le_of_lt hij) hjLeW
                have hrunXY : DFA.RunFrom M M.start (Word.Concat x y) = q := by
                  rw [← hxyTake]
                  exact hrunJ
                have hloop : DFA.RunFrom M (DFA.RunFrom M M.start x) y =
                    DFA.RunFrom M M.start x := by
                  have hloopToQ : DFA.RunFrom M (DFA.RunFrom M M.start x) y = q := by
                    rw [← DFA.runFrom_append]
                    exact hrunXY
                  exact Eq.trans hloopToQ hrunI.symm
                have hrecon :
                    w = Word.Concat x (Word.Concat y z) := by
                  simpa [x, y, z] using
                    word_split_reconstruct (alpha := alpha) w (Nat.le_of_lt hij)
                have hOriginalFromLoop : M.accept (DFA.RunFrom M (DFA.RunFrom M M.start x) z) := by
                  change M.accept (DFA.RunFrom M M.start w) at hw
                  rw [hrecon, DFA.runFrom_append, DFA.runFrom_append, hloop] at hw
                  exact hw
                exists x
                exists y
                exists z
                constructor
                · exact hrecon
                constructor
                · have hlenXY :
                      Word.Length (Word.Concat x y) = j := by
                    simpa [x, y] using
                      word_split_prefix_length (alpha := alpha) w (Nat.le_of_lt hij) hjLeW
                  rw [hlenXY]
                  exact hjLeN
                constructor
                · have hlenY :
                      Word.Length y = j - i := by
                    simpa [y] using
                      word_split_middle_length (alpha := alpha) w hjLeW
                  rw [hlenY]
                  omega
                · intro k
                  change M.accept
                    (DFA.RunFrom M M.start
                      (Word.Concat x (Word.Concat (Word.RepeatWord y k) z)))
                  rw [DFA.runFrom_append, DFA.runFrom_append]
                  have hrepeat := runFrom_repeatWord_loop M
                    (DFA.RunFrom M M.start x) y hloop k
                  rw [hrepeat]
                  exact hOriginalFromLoop

theorem dfa_hasPumpingProperty (M : DFA alpha state) :
    HasPumpingProperty (DFA.Language M) := by
  exists M.statesFinite.elems.length + 1
  exact dfa_pumpingLength M

/-!
# Transfer to regular languages

The DFA pumping property is transported across language equality and then
through the regular-language to DFA-recognizable bridge.
-/

theorem decomposition_original_word_mem {L : Language alpha} {n : Nat} {w : Word alpha}
    (h : Decomposition L n w) : w ∈ L := by
  cases h with
  | intro x hx =>
      cases hx with
      | intro y hy =>
          cases hy with
          | intro z hz =>
              cases hz with
              | intro hwEq hrest =>
                  have hpump := hrest.right.right 1
                  rw [hwEq]
                  simpa [Word.RepeatWord, Word.Concat] using hpump

theorem decomposition_of_equal {L M : Language alpha} {n : Nat} {w : Word alpha}
    (hEq : Language.Equal L M) (h : Decomposition L n w) :
    Decomposition M n w := by
  cases h with
  | intro x hx =>
      cases hx with
      | intro y hy =>
          cases hy with
          | intro z hz =>
              cases hz with
              | intro hwEq hrest =>
                  exists x
                  exists y
                  exists z
                  constructor
                  · exact hwEq
                  constructor
                  · exact hrest.left
                  constructor
                  · exact hrest.right.left
                  · intro k
                    exact (hEq _).mp (hrest.right.right k)

theorem pumpingLength_of_equal {L M : Language alpha} {n : Nat}
    (hEq : Language.Equal L M) (h : PumpingLength L n) :
    PumpingLength M n := by
  constructor
  · exact h.left
  · intro w hw hlen
    exact decomposition_of_equal hEq
      (h.right w ((hEq w).mpr hw) hlen)

theorem hasPumpingProperty_of_equal {L M : Language alpha}
    (hEq : Language.Equal L M) (h : HasPumpingProperty L) :
    HasPumpingProperty M := by
  cases h with
  | intro n hn =>
      exists n
      exact pumpingLength_of_equal hEq hn

theorem dfa_recognizable_hasPumpingProperty {L : Language alpha}
    (hL : RegularLanguage.DFARecognizable L) :
    HasPumpingProperty L := by
  cases hL with
  | intro state hstate =>
      cases hstate with
      | intro M hM =>
          exact hasPumpingProperty_of_equal hM (dfa_hasPumpingProperty M)

theorem regular_hasPumpingProperty {L : Language alpha}
    (hL : RegularLanguage.Regular L) :
    HasPumpingProperty L :=
  dfa_recognizable_hasPumpingProperty
    (RegularLanguage.regular_is_dfa_recognizable hL)

theorem regular_pumpingLemmaConclusion (L : Language alpha) :
    PumpingLemmaConclusion L := by
  intro hreg
  exact regular_hasPumpingProperty hreg

theorem pumpingLength_mono {L : Language alpha} {n m : Nat}
    (hnm : n <= m) (h : PumpingLength L n) :
    PumpingLength L m := by
  constructor
  · exact Nat.lt_of_lt_of_le h.left hnm
  · intro w hw hlen
    cases h.right w hw (Nat.le_trans hnm hlen) with
    | intro x hx =>
        cases hx with
        | intro y hy =>
            cases hy with
            | intro z hz =>
                cases hz with
                | intro hwEq hrest =>
                    exists x
                    exists y
                    exists z
                    constructor
                    · exact hwEq
                    constructor
                    · exact Nat.le_trans hrest.left hnm
                    exact hrest.right

/-!
# Pumping counterexamples

These are the contrapositive tools used in the book examples: exhibit, for
every proposed pumping length, a long word whose every valid split fails.
-/

theorem not_pumpingLength_of_counterexample {L : Language alpha} {n : Nat}
    {w : Word alpha}
    (hw : w ∈ L) (hlen : n <= Word.Length w)
    (hbad :
      forall x y z : Word alpha,
        w = Word.Concat x (Word.Concat y z) ->
        Word.Length (Word.Concat x y) <= n ->
        Word.Length y > 0 ->
        exists k : Nat,
          ¬ Word.Concat x (Word.Concat (Word.RepeatWord y k) z) ∈ L) :
    ¬ PumpingLength L n := by
  intro hpump
  cases hpump.right w hw hlen with
  | intro x hx =>
      cases hx with
      | intro y hy =>
          cases hy with
          | intro z hz =>
              cases hz with
              | intro hwEq hrest =>
                  cases hbad x y z hwEq hrest.left hrest.right.left with
                  | intro k hk =>
                      exact hk (hrest.right.right k)

theorem not_hasPumpingProperty_of_counterexamples {L : Language alpha}
    (hbad :
      forall n : Nat, n > 0 ->
        exists w : Word alpha,
          w ∈ L ∧
          n <= Word.Length w ∧
          forall x y z : Word alpha,
            w = Word.Concat x (Word.Concat y z) ->
            Word.Length (Word.Concat x y) <= n ->
            Word.Length y > 0 ->
            exists k : Nat,
              ¬ Word.Concat x (Word.Concat (Word.RepeatWord y k) z) ∈ L) :
    ¬ HasPumpingProperty L := by
  intro hpump
  cases hpump with
  | intro n hn =>
      cases hbad n hn.left with
      | intro w hw =>
          exact not_pumpingLength_of_counterexample hw.left hw.right.left
            hw.right.right hn

theorem not_regular_of_no_pumping_property {L : Language alpha}
    (pumpingLemma : PumpingLemmaConclusion L)
    (hNoPump : ¬ HasPumpingProperty L) :
    ¬ RegularLanguage.Regular L := by
  intro hreg
  exact hNoPump (pumpingLemma hreg)

theorem not_regular_of_no_pumping_property_regular {L : Language alpha}
    (hNoPump : ¬ HasPumpingProperty L) :
    ¬ RegularLanguage.Regular L :=
  not_regular_of_no_pumping_property (regular_pumpingLemmaConclusion L) hNoPump

end Pumping
end Languages
end FoC
