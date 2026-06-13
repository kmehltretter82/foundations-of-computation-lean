import FoC.Book.Chapter04.Section06.UnarySquares

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
# Section 4.6 powers of two
-/

open Languages
open Grammars

/-!
# Powers of Two

The final example uses a doubling phase: each pass duplicates the current
markers and returns to the left before either doubling again or finishing.
-/

inductive PowerTwoNT where
  | start
  | left
  | h
  | d
  | r
  | boundary
  | markA
deriving DecidableEq

namespace PowerTwoNT

def finite : Foundation.FiniteType PowerTwoNT where
  elems := [start, left, h, d, r, boundary, markA]
  complete := by
    intro A
    cases A <;> simp

end PowerTwoNT

def powN (A : PowerTwoNT) : Symbol SquareTerminal PowerTwoNT :=
  ggNonterminal A

def powT (tok : SquareTerminal) : Symbol SquareTerminal PowerTwoNT :=
  ggTerminal tok

inductive PowerTwoProduces :
    SententialForm SquareTerminal PowerTwoNT ->
      SententialForm SquareTerminal PowerTwoNT -> Prop where
  | start :
      PowerTwoProduces [powN PowerTwoNT.start]
        [powN PowerTwoNT.left, powN PowerTwoNT.h, powN PowerTwoNT.markA,
          powN PowerTwoNT.boundary]
  | beginDouble :
      PowerTwoProduces [powN PowerTwoNT.h] [powN PowerTwoNT.d]
  | duplicate :
      PowerTwoProduces [powN PowerTwoNT.d, powN PowerTwoNT.markA]
        [powN PowerTwoNT.markA, powN PowerTwoNT.markA,
          powN PowerTwoNT.d]
  | turnAround :
      PowerTwoProduces [powN PowerTwoNT.d, powN PowerTwoNT.boundary]
        [powN PowerTwoNT.r, powN PowerTwoNT.boundary]
  | returnLeft :
      PowerTwoProduces [powN PowerTwoNT.markA, powN PowerTwoNT.r]
        [powN PowerTwoNT.r, powN PowerTwoNT.markA]
  | ready :
      PowerTwoProduces [powN PowerTwoNT.left, powN PowerTwoNT.r]
        [powN PowerTwoNT.left, powN PowerTwoNT.h]
  | finishH :
      PowerTwoProduces [powN PowerTwoNT.left, powN PowerTwoNT.h] []
  | finishBoundary :
      PowerTwoProduces [powN PowerTwoNT.boundary] []
  | emitA :
      PowerTwoProduces [powN PowerTwoNT.markA]
        [powT SquareTerminal.a]

def PowerTwoGrammar : GeneralGrammar SquareTerminal PowerTwoNT where
  start := PowerTwoNT.start
  produces := PowerTwoProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, powN,
      ggNonterminal]
  nonterminalsFinite := PowerTwoNT.finite

def PowerTwoProductionList :
    List (GeneralGrammar.Production SquareTerminal PowerTwoNT) :=
  [{ lhs := [powN PowerTwoNT.start],
     rhs := [powN PowerTwoNT.left, powN PowerTwoNT.h,
       powN PowerTwoNT.markA,
       powN PowerTwoNT.boundary] },
   { lhs := [powN PowerTwoNT.h],
     rhs := [powN PowerTwoNT.d] },
   { lhs := [powN PowerTwoNT.d, powN PowerTwoNT.markA],
     rhs := [powN PowerTwoNT.markA, powN PowerTwoNT.markA,
       powN PowerTwoNT.d] },
   { lhs := [powN PowerTwoNT.d, powN PowerTwoNT.boundary],
     rhs := [powN PowerTwoNT.r, powN PowerTwoNT.boundary] },
   { lhs := [powN PowerTwoNT.markA, powN PowerTwoNT.r],
     rhs := [powN PowerTwoNT.r, powN PowerTwoNT.markA] },
   { lhs := [powN PowerTwoNT.left, powN PowerTwoNT.r],
     rhs := [powN PowerTwoNT.left, powN PowerTwoNT.h] },
   { lhs := [powN PowerTwoNT.left, powN PowerTwoNT.h],
     rhs := [] },
   { lhs := [powN PowerTwoNT.boundary],
     rhs := [] },
   { lhs := [powN PowerTwoNT.markA],
     rhs := [powT SquareTerminal.a] }]

/-!
As above, the finite-production theorem only checks that the displayed rules
are exactly the grammar's rules. The final concrete derivation shows the
intended doubling behavior on the word of length four.
-/

theorem powerTwoGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions PowerTwoGrammar := by
  exists PowerTwoProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [PowerTwoProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [PowerTwoProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.start
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.beginDouble
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.duplicate
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.turnAround
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.returnLeft
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.ready
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.finishH
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.finishBoundary
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.emitA

theorem powerTwoGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage PowerTwoGrammar) := by
  exists PowerTwoNT
  exists PowerTwoGrammar
  constructor
  · exact powerTwoGrammar_has_finite_productions
  · intro word
    rfl

def powerTwoMarkerForm (n : Nat) :
    SententialForm SquareTerminal PowerTwoNT :=
  Word.RepeatSymbol (powN PowerTwoNT.markA) n

def powerTwoControlForm (markers : Nat) :
    SententialForm SquareTerminal PowerTwoNT :=
  [powN PowerTwoNT.left, powN PowerTwoNT.h] ++ powerTwoMarkerForm markers ++
    [powN PowerTwoNT.boundary]

def powerTwoWord (n : Nat) : Word SquareTerminal :=
  Word.RepeatSymbol SquareTerminal.a (2 ^ n)

def powerTwoLanguage : Language SquareTerminal :=
  fun word => exists n, word = powerTwoWord n

/-!
**Marker algebra.** The next lemmas formalize the two moving-head phases in the
book grammar. A {name}`PowerTwoNT.d` marker scans right and doubles every
{name}`PowerTwoNT.markA`; a {name}`PowerTwoNT.r` marker then returns left.
-/

theorem powerTwoMarkerForm_succ_eq_append (n : Nat) :
    powerTwoMarkerForm (n + 1) =
      powerTwoMarkerForm n ++ [powN PowerTwoNT.markA] := by
  simpa [powerTwoMarkerForm] using
    repeatSymbol_succ_eq_append (powN PowerTwoNT.markA) n

theorem powerTwo_duplicate_markers_derives
    (n : Nat) (pre suffix : SententialForm SquareTerminal PowerTwoNT) :
    GeneralGrammar.Derives PowerTwoGrammar
      (pre ++ [powN PowerTwoNT.d] ++ powerTwoMarkerForm n ++ suffix)
      (pre ++ powerTwoMarkerForm (n + n) ++ [powN PowerTwoNT.d] ++
        suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [powerTwoMarkerForm, Word.RepeatSymbol, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := PowerTwoGrammar)
          (pre ++ [powN PowerTwoNT.d] ++ suffix))
  | succ n ih =>
      let D := powN PowerTwoNT.d
      let A := powN PowerTwoNT.markA
      have hstep :
          GeneralGrammar.Yields PowerTwoGrammar
            (pre ++ [D, A] ++ powerTwoMarkerForm n ++ suffix)
            (pre ++ [A, A, D] ++ powerTwoMarkerForm n ++ suffix) := by
        simpa [D, A, List.append_assoc] using
          general_yields_of_production (G := PowerTwoGrammar)
            PowerTwoProduces.duplicate pre (powerTwoMarkerForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives PowerTwoGrammar
            (pre ++ [A, A, D] ++ powerTwoMarkerForm n ++ suffix)
            (pre ++ [A, A] ++ powerTwoMarkerForm (n + n) ++ [D] ++
              suffix) := by
        simpa [D, A, List.append_assoc] using
          ih (pre ++ [A, A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      have hmarkers :
          powerTwoMarkerForm ((n + 1) + (n + 1)) =
            [A, A] ++ powerTwoMarkerForm (n + n) := by
        have hnat : (n + 1) + (n + 1) = 2 + (n + n) := by omega
        rw [hnat]
        simpa [powerTwoMarkerForm, A] using
          repeatSymbol_add_eq_concat (powN PowerTwoNT.markA) 2 (n + n)
      have hsuccFront :
          powerTwoMarkerForm (n + 1) = [A] ++ powerTwoMarkerForm n := by
        have hnat : n + 1 = Nat.succ n := by omega
        unfold powerTwoMarkerForm
        rw [hnat]
        rfl
      have hsource :
          pre ++ [D] ++ powerTwoMarkerForm (n + 1) ++ suffix =
            pre ++ [D, A] ++ powerTwoMarkerForm n ++ suffix := by
        rw [hsuccFront]
        simp [List.append_assoc]
      have htarget :
          pre ++ powerTwoMarkerForm ((n + 1) + (n + 1)) ++ [D] ++ suffix =
            pre ++ [A, A] ++ powerTwoMarkerForm (n + n) ++ [D] ++ suffix := by
        rw [hmarkers]
        simp [List.append_assoc]
      rw [hsource, htarget]
      exact hall

theorem powerTwo_return_left_derives
    (n : Nat) (pre suffix : SententialForm SquareTerminal PowerTwoNT) :
    GeneralGrammar.Derives PowerTwoGrammar
      (pre ++ powerTwoMarkerForm n ++ [powN PowerTwoNT.r] ++ suffix)
      (pre ++ [powN PowerTwoNT.r] ++ powerTwoMarkerForm n ++ suffix) := by
  induction n generalizing suffix with
  | zero =>
      simpa [powerTwoMarkerForm, Word.RepeatSymbol, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := PowerTwoGrammar)
          (pre ++ [powN PowerTwoNT.r] ++ suffix))
  | succ n ih =>
      let R := powN PowerTwoNT.r
      let A := powN PowerTwoNT.markA
      have hstep :
          GeneralGrammar.Yields PowerTwoGrammar
            (pre ++ powerTwoMarkerForm n ++ [A, R] ++ suffix)
            (pre ++ powerTwoMarkerForm n ++ [R, A] ++ suffix) := by
        simpa [A, R, List.append_assoc] using
          general_yields_of_production (G := PowerTwoGrammar)
            PowerTwoProduces.returnLeft
            (pre ++ powerTwoMarkerForm n) suffix
      have hrest :
          GeneralGrammar.Derives PowerTwoGrammar
            (pre ++ powerTwoMarkerForm n ++ [R, A] ++ suffix)
            (pre ++ [R] ++ powerTwoMarkerForm n ++ [A] ++ suffix) := by
        simpa [A, R, List.append_assoc] using ih ([A] ++ suffix)
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [powerTwoMarkerForm_succ_eq_append, A, R,
        List.append_assoc] using hall

/-!
**Doubling passes.** One pass changes {lit}`H A^n E` into {lit}`H A^(2n) E`.
Iterating that pass from the single marker introduced by the start production
gives the control form with {lit}`2^n` markers.
-/

theorem powerTwo_doubling_pass_derives (n : Nat) :
    GeneralGrammar.Derives PowerTwoGrammar
      (powerTwoControlForm n)
      (powerTwoControlForm (n + n)) := by
  let L := powN PowerTwoNT.left
  let H := powN PowerTwoNT.h
  let D := powN PowerTwoNT.d
  let R := powN PowerTwoNT.r
  let E := powN PowerTwoNT.boundary
  have hbegin :
      GeneralGrammar.Yields PowerTwoGrammar
        ([L, H] ++ powerTwoMarkerForm n ++ [E])
        ([L, D] ++ powerTwoMarkerForm n ++ [E]) := by
    simpa [L, H, D, E, List.append_assoc] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.beginDouble [L] (powerTwoMarkerForm n ++ [E])
  have hdup :
      GeneralGrammar.Derives PowerTwoGrammar
        ([L, D] ++ powerTwoMarkerForm n ++ [E])
        ([L] ++ powerTwoMarkerForm (n + n) ++ [D, E]) := by
    simpa [L, D, E, List.append_assoc] using
      powerTwo_duplicate_markers_derives n [L] [E]
  have hturn :
      GeneralGrammar.Yields PowerTwoGrammar
        ([L] ++ powerTwoMarkerForm (n + n) ++ [D, E])
        ([L] ++ powerTwoMarkerForm (n + n) ++ [R, E]) := by
    simpa [L, D, R, E, List.append_assoc] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.turnAround
          ([L] ++ powerTwoMarkerForm (n + n)) []
  have hreturn :
      GeneralGrammar.Derives PowerTwoGrammar
        ([L] ++ powerTwoMarkerForm (n + n) ++ [R, E])
        ([L, R] ++ powerTwoMarkerForm (n + n) ++ [E]) := by
    simpa [L, R, E, List.append_assoc] using
      powerTwo_return_left_derives (n + n) [L] [E]
  have hready :
      GeneralGrammar.Yields PowerTwoGrammar
        ([L, R] ++ powerTwoMarkerForm (n + n) ++ [E])
        ([L, H] ++ powerTwoMarkerForm (n + n) ++ [E]) := by
    simpa [L, H, R, E, List.append_assoc] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.ready [] (powerTwoMarkerForm (n + n) ++ [E])
  have hall := GeneralGrammar.Derives.step hbegin
    (GeneralGrammar.derives_trans hdup
      (GeneralGrammar.Derives.step hturn
        (GeneralGrammar.derives_trans hreturn
          (GeneralGrammar.yields_derives hready))))
  simpa [powerTwoControlForm, L, H, D, R, E, List.append_assoc] using hall

theorem powerTwo_start_control_derives :
    GeneralGrammar.Derives PowerTwoGrammar [powN PowerTwoNT.start]
      (powerTwoControlForm 1) := by
  have hstart :
      GeneralGrammar.Yields PowerTwoGrammar [powN PowerTwoNT.start]
        [powN PowerTwoNT.left, powN PowerTwoNT.h,
          powN PowerTwoNT.markA,
          powN PowerTwoNT.boundary] := by
    simpa using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.start [] []
  simpa [powerTwoControlForm, powerTwoMarkerForm, Word.RepeatSymbol,
    List.append_assoc] using GeneralGrammar.yields_derives hstart

theorem powerTwo_control_derives_pow (n : Nat) :
    GeneralGrammar.Derives PowerTwoGrammar [powN PowerTwoNT.start]
      (powerTwoControlForm (2 ^ n)) := by
  induction n with
  | zero =>
      simpa using powerTwo_start_control_derives
  | succ n ih =>
      have hpass := powerTwo_doubling_pass_derives (2 ^ n)
      have hall := GeneralGrammar.derives_trans ih hpass
      have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
        rw [Nat.pow_succ]
        omega
      simpa [hpow] using hall

/-!
**Emitting terminals.** After the control marker decides to stop, the boundary
is removed and each accumulated marker becomes a terminal {lit}`a`.
-/

theorem powerTwo_emit_markers_derives_context
    (n : Nat) (pre suffix : SententialForm SquareTerminal PowerTwoNT) :
    GeneralGrammar.Derives PowerTwoGrammar
      (pre ++ powerTwoMarkerForm n ++ suffix)
      (pre ++ SententialForm.terminalWord
        (Word.RepeatSymbol SquareTerminal.a n) ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [powerTwoMarkerForm, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := PowerTwoGrammar)
          (pre ++ suffix))
  | succ n ih =>
      let A := powN PowerTwoNT.markA
      let a := powT SquareTerminal.a
      have hemit :
          GeneralGrammar.Yields PowerTwoGrammar
            (pre ++ [A] ++ powerTwoMarkerForm n ++ suffix)
            (pre ++ [a] ++ powerTwoMarkerForm n ++ suffix) := by
        simpa [A, a, List.append_assoc] using
          general_yields_of_production (G := PowerTwoGrammar)
            PowerTwoProduces.emitA pre (powerTwoMarkerForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives PowerTwoGrammar
            (pre ++ [a] ++ powerTwoMarkerForm n ++ suffix)
            (pre ++ [a] ++ SententialForm.terminalWord
              (Word.RepeatSymbol SquareTerminal.a n) ++ suffix) := by
        simpa [a, List.append_assoc] using ih (pre ++ [a])
      have hall := GeneralGrammar.Derives.step hemit hrest
      simpa [powerTwoMarkerForm, Word.RepeatSymbol,
        SententialForm.terminalWord, A, a, powT, ggTerminal,
        List.append_assoc] using hall

theorem powerTwo_finish_control_derives (n : Nat) :
    GeneralGrammar.Derives PowerTwoGrammar
      (powerTwoControlForm n)
      (SententialForm.terminalWord
        (Word.RepeatSymbol SquareTerminal.a n)) := by
  let L := powN PowerTwoNT.left
  let H := powN PowerTwoNT.h
  let E := powN PowerTwoNT.boundary
  have hfinishH :
      GeneralGrammar.Yields PowerTwoGrammar
        ([L, H] ++ powerTwoMarkerForm n ++ [E])
        (powerTwoMarkerForm n ++ [E]) := by
    simpa [L, H, E, List.append_assoc] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.finishH [] (powerTwoMarkerForm n ++ [E])
  have hfinishBoundary :
      GeneralGrammar.Yields PowerTwoGrammar
        (powerTwoMarkerForm n ++ [E])
        (powerTwoMarkerForm n) := by
    simpa [E, List.append_assoc] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.finishBoundary (powerTwoMarkerForm n) []
  have hemits :
      GeneralGrammar.Derives PowerTwoGrammar
        (powerTwoMarkerForm n)
        (SententialForm.terminalWord
          (Word.RepeatSymbol SquareTerminal.a n)) := by
    simpa using powerTwo_emit_markers_derives_context n [] []
  have hall := GeneralGrammar.Derives.step hfinishH
    (GeneralGrammar.Derives.step hfinishBoundary hemits)
  simpa [powerTwoControlForm, L, H, E, List.append_assoc] using hall

theorem powerTwo_words_generated (n : Nat) :
    powerTwoWord n ∈ GeneralGrammar.GeneratedLanguage PowerTwoGrammar := by
  have hcontrol := powerTwo_control_derives_pow n
  have hfinish := powerTwo_finish_control_derives (2 ^ n)
  have hall := GeneralGrammar.derives_trans hcontrol hfinish
  simpa [GeneralGrammar.GeneratedLanguage, PowerTwoGrammar, powerTwoWord,
    powN, ggNonterminal] using hall

/-!
**Power-of-two closeout.** The constructive direction now covers the full
family. Exactness is reduced to the remaining soundness statement that every
terminal derivation has power-of-two length.
-/

theorem powerTwo_language_subset_generated {word : Word SquareTerminal}
    (h : word ∈ powerTwoLanguage) :
    word ∈ GeneralGrammar.GeneratedLanguage PowerTwoGrammar := by
  rcases h with ⟨n, hword⟩
  rw [hword]
  exact powerTwo_words_generated n

def PowerTwoGeneratedOnlyLanguageConstruction : Prop :=
  Language.Subset (GeneralGrammar.GeneratedLanguage PowerTwoGrammar)
    powerTwoLanguage

theorem powerTwo_generated_language_exact_of_soundness
    (hsound : PowerTwoGeneratedOnlyLanguageConstruction) :
    Language.Equal (GeneralGrammar.GeneratedLanguage PowerTwoGrammar)
      powerTwoLanguage := by
  intro word
  constructor
  · exact hsound word
  · exact powerTwo_language_subset_generated

/-!
The theorem {name}`powerTwo_words_generated` proves the intended family: after
{lit}`n` doubling passes the grammar derives {lit}`a^(2^n)`. The concrete
{lit}`aaaa` example is just the case {lit}`n = 2`.
-/

theorem powerTwoGrammar_generates_four_as :
    fourAsWord ∈ GeneralGrammar.GeneratedLanguage PowerTwoGrammar := by
  simpa [fourAsWord, powerTwoWord, Word.RepeatSymbol] using
    powerTwo_words_generated 2


end Section06
end Chapter04
end Book
end FoC
