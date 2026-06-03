import FoC.Foundation.Finite
import FoC.Foundation.Countable
import FoC.Languages.Language

set_option doc.verso true

/-!
# Context-free grammars

## Grammar syntax and derivations

This file is the core formal model for Chapter 4.  It represents terminals and
nonterminals as a tagged symbol type, sentential forms as lists of symbols, and
derivations as the reflexive-transitive closure of one-step production use.

## Book coordinates

Used by:
- Chapter 4, Section 4.1: context-free grammar definitions, one-step
  derivation, reflexive-transitive derivation, generated languages, and the
  basic yield laws.
- Chapter 4, Section 4.3: parse trees are related back to derivations.
- Chapter 4, Section 4.6: context-free grammars embed into general grammars.
-/

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace FiniteType

/-!
# Finite helper types

Closure constructions introduce unit and sum nonterminal types. These helpers
carry the finite-witness bookkeeping required by the grammar structures.
-/

def unit : FiniteType Unit where
  elems := [()]
  complete := by
    intro x
    cases x
    exact List.Mem.head []

def sum (left : FiniteType alpha) (right : FiniteType beta) :
    FiniteType (Sum alpha beta) where
  elems := (left.elems.map Sum.inl) ++ (right.elems.map Sum.inr)
  complete := by
    intro x
    cases x with
    | inl a =>
        apply List.mem_append_left
        exact List.mem_map.mpr (Exists.intro a (And.intro (left.complete a) rfl))
    | inr b =>
        apply List.mem_append_right
        exact List.mem_map.mpr (Exists.intro b (And.intro (right.complete b) rfl))

end FiniteType

/-!
# Symbols

A sentential form contains terminals and nonterminals in one tagged type. The
encoding lemmas support the countability arguments for grammars.
-/

inductive Symbol (terminal : Type u) (nonterminal : Type v) where
  | terminal : terminal -> Symbol terminal nonterminal
  | nonterminal : nonterminal -> Symbol terminal nonterminal
deriving DecidableEq

namespace Symbol

def mapNonterminal (f : nt -> nt') :
    Symbol term nt -> Symbol term nt'
  | terminal a => terminal a
  | nonterminal A => nonterminal (f A)

def isTerminal : Symbol term nt -> Prop
  | terminal _ => True
  | nonterminal _ => False

def Code (terminalCode : term -> Nat) (nonterminalCode : nt -> Nat) :
    Symbol term nt -> Nat
  | terminal a => 2 * terminalCode a
  | nonterminal A => 2 * nonterminalCode A + 1

theorem code_injective {terminalCode : term -> Nat}
    {nonterminalCode : nt -> Nat}
    (hterminal : Foundation.Fn.Injective terminalCode)
    (hnonterminal : Foundation.Fn.Injective nonterminalCode) :
    Foundation.Fn.Injective (Code terminalCode nonterminalCode) := by
  intro x y h
  cases x <;> cases y <;> simp [Code] at h ⊢
  · exact hterminal (by omega)
  · omega
  · omega
  · exact hnonterminal (by omega)

theorem encodable
    (hterminal : Foundation.Countability.EncodableByNat term)
    (hnonterminal : Foundation.Countability.EncodableByNat nt) :
    Foundation.Countability.EncodableByNat (Symbol term nt) := by
  rcases hterminal with ⟨terminalCode, hterminalCode⟩
  rcases hnonterminal with ⟨nonterminalCode, hnonterminalCode⟩
  exact ⟨Code terminalCode nonterminalCode,
    code_injective hterminalCode hnonterminalCode⟩

end Symbol

/-!
# Sentential forms

Sentential forms are lists of symbols. This section defines terminal words,
nonterminal maps, terminal-only checks, and conversion back to words.
-/

abbrev SententialForm (terminal : Type u) (nonterminal : Type v) :=
  List (Symbol terminal nonterminal)

namespace SententialForm

def terminalWord (w : Word term) : SententialForm term nt :=
  w.map Symbol.terminal

def mapNonterminal (f : nt -> nt')
    (w : SententialForm term nt) :
    SententialForm term nt' :=
  w.map (Symbol.mapNonterminal f)

def allTerminals : SententialForm term nt -> Prop
  | [] => True
  | Symbol.terminal _ :: rest => allTerminals rest
  | Symbol.nonterminal _ :: _ => False

def toWord? : SententialForm term nt -> Option (Word term)
  | [] => some []
  | Symbol.terminal a :: rest =>
      match toWord? rest with
      | some w => some (a :: w)
      | none => none
  | Symbol.nonterminal _ :: _ => none

theorem terminalWord_append (x y : Word term) :
    terminalWord (nt := nt) (Word.Concat x y) =
      terminalWord x ++ terminalWord y := by
  simp [terminalWord, Word.Concat]

theorem terminalWord_reverse (w : Word term) :
    (terminalWord (nt := nt) w).reverse =
      terminalWord (nt := nt) (Word.Reverse w) := by
  simp [terminalWord, Word.Reverse]

theorem mapNonterminal_append (f : nt -> nt')
    (x y : SententialForm term nt) :
    mapNonterminal f (x ++ y) = mapNonterminal f x ++ mapNonterminal f y := by
  simp [mapNonterminal]

theorem mapNonterminal_terminalWord (f : nt -> nt')
    (w : Word term) :
    mapNonterminal f (terminalWord (nt := nt) w) =
      terminalWord (nt := nt') w := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
      simp [terminalWord, mapNonterminal, Symbol.mapNonterminal]

theorem terminalWord_allTerminals (w : Word term) :
    allTerminals (terminalWord (nt := nt) w) := by
  induction w with
  | nil => trivial
  | cons _ rest ih =>
      exact ih

theorem encodable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.Countability.EncodableByNat
      (SententialForm terminal nonterminal) :=
  Foundation.Countability.list_encodable
    (Symbol.encodable hterminal hnonterminal)

theorem allTerminals_append_of {x y : SententialForm term nt}
    (hx : allTerminals x) (hy : allTerminals y) :
    allTerminals (x ++ y) := by
  induction x with
  | nil =>
      exact hy
  | cons s rest ih =>
      cases s with
      | terminal _ =>
          exact ih hx
      | nonterminal _ =>
          cases hx

theorem terminalWord_toWord (w : Word term) :
    toWord? (terminalWord (nt := nt) w) = some w := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
      change (match toWord? (terminalWord (nt := nt) rest) with
        | some w => some (a :: w)
        | none => none) = some (a :: rest)
      rw [ih]

theorem toWord?_mapNonterminal (f : nt -> nt')
    (w : SententialForm term nt) :
    toWord? (mapNonterminal f w) = toWord? w := by
  induction w with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | terminal a =>
          change (match toWord? (mapNonterminal f rest) with
            | some w => some (a :: w)
            | none => none) =
            match toWord? rest with
            | some w => some (a :: w)
            | none => none
          rw [ih]
      | nonterminal A =>
          rfl

theorem toWord?_append_some {x y : SententialForm term nt}
    {w : Word term} (h : toWord? (x ++ y) = some w) :
    exists wx wy, toWord? x = some wx ∧ toWord? y = some wy ∧
      w = Word.Concat wx wy := by
  induction x generalizing w with
  | nil =>
      exists []
      exists w
  | cons s rest ih =>
      cases s with
      | terminal a =>
          simp [toWord?] at h
          cases hrest : toWord? (rest ++ y) with
          | none =>
              rw [hrest] at h
              cases h
          | some tail =>
              rw [hrest] at h
              cases h
              cases ih hrest with
              | intro wx hwx =>
                  cases hwx with
                  | intro wy hwy =>
                      exists a :: wx
                      exists wy
                      constructor
                      · simp [toWord?, hwy.left]
                      constructor
                      · exact hwy.right.left
                      · simp [Word.Concat, hwy.right.right]
      | nonterminal A =>
          cases h

theorem toWord?_some_eq_terminalWord {x : SententialForm term nt}
    {w : Word term} (h : toWord? x = some w) :
    x = terminalWord w := by
  induction x generalizing w with
  | nil =>
      cases h
      rfl
  | cons s rest ih =>
      cases s with
      | terminal a =>
          simp [toWord?] at h
          cases hrest : toWord? rest with
          | none =>
              rw [hrest] at h
              cases h
          | some tail =>
              rw [hrest] at h
              cases h
              rw [ih hrest]
              rfl
      | nonterminal A =>
          cases h

end SententialForm

/-!
# Grammar structures and finite presentations

A CFG consists of a start nonterminal, a production predicate, and finite
nonterminal data. The finite-presentation records and encodings package the
book's finite list of productions as Lean data.
-/

structure CFG (terminal : Type u) (nonterminal : Type v) where
  start : nonterminal
  produces : nonterminal -> SententialForm terminal nonterminal -> Prop
  nonterminalsFinite : FiniteType nonterminal

namespace CFG

structure Production (terminal : Type u) (nonterminal : Type v) where
  lhs : nonterminal
  rhs : SententialForm terminal nonterminal

namespace Production

def Code (terminalCode : terminal -> Nat) (nonterminalCode : nonterminal -> Nat)
    (rule : Production terminal nonterminal) : Nat :=
  Foundation.Countability.PairCode
    (nonterminalCode rule.lhs)
    (Foundation.Countability.ListCode
      (Symbol.Code terminalCode nonterminalCode) rule.rhs)

theorem code_injective {terminalCode : terminal -> Nat}
    {nonterminalCode : nonterminal -> Nat}
    (hterminal : Foundation.Fn.Injective terminalCode)
    (hnonterminal : Foundation.Fn.Injective nonterminalCode) :
    Foundation.Fn.Injective (Code terminalCode nonterminalCode) := by
  intro x y h
  rcases x with ⟨xLhs, xRhs⟩
  rcases y with ⟨yLhs, yRhs⟩
  rcases Foundation.Countability.pairCode_injective_left h with
    ⟨hlhs, hrhs⟩
  have hLhs : xLhs = yLhs := hnonterminal hlhs
  have hRhs : xRhs = yRhs :=
    Foundation.Countability.listCode_injective
      (Symbol.code_injective hterminal hnonterminal) hrhs
  cases hLhs
  cases hRhs
  rfl

theorem encodable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.Countability.EncodableByNat
      (Production terminal nonterminal) := by
  rcases hterminal with ⟨terminalCode, hterminalCode⟩
  rcases hnonterminal with ⟨nonterminalCode, hnonterminalCode⟩
  exact ⟨Code terminalCode nonterminalCode,
    code_injective hterminalCode hnonterminalCode⟩

end Production

structure FinitePresentationCode (terminal : Type u) (nonterminal : Type v) where
  start : nonterminal
  rules : List (Production terminal nonterminal)

namespace FinitePresentationCode

def Code (terminalCode : terminal -> Nat) (nonterminalCode : nonterminal -> Nat)
    (presentation : FinitePresentationCode terminal nonterminal) : Nat :=
  Foundation.Countability.PairCode
    (nonterminalCode presentation.start)
    (Foundation.Countability.ListCode
      (Production.Code terminalCode nonterminalCode) presentation.rules)

theorem code_injective {terminalCode : terminal -> Nat}
    {nonterminalCode : nonterminal -> Nat}
    (hterminal : Foundation.Fn.Injective terminalCode)
    (hnonterminal : Foundation.Fn.Injective nonterminalCode) :
    Foundation.Fn.Injective (Code terminalCode nonterminalCode) := by
  intro x y h
  rcases x with ⟨xStart, xRules⟩
  rcases y with ⟨yStart, yRules⟩
  rcases Foundation.Countability.pairCode_injective_left h with
    ⟨hstart, hrules⟩
  have hStart : xStart = yStart := hnonterminal hstart
  have hRules : xRules = yRules :=
    Foundation.Countability.listCode_injective
      (Production.code_injective hterminal hnonterminal) hrules
  cases hStart
  cases hRules
  rfl

theorem encodable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.Countability.EncodableByNat
      (FinitePresentationCode terminal nonterminal) := by
  rcases hterminal with ⟨terminalCode, hterminalCode⟩
  rcases hnonterminal with ⟨nonterminalCode, hnonterminalCode⟩
  exact ⟨Code terminalCode nonterminalCode,
    code_injective hterminalCode hnonterminalCode⟩

theorem countable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.FSet.Countable
      (Foundation.FSet.Univ :
        Foundation.FSet (FinitePresentationCode terminal nonterminal)) :=
  Foundation.Countability.countable_univ_of_encodableByNat
    (encodable hterminal hnonterminal)

end FinitePresentationCode

namespace ProductionList

def MaxRhsLength : List (Production terminal nonterminal) -> Nat
  | [] => 0
  | rule :: rules => Nat.max rule.rhs.length (MaxRhsLength rules)

theorem rhs_length_le_max {rule : Production terminal nonterminal}
    {rules : List (Production terminal nonterminal)}
    (h : rule ∈ rules) :
    rule.rhs.length <= MaxRhsLength rules := by
  induction rules with
  | nil =>
      cases h
  | cons head tail ih =>
      cases h with
      | head =>
          exact Nat.le_max_left _ _
      | tail _ htail =>
          have hle := ih htail
          exact Nat.le_trans hle (Nat.le_max_right _ _)

end ProductionList

def HasFiniteProductions (G : CFG terminal nonterminal) : Prop :=
  exists rules : List (Production terminal nonterminal),
    forall A rhs,
      G.produces A rhs <->
        exists rule, rule ∈ rules ∧ rule.lhs = A ∧ rule.rhs = rhs

/-!
# Production bounds

Finite production lists have a maximum right-hand-side length. That bound is
used later in pumping and finite-presentation arguments.
-/

theorem finiteProductions_rhs_length_bound
    {G : CFG terminal nonterminal}
    (hG : HasFiniteProductions G) :
    exists B : Nat,
      B > 0 ∧ forall A rhs, G.produces A rhs -> rhs.length < B := by
  cases hG with
  | intro rules hrules =>
      exists ProductionList.MaxRhsLength rules + 1
      constructor
      · omega
      · intro A rhs hprod
        cases (hrules A rhs).mp hprod with
        | intro rule hrule =>
            have hlen := ProductionList.rhs_length_le_max hrule.left
            rw [← hrule.right.right]
            omega

/-!
# Derivations and generated languages

One-step yields replace a single nonterminal occurrence by a right-hand side.
Derivations are the reflexive-transitive closure, and generated languages are
terminal words reachable from the start nonterminal.
-/

def Yields (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  exists u, exists v, exists A, exists rhs,
    G.produces A rhs ∧
      x = u ++ [Symbol.nonterminal A] ++ v ∧
      y = u ++ rhs ++ v

inductive Derives (G : CFG terminal nonterminal) :
    SententialForm terminal nonterminal -> SententialForm terminal nonterminal -> Prop where
  | refl (x : SententialForm terminal nonterminal) : Derives G x x
  | step {x y z : SententialForm terminal nonterminal} :
      Yields G x y -> Derives G y z -> Derives G x z

def GeneratedLanguage (G : CFG terminal nonterminal) : Language terminal :=
  fun w => Derives G [Symbol.nonterminal G.start] (SententialForm.terminalWord w)

def GeneratedFrom (G : CFG terminal nonterminal) (A : nonterminal) : Language terminal :=
  fun w => Derives G [Symbol.nonterminal A] (SententialForm.terminalWord w)

def DerivationSymbolLanguage (G : CFG terminal nonterminal) :
    Symbol terminal nonterminal -> Language terminal
  | Symbol.terminal a => Language.Singleton (Word.Symbol a)
  | Symbol.nonterminal A => GeneratedFrom G A

def FormLanguage (symbolLanguage : Symbol terminal nonterminal -> Language terminal) :
    SententialForm terminal nonterminal -> Language terminal
  | [] => Language.Singleton Word.Empty
  | s :: rest => Language.Concat (symbolLanguage s) (FormLanguage symbolLanguage rest)

def ContextFree (L : Language terminal) : Prop :=
  exists nonterminal : Type, exists G : CFG terminal nonterminal,
    Language.Equal (GeneratedLanguage G) L

def Equivalent (G H : CFG terminal nonterminal) : Prop :=
  Language.Equal (GeneratedLanguage G) (GeneratedLanguage H)

/-!
# Regular grammar shapes

Right-regular and left-regular grammars are classified by the shape of every
production right-hand side.
-/

inductive RightRegularRHS : SententialForm terminal nonterminal -> Prop where
  | epsilon : RightRegularRHS []
  | nonterminal (A : nonterminal) :
      RightRegularRHS [Symbol.nonterminal A]
  | terminalThenNonterminal (a : terminal) (A : nonterminal) :
      RightRegularRHS [Symbol.terminal a, Symbol.nonterminal A]

def RightRegular (G : CFG terminal nonterminal) : Prop :=
  forall A rhs, G.produces A rhs -> RightRegularRHS rhs

inductive LeftRegularRHS : SententialForm terminal nonterminal -> Prop where
  | epsilon : LeftRegularRHS []
  | nonterminal (A : nonterminal) :
      LeftRegularRHS [Symbol.nonterminal A]
  | nonterminalThenTerminal (A : nonterminal) (a : terminal) :
      LeftRegularRHS [Symbol.nonterminal A, Symbol.terminal a]

def LeftRegular (G : CFG terminal nonterminal) : Prop :=
  forall A rhs, G.produces A rhs -> LeftRegularRHS rhs

/-!
# Reverse grammars and derivation algebra

Reversing each production right-hand side defines the reverse grammar. The
following derivation lemmas provide context, transitivity, and word-level
reasoning used by parse-tree and closure constructions.
-/

def ReverseGrammar (G : CFG terminal nonterminal) :
    CFG terminal nonterminal where
  start := G.start
  produces := fun A rhs =>
    exists original, G.produces A original ∧ rhs = original.reverse
  nonterminalsFinite := G.nonterminalsFinite

theorem derives_refl (G : CFG terminal nonterminal)
    (x : SententialForm terminal nonterminal) : Derives G x x :=
  Derives.refl x

theorem yields_derives {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Yields G x y) :
    Derives G x y :=
  Derives.step h (Derives.refl y)

theorem derives_trans {G : CFG terminal nonterminal}
    {x y z : SententialForm terminal nonterminal}
    (hxy : Derives G x y) (hyz : Derives G y z) : Derives G x z := by
  induction hxy with
  | refl _ => exact hyz
  | step hstep _ ih => exact Derives.step hstep (ih hyz)

theorem yields_context {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Yields G x y)
    (s t : SententialForm terminal nonterminal) :
    Yields G (s ++ x ++ t) (s ++ y ++ t) := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          exists s ++ u
                          exists v ++ t
                          exists A
                          exists rhs
                          constructor
                          · exact hprod
                          constructor
                          · rw [hx]
                            simp [List.append_assoc]
                          · rw [hy]
                            simp [List.append_assoc]

theorem reverseGrammar_hasFiniteProductions
    {G : CFG terminal nonterminal}
    (hG : HasFiniteProductions G) :
    HasFiniteProductions (ReverseGrammar G) := by
  cases hG with
  | intro rules hrules =>
      exists rules.map
        (fun rule : Production terminal nonterminal =>
          { lhs := rule.lhs, rhs := rule.rhs.reverse })
      intro A rhs
      constructor
      · intro hprod
        cases hprod with
        | intro original horiginal =>
            cases (hrules A original).mp horiginal.left with
            | intro rule hrule =>
                exists { lhs := rule.lhs, rhs := rule.rhs.reverse }
                constructor
                · apply List.mem_map.mpr
                  exists rule
                  exact ⟨hrule.left, rfl⟩
                constructor
                · rw [hrule.right.left]
                · rw [horiginal.right, hrule.right.right]
      · intro hrule
        cases hrule with
        | intro reversedRule hreversedRule =>
            have hmem :=
              List.mem_map.mp hreversedRule.left
            cases hmem with
            | intro rule hrule =>
                rw [← hrule.right] at hreversedRule
                exists rule.rhs
                constructor
                · exact (hrules A rule.rhs).mpr
                    ⟨rule, hrule.left, hreversedRule.right.left, rfl⟩
                · exact hreversedRule.right.right.symm

theorem reverseGrammar_yields {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Yields G x y) :
    Yields (ReverseGrammar G) x.reverse y.reverse := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  exists v.reverse
                  exists u.reverse
                  exists A
                  exists rhs.reverse
                  constructor
                  · exists rhs
                    exact ⟨hrhs.left, rfl⟩
                  constructor
                  · rw [hrhs.right.left]
                    simp [List.reverse_append]
                  · rw [hrhs.right.right]
                    simp [List.reverse_append, List.append_assoc]

theorem reverseGrammar_yields_inv {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Yields (ReverseGrammar G) x y) :
    Yields G x.reverse y.reverse := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs.left with
                  | intro original horiginal =>
                      exists v.reverse
                      exists u.reverse
                      exists A
                      exists original
                      constructor
                      · exact horiginal.left
                      constructor
                      · rw [hrhs.right.left]
                        simp [List.reverse_append]
                      · rw [hrhs.right.right, horiginal.right]
                        simp [List.reverse_append, List.append_assoc]

theorem reverseGrammar_derives {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Derives G x y) :
    Derives (ReverseGrammar G) x.reverse y.reverse := by
  induction h with
  | refl x =>
      exact Derives.refl x.reverse
  | step hstep _ ih =>
      exact Derives.step (reverseGrammar_yields hstep) ih

theorem reverseGrammar_derives_inv {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Derives (ReverseGrammar G) x y) :
    Derives G x.reverse y.reverse := by
  induction h with
  | refl x =>
      exact Derives.refl x.reverse
  | step hstep _ ih =>
      exact Derives.step (reverseGrammar_yields_inv hstep) ih

theorem reverseGrammar_generates {G : CFG terminal nonterminal}
    {w : Word terminal} (h : w ∈ GeneratedLanguage G) :
    Word.Reverse w ∈ GeneratedLanguage (ReverseGrammar G) := by
  have hrev := reverseGrammar_derives h
  simpa [GeneratedLanguage, SententialForm.terminalWord_reverse] using hrev

theorem reverseGrammar_generates_inv {G : CFG terminal nonterminal}
    {w : Word terminal} (h : w ∈ GeneratedLanguage (ReverseGrammar G)) :
    Word.Reverse w ∈ GeneratedLanguage G := by
  have hrev := reverseGrammar_derives_inv h
  simpa [GeneratedLanguage, SententialForm.terminalWord_reverse] using hrev

theorem reverseGrammar_language_exact (G : CFG terminal nonterminal) :
    Language.Equal (GeneratedLanguage (ReverseGrammar G))
      (Language.Reverse (GeneratedLanguage G)) := by
  intro w
  constructor
  · exact reverseGrammar_generates_inv
  · intro hw
    have hgen := reverseGrammar_generates (G := G) hw
    simpa [Word.Reverse] using hgen

theorem leftRegular_reverseGrammar_rightRegular
    {G : CFG terminal nonterminal}
    (hG : LeftRegular G) :
    RightRegular (ReverseGrammar G) := by
  intro A rhs hprod
  cases hprod with
  | intro original horiginal =>
      rw [horiginal.right]
      cases hG A original horiginal.left with
      | epsilon =>
          exact RightRegularRHS.epsilon
      | nonterminal B =>
          exact RightRegularRHS.nonterminal B
      | nonterminalThenTerminal B a =>
          exact RightRegularRHS.terminalThenNonterminal a B

theorem rightRegular_reverseGrammar_leftRegular
    {G : CFG terminal nonterminal}
    (hG : RightRegular G) :
    LeftRegular (ReverseGrammar G) := by
  intro A rhs hprod
  cases hprod with
  | intro original horiginal =>
      rw [horiginal.right]
      cases hG A original horiginal.left with
      | epsilon =>
          exact LeftRegularRHS.epsilon
      | nonterminal B =>
          exact LeftRegularRHS.nonterminal B
      | terminalThenNonterminal a B =>
          exact LeftRegularRHS.nonterminalThenTerminal B a

theorem derives_context {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Derives G x y)
    (s t : SententialForm terminal nonterminal) :
    Derives G (s ++ x ++ t) (s ++ y ++ t) := by
  induction h with
  | refl _ => exact Derives.refl _
  | step hstep _ ih => exact Derives.step (yields_context hstep s t) ih

theorem derives_append_left {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Derives G x y)
    (s : SententialForm terminal nonterminal) :
    Derives G (s ++ x) (s ++ y) := by
  simpa using derives_context h s []

theorem derives_append_right {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Derives G x y)
    (t : SententialForm terminal nonterminal) :
    Derives G (x ++ t) (y ++ t) := by
  simpa using derives_context h [] t

theorem derives_pumped_loop {G : CFG terminal nonterminal}
    {A : nonterminal} {x y z : Word terminal}
    (hloop :
      Derives G [Symbol.nonterminal A]
        (SententialForm.terminalWord x ++ [Symbol.nonterminal A] ++
          SententialForm.terminalWord z))
    (hbase :
      Derives G [Symbol.nonterminal A] (SententialForm.terminalWord y)) :
    forall n : Nat,
      Derives G [Symbol.nonterminal A]
        (SententialForm.terminalWord
          (Word.Concat (Word.RepeatWord x n)
            (Word.Concat y (Word.RepeatWord z n)))) := by
  intro n
  induction n with
  | zero =>
      simpa [Word.RepeatWord, Word.Concat] using hbase
  | succ n ih =>
      have hctx :
          Derives G
            (SententialForm.terminalWord x ++ [Symbol.nonterminal A] ++
              SententialForm.terminalWord z)
            (SententialForm.terminalWord x ++
              SententialForm.terminalWord
                (Word.Concat (Word.RepeatWord x n)
                  (Word.Concat y (Word.RepeatWord z n))) ++
              SententialForm.terminalWord z) := by
        simpa [List.append_assoc] using
          derives_context ih (SententialForm.terminalWord x)
            (SententialForm.terminalWord z)
      have hAll := derives_trans hloop hctx
      have htarget :
          SententialForm.terminalWord (nt := nonterminal) x ++
              SententialForm.terminalWord (nt := nonterminal)
                (Word.Concat (Word.RepeatWord x n)
                  (Word.Concat y (Word.RepeatWord z n))) ++
              SententialForm.terminalWord (nt := nonterminal) z =
            SententialForm.terminalWord (nt := nonterminal)
              (Word.Concat (Word.RepeatWord x (n + 1))
                (Word.Concat y (Word.RepeatWord z (n + 1)))) := by
        simp [SententialForm.terminalWord, Word.Concat, Word.RepeatWord,
          List.append_assoc]
        simpa [Word.Concat] using
          congrArg
            (fun w : Word terminal =>
              w.map (Symbol.terminal (nonterminal := nonterminal)))
            (Word.repeatWord_concat_self z n)
      rw [← htarget]
      exact hAll

theorem generated_language_mem (G : CFG terminal nonterminal) (w : Word terminal) :
    w ∈ GeneratedLanguage G <->
      Derives G [Symbol.nonterminal G.start] (SententialForm.terminalWord w) :=
  Iff.rfl

theorem formLanguage_empty
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal) :
    Word.Empty ∈ FormLanguage symbolLanguage [] :=
  rfl

theorem formLanguage_append
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (x y : SententialForm terminal nonterminal) :
    Language.Equal (FormLanguage symbolLanguage (x ++ y))
      (Language.Concat (FormLanguage symbolLanguage x) (FormLanguage symbolLanguage y)) := by
  induction x with
  | nil =>
      intro w
      constructor
      · intro hw
        exists Word.Empty
        exists w
      · intro hw
        cases hw with
        | intro wx hwx =>
            cases hwx with
            | intro wy hwy =>
                cases hwy.left
                cases hwy.right.right
                exact hwy.right.left
  | cons s rest ih =>
      intro w
      constructor
      · intro hw
        cases hw with
        | intro first hfirst =>
            cases hfirst with
            | intro tail htail =>
                have htailSplit := (ih tail).mp htail.right.left
                cases htailSplit with
                | intro restWord hrestWord =>
                    cases hrestWord with
                    | intro yWord hyWord =>
                        exists Word.Concat first restWord
                        exists yWord
                        constructor
                        · exists first
                          exists restWord
                          exact And.intro htail.left
                            (And.intro hyWord.left rfl)
                        constructor
                        · exact hyWord.right.left
                        · calc
                            w = Word.Concat first tail := htail.right.right
                            _ = Word.Concat first (Word.Concat restWord yWord) := by
                              rw [hyWord.right.right]
                            _ = Word.Concat (Word.Concat first restWord) yWord := by
                              rw [← Word.concat_assoc]
      · intro hw
        cases hw with
        | intro pref hp =>
            cases hp with
            | intro suffix hs =>
                cases hs.left with
                | intro first hfirst =>
                    cases hfirst with
                    | intro restWord hrestWord =>
                        have htail : Word.Concat restWord suffix ∈
                            FormLanguage symbolLanguage (rest ++ y) :=
                          (ih (Word.Concat restWord suffix)).mpr
                            (Exists.intro restWord
                              (Exists.intro suffix
                                (And.intro hrestWord.right.left
                                  (And.intro hs.right.left rfl))))
                        exists first
                        exists Word.Concat restWord suffix
                        constructor
                        · exact hrestWord.left
                        constructor
                        · exact htail
                        · calc
                            w = Word.Concat pref suffix := hs.right.right
                            _ = Word.Concat (Word.Concat first restWord) suffix := by
                              rw [hrestWord.right.right]
                            _ = Word.Concat first (Word.Concat restWord suffix) := by
                              rw [Word.concat_assoc]

theorem formLanguage_replace_sound
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    {u rhs v : SententialForm terminal nonterminal}
    {A : nonterminal} {w : Word terminal}
    (hlocal : forall x, x ∈ FormLanguage symbolLanguage rhs ->
      x ∈ symbolLanguage (Symbol.nonterminal A))
    (hw : w ∈ FormLanguage symbolLanguage (u ++ rhs ++ v)) :
    w ∈ FormLanguage symbolLanguage (u ++ [Symbol.nonterminal A] ++ v) := by
  have hu := (formLanguage_append symbolLanguage u (rhs ++ v) w).mp (by
    simpa [List.append_assoc] using hw)
  cases hu with
  | intro pref hp =>
      cases hp with
      | intro suffix hs =>
          have hsSplit := (formLanguage_append symbolLanguage rhs v suffix).mp hs.right.left
          cases hsSplit with
          | intro middle hm =>
              cases hm with
              | intro tail ht =>
                  have hnew : w ∈ FormLanguage symbolLanguage
                      (u ++ ([Symbol.nonterminal A] ++ v)) := by
                    apply (formLanguage_append symbolLanguage u
                      ([Symbol.nonterminal A] ++ v) w).mpr
                    exists pref
                    exists Word.Concat middle tail
                    constructor
                    · exact hs.left
                    constructor
                    · exists middle
                      exists tail
                      exact And.intro (hlocal middle ht.left)
                        (And.intro ht.right.left rfl)
                    · calc
                        w = Word.Concat pref suffix := hs.right.right
                        _ = Word.Concat pref (Word.Concat middle tail) := by
                          rw [ht.right.right]
                  simpa [List.append_assoc] using hnew

theorem terminalWord_mem_formLanguage
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hterminal : forall a, Word.Symbol a ∈ symbolLanguage (Symbol.terminal a))
    (w : Word terminal) :
    w ∈ FormLanguage symbolLanguage (SententialForm.terminalWord (nt := nonterminal) w) := by
  induction w with
  | nil =>
      rfl
  | cons a rest ih =>
      exists [a]
      exists rest
      constructor
      · exact hterminal a
      constructor
      · exact ih
      · rfl

theorem formLanguage_derives {G : CFG terminal nonterminal}
    {sf : SententialForm terminal nonterminal} {w : Word terminal}
    (h : w ∈ FormLanguage (DerivationSymbolLanguage G) sf) :
    Derives G sf (SententialForm.terminalWord w) := by
  induction sf generalizing w with
  | nil =>
      cases h
      exact Derives.refl []
  | cons s rest ih =>
      cases h with
      | intro first hfirst =>
          cases hfirst with
          | intro tail htail =>
              have hrest := ih htail.right.left
              cases s with
              | terminal a =>
                  have hfirstEq : first = [a] := htail.left
                  rw [htail.right.right, hfirstEq]
                  change Derives G (Symbol.terminal a :: rest)
                    (SententialForm.terminalWord (Word.Concat [a] tail))
                  have hctx := derives_context hrest [Symbol.terminal a] []
                  rw [SententialForm.terminalWord_append]
                  simpa [SententialForm.terminalWord] using hctx
              | nonterminal A =>
                  have hsym : Derives G [Symbol.nonterminal A]
                      (SententialForm.terminalWord first) := htail.left
                  rw [htail.right.right]
                  change Derives G (Symbol.nonterminal A :: rest)
                    (SententialForm.terminalWord (Word.Concat first tail))
                  have hleft :
                      Derives G (Symbol.nonterminal A :: rest)
                        (SententialForm.terminalWord first ++ rest) := by
                    simpa using derives_context hsym [] rest
                  have hright :
                      Derives G (SententialForm.terminalWord first ++ rest)
                        (SententialForm.terminalWord first ++
                          SententialForm.terminalWord tail) := by
                    simpa using derives_context hrest (SententialForm.terminalWord first) []
                  rw [SententialForm.terminalWord_append]
                  exact derives_trans hleft hright

theorem context_free_of_equal {L M : Language terminal}
    (hL : ContextFree L) (hEq : Language.Equal L M) : ContextFree M := by
  cases hL with
  | intro nt hnt =>
      cases hnt with
      | intro G hG =>
          exists nt
          exists G
          exact Language.equal_trans hG hEq

def mapYieldsNonterminal
    (f : nonterminal -> nonterminal')
    (G : CFG terminal nonterminal)
    (H : CFG terminal nonterminal')
    (hprod :
      forall A rhs, G.produces A rhs ->
        H.produces (f A) (SententialForm.mapNonterminal f rhs))
    {x y : SententialForm terminal nonterminal}
    (h : Yields G x y) :
    Yields H (SententialForm.mapNonterminal f x)
      (SententialForm.mapNonterminal f y) := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hAprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          exists SententialForm.mapNonterminal f u
                          exists SententialForm.mapNonterminal f v
                          exists f A
                          exists SententialForm.mapNonterminal f rhs
                          constructor
                          · exact hprod A rhs hAprod
                          constructor
                          · rw [hx]
                            simp [SententialForm.mapNonterminal, Symbol.mapNonterminal,
                              List.map_append]
                          · rw [hy]
                            simp [SententialForm.mapNonterminal, List.map_append]

def mapDerivesNonterminal
    (f : nonterminal -> nonterminal')
    (G : CFG terminal nonterminal)
    (H : CFG terminal nonterminal')
    (hprod :
      forall A rhs, G.produces A rhs ->
        H.produces (f A) (SententialForm.mapNonterminal f rhs))
    {x y : SententialForm terminal nonterminal}
    (h : Derives G x y) :
    Derives H (SententialForm.mapNonterminal f x)
      (SententialForm.mapNonterminal f y) := by
  induction h with
  | refl _ => exact Derives.refl _
  | step hstep _ ih =>
      exact Derives.step (mapYieldsNonterminal f G H hprod hstep) ih

inductive SumStart (left right : Type u) where
  | start : SumStart left right
  | inLeft : left -> SumStart left right
  | inRight : right -> SumStart left right

namespace SumStart

def finite (left : FiniteType alpha) (right : FiniteType beta) :
    FiniteType (SumStart alpha beta) where
  elems := [SumStart.start] ++
    (left.elems.map SumStart.inLeft) ++ (right.elems.map SumStart.inRight)
  complete := by
    intro x
    cases x with
    | start =>
        exact List.Mem.head _
    | inLeft a =>
        apply List.Mem.tail
        apply List.mem_append_left
        exact List.mem_map.mpr (Exists.intro a (And.intro (left.complete a) rfl))
    | inRight b =>
        apply List.Mem.tail
        apply List.mem_append_right
        exact List.mem_map.mpr (Exists.intro b (And.intro (right.complete b) rfl))

end SumStart

def inLeftSymbol (s : Symbol terminal left) : Symbol terminal (SumStart left right) :=
  Symbol.mapNonterminal SumStart.inLeft s

def inRightSymbol (s : Symbol terminal right) : Symbol terminal (SumStart left right) :=
  Symbol.mapNonterminal SumStart.inRight s

def inLeftForm (w : SententialForm terminal left) :
    SententialForm terminal (SumStart left right) :=
  SententialForm.mapNonterminal SumStart.inLeft w

def inRightForm (w : SententialForm terminal right) :
    SententialForm terminal (SumStart left right) :=
  SententialForm.mapNonterminal SumStart.inRight w

theorem inLeftForm_no_start (x : SententialForm terminal left) :
    ¬ Symbol.nonterminal (SumStart.start : SumStart left right) ∈
      inLeftForm (right := right) x := by
  induction x with
  | nil =>
      intro h
      cases h
  | cons s rest ih =>
      intro h
      cases s with
      | terminal a =>
          cases h with
          | tail _ htail => exact ih htail
      | nonterminal A =>
          cases h with
          | tail _ htail => exact ih htail

theorem inRightForm_no_start (y : SententialForm terminal right) :
    ¬ Symbol.nonterminal (SumStart.start : SumStart left right) ∈
      inRightForm (left := left) y := by
  induction y with
  | nil =>
      intro h
      cases h
  | cons s rest ih =>
      intro h
      cases s with
      | terminal a =>
          cases h with
          | tail _ htail => exact ih htail
      | nonterminal A =>
          cases h with
          | tail _ htail => exact ih htail

theorem inLeftForm_no_inRight (A : right) (x : SententialForm terminal left) :
    ¬ Symbol.nonterminal (SumStart.inRight A : SumStart left right) ∈
      inLeftForm x := by
  induction x with
  | nil =>
      intro h
      cases h
  | cons s rest ih =>
      intro h
      cases s with
      | terminal a =>
          cases h with
          | tail _ htail => exact ih htail
      | nonterminal B =>
          cases h with
          | tail _ htail => exact ih htail

theorem inRightForm_no_inLeft (A : left) (y : SententialForm terminal right) :
    ¬ Symbol.nonterminal (SumStart.inLeft A : SumStart left right) ∈
      inRightForm y := by
  induction y with
  | nil =>
      intro h
      cases h
  | cons s rest ih =>
      intro h
      cases s with
      | terminal a =>
          cases h with
          | tail _ htail => exact ih htail
      | nonterminal B =>
          cases h with
          | tail _ htail => exact ih htail

inductive UnionProduces (G : CFG terminal left) (H : CFG terminal right) :
    SumStart left right -> SententialForm terminal (SumStart left right) -> Prop where
  | chooseLeft :
      UnionProduces G H SumStart.start [Symbol.nonterminal (SumStart.inLeft G.start)]
  | chooseRight :
      UnionProduces G H SumStart.start [Symbol.nonterminal (SumStart.inRight H.start)]
  | leftRule {A rhs} :
      G.produces A rhs -> UnionProduces G H (SumStart.inLeft A) (inLeftForm rhs)
  | rightRule {A rhs} :
      H.produces A rhs -> UnionProduces G H (SumStart.inRight A) (inRightForm rhs)

def UnionGrammar (G : CFG terminal left) (H : CFG terminal right) :
    CFG terminal (SumStart left right) where
  start := SumStart.start
  produces := UnionProduces G H
  nonterminalsFinite := SumStart.finite G.nonterminalsFinite H.nonterminalsFinite

def unionChooseLeftProduction (G : CFG terminal left) :
    Production terminal (SumStart left right) where
  lhs := SumStart.start
  rhs := [Symbol.nonterminal (SumStart.inLeft G.start)]

def unionChooseRightProduction (H : CFG terminal right) :
    Production terminal (SumStart left right) where
  lhs := SumStart.start
  rhs := [Symbol.nonterminal (SumStart.inRight H.start)]

def unionLeftProduction (rule : Production terminal left) :
    Production terminal (SumStart left right) where
  lhs := SumStart.inLeft rule.lhs
  rhs := inLeftForm rule.rhs

def unionRightProduction (rule : Production terminal right) :
    Production terminal (SumStart left right) where
  lhs := SumStart.inRight rule.lhs
  rhs := inRightForm rule.rhs

theorem union_hasFiniteProductions
    {G : CFG terminal left} {H : CFG terminal right}
    (hG : HasFiniteProductions G) (hH : HasFiniteProductions H) :
    HasFiniteProductions (UnionGrammar G H) := by
  cases hG with
  | intro rulesG hrulesG =>
      cases hH with
      | intro rulesH hrulesH =>
          exists [unionChooseLeftProduction (right := right) G,
            unionChooseRightProduction (left := left) H] ++
            rulesG.map (unionLeftProduction (right := right)) ++
            rulesH.map (unionRightProduction (left := left))
          intro A rhs
          constructor
          · intro h
            cases h with
            | chooseLeft =>
                exists unionChooseLeftProduction (right := right) G
                simp [unionChooseLeftProduction]
            | chooseRight =>
                exists unionChooseRightProduction (left := left) H
                simp [unionChooseRightProduction]
            | leftRule hprod =>
                cases (hrulesG _ _).mp hprod with
                | intro rule hrule =>
                    exists unionLeftProduction (right := right) rule
                    constructor
                    · apply List.mem_append_left
                      apply List.mem_append_right
                      exact List.mem_map.mpr
                        (Exists.intro rule (And.intro hrule.left rfl))
                    · constructor
                      · simp [unionLeftProduction, hrule.right.left]
                      · simp [unionLeftProduction, hrule.right.right]
            | rightRule hprod =>
                cases (hrulesH _ _).mp hprod with
                | intro rule hrule =>
                    exists unionRightProduction (left := left) rule
                    constructor
                    · apply List.mem_append_right
                      exact List.mem_map.mpr
                        (Exists.intro rule (And.intro hrule.left rfl))
                    · constructor
                      · simp [unionRightProduction, hrule.right.left]
                      · simp [unionRightProduction, hrule.right.right]
          · intro h
            cases h with
            | intro rule hrule =>
                have hmem := hrule.left
                simp [unionChooseLeftProduction, unionChooseRightProduction,
                  unionLeftProduction, unionRightProduction] at hmem
                cases hmem with
                | inl hleft =>
                    rw [← hrule.right.left, ← hrule.right.right, hleft]
                    exact UnionProduces.chooseLeft
                | inr hrest =>
                    cases hrest with
                    | inl hright =>
                        rw [← hrule.right.left, ← hrule.right.right, hright]
                        exact UnionProduces.chooseRight
                    | inr hrest' =>
                        cases hrest' with
                        | inl hleftRule =>
                            cases hleftRule with
                            | intro base hbase =>
                                cases hbase with
                                | intro hbaseMem hbaseEq =>
                                    rw [← hrule.right.left, ← hrule.right.right, ← hbaseEq]
                                    exact UnionProduces.leftRule
                                      ((hrulesG base.lhs base.rhs).mpr
                                        (Exists.intro base
                                          (And.intro hbaseMem
                                            (And.intro rfl rfl))))
                        | inr hrightRule =>
                            cases hrightRule with
                            | intro base hbase =>
                                cases hbase with
                                | intro hbaseMem hbaseEq =>
                                    rw [← hrule.right.left, ← hrule.right.right, ← hbaseEq]
                                    exact UnionProduces.rightRule
                                      ((hrulesH base.lhs base.rhs).mpr
                                        (Exists.intro base
                                          (And.intro hbaseMem
                                            (And.intro rfl rfl))))

def UnionSymbolLanguage (G : CFG terminal left) (H : CFG terminal right) :
    Symbol terminal (SumStart left right) -> Language terminal
  | Symbol.terminal a => Language.Singleton (Word.Symbol a)
  | Symbol.nonterminal SumStart.start =>
      Language.Union (GeneratedLanguage G) (GeneratedLanguage H)
  | Symbol.nonterminal (SumStart.inLeft A) => GeneratedFrom G A
  | Symbol.nonterminal (SumStart.inRight A) => GeneratedFrom H A

theorem inLeftForm_formLanguage_to_derivation
    (G : CFG terminal left) (H : CFG terminal right)
    {sf : SententialForm terminal left} {w : Word terminal}
    (h : w ∈ FormLanguage (UnionSymbolLanguage G H) (inLeftForm sf)) :
    w ∈ FormLanguage (DerivationSymbolLanguage G) sf := by
  induction sf generalizing w with
  | nil =>
      exact h
  | cons s rest ih =>
      cases s with
      | terminal a =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)
      | nonterminal A =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)

theorem inRightForm_formLanguage_to_derivation
    (G : CFG terminal left) (H : CFG terminal right)
    {sf : SententialForm terminal right} {w : Word terminal}
    (h : w ∈ FormLanguage (UnionSymbolLanguage G H) (inRightForm sf)) :
    w ∈ FormLanguage (DerivationSymbolLanguage H) sf := by
  induction sf generalizing w with
  | nil =>
      exact h
  | cons s rest ih =>
      cases s with
      | terminal a =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)
      | nonterminal A =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)

theorem union_production_sound (G : CFG terminal left) (H : CFG terminal right)
    {A : SumStart left right} {rhs : SententialForm terminal (SumStart left right)}
    (hprod : UnionProduces G H A rhs) :
    forall w, w ∈ FormLanguage (UnionSymbolLanguage G H) rhs ->
      w ∈ UnionSymbolLanguage G H (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | chooseLeft =>
      cases hw with
      | intro first hfirst =>
          cases hfirst with
          | intro tail htail =>
              cases htail.right.left
              rw [htail.right.right, Word.concat_empty_right]
              exact Or.inl htail.left
  | chooseRight =>
      cases hw with
      | intro first hfirst =>
          cases hfirst with
          | intro tail htail =>
              cases htail.right.left
              rw [htail.right.right, Word.concat_empty_right]
              exact Or.inr htail.left
  | leftRule hG =>
      rename_i A rhs
      have hbody := inLeftForm_formLanguage_to_derivation G H hw
      have hstep : Yields G [Symbol.nonterminal A] rhs := by
        exists []
        exists []
        exists A
        exists rhs
        constructor
        · exact hG
        constructor
        · rfl
        · simp
      exact Derives.step hstep (formLanguage_derives hbody)
  | rightRule hH =>
      rename_i A rhs
      have hbody := inRightForm_formLanguage_to_derivation G H hw
      have hstep : Yields H [Symbol.nonterminal A] rhs := by
        exists []
        exists []
        exists A
        exists rhs
        constructor
        · exact hH
        constructor
        · rfl
        · simp
      exact Derives.step hstep (formLanguage_derives hbody)

theorem union_yields_sound (G : CFG terminal left) (H : CFG terminal right)
    {x y : SententialForm terminal (SumStart left right)} {w : Word terminal}
    (h : Yields (UnionGrammar G H) x y)
    (hw : w ∈ FormLanguage (UnionSymbolLanguage G H) y) :
    w ∈ FormLanguage (UnionSymbolLanguage G H) x := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hy] at hw
                          rw [hx]
                          exact formLanguage_replace_sound
                            (UnionSymbolLanguage G H)
                            (union_production_sound G H hprod)
                            hw

theorem union_derives_sound (G : CFG terminal left) (H : CFG terminal right)
    {x y : SententialForm terminal (SumStart left right)} {w : Word terminal}
    (h : Derives (UnionGrammar G H) x y)
    (hw : w ∈ FormLanguage (UnionSymbolLanguage G H) y) :
    w ∈ FormLanguage (UnionSymbolLanguage G H) x := by
  induction h with
  | refl _ =>
      exact hw
  | step hstep _ ih =>
      exact union_yields_sound G H hstep (ih hw)

theorem union_generates_left (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ GeneratedLanguage G) :
    w ∈ GeneratedLanguage (UnionGrammar G H) := by
  have hStart : Yields (UnionGrammar G H)
      [Symbol.nonterminal SumStart.start]
      [Symbol.nonterminal (SumStart.inLeft G.start)] := by
    exists []
    exists []
    exists SumStart.start
    exists [Symbol.nonterminal (SumStart.inLeft G.start)]
    constructor
    · exact UnionProduces.chooseLeft
    constructor <;> rfl
  have hMap : Derives (UnionGrammar G H)
      [Symbol.nonterminal (SumStart.inLeft G.start)]
      (SententialForm.terminalWord w) := by
    have hMapped := mapDerivesNonterminal SumStart.inLeft G (UnionGrammar G H)
      (by
        intro A rhs hprod
        exact UnionProduces.leftRule hprod)
      hw
    change Derives (UnionGrammar G H)
      [Symbol.nonterminal (SumStart.inLeft G.start)]
      (SententialForm.mapNonterminal SumStart.inLeft (SententialForm.terminalWord w)) at hMapped
    rw [SententialForm.mapNonterminal_terminalWord] at hMapped
    exact hMapped
  exact Derives.step hStart hMap

theorem union_generates_right (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ GeneratedLanguage H) :
    w ∈ GeneratedLanguage (UnionGrammar G H) := by
  have hStart : Yields (UnionGrammar G H)
      [Symbol.nonterminal SumStart.start]
      [Symbol.nonterminal (SumStart.inRight H.start)] := by
    exists []
    exists []
    exists SumStart.start
    exists [Symbol.nonterminal (SumStart.inRight H.start)]
    constructor
    · exact UnionProduces.chooseRight
    constructor <;> rfl
  have hMap : Derives (UnionGrammar G H)
      [Symbol.nonterminal (SumStart.inRight H.start)]
      (SententialForm.terminalWord w) := by
    have hMapped := mapDerivesNonterminal SumStart.inRight H (UnionGrammar G H)
      (by
        intro A rhs hprod
        exact UnionProduces.rightRule hprod)
      hw
    change Derives (UnionGrammar G H)
      [Symbol.nonterminal (SumStart.inRight H.start)]
      (SententialForm.mapNonterminal SumStart.inRight (SententialForm.terminalWord w)) at hMapped
    rw [SententialForm.mapNonterminal_terminalWord] at hMapped
    exact hMapped
  exact Derives.step hStart hMap

theorem union_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ GeneratedLanguage (UnionGrammar G H)) :
    w ∈ Language.Union (GeneratedLanguage G) (GeneratedLanguage H) := by
  have hterminal : w ∈ FormLanguage (UnionSymbolLanguage G H)
      (SententialForm.terminalWord (nt := SumStart left right) w) :=
    terminalWord_mem_formLanguage (UnionSymbolLanguage G H) (by intro a; rfl) w
  have hsound := union_derives_sound G H h hterminal
  cases hsound with
  | intro first hfirst =>
      cases hfirst with
      | intro tail htail =>
          cases htail.right.left
          rw [htail.right.right, Word.concat_empty_right]
          exact htail.left

theorem union_generated_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ GeneratedLanguage (UnionGrammar G H) <->
      w ∈ Language.Union (GeneratedLanguage G) (GeneratedLanguage H) := by
  constructor
  · exact union_generates_inv G H
  · intro hw
    cases hw with
    | inl hleft =>
        exact union_generates_left G H hleft
    | inr hright =>
        exact union_generates_right G H hright

inductive ConcatProduces (G : CFG terminal left) (H : CFG terminal right) :
    SumStart left right -> SententialForm terminal (SumStart left right) -> Prop where
  | startRule :
      ConcatProduces G H SumStart.start
        [Symbol.nonterminal (SumStart.inLeft G.start),
         Symbol.nonterminal (SumStart.inRight H.start)]
  | leftRule {A rhs} :
      G.produces A rhs -> ConcatProduces G H (SumStart.inLeft A) (inLeftForm rhs)
  | rightRule {A rhs} :
      H.produces A rhs -> ConcatProduces G H (SumStart.inRight A) (inRightForm rhs)

def ConcatGrammar (G : CFG terminal left) (H : CFG terminal right) :
    CFG terminal (SumStart left right) where
  start := SumStart.start
  produces := ConcatProduces G H
  nonterminalsFinite := SumStart.finite G.nonterminalsFinite H.nonterminalsFinite

def concatStartProduction (G : CFG terminal left) (H : CFG terminal right) :
    Production terminal (SumStart left right) where
  lhs := SumStart.start
  rhs := [Symbol.nonterminal (SumStart.inLeft G.start),
    Symbol.nonterminal (SumStart.inRight H.start)]

def concatLeftProduction (rule : Production terminal left) :
    Production terminal (SumStart left right) where
  lhs := SumStart.inLeft rule.lhs
  rhs := inLeftForm rule.rhs

def concatRightProduction (rule : Production terminal right) :
    Production terminal (SumStart left right) where
  lhs := SumStart.inRight rule.lhs
  rhs := inRightForm rule.rhs

theorem concat_hasFiniteProductions
    {G : CFG terminal left} {H : CFG terminal right}
    (hG : HasFiniteProductions G) (hH : HasFiniteProductions H) :
    HasFiniteProductions (ConcatGrammar G H) := by
  cases hG with
  | intro rulesG hrulesG =>
      cases hH with
      | intro rulesH hrulesH =>
          exists [concatStartProduction G H] ++
            rulesG.map (concatLeftProduction (right := right)) ++
            rulesH.map (concatRightProduction (left := left))
          intro A rhs
          constructor
          · intro h
            cases h with
            | startRule =>
                exists concatStartProduction G H
                simp [concatStartProduction]
            | leftRule hprod =>
                cases (hrulesG _ _).mp hprod with
                | intro rule hrule =>
                    exists concatLeftProduction (right := right) rule
                    constructor
                    · apply List.mem_append_left
                      apply List.mem_append_right
                      exact List.mem_map.mpr
                        (Exists.intro rule (And.intro hrule.left rfl))
                    · constructor
                      · simp [concatLeftProduction, hrule.right.left]
                      · simp [concatLeftProduction, hrule.right.right]
            | rightRule hprod =>
                cases (hrulesH _ _).mp hprod with
                | intro rule hrule =>
                    exists concatRightProduction (left := left) rule
                    constructor
                    · apply List.mem_append_right
                      exact List.mem_map.mpr
                        (Exists.intro rule (And.intro hrule.left rfl))
                    · constructor
                      · simp [concatRightProduction, hrule.right.left]
                      · simp [concatRightProduction, hrule.right.right]
          · intro h
            cases h with
            | intro rule hrule =>
                have hmem := hrule.left
                simp [concatStartProduction, concatLeftProduction,
                  concatRightProduction] at hmem
                cases hmem with
                | inl hstart =>
                    rw [← hrule.right.left, ← hrule.right.right, hstart]
                    exact ConcatProduces.startRule
                | inr hrest =>
                    cases hrest with
                    | inl hleftRule =>
                        cases hleftRule with
                        | intro base hbase =>
                            cases hbase with
                            | intro hbaseMem hbaseEq =>
                                rw [← hrule.right.left, ← hrule.right.right, ← hbaseEq]
                                exact ConcatProduces.leftRule
                                  ((hrulesG base.lhs base.rhs).mpr
                                    (Exists.intro base
                                      (And.intro hbaseMem (And.intro rfl rfl))))
                    | inr hrightRule =>
                        cases hrightRule with
                        | intro base hbase =>
                            cases hbase with
                            | intro hbaseMem hbaseEq =>
                                rw [← hrule.right.left, ← hrule.right.right, ← hbaseEq]
                                exact ConcatProduces.rightRule
                                  ((hrulesH base.lhs base.rhs).mpr
                                    (Exists.intro base
                                      (And.intro hbaseMem (And.intro rfl rfl))))

theorem inLeftForm_context_of_eq
    {x : SententialForm terminal left} {y : SententialForm terminal right}
    {u v : SententialForm terminal (SumStart left right)} {A : left}
    (h : inLeftForm x ++ inRightForm y =
      u ++ [Symbol.nonterminal (SumStart.inLeft A)] ++ v) :
    exists ux vx,
      x = ux ++ [Symbol.nonterminal A] ++ vx ∧
      u = inLeftForm ux ∧
      v = inLeftForm vx ++ inRightForm y := by
  induction x generalizing u with
  | nil =>
      have hmem : Symbol.nonterminal (SumStart.inLeft A) ∈
          inRightForm y := by
        have hmem' : Symbol.nonterminal (SumStart.inLeft A) ∈
            inLeftForm ([] : SententialForm terminal left) ++ inRightForm y := by
          rw [h]
          simp
        cases List.mem_append.mp hmem' with
        | inl hnil =>
            cases hnil
        | inr hright =>
            exact hright
      exact False.elim (inRightForm_no_inLeft A y hmem)
  | cons s rest ih =>
      cases s with
      | terminal a =>
          cases u with
          | nil =>
              simp [inLeftForm, inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
          | cons head tail =>
              simp [inLeftForm, inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
              cases ih (by
                simpa [inLeftForm, inRightForm, SententialForm.mapNonterminal]
                  using h.right) with
              | intro ux hux =>
                  cases hux with
                  | intro vx hvx =>
                      exists Symbol.terminal a :: ux
                      exists vx
                      constructor
                      · rw [hvx.left]
                        rfl
                      constructor
                      · cases h.left
                        rw [hvx.right.left]
                        rfl
                      · exact hvx.right.right
      | nonterminal B =>
          cases u with
          | nil =>
              simp [inLeftForm, inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
              cases h.left
              exists []
              exists rest
              constructor
              · rfl
              constructor
              · rfl
              · simpa [inLeftForm, inRightForm, SententialForm.mapNonterminal]
                  using h.right.symm
          | cons head tail =>
              simp [inLeftForm, inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
              cases ih (by
                simpa [inLeftForm, inRightForm, SententialForm.mapNonterminal]
                  using h.right) with
              | intro ux hux =>
                  cases hux with
                  | intro vx hvx =>
                      exists Symbol.nonterminal B :: ux
                      exists vx
                      constructor
                      · rw [hvx.left]
                        rfl
                      constructor
                      · cases h.left
                        rw [hvx.right.left]
                        rfl
                      · exact hvx.right.right

theorem inRightForm_context_only_of_eq
    {y : SententialForm terminal right}
    {u v : SententialForm terminal (SumStart left right)} {A : right}
    (h : inRightForm (left := left) y =
      u ++ [Symbol.nonterminal (SumStart.inRight A)] ++ v) :
    exists uy vy,
      y = uy ++ [Symbol.nonterminal A] ++ vy ∧
      u = inRightForm (left := left) uy ∧
      v = inRightForm vy := by
  induction y generalizing u with
  | nil =>
      simp [inRightForm, SententialForm.mapNonterminal] at h
  | cons s rest ih =>
      cases s with
      | terminal a =>
          cases u with
          | nil =>
              simp [inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
          | cons head tail =>
              simp [inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
              cases ih (by
                simpa [inRightForm, SententialForm.mapNonterminal] using h.right) with
              | intro uy huy =>
                  cases huy with
                  | intro vy hvy =>
                      exists Symbol.terminal a :: uy
                      exists vy
                      constructor
                      · rw [hvy.left]
                        rfl
                      constructor
                      · cases h.left
                        rw [hvy.right.left]
                        rfl
                      · exact hvy.right.right
      | nonterminal B =>
          cases u with
          | nil =>
              simp [inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
              cases h.left
              exists []
              exists rest
              constructor
              · rfl
              constructor
              · rfl
              · simpa [inRightForm, SententialForm.mapNonterminal] using h.right.symm
          | cons head tail =>
              simp [inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
              cases ih (by
                simpa [inRightForm, SententialForm.mapNonterminal] using h.right) with
              | intro uy huy =>
                  cases huy with
                  | intro vy hvy =>
                      exists Symbol.nonterminal B :: uy
                      exists vy
                      constructor
                      · rw [hvy.left]
                        rfl
                      constructor
                      · cases h.left
                        rw [hvy.right.left]
                        rfl
                      · exact hvy.right.right

theorem inRightForm_context_of_eq
    {x : SententialForm terminal left} {y : SententialForm terminal right}
    {u v : SententialForm terminal (SumStart left right)} {A : right}
    (h : inLeftForm x ++ inRightForm y =
      u ++ [Symbol.nonterminal (SumStart.inRight A)] ++ v) :
    exists uy vy,
      y = uy ++ [Symbol.nonterminal A] ++ vy ∧
      u = inLeftForm x ++ inRightForm uy ∧
      v = inRightForm vy := by
  induction x generalizing u with
  | nil =>
      cases inRightForm_context_only_of_eq
          (left := left) (y := y) (A := A)
          (by simpa [inLeftForm] using h) with
      | intro uy huy =>
          cases huy with
          | intro vy hvy =>
              exists uy
              exists vy
  | cons s rest ih =>
      cases u with
      | nil =>
          cases s with
          | terminal a =>
              simp [inLeftForm, inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
          | nonterminal B =>
              simp [inLeftForm, inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
      | cons head tail =>
          cases s with
          | terminal a =>
              simp [inLeftForm, inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
              cases ih (by
                simpa [inLeftForm, inRightForm, SententialForm.mapNonterminal]
                  using h.right) with
              | intro uy huy =>
                  cases huy with
                  | intro vy hvy =>
                      exists uy
                      exists vy
                      constructor
                      · exact hvy.left
                      constructor
                      · cases h.left
                        rw [hvy.right.left]
                        rfl
                      · exact hvy.right.right
          | nonterminal B =>
              simp [inLeftForm, inRightForm, SententialForm.mapNonterminal,
                Symbol.mapNonterminal] at h
              cases ih (by
                simpa [inLeftForm, inRightForm, SententialForm.mapNonterminal]
                  using h.right) with
              | intro uy huy =>
                  cases huy with
                  | intro vy hvy =>
                      exists uy
                      exists vy
                      constructor
                      · exact hvy.left
                      constructor
                      · cases h.left
                        rw [hvy.right.left]
                        rfl
                      · exact hvy.right.right

theorem concat_zone_yields_inv (G : CFG terminal left) (H : CFG terminal right)
    {x : SententialForm terminal left} {y : SententialForm terminal right}
    {z : SententialForm terminal (SumStart left right)}
    (h : Yields (ConcatGrammar G H) (inLeftForm x ++ inRightForm y) z) :
    exists x' y',
      z = inLeftForm x' ++ inRightForm y' ∧
      ((Yields G x x' ∧ y' = y) ∨ (x' = x ∧ Yields H y y')) := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          cases hprod with
                          | startRule =>
                              have hmem : Symbol.nonterminal
                                  (SumStart.start : SumStart left right) ∈
                                    inLeftForm x ++ inRightForm y := by
                                rw [hx]
                                simp
                              cases List.mem_append.mp hmem with
                              | inl hleft =>
                                  exact False.elim (inLeftForm_no_start x hleft)
                              | inr hright =>
                                  exact False.elim (inRightForm_no_start y hright)
                          | leftRule hG =>
                              rename_i Aleft rhsl
                              cases inLeftForm_context_of_eq hx with
                              | intro ux hux =>
                                  cases hux with
                                  | intro vx hvx =>
                                      exists ux ++ rhsl ++ vx
                                      exists y
                                      constructor
                                      · rw [hy, hvx.right.left, hvx.right.right]
                                        simp [inLeftForm,
                                          SententialForm.mapNonterminal_append,
                                          List.append_assoc]
                                      · apply Or.inl
                                        constructor
                                        · exists ux
                                          exists vx
                                          exists Aleft
                                          exists rhsl
                                          exact And.intro hG (And.intro hvx.left rfl)
                                        · rfl
                          | rightRule hH =>
                              rename_i Aright rhsr
                              cases inRightForm_context_of_eq hx with
                              | intro uy huy =>
                                  cases huy with
                                  | intro vy hvy =>
                                      exists x
                                      exists uy ++ rhsr ++ vy
                                      constructor
                                      · rw [hy, hvy.right.left, hvy.right.right]
                                        simp [inRightForm,
                                          SententialForm.mapNonterminal_append,
                                          List.append_assoc]
                                      · apply Or.inr
                                        constructor
                                        · rfl
                                        · exists uy
                                          exists vy
                                          exists Aright
                                          exists rhsr
                                          exact And.intro hH (And.intro hvy.left rfl)

theorem concat_zone_derives_inv_aux
    (G : CFG terminal left) (H : CFG terminal right)
    {s z : SententialForm terminal (SumStart left right)}
    {x : SententialForm terminal left} {y : SententialForm terminal right}
    (hs : s = inLeftForm x ++ inRightForm y)
    (h : Derives (ConcatGrammar G H) s z) :
    exists x' y',
      z = inLeftForm x' ++ inRightForm y' ∧
      Derives G x x' ∧ Derives H y y' := by
  induction h generalizing x y with
  | refl s =>
      exists x
      exists y
      exact And.intro hs (And.intro (Derives.refl x) (Derives.refl y))
  | step hstep hrest ih =>
      rw [hs] at hstep
      cases concat_zone_yields_inv G H hstep with
      | intro xmid hxmid =>
          cases hxmid with
          | intro ymid hymid =>
              cases hymid with
              | intro hmid hcases =>
                  cases ih hmid with
                  | intro xfinal hxfinal =>
                      cases hxfinal with
                      | intro yfinal hyfinal =>
                          exists xfinal
                          exists yfinal
                          constructor
                          · exact hyfinal.left
                          · cases hcases with
                            | inl hleft =>
                                cases hleft with
                                | intro hyield hyEq =>
                                    cases hyEq
                                    exact And.intro
                                      (derives_trans (yields_derives hyield) hyfinal.right.left)
                                      hyfinal.right.right
                            | inr hright =>
                                cases hright with
                                | intro hxEq hyield =>
                                    cases hxEq
                                    exact And.intro hyfinal.right.left
                                      (derives_trans (yields_derives hyield)
                                        hyfinal.right.right)

theorem concat_zone_derives_inv
    (G : CFG terminal left) (H : CFG terminal right)
    {x : SententialForm terminal left} {y : SententialForm terminal right}
    {z : SententialForm terminal (SumStart left right)}
    (h : Derives (ConcatGrammar G H) (inLeftForm x ++ inRightForm y) z) :
    exists x' y',
      z = inLeftForm x' ++ inRightForm y' ∧
      Derives G x x' ∧ Derives H y y' :=
  concat_zone_derives_inv_aux G H rfl h

theorem concat_start_yields_inv (G : CFG terminal left) (H : CFG terminal right)
    {z : SententialForm terminal (SumStart left right)}
    (h : Yields (ConcatGrammar G H) [Symbol.nonterminal SumStart.start] z) :
    z = [Symbol.nonterminal (SumStart.inLeft G.start),
      Symbol.nonterminal (SumStart.inRight H.start)] := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          cases u <;> simp at hx
                          subst z
                          cases hx.left
                          rw [hx.right]
                          cases hprod <;> rfl

theorem concat_terminal_split_of_forms
    {x : SententialForm terminal left} {y : SententialForm terminal right}
    {w : Word terminal}
    (h : inLeftForm x ++ inRightForm y =
      SententialForm.terminalWord (nt := SumStart left right) w) :
    exists wx wy,
      x = SententialForm.terminalWord (nt := left) wx ∧
      y = SententialForm.terminalWord (nt := right) wy ∧
      w = Word.Concat wx wy := by
  have hto : SententialForm.toWord? (inLeftForm x ++ inRightForm y) = some w := by
    rw [h, SententialForm.terminalWord_toWord]
  cases SententialForm.toWord?_append_some hto with
  | intro wx hwx =>
      cases hwx with
      | intro wy hwy =>
          have hxWord : SententialForm.toWord? x = some wx := by
            rw [← SententialForm.toWord?_mapNonterminal SumStart.inLeft x]
            exact hwy.left
          have hyWord : SententialForm.toWord? y = some wy := by
            rw [← SententialForm.toWord?_mapNonterminal SumStart.inRight y]
            exact hwy.right.left
          exists wx
          exists wy
          exact And.intro (SententialForm.toWord?_some_eq_terminalWord hxWord)
            (And.intro (SententialForm.toWord?_some_eq_terminalWord hyWord)
              hwy.right.right)

theorem concat_generates (G : CFG terminal left) (H : CFG terminal right)
    {x y : Word terminal}
    (hx : x ∈ GeneratedLanguage G) (hy : y ∈ GeneratedLanguage H) :
    Word.Concat x y ∈ GeneratedLanguage (ConcatGrammar G H) := by
  have hStart : Yields (ConcatGrammar G H)
      [Symbol.nonterminal SumStart.start]
      [Symbol.nonterminal (SumStart.inLeft G.start),
       Symbol.nonterminal (SumStart.inRight H.start)] := by
    exists []
    exists []
    exists SumStart.start
    exists [Symbol.nonterminal (SumStart.inLeft G.start),
      Symbol.nonterminal (SumStart.inRight H.start)]
    constructor
    · exact ConcatProduces.startRule
    constructor <;> rfl
  have hLeft : Derives (ConcatGrammar G H)
      [Symbol.nonterminal (SumStart.inLeft G.start)]
      (SententialForm.terminalWord x) := by
    have hMapped := mapDerivesNonterminal SumStart.inLeft G (ConcatGrammar G H)
      (by
        intro A rhs hprod
        exact ConcatProduces.leftRule hprod)
      hx
    change Derives (ConcatGrammar G H)
      [Symbol.nonterminal (SumStart.inLeft G.start)]
      (SententialForm.mapNonterminal SumStart.inLeft (SententialForm.terminalWord x)) at hMapped
    rw [SententialForm.mapNonterminal_terminalWord] at hMapped
    exact hMapped
  have hRight : Derives (ConcatGrammar G H)
      [Symbol.nonterminal (SumStart.inRight H.start)]
      (SententialForm.terminalWord y) := by
    have hMapped := mapDerivesNonterminal SumStart.inRight H (ConcatGrammar G H)
      (by
        intro A rhs hprod
        exact ConcatProduces.rightRule hprod)
      hy
    change Derives (ConcatGrammar G H)
      [Symbol.nonterminal (SumStart.inRight H.start)]
      (SententialForm.mapNonterminal SumStart.inRight (SententialForm.terminalWord y)) at hMapped
    rw [SententialForm.mapNonterminal_terminalWord] at hMapped
    exact hMapped
  have hLeftContext :
      Derives (ConcatGrammar G H)
        ([Symbol.nonterminal (SumStart.inLeft G.start),
          Symbol.nonterminal (SumStart.inRight H.start)])
        (SententialForm.terminalWord x ++
          [Symbol.nonterminal (SumStart.inRight H.start)]) := by
    simpa using derives_context hLeft [] [Symbol.nonterminal (SumStart.inRight H.start)]
  have hRightContext :
      Derives (ConcatGrammar G H)
        (SententialForm.terminalWord x ++
          [Symbol.nonterminal (SumStart.inRight H.start)])
        (SententialForm.terminalWord x ++ SententialForm.terminalWord y) := by
    simpa using derives_context hRight (SententialForm.terminalWord x) []
  have hAll : Derives (ConcatGrammar G H)
      [Symbol.nonterminal SumStart.start]
      (SententialForm.terminalWord x ++ SententialForm.terminalWord y) :=
    Derives.step hStart (derives_trans hLeftContext hRightContext)
  change Derives (ConcatGrammar G H) [Symbol.nonterminal SumStart.start]
    (SententialForm.terminalWord (Word.Concat x y))
  rw [SententialForm.terminalWord_append]
  exact hAll

theorem concat_generates_inv_aux (G : CFG terminal left) (H : CFG terminal right)
    {s yform : SententialForm terminal (SumStart left right)} {w : Word terminal}
    (hs : s = [Symbol.nonterminal (SumStart.start : SumStart left right)])
    (hyform : yform = SententialForm.terminalWord (nt := SumStart left right) w)
    (h : Derives (ConcatGrammar G H) s yform) :
    w ∈ Language.Concat (GeneratedLanguage G) (GeneratedLanguage H) := by
  induction h with
  | refl s =>
      have hbad : SententialForm.toWord? s = some w := by
        rw [hyform, SententialForm.terminalWord_toWord]
      rw [hs] at hbad
      cases hbad
  | step hstep hrest _ih =>
      rw [hs] at hstep
      have hfirst := concat_start_yields_inv G H hstep
      have hzone := concat_zone_derives_inv_aux G H
        (x := [Symbol.nonterminal G.start])
        (y := [Symbol.nonterminal H.start])
        (by
          rw [hfirst]
          simp [inLeftForm, inRightForm, SententialForm.mapNonterminal,
            Symbol.mapNonterminal])
        hrest
      cases hzone with
      | intro xform hxform =>
          cases hxform with
          | intro yform' hyforms =>
              have hterminal :
                  inLeftForm xform ++ inRightForm yform' =
                    SententialForm.terminalWord
                      (nt := SumStart left right) w := by
                rw [← hyforms.left, hyform]
              cases concat_terminal_split_of_forms hterminal with
              | intro xw hxw =>
                  cases hxw with
                  | intro yw hyw =>
                      exists xw
                      exists yw
                      constructor
                      · rw [hyw.left] at hyforms
                        exact hyforms.right.left
                      constructor
                      · rw [hyw.right.left] at hyforms
                        exact hyforms.right.right
                      · exact hyw.right.right

theorem concat_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ GeneratedLanguage (ConcatGrammar G H)) :
    w ∈ Language.Concat (GeneratedLanguage G) (GeneratedLanguage H) :=
  concat_generates_inv_aux G H rfl rfl h

theorem concat_generated_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ GeneratedLanguage (ConcatGrammar G H) <->
      w ∈ Language.Concat (GeneratedLanguage G) (GeneratedLanguage H) := by
  constructor
  · exact concat_generates_inv G H
  · intro h
    cases h with
    | intro x hx =>
        cases hx with
        | intro y hy =>
            cases hy with
            | intro hxG hrest =>
                cases hrest with
                | intro hyH hw =>
                    rw [hw]
                    exact concat_generates G H hxG hyH

inductive StarNT (nt : Type u) where
  | start : StarNT nt
  | body : nt -> StarNT nt

namespace StarNT

def finite (f : FiniteType nt) : FiniteType (StarNT nt) where
  elems := [StarNT.start] ++ f.elems.map StarNT.body
  complete := by
    intro x
    cases x with
    | start => exact List.Mem.head _
    | body A =>
        apply List.Mem.tail
        exact List.mem_map.mpr (Exists.intro A (And.intro (f.complete A) rfl))

end StarNT

def starBodyForm (w : SententialForm terminal nt) :
    SententialForm terminal (StarNT nt) :=
  SententialForm.mapNonterminal StarNT.body w

inductive StarProduces (G : CFG terminal nt) :
    StarNT nt -> SententialForm terminal (StarNT nt) -> Prop where
  | stop : StarProduces G StarNT.start []
  | more :
      StarProduces G StarNT.start
        [Symbol.nonterminal (StarNT.body G.start), Symbol.nonterminal StarNT.start]
  | bodyRule {A rhs} :
      G.produces A rhs -> StarProduces G (StarNT.body A) (starBodyForm rhs)

def StarGrammar (G : CFG terminal nt) : CFG terminal (StarNT nt) where
  start := StarNT.start
  produces := StarProduces G
  nonterminalsFinite := StarNT.finite G.nonterminalsFinite

def starStopProduction : Production terminal (StarNT nt) where
  lhs := StarNT.start
  rhs := []

def starMoreProduction (G : CFG terminal nt) :
    Production terminal (StarNT nt) where
  lhs := StarNT.start
  rhs := [Symbol.nonterminal (StarNT.body G.start), Symbol.nonterminal StarNT.start]

def starBodyProduction (rule : Production terminal nt) :
    Production terminal (StarNT nt) where
  lhs := StarNT.body rule.lhs
  rhs := starBodyForm rule.rhs

theorem star_hasFiniteProductions
    {G : CFG terminal nt}
    (hG : HasFiniteProductions G) :
    HasFiniteProductions (StarGrammar G) := by
  cases hG with
  | intro rules hrules =>
      exists [starStopProduction (terminal := terminal) (nt := nt),
        starMoreProduction G] ++ rules.map starBodyProduction
      intro A rhs
      constructor
      · intro h
        cases h with
        | stop =>
            exists starStopProduction (terminal := terminal) (nt := nt)
            simp [starStopProduction]
        | more =>
            exists starMoreProduction G
            simp [starMoreProduction]
        | bodyRule hprod =>
            cases (hrules _ _).mp hprod with
            | intro rule hrule =>
                exists starBodyProduction rule
                constructor
                · apply List.mem_append_right
                  exact List.mem_map.mpr
                    (Exists.intro rule (And.intro hrule.left rfl))
                · constructor
                  · simp [starBodyProduction, hrule.right.left]
                  · simp [starBodyProduction, hrule.right.right]
      · intro h
        cases h with
        | intro rule hrule =>
            have hmem := hrule.left
            simp [starStopProduction, starMoreProduction, starBodyProduction] at hmem
            cases hmem with
            | inl hstop =>
                rw [← hrule.right.left, ← hrule.right.right, hstop]
                exact StarProduces.stop
            | inr hrest =>
                cases hrest with
                | inl hmore =>
                    rw [← hrule.right.left, ← hrule.right.right, hmore]
                    exact StarProduces.more
                | inr hbody =>
                    cases hbody with
                    | intro base hbase =>
                        cases hbase with
                        | intro hbaseMem hbaseEq =>
                            rw [← hrule.right.left, ← hrule.right.right, ← hbaseEq]
                            exact StarProduces.bodyRule
                              ((hrules base.lhs base.rhs).mpr
                                (Exists.intro base
                                  (And.intro hbaseMem (And.intro rfl rfl))))

def StarSymbolLanguage (G : CFG terminal nt) :
    Symbol terminal (StarNT nt) -> Language terminal
  | Symbol.terminal a => Language.Singleton (Word.Symbol a)
  | Symbol.nonterminal StarNT.start => Language.Star (GeneratedLanguage G)
  | Symbol.nonterminal (StarNT.body A) => GeneratedFrom G A

theorem starBodyForm_formLanguage_to_derivation
    (G : CFG terminal nt) {sf : SententialForm terminal nt} {w : Word terminal}
    (h : w ∈ FormLanguage (StarSymbolLanguage G) (starBodyForm sf)) :
    w ∈ FormLanguage (DerivationSymbolLanguage G) sf := by
  induction sf generalizing w with
  | nil =>
      exact h
  | cons s rest ih =>
      cases s with
      | terminal a =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)
      | nonterminal A =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)

theorem star_production_sound (G : CFG terminal nt)
    {A : StarNT nt} {rhs : SententialForm terminal (StarNT nt)}
    (hprod : StarProduces G A rhs) :
    forall w, w ∈ FormLanguage (StarSymbolLanguage G) rhs ->
      w ∈ StarSymbolLanguage G (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | stop =>
      cases hw
      exact Language.star_empty_word (GeneratedLanguage G)
  | more =>
      cases hw with
      | intro first hfirst =>
          cases hfirst with
          | intro tail htail =>
              have htailStar : tail ∈ Language.Star (GeneratedLanguage G) := by
                cases htail.right.left with
                | intro starPart hstarPart =>
                    cases hstarPart with
                    | intro emptyPart hemptyPart =>
                      cases hemptyPart.right.left
                      rw [hemptyPart.right.right, Word.concat_empty_right]
                      exact hemptyPart.left
              rw [htail.right.right]
              exact Language.star_concat
                (Language.star_of_mem (GeneratedLanguage G) htail.left)
                htailStar
  | bodyRule hG =>
      rename_i A rhs
      have hbody := starBodyForm_formLanguage_to_derivation G hw
      have hstep : Yields G [Symbol.nonterminal A] rhs := by
        exists []
        exists []
        exists A
        exists rhs
        constructor
        · exact hG
        constructor
        · rfl
        · simp
      exact Derives.step hstep (formLanguage_derives hbody)

theorem star_yields_sound (G : CFG terminal nt)
    {x y : SententialForm terminal (StarNT nt)} {w : Word terminal}
    (h : Yields (StarGrammar G) x y)
    (hw : w ∈ FormLanguage (StarSymbolLanguage G) y) :
    w ∈ FormLanguage (StarSymbolLanguage G) x := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hy] at hw
                          rw [hx]
                          exact formLanguage_replace_sound
                            (StarSymbolLanguage G)
                            (star_production_sound G hprod)
                            hw

theorem star_derives_sound (G : CFG terminal nt)
    {x y : SententialForm terminal (StarNT nt)} {w : Word terminal}
    (h : Derives (StarGrammar G) x y)
    (hw : w ∈ FormLanguage (StarSymbolLanguage G) y) :
    w ∈ FormLanguage (StarSymbolLanguage G) x := by
  induction h with
  | refl _ =>
      exact hw
  | step hstep _ ih =>
      exact star_yields_sound G hstep (ih hw)

theorem star_generates_inv (G : CFG terminal nt) {w : Word terminal}
    (h : w ∈ GeneratedLanguage (StarGrammar G)) :
    w ∈ Language.Star (GeneratedLanguage G) := by
  have hterminal : w ∈ FormLanguage (StarSymbolLanguage G)
      (SententialForm.terminalWord (nt := StarNT nt) w) :=
    terminalWord_mem_formLanguage (StarSymbolLanguage G) (by intro a; rfl) w
  have hsound := star_derives_sound G h hterminal
  cases hsound with
  | intro starPart hstarPart =>
      cases hstarPart with
      | intro emptyPart hemptyPart =>
          cases hemptyPart.right.left
          rw [hemptyPart.right.right, Word.concat_empty_right]
          exact hemptyPart.left

theorem star_generates_empty (G : CFG terminal nt) :
    ([] : Word terminal) ∈ GeneratedLanguage (StarGrammar G) := by
  apply yields_derives
  exists []
  exists []
  exists StarNT.start
  exists ([] : SententialForm terminal (StarNT nt))
  constructor
  · exact StarProduces.stop
  constructor <;> rfl

theorem star_generates_cons (G : CFG terminal nt)
    {x y : Word terminal}
    (hx : x ∈ GeneratedLanguage G)
    (hy : y ∈ GeneratedLanguage (StarGrammar G)) :
    Word.Concat x y ∈ GeneratedLanguage (StarGrammar G) := by
  have hStart : Yields (StarGrammar G)
      [Symbol.nonterminal StarNT.start]
      [Symbol.nonterminal (StarNT.body G.start), Symbol.nonterminal StarNT.start] := by
    exists []
    exists []
    exists StarNT.start
    exists [Symbol.nonterminal (StarNT.body G.start), Symbol.nonterminal StarNT.start]
    constructor
    · exact StarProduces.more
    constructor <;> rfl
  have hBody : Derives (StarGrammar G)
      [Symbol.nonterminal (StarNT.body G.start)]
      (SententialForm.terminalWord x) := by
    have hMapped := mapDerivesNonterminal StarNT.body G (StarGrammar G)
      (by
        intro A rhs hprod
        exact StarProduces.bodyRule hprod)
      hx
    change Derives (StarGrammar G)
      [Symbol.nonterminal (StarNT.body G.start)]
      (SententialForm.mapNonterminal StarNT.body (SententialForm.terminalWord x)) at hMapped
    rw [SententialForm.mapNonterminal_terminalWord] at hMapped
    exact hMapped
  have hBodyContext :
      Derives (StarGrammar G)
        [Symbol.nonterminal (StarNT.body G.start), Symbol.nonterminal StarNT.start]
        (SententialForm.terminalWord x ++ [Symbol.nonterminal StarNT.start]) := by
    simpa using derives_context hBody [] [Symbol.nonterminal StarNT.start]
  have hTailContext :
      Derives (StarGrammar G)
        (SententialForm.terminalWord x ++ [Symbol.nonterminal StarNT.start])
        (SententialForm.terminalWord x ++ SententialForm.terminalWord y) := by
    simpa using derives_context hy (SententialForm.terminalWord x) []
  have hAll : Derives (StarGrammar G) [Symbol.nonterminal StarNT.start]
      (SententialForm.terminalWord x ++ SententialForm.terminalWord y) :=
    Derives.step hStart (derives_trans hBodyContext hTailContext)
  change Derives (StarGrammar G) [Symbol.nonterminal StarNT.start]
    (SententialForm.terminalWord (Word.Concat x y))
  rw [SententialForm.terminalWord_append]
  exact hAll

theorem star_generates_of_pieces (G : CFG terminal nt)
    (pieces : List (Word terminal))
    (hall : forall p, p ∈ pieces -> p ∈ GeneratedLanguage G) :
    Language.ConcatWords pieces ∈ GeneratedLanguage (StarGrammar G) := by
  induction pieces with
  | nil =>
      exact star_generates_empty G
  | cons p rest ih =>
      exact star_generates_cons G (hall p (List.Mem.head rest))
        (ih (by
          intro q hq
          exact hall q (List.Mem.tail p hq)))

theorem star_generated_language_exact (G : CFG terminal nt) (w : Word terminal) :
    w ∈ GeneratedLanguage (StarGrammar G) <->
      w ∈ Language.Star (GeneratedLanguage G) := by
  constructor
  · exact star_generates_inv G
  · intro hw
    cases hw with
    | intro pieces hpieces =>
        rw [← hpieces.right]
        exact star_generates_of_pieces G pieces hpieces.left

end CFG

end Grammars
end FoC
