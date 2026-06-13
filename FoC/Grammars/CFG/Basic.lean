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


end CFG

end Grammars
end FoC
