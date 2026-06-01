import FoC.Foundation.Finite
import FoC.Languages.Language

namespace FoC
namespace Grammars

/-!
Context-free grammars and derivations.

Used by:
- Chapter 4, Section 4.1: context-free grammar definitions, one-step
  derivation, reflexive-transitive derivation, generated languages, and the
  basic yield laws.
- Chapter 4, Section 4.3: parse trees are related back to derivations.
- Chapter 4, Section 4.6: context-free grammars embed into general grammars.
-/

open Foundation
open Languages

namespace FiniteType

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

end Symbol

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

structure CFG (terminal : Type u) (nonterminal : Type v) where
  start : nonterminal
  produces : nonterminal -> SententialForm terminal nonterminal -> Prop
  nonterminalsFinite : FiniteType nonterminal

namespace CFG

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

def ContextFree (L : Language terminal) : Prop :=
  exists nonterminal : Type, exists G : CFG terminal nonterminal,
    Language.Equal (GeneratedLanguage G) L

def Equivalent (G H : CFG terminal nonterminal) : Prop :=
  Language.Equal (GeneratedLanguage G) (GeneratedLanguage H)

inductive RightRegularRHS : SententialForm terminal nonterminal -> Prop where
  | epsilon : RightRegularRHS []
  | nonterminal (A : nonterminal) :
      RightRegularRHS [Symbol.nonterminal A]
  | terminalThenNonterminal (a : terminal) (A : nonterminal) :
      RightRegularRHS [Symbol.terminal a, Symbol.nonterminal A]

def RightRegular (G : CFG terminal nonterminal) : Prop :=
  forall A rhs, G.produces A rhs -> RightRegularRHS rhs

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

theorem generated_language_mem (G : CFG terminal nonterminal) (w : Word terminal) :
    w ∈ GeneratedLanguage G <->
      Derives G [Symbol.nonterminal G.start] (SententialForm.terminalWord w) :=
  Iff.rfl

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

end CFG

end Grammars
end FoC
