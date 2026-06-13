import FoC.Grammars.CFG.Derivations

set_option doc.verso true

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace CFG

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


end CFG

end Grammars
end FoC
