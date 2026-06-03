import FoC.Languages.NFA

set_option doc.verso true

/-!
# NFA path semantics

## Path semantics

## Book coordinates

Used by:
- Chapter 3, Section 3.6: regular-expression-to-NFA constructions

The core {lit}`NFA.Accepts` definition is reachability-set based because that
is convenient for subset construction.  Thompson-style constructions are easier
to prove with explicit paths.  This module proves that both views agree.
-/

namespace FoC
namespace Languages

open Foundation

namespace NFA

/-!
# Explicit paths

The inductive path relation records a concrete accepting computation: epsilon
steps may occur before reading the next input symbol, and word labels compose
along the path.
-/

inductive Path (M : NFA alpha state) : state -> Word alpha -> state -> Prop where
  | nil (q : state) : Path M q Word.Empty q
  | eps {q r s : state} {w : Word alpha} :
      r ∈ M.step q none -> Path M r w s -> Path M q w s
  | sym {q r s : state} {a : alpha} {w : Word alpha} :
      r ∈ M.step q (some a) -> Path M r w s -> Path M q (a :: w) s

def PathAccepts (M : NFA alpha state) (w : Word alpha) : Prop :=
  exists q, Path M M.start w q ∧ M.accept q

/-!
# Empty paths and composition

These facts connect empty-word paths with epsilon reachability and show that
paths compose across word concatenation.
-/

theorem epsilonReach_trans {M : NFA alpha state} {q r s : state}
    (hqr : EpsilonReach M q r) (hrs : EpsilonReach M r s) :
    EpsilonReach M q s := by
  induction hqr with
  | refl _ => exact hrs
  | step hstep _ ih => exact EpsilonReach.step hstep (ih hrs)

theorem path_epsilonReach_prefix {M : NFA alpha state} {q r s : state}
    {w : Word alpha} (hqr : EpsilonReach M q r) (hpath : Path M r w s) :
    Path M q w s := by
  induction hqr with
  | refl _ => exact hpath
  | step hstep _ ih => exact Path.eps hstep (ih hpath)

theorem path_of_epsilonReach {M : NFA alpha state} {q r : state}
    (hqr : EpsilonReach M q r) : Path M q Word.Empty r :=
  path_epsilonReach_prefix hqr (Path.nil r)

theorem epsilonReach_of_path_empty_aux {M : NFA alpha state} {q r : state}
    {v : Word alpha} (hpath : Path M q v r) :
    v = Word.Empty -> EpsilonReach M q r := by
  induction hpath with
  | nil q =>
      intro _
      exact EpsilonReach.refl q
  | eps hstep _ ih =>
      intro hv
      exact EpsilonReach.step hstep (ih hv)
  | sym hstep _ ih =>
      intro hv
      cases hv

theorem epsilonReach_of_path_empty {M : NFA alpha state} {q r : state}
    (hpath : Path M q Word.Empty r) : EpsilonReach M q r :=
  epsilonReach_of_path_empty_aux hpath rfl

theorem path_append {M : NFA alpha state} {q r s : state}
    {x y : Word alpha} (hxy : Path M q x r) (hyz : Path M r y s) :
    Path M q (Word.Concat x y) s := by
  induction hxy with
  | nil _ =>
      exact hyz
  | eps hstep _ ih =>
      exact Path.eps hstep (ih hyz)
  | sym hstep _ ih =>
      exact Path.sym hstep (ih hyz)

/-!
# Closed reachable sets

The set-based semantics used by the subset construction is related back to
explicit paths by closure lemmas for starts, next states, and reachable sets.
-/

def EpsilonClosed (M : NFA alpha state) (S : FSet state) : Prop :=
  forall {q r}, q ∈ S -> EpsilonReach M q r -> r ∈ S

theorem epsilonClosure_closed (M : NFA alpha state) (S : FSet state) :
    EpsilonClosed M (EpsilonClosure M S) := by
  intro q r hq hqr
  cases hq with
  | intro p hp =>
      cases hp with
      | intro hpS hpq =>
          exists p
          exact And.intro hpS (epsilonReach_trans hpq hqr)

theorem startSet_closed (M : NFA alpha state) :
    EpsilonClosed M (StartSet M) :=
  epsilonClosure_closed M (FSet.Singleton M.start)

theorem next_closed (M : NFA alpha state) (S : FSet state) (a : alpha) :
    EpsilonClosed M (Next M S a) :=
  epsilonClosure_closed M (SymbolMove M S a)

theorem start_mem_startSet (M : NFA alpha state) : M.start ∈ StartSet M :=
  epsilonClosure_contains rfl

theorem path_from_next {M : NFA alpha state} {S : FSet state}
    {a : alpha} {w : Word alpha} {p r : state}
    (hp : p ∈ Next M S a) (hpath : Path M p w r) :
    exists q, q ∈ S ∧ Path M q (a :: w) r := by
  cases hp with
  | intro moved hmoved =>
      cases hmoved with
      | intro hmovedBySymbol heps =>
          cases hmovedBySymbol with
          | intro q hq =>
              cases hq with
              | intro hqS hstep =>
                  exists q
                  constructor
                  · exact hqS
                  · exact Path.sym hstep (path_epsilonReach_prefix heps hpath)

theorem path_cons_from_closed_aux {M : NFA alpha state} {S : FSet state}
    (hclosed : EpsilonClosed M S) {q r : state} {v : Word alpha}
    (hq : q ∈ S) (hpath : Path M q v r) :
    forall {a : alpha} {w : Word alpha}, v = a :: w ->
      exists p, p ∈ Next M S a ∧ Path M p w r := by
  induction hpath generalizing S with
  | nil _ =>
      intro a w hv
      cases hv
  | eps hstep htail ih =>
      intro a w hv
      exact ih hclosed (hclosed hq (EpsilonReach.step hstep (EpsilonReach.refl _))) hv
  | sym hstep htail =>
      intro a' w' hv
      cases hv
      exact Exists.intro _
        (And.intro (epsilonClosure_contains (Exists.intro _ (And.intro hq hstep))) htail)

theorem path_cons_from_closed {M : NFA alpha state} {S : FSet state}
    (hclosed : EpsilonClosed M S) {q r : state} {a : alpha} {w : Word alpha}
    (hq : q ∈ S) (hpath : Path M q (a :: w) r) :
    exists p, p ∈ Next M S a ∧ Path M p w r :=
  path_cons_from_closed_aux hclosed hq hpath rfl

theorem reachFromSet_path_iff {M : NFA alpha state} {S : FSet state}
    (hclosed : EpsilonClosed M S) (w : Word alpha) (r : state) :
    r ∈ ReachFromSet M S w <-> exists q, q ∈ S ∧ Path M q w r := by
  induction w generalizing S r with
  | nil =>
      constructor
      · intro hr
        exists r
        exact And.intro hr (Path.nil r)
      · intro h
        cases h with
        | intro q hq =>
            exact hclosed hq.left (epsilonReach_of_path_empty hq.right)
  | cons a rest ih =>
      constructor
      · intro hr
        have hnextClosed : EpsilonClosed M (Next M S a) := next_closed M S a
        cases (ih hnextClosed r).mp hr with
        | intro p hp =>
            exact path_from_next hp.left hp.right
      · intro h
        cases h with
        | intro q hq =>
            cases path_cons_from_closed hclosed hq.left hq.right with
            | intro p hp =>
                exact (ih (next_closed M S a) r).mpr
                  (Exists.intro p (And.intro hp.left hp.right))

/-!
# Acceptance equivalence

The final theorem proves that the set-of-states acceptance predicate agrees
with the explicit path semantics.
-/

theorem pathAccepts_iff_accepts (M : NFA alpha state) (w : Word alpha) :
    PathAccepts M w <-> Accepts M w := by
  constructor
  · intro h
    cases h with
    | intro q hq =>
        exists q
        constructor
        · exact (reachFromSet_path_iff (startSet_closed M) w q).mpr
            (Exists.intro M.start (And.intro (start_mem_startSet M) hq.left))
        · exact hq.right
  · intro h
    cases h with
    | intro q hq =>
        cases (reachFromSet_path_iff (startSet_closed M) w q).mp hq.left with
        | intro p hp =>
            cases hp.left with
            | intro start hstart =>
                cases hstart with
                | intro hstartEq hreach =>
                    rw [hstartEq] at hreach
                    exists q
                    constructor
                    · exact path_epsilonReach_prefix hreach hp.right
                    · exact hq.right

end NFA
end Languages
end FoC
