import FoC.Computability.TapeLemmas
import FoC.Computability.Compiler.Structured.Lowering.Layout

set_option doc.verso true

/-!
# Injectivity of the guarded structured encoding

Physical tape equivalence between canonical guarded encodings forces equality
of the encoded logical tape lists.  Construction leaves need this to turn
per-step logical tape changes into per-step encoding changes: a spinning
structured core moves a cursor on every step, and this module upgrades those
moves to the per-step non-equivalence hypothesis of the divergence transfer
{lit}`staticLoweredDescriptionWithRefresh_not_haltsFromTape_of_state_or_tape_progress`.

The proof works on the raw Boolean payloads: logical cell codes are the
two-bit groups {lit}`FF`/{lit}`FT`/{lit}`TF`, so the head marker {lit}`TT` is
recovered as the first pair-aligned {lit}`TT` group, and the blank physical
separators split the per-tape segments uniquely because segment payloads are
blank-free.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

/-!
## List splitting helpers
-/

private theorem map_some_inj {α : Type _} :
    forall {xs ys : List α},
      xs.map some = ys.map some -> xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by injection h
  | _ :: _, [], h => by injection h
  | x :: xs, y :: ys, h => by
      injection h with hhead htail
      injection hhead with hxy
      rw [hxy, map_some_inj htail]

private theorem dropTrailingNone_map_some {α : Type _} (xs : List α) :
    Tape.dropTrailingNone (xs.map some) = xs.map some := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [Tape.dropTrailingNone, ih]

private theorem dropTrailingNone_append_of_ne_nil {α : Type _}
    (xs : List (Option α)) {ys : List (Option α)}
    (hys : Tape.dropTrailingNone ys ≠ []) :
    Tape.dropTrailingNone (List.append xs ys) =
      List.append xs (Tape.dropTrailingNone ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hne : List.append xs (Tape.dropTrailingNone ys) ≠ [] := by
        cases xs with
        | nil => simpa using hys
        | cons z zs => simp
      show Tape.dropTrailingNone (x :: List.append xs ys) = _
      rw [Tape.dropTrailingNone_cons, ih, if_neg]
      · rfl
      · intro hcond
        exact hne hcond.right

/--
Blank-separated blocks of blank-free cells split uniquely at the first blank.
-/
private theorem map_some_append_none_cons_inj {α : Type _} :
    forall (xs ys : List α) (u v : List (Option α)),
      List.append (xs.map some) (none :: u) =
        List.append (ys.map some) (none :: v) ->
      xs = ys ∧ u = v
  | [], [], _u, _v, h => by
      injection h with _ huv
      exact ⟨rfl, huv⟩
  | [], y :: ys, u, v, h => by
      injection h with hcontra _
      cases hcontra
  | x :: xs, [], u, v, h => by
      injection h with hcontra _
      cases hcontra
  | x :: xs, y :: ys, u, v, h => by
      injection h with hhead htail
      injection hhead with hxy
      rcases map_some_append_none_cons_inj xs ys u v htail with ⟨hxs, huv⟩
      exact ⟨by rw [hxy, hxs], huv⟩

/-!
## Cell-payload injectivity

Logical cell payloads are the pairs {lit}`FF`, {lit}`FT`, {lit}`TF`; the pair
{lit}`TT` only occurs pair-aligned as the head marker.
-/

private theorem logicalCellBits_head_split :
    forall (a b : Option Bool) (u v : List Bool),
      List.append (logicalCellBits a) u =
        List.append (logicalCellBits b) v ->
      a = b ∧ u = v := by
  intro a b u v h
  cases a with
  | none =>
      cases b with
      | none =>
          injection h with _ h1
          injection h1 with _ huv
          exact ⟨rfl, huv⟩
      | some bitB =>
          cases bitB with
          | false =>
              injection h with _ h1
              injection h1 with hcontra _
              exact Bool.noConfusion hcontra
          | true =>
              injection h with hcontra _
              exact Bool.noConfusion hcontra
  | some bitA =>
      cases bitA with
      | false =>
          cases b with
          | none =>
              injection h with _ h1
              injection h1 with hcontra _
              exact Bool.noConfusion hcontra
          | some bitB =>
              cases bitB with
              | false =>
                  injection h with _ h1
                  injection h1 with _ huv
                  exact ⟨rfl, huv⟩
              | true =>
                  injection h with hcontra _
                  exact Bool.noConfusion hcontra
      | true =>
          cases b with
          | none =>
              injection h with hcontra _
              exact Bool.noConfusion hcontra
          | some bitB =>
              cases bitB with
              | false =>
                  injection h with hcontra _
                  exact Bool.noConfusion hcontra
              | true =>
                  injection h with _ h1
                  injection h1 with _ huv
                  exact ⟨rfl, huv⟩

private theorem logicalCellListBits_inj :
    forall (xs ys : List (Option Bool)),
      logicalCellListBits xs = logicalCellListBits ys -> xs = ys
  | [], [], _h => rfl
  | [], y :: ys, h => by
      exfalso
      have h' :
          ([] : List Bool) =
            List.append (logicalCellBits y) (logicalCellListBits ys) := h
      cases y with
      | none => injection h'
      | some bit => cases bit <;> injection h'
  | x :: xs, [], h => by
      exfalso
      have h' :
          List.append (logicalCellBits x) (logicalCellListBits xs) =
            ([] : List Bool) := h
      cases x with
      | none => injection h'
      | some bit => cases bit <;> injection h'
  | x :: xs, y :: ys, h => by
      have h' :
          List.append (logicalCellBits x) (logicalCellListBits xs) =
            List.append (logicalCellBits y) (logicalCellListBits ys) := h
      rcases logicalCellBits_head_split x y _ _ h' with ⟨hxy, htail⟩
      rw [hxy, logicalCellListBits_inj xs ys htail]

/--
A cell-payload run followed by the head marker splits uniquely: cell payload
pairs are never {lit}`TT`, so the first pair-aligned {lit}`TT` is the marker.
-/
private theorem logicalCellListBits_marker_split :
    forall (xs ys : List (Option Bool)) (u v : List Bool),
      List.append (logicalCellListBits xs) (true :: true :: u) =
        List.append (logicalCellListBits ys) (true :: true :: v) ->
      xs = ys ∧ u = v
  | [], [], _u, _v, h => by
      injection h with _ h1
      injection h1 with _ huv
      exact ⟨rfl, huv⟩
  | [], y :: ys, u, v, h => by
      exfalso
      cases y with
      | none =>
          injection h with hcontra _
          exact Bool.noConfusion hcontra
      | some bit =>
          cases bit with
          | false =>
              injection h with hcontra _
              exact Bool.noConfusion hcontra
          | true =>
              injection h with _ h1
              injection h1 with hcontra _
              exact Bool.noConfusion hcontra
  | x :: xs, [], u, v, h => by
      exfalso
      cases x with
      | none =>
          injection h with hcontra _
          exact Bool.noConfusion hcontra
      | some bit =>
          cases bit with
          | false =>
              injection h with hcontra _
              exact Bool.noConfusion hcontra
          | true =>
              injection h with _ h1
              injection h1 with hcontra _
              exact Bool.noConfusion hcontra
  | x :: xs, y :: ys, u, v, h => by
      have h' :
          List.append (logicalCellBits x)
              (List.append (logicalCellListBits xs) (true :: true :: u)) =
            List.append (logicalCellBits y)
              (List.append (logicalCellListBits ys)
                (true :: true :: v)) := by
        cases x <;> cases y <;>
          first
            | exact h
            | (rename_i bitA bitB; cases bitA <;> cases bitB <;> exact h)
            | (rename_i bit; cases bit <;> exact h)
      rcases logicalCellBits_head_split x y _ _ h' with ⟨hxy, htail⟩
      rcases logicalCellListBits_marker_split xs ys u v htail with
        ⟨hxs, huv⟩
      exact ⟨by rw [hxy, hxs], huv⟩

/-- The raw Boolean payload of an encoded logical tape determines the tape. -/
theorem logicalTapeBits_inj {T U : Tape Bool}
    (h : logicalTapeBits T = logicalTapeBits U) : T = U := by
  have h' :
      List.append (logicalCellListBits T.left.reverse)
          (true :: true ::
            List.append (logicalCellBits T.head)
              (logicalCellListBits T.right)) =
        List.append (logicalCellListBits U.left.reverse)
          (true :: true ::
            List.append (logicalCellBits U.head)
              (logicalCellListBits U.right)) := h
  rcases
      logicalCellListBits_marker_split
        T.left.reverse U.left.reverse _ _ h' with
    ⟨hleftRev, hrest⟩
  rcases logicalCellBits_head_split T.head U.head _ _ hrest with
    ⟨hhead, hright⟩
  have hleft : T.left = U.left := by
    have := congrArg List.reverse hleftRev
    simpa using this
  have hrightEq : T.right = U.right :=
    logicalCellListBits_inj T.right U.right hright
  cases T with
  | mk tleft thead tright =>
      cases U with
      | mk uleft uhead uright =>
          simp_all

/-- Far-edge representation guards do not identify distinct logical tapes. -/
theorem guardLogicalTape_inj {T U : Tape Bool}
    (h : guardLogicalTape T = guardLogicalTape U) : T = U := by
  cases T with
  | mk tleft thead tright =>
      cases U with
      | mk uleft uhead uright =>
          simp only [guardLogicalTape, Tape.mk.injEq] at h
          rcases h with ⟨hleftG, hhead, hrightG⟩
          have hleft : tleft = uleft := by
            have hrev :
                none :: tleft.reverse = none :: uleft.reverse := by
              simpa [List.reverse_append] using
                congrArg List.reverse hleftG
            have hrev' : tleft.reverse = uleft.reverse := by
              injection hrev
            simpa using congrArg List.reverse hrev'
          have hright : tright = uright := by
            have hrev :
                none :: tright.reverse = none :: uright.reverse := by
              simpa [List.reverse_append] using
                congrArg List.reverse hrightG
            have hrev' : tright.reverse = uright.reverse := by
              injection hrev
            simpa using congrArg List.reverse hrev'
          simp [hleft, hhead, hright]

/-!
## Guarded encoding injectivity
-/

private theorem encodedGuardedStructuredTapes_three_right
    (T0 T1 T2 : Tape Bool) :
    (encodedGuardedStructuredTapes [T0, T1, T2]).right =
      List.append (logicalTapeCode (guardLogicalTape T0))
        (none ::
          List.append (logicalTapeCode (guardLogicalTape T1))
            (none ::
              List.append (logicalTapeCode (guardLogicalTape T2))
                [none])) := by
  rfl

private theorem dropTrailingNone_threeBlock
    (a b c : Word Bool) (hc : c ≠ []) :
    Tape.dropTrailingNone
        (List.append (a.map some)
          (none ::
            List.append (b.map some)
              (none :: List.append (c.map some) [none]))) =
      List.append (a.map some)
        (none :: List.append (b.map some) (none :: c.map some)) := by
  have hcSome : c.map some ≠ [] := by
    cases c with
    | nil => cases hc rfl
    | cons bit rest => simp
  have hinner :
      Tape.dropTrailingNone (List.append (c.map some) [none]) =
        c.map some := by
    have hAppend :
        Tape.dropTrailingNone (List.append (c.map some) [none]) =
          Tape.dropTrailingNone (c.map some) := by
      simpa using dropTrailingNone_append_none (c.map some)
    rw [hAppend, dropTrailingNone_map_some]
  have hconsInner :
      Tape.dropTrailingNone
          (none :: List.append (c.map some) [none]) =
        none :: c.map some := by
    rw [Tape.dropTrailingNone_cons, hinner, if_neg]
    intro hcond
    exact hcSome hcond.right
  have hmid :
      Tape.dropTrailingNone
          (List.append (b.map some)
            (none :: List.append (c.map some) [none])) =
        List.append (b.map some) (none :: c.map some) := by
    rw [dropTrailingNone_append_of_ne_nil (b.map some)
      (by rw [hconsInner]; simp), hconsInner]
  have hconsMid :
      Tape.dropTrailingNone
          (none ::
            List.append (b.map some)
              (none :: List.append (c.map some) [none])) =
        none :: List.append (b.map some) (none :: c.map some) := by
    rw [Tape.dropTrailingNone_cons, hmid, if_neg]
    intro hcond
    have hne : List.append (b.map some) (none :: c.map some) ≠ [] := by
      cases hb : b.map some with
      | nil => simp
      | cons bit rest => simp
    exact hne hcond.right
  rw [dropTrailingNone_append_of_ne_nil (a.map some)
    (by rw [hconsMid]; simp), hconsMid]

/--
Physical tape equivalence between canonical guarded three-tape encodings
forces equality of the encoded logical tapes.
-/
theorem encodedGuardedStructuredTapes_three_equiv_inj
    {T0 T1 T2 U0 U1 U2 : Tape Bool}
    (h :
      Tape.Equiv (encodedGuardedStructuredTapes [T0, T1, T2])
        (encodedGuardedStructuredTapes [U0, U1, U2])) :
    T0 = U0 ∧ T1 = U1 ∧ T2 = U2 := by
  rcases h with ⟨_hleft, _hhead, hright⟩
  rw [encodedGuardedStructuredTapes_three_right T0 T1 T2,
    encodedGuardedStructuredTapes_three_right U0 U1 U2] at hright
  simp only [logicalTapeCode_eq_map_some] at hright
  obtain ⟨bitT, restT, hbitsT⟩ :=
    logicalTapeBits_exists_cons (guardLogicalTape T2)
  obtain ⟨bitU, restU, hbitsU⟩ :=
    logicalTapeBits_exists_cons (guardLogicalTape U2)
  rw [dropTrailingNone_threeBlock _ _ _ (by rw [hbitsT]; simp),
    dropTrailingNone_threeBlock _ _ _ (by rw [hbitsU]; simp)] at hright
  rcases
      map_some_append_none_cons_inj
        (logicalTapeBits (guardLogicalTape T0))
        (logicalTapeBits (guardLogicalTape U0)) _ _ hright with
    ⟨h0, hrest⟩
  rcases
      map_some_append_none_cons_inj
        (logicalTapeBits (guardLogicalTape T1))
        (logicalTapeBits (guardLogicalTape U1)) _ _ hrest with
    ⟨h1, h2m⟩
  have h2 :
      logicalTapeBits (guardLogicalTape T2) =
        logicalTapeBits (guardLogicalTape U2) :=
    map_some_inj h2m
  exact
    ⟨guardLogicalTape_inj (logicalTapeBits_inj h0),
      guardLogicalTape_inj (logicalTapeBits_inj h1),
      guardLogicalTape_inj (logicalTapeBits_inj h2)⟩

/--
Distinct logical three-tape layouts have non-equivalent guarded encodings.
This is the per-step progress producer for divergence transfers: any step
that moves a cursor or changes a cell changes the encoding class.
-/
theorem encodedGuardedStructuredTapes_three_not_equiv_of_ne
    {T0 T1 T2 U0 U1 U2 : Tape Bool}
    (hne : ¬ (T0 = U0 ∧ T1 = U1 ∧ T2 = U2)) :
    ¬ Tape.Equiv (encodedGuardedStructuredTapes [T0, T1, T2])
      (encodedGuardedStructuredTapes [U0, U1, U2]) :=
  fun h => hne (encodedGuardedStructuredTapes_three_equiv_inj h)

private theorem exists_three_of_length_eq_three {α : Type _}
    {l : List α} (h : l.length = 3) :
    exists a b c : α, l = [a, b, c] := by
  cases l with
  | nil => simp at h
  | cons a l =>
      cases l with
      | nil => simp at h
      | cons b l =>
          cases l with
          | nil => simp at h
          | cons c l =>
              cases l with
              | nil => exact ⟨a, b, c, rfl⟩
              | cons d l => simp at h

/--
List form of the progress producer for three-tape structured trajectories.
-/
theorem encodedGuardedStructuredTapes_not_equiv_of_ne_of_length_three
    {A B : List (Tape Bool)}
    (hA : A.length = 3) (hB : B.length = 3) (hne : A ≠ B) :
    ¬ Tape.Equiv (encodedGuardedStructuredTapes A)
      (encodedGuardedStructuredTapes B) := by
  obtain ⟨a0, a1, a2, hAeq⟩ := exists_three_of_length_eq_three hA
  obtain ⟨b0, b1, b2, hBeq⟩ := exists_three_of_length_eq_three hB
  subst hAeq
  subst hBeq
  refine encodedGuardedStructuredTapes_three_not_equiv_of_ne ?_
  intro hcomponents
  rcases hcomponents with ⟨h0, h1, h2⟩
  exact hne (by rw [h0, h1, h2])

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
