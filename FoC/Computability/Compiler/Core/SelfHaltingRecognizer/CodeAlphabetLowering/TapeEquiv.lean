import FoC.Computability.TapeLemmas

set_option doc.verso true

/-!
# Block-expansion tape equivalence

Local normalization lemmas for the finite code-alphabet lowering.  Keeping
them above the lowering rather than in the shared tape foundation avoids
invalidating unrelated Compiler constructions.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace CodeAlphabetLowering

private theorem eq_dropTrailingNone_append_replicate_none
    {symbol : Type u} (cells : List (Option symbol)) :
    exists padding : Nat,
      cells = Tape.dropTrailingNone cells ++
        List.replicate padding (none : Option symbol) := by
  induction cells with
  | nil => exact ⟨0, rfl⟩
  | cons cell rest ih =>
      rcases ih with ⟨padding, hrest⟩
      cases cell with
      | none =>
          by_cases hnormalized : Tape.dropTrailingNone rest = []
          · refine ⟨padding + 1, ?_⟩
            rw [Tape.dropTrailingNone_cons]
            rw [if_pos ⟨rfl, hnormalized⟩, List.nil_append, hrest,
              hnormalized, List.nil_append, List.replicate_succ]
          · refine ⟨padding, ?_⟩
            rw [Tape.dropTrailingNone_cons]
            rw [if_neg (fun h => hnormalized h.2), List.cons_append]
            exact congrArg (fun suffix => none :: suffix) hrest
      | some symbol =>
          refine ⟨padding, ?_⟩
          rw [Tape.dropTrailingNone_cons,
            if_neg (by simp), List.cons_append]
          exact congrArg (fun suffix => some symbol :: suffix) hrest

private theorem dropTrailingNone_flatMap_eq_normalized_flatMap
    {source : Type u} {target : Type v}
    (block : Option source -> List (Option target))
    (blankWidth : Nat)
    (hblank : block none = List.replicate blankWidth none)
    (cells : List (Option source)) :
    Tape.dropTrailingNone (cells.flatMap block) =
      Tape.dropTrailingNone
        ((Tape.dropTrailingNone cells).flatMap block) := by
  rcases eq_dropTrailingNone_append_replicate_none cells with
    ⟨padding, hcells⟩
  have appendReplicate (first second : Nat) :
      List.replicate first (none : Option target) ++
          List.replicate second none =
        List.replicate (first + second) none := by
    induction first with
    | zero => rw [Nat.zero_add]; rfl
    | succ first ih =>
        rw [Nat.succ_add]
        change none :: (List.replicate first none ++
            List.replicate second none) =
          none :: List.replicate (first + second) none
        exact congrArg (fun suffix => none :: suffix) ih
  have encodePadding : forall padding : Nat,
      exists encodedPadding : Nat,
        (List.replicate padding (none : Option source)).flatMap block =
          List.replicate encodedPadding (none : Option target) := by
    intro padding
    induction padding with
    | zero => exact ⟨0, rfl⟩
    | succ padding ih =>
        rcases ih with ⟨encodedPadding, hencoded⟩
        refine ⟨blankWidth + encodedPadding, ?_⟩
        simp only [List.replicate_succ, List.flatMap_cons, hblank, hencoded]
        exact appendReplicate blankWidth encodedPadding
  rcases encodePadding padding with ⟨encodedPadding, hencoded⟩
  calc
    Tape.dropTrailingNone (cells.flatMap block) =
        Tape.dropTrailingNone
          ((Tape.dropTrailingNone cells ++
            List.replicate padding none).flatMap block) :=
      congrArg (fun xs => Tape.dropTrailingNone (xs.flatMap block)) hcells
    _ = Tape.dropTrailingNone
          ((Tape.dropTrailingNone cells).flatMap block ++
            (List.replicate padding none).flatMap block) := by
      rw [List.flatMap_append]
    _ = Tape.dropTrailingNone
          ((Tape.dropTrailingNone cells).flatMap block ++
            List.replicate encodedPadding none) := by rw [hencoded]
    _ = Tape.dropTrailingNone
          ((Tape.dropTrailingNone cells).flatMap block) :=
      dropTrailingNone_append_replicate_none _ _

theorem dropTrailingNone_flatMap_congr
    {source : Type u} {target : Type v}
    (block : Option source -> List (Option target))
    (blankWidth : Nat)
    (hblank : block none = List.replicate blankWidth none)
    {xs ys : List (Option source)}
    (h : Tape.dropTrailingNone xs = Tape.dropTrailingNone ys) :
    Tape.dropTrailingNone (xs.flatMap block) =
      Tape.dropTrailingNone (ys.flatMap block) := by
  calc
    _ = Tape.dropTrailingNone
          ((Tape.dropTrailingNone xs).flatMap block) :=
      dropTrailingNone_flatMap_eq_normalized_flatMap block blankWidth hblank xs
    _ = Tape.dropTrailingNone
          ((Tape.dropTrailingNone ys).flatMap block) :=
      congrArg (fun cells => Tape.dropTrailingNone (cells.flatMap block)) h
    _ = _ :=
      (dropTrailingNone_flatMap_eq_normalized_flatMap
        block blankWidth hblank ys).symm

end CodeAlphabetLowering
end SelfHaltingRecognizer
end Computability
end FoC
