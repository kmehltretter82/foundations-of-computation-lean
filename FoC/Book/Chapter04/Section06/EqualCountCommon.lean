import FoC.Book.Chapter04.Section06.Basics
import FoC.Grammars.GeneralGrammar.Permutation

set_option doc.verso true

/-!
# Equal-count marker permutations

The equal-count book examples use different concrete alphabets but the same
rewriting operation: adjacent marker swaps realize a permutation, including
inside an arbitrary sentential context. The repeat-block corollaries below
replace the pair-specific marker-moving inductions formerly repeated by the
three- and four-symbol examples.
-/

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

open Languages
open Grammars

universe w

/-- Lift a permutation of marker names into an arbitrary sentential context. -/
theorem markerPermutation_derives
    {G : GeneralGrammar terminal nonterminal}
    {markerType : Type w}
    [DecidableEq markerType]
    (marker : markerType -> Symbol terminal nonterminal)
    (hswap : forall a b, a ≠ b ->
      G.produces [marker a, marker b] [marker b, marker a])
    {xs ys : List markerType}
    (hperm : xs.Perm ys)
    (pre suffix : SententialForm terminal nonterminal) :
    GeneralGrammar.Derives G
      (pre ++ xs.map marker ++ suffix)
      (pre ++ ys.map marker ++ suffix) :=
  GeneralGrammar.derives_context pre suffix
    (GeneralGrammar.derives_map_of_perm_of_swaps marker hswap hperm)

/-- Move one marker rightward across a repeated block using permutation swaps. -/
theorem markerMovesRightOverRepeat
    {G : GeneralGrammar terminal nonterminal}
    {markerType : Type w}
    [DecidableEq markerType]
    (marker : markerType -> Symbol terminal nonterminal)
    (hswap : forall a b, a ≠ b ->
      G.produces [marker a, marker b] [marker b, marker a])
    (moving fixed : markerType) (n : Nat)
    (pre suffix : SententialForm terminal nonterminal) :
    GeneralGrammar.Derives G
      (pre ++ [marker moving] ++ List.replicate n (marker fixed) ++ suffix)
      (pre ++ List.replicate n (marker fixed) ++ [marker moving] ++ suffix) := by
  have hperm :
      ([moving] ++ List.replicate n fixed).Perm
        (List.replicate n fixed ++ [moving]) :=
    List.perm_append_comm
  simpa [List.append_assoc] using
    markerPermutation_derives marker hswap hperm pre suffix

/-- Move one marker leftward across a repeated block using permutation swaps. -/
theorem markerMovesLeftOverRepeat
    {G : GeneralGrammar terminal nonterminal}
    {markerType : Type w}
    [DecidableEq markerType]
    (marker : markerType -> Symbol terminal nonterminal)
    (hswap : forall a b, a ≠ b ->
      G.produces [marker a, marker b] [marker b, marker a])
    (moving fixed : markerType) (n : Nat)
    (pre suffix : SententialForm terminal nonterminal) :
    GeneralGrammar.Derives G
      (pre ++ List.replicate n (marker fixed) ++ [marker moving] ++ suffix)
      (pre ++ [marker moving] ++ List.replicate n (marker fixed) ++ suffix) := by
  have hperm :
      (List.replicate n fixed ++ [moving]).Perm
        ([moving] ++ List.replicate n fixed) :=
    List.perm_append_comm
  simpa [List.append_assoc] using
    markerPermutation_derives marker hswap hperm pre suffix

end Section06
end Chapter04
end Book
end FoC
