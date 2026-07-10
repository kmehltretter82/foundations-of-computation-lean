import FoC.Grammars.GeneralGrammar

set_option doc.verso true

/-!
# Permutations in general-grammar derivations

Adjacent exchange productions generate arbitrary permutations of marker
words. Pointwise singleton productions similarly rewrite a whole mapped word.
These derivation combinators keep concrete unrestricted-grammar examples from
reproving the same contextual rewriting inductions.
-/

namespace FoC
namespace Grammars
namespace GeneralGrammar

universe w

/-- A permutation of marker names is derivable when every pair of distinct
markers can be exchanged by a production. -/
theorem derives_map_of_perm_of_swaps
    {G : GeneralGrammar terminal nonterminal}
    {markerType : Type w}
    [DecidableEq markerType]
    (marker : markerType -> Symbol terminal nonterminal)
    (hswap : forall a b, a ≠ b ->
      G.produces [marker a, marker b] [marker b, marker a])
    {xs ys : List markerType}
    (hperm : xs.Perm ys) :
    Derives G (xs.map marker) (ys.map marker) := by
  induction hperm with
  | nil => exact Derives.refl []
  | cons a hperm ih =>
      simpa using derives_context [marker a] [] ih
  | swap x y rest =>
      by_cases hxy : y = x
      · subst y
        exact Derives.refl _
      · apply yields_derives
        simpa using
          yields_of_produces (hswap y x hxy) [] (rest.map marker)
  | trans hxy hyz ihxy ihyz => exact derives_trans ihxy ihyz

/-- Singleton productions can be applied pointwise across a mapped word. -/
theorem derives_map_of_pointwise_produces
    {G : GeneralGrammar terminal nonterminal}
    {itemType : Type w}
    (source target : itemType -> Symbol terminal nonterminal)
    (hproduces : forall item,
      G.produces [source item] [target item])
    (items : List itemType) :
    Derives G (items.map source) (items.map target) := by
  induction items with
  | nil => exact Derives.refl []
  | cons item items ih =>
      apply Derives.step (y := target item :: items.map source)
      · simpa using
          yields_of_produces (hproduces item) [] (items.map source)
      · simpa using derives_context [target item] [] ih

end GeneralGrammar
end Grammars
end FoC
