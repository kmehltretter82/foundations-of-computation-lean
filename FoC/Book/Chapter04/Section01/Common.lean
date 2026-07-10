import FoC.Book.Chapter04.Section01.Closure

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section01

open Foundation
open Languages
open Grammars

/-!
# Common Infrastructure for Concrete CFG Examples

A form-language interpretation of grammar symbols reduces soundness of whole derivations to soundness of individual productions.
-/

/-!
## Concrete Grammar Examples

The remaining code in this section builds exact grammar examples, beginning
with balanced parentheses. The helper soundness principles let a grammar proof
be checked by giving a semantic interpretation to each symbol.

For examples, the formalization often proves exactness by assigning a language
meaning to each nonterminal. Every production must be sound for that meaning,
and derivation soundness then follows for the generated language.
-/

theorem form_language_yields_sound_of_productions
    {G : CFG terminal nonterminal}
    {symbolLanguage : Symbol terminal nonterminal -> Language terminal}
    (hprod : forall A rhs,
      G.produces A rhs ->
        forall w, w ∈ CFG.FormLanguage symbolLanguage rhs ->
          w ∈ symbolLanguage (Symbol.nonterminal A))
    {x y : SententialForm terminal nonterminal} {w : Word terminal}
    (h : CFG.Yields G x y)
    (hw : w ∈ CFG.FormLanguage symbolLanguage y) :
    w ∈ CFG.FormLanguage symbolLanguage x := by
  rcases h with ⟨u, v, A, rhs, hA, hx, hy⟩
  rw [hy] at hw
  rw [hx]
  exact CFG.formLanguage_replace_sound symbolLanguage (hprod A rhs hA) hw

theorem form_language_derives_sound_of_productions
    {G : CFG terminal nonterminal}
    {symbolLanguage : Symbol terminal nonterminal -> Language terminal}
    (hprod : forall A rhs,
      G.produces A rhs ->
        forall w, w ∈ CFG.FormLanguage symbolLanguage rhs ->
          w ∈ symbolLanguage (Symbol.nonterminal A))
    {x y : SententialForm terminal nonterminal} {w : Word terminal}
    (h : CFG.Derives G x y)
    (hw : w ∈ CFG.FormLanguage symbolLanguage y) :
    w ∈ CFG.FormLanguage symbolLanguage x := by
  induction h with
  | refl _ =>
      exact hw
  | step hstep _ ih =>
      exact form_language_yields_sound_of_productions hprod hstep (ih hw)

end Section01
end Chapter04
end Book
end FoC
