import FoC.Book.Chapter04.Section01.Basic

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section01

open Foundation
open Languages
open Grammars

/-!
# Closure of Context-Free Languages

The foundational grammar combinators yield the book-facing closure theorems for union, concatenation, and Kleene star.
-/

/-!
## Closure of CFLs

The closure theorems for union, concatenation, and Kleene star are proved by
constructing new grammars and then showing their generated languages are exact.

Each construction has two kinds of theorem: generation lemmas saying how to
build words in the new grammar, and inverse lemmas saying every generated word
has the expected language-theoretic shape.
-/

theorem union_grammar_generates_left (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ CFG.GeneratedLanguage G) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) :=
  CFG.union_generates_left G H hw

theorem union_grammar_generates_right (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ CFG.GeneratedLanguage H) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) :=
  CFG.union_generates_right G H hw

theorem union_grammar_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H)) :
    w ∈ Language.Union (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.union_generates_inv G H h

theorem union_grammar_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.UnionGrammar G H) <->
      w ∈ Language.Union (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.union_generated_language_exact G H w

theorem context_free_languages_closed_under_union {L M : Language terminal}
    (hL : ContextFreeLanguage L) (hM : ContextFreeLanguage M) :
    ContextFreeLanguage (Language.Union L M) :=
  CFL.union_context_free hL hM

theorem concat_grammar_generates (G : CFG terminal left) (H : CFG terminal right)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G) (hy : y ∈ CFG.GeneratedLanguage H) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H) :=
  CFG.concat_generates G H hx hy

theorem concat_grammar_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H)) :
    w ∈ Language.Concat (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.concat_generates_inv G H h

theorem concat_grammar_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.ConcatGrammar G H) <->
      w ∈ Language.Concat (CFG.GeneratedLanguage G) (CFG.GeneratedLanguage H) :=
  CFG.concat_generated_language_exact G H w

theorem context_free_languages_closed_under_concatenation {L M : Language terminal}
    (hL : ContextFreeLanguage L) (hM : ContextFreeLanguage M) :
    ContextFreeLanguage (Language.Concat L M) :=
  CFL.concat_context_free hL hM

theorem star_grammar_generates_empty (G : CFG terminal nt) :
    ([] : Word terminal) ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) :=
  CFG.star_generates_empty G

theorem star_grammar_generates_cons (G : CFG terminal nt)
    {x y : Word terminal}
    (hx : x ∈ CFG.GeneratedLanguage G)
    (hy : y ∈ CFG.GeneratedLanguage (CFG.StarGrammar G)) :
    Word.Concat x y ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) :=
  CFG.star_generates_cons G hx hy

theorem star_grammar_generates_inv (G : CFG terminal nt) {w : Word terminal}
    (h : w ∈ CFG.GeneratedLanguage (CFG.StarGrammar G)) :
    w ∈ Language.Star (CFG.GeneratedLanguage G) :=
  CFG.star_generates_inv G h

theorem star_grammar_language_exact (G : CFG terminal nt) (w : Word terminal) :
    w ∈ CFG.GeneratedLanguage (CFG.StarGrammar G) <->
      w ∈ Language.Star (CFG.GeneratedLanguage G) :=
  CFG.star_generated_language_exact G w

theorem context_free_languages_closed_under_kleene_star {L : Language terminal}
    (hL : ContextFreeLanguage L) :
    ContextFreeLanguage (Language.Star L) :=
  CFL.star_context_free hL

end Section01
end Chapter04
end Book
end FoC
