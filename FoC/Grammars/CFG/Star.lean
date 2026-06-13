import FoC.Grammars.CFG.Concat

set_option doc.verso true

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace CFG

/-!
Kleene star uses a fresh start symbol that either stops with the empty word or
emits one body derivation and recurs. The body nonterminals are tagged copies of
the original grammar's nonterminals.
-/

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

def starStopProduction : Production terminal (StarNT nt) where
  lhs := StarNT.start
  rhs := []

def starMoreProduction (G : CFG terminal nt) :
    Production terminal (StarNT nt) where
  lhs := StarNT.start
  rhs := [Symbol.nonterminal (StarNT.body G.start), Symbol.nonterminal StarNT.start]

def starBodyProduction (rule : Production terminal nt) :
    Production terminal (StarNT nt) where
  lhs := StarNT.body rule.lhs
  rhs := starBodyForm rule.rhs

/-!
The star grammar adds a stop production, a recursive "more" production, and
tagged copies of the body grammar. The finite-production proof makes that finite
list explicit before the semantic induction over repeated pieces begins.
-/

theorem star_hasFiniteProductions
    {G : CFG terminal nt}
    (hG : HasFiniteProductions G) :
    HasFiniteProductions (StarGrammar G) := by
  cases hG with
  | intro rules hrules =>
      exists [starStopProduction (terminal := terminal) (nt := nt),
        starMoreProduction G] ++ rules.map starBodyProduction
      intro A rhs
      constructor
      · intro h
        cases h with
        | stop =>
            exists starStopProduction (terminal := terminal) (nt := nt)
            simp [starStopProduction]
        | more =>
            exists starMoreProduction G
            simp [starMoreProduction]
        | bodyRule hprod =>
            cases (hrules _ _).mp hprod with
            | intro rule hrule =>
                exists starBodyProduction rule
                constructor
                · apply List.mem_append_right
                  exact List.mem_map.mpr
                    (Exists.intro rule (And.intro hrule.left rfl))
                · constructor
                  · simp [starBodyProduction, hrule.right.left]
                  · simp [starBodyProduction, hrule.right.right]
      · intro h
        cases h with
        | intro rule hrule =>
            have hmem := hrule.left
            simp [starStopProduction, starMoreProduction, starBodyProduction] at hmem
            cases hmem with
            | inl hstop =>
                rw [← hrule.right.left, ← hrule.right.right, hstop]
                exact StarProduces.stop
            | inr hrest =>
                cases hrest with
                | inl hmore =>
                    rw [← hrule.right.left, ← hrule.right.right, hmore]
                    exact StarProduces.more
                | inr hbody =>
                    cases hbody with
                    | intro base hbase =>
                        cases hbase with
                        | intro hbaseMem hbaseEq =>
                            rw [← hrule.right.left, ← hrule.right.right, ← hbaseEq]
                            exact StarProduces.bodyRule
                              ((hrules base.lhs base.rhs).mpr
                                (Exists.intro base
                                  (And.intro hbaseMem (And.intro rfl rfl))))

def StarSymbolLanguage (G : CFG terminal nt) :
    Symbol terminal (StarNT nt) -> Language terminal
  | Symbol.terminal a => Language.Singleton (Word.Symbol a)
  | Symbol.nonterminal StarNT.start => Language.Star (GeneratedLanguage G)
  | Symbol.nonterminal (StarNT.body A) => GeneratedFrom G A

theorem starBodyForm_formLanguage_to_derivation
    (G : CFG terminal nt) {sf : SententialForm terminal nt} {w : Word terminal}
    (h : w ∈ FormLanguage (StarSymbolLanguage G) (starBodyForm sf)) :
    w ∈ FormLanguage (DerivationSymbolLanguage G) sf := by
  induction sf generalizing w with
  | nil =>
      exact h
  | cons s rest ih =>
      cases s with
      | terminal a =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)
      | nonterminal A =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)

/-!
Star soundness follows the grammar structure: stop generates the empty list of
pieces, more adds one generated body word and recurses, and body productions are
interpreted through the tagged body form language.
-/

theorem star_production_sound (G : CFG terminal nt)
    {A : StarNT nt} {rhs : SententialForm terminal (StarNT nt)}
    (hprod : StarProduces G A rhs) :
    forall w, w ∈ FormLanguage (StarSymbolLanguage G) rhs ->
      w ∈ StarSymbolLanguage G (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | stop =>
      cases hw
      exact Language.star_empty_word (GeneratedLanguage G)
  | more =>
      cases hw with
      | intro first hfirst =>
          cases hfirst with
          | intro tail htail =>
              have htailStar : tail ∈ Language.Star (GeneratedLanguage G) := by
                cases htail.right.left with
                | intro starPart hstarPart =>
                    cases hstarPart with
                    | intro emptyPart hemptyPart =>
                      cases hemptyPart.right.left
                      rw [hemptyPart.right.right, Word.concat_empty_right]
                      exact hemptyPart.left
              rw [htail.right.right]
              exact Language.star_concat
                (Language.star_of_mem (GeneratedLanguage G) htail.left)
                htailStar
  | bodyRule hG =>
      rename_i A rhs
      have hbody := starBodyForm_formLanguage_to_derivation G hw
      have hstep : Yields G [Symbol.nonterminal A] rhs := by
        exists []
        exists []
        exists A
        exists rhs
        constructor
        · exact hG
        constructor
        · rfl
        · simp
      exact Derives.step hstep (formLanguage_derives hbody)

theorem star_yields_sound (G : CFG terminal nt)
    {x y : SententialForm terminal (StarNT nt)} {w : Word terminal}
    (h : Yields (StarGrammar G) x y)
    (hw : w ∈ FormLanguage (StarSymbolLanguage G) y) :
    w ∈ FormLanguage (StarSymbolLanguage G) x := by
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
                          rw [hy] at hw
                          rw [hx]
                          exact formLanguage_replace_sound
                            (StarSymbolLanguage G)
                            (star_production_sound G hprod)
                            hw

theorem star_derives_sound (G : CFG terminal nt)
    {x y : SententialForm terminal (StarNT nt)} {w : Word terminal}
    (h : Derives (StarGrammar G) x y)
    (hw : w ∈ FormLanguage (StarSymbolLanguage G) y) :
    w ∈ FormLanguage (StarSymbolLanguage G) x := by
  induction h with
  | refl _ =>
      exact hw
  | step hstep _ ih =>
      exact star_yields_sound G hstep (ih hw)

/-!
The final star theorems prove both directions. Soundness interprets every
generated word as a concatenation of generated pieces; completeness builds a
star derivation by repeatedly using the recursive start production.
-/

theorem star_generates_inv (G : CFG terminal nt) {w : Word terminal}
    (h : w ∈ GeneratedLanguage (StarGrammar G)) :
    w ∈ Language.Star (GeneratedLanguage G) := by
  have hterminal : w ∈ FormLanguage (StarSymbolLanguage G)
      (SententialForm.terminalWord (nt := StarNT nt) w) :=
    terminalWord_mem_formLanguage (StarSymbolLanguage G) (by intro a; rfl) w
  have hsound := star_derives_sound G h hterminal
  cases hsound with
  | intro starPart hstarPart =>
      cases hstarPart with
      | intro emptyPart hemptyPart =>
          cases hemptyPart.right.left
          rw [hemptyPart.right.right, Word.concat_empty_right]
          exact hemptyPart.left

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

theorem star_generates_of_pieces (G : CFG terminal nt)
    (pieces : List (Word terminal))
    (hall : forall p, p ∈ pieces -> p ∈ GeneratedLanguage G) :
    Language.ConcatWords pieces ∈ GeneratedLanguage (StarGrammar G) := by
  induction pieces with
  | nil =>
      exact star_generates_empty G
  | cons p rest ih =>
      exact star_generates_cons G (hall p (List.Mem.head rest))
        (ih (by
          intro q hq
          exact hall q (List.Mem.tail p hq)))

theorem star_generated_language_exact (G : CFG terminal nt) (w : Word terminal) :
    w ∈ GeneratedLanguage (StarGrammar G) <->
      w ∈ Language.Star (GeneratedLanguage G) := by
  constructor
  · exact star_generates_inv G
  · intro hw
    cases hw with
    | intro pieces hpieces =>
        rw [← hpieces.right]
        exact star_generates_of_pieces G pieces hpieces.left

end CFG

end Grammars
end FoC
