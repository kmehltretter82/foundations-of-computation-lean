import FoC.Grammars.CFG.Union

set_option doc.verso true

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace CFG

/-!
The concatenation grammar also uses a fresh start symbol, but its start rule
places a left derivation followed by a right derivation. The harder direction is
showing that every derivation from that start form preserves the left/right zone
split.
-/

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

def concatStartProduction (G : CFG terminal left) (H : CFG terminal right) :
    Production terminal (SumStart left right) where
  lhs := SumStart.start
  rhs := [Symbol.nonterminal (SumStart.inLeft G.start),
    Symbol.nonterminal (SumStart.inRight H.start)]

def concatLeftProduction (rule : Production terminal left) :
    Production terminal (SumStart left right) where
  lhs := SumStart.inLeft rule.lhs
  rhs := inLeftForm rule.rhs

def concatRightProduction (rule : Production terminal right) :
    Production terminal (SumStart left right) where
  lhs := SumStart.inRight rule.lhs
  rhs := inRightForm rule.rhs

/-!
The concatenation grammar has one new start production plus tagged copies of the
left and right production lists. The finite-production proof records that
concrete list before the soundness and inverse-zone lemmas inspect it.
-/

theorem concat_hasFiniteProductions
    {G : CFG terminal left} {H : CFG terminal right}
    (hG : HasFiniteProductions G) (hH : HasFiniteProductions H) :
    HasFiniteProductions (ConcatGrammar G H) := by
  cases hG with
  | intro rulesG hrulesG =>
      cases hH with
      | intro rulesH hrulesH =>
          exists [concatStartProduction G H] ++
            rulesG.map (concatLeftProduction (right := right)) ++
            rulesH.map (concatRightProduction (left := left))
          intro A rhs
          constructor
          · intro h
            cases h with
            | startRule =>
                exists concatStartProduction G H
                simp [concatStartProduction]
            | leftRule hprod =>
                cases (hrulesG _ _).mp hprod with
                | intro rule hrule =>
                    exists concatLeftProduction (right := right) rule
                    constructor
                    · apply List.mem_append_left
                      apply List.mem_append_right
                      exact List.mem_map.mpr
                        (Exists.intro rule (And.intro hrule.left rfl))
                    · constructor
                      · simp [concatLeftProduction, hrule.right.left]
                      · simp [concatLeftProduction, hrule.right.right]
            | rightRule hprod =>
                cases (hrulesH _ _).mp hprod with
                | intro rule hrule =>
                    exists concatRightProduction (left := left) rule
                    constructor
                    · apply List.mem_append_right
                      exact List.mem_map.mpr
                        (Exists.intro rule (And.intro hrule.left rfl))
                    · constructor
                      · simp [concatRightProduction, hrule.right.left]
                      · simp [concatRightProduction, hrule.right.right]
          · intro h
            cases h with
            | intro rule hrule =>
                have hmem := hrule.left
                simp [concatStartProduction, concatLeftProduction,
                  concatRightProduction] at hmem
                cases hmem with
                | inl hstart =>
                    rw [← hrule.right.left, ← hrule.right.right, hstart]
                    exact ConcatProduces.startRule
                | inr hrest =>
                    cases hrest with
                    | inl hleftRule =>
                        cases hleftRule with
                        | intro base hbase =>
                            cases hbase with
                            | intro hbaseMem hbaseEq =>
                                rw [← hrule.right.left, ← hrule.right.right, ← hbaseEq]
                                exact ConcatProduces.leftRule
                                  ((hrulesG base.lhs base.rhs).mpr
                                    (Exists.intro base
                                      (And.intro hbaseMem (And.intro rfl rfl))))
                    | inr hrightRule =>
                        cases hrightRule with
                        | intro base hbase =>
                            cases hbase with
                            | intro hbaseMem hbaseEq =>
                                rw [← hrule.right.left, ← hrule.right.right, ← hbaseEq]
                                exact ConcatProduces.rightRule
                                  ((hrulesH base.lhs base.rhs).mpr
                                    (Exists.intro base
                                      (And.intro hbaseMem (And.intro rfl rfl))))

/-!
The concat inverse proofs need context-zone lemmas: an equality whose middle
symbol is tagged as left can only have come from a left-tagged region, up to the
surrounding context. This prevents left and right derivations from being mixed.
-/

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

/-!
The right-zone version is slightly different because right-tagged forms occur
after the left grammar has already produced terminals. These lemmas isolate the
right component while preserving the terminal prefix around it.
-/

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

/-!
Zone inversion is the central concatenation argument. If a sentential form is a
tagged left part followed by a tagged right part, then one derivation step either
rewrites inside the left zone or inside the right zone; it cannot cross the
boundary or reintroduce the start symbol.
-/

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

/-!
After zone inversion, the language proof is straightforward: one mapped
derivation produces the left word, one mapped derivation produces the right word,
and terminal forms split into exactly the two generated pieces.
-/

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


end CFG

end Grammars
end FoC
