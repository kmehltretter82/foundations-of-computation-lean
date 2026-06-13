import FoC.Grammars.CFG.Basic

set_option doc.verso true

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace CFG

/-!
# Derivations and generated languages

One-step yields replace a single nonterminal occurrence by a right-hand side.
Derivations are the reflexive-transitive closure, and generated languages are
terminal words reachable from the start nonterminal.
-/

def Yields (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  exists u, exists v, exists A, exists rhs,
    G.produces A rhs ∧
      x = u ++ [Symbol.nonterminal A] ++ v ∧
      y = u ++ rhs ++ v

inductive Derives (G : CFG terminal nonterminal) :
    SententialForm terminal nonterminal -> SententialForm terminal nonterminal -> Prop where
  | refl (x : SententialForm terminal nonterminal) : Derives G x x
  | step {x y z : SententialForm terminal nonterminal} :
      Yields G x y -> Derives G y z -> Derives G x z

def GeneratedLanguage (G : CFG terminal nonterminal) : Language terminal :=
  fun w => Derives G [Symbol.nonterminal G.start] (SententialForm.terminalWord w)

def GeneratedFrom (G : CFG terminal nonterminal) (A : nonterminal) : Language terminal :=
  fun w => Derives G [Symbol.nonterminal A] (SententialForm.terminalWord w)

def DerivationSymbolLanguage (G : CFG terminal nonterminal) :
    Symbol terminal nonterminal -> Language terminal
  | Symbol.terminal a => Language.Singleton (Word.Symbol a)
  | Symbol.nonterminal A => GeneratedFrom G A

def FormLanguage (symbolLanguage : Symbol terminal nonterminal -> Language terminal) :
    SententialForm terminal nonterminal -> Language terminal
  | [] => Language.Singleton Word.Empty
  | s :: rest => Language.Concat (symbolLanguage s) (FormLanguage symbolLanguage rest)

def ContextFree (L : Language terminal) : Prop :=
  exists nonterminal : Type, exists G : CFG terminal nonterminal,
    Language.Equal (GeneratedLanguage G) L

def Equivalent (G H : CFG terminal nonterminal) : Prop :=
  Language.Equal (GeneratedLanguage G) (GeneratedLanguage H)

/-!
# Regular grammar shapes

Right-regular and left-regular grammars are classified by the shape of every
production right-hand side.
-/

inductive RightRegularRHS : SententialForm terminal nonterminal -> Prop where
  | epsilon : RightRegularRHS []
  | nonterminal (A : nonterminal) :
      RightRegularRHS [Symbol.nonterminal A]
  | terminalThenNonterminal (a : terminal) (A : nonterminal) :
      RightRegularRHS [Symbol.terminal a, Symbol.nonterminal A]

def RightRegular (G : CFG terminal nonterminal) : Prop :=
  forall A rhs, G.produces A rhs -> RightRegularRHS rhs

inductive LeftRegularRHS : SententialForm terminal nonterminal -> Prop where
  | epsilon : LeftRegularRHS []
  | nonterminal (A : nonterminal) :
      LeftRegularRHS [Symbol.nonterminal A]
  | nonterminalThenTerminal (A : nonterminal) (a : terminal) :
      LeftRegularRHS [Symbol.nonterminal A, Symbol.terminal a]

def LeftRegular (G : CFG terminal nonterminal) : Prop :=
  forall A rhs, G.produces A rhs -> LeftRegularRHS rhs

/-!
# Reverse grammars and derivation algebra

Reversing each production right-hand side defines the reverse grammar. The
following derivation lemmas provide context, transitivity, and word-level
reasoning used by parse-tree and closure constructions.
-/

def ReverseGrammar (G : CFG terminal nonterminal) :
    CFG terminal nonterminal where
  start := G.start
  produces := fun A rhs =>
    exists original, G.produces A original ∧ rhs = original.reverse
  nonterminalsFinite := G.nonterminalsFinite

theorem derives_refl (G : CFG terminal nonterminal)
    (x : SententialForm terminal nonterminal) : Derives G x x :=
  Derives.refl x

theorem yields_derives {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Yields G x y) :
    Derives G x y :=
  Derives.step h (Derives.refl y)

theorem derives_trans {G : CFG terminal nonterminal}
    {x y z : SententialForm terminal nonterminal}
    (hxy : Derives G x y) (hyz : Derives G y z) : Derives G x z := by
  induction hxy with
  | refl _ => exact hyz
  | step hstep _ ih => exact Derives.step hstep (ih hyz)

theorem yields_context {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Yields G x y)
    (s t : SententialForm terminal nonterminal) :
    Yields G (s ++ x ++ t) (s ++ y ++ t) := by
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
                          exists s ++ u
                          exists v ++ t
                          exists A
                          exists rhs
                          constructor
                          · exact hprod
                          constructor
                          · rw [hx]
                            simp [List.append_assoc]
                          · rw [hy]
                            simp [List.append_assoc]

theorem reverseGrammar_hasFiniteProductions
    {G : CFG terminal nonterminal}
    (hG : HasFiniteProductions G) :
    HasFiniteProductions (ReverseGrammar G) := by
  cases hG with
  | intro rules hrules =>
      exists rules.map
        (fun rule : Production terminal nonterminal =>
          { lhs := rule.lhs, rhs := rule.rhs.reverse })
      intro A rhs
      constructor
      · intro hprod
        cases hprod with
        | intro original horiginal =>
            cases (hrules A original).mp horiginal.left with
            | intro rule hrule =>
                exists { lhs := rule.lhs, rhs := rule.rhs.reverse }
                constructor
                · apply List.mem_map.mpr
                  exists rule
                  exact ⟨hrule.left, rfl⟩
                constructor
                · rw [hrule.right.left]
                · rw [horiginal.right, hrule.right.right]
      · intro hrule
        cases hrule with
        | intro reversedRule hreversedRule =>
            have hmem :=
              List.mem_map.mp hreversedRule.left
            cases hmem with
            | intro rule hrule =>
                rw [← hrule.right] at hreversedRule
                exists rule.rhs
                constructor
                · exact (hrules A rule.rhs).mpr
                    ⟨rule, hrule.left, hreversedRule.right.left, rfl⟩
                · exact hreversedRule.right.right.symm

/-!
Reversal is proved one derivation step at a time. A yield in the original grammar
becomes a yield in the reversed grammar after reversing both the context and the
right-hand side of the production.
-/

theorem reverseGrammar_yields {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Yields G x y) :
    Yields (ReverseGrammar G) x.reverse y.reverse := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  exists v.reverse
                  exists u.reverse
                  exists A
                  exists rhs.reverse
                  constructor
                  · exists rhs
                    exact ⟨hrhs.left, rfl⟩
                  constructor
                  · rw [hrhs.right.left]
                    simp [List.reverse_append]
                  · rw [hrhs.right.right]
                    simp [List.reverse_append, List.append_assoc]

theorem reverseGrammar_yields_inv {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Yields (ReverseGrammar G) x y) :
    Yields G x.reverse y.reverse := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs.left with
                  | intro original horiginal =>
                      exists v.reverse
                      exists u.reverse
                      exists A
                      exists original
                      constructor
                      · exact horiginal.left
                      constructor
                      · rw [hrhs.right.left]
                        simp [List.reverse_append]
                      · rw [hrhs.right.right, horiginal.right]
                        simp [List.reverse_append, List.append_assoc]

theorem reverseGrammar_derives {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Derives G x y) :
    Derives (ReverseGrammar G) x.reverse y.reverse := by
  induction h with
  | refl x =>
      exact Derives.refl x.reverse
  | step hstep _ ih =>
      exact Derives.step (reverseGrammar_yields hstep) ih

theorem reverseGrammar_derives_inv {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Derives (ReverseGrammar G) x y) :
    Derives G x.reverse y.reverse := by
  induction h with
  | refl x =>
      exact Derives.refl x.reverse
  | step hstep _ ih =>
      exact Derives.step (reverseGrammar_yields_inv hstep) ih

theorem reverseGrammar_generates {G : CFG terminal nonterminal}
    {w : Word terminal} (h : w ∈ GeneratedLanguage G) :
    Word.Reverse w ∈ GeneratedLanguage (ReverseGrammar G) := by
  have hrev := reverseGrammar_derives h
  simpa [GeneratedLanguage, SententialForm.terminalWord_reverse] using hrev

theorem reverseGrammar_generates_inv {G : CFG terminal nonterminal}
    {w : Word terminal} (h : w ∈ GeneratedLanguage (ReverseGrammar G)) :
    Word.Reverse w ∈ GeneratedLanguage G := by
  have hrev := reverseGrammar_derives_inv h
  simpa [GeneratedLanguage, SententialForm.terminalWord_reverse] using hrev

theorem reverseGrammar_language_exact (G : CFG terminal nonterminal) :
    Language.Equal (GeneratedLanguage (ReverseGrammar G))
      (Language.Reverse (GeneratedLanguage G)) := by
  intro w
  constructor
  · exact reverseGrammar_generates_inv
  · intro hw
    have hgen := reverseGrammar_generates (G := G) hw
    simpa [Word.Reverse] using hgen

theorem leftRegular_reverseGrammar_rightRegular
    {G : CFG terminal nonterminal}
    (hG : LeftRegular G) :
    RightRegular (ReverseGrammar G) := by
  intro A rhs hprod
  cases hprod with
  | intro original horiginal =>
      rw [horiginal.right]
      cases hG A original horiginal.left with
      | epsilon =>
          exact RightRegularRHS.epsilon
      | nonterminal B =>
          exact RightRegularRHS.nonterminal B
      | nonterminalThenTerminal B a =>
          exact RightRegularRHS.terminalThenNonterminal a B

theorem rightRegular_reverseGrammar_leftRegular
    {G : CFG terminal nonterminal}
    (hG : RightRegular G) :
    LeftRegular (ReverseGrammar G) := by
  intro A rhs hprod
  cases hprod with
  | intro original horiginal =>
      rw [horiginal.right]
      cases hG A original horiginal.left with
      | epsilon =>
          exact LeftRegularRHS.epsilon
      | nonterminal B =>
          exact LeftRegularRHS.nonterminal B
      | terminalThenNonterminal a B =>
          exact LeftRegularRHS.nonterminalThenTerminal B a

/-!
The context lemmas below are the shared algebra for all closure constructions.
They say that a derivation can be placed inside surrounding sentential forms and
that a self-embedding derivation can be iterated, which is the proof shape used
later for pumping-style arguments.
-/

theorem derives_context {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Derives G x y)
    (s t : SententialForm terminal nonterminal) :
    Derives G (s ++ x ++ t) (s ++ y ++ t) := by
  induction h with
  | refl _ => exact Derives.refl _
  | step hstep _ ih => exact Derives.step (yields_context hstep s t) ih

theorem derives_append_left {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Derives G x y)
    (s : SententialForm terminal nonterminal) :
    Derives G (s ++ x) (s ++ y) := by
  simpa using derives_context h s []

theorem derives_append_right {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Derives G x y)
    (t : SententialForm terminal nonterminal) :
    Derives G (x ++ t) (y ++ t) := by
  simpa using derives_context h [] t

theorem derives_pumped_loop {G : CFG terminal nonterminal}
    {A : nonterminal} {x y z : Word terminal}
    (hloop :
      Derives G [Symbol.nonterminal A]
        (SententialForm.terminalWord x ++ [Symbol.nonterminal A] ++
          SententialForm.terminalWord z))
    (hbase :
      Derives G [Symbol.nonterminal A] (SententialForm.terminalWord y)) :
    forall n : Nat,
      Derives G [Symbol.nonterminal A]
        (SententialForm.terminalWord
          (Word.Concat (Word.RepeatWord x n)
            (Word.Concat y (Word.RepeatWord z n)))) := by
  intro n
  induction n with
  | zero =>
      simpa [Word.RepeatWord, Word.Concat] using hbase
  | succ n ih =>
      have hctx :
          Derives G
            (SententialForm.terminalWord x ++ [Symbol.nonterminal A] ++
              SententialForm.terminalWord z)
            (SententialForm.terminalWord x ++
              SententialForm.terminalWord
                (Word.Concat (Word.RepeatWord x n)
                  (Word.Concat y (Word.RepeatWord z n))) ++
              SententialForm.terminalWord z) := by
        simpa [List.append_assoc] using
          derives_context ih (SententialForm.terminalWord x)
            (SententialForm.terminalWord z)
      have hAll := derives_trans hloop hctx
      have htarget :
          SententialForm.terminalWord (nt := nonterminal) x ++
              SententialForm.terminalWord (nt := nonterminal)
                (Word.Concat (Word.RepeatWord x n)
                  (Word.Concat y (Word.RepeatWord z n))) ++
              SententialForm.terminalWord (nt := nonterminal) z =
            SententialForm.terminalWord (nt := nonterminal)
              (Word.Concat (Word.RepeatWord x (n + 1))
                (Word.Concat y (Word.RepeatWord z (n + 1)))) := by
        simp [SententialForm.terminalWord, Word.Concat, Word.RepeatWord,
          List.append_assoc]
        simpa [Word.Concat] using
          congrArg
            (fun w : Word terminal =>
              w.map (Symbol.terminal (nonterminal := nonterminal)))
            (Word.repeatWord_concat_self z n)
      rw [← htarget]
      exact hAll

theorem generated_language_mem (G : CFG terminal nonterminal) (w : Word terminal) :
    w ∈ GeneratedLanguage G <->
      Derives G [Symbol.nonterminal G.start] (SententialForm.terminalWord w) :=
  Iff.rfl

theorem formLanguage_empty
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal) :
    Word.Empty ∈ FormLanguage symbolLanguage [] :=
  rfl

/-!
Form-language concatenation is the semantic counterpart of list append on
sentential forms. It provides the standard split-and-combine interface used by
the closure proofs below.
-/

theorem formLanguage_append
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (x y : SententialForm terminal nonterminal) :
    Language.Equal (FormLanguage symbolLanguage (x ++ y))
      (Language.Concat (FormLanguage symbolLanguage x) (FormLanguage symbolLanguage y)) := by
  induction x with
  | nil =>
      intro w
      constructor
      · intro hw
        exists Word.Empty
        exists w
      · intro hw
        cases hw with
        | intro wx hwx =>
            cases hwx with
            | intro wy hwy =>
                cases hwy.left
                cases hwy.right.right
                exact hwy.right.left
  | cons s rest ih =>
      intro w
      constructor
      · intro hw
        cases hw with
        | intro first hfirst =>
            cases hfirst with
            | intro tail htail =>
                have htailSplit := (ih tail).mp htail.right.left
                cases htailSplit with
                | intro restWord hrestWord =>
                    cases hrestWord with
                    | intro yWord hyWord =>
                        exists Word.Concat first restWord
                        exists yWord
                        constructor
                        · exists first
                          exists restWord
                          exact And.intro htail.left
                            (And.intro hyWord.left rfl)
                        constructor
                        · exact hyWord.right.left
                        · calc
                            w = Word.Concat first tail := htail.right.right
                            _ = Word.Concat first (Word.Concat restWord yWord) := by
                              rw [hyWord.right.right]
                            _ = Word.Concat (Word.Concat first restWord) yWord := by
                              rw [← Word.concat_assoc]
      · intro hw
        cases hw with
        | intro pref hp =>
            cases hp with
            | intro suffix hs =>
                cases hs.left with
                | intro first hfirst =>
                    cases hfirst with
                    | intro restWord hrestWord =>
                        have htail : Word.Concat restWord suffix ∈
                            FormLanguage symbolLanguage (rest ++ y) :=
                          (ih (Word.Concat restWord suffix)).mpr
                            (Exists.intro restWord
                              (Exists.intro suffix
                                (And.intro hrestWord.right.left
                                  (And.intro hs.right.left rfl))))
                        exists first
                        exists Word.Concat restWord suffix
                        constructor
                        · exact hrestWord.left
                        constructor
                        · exact htail
                        · calc
                            w = Word.Concat pref suffix := hs.right.right
                            _ = Word.Concat (Word.Concat first restWord) suffix := by
                              rw [hrestWord.right.right]
                            _ = Word.Concat first (Word.Concat restWord suffix) := by
                              rw [Word.concat_assoc]

/-!
Replacement soundness is the local semantic rule for one grammar step inside a
larger context. If the replacement right-hand side denotes only words from the
nonterminal language, then the whole surrounding form remains sound.
-/

theorem formLanguage_replace_sound
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    {u rhs v : SententialForm terminal nonterminal}
    {A : nonterminal} {w : Word terminal}
    (hlocal : forall x, x ∈ FormLanguage symbolLanguage rhs ->
      x ∈ symbolLanguage (Symbol.nonterminal A))
    (hw : w ∈ FormLanguage symbolLanguage (u ++ rhs ++ v)) :
    w ∈ FormLanguage symbolLanguage (u ++ [Symbol.nonterminal A] ++ v) := by
  have hu := (formLanguage_append symbolLanguage u (rhs ++ v) w).mp (by
    simpa [List.append_assoc] using hw)
  cases hu with
  | intro pref hp =>
      cases hp with
      | intro suffix hs =>
          have hsSplit := (formLanguage_append symbolLanguage rhs v suffix).mp hs.right.left
          cases hsSplit with
          | intro middle hm =>
              cases hm with
              | intro tail ht =>
                  have hnew : w ∈ FormLanguage symbolLanguage
                      (u ++ ([Symbol.nonterminal A] ++ v)) := by
                    apply (formLanguage_append symbolLanguage u
                      ([Symbol.nonterminal A] ++ v) w).mpr
                    exists pref
                    exists Word.Concat middle tail
                    constructor
                    · exact hs.left
                    constructor
                    · exists middle
                      exists tail
                      exact And.intro (hlocal middle ht.left)
                        (And.intro ht.right.left rfl)
                    · calc
                        w = Word.Concat pref suffix := hs.right.right
                        _ = Word.Concat pref (Word.Concat middle tail) := by
                          rw [ht.right.right]
                  simpa [List.append_assoc] using hnew

theorem terminalWord_mem_formLanguage
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hterminal : forall a, Word.Symbol a ∈ symbolLanguage (Symbol.terminal a))
    (w : Word terminal) :
    w ∈ FormLanguage symbolLanguage (SententialForm.terminalWord (nt := nonterminal) w) := by
  induction w with
  | nil =>
      rfl
  | cons a rest ih =>
      exists [a]
      exists rest
      constructor
      · exact hterminal a
      constructor
      · exact ih
      · rfl

theorem formLanguage_derives {G : CFG terminal nonterminal}
    {sf : SententialForm terminal nonterminal} {w : Word terminal}
    (h : w ∈ FormLanguage (DerivationSymbolLanguage G) sf) :
    Derives G sf (SententialForm.terminalWord w) := by
  induction sf generalizing w with
  | nil =>
      cases h
      exact Derives.refl []
  | cons s rest ih =>
      cases h with
      | intro first hfirst =>
          cases hfirst with
          | intro tail htail =>
              have hrest := ih htail.right.left
              cases s with
              | terminal a =>
                  have hfirstEq : first = [a] := htail.left
                  rw [htail.right.right, hfirstEq]
                  change Derives G (Symbol.terminal a :: rest)
                    (SententialForm.terminalWord (Word.Concat [a] tail))
                  have hctx := derives_context hrest [Symbol.terminal a] []
                  rw [SententialForm.terminalWord_append]
                  simpa [SententialForm.terminalWord] using hctx
              | nonterminal A =>
                  have hsym : Derives G [Symbol.nonterminal A]
                      (SententialForm.terminalWord first) := htail.left
                  rw [htail.right.right]
                  change Derives G (Symbol.nonterminal A :: rest)
                    (SententialForm.terminalWord (Word.Concat first tail))
                  have hleft :
                      Derives G (Symbol.nonterminal A :: rest)
                        (SententialForm.terminalWord first ++ rest) := by
                    simpa using derives_context hsym [] rest
                  have hright :
                      Derives G (SententialForm.terminalWord first ++ rest)
                        (SententialForm.terminalWord first ++
                          SententialForm.terminalWord tail) := by
                    simpa using derives_context hrest (SententialForm.terminalWord first) []
                  rw [SententialForm.terminalWord_append]
                  exact derives_trans hleft hright

theorem context_free_of_equal {L M : Language terminal}
    (hL : ContextFree L) (hEq : Language.Equal L M) : ContextFree M := by
  cases hL with
  | intro nt hnt =>
      cases hnt with
      | intro G hG =>
          exists nt
          exists G
          exact Language.equal_trans hG hEq

end CFG

end Grammars
end FoC
