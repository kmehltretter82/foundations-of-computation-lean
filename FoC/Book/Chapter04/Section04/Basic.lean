import FoC.Book.Chapter04.Section01
import FoC.Grammars.CFGToPDA
import FoC.Grammars.PDAToCFG

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

/-!
# Chapter 4, Section 4.4: Pushdown Automata

Pushdown automata add a stack to finite-state control. This section states
the computation API, acceptance modes, deterministic-PDA vocabulary, and the
standard conversions between CFGs and PDAs. The reusable modules are
{module}`FoC.Grammars.PDA`, {module}`FoC.Grammars.CFGToPDA`, and
{module}`FoC.Grammars.PDAToCFG`.

There are two levels of material on this page. The first half states the
general conversion theorems: CFGs can be simulated by PDAs, and finitely
presented PDAs can be converted back to CFGs after a normal-form step. The
second half gives concrete PDA examples and proves their accepted languages
exactly.
-/

open Languages
open Grammars

/-!
# PDA Computations

The first group relates one-step moves, arbitrary finite computations, and
length-indexed computations. The prefix-consumption lemmas make precise that a
PDA can only consume a prefix of its unread input.

The length-indexed relation is useful for induction over computations. The
unindexed relation is the ordinary "zero or more steps" reachability relation.
The bridge lemmas let later proofs move between the two.
-/

theorem pda_computation_transitive {M : PDA input stack state}
    {a b c : PDA.Configuration input stack state}
    (hab : PDA.Computes M a b) (hbc : PDA.Computes M b c) :
    PDA.Computes M a c :=
  PDA.computes_trans hab hbc

theorem pda_step_is_computation {M : PDA input stack state}
    {a b : PDA.Configuration input stack state} (h : PDA.Step M a b) :
    PDA.Computes M a b :=
  PDA.computes_of_step h

theorem pda_bounded_computation_is_computation
    {M : PDA input stack state}
    {n : Nat} {a b : PDA.Configuration input stack state}
    (h : PDA.ComputesIn M n a b) :
    PDA.Computes M a b :=
  PDA.computesIn_computes h

theorem pda_computation_has_length
    {M : PDA input stack state}
    {a b : PDA.Configuration input stack state}
    (h : PDA.Computes M a b) :
    exists n : Nat, PDA.ComputesIn M n a b :=
  PDA.computes_exists_length h

theorem pda_computation_iff_has_length
    {M : PDA input stack state}
    {a b : PDA.Configuration input stack state} :
    PDA.Computes M a b <->
      exists n : Nat, PDA.ComputesIn M n a b :=
  PDA.computes_iff_exists_computesIn

theorem pda_step_is_bounded_computation
    {M : PDA input stack state}
    {a b : PDA.Configuration input stack state}
    (h : PDA.Step M a b) :
    PDA.ComputesIn M 1 a b :=
  PDA.computesIn_of_step h

theorem pda_bounded_computation_transitive
    {M : PDA input stack state}
    {m n : Nat} {a b c : PDA.Configuration input stack state}
    (hab : PDA.ComputesIn M m a b)
    (hbc : PDA.ComputesIn M n b c) :
    PDA.ComputesIn M (m + n) a c :=
  PDA.computesIn_trans hab hbc

theorem pda_bounded_computation_zero_eq
    {M : PDA input stack state}
    {a b : PDA.Configuration input stack state}
    (h : PDA.ComputesIn M 0 a b) : a = b :=
  PDA.computesIn_zero_eq h

theorem pda_bounded_computation_succ_inv
    {M : PDA input stack state}
    {n : Nat} {a c : PDA.Configuration input stack state}
    (h : PDA.ComputesIn M (n + 1) a c) :
    exists b : PDA.Configuration input stack state,
      PDA.Step M a b ∧ PDA.ComputesIn M n b c :=
  PDA.computesIn_succ_inv h

theorem pda_bounded_computation_one_inv
    {M : PDA input stack state}
    {a c : PDA.Configuration input stack state}
    (h : PDA.ComputesIn M 1 a c) :
    PDA.Step M a c :=
  PDA.computesIn_one_inv h

theorem pda_step_consumes_empty_or_symbol
    {M : PDA input stack state}
    {c d : PDA.Configuration input stack state}
    (h : PDA.Step M c d) :
    (c.unread = d.unread) ∨
      exists a : input, c.unread = a :: d.unread :=
  PDA.step_consumes_empty_or_symbol h

theorem pda_step_consumes_prefix
    {M : PDA input stack state}
    {c d : PDA.Configuration input stack state}
    (h : PDA.Step M c d) :
    exists consumed : Word input,
      c.unread = Word.Concat consumed d.unread :=
  PDA.step_consumes_prefix h

theorem pda_bounded_computation_consumes_prefix
    {M : PDA input stack state}
    {n : Nat} {c d : PDA.Configuration input stack state}
    (h : PDA.ComputesIn M n c d) :
    exists consumed : Word input,
      c.unread = Word.Concat consumed d.unread :=
  PDA.computesIn_consumes_prefix h

theorem pda_computation_consumes_prefix
    {M : PDA input stack state}
    {c d : PDA.Configuration input stack state}
    (h : PDA.Computes M c d) :
    exists consumed : Word input,
      c.unread = Word.Concat consumed d.unread :=
  PDA.computes_consumes_prefix h

/-!
# Acceptance and Determinism

The definitions name accepted languages, finite presentations, top-pop normal
form, and deterministic context-free languages with an explicit end marker.

The accepted-language predicate packages the machine behavior as a language.
Finite presentations are needed for constructive conversion back to grammars:
the grammar must have a finite set of productions.
-/

def PDAAcceptedLanguage (M : PDA input stack state) : Language input :=
  PDA.AcceptedLanguage M

def FinitePresentationPDA (M : PDA input stack state) : Prop :=
  PDA.HasFinitePresentation M

def TopPopNormalFormPDA (M : PDA input stack state) : Prop :=
  PDA.PopsAtMostOne M

def FinitePresentationPDARecognizable (L : Language input) : Prop :=
  PDA.FinitePresentationRecognizable L

theorem pda_accepts_implies_final_state_accepts {M : PDA input stack state}
    {w : Word input} (h : PDA.Accepts M w) :
    PDA.AcceptsByFinalState M w :=
  PDA.accepts_implies_final_state_accepts h

theorem pda_accepts_implies_empty_stack_accepts {M : PDA input stack state}
    {w : Word input} (h : PDA.Accepts M w) :
    PDA.AcceptsByEmptyStack M w :=
  PDA.accepts_implies_empty_stack_accepts h

def DeterministicPDA (M : PDA input stack state) : Prop :=
  PDA.Deterministic M

def DeterministicPDARecognizable (L : Language input) : Prop :=
  exists stack : Type, exists state : Type, exists M : PDA input stack state,
    PDA.Deterministic M ∧ Language.Equal (PDA.AcceptedLanguage M) L

inductive EndMarked (input : Type u) where
  | symbol : input -> EndMarked input
  | end : EndMarked input

def endMarkedInputWord (w : Word input) : Word (EndMarked input) :=
  w.map EndMarked.symbol

def endMarkedWord (w : Word input) : Word (EndMarked input) :=
  Word.Concat (endMarkedInputWord w) [EndMarked.end]

def EndMarkedLanguage (L : Language input) : Language (EndMarked input) :=
  fun w => exists base : Word input, base ∈ L ∧ w = endMarkedWord base

def DeterministicContextFreeLanguageWithEndMarker (L : Language input) : Prop :=
  exists stack : Type, exists state : Type,
    exists M : PDA (EndMarked input) stack state,
      PDA.Deterministic M ∧
        Language.Equal (PDA.AcceptedLanguage M) (EndMarkedLanguage L)

/-!
# CFG to PDA

The standard construction simulates grammar derivations with a stack of
grammar symbols. The exactness theorem says it accepts precisely the generated
language.

Intuitively, the PDA keeps a sentential form on its stack. Expanding a
nonterminal corresponds to a grammar production, and matching a terminal
corresponds to consuming one input symbol.

Reader map for the Lean names below:

* {lit}`CFGToPDA G` is the machine constructed from a grammar {lit}`G`.
* {lit}`cfg_to_pda_language_exact` is the main theorem: the machine accepts
  exactly the words generated by the grammar.
* The finite-presentation statements record that a finite grammar gives a
  finite machine. This matters for the reverse conversion, where a PDA is
  converted back to a finite CFG.
* The last two theorems expose the two directions of exactness separately, so
  later examples can use only the direction they need.
-/

def CFGToPDA (G : CFG terminal nonterminal) :
    PDA terminal (Symbol terminal nonterminal) CFG.ToPDAState :=
  CFG.ToPDA G

/-!
The core theorem is a language equality. In ordinary textbook language, it
says: start with a context-free grammar, build the standard stack machine, and
no word is lost or added by the construction.
-/

theorem cfg_to_pda_language_exact
    {terminal nonterminal : Type} (G : CFG terminal nonterminal) :
    Language.Equal (PDA.AcceptedLanguage (CFGToPDA G))
      (CFG.GeneratedLanguage G) :=
  CFG.toPDA_acceptedLanguage_exact G

/-!
The next two declarations are about size, not language behavior. They say that
when the alphabet is finite and the grammar has finitely many productions, the
constructed PDA has a finite presentation.
-/

noncomputable def cfg_to_pda_finite_presentation
    (G : CFG terminal nonterminal)
    (terminalFinite : Foundation.FiniteType terminal)
    (hG : CFG.HasFiniteProductions G) :
    PDA.FinitePresentation (CFGToPDA G) :=
  CFG.toPDA_finitePresentation G terminalFinite hG

theorem cfg_to_pda_has_finite_presentation
    (G : CFG terminal nonterminal)
    (terminalFinite : Foundation.FiniteType terminal)
    (hG : CFG.HasFiniteProductions G) :
    FinitePresentationPDA (CFGToPDA G) :=
  CFG.toPDA_hasFinitePresentation G terminalFinite hG

theorem cfg_generated_language_finite_presentation_pda_recognizable
    {terminal nonterminal : Type}
    (G : CFG terminal nonterminal)
    (terminalFinite : Foundation.FiniteType terminal)
    (hG : CFG.HasFiniteProductions G) :
    PDA.FinitePresentationRecognizable (CFG.GeneratedLanguage G) := by
  exact ⟨Symbol terminal nonterminal, CFG.ToPDAState, CFGToPDA G,
    cfg_to_pda_finite_presentation G terminalFinite hG,
    cfg_to_pda_language_exact G⟩

theorem finite_production_context_free_language_finite_presentation_pda_recognizable
    {terminal : Type} {L : Language terminal}
    (terminalFinite : Foundation.FiniteType terminal)
    (hL : Section01.ContextFreeLanguage L) :
    PDA.FinitePresentationRecognizable L := by
  rcases hL with ⟨nonterminal, G, hGfinite, hGexact⟩
  exact ⟨Symbol terminal nonterminal, CFG.ToPDAState, CFGToPDA G,
    cfg_to_pda_finite_presentation G terminalFinite hGfinite,
    Language.equal_trans (cfg_to_pda_language_exact G) hGexact⟩

/-!
These are the same language-equality theorem split into the two directions used
in proofs: generated words are accepted by the constructed PDA, and accepted
words come from a grammar derivation.
-/

theorem cfg_to_pda_accepts_of_generates
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    {w : Word terminal} (h : w ∈ CFG.GeneratedLanguage G) :
    PDA.Accepts (CFGToPDA G) w :=
  CFG.toPDA_accepts_of_generates h

theorem cfg_to_pda_generates_of_accepts
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    {w : Word terminal} (h : PDA.Accepts (CFGToPDA G) w) :
    w ∈ CFG.GeneratedLanguage G :=
  CFG.toPDA_generates_of_accepts h

end Section04
end Chapter04
end Book
end FoC
