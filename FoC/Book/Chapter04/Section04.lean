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

/-!
# PDA to CFG

The reverse direction is organized around finite presentations and a top-pop
normal form. Pop normalization splits longer pops into finite helper-state
chains before applying the PDA-to-CFG construction.

The nonterminals of the constructed CFG summarize PDA behavior: they describe
which input words can take the PDA from one state and stack condition to
another. The many local lemmas below prove that those summaries match actual
PDA computations.

There are two important families of nonterminals in {lit}`PDAToCFG`:

* {lit}`empty p q` represents computations that move from state {lit}`p` to
  state {lit}`q` while preserving an empty stack.
* {lit}`between p A q` represents computations that start with stack symbol
  {lit}`A` on top and finish after exactly that symbol has been removed.

The construction is technical because PDA transitions can push several stack
symbols. The file first handles those local stack chains, then packages the
result into the familiar theorem that every finitely presented PDA recognizes a
context-free language.
-/

def PDAToCFG (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    CFG input (PDA.ToCFGNonterminal stack state) :=
  PDA.ToCFG M presentation

def PDAToCFGExact (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) : Prop :=
  PDA.ToCFGTopPopExact M presentation

def PDAPopNormalize (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    PDA input stack (PDA.PopNormalizedState (M := M) presentation) :=
  PDA.PopNormalize M presentation

def PDAPopNormalizeLanguageExact (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) : Prop :=
  PDA.PopNormalizeLanguageExact M presentation

def PDAToCFGNormalized (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    CFG input
      (PDA.ToCFGNonterminal stack
        (PDA.PopNormalizedState (M := M) presentation)) :=
  PDA.ToCFGNormalized M presentation

/-!
Pop normalization is the bridge between arbitrary finitely presented PDAs and
the easier top-pop case. It replaces a machine by an equivalent one whose
transitions pop at most one stack symbol. The language-exactness lemmas below
are the bookkeeping that lets us prove the conversion for the normalized
machine and then transfer it back to the original PDA.
-/

def pda_pop_normalize_finite_presentation
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    PDA.FinitePresentation (PDAPopNormalize M presentation) :=
  PDA.popNormalizeFinitePresentation M presentation

theorem pda_pop_normalize_top_pop
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    TopPopNormalFormPDA (PDAPopNormalize M presentation) :=
  PDA.popNormalize_popsAtMostOne M presentation

theorem pda_pop_normalize_accepts_of_accepts
    {M : PDA input stack state}
    (presentation : PDA.FinitePresentation M)
    {w : Word input}
    (h : PDA.Accepts M w) :
    PDA.Accepts (PDAPopNormalize M presentation) w :=
  PDA.popNormalize_accepts_of_accepts presentation h

theorem pda_accepted_language_subset_pop_normalize
    {M : PDA input stack state}
    (presentation : PDA.FinitePresentation M) :
    Language.Subset (PDA.AcceptedLanguage M)
      (PDA.AcceptedLanguage (PDAPopNormalize M presentation)) :=
  PDA.acceptedLanguage_subset_popNormalizeLanguage presentation

theorem pda_pop_normalize_accepts_original_of_accepts
    {M : PDA input stack state}
    (presentation : PDA.FinitePresentation M)
    {w : Word input}
    (h : PDA.Accepts (PDAPopNormalize M presentation) w) :
    PDA.Accepts M w :=
  PDA.popNormalize_accepts_original_of_accepts presentation h

theorem pda_pop_normalize_language_exact
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    PDAPopNormalizeLanguageExact M presentation :=
  PDA.popNormalizeLanguageExact M presentation

/-!
The next block starts the PDA-to-CFG proof itself.

The first few theorems say that the generated grammar is finite and sound:
anything the grammar generates is accepted by the original PDA. After that, the
lemmas build grammar derivations from individual PDA moves.

The names with {lit}`empty` refer to the nonterminal summarizing an empty-stack
computation from one state to another. The names with {lit}`between` refer to
the nonterminal summarizing a computation that removes one distinguished top
stack symbol.
-/

theorem pda_to_cfg_nonterminals_finite
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    (PDAToCFG M presentation).nonterminalsFinite =
      PDA.ToCFGNonterminal.finite
        presentation.stackFinite M.statesFinite :=
  PDA.toCFG_nonterminals_finite M presentation

theorem pda_to_cfg_hasFiniteProductions
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    CFG.HasFiniteProductions (PDAToCFG M presentation) :=
  PDA.toCFG_hasFiniteProductions M presentation

theorem pda_to_cfg_normalized_hasFiniteProductions
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    CFG.HasFiniteProductions (PDAToCFGNormalized M presentation) :=
  PDA.toCFGNormalized_hasFiniteProductions M presentation

theorem pda_to_cfg_accepts_of_generates
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input}
    (h : w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation)) :
    PDA.Accepts M w :=
  PDA.toCFG_accepts_of_generates h

theorem pda_to_cfg_start_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {q : state} {w : Word input}
    (haccept : M.accept q)
    (hbody : CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty M.start q)]
      (SententialForm.terminalWord w)) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_start_derives haccept hbody

theorem pda_to_cfg_empty_refl_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {q : state} :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty q q)]
      (SententialForm.terminalWord (Word.Empty : Word input)) :=
  PDA.toCFG_emptyRefl_derives

theorem pda_to_cfg_pop_step_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {chainRhs : SententialForm input (PDA.ToCFGNonterminal stack state)}
    {pref chainWord : Word input}
    (htransition : M.transition p a? [A] r push)
    (hchain : PDA.ToCFGChain r push q chainRhs)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (PDAToCFG M presentation))
      (PDA.inputPrefix (nonterminal := PDA.ToCFGNonterminal stack state) a?))
    (hchainWord : chainWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (PDAToCFG M presentation)) chainRhs) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Concat pref chainWord)) :=
  PDA.toCFG_popStep_derives htransition hchain hpref hchainWord

theorem pda_to_cfg_empty_step_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r s q : state} {a? : Option input}
    {push : Word stack}
    {chainRhs : SententialForm input (PDA.ToCFGNonterminal stack state)}
    {pref chainWord emptyWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : PDA.ToCFGChain r push s chainRhs)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (PDAToCFG M presentation))
      (PDA.inputPrefix (nonterminal := PDA.ToCFGNonterminal stack state) a?))
    (hchainWord : chainWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (PDAToCFG M presentation)) chainRhs)
    (hempty : CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord emptyWord))) :=
  PDA.toCFG_emptyStep_derives htransition hchain hpref hchainWord hempty

theorem pda_to_cfg_empty_before_top_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r s q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {chainRhs : SententialForm input (PDA.ToCFGNonterminal stack state)}
    {pref chainWord topWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : PDA.ToCFGChain r push s chainRhs)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (PDAToCFG M presentation))
      (PDA.inputPrefix (nonterminal := PDA.ToCFGNonterminal stack state) a?))
    (hchainWord : chainWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (PDAToCFG M presentation)) chainRhs)
    (htop : CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord topWord))) :=
  PDA.toCFG_emptyBeforeTop_derives htransition hchain hpref hchainWord htop

/-!
When a PDA transition pushes several stack symbols, the grammar must generate a
sequence of nonterminals, one for each pushed symbol. The {lit}`ToCFGChain`
lemmas below package that sequence. They are the formal version of saying:
"after this transition, handle the pushed stack string one symbol at a time."
-/

theorem pda_to_cfg_chain_derives_formLanguage
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {push : Word stack} {w : Word input}
    (h : PDA.ToCFGChainDerives M presentation p push q w) :
    exists rhs : SententialForm input (PDA.ToCFGNonterminal stack state),
      PDA.ToCFGChain p push q rhs ∧
        w ∈ CFG.FormLanguage
          (CFG.DerivationSymbolLanguage (PDAToCFG M presentation)) rhs :=
  PDA.toCFGChainDerives_formLanguage h

theorem pda_to_cfg_chain_derives_of_formLanguage
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {push : Word stack}
    {rhs : SententialForm input (PDA.ToCFGNonterminal stack state)}
    (hchain : PDA.ToCFGChain p push q rhs)
    {w : Word input}
    (hw : w ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (PDAToCFG M presentation)) rhs) :
    PDA.ToCFGChainDerives M presentation p push q w :=
  PDA.toCFGChainDerives_of_formLanguage hchain hw

theorem pda_to_cfg_chain_derives_append
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r q : state} {left right : Word stack} {x y : Word input}
    (hleft : PDA.ToCFGChainDerives M presentation p left r x)
    (hright : PDA.ToCFGChainDerives M presentation r right q y) :
    PDA.ToCFGChainDerives M presentation p (Word.Concat left right) q
      (Word.Concat x y) :=
  PDA.toCFGChainDerives_append hleft hright

theorem pda_to_cfg_pop_step_of_chain_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {pref chainWord : Word input}
    (htransition : M.transition p a? [A] r push)
    (hchain : PDA.ToCFGChainDerives M presentation r push q chainWord)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (PDAToCFG M presentation))
      (PDA.inputPrefix (nonterminal := PDA.ToCFGNonterminal stack state) a?)) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Concat pref chainWord)) :=
  PDA.toCFG_popStep_of_chainDerives htransition hchain hpref

theorem pda_to_cfg_empty_step_of_chain_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r s q : state} {a? : Option input}
    {push : Word stack}
    {pref chainWord emptyWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : PDA.ToCFGChainDerives M presentation r push s chainWord)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (PDAToCFG M presentation))
      (PDA.inputPrefix (nonterminal := PDA.ToCFGNonterminal stack state) a?))
    (hempty : CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord emptyWord))) :=
  PDA.toCFG_emptyStep_of_chainDerives htransition hchain hpref hempty

theorem pda_to_cfg_empty_before_top_of_chain_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r s q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {pref chainWord topWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : PDA.ToCFGChainDerives M presentation r push s chainWord)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (PDAToCFG M presentation))
      (PDA.inputPrefix (nonterminal := PDA.ToCFGNonterminal stack state) a?))
    (htop : CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord topWord))) :=
  PDA.toCFG_emptyBeforeTop_of_chainDerives htransition hchain hpref htop

/-!
The previous statements handled an optional input symbol uniformly. The next
specializations separate read transitions from epsilon transitions. They make
later proofs shorter because they do not need to repeatedly unpack
{lit}`Option input`.
-/

theorem pda_to_cfg_pop_read_of_chain_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r q : state} {A : stack} {a : input}
    {push : Word stack} {chainWord : Word input}
    (htransition : M.transition p (some a) [A] r push)
    (hchain : PDA.ToCFGChainDerives M presentation r push q chainWord) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat (Word.Symbol a) chainWord)) :=
  PDA.toCFG_popRead_of_chainDerives htransition hchain

theorem pda_to_cfg_pop_epsilon_of_chain_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r q : state} {A : stack}
    {push : Word stack} {chainWord : Word input}
    (htransition : M.transition p none [A] r push)
    (hchain : PDA.ToCFGChainDerives M presentation r push q chainWord) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord chainWord) :=
  PDA.toCFG_popEpsilon_of_chainDerives htransition hchain

theorem pda_to_cfg_empty_read_of_chain_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r s q : state} {a : input}
    {push : Word stack}
    {chainWord emptyWord : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hchain : PDA.ToCFGChainDerives M presentation r push s chainWord)
    (hempty : CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat (Word.Symbol a)
          (Word.Concat chainWord emptyWord))) :=
  PDA.toCFG_emptyRead_of_chainDerives htransition hchain hempty

theorem pda_to_cfg_empty_epsilon_of_chain_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r s q : state}
    {push : Word stack}
    {chainWord emptyWord : Word input}
    (htransition : M.transition p none [] r push)
    (hchain : PDA.ToCFGChainDerives M presentation r push s chainWord)
    (hempty : CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat chainWord emptyWord)) :=
  PDA.toCFG_emptyEpsilon_of_chainDerives htransition hchain hempty

theorem pda_to_cfg_empty_before_top_read_of_chain_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r s q : state} {A : stack} {a : input}
    {push : Word stack}
    {chainWord topWord : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hchain : PDA.ToCFGChainDerives M presentation r push s chainWord)
    (htop : CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat (Word.Symbol a)
          (Word.Concat chainWord topWord))) :=
  PDA.toCFG_emptyBeforeTopRead_of_chainDerives htransition hchain htop

theorem pda_to_cfg_empty_before_top_epsilon_of_chain_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p r s q : state} {A : stack}
    {push : Word stack}
    {chainWord topWord : Word input}
    (htransition : M.transition p none [] r push)
    (hchain : PDA.ToCFGChainDerives M presentation r push s chainWord)
    (htop : CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat chainWord topWord)) :=
  PDA.toCFG_emptyBeforeTopEpsilon_of_chainDerives htransition hchain htop

/-!
These are the base cases for converting actual PDA steps into grammar
derivations. An empty-stack step becomes an {lit}`empty` nonterminal derivation.
A top-pop step becomes a {lit}`between` nonterminal derivation. Each case has a
read and an epsilon variant.
-/

theorem pda_to_cfg_empty_read_of_step_empty_stack
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {a : input} {restInput : Word input}
    (hstep : PDA.Step M
      { state := p, unread := a :: restInput, stack := [] }
      { state := q, unread := restInput, stack := [] }) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord (Word.Symbol a)) :=
  PDA.toCFG_emptyRead_of_step_emptyStack hstep

theorem pda_to_cfg_empty_epsilon_of_step_empty_stack
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {restInput : Word input}
    (hstep : PDA.Step M
      { state := p, unread := restInput, stack := [] }
      { state := q, unread := restInput, stack := [] }) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord (Word.Empty : Word input)) :=
  PDA.toCFG_emptyEpsilon_of_step_emptyStack hstep

theorem pda_to_cfg_between_read_of_step_top_pop
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {A : stack} {a : input}
    {restInput : Word input} {tail : Word stack}
    (hnorm : PDA.PopsAtMostOne M)
    (hstep : PDA.Step M
      { state := p, unread := a :: restInput, stack := A :: tail }
      { state := q, unread := restInput, stack := tail }) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Symbol a)) :=
  PDA.toCFG_betweenRead_of_step_topPop hnorm hstep

theorem pda_to_cfg_between_epsilon_of_step_top_pop
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {A : stack}
    {restInput : Word input} {tail : Word stack}
    (hnorm : PDA.PopsAtMostOne M)
    (hstep : PDA.Step M
      { state := p, unread := restInput, stack := A :: tail }
      { state := q, unread := restInput, stack := tail }) :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Empty : Word input)) :=
  PDA.toCFG_betweenEpsilon_of_step_topPop hnorm hstep

theorem pda_to_cfg_empty_derives_cases_of_step_empty_stack
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hstep : PDA.Step M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    (sourceInput = targetInput ∧
      CFG.Derives (PDAToCFG M presentation)
        [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
        (SententialForm.terminalWord (Word.Empty : Word input))) ∨
    (exists a : input,
      sourceInput = a :: targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord (Word.Symbol a))) :=
  PDA.toCFG_emptyDerives_cases_of_step_emptyStack hstep

theorem pda_to_cfg_between_derives_cases_of_step_top_pop
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PDA.PopsAtMostOne M)
    (hstep : PDA.Step M
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    (sourceInput = targetInput ∧
      CFG.Derives (PDAToCFG M presentation)
        [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
        (SententialForm.terminalWord (Word.Empty : Word input))) ∨
    (exists a : input,
      sourceInput = a :: targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord (Word.Symbol a))) :=
  PDA.toCFG_betweenDerives_cases_of_step_topPop hnorm hstep

theorem pda_step_source_stack_empty_or_single_of_step_to_empty_stack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    {sourceStack : Word stack}
    (hnorm : PDA.PopsAtMostOne M)
    (hstep : PDA.Step M
      { state := p, unread := sourceInput, stack := sourceStack }
      { state := q, unread := targetInput, stack := [] }) :
    sourceStack = [] ∨ exists A : stack, sourceStack = [A] :=
  PDA.step_sourceStack_empty_or_single_of_step_to_emptyStack hnorm hstep

/-!
Short bounded computations are useful induction anchors. These lemmas prove
that computations of length zero, one, or two already have corresponding CFG
derivations. The length-two case is where top-pop normal form starts to matter:
one step can introduce a top symbol and the next step can remove it.
-/

theorem pda_to_cfg_empty_derives_of_computes_in_zero_empty_stack
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : PDA.ComputesIn M 0
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_computesIn_zero_emptyStack hcomp

theorem pda_to_cfg_empty_derives_of_computes_in_one_empty_stack
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : PDA.ComputesIn M 1
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_computesIn_one_emptyStack hcomp

theorem pda_to_cfg_empty_derives_of_computes_in_at_most_one_empty_stack
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hn : n <= 1)
    (hcomp : PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_computesIn_atMostOne_emptyStack hn hcomp

theorem pda_to_cfg_between_derives_of_computes_in_one_top_pop
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PDA.PopsAtMostOne M)
    (hcomp : PDA.ComputesIn M 1
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_betweenDerives_of_computesIn_one_topPop hnorm hcomp

theorem pda_to_cfg_empty_derives_of_computes_in_two_empty_stack
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PDA.PopsAtMostOne M)
    (hcomp : PDA.ComputesIn M 2
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_computesIn_two_emptyStack hnorm hcomp

theorem pda_to_cfg_empty_derives_of_computes_in_at_most_two_empty_stack
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PDA.PopsAtMostOne M)
    (hn : n <= 2)
    (hcomp : PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_computesIn_atMostTwo_emptyStack
    hnorm hn hcomp

/-!
The next lemmas lift those short-computation derivations all the way to the
start symbol of the constructed grammar. They are specialized conveniences for
accepting runs of length zero, one, or two.
-/

theorem pda_to_cfg_generates_of_accepts_in_zero
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : PDA.ComputesIn M 0 (PDA.initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_acceptsIn_zero haccept hcomp

theorem pda_to_cfg_generates_of_accepts_in_one
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : PDA.ComputesIn M 1 (PDA.initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_acceptsIn_one haccept hcomp

theorem pda_to_cfg_generates_of_accepts_in_two
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input} {qf : state}
    (hnorm : PDA.PopsAtMostOne M)
    (haccept : M.accept qf)
    (hcomp : PDA.ComputesIn M 2 (PDA.initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_acceptsIn_two hnorm haccept hcomp

theorem pda_to_cfg_generates_of_accepts_in_at_most_one
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (hn : n <= 1)
    (haccept : M.accept qf)
    (hcomp : PDA.ComputesIn M n (PDA.initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_acceptsIn_atMostOne hn haccept hcomp

theorem pda_to_cfg_generates_of_accepts_in_at_most_two
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (hnorm : PDA.PopsAtMostOne M)
    (hn : n <= 2)
    (haccept : M.accept qf)
    (hcomp : PDA.ComputesIn M n (PDA.initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_acceptsIn_atMostTwo hnorm hn haccept hcomp

/-!
The summary predicates below abstract the recurring proof shape. Instead of
repeating whole configurations every time, they name computations that consume
some input while emptying a stack segment or preserving an arbitrary tail.
These summaries are the induction targets used to prove PDA-to-CFG completeness.

The three main summaries are:

* {lit}`StackSummaryPDAComputesIn`: a stack word is consumed while an arbitrary
  tail is preserved.
* {lit}`EmptySummaryPDAComputesIn`: a computation runs with an empty-stack
  summary from state to state.
* {lit}`StackThenEmptySummaryPDAComputesIn`: first consume a stack word, then
  continue with an empty-stack summary.
-/

def EmptyStackPDAComputesIn (M : PDA input stack state)
    (n : Nat) (p : state) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  PDA.EmptyStackComputesIn M n p sourceInput q targetInput

theorem pda_empty_stack_trace_is_bounded_computation
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackPDAComputesIn M n p sourceInput q targetInput) :
    PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  PDA.emptyStackComputesIn_computesIn h

theorem pda_empty_stack_trace_is_computation
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackPDAComputesIn M n p sourceInput q targetInput) :
    PDA.Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  PDA.emptyStackComputesIn_computes h

theorem pda_to_cfg_empty_derives_of_empty_stack_trace
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackPDAComputesIn M n p sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_emptyStackComputesIn h

theorem pda_to_cfg_generates_of_empty_stack_accepts_in
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptyStackPDAComputesIn M n M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_emptyStackAcceptsIn haccept hcomp

def StackSummaryPDAComputesIn (M : PDA input stack state)
    (n : Nat) (p : state) (stackWord : Word stack)
    (sourceInput : Word input) (q : state)
    (targetInput : Word input) : Prop :=
  PDA.StackSummaryComputesIn M n p stackWord sourceInput q targetInput

def StackSummaryPDAComputes (M : PDA input stack state)
    (p : state) (stackWord : Word stack) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  PDA.StackSummaryComputes M p stackWord sourceInput q targetInput

def EmptySummaryPDAComputesIn (M : PDA input stack state)
    (n : Nat) (p : state) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  PDA.EmptySummaryComputesIn M n p sourceInput q targetInput

def EmptySummaryPDAComputes (M : PDA input stack state)
    (p : state) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  PDA.EmptySummaryComputes M p sourceInput q targetInput

def StackThenEmptySummaryPDAComputesIn (M : PDA input stack state)
    (n : Nat) (p : state) (stackWord : Word stack)
    (sourceInput : Word input) (q : state)
    (targetInput : Word input) : Prop :=
  PDA.StackThenEmptySummaryComputesIn M n p stackWord sourceInput
    q targetInput

def StackThenEmptySummaryPDAComputes (M : PDA input stack state)
    (p : state) (stackWord : Word stack) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  PDA.StackThenEmptySummaryComputes M p stackWord sourceInput
    q targetInput

def EmptySummaryPDAComplete (M : PDA input stack state) : Prop :=
  PDA.EmptySummaryComplete M

def EmptySummaryPDACompleteUpTo (M : PDA input stack state)
    (bound : Nat) : Prop :=
  PDA.EmptySummaryCompleteUpTo M bound

def EmptySummaryPDACompleteForComputes
    (M : PDA input stack state) : Prop :=
  PDA.EmptySummaryCompleteForComputes M

def StackThenEmptySummaryPDAComplete
    (M : PDA input stack state) : Prop :=
  PDA.StackThenEmptySummaryComplete M

def StackThenEmptySummaryPDACompleteForComputes
    (M : PDA input stack state) : Prop :=
  PDA.StackThenEmptySummaryCompleteForComputes M

def TopPopEmptySummaryPDAComplete (M : PDA input stack state) : Prop :=
  PDA.TopPopEmptySummaryComplete M

def TopPopStackThenEmptySummaryPDAComplete
    (M : PDA input stack state) : Prop :=
  PDA.TopPopStackThenEmptySummaryComplete M

/-!
These bridge lemmas translate the summary predicates back into ordinary PDA
computations. They are mostly "unfolding with good names": the summaries make
the induction readable, while these theorems recover the concrete configuration
statements needed by the conversion proof.
-/

theorem pda_stack_summary_trace_is_bounded_computation
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryPDAComputesIn M n p stackWord sourceInput q targetInput)
    (tail : Word stack) :
    PDA.ComputesIn M n
      { state := p, unread := sourceInput,
        stack := Word.Concat stackWord tail }
      { state := q, unread := targetInput, stack := tail } :=
  PDA.stackSummaryComputesIn_computesIn h tail

theorem pda_stack_summary_trace_is_computation
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryPDAComputesIn M n p stackWord sourceInput q targetInput)
    (tail : Word stack) :
    PDA.Computes M
      { state := p, unread := sourceInput,
        stack := Word.Concat stackWord tail }
      { state := q, unread := targetInput, stack := tail } :=
  PDA.stackSummaryComputesIn_computes h tail

theorem pda_stack_summary_trace_is_computation_unindexed
    {M : PDA input stack state}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryPDAComputes M p stackWord sourceInput q targetInput)
    (tail : Word stack) :
    PDA.Computes M
      { state := p, unread := sourceInput,
        stack := Word.Concat stackWord tail }
      { state := q, unread := targetInput, stack := tail } :=
  PDA.stackSummaryComputes_computes h tail

theorem pda_empty_summary_trace_is_bounded_computation
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputesIn M n p sourceInput q targetInput) :
    PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  PDA.emptySummaryComputesIn_computesIn h

theorem pda_empty_summary_trace_is_bounded_computation_with_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputesIn M n p sourceInput q targetInput)
    (tail : Word stack) :
    PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := tail }
      { state := q, unread := targetInput, stack := tail } :=
  PDA.emptySummaryComputesIn_computesIn_tail h tail

theorem pda_empty_summary_trace_is_computation
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputesIn M n p sourceInput q targetInput) :
    PDA.Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  PDA.emptySummaryComputesIn_computes h

theorem pda_empty_summary_trace_is_computation_with_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputesIn M n p sourceInput q targetInput)
    (tail : Word stack) :
    PDA.Computes M
      { state := p, unread := sourceInput, stack := tail }
      { state := q, unread := targetInput, stack := tail } :=
  PDA.emptySummaryComputesIn_computes_tail h tail

theorem pda_empty_summary_trace_is_computation_unindexed
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputes M p sourceInput q targetInput) :
    PDA.Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  PDA.emptySummaryComputes_computes h

theorem pda_empty_summary_trace_is_computation_unindexed_with_tail
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputes M p sourceInput q targetInput)
    (tail : Word stack) :
    PDA.Computes M
      { state := p, unread := sourceInput, stack := tail }
      { state := q, unread := targetInput, stack := tail } :=
  PDA.emptySummaryComputes_computes_tail h tail

theorem pda_stack_then_empty_summary_trace_is_bounded_computation_with_tail
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryPDAComputesIn M n p stackWord
      sourceInput q targetInput)
    (tail : Word stack) :
    PDA.ComputesIn M n
      { state := p, unread := sourceInput,
        stack := Word.Concat stackWord tail }
      { state := q, unread := targetInput, stack := tail } :=
  PDA.stackThenEmptySummaryComputesIn_computesIn_tail h tail

theorem pda_stack_then_empty_summary_trace_is_computation_with_tail
    {M : PDA input stack state}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryPDAComputes M p stackWord
      sourceInput q targetInput)
    (tail : Word stack) :
    PDA.Computes M
      { state := p, unread := sourceInput,
        stack := Word.Concat stackWord tail }
      { state := q, unread := targetInput, stack := tail } :=
  PDA.stackThenEmptySummaryComputes_computes_tail h tail

theorem pda_stack_summary_trace_unindexed_of_indexed
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryPDAComputesIn M n p stackWord sourceInput q targetInput) :
    StackSummaryPDAComputes M p stackWord sourceInput q targetInput :=
  PDA.stackSummaryComputes_of_stackSummaryComputesIn h

theorem pda_empty_summary_trace_unindexed_of_indexed
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputesIn M n p sourceInput q targetInput) :
    EmptySummaryPDAComputes M p sourceInput q targetInput :=
  PDA.emptySummaryComputes_of_emptySummaryComputesIn h

theorem pda_stack_then_empty_summary_trace_of_stack_and_empty
    {M : PDA input stack state}
    {m n : Nat} {p r q : state} {stackWord : Word stack}
    {sourceInput midInput targetInput : Word input}
    (hstack : StackSummaryPDAComputesIn M m p stackWord sourceInput
      r midInput)
    (hempty : EmptySummaryPDAComputesIn M n r midInput q targetInput) :
    StackThenEmptySummaryPDAComputesIn M (m + n) p stackWord
      sourceInput q targetInput :=
  PDA.stackThenEmptySummaryComputesIn_of_stack_and_empty hstack hempty

theorem pda_stack_then_empty_summary_trace_of_empty
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hempty : EmptySummaryPDAComputesIn M n p sourceInput q targetInput) :
    StackThenEmptySummaryPDAComputesIn M n p ([] : Word stack)
      sourceInput q targetInput :=
  PDA.stackThenEmptySummaryComputesIn_of_empty hempty

theorem pda_empty_summary_trace_of_stack_then_empty_empty_stack
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : StackThenEmptySummaryPDAComputesIn M n p ([] : Word stack)
      sourceInput q targetInput) :
    EmptySummaryPDAComputesIn M n p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_stackThenEmptySummaryComputesIn_nil h

theorem pda_stack_then_empty_summary_trace_of_computes_in_top_pop
    {M : PDA input stack state}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (hnorm : PDA.PopsAtMostOne M)
    (hcomp : PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := stackWord }
      { state := q, unread := targetInput, stack := [] }) :
    StackThenEmptySummaryPDAComputesIn M n p stackWord sourceInput
      q targetInput :=
  PDA.stackThenEmptySummaryComputesIn_of_computesIn_topPop
    hnorm hcomp

theorem pda_empty_summary_trace_of_empty_stack_trace
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackPDAComputesIn M n p sourceInput q targetInput) :
    EmptySummaryPDAComputesIn M n p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_emptyStackComputesIn h

theorem pda_empty_summary_trace_of_step_empty_stack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hstep : PDA.Step M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryPDAComputesIn M 1 p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_step_emptyStack hstep

theorem pda_empty_summary_trace_of_computes_in_zero_empty_stack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : PDA.ComputesIn M 0
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryPDAComputesIn M 0 p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_computesIn_zero_emptyStack hcomp

theorem pda_empty_summary_trace_of_computes_in_one_empty_stack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : PDA.ComputesIn M 1
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryPDAComputesIn M 1 p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_computesIn_one_emptyStack hcomp

theorem pda_stack_summary_trace_of_step_top_pop
    {M : PDA input stack state}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PDA.PopsAtMostOne M)
    (hstep : PDA.Step M
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    StackSummaryPDAComputesIn M 1 p [A] sourceInput q targetInput :=
  PDA.stackSummaryComputesIn_of_step_topPop hnorm hstep

theorem pda_stack_summary_trace_of_computes_in_one_top_pop
    {M : PDA input stack state}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PDA.PopsAtMostOne M)
    (hcomp : PDA.ComputesIn M 1
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    StackSummaryPDAComputesIn M 1 p [A] sourceInput q targetInput :=
  PDA.stackSummaryComputesIn_of_computesIn_one_topPop hnorm hcomp

theorem pda_empty_summary_trace_of_computes_in_two_empty_stack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PDA.PopsAtMostOne M)
    (hcomp : PDA.ComputesIn M 2
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryPDAComputesIn M 2 p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_computesIn_two_emptyStack hnorm hcomp

theorem pda_empty_summary_trace_of_computes_in_at_most_two_empty_stack
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PDA.PopsAtMostOne M)
    (hn : n <= 2)
    (hcomp : PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryPDAComputesIn M n p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_computesIn_atMostTwo_emptyStack
    hnorm hn hcomp

/-!
This is the point where summaries turn into grammar derivations. Stack summaries
produce {lit}`ToCFGChainDerives`; empty summaries produce derivations from
{lit}`empty p q`; and stack-then-empty summaries handle transitions that push a
stack string before eventually emptying it.
-/

theorem pda_to_cfg_chain_derives_of_stack_summary_trace
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryPDAComputesIn M n p stackWord sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        PDA.ToCFGChainDerives M presentation p stackWord q consumed :=
  PDA.toCFGChainDerives_of_stackSummaryComputesIn h

theorem pda_to_cfg_chain_derives_of_stack_summary_trace_unindexed
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {stackWord : Word stack}
    {sourceInput targetInput : Word input}
    (h : StackSummaryPDAComputes M p stackWord sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        PDA.ToCFGChainDerives M presentation p stackWord q consumed :=
  PDA.toCFGChainDerives_of_stackSummaryComputes h

theorem pda_to_cfg_empty_derives_of_empty_summary_trace
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputesIn M n p sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_emptySummaryComputesIn h

theorem pda_to_cfg_empty_derives_of_empty_summary_trace_unindexed
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputes M p sourceInput q targetInput) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_emptySummaryComputes h

theorem pda_to_cfg_empty_derives_of_read_stack_then_empty_summary
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {p r q : state} {a : input}
    {push : Word stack}
    {midInput targetInput : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hrest : StackThenEmptySummaryPDAComputesIn M n r push midInput
      q targetInput) :
    exists consumed : Word input,
      a :: midInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_read_stackThenEmptySummary
    htransition hrest

theorem pda_to_cfg_empty_derives_of_epsilon_stack_then_empty_summary
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {p r q : state}
    {push : Word stack}
    {midInput targetInput : Word input}
    (htransition : M.transition p none [] r push)
    (hrest : StackThenEmptySummaryPDAComputesIn M n r push midInput
      q targetInput) :
    exists consumed : Word input,
      midInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_epsilon_stackThenEmptySummary
    htransition hrest

theorem pda_to_cfg_empty_derives_of_computes_in_at_most_two_via_summary
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PDA.PopsAtMostOne M)
    (hn : n <= 2)
    (hcomp : PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (PDAToCFG M presentation)
          [Symbol.nonterminal (PDA.ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) :=
  PDA.toCFG_emptyDerives_of_computesIn_atMostTwo_emptyStack_viaSummary
    hnorm hn hcomp

theorem pda_to_cfg_generates_of_empty_summary_accepts_in
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptySummaryPDAComputesIn M n M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_emptySummaryAcceptsIn haccept hcomp

theorem pda_to_cfg_generates_of_empty_summary_accepts
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptySummaryPDAComputes M M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_emptySummaryAccepts haccept hcomp

/-!
The completeness predicates say that the summary descriptions cover all PDA
computations of the relevant kind. Top-pop normal form gives this completeness,
which is why the conversion normalizes a PDA before applying the final
PDA-to-CFG exactness theorem.
-/

theorem pda_empty_summary_complete_for_computes_of_empty_summary_complete
    {M : PDA input stack state}
    (hcomplete : EmptySummaryPDAComplete M) :
    EmptySummaryPDACompleteForComputes M :=
  PDA.emptySummaryCompleteForComputes_of_emptySummaryComplete hcomplete

theorem pda_empty_summary_complete_of_stack_then_empty_summary_complete
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryPDAComplete M) :
    EmptySummaryPDAComplete M :=
  PDA.emptySummaryComplete_of_stackThenEmptySummaryComplete hcomplete

theorem pda_empty_summary_trace_of_step_empty_stack_and_stack_then_empty_complete
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    {mid : PDA.Configuration input stack state}
    (hcomplete : StackThenEmptySummaryPDAComplete M)
    (hstep : PDA.Step M
      { state := p, unread := sourceInput, stack := [] } mid)
    (hrest : PDA.ComputesIn M n mid
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryPDAComputesIn M (n + 1) p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_step_emptyStack_of_stackThenEmptySummaryComplete
    hcomplete hstep hrest

theorem pda_empty_summary_complete_of_stack_then_empty_summary_complete_by_first_step
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryPDAComplete M) :
    EmptySummaryPDAComplete M :=
  PDA.emptySummaryComplete_of_stackThenEmptySummaryComplete_by_first_step
    hcomplete

theorem pda_stack_then_empty_summary_complete_for_computes_of_complete
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryPDAComplete M) :
    StackThenEmptySummaryPDACompleteForComputes M :=
  PDA.stackThenEmptySummaryCompleteForComputes_of_complete hcomplete

theorem pda_empty_summary_complete_for_computes_of_stack_then_empty_summary_complete_for_computes
    {M : PDA input stack state}
    (hcomplete : StackThenEmptySummaryPDACompleteForComputes M) :
    EmptySummaryPDACompleteForComputes M :=
  PDA.emptySummaryCompleteForComputes_of_stackThenEmptySummaryCompleteForComputes
    hcomplete

theorem pda_stack_then_empty_summary_complete_of_top_pop
    {M : PDA input stack state}
    (hnorm : PDA.PopsAtMostOne M) :
    StackThenEmptySummaryPDAComplete M :=
  PDA.stackThenEmptySummaryComplete_of_topPop hnorm

theorem pda_top_pop_stack_then_empty_summary_complete
    (M : PDA input stack state) :
    TopPopStackThenEmptySummaryPDAComplete M :=
  PDA.topPopStackThenEmptySummaryComplete M

theorem pda_empty_summary_complete_of_top_pop
    {M : PDA input stack state}
    (hnorm : PDA.PopsAtMostOne M) :
    EmptySummaryPDAComplete M :=
  PDA.emptySummaryComplete_of_topPop hnorm

theorem pda_top_pop_empty_summary_complete
    (M : PDA input stack state) :
    TopPopEmptySummaryPDAComplete M :=
  PDA.topPopEmptySummaryComplete M

theorem pda_empty_summary_complete_up_to_two_of_top_pop
    {M : PDA input stack state}
    (hnorm : PDA.PopsAtMostOne M) :
    EmptySummaryPDACompleteUpTo M 2 :=
  PDA.emptySummaryCompleteUpTo_two_of_topPop hnorm

/-!
The final conversion theorems assemble the pieces:

1. completeness of summaries gives grammar generation for accepting runs;
2. generated words are already known to be accepted by the PDA;
3. therefore the generated language of the constructed CFG equals the accepted
   language of the PDA.
-/

theorem pda_to_cfg_generates_of_accepts_in_of_empty_summary_complete
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (hcomplete : EmptySummaryPDAComplete M)
    (haccept : M.accept qf)
    (hcomp : PDA.ComputesIn M n (PDA.initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_acceptsIn_of_emptySummaryComplete
    hcomplete haccept hcomp

theorem pda_to_cfg_generates_of_accepts_in_of_empty_summary_complete_up_to
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {bound n : Nat} {w : Word input} {qf : state}
    (hcomplete : EmptySummaryPDACompleteUpTo M bound)
    (hn : n <= bound)
    (haccept : M.accept qf)
    (hcomp : PDA.ComputesIn M n (PDA.initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_acceptsIn_of_emptySummaryCompleteUpTo
    hcomplete hn haccept hcomp

theorem pda_to_cfg_generates_of_accepts_of_empty_summary_complete
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input}
    (hcomplete : EmptySummaryPDAComplete M)
    (haccepts : PDA.Accepts M w) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_accepts_of_emptySummaryComplete
    hcomplete haccepts

theorem pda_to_cfg_generates_of_accepts_of_empty_summary_complete_for_computes
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input}
    (hcomplete : EmptySummaryPDACompleteForComputes M)
    (haccepts : PDA.Accepts M w) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_accepts_of_emptySummaryCompleteForComputes
    hcomplete haccepts

theorem pda_to_cfg_language_exact_of_empty_summary_complete
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hcomplete : EmptySummaryPDAComplete M) :
    Language.Equal (CFG.GeneratedLanguage (PDAToCFG M presentation))
      (PDA.AcceptedLanguage M) :=
  PDA.toCFG_language_exact_of_emptySummaryComplete hcomplete

theorem pda_to_cfg_language_exact_of_empty_summary_complete_for_computes
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hcomplete : EmptySummaryPDACompleteForComputes M) :
    Language.Equal (CFG.GeneratedLanguage (PDAToCFG M presentation))
      (PDA.AcceptedLanguage M) :=
  PDA.toCFG_language_exact_of_emptySummaryCompleteForComputes hcomplete

theorem pda_to_cfg_language_exact_of_stack_then_empty_summary_complete
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hcomplete : StackThenEmptySummaryPDAComplete M) :
    Language.Equal (CFG.GeneratedLanguage (PDAToCFG M presentation))
      (PDA.AcceptedLanguage M) :=
  PDA.toCFG_language_exact_of_stackThenEmptySummaryComplete hcomplete

theorem pda_to_cfg_language_exact_of_stack_then_empty_summary_complete_for_computes
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hcomplete : StackThenEmptySummaryPDACompleteForComputes M) :
    Language.Equal (CFG.GeneratedLanguage (PDAToCFG M presentation))
      (PDA.AcceptedLanguage M) :=
  PDA.toCFG_language_exact_of_stackThenEmptySummaryCompleteForComputes
    hcomplete

theorem pda_to_cfg_language_exact_of_top_pop
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hnorm : PDA.PopsAtMostOne M) :
    Language.Equal (CFG.GeneratedLanguage (PDAToCFG M presentation))
      (PDA.AcceptedLanguage M) :=
  PDA.toCFG_language_exact_of_topPop hnorm

/-!
For an arbitrary finitely presented PDA, the public theorem uses the normalized
machine. The normalized CFG has the same language as the original PDA because
pop normalization was proved language-exact above.
-/

theorem pda_to_cfg_normalized_language_exact
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    Language.Equal
      (CFG.GeneratedLanguage (PDAToCFGNormalized M presentation))
      (PDA.AcceptedLanguage (PDAPopNormalize M presentation)) :=
  PDA.toCFGNormalized_language_exact M presentation

theorem pda_to_cfg_normalized_generates_of_accepts
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input}
    (h : w ∈ PDA.AcceptedLanguage M) :
    w ∈ CFG.GeneratedLanguage (PDAToCFGNormalized M presentation) :=
  PDA.toCFGNormalized_generates_of_accepts h

theorem pda_accepted_language_subset_to_cfg_normalized
    {M : PDA input stack state}
    (presentation : PDA.FinitePresentation M) :
    Language.Subset (PDA.AcceptedLanguage M)
      (CFG.GeneratedLanguage (PDAToCFGNormalized M presentation)) :=
  PDA.acceptedLanguage_subset_toCFGNormalized presentation

theorem pda_to_cfg_normalized_language_exact_of_pop_normalize_language_exact
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hexact : PDAPopNormalizeLanguageExact M presentation) :
    Language.Equal
      (CFG.GeneratedLanguage (PDAToCFGNormalized M presentation))
      (PDA.AcceptedLanguage M) :=
  PDA.toCFGNormalized_language_exact_of_popNormalizeLanguageExact hexact

theorem pda_to_cfg_normalized_language_exact_original
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    Language.Equal
      (CFG.GeneratedLanguage (PDAToCFGNormalized M presentation))
      (PDA.AcceptedLanguage M) :=
  PDA.toCFGNormalized_language_exact_original M presentation

theorem pda_to_cfg_top_pop_exact_of_empty_summary_complete
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hcomplete : TopPopEmptySummaryPDAComplete M) :
    PDAToCFGExact M presentation :=
  PDA.toCFG_topPopExact_of_emptySummaryComplete hcomplete

theorem pda_to_cfg_top_pop_exact_of_stack_then_empty_summary_complete
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hcomplete : TopPopStackThenEmptySummaryPDAComplete M) :
    PDAToCFGExact M presentation :=
  PDA.toCFG_topPopExact_of_stackThenEmptySummaryComplete hcomplete

theorem pda_to_cfg_top_pop_exact
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    PDAToCFGExact M presentation :=
  PDA.toCFG_topPopExact M presentation

/-!
These are the book-level consequences: every finitely presented PDA recognizes
a context-free language. The strongest final theorem first normalizes the PDA,
then applies the top-pop conversion.
-/

theorem finite_presentation_pda_context_free_of_empty_summary_complete
    {input stack state : Type}
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hcomplete : EmptySummaryPDAComplete M) :
    CFL.ContextFreeLanguage (PDA.AcceptedLanguage M) := by
  exists PDA.ToCFGNonterminal stack state
  exists PDAToCFG M presentation
  constructor
  · exact pda_to_cfg_hasFiniteProductions M presentation
  · exact pda_to_cfg_language_exact_of_empty_summary_complete
      (M := M) (presentation := presentation) hcomplete

theorem finite_presentation_top_pop_pda_context_free
    {input stack state : Type}
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hnorm : PDA.PopsAtMostOne M) :
    CFL.ContextFreeLanguage (PDA.AcceptedLanguage M) := by
  exists PDA.ToCFGNonterminal stack state
  exists PDAToCFG M presentation
  constructor
  · exact pda_to_cfg_hasFiniteProductions M presentation
  · exact pda_to_cfg_language_exact_of_top_pop
      (M := M) (presentation := presentation) hnorm

theorem finite_presentation_pda_context_free_of_pop_normalize_language_exact
    {input stack state : Type}
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    (hexact : PDAPopNormalizeLanguageExact M presentation) :
    CFL.ContextFreeLanguage (PDA.AcceptedLanguage M) := by
  exists PDA.ToCFGNonterminal stack
    (PDA.PopNormalizedState (M := M) presentation)
  exists PDAToCFGNormalized M presentation
  constructor
  · exact pda_to_cfg_normalized_hasFiniteProductions M presentation
  · exact
      pda_to_cfg_normalized_language_exact_of_pop_normalize_language_exact
        (M := M) (presentation := presentation) hexact

theorem finite_presentation_pda_context_free
    {input stack state : Type}
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M} :
    CFL.ContextFreeLanguage (PDA.AcceptedLanguage M) :=
  finite_presentation_pda_context_free_of_pop_normalize_language_exact
    (M := M) (presentation := presentation)
    (pda_pop_normalize_language_exact M presentation)

/-!
# Concrete PDA Examples

The remainder of the page proves exact languages for concrete machines. Each
example defines a small finite state type, a transition relation, and then two
directions of correctness: accepted computations have the intended word shape,
and every word of the intended shape has an accepting computation.
-/

/-!
# The {lit}`a^n b^n` PDA

This standard PDA pushes one marker for each `a`, then pops one marker for
each `b`. Acceptance requires the input and stack to be empty, so the counts
must match.
-/

inductive AnBnPDAStack where
  | marker
deriving DecidableEq

inductive AnBnPDAState where
  | push
  | pop
  | accept
deriving DecidableEq

namespace AnBnPDAState

def finite : Foundation.FiniteType AnBnPDAState where
  elems := [push, pop, accept]
  complete := by
    intro q
    cases q <;> simp

end AnBnPDAState

inductive AnBnPDATransition :
    AnBnPDAState -> Option Section01.AB -> Word AnBnPDAStack ->
      AnBnPDAState -> Word AnBnPDAStack -> Prop where
  | pushA :
      AnBnPDATransition AnBnPDAState.push (some Section01.AB.a) []
        AnBnPDAState.push [AnBnPDAStack.marker]
  | startPop :
      AnBnPDATransition AnBnPDAState.push none []
        AnBnPDAState.pop []
  | popB :
      AnBnPDATransition AnBnPDAState.pop (some Section01.AB.b)
        [AnBnPDAStack.marker] AnBnPDAState.pop []
  | finish :
      AnBnPDATransition AnBnPDAState.pop none []
        AnBnPDAState.accept []

def AnBnPDA : PDA Section01.AB AnBnPDAStack AnBnPDAState where
  start := AnBnPDAState.push
  transition := AnBnPDATransition
  accept := fun q => q = AnBnPDAState.accept
  statesFinite := AnBnPDAState.finite

def AnBnPDAStackWord (n : Nat) : Word AnBnPDAStack :=
  Word.RepeatSymbol AnBnPDAStack.marker n

theorem anbnPDAStackWord_succ (n : Nat) :
    AnBnPDAStack.marker :: AnBnPDAStackWord n =
      AnBnPDAStackWord (n + 1) :=
  rfl

/-!
The acceptance direction is constructive. The lemmas below show how to run the
machine: push one marker for each {lit}`a`, switch to popping, pop one marker
for each {lit}`b`, and finally accept when both the input and stack are empty.
-/

theorem anbnPDA_push_as (n : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes AnBnPDA
      { state := AnBnPDAState.push,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
        stack := stack }
      { state := AnBnPDAState.push,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord n) stack } := by
  induction n generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      have hstep : PDA.Step AnBnPDA
          { state := AnBnPDAState.push,
            unread := Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := stack }
          { state := AnBnPDAState.push,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := AnBnPDAStack.marker :: stack } := by
        exact PDA.Step.read (M := AnBnPDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest)
          (restStack := stack) AnBnPDATransition.pushA
      have hrest := ih (AnBnPDAStack.marker :: stack)
      have htarget :
          Word.Concat (AnBnPDAStackWord n)
              (AnBnPDAStack.marker :: stack) =
            Word.Concat (AnBnPDAStackWord (n + 1)) stack := by
        simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol,
          Section01.replicate_succ_eq_append AnBnPDAStack.marker n,
          List.append_assoc]
      exact PDA.Computes.step hstep (by
        simpa [htarget] using hrest)

theorem anbnPDA_switch_to_pop (unread : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Step AnBnPDA
      { state := AnBnPDAState.push, unread := unread, stack := stack }
      { state := AnBnPDAState.pop, unread := unread, stack := stack } := by
  simpa [Word.Concat] using
    (PDA.Step.epsilon (M := AnBnPDA) (unread := unread)
      (restStack := stack) AnBnPDATransition.startPop)

theorem anbnPDA_pop_bs (n : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes AnBnPDA
      { state := AnBnPDAState.pop,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
        stack := Word.Concat (AnBnPDAStackWord n) stack }
      { state := AnBnPDAState.pop, unread := rest, stack := stack } := by
  induction n generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      have hstep : PDA.Step AnBnPDA
          { state := AnBnPDAState.pop,
            unread := Section01.AB.b ::
              Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
            stack := AnBnPDAStack.marker ::
              Word.Concat (AnBnPDAStackWord n) stack }
          { state := AnBnPDAState.pop,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
            stack := Word.Concat (AnBnPDAStackWord n) stack } := by
        exact PDA.Step.read (M := AnBnPDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest)
          (restStack := Word.Concat (AnBnPDAStackWord n) stack)
          AnBnPDATransition.popB
      exact PDA.Computes.step hstep (ih stack)

theorem anbnPDA_finish :
    PDA.Step AnBnPDA
      { state := AnBnPDAState.pop, unread := [], stack := [] }
      { state := AnBnPDAState.accept, unread := [], stack := [] } := by
  simpa [Word.Concat] using
    (PDA.Step.epsilon (M := AnBnPDA)
      (unread := ([] : Word Section01.AB))
      (restStack := ([] : Word AnBnPDAStack))
      AnBnPDATransition.finish)

theorem anbnPDA_accepts_anbn_words (n : Nat) :
    PDA.Accepts AnBnPDA (Section01.AnBnWord n) := by
  exists AnBnPDAState.accept
  constructor
  · rfl
  · unfold Section01.AnBnWord PDA.initial
    have hpush :=
      anbnPDA_push_as n (Word.RepeatSymbol Section01.AB.b n)
        ([] : Word AnBnPDAStack)
    have hswitch : PDA.Computes AnBnPDA
        { state := AnBnPDAState.push,
          unread := Word.RepeatSymbol Section01.AB.b n,
          stack := Word.Concat (AnBnPDAStackWord n) [] }
        { state := AnBnPDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b n,
          stack := Word.Concat (AnBnPDAStackWord n) [] } := by
      simpa [Word.Concat] using PDA.computes_of_step
        (anbnPDA_switch_to_pop (Word.RepeatSymbol Section01.AB.b n)
          (AnBnPDAStackWord n))
    have hpop : PDA.Computes AnBnPDA
        { state := AnBnPDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b n,
          stack := Word.Concat (AnBnPDAStackWord n) [] }
        { state := AnBnPDAState.pop, unread := [], stack := [] } := by
      simpa [Word.Concat] using anbnPDA_pop_bs n [] []
    have hfinish := PDA.computes_of_step anbnPDA_finish
    exact PDA.computes_trans hpush
      (PDA.computes_trans hswitch
        (PDA.computes_trans hpop hfinish))

/-!
The converse direction is a shape argument. Starting in the push state, any
accepting computation must read some number of {lit}`a`s, switch once, and then
read exactly as many {lit}`b`s as there are stack markers.
-/

theorem anbnPDA_accept_state_no_steps
    {w : Word Section01.AB} {stack : Word AnBnPDAStack}
    {c : PDA.Configuration Section01.AB AnBnPDAStack AnBnPDAState} :
    ¬ PDA.Step AnBnPDA
      { state := AnBnPDAState.accept, unread := w, stack := stack } c := by
  intro h
  cases h with
  | read htrans =>
      cases htrans
  | epsilon htrans =>
      cases htrans

theorem anbnPDA_accept_computes_final_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack AnBnPDAState}
    (h : PDA.Computes AnBnPDA c d)
    (hstate : c.state = AnBnPDAState.accept)
    (hfinal :
      d = { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    c.unread = [] ∧ c.stack = [] := by
  induction h with
  | refl c =>
      rw [hfinal]
      exact And.intro rfl rfl
  | step hstep _ _ =>
      cases hstep with
      | read htrans =>
          cases hstate
          cases htrans
      | epsilon htrans =>
          cases hstate
          cases htrans

theorem anbnPDA_accept_computes_final
    {w : Word Section01.AB} {stack : Word AnBnPDAStack}
    (h : PDA.Computes AnBnPDA
      { state := AnBnPDAState.accept, unread := w, stack := stack }
      { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    w = [] ∧ stack = [] :=
  anbnPDA_accept_computes_final_config h rfl rfl

theorem anbnPDA_pop_accepts_only_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack AnBnPDAState}
    (h : PDA.Computes AnBnPDA c d)
    (hstate : c.state = AnBnPDAState.pop)
    (hfinal :
      d = { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    c.unread = Word.RepeatSymbol Section01.AB.b (Word.Length c.stack) := by
  induction h with
  | refl c =>
      rw [hfinal] at hstate
      cases hstate
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases hstate
          cases htrans
          have htail := ih rfl hfinal
          simp [Word.Length, Word.RepeatSymbol, Word.Concat] at htail ⊢
          rw [htail]
          rw [Section01.replicate_succ_eq_cons Section01.AB.b]
      | epsilon htrans =>
          cases hstate
          cases htrans
          have hfinalSource :=
            anbnPDA_accept_computes_final_config hrest rfl hfinal
          rw [hfinalSource.left, hfinalSource.right]
          rfl

theorem anbnPDA_pop_accepts_only
    {w : Word Section01.AB} {stack : Word AnBnPDAStack}
    (h : PDA.Computes AnBnPDA
      { state := AnBnPDAState.pop, unread := w, stack := stack }
      { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    w = Word.RepeatSymbol Section01.AB.b (Word.Length stack) :=
  anbnPDA_pop_accepts_only_config h rfl rfl

theorem anbnPDA_push_accepts_only_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack AnBnPDAState}
    (h : PDA.Computes AnBnPDA c d)
    (hstate : c.state = AnBnPDAState.push)
    (hfinal :
      d = { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    exists n,
      c.unread =
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (Word.Length c.stack + n)) := by
  induction h with
  | refl c =>
      rw [hfinal] at hstate
      cases hstate
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases hstate
          cases htrans
          cases ih rfl hfinal with
          | intro n hn =>
              exists n + 1
              simp [Word.Concat, Word.RepeatSymbol, Word.Length] at hn ⊢
              rw [hn]
              simp [Section01.replicate_succ_eq_cons, Nat.add_comm, Nat.add_left_comm]
      | epsilon htrans =>
          cases hstate
          cases htrans
          exists 0
          have hpop := anbnPDA_pop_accepts_only_config hrest rfl hfinal
          simpa [Word.Concat, Word.RepeatSymbol, Word.Length] using hpop

theorem anbnPDA_push_accepts_only
    {w : Word Section01.AB} {stack : Word AnBnPDAStack}
    (h : PDA.Computes AnBnPDA
      { state := AnBnPDAState.push, unread := w, stack := stack }
      { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    exists n,
      w =
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (Word.Length stack + n)) :=
  anbnPDA_push_accepts_only_config h rfl rfl

theorem anbnPDA_accepts_only_anbn_words {w : Word Section01.AB}
    (h : PDA.Accepts AnBnPDA w) :
    exists n, w = Section01.AnBnWord n := by
  cases h with
  | intro q hq =>
      cases hq.left
      have hshape := anbnPDA_push_accepts_only hq.right
      cases hshape with
      | intro n hn =>
          exists n
          simpa [Section01.AnBnWord, Word.Length, Word.Concat,
            Word.RepeatSymbol] using hn

theorem anbnPDA_accepted_language_exact (w : Word Section01.AB) :
    w ∈ PDA.AcceptedLanguage AnBnPDA <->
      exists n, w = Section01.AnBnWord n := by
  constructor
  · exact anbnPDA_accepts_only_anbn_words
  · intro h
    cases h with
    | intro n hn =>
        rw [hn]
        exact anbnPDA_accepts_anbn_words n

/-!
# The Range {lit}`n <= m <= 2n`

The next PDA recognizes block words `a^n b^m` where each `a` contributes one
or two stack markers. Popping one marker per `b` allows exactly the range
between `n` and `2n`.
-/

inductive Range12PDAState where
  | push
  | pop
deriving DecidableEq

namespace Range12PDAState

def finite : Foundation.FiniteType Range12PDAState where
  elems := [push, pop]
  complete := by
    intro q
    cases q <;> simp

end Range12PDAState

inductive Range12PDATransition :
    Range12PDAState -> Option Section01.AB -> Word AnBnPDAStack ->
      Range12PDAState -> Word AnBnPDAStack -> Prop where
  | pushOne :
      Range12PDATransition Range12PDAState.push (some Section01.AB.a) []
        Range12PDAState.push [AnBnPDAStack.marker]
  | pushTwo :
      Range12PDATransition Range12PDAState.push (some Section01.AB.a) []
        Range12PDAState.push [AnBnPDAStack.marker, AnBnPDAStack.marker]
  | startPop :
      Range12PDATransition Range12PDAState.push none []
        Range12PDAState.pop []
  | popB :
      Range12PDATransition Range12PDAState.pop (some Section01.AB.b)
        [AnBnPDAStack.marker] Range12PDAState.pop []

def Range12PDA : PDA Section01.AB AnBnPDAStack Range12PDAState where
  start := Range12PDAState.push
  transition := Range12PDATransition
  accept := fun q => q = Range12PDAState.pop
  statesFinite := Range12PDAState.finite

def AnBmWord (n m : Nat) : Word Section01.AB :=
  Word.Concat (Word.RepeatSymbol Section01.AB.a n)
    (Word.RepeatSymbol Section01.AB.b m)

def Range12Language : Language Section01.AB :=
  fun w => exists n m, n <= m ∧ m <= 2 * n ∧ w = AnBmWord n m

/-!
For the forward direction, choose nondeterministically whether each {lit}`a`
pushes one or two markers. The variable {lit}`extra` counts how many of the
{lit}`a`s used the two-marker transition, so the stack has {lit}`n + extra`
markers before the {lit}`b` phase.
-/

theorem range12PDA_push_as_with_extra (n extra : Nat) (hextra : extra <= n)
    (rest : Word Section01.AB) (stack : Word AnBnPDAStack) :
    PDA.Computes Range12PDA
      { state := Range12PDAState.push,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
        stack := stack }
      { state := Range12PDAState.push,
        unread := rest,
        stack :=
          Word.Concat (AnBnPDAStackWord (n + extra)) stack } := by
  induction n generalizing extra stack with
  | zero =>
      have hextraZero : extra = 0 := by omega
      subst extra
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      cases extra with
      | zero =>
          have hstep : PDA.Step Range12PDA
              { state := Range12PDAState.push,
                unread := Section01.AB.a ::
                  Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
                stack := stack }
              { state := Range12PDAState.push,
                unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
                stack := AnBnPDAStack.marker :: stack } := by
            exact PDA.Step.read (M := Range12PDA)
              (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest)
              (restStack := stack) Range12PDATransition.pushOne
          have hrest := ih 0 (by omega) (AnBnPDAStack.marker :: stack)
          have htarget :
              Word.Concat (AnBnPDAStackWord n)
                  (AnBnPDAStack.marker :: stack) =
                Word.Concat (AnBnPDAStackWord (n + 1)) stack := by
            simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol,
              Section01.replicate_succ_eq_append AnBnPDAStack.marker n,
              List.append_assoc]
          exact PDA.Computes.step hstep (by
            simpa [htarget] using hrest)
      | succ extra =>
          have hstep : PDA.Step Range12PDA
              { state := Range12PDAState.push,
                unread := Section01.AB.a ::
                  Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
                stack := stack }
              { state := Range12PDAState.push,
                unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
                stack := AnBnPDAStack.marker :: AnBnPDAStack.marker :: stack } := by
            exact PDA.Step.read (M := Range12PDA)
              (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest)
              (restStack := stack) Range12PDATransition.pushTwo
          have hrest := ih extra (by omega)
            (AnBnPDAStack.marker :: AnBnPDAStack.marker :: stack)
          have htarget :
              Word.Concat (AnBnPDAStackWord (n + extra))
                  (AnBnPDAStack.marker :: AnBnPDAStack.marker :: stack) =
                Word.Concat (AnBnPDAStackWord (n + 1 + (extra + 1))) stack := by
            have hnat : n + extra + 2 = n + 1 + (extra + 1) := by omega
            simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol]
            rw [← hnat]
            rw [Section01.replicate_succ_eq_append AnBnPDAStack.marker
              (n + extra + 1)]
            rw [Section01.replicate_succ_eq_append AnBnPDAStack.marker
              (n + extra)]
            simp [List.append_assoc]
          exact PDA.Computes.step hstep (by
            simpa [htarget] using hrest)

theorem range12PDA_switch_to_pop (unread : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Step Range12PDA
      { state := Range12PDAState.push, unread := unread, stack := stack }
      { state := Range12PDAState.pop, unread := unread, stack := stack } := by
  simpa [Word.Concat] using
    (PDA.Step.epsilon (M := Range12PDA) (unread := unread)
      (restStack := stack) Range12PDATransition.startPop)

theorem range12PDA_pop_bs (m : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes Range12PDA
      { state := Range12PDAState.pop,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
        stack := Word.Concat (AnBnPDAStackWord m) stack }
      { state := Range12PDAState.pop, unread := rest, stack := stack } := by
  induction m generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ m ih =>
      have hstep : PDA.Step Range12PDA
          { state := Range12PDAState.pop,
            unread := Section01.AB.b ::
              Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
            stack := AnBnPDAStack.marker ::
              Word.Concat (AnBnPDAStackWord m) stack }
          { state := Range12PDAState.pop,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
            stack := Word.Concat (AnBnPDAStackWord m) stack } := by
        exact PDA.Step.read (M := Range12PDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest)
          (restStack := Word.Concat (AnBnPDAStackWord m) stack)
          Range12PDATransition.popB
      exact PDA.Computes.step hstep (ih stack)

theorem range12PDA_accepts_range_words {n m : Nat}
    (hLower : n <= m) (hUpper : m <= 2 * n) :
    PDA.Accepts Range12PDA (AnBmWord n m) := by
  let extra := m - n
  have hm : m = n + extra := by
    simp [extra]
    omega
  have hextra : extra <= n := by
    simp [extra]
    omega
  exists Range12PDAState.pop
  constructor
  · rfl
  · unfold PDA.initial AnBmWord
    have hpush :=
      range12PDA_push_as_with_extra n extra hextra
        (Word.RepeatSymbol Section01.AB.b m) ([] : Word AnBnPDAStack)
    have hswitch : PDA.Computes Range12PDA
        { state := Range12PDAState.push,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord (n + extra)) [] }
        { state := Range12PDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord (n + extra)) [] } := by
      exact PDA.computes_of_step
        (range12PDA_switch_to_pop (Word.RepeatSymbol Section01.AB.b m)
          (Word.Concat (AnBnPDAStackWord (n + extra)) []))
    have hpop : PDA.Computes Range12PDA
        { state := Range12PDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord (n + extra)) [] }
        { state := Range12PDAState.pop, unread := [], stack := [] } := by
      rw [hm]
      simpa [Word.Concat] using range12PDA_pop_bs (n + extra) [] []
    exact PDA.computes_trans hpush
      (PDA.computes_trans hswitch hpop)

/-!
For the reverse direction, the proof reads the computation backwards by state.
In the pop state, only {lit}`b`s can be consumed. In the push state, each
{lit}`a` accounts for either one or two future {lit}`b`s.
-/

theorem range12PDA_pop_accepts_only_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack Range12PDAState}
    (h : PDA.Computes Range12PDA c d)
    (hstate : c.state = Range12PDAState.pop)
    (hfinal :
      d = { state := Range12PDAState.pop, unread := [], stack := [] }) :
    c.unread = Word.RepeatSymbol Section01.AB.b (Word.Length c.stack) := by
  induction h with
  | refl c =>
      rw [hfinal]
      rfl
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases hstate
          cases htrans
          have htail := ih rfl hfinal
          simp [Word.Length, Word.RepeatSymbol, Word.Concat] at htail ⊢
          rw [htail]
          rw [Section01.replicate_succ_eq_cons Section01.AB.b]
      | epsilon htrans =>
          cases hstate
          cases htrans

theorem range12PDA_push_accepts_only_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack Range12PDAState}
    (h : PDA.Computes Range12PDA c d)
    (hstate : c.state = Range12PDAState.push)
    (hfinal :
      d = { state := Range12PDAState.pop, unread := [], stack := [] }) :
    exists n k,
      n <= k ∧ k <= 2 * n ∧
      c.unread =
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (Word.Length c.stack + k)) := by
  induction h with
  | refl c =>
      rw [hfinal] at hstate
      cases hstate
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases hstate
          cases htrans
          · cases ih rfl hfinal with
            | intro n hn =>
                cases hn with
                | intro k hk =>
                    exists n + 1
                    exists k + 1
                    constructor
                    · omega
                    constructor
                    · omega
                    · simp [Word.Concat, Word.RepeatSymbol, Word.Length] at hk ⊢
                      rw [hk.right.right]
                      simp [Section01.replicate_succ_eq_cons,
                        Nat.add_comm, Nat.add_left_comm]
          · cases ih rfl hfinal with
            | intro n hn =>
                cases hn with
                | intro k hk =>
                    exists n + 1
                    exists k + 2
                    constructor
                    · omega
                    constructor
                    · omega
                    · simp [Word.Concat, Word.RepeatSymbol, Word.Length] at hk ⊢
                      rw [hk.right.right]
                      simp [Section01.replicate_succ_eq_cons,
                        Nat.add_comm, Nat.add_left_comm]
      | epsilon htrans =>
          cases hstate
          cases htrans
          exists 0
          exists 0
          constructor
          · omega
          constructor
          · omega
          · have hpop := range12PDA_pop_accepts_only_config hrest rfl hfinal
            simpa [Word.Concat, Word.RepeatSymbol, Word.Length] using hpop

theorem range12PDA_accepts_only_range_words {w : Word Section01.AB}
    (h : PDA.Accepts Range12PDA w) :
    w ∈ Range12Language := by
  cases h with
  | intro q hq =>
      cases hq.left
      have hshape := range12PDA_push_accepts_only_config hq.right rfl rfl
      cases hshape with
      | intro n hn =>
          cases hn with
          | intro k hk =>
              exists n
              exists k
              constructor
              · exact hk.left
              constructor
              · exact hk.right.left
              · simpa [PDA.initial, AnBmWord, Word.Length, Word.Concat]
                  using hk.right.right

theorem range12PDA_accepted_language_exact (w : Word Section01.AB) :
    w ∈ PDA.AcceptedLanguage Range12PDA <-> w ∈ Range12Language := by
  constructor
  · exact range12PDA_accepts_only_range_words
  · intro hw
    cases hw with
    | intro n hn =>
        cases hn with
        | intro m hm =>
            rw [hm.right.right]
            exact range12PDA_accepts_range_words hm.left hm.right.left

/-!
# The Half-Range Variant

This machine recognizes the complementary block-range pattern `m <= n <= 2m`.
It nondeterministically groups some `a`s in pairs before switching to the
`b`-popping phase.
-/

inductive HalfRangePDAState where
  | ready
  | needSecond
  | pop
deriving DecidableEq

namespace HalfRangePDAState

def finite : Foundation.FiniteType HalfRangePDAState where
  elems := [ready, needSecond, pop]
  complete := by
    intro q
    cases q <;> simp

end HalfRangePDAState

inductive HalfRangePDATransition :
    HalfRangePDAState -> Option Section01.AB -> Word AnBnPDAStack ->
      HalfRangePDAState -> Word AnBnPDAStack -> Prop where
  | oneA :
      HalfRangePDATransition HalfRangePDAState.ready (some Section01.AB.a) []
        HalfRangePDAState.ready [AnBnPDAStack.marker]
  | firstOfPair :
      HalfRangePDATransition HalfRangePDAState.ready (some Section01.AB.a) []
        HalfRangePDAState.needSecond []
  | secondOfPair :
      HalfRangePDATransition HalfRangePDAState.needSecond (some Section01.AB.a) []
        HalfRangePDAState.ready [AnBnPDAStack.marker]
  | startPop :
      HalfRangePDATransition HalfRangePDAState.ready none []
        HalfRangePDAState.pop []
  | popB :
      HalfRangePDATransition HalfRangePDAState.pop (some Section01.AB.b)
        [AnBnPDAStack.marker] HalfRangePDAState.pop []

def HalfRangePDA : PDA Section01.AB AnBnPDAStack HalfRangePDAState where
  start := HalfRangePDAState.ready
  transition := HalfRangePDATransition
  accept := fun q => q = HalfRangePDAState.pop
  statesFinite := HalfRangePDAState.finite

def HalfRangeLanguage : Language Section01.AB :=
  fun w => exists n m, m <= n ∧ n <= 2 * m ∧ w = AnBmWord n m

def halfRangeExampleWord : Word Section01.AB :=
  AnBmWord 3 2

/-!
The example word demonstrates the intended behavior before the general proof:
read three {lit}`a`s, push two markers by grouping one pair and one single,
then pop those two markers while reading two {lit}`b`s.
-/

theorem halfRangePDA_accepts_three_a_two_b :
    PDA.Accepts HalfRangePDA halfRangeExampleWord := by
  exists HalfRangePDAState.pop
  constructor
  · rfl
  · unfold halfRangeExampleWord AnBmWord PDA.initial
    let c0 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.ready,
        unread := [Section01.AB.a, Section01.AB.a, Section01.AB.a,
          Section01.AB.b, Section01.AB.b],
        stack := [] }
    let c1 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.needSecond,
        unread := [Section01.AB.a, Section01.AB.a, Section01.AB.b, Section01.AB.b],
        stack := [] }
    let c2 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.ready,
        unread := [Section01.AB.a, Section01.AB.b, Section01.AB.b],
        stack := [AnBnPDAStack.marker] }
    let c3 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.ready,
        unread := [Section01.AB.b, Section01.AB.b],
        stack := [AnBnPDAStack.marker, AnBnPDAStack.marker] }
    let c4 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.pop,
        unread := [Section01.AB.b, Section01.AB.b],
        stack := [AnBnPDAStack.marker, AnBnPDAStack.marker] }
    let c5 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.pop,
        unread := [Section01.AB.b],
        stack := [AnBnPDAStack.marker] }
    let c6 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.pop,
        unread := [],
        stack := [] }
    have h01 : PDA.Step HalfRangePDA c0 c1 := by
      exact PDA.Step.read (M := HalfRangePDA)
        (unread := [Section01.AB.a, Section01.AB.a,
          Section01.AB.b, Section01.AB.b])
        (restStack := []) HalfRangePDATransition.firstOfPair
    have h12 : PDA.Step HalfRangePDA c1 c2 := by
      exact PDA.Step.read (M := HalfRangePDA)
        (unread := [Section01.AB.a, Section01.AB.b, Section01.AB.b])
        (restStack := []) HalfRangePDATransition.secondOfPair
    have h23 : PDA.Step HalfRangePDA c2 c3 := by
      exact PDA.Step.read (M := HalfRangePDA)
        (unread := [Section01.AB.b, Section01.AB.b])
        (restStack := [AnBnPDAStack.marker]) HalfRangePDATransition.oneA
    have h34 : PDA.Step HalfRangePDA c3 c4 := by
      exact PDA.Step.epsilon (M := HalfRangePDA)
        (unread := [Section01.AB.b, Section01.AB.b])
        (restStack := [AnBnPDAStack.marker, AnBnPDAStack.marker])
        HalfRangePDATransition.startPop
    have h45 : PDA.Step HalfRangePDA c4 c5 := by
      exact PDA.Step.read (M := HalfRangePDA)
        (unread := [Section01.AB.b])
        (restStack := [AnBnPDAStack.marker]) HalfRangePDATransition.popB
    have h56 : PDA.Step HalfRangePDA c5 c6 := by
      exact PDA.Step.read (M := HalfRangePDA)
        (unread := [])
        (restStack := []) HalfRangePDATransition.popB
    change PDA.Computes HalfRangePDA c0 c6
    exact PDA.Computes.step h01
      (PDA.Computes.step h12
        (PDA.Computes.step h23
          (PDA.Computes.step h34
            (PDA.Computes.step h45
      (PDA.Computes.step h56 (PDA.Computes.refl c6))))))

/-!
The general acceptance proof separates two ways of creating markers. A single
{lit}`a` may push one marker, while a pair of {lit}`a`s may also push one marker.
Combining those computations recognizes exactly the range
{lit}`m <= n <= 2 * m`.
-/

theorem halfRangePDA_push_singles (n : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.ready,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
        stack := stack }
      { state := HalfRangePDAState.ready,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord n) stack } := by
  induction n generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      have hstep : PDA.Step HalfRangePDA
          { state := HalfRangePDAState.ready,
            unread := Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := stack }
          { state := HalfRangePDAState.ready,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := AnBnPDAStack.marker :: stack } := by
        exact PDA.Step.read (M := HalfRangePDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest)
          (restStack := stack) HalfRangePDATransition.oneA
      have hrest := ih (AnBnPDAStack.marker :: stack)
      have htarget :
          Word.Concat (AnBnPDAStackWord n)
              (AnBnPDAStack.marker :: stack) =
            Word.Concat (AnBnPDAStackWord (n + 1)) stack := by
        simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol,
          Section01.replicate_succ_eq_append AnBnPDAStack.marker n,
          List.append_assoc]
      exact PDA.Computes.step hstep (by
        simpa [htarget] using hrest)

theorem halfRangePDA_push_pairs (pairs : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.ready,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
        stack := stack }
      { state := HalfRangePDAState.ready,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord pairs) stack } := by
  induction pairs generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ pairs ih =>
      have hfirst : PDA.Step HalfRangePDA
          { state := HalfRangePDAState.ready,
            unread := Section01.AB.a :: Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
            stack := stack }
          { state := HalfRangePDAState.needSecond,
            unread := Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
            stack := stack } := by
        exact PDA.Step.read (M := HalfRangePDA)
          (unread := Section01.AB.a ::
            Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest)
          (restStack := stack) HalfRangePDATransition.firstOfPair
      have hsecond : PDA.Step HalfRangePDA
          { state := HalfRangePDAState.needSecond,
            unread := Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
            stack := stack }
          { state := HalfRangePDAState.ready,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
            stack := AnBnPDAStack.marker :: stack } := by
        exact PDA.Step.read (M := HalfRangePDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest)
          (restStack := stack) HalfRangePDATransition.secondOfPair
      have hrest := ih (AnBnPDAStack.marker :: stack)
      have htarget :
          Word.Concat (AnBnPDAStackWord pairs)
              (AnBnPDAStack.marker :: stack) =
            Word.Concat (AnBnPDAStackWord (pairs + 1)) stack := by
        simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol,
          Section01.replicate_succ_eq_append AnBnPDAStack.marker pairs,
          List.append_assoc]
      have htail : PDA.Computes HalfRangePDA
          { state := HalfRangePDAState.ready,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
            stack := AnBnPDAStack.marker :: stack }
          { state := HalfRangePDAState.ready, unread := rest,
            stack := Word.Concat (AnBnPDAStackWord (pairs + 1)) stack } := by
        simpa [htarget] using hrest
      have hprefix :
          Word.RepeatSymbol Section01.AB.a (2 * (pairs + 1)) =
            Section01.AB.a :: Section01.AB.a ::
              Word.RepeatSymbol Section01.AB.a (2 * pairs) := by
        simp [Word.RepeatSymbol]
        rw [show 2 * (pairs + 1) = 2 * pairs + 1 + 1 by omega]
        rw [List.replicate_succ]
        rw [List.replicate_succ]
      rw [hprefix]
      exact PDA.Computes.step hfirst
        (PDA.Computes.step hsecond htail)

theorem halfRangePDA_push_as_with_pairs (pairs singles : Nat)
    (rest : Word Section01.AB) (stack : Word AnBnPDAStack) :
    PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.ready,
        unread :=
          Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs + singles)) rest,
        stack := stack }
      { state := HalfRangePDAState.ready,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord (pairs + singles)) stack } := by
  have hpairs :=
    halfRangePDA_push_pairs pairs
      (Word.Concat (Word.RepeatSymbol Section01.AB.a singles) rest) stack
  have hsingles :=
    halfRangePDA_push_singles singles rest
      (Word.Concat (AnBnPDAStackWord pairs) stack)
  have hpairs' : PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.ready,
        unread :=
          Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs + singles)) rest,
        stack := stack }
      { state := HalfRangePDAState.ready,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a singles) rest,
        stack := Word.Concat (AnBnPDAStackWord pairs) stack } := by
    have hrepeat :
        Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs))
            (Word.Concat (Word.RepeatSymbol Section01.AB.a singles) rest) =
          Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs + singles)) rest := by
      simp [Word.Concat, Word.RepeatSymbol]
      rw [← List.append_assoc, List.replicate_append_replicate]
    simpa [hrepeat] using hpairs
  have hsingles' : PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.ready,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a singles) rest,
        stack := Word.Concat (AnBnPDAStackWord pairs) stack }
      { state := HalfRangePDAState.ready,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord (pairs + singles)) stack } := by
    have hstack :
        Word.Concat (AnBnPDAStackWord singles)
            (Word.Concat (AnBnPDAStackWord pairs) stack) =
          Word.Concat (AnBnPDAStackWord (pairs + singles)) stack := by
      simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol]
      rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm]
    simpa [hstack] using hsingles
  exact PDA.computes_trans hpairs' hsingles'

theorem halfRangePDA_switch_to_pop (unread : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Step HalfRangePDA
      { state := HalfRangePDAState.ready, unread := unread, stack := stack }
      { state := HalfRangePDAState.pop, unread := unread, stack := stack } := by
  simpa [Word.Concat] using
    (PDA.Step.epsilon (M := HalfRangePDA) (unread := unread)
      (restStack := stack) HalfRangePDATransition.startPop)

theorem halfRangePDA_pop_bs (m : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.pop,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
        stack := Word.Concat (AnBnPDAStackWord m) stack }
      { state := HalfRangePDAState.pop, unread := rest, stack := stack } := by
  induction m generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ m ih =>
      have hstep : PDA.Step HalfRangePDA
          { state := HalfRangePDAState.pop,
            unread := Section01.AB.b ::
              Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
            stack := AnBnPDAStack.marker ::
              Word.Concat (AnBnPDAStackWord m) stack }
          { state := HalfRangePDAState.pop,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
            stack := Word.Concat (AnBnPDAStackWord m) stack } := by
        exact PDA.Step.read (M := HalfRangePDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest)
          (restStack := Word.Concat (AnBnPDAStackWord m) stack)
          HalfRangePDATransition.popB
      exact PDA.Computes.step hstep (ih stack)

theorem halfRangePDA_accepts_range_words {n m : Nat}
    (hLower : m <= n) (hUpper : n <= 2 * m) :
    PDA.Accepts HalfRangePDA (AnBmWord n m) := by
  let pairs := n - m
  let singles := 2 * m - n
  have hn : n = 2 * pairs + singles := by
    simp [pairs, singles]
    omega
  have hm : m = pairs + singles := by
    simp [pairs, singles]
    omega
  exists HalfRangePDAState.pop
  constructor
  · rfl
  · unfold PDA.initial AnBmWord
    have hpush :=
      halfRangePDA_push_as_with_pairs pairs singles
        (Word.RepeatSymbol Section01.AB.b m) ([] : Word AnBnPDAStack)
    have hpush' : PDA.Computes HalfRangePDA
        { state := HalfRangePDAState.ready,
          unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n)
            (Word.RepeatSymbol Section01.AB.b m),
          stack := [] }
        { state := HalfRangePDAState.ready,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord m) [] } := by
      rw [hn]
      have hstack :
          Word.Concat (AnBnPDAStackWord (pairs + singles)) [] =
            Word.Concat (AnBnPDAStackWord m) [] := by
        rw [← hm]
      simpa [hstack] using hpush
    have hswitch : PDA.Computes HalfRangePDA
        { state := HalfRangePDAState.ready,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord m) [] }
        { state := HalfRangePDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord m) [] } := by
      exact PDA.computes_of_step
        (halfRangePDA_switch_to_pop (Word.RepeatSymbol Section01.AB.b m)
          (Word.Concat (AnBnPDAStackWord m) []))
    have hpop : PDA.Computes HalfRangePDA
        { state := HalfRangePDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord m) [] }
        { state := HalfRangePDAState.pop, unread := [], stack := [] } := by
      simpa [Word.Concat] using halfRangePDA_pop_bs m [] []
    exact PDA.computes_trans hpush'
      (PDA.computes_trans hswitch hpop)

/-!
The converse proof uses tail predicates to describe what remains possible from
each state. They rule out malformed endings, for example stopping in the middle
of an {lit}`a` pair or trying to pop more markers than were pushed.
-/

def HalfRangeReadyTail (unread : Word Section01.AB)
    (stack : Word AnBnPDAStack) : Prop :=
  exists n m,
    m <= n ∧ n <= 2 * m ∧
      unread =
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (Word.Length stack + m))

def HalfRangeNeedSecondTail (unread : Word Section01.AB)
    (stack : Word AnBnPDAStack) : Prop :=
  exists n m,
    m <= n ∧ n < 2 * m ∧
      unread =
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (Word.Length stack + m))

def HalfRangeAcceptedTail :
    HalfRangePDAState -> Word Section01.AB -> Word AnBnPDAStack -> Prop
  | HalfRangePDAState.pop, unread, stack =>
      unread = Word.RepeatSymbol Section01.AB.b (Word.Length stack)
  | HalfRangePDAState.ready, unread, stack =>
      HalfRangeReadyTail unread stack
  | HalfRangePDAState.needSecond, unread, stack =>
      HalfRangeNeedSecondTail unread stack

theorem halfRangePDA_computes_final_shape_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState}
    (h : PDA.Computes HalfRangePDA c d)
    (hfinal :
      d = { state := HalfRangePDAState.pop, unread := [], stack := [] }) :
    HalfRangeAcceptedTail c.state c.unread c.stack := by
  induction h with
  | refl c =>
      rw [hfinal]
      simp [HalfRangeAcceptedTail, Word.Length, Word.RepeatSymbol]
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases htrans with
          | oneA =>
              cases ih hfinal with
              | intro n hn =>
                  cases hn with
                  | intro m hm =>
                      exists n + 1
                      exists m + 1
                      constructor
                      · omega
                      constructor
                      · omega
                      · simp [Word.Length, Word.Concat, Word.RepeatSymbol] at hm ⊢
                        rw [hm.right.right]
                        simp [Section01.replicate_succ_eq_cons,
                          Nat.add_comm, Nat.add_left_comm]
          | firstOfPair =>
              cases ih hfinal with
              | intro n hn =>
                  cases hn with
                  | intro m hm =>
                      exists n + 1
                      exists m
                      constructor
                      · omega
                      constructor
                      · omega
                      · simp [Word.Length, Word.Concat, Word.RepeatSymbol] at hm ⊢
                        rw [hm.right.right]
                        simp [Section01.replicate_succ_eq_cons]
          | secondOfPair =>
              cases ih hfinal with
              | intro n hn =>
                  cases hn with
                  | intro m hm =>
                      exists n + 1
                      exists m + 1
                      constructor
                      · omega
                      constructor
                      · omega
                      · simp [Word.Length, Word.Concat, Word.RepeatSymbol] at hm ⊢
                        rw [hm.right.right]
                        simp [Section01.replicate_succ_eq_cons,
                          Nat.add_comm, Nat.add_left_comm]
          | popB =>
              have htail := ih hfinal
              simp [HalfRangeAcceptedTail, Word.Concat, Word.Length,
                Word.RepeatSymbol] at htail ⊢
              rw [htail]
              rw [List.replicate_succ]
      | epsilon htrans =>
          cases htrans with
          | startPop =>
              have hpop := ih hfinal
              exact ⟨0, 0, by omega, by omega,
                by
                  simpa [HalfRangeAcceptedTail, HalfRangeReadyTail,
                    Word.Concat, Word.RepeatSymbol, Word.Length] using hpop⟩

theorem halfRangePDA_accepts_only_range_words {w : Word Section01.AB}
    (h : PDA.Accepts HalfRangePDA w) :
    w ∈ HalfRangeLanguage := by
  cases h with
  | intro q hq =>
      cases hq.left
      have hshape := halfRangePDA_computes_final_shape_config hq.right rfl
      cases hshape with
      | intro n hn =>
          cases hn with
          | intro m hm =>
              exists n
              exists m
              constructor
              · exact hm.left
              constructor
              · exact hm.right.left
              · simpa [PDA.initial, HalfRangeAcceptedTail, HalfRangeReadyTail,
                  HalfRangeLanguage, AnBmWord, Word.Length, Word.Concat]
                  using hm.right.right

theorem halfRangePDA_accepted_language_exact (w : Word Section01.AB) :
    w ∈ PDA.AcceptedLanguage HalfRangePDA <-> w ∈ HalfRangeLanguage := by
  constructor
  · exact halfRangePDA_accepts_only_range_words
  · intro hw
    cases hw with
    | intro n hn =>
        cases hn with
        | intro m hm =>
            rw [hm.right.right]
            exact halfRangePDA_accepts_range_words hm.left hm.right.left

/-!
# A Deterministic {lit}`a^n b^n` PDA

This variant removes epsilon guessing: the first `b` deterministically switches
from pushing to popping. It illustrates the deterministic vocabulary introduced
earlier in the section.
-/

inductive DetAnBnPDAState where
  | read
  | pop
deriving DecidableEq

namespace DetAnBnPDAState

def finite : Foundation.FiniteType DetAnBnPDAState where
  elems := [read, pop]
  complete := by
    intro q
    cases q <;> simp

end DetAnBnPDAState

inductive DetAnBnPDATransition :
    DetAnBnPDAState -> Option Section01.AB -> Word AnBnPDAStack ->
      DetAnBnPDAState -> Word AnBnPDAStack -> Prop where
  | readA :
      DetAnBnPDATransition DetAnBnPDAState.read (some Section01.AB.a) []
        DetAnBnPDAState.read [AnBnPDAStack.marker]
  | firstB :
      DetAnBnPDATransition DetAnBnPDAState.read (some Section01.AB.b)
        [AnBnPDAStack.marker] DetAnBnPDAState.pop []
  | popB :
      DetAnBnPDATransition DetAnBnPDAState.pop (some Section01.AB.b)
        [AnBnPDAStack.marker] DetAnBnPDAState.pop []

def DetAnBnPDA : PDA Section01.AB AnBnPDAStack DetAnBnPDAState where
  start := DetAnBnPDAState.read
  transition := DetAnBnPDATransition
  accept := fun q => q = DetAnBnPDAState.read ∨ q = DetAnBnPDAState.pop
  statesFinite := DetAnBnPDAState.finite

/-!
The deterministic machine has no epsilon choice for when to switch. It keeps
reading {lit}`a`s until it sees the first {lit}`b`; that first {lit}`b` both
changes state and pops one marker. Because the transition relation has no
alternative in a given situation, the language proof also establishes the
deterministic behavior expected in the textbook discussion.
-/

theorem detAnBnPDA_push_as (n : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes DetAnBnPDA
      { state := DetAnBnPDAState.read,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
        stack := stack }
      { state := DetAnBnPDAState.read,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord n) stack } := by
  induction n generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      have hstep : PDA.Step DetAnBnPDA
          { state := DetAnBnPDAState.read,
            unread := Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := stack }
          { state := DetAnBnPDAState.read,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := AnBnPDAStack.marker :: stack } := by
        exact PDA.Step.read (M := DetAnBnPDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest)
          (restStack := stack) DetAnBnPDATransition.readA
      have hrest := ih (AnBnPDAStack.marker :: stack)
      have htarget :
          Word.Concat (AnBnPDAStackWord n)
              (AnBnPDAStack.marker :: stack) =
            Word.Concat (AnBnPDAStackWord (n + 1)) stack := by
        simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol,
          Section01.replicate_succ_eq_append AnBnPDAStack.marker n,
          List.append_assoc]
      exact PDA.Computes.step hstep (by
        simpa [htarget] using hrest)

theorem detAnBnPDA_first_b (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Step DetAnBnPDA
      { state := DetAnBnPDAState.read,
        unread := Section01.AB.b :: rest,
        stack := AnBnPDAStack.marker :: stack }
      { state := DetAnBnPDAState.pop, unread := rest, stack := stack } := by
  simpa [Word.Concat] using
    (PDA.Step.read (M := DetAnBnPDA) (unread := rest)
      (restStack := stack) DetAnBnPDATransition.firstB)

theorem detAnBnPDA_pop_bs (n : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes DetAnBnPDA
      { state := DetAnBnPDAState.pop,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
        stack := Word.Concat (AnBnPDAStackWord n) stack }
      { state := DetAnBnPDAState.pop, unread := rest, stack := stack } := by
  induction n generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      have hstep : PDA.Step DetAnBnPDA
          { state := DetAnBnPDAState.pop,
            unread := Section01.AB.b ::
              Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
            stack := AnBnPDAStack.marker ::
              Word.Concat (AnBnPDAStackWord n) stack }
          { state := DetAnBnPDAState.pop,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
            stack := Word.Concat (AnBnPDAStackWord n) stack } := by
        exact PDA.Step.read (M := DetAnBnPDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest)
          (restStack := Word.Concat (AnBnPDAStackWord n) stack)
          DetAnBnPDATransition.popB
      exact PDA.Computes.step hstep (ih stack)

theorem detAnBnPDA_accepts_anbn_words (n : Nat) :
    PDA.Accepts DetAnBnPDA (Section01.AnBnWord n) := by
  cases n with
  | zero =>
      exists DetAnBnPDAState.read
      constructor
      · exact Or.inl rfl
      · simp [Section01.AnBnWord, PDA.initial, Word.Concat, Word.RepeatSymbol]
        exact PDA.Computes.refl _
  | succ n =>
      exists DetAnBnPDAState.pop
      constructor
      · exact Or.inr rfl
      · unfold Section01.AnBnWord PDA.initial
        have hpush :=
          detAnBnPDA_push_as (n + 1)
            (Word.RepeatSymbol Section01.AB.b (n + 1))
            ([] : Word AnBnPDAStack)
        have hfirst : PDA.Computes DetAnBnPDA
            { state := DetAnBnPDAState.read,
              unread := Section01.AB.b :: Word.RepeatSymbol Section01.AB.b n,
              stack := Word.Concat (AnBnPDAStackWord (n + 1)) [] }
            { state := DetAnBnPDAState.pop,
              unread := Word.RepeatSymbol Section01.AB.b n,
              stack := Word.Concat (AnBnPDAStackWord n) [] } := by
          simpa [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol] using
            PDA.computes_of_step (detAnBnPDA_first_b
              (Word.RepeatSymbol Section01.AB.b n)
              (Word.Concat (AnBnPDAStackWord n) []))
        have hpop : PDA.Computes DetAnBnPDA
            { state := DetAnBnPDAState.pop,
              unread := Word.RepeatSymbol Section01.AB.b n,
              stack := Word.Concat (AnBnPDAStackWord n) [] }
            { state := DetAnBnPDAState.pop, unread := [], stack := [] } := by
          simpa [Word.Concat] using detAnBnPDA_pop_bs n [] []
        exact PDA.computes_trans hpush
          (PDA.computes_trans hfirst hpop)

/-!
As with the nondeterministic version, the reverse direction is a state-by-state
shape proof. The read state can only consume {lit}`a`s or the first {lit}`b`;
the pop state can only consume the remaining {lit}`b`s while removing markers.
-/

def DetAnBnReadFinalTail :
    DetAnBnPDAState -> Word Section01.AB -> Word AnBnPDAStack -> Prop
  | DetAnBnPDAState.read, unread, stack => unread = [] ∧ stack = []
  | DetAnBnPDAState.pop, _, _ => False

def DetAnBnPopFinalTail :
    DetAnBnPDAState -> Word Section01.AB -> Word AnBnPDAStack -> Prop
  | DetAnBnPDAState.pop, unread, stack =>
      unread = Word.RepeatSymbol Section01.AB.b (Word.Length stack)
  | DetAnBnPDAState.read, unread, stack =>
      exists n,
        unread =
          Word.Concat (Word.RepeatSymbol Section01.AB.a n)
            (Word.RepeatSymbol Section01.AB.b (Word.Length stack + n))

theorem detAnBnPDA_computes_read_final_shape_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack DetAnBnPDAState}
    (h : PDA.Computes DetAnBnPDA c d)
    (hfinal :
      d = { state := DetAnBnPDAState.read, unread := [], stack := [] }) :
    DetAnBnReadFinalTail c.state c.unread c.stack := by
  induction h with
  | refl c =>
      rw [hfinal]
      simp [DetAnBnReadFinalTail]
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases htrans with
          | readA =>
              have htail := ih hfinal
              cases htail.right
          | firstB =>
              exact False.elim (ih hfinal)
          | popB =>
              exact False.elim (ih hfinal)
      | epsilon htrans =>
          cases htrans

theorem detAnBnPDA_computes_pop_final_shape_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack DetAnBnPDAState}
    (h : PDA.Computes DetAnBnPDA c d)
    (hfinal :
      d = { state := DetAnBnPDAState.pop, unread := [], stack := [] }) :
    DetAnBnPopFinalTail c.state c.unread c.stack := by
  induction h with
  | refl c =>
      rw [hfinal]
      simp [DetAnBnPopFinalTail, Word.Length, Word.RepeatSymbol]
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases htrans with
          | readA =>
              cases ih hfinal with
              | intro n hn =>
                  exists n + 1
                  simp [Word.Length, Word.Concat, Word.RepeatSymbol] at hn ⊢
                  rw [hn]
                  simp [Section01.replicate_succ_eq_cons,
                    Nat.add_comm, Nat.add_left_comm]
          | firstB =>
              have htail := ih hfinal
              exists 0
              simp [DetAnBnPopFinalTail, Word.Length, Word.Concat,
                Word.RepeatSymbol] at htail ⊢
              rw [htail]
              rw [List.replicate_succ]
          | popB =>
              have htail := ih hfinal
              simp [DetAnBnPopFinalTail, Word.Concat, Word.Length,
                Word.RepeatSymbol] at htail ⊢
              rw [htail]
              rw [List.replicate_succ]
      | epsilon htrans =>
          cases htrans

theorem detAnBnPDA_accepts_only_anbn_words {w : Word Section01.AB}
    (h : PDA.Accepts DetAnBnPDA w) :
    exists n, w = Section01.AnBnWord n := by
  cases h with
  | intro q hq =>
      cases hq.left with
      | inl hread =>
          subst q
          have hshape :=
            detAnBnPDA_computes_read_final_shape_config hq.right rfl
          exists 0
          simpa [PDA.initial, DetAnBnReadFinalTail, Section01.AnBnWord,
            Word.Concat, Word.RepeatSymbol] using hshape.left
      | inr hpop =>
          subst q
          have hshape :=
            detAnBnPDA_computes_pop_final_shape_config hq.right rfl
          cases hshape with
          | intro n hn =>
              exists n
              simpa [PDA.initial, DetAnBnPopFinalTail, Section01.AnBnWord,
                Word.Length, Word.Concat] using hn

theorem detAnBnPDA_accepted_language_exact (w : Word Section01.AB) :
    w ∈ PDA.AcceptedLanguage DetAnBnPDA <->
      exists n, w = Section01.AnBnWord n := by
  constructor
  · exact detAnBnPDA_accepts_only_anbn_words
  · intro h
    cases h with
        | intro n hn =>
            rw [hn]
            exact detAnBnPDA_accepts_anbn_words n

/-!
# Copy Across a Center Marker

The final example recognizes words of the form `w c reverse(w)`. The stack
stores the first half, the center marker switches modes, and the second half
must pop matching symbols in reverse order.
-/

inductive CopyInput where
  | a
  | b
  | c
deriving DecidableEq

inductive CopyPDAState where
  | push
  | pop
deriving DecidableEq

namespace CopyPDAState

def finite : Foundation.FiniteType CopyPDAState where
  elems := [push, pop]
  complete := by
    intro q
    cases q <;> simp

end CopyPDAState

def copyInputOfAB : Section01.AB -> CopyInput
  | Section01.AB.a => CopyInput.a
  | Section01.AB.b => CopyInput.b

def copyInputWord (w : Word Section01.AB) : Word CopyInput :=
  w.map copyInputOfAB

def copyCenteredWord (w : Word Section01.AB) : Word CopyInput :=
  Word.Concat (copyInputWord w)
    (CopyInput.c :: copyInputWord (Word.Reverse w))

inductive CopyPDATransition :
    CopyPDAState -> Option CopyInput -> Word Section01.AB ->
      CopyPDAState -> Word Section01.AB -> Prop where
  | pushA :
      CopyPDATransition CopyPDAState.push (some CopyInput.a) []
        CopyPDAState.push [Section01.AB.a]
  | pushB :
      CopyPDATransition CopyPDAState.push (some CopyInput.b) []
        CopyPDAState.push [Section01.AB.b]
  | readCenter :
      CopyPDATransition CopyPDAState.push (some CopyInput.c) []
        CopyPDAState.pop []
  | popA :
      CopyPDATransition CopyPDAState.pop (some CopyInput.a)
        [Section01.AB.a] CopyPDAState.pop []
  | popB :
      CopyPDATransition CopyPDAState.pop (some CopyInput.b)
        [Section01.AB.b] CopyPDAState.pop []

def CopyPDA : PDA CopyInput Section01.AB CopyPDAState where
  start := CopyPDAState.push
  transition := CopyPDATransition
  accept := fun q => q = CopyPDAState.pop
  statesFinite := CopyPDAState.finite

/-!
The copy PDA uses the stack as a reverse buffer. Before the center marker, it
pushes each {lit}`a` or {lit}`b`. After the center marker, it must read the
matching symbols while popping them, so the second half is the reverse of the
first half.
-/

theorem copyPDA_push_word (w : Word Section01.AB) (rest : Word CopyInput)
    (stack : Word Section01.AB) :
    PDA.Computes CopyPDA
      { state := CopyPDAState.push,
        unread := Word.Concat (copyInputWord w) rest,
        stack := stack }
      { state := CopyPDAState.push,
        unread := rest,
        stack := Word.Concat (Word.Reverse w) stack } := by
  induction w generalizing stack with
  | nil =>
      simp [copyInputWord, Word.Concat, Word.Reverse]
      exact PDA.Computes.refl _
  | cons sym tail ih =>
      cases sym
      · have hstep : PDA.Step CopyPDA
            { state := CopyPDAState.push,
              unread := CopyInput.a :: Word.Concat (copyInputWord tail) rest,
              stack := stack }
            { state := CopyPDAState.push,
              unread := Word.Concat (copyInputWord tail) rest,
              stack := Section01.AB.a :: stack } := by
          exact PDA.Step.read (M := CopyPDA)
            (unread := Word.Concat (copyInputWord tail) rest)
            (restStack := stack) CopyPDATransition.pushA
        have hrest := ih (Section01.AB.a :: stack)
        exact PDA.Computes.step hstep (by
          simpa [copyInputWord, copyInputOfAB, Word.Concat, Word.Reverse,
            List.map_reverse, List.append_assoc] using hrest)
      · have hstep : PDA.Step CopyPDA
            { state := CopyPDAState.push,
              unread := CopyInput.b :: Word.Concat (copyInputWord tail) rest,
              stack := stack }
            { state := CopyPDAState.push,
              unread := Word.Concat (copyInputWord tail) rest,
              stack := Section01.AB.b :: stack } := by
          exact PDA.Step.read (M := CopyPDA)
            (unread := Word.Concat (copyInputWord tail) rest)
            (restStack := stack) CopyPDATransition.pushB
        have hrest := ih (Section01.AB.b :: stack)
        exact PDA.Computes.step hstep (by
          simpa [copyInputWord, copyInputOfAB, Word.Concat, Word.Reverse,
            List.map_reverse, List.append_assoc] using hrest)

theorem copyPDA_read_center (rest : Word CopyInput)
    (stack : Word Section01.AB) :
    PDA.Step CopyPDA
      { state := CopyPDAState.push,
        unread := CopyInput.c :: rest,
        stack := stack }
      { state := CopyPDAState.pop, unread := rest, stack := stack } := by
  simpa [Word.Concat] using
    (PDA.Step.read (M := CopyPDA) (unread := rest)
      (restStack := stack) CopyPDATransition.readCenter)

theorem copyPDA_pop_word (w : Word Section01.AB) (rest : Word CopyInput)
    (stack : Word Section01.AB) :
    PDA.Computes CopyPDA
      { state := CopyPDAState.pop,
        unread := Word.Concat (copyInputWord w) rest,
        stack := Word.Concat w stack }
      { state := CopyPDAState.pop, unread := rest, stack := stack } := by
  induction w generalizing stack with
  | nil =>
      simp [copyInputWord, Word.Concat]
      exact PDA.Computes.refl _
  | cons sym tail ih =>
      cases sym
      · have hstep : PDA.Step CopyPDA
            { state := CopyPDAState.pop,
              unread := CopyInput.a :: Word.Concat (copyInputWord tail) rest,
              stack := Section01.AB.a :: Word.Concat tail stack }
            { state := CopyPDAState.pop,
              unread := Word.Concat (copyInputWord tail) rest,
              stack := Word.Concat tail stack } := by
          exact PDA.Step.read (M := CopyPDA)
            (unread := Word.Concat (copyInputWord tail) rest)
            (restStack := Word.Concat tail stack) CopyPDATransition.popA
        exact PDA.Computes.step hstep (ih stack)
      · have hstep : PDA.Step CopyPDA
            { state := CopyPDAState.pop,
              unread := CopyInput.b :: Word.Concat (copyInputWord tail) rest,
              stack := Section01.AB.b :: Word.Concat tail stack }
            { state := CopyPDAState.pop,
              unread := Word.Concat (copyInputWord tail) rest,
              stack := Word.Concat tail stack } := by
          exact PDA.Step.read (M := CopyPDA)
            (unread := Word.Concat (copyInputWord tail) rest)
            (restStack := Word.Concat tail stack) CopyPDATransition.popB
        exact PDA.Computes.step hstep (ih stack)

theorem copyPDA_accepts_centered_reverse (w : Word Section01.AB) :
    PDA.Accepts CopyPDA (copyCenteredWord w) := by
  exists CopyPDAState.pop
  constructor
  · rfl
  · unfold PDA.initial copyCenteredWord
    have hpush :=
      copyPDA_push_word w
        (CopyInput.c :: copyInputWord (Word.Reverse w))
        ([] : Word Section01.AB)
    have hcenter : PDA.Computes CopyPDA
        { state := CopyPDAState.push,
          unread := CopyInput.c :: copyInputWord (Word.Reverse w),
          stack := Word.Concat (Word.Reverse w) [] }
        { state := CopyPDAState.pop,
          unread := copyInputWord (Word.Reverse w),
          stack := Word.Concat (Word.Reverse w) [] } := by
      exact PDA.computes_of_step
        (copyPDA_read_center (copyInputWord (Word.Reverse w))
          (Word.Concat (Word.Reverse w) []))
    have hpop : PDA.Computes CopyPDA
        { state := CopyPDAState.pop,
          unread := copyInputWord (Word.Reverse w),
          stack := Word.Concat (Word.Reverse w) [] }
        { state := CopyPDAState.pop, unread := [], stack := [] } := by
      simpa [Word.Concat] using copyPDA_pop_word (Word.Reverse w) [] []
    exact PDA.computes_trans hpush
      (PDA.computes_trans hcenter hpop)

/-!
The converse proof again uses a tail predicate: once the machine has crossed
the center marker, every remaining input symbol must match the current stack
top. That forces accepted words to have the form {lit}`w c reverse(w)`.
-/

def CopyCenteredLanguage : Language CopyInput :=
  fun input => exists w : Word Section01.AB, input = copyCenteredWord w

def CopyAcceptedTail :
    CopyPDAState -> Word CopyInput -> Word Section01.AB -> Prop
  | CopyPDAState.pop, unread, stack =>
      unread = copyInputWord stack
  | CopyPDAState.push, unread, stack =>
      exists w : Word Section01.AB,
        unread =
          Word.Concat (copyInputWord w)
            (CopyInput.c ::
              copyInputWord (Word.Concat (Word.Reverse w) stack))

theorem copyPDA_computes_final_shape_config
    {c d : PDA.Configuration CopyInput Section01.AB CopyPDAState}
    (h : PDA.Computes CopyPDA c d)
    (hfinal :
      d = { state := CopyPDAState.pop, unread := [], stack := [] }) :
    CopyAcceptedTail c.state c.unread c.stack := by
  induction h with
  | refl c =>
      rw [hfinal]
      simp [CopyAcceptedTail, copyInputWord]
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases htrans with
          | pushA =>
              cases ih hfinal with
              | intro w hw =>
                  exists Section01.AB.a :: w
                  simp [copyInputWord, copyInputOfAB,
                    Word.Concat, Word.Reverse, List.map_reverse,
                    List.append_assoc] at hw ⊢
                  rw [hw]
          | pushB =>
              cases ih hfinal with
              | intro w hw =>
                  exists Section01.AB.b :: w
                  simp [copyInputWord, copyInputOfAB,
                    Word.Concat, Word.Reverse, List.map_reverse,
                    List.append_assoc] at hw ⊢
                  rw [hw]
          | readCenter =>
              have htail := ih hfinal
              exists []
              simp [CopyAcceptedTail, copyInputWord, Word.Concat, Word.Reverse] at htail ⊢
              rw [htail]
          | popA =>
              have htail := ih hfinal
              simp [CopyAcceptedTail, copyInputWord, copyInputOfAB,
                Word.Concat] at htail ⊢
              rw [htail]
          | popB =>
              have htail := ih hfinal
              simp [CopyAcceptedTail, copyInputWord, copyInputOfAB,
                Word.Concat] at htail ⊢
              rw [htail]
      | epsilon htrans =>
          cases htrans

theorem copyPDA_accepts_only_centered_reverse {input : Word CopyInput}
    (h : PDA.Accepts CopyPDA input) :
    input ∈ CopyCenteredLanguage := by
  cases h with
  | intro q hq =>
      cases hq.left
      have hshape := copyPDA_computes_final_shape_config hq.right rfl
      cases hshape with
      | intro w hw =>
          exists w
          simpa [PDA.initial, CopyAcceptedTail, CopyCenteredLanguage,
            copyCenteredWord, Word.Concat] using hw

theorem copyPDA_accepted_language_exact (input : Word CopyInput) :
    input ∈ PDA.AcceptedLanguage CopyPDA <->
      input ∈ CopyCenteredLanguage := by
  constructor
  · exact copyPDA_accepts_only_centered_reverse
  · intro h
    cases h with
    | intro w hw =>
        rw [hw]
        exact copyPDA_accepts_centered_reverse w

end Section04
end Chapter04
end Book
end FoC
