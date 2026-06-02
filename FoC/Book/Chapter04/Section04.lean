import FoC.Book.Chapter04.Section01
import FoC.Grammars.CFGToPDA
import FoC.Grammars.PDAToCFG

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

/-!
Book: Chapter 4, Section 4.4, Pushdown Automata.
-/

open Languages
open Grammars

-- Book: Chapter 4, Section 4.4, multi-step PDA computation is transitive.
theorem pda_computation_transitive {M : PDA input stack state}
    {a b c : PDA.Configuration input stack state}
    (hab : PDA.Computes M a b) (hbc : PDA.Computes M b c) :
    PDA.Computes M a c :=
  PDA.computes_trans hab hbc

-- Book: Chapter 4, Section 4.4, one PDA step is a computation.
theorem pda_step_is_computation {M : PDA input stack state}
    {a b : PDA.Configuration input stack state} (h : PDA.Step M a b) :
    PDA.Computes M a b :=
  PDA.computes_of_step h

-- Book: Chapter 4, Section 4.4, a length-indexed PDA computation is an
-- ordinary multi-step computation.
theorem pda_bounded_computation_is_computation
    {M : PDA input stack state}
    {n : Nat} {a b : PDA.Configuration input stack state}
    (h : PDA.ComputesIn M n a b) :
    PDA.Computes M a b :=
  PDA.computesIn_computes h

-- Book: Chapter 4, Section 4.4, every ordinary multi-step computation has a
-- finite step count.
theorem pda_computation_has_length
    {M : PDA input stack state}
    {a b : PDA.Configuration input stack state}
    (h : PDA.Computes M a b) :
    exists n : Nat, PDA.ComputesIn M n a b :=
  PDA.computes_exists_length h

-- Book: Chapter 4, Section 4.4, ordinary and length-indexed PDA computations
-- are equivalent up to existentially hiding the step count.
theorem pda_computation_iff_has_length
    {M : PDA input stack state}
    {a b : PDA.Configuration input stack state} :
    PDA.Computes M a b <->
      exists n : Nat, PDA.ComputesIn M n a b :=
  PDA.computes_iff_exists_computesIn

-- Book: Chapter 4, Section 4.4, one PDA step is a one-step indexed
-- computation.
theorem pda_step_is_bounded_computation
    {M : PDA input stack state}
    {a b : PDA.Configuration input stack state}
    (h : PDA.Step M a b) :
    PDA.ComputesIn M 1 a b :=
  PDA.computesIn_of_step h

-- Book: Chapter 4, Section 4.4, length-indexed PDA computations compose and
-- their lengths add.
theorem pda_bounded_computation_transitive
    {M : PDA input stack state}
    {m n : Nat} {a b c : PDA.Configuration input stack state}
    (hab : PDA.ComputesIn M m a b)
    (hbc : PDA.ComputesIn M n b c) :
    PDA.ComputesIn M (m + n) a c :=
  PDA.computesIn_trans hab hbc

-- Book: Chapter 4, Section 4.4, a zero-length indexed computation has equal
-- endpoints.
theorem pda_bounded_computation_zero_eq
    {M : PDA input stack state}
    {a b : PDA.Configuration input stack state}
    (h : PDA.ComputesIn M 0 a b) : a = b :=
  PDA.computesIn_zero_eq h

-- Book: Chapter 4, Section 4.4, a positive-length indexed computation splits
-- into its first step and the remaining indexed computation.
theorem pda_bounded_computation_succ_inv
    {M : PDA input stack state}
    {n : Nat} {a c : PDA.Configuration input stack state}
    (h : PDA.ComputesIn M (n + 1) a c) :
    exists b : PDA.Configuration input stack state,
      PDA.Step M a b ∧ PDA.ComputesIn M n b c :=
  PDA.computesIn_succ_inv h

-- Book: Chapter 4, Section 4.4, a one-step indexed computation is exactly a
-- PDA step.
theorem pda_bounded_computation_one_inv
    {M : PDA input stack state}
    {a c : PDA.Configuration input stack state}
    (h : PDA.ComputesIn M 1 a c) :
    PDA.Step M a c :=
  PDA.computesIn_one_inv h

-- Book: Chapter 4, Section 4.4, a PDA step consumes either no input or one
-- leading input symbol.
theorem pda_step_consumes_empty_or_symbol
    {M : PDA input stack state}
    {c d : PDA.Configuration input stack state}
    (h : PDA.Step M c d) :
    (c.unread = d.unread) ∨
      exists a : input, c.unread = a :: d.unread :=
  PDA.step_consumes_empty_or_symbol h

-- Book: Chapter 4, Section 4.4, a PDA step consumes a prefix of the source
-- unread word.
theorem pda_step_consumes_prefix
    {M : PDA input stack state}
    {c d : PDA.Configuration input stack state}
    (h : PDA.Step M c d) :
    exists consumed : Word input,
      c.unread = Word.Concat consumed d.unread :=
  PDA.step_consumes_prefix h

-- Book: Chapter 4, Section 4.4, a bounded PDA computation consumes a prefix
-- of the source unread word.
theorem pda_bounded_computation_consumes_prefix
    {M : PDA input stack state}
    {n : Nat} {c d : PDA.Configuration input stack state}
    (h : PDA.ComputesIn M n c d) :
    exists consumed : Word input,
      c.unread = Word.Concat consumed d.unread :=
  PDA.computesIn_consumes_prefix h

-- Book: Chapter 4, Section 4.4, any PDA computation consumes a prefix of the
-- source unread word.
theorem pda_computation_consumes_prefix
    {M : PDA input stack state}
    {c d : PDA.Configuration input stack state}
    (h : PDA.Computes M c d) :
    exists consumed : Word input,
      c.unread = Word.Concat consumed d.unread :=
  PDA.computes_consumes_prefix h

-- Book: Chapter 4, Section 4.4, accepted language of a PDA.
def PDAAcceptedLanguage (M : PDA input stack state) : Language input :=
  PDA.AcceptedLanguage M

-- Book: Chapter 4, Section 4.4, a finite PDA presentation includes a finite
-- stack alphabet, a finite transition table, and a finite accepting-state
-- table.  The state set is already finite in the base `PDA` structure.
def FinitePresentationPDA (M : PDA input stack state) : Prop :=
  PDA.HasFinitePresentation M

-- Book: Chapter 4, Section 4.4, top-pop normal-form PDAs are the direct input
-- to the standard PDA-to-CFG construction: each transition pops either no stack
-- symbol or exactly the current top stack symbol.
def TopPopNormalFormPDA (M : PDA input stack state) : Prop :=
  PDA.PopsAtMostOne M

-- Book: Chapter 4, Section 4.4, languages recognized by explicitly finite
-- PDA presentations.
def FinitePresentationPDARecognizable (L : Language input) : Prop :=
  PDA.FinitePresentationRecognizable L

-- Book: Chapter 4, Section 4.4, acceptance by final state and empty stack
-- implies final-state-only acceptance.
theorem pda_accepts_implies_final_state_accepts {M : PDA input stack state}
    {w : Word input} (h : PDA.Accepts M w) :
    PDA.AcceptsByFinalState M w :=
  PDA.accepts_implies_final_state_accepts h

-- Book: Chapter 4, Section 4.4, acceptance by final state and empty stack
-- implies empty-stack-only acceptance.
theorem pda_accepts_implies_empty_stack_accepts {M : PDA input stack state}
    {w : Word input} (h : PDA.Accepts M w) :
    PDA.AcceptsByEmptyStack M w :=
  PDA.accepts_implies_empty_stack_accepts h

-- Book: Chapter 4, Section 4.4, deterministic PDA vocabulary.
def DeterministicPDA (M : PDA input stack state) : Prop :=
  PDA.Deterministic M

-- Book: Chapter 4, Section 4.4, deterministic CFL presentations use an
-- explicit end marker so the deterministic PDA can see the end of input.
inductive EndMarked (input : Type u) where
  | symbol : input -> EndMarked input
  | end : EndMarked input

def endMarkedInputWord (w : Word input) : Word (EndMarked input) :=
  w.map EndMarked.symbol

def endMarkedWord (w : Word input) : Word (EndMarked input) :=
  Word.Concat (endMarkedInputWord w) [EndMarked.end]

def EndMarkedLanguage (L : Language input) : Language (EndMarked input) :=
  fun w => exists base : Word input, base ∈ L ∧ w = endMarkedWord base

-- Book: Chapter 4, Section 4.4, deterministic context-free language
-- vocabulary with an explicit end marker.
def DeterministicContextFreeLanguageWithEndMarker (L : Language input) : Prop :=
  exists stack : Type, exists state : Type,
    exists M : PDA (EndMarked input) stack state,
      PDA.Deterministic M ∧
        Language.Equal (PDA.AcceptedLanguage M) (EndMarkedLanguage L)

-- Book: Chapter 4, Section 4.4, the standard PDA constructed from a CFG.
def CFGToPDA (G : CFG terminal nonterminal) :
    PDA terminal (Symbol terminal nonterminal) CFG.ToPDAState :=
  CFG.ToPDA G

-- Book: Chapter 4, Section 4.4, the CFG-to-PDA construction recognizes
-- exactly the grammar-generated language.
theorem cfg_to_pda_language_exact
    {terminal nonterminal : Type} (G : CFG terminal nonterminal) :
    Language.Equal (PDA.AcceptedLanguage (CFGToPDA G))
      (CFG.GeneratedLanguage G) :=
  CFG.toPDA_acceptedLanguage_exact G

-- Book: Chapter 4, Section 4.4, every grammar derivation is accepted by the
-- constructed PDA.
theorem cfg_to_pda_accepts_of_generates
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    {w : Word terminal} (h : w ∈ CFG.GeneratedLanguage G) :
    PDA.Accepts (CFGToPDA G) w :=
  CFG.toPDA_accepts_of_generates h

-- Book: Chapter 4, Section 4.4, every word accepted by the constructed PDA is
-- generated by the grammar.
theorem cfg_to_pda_generates_of_accepts
    {terminal nonterminal : Type} {G : CFG terminal nonterminal}
    {w : Word terminal} (h : PDA.Accepts (CFGToPDA G) w) :
    w ∈ CFG.GeneratedLanguage G :=
  CFG.toPDA_generates_of_accepts h

-- Book: Chapter 4, Section 4.4, the standard PDA-to-CFG construction for a
-- finite-presented top-pop PDA.
def PDAToCFG (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    CFG input (PDA.ToCFGNonterminal stack state) :=
  PDA.ToCFG M presentation

-- Book: Chapter 4, Section 4.4, exactness target for the PDA-to-CFG
-- construction under the top-pop normal-form assumption.  The construction
-- module keeps this as the main theorem target while the normalization and
-- reverse direction are completed.
def PDAToCFGExact (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) : Prop :=
  PDA.ToCFGTopPopExact M presentation

-- Book: Chapter 4, Section 4.4, the PDA-to-CFG construction has a finite
-- nonterminal type from the finite state and stack alphabets.
theorem pda_to_cfg_nonterminals_finite
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    (PDAToCFG M presentation).nonterminalsFinite =
      PDA.ToCFGNonterminal.finite
        presentation.stackFinite M.statesFinite :=
  PDA.toCFG_nonterminals_finite M presentation

-- Book: Chapter 4, Section 4.4, the PDA-to-CFG construction has a finite
-- production presentation from the finite PDA transition, state, accepting,
-- and stack-symbol lists.
theorem pda_to_cfg_hasFiniteProductions
    (M : PDA input stack state)
    (presentation : PDA.FinitePresentation M) :
    CFG.HasFiniteProductions (PDAToCFG M presentation) :=
  PDA.toCFG_hasFiniteProductions M presentation

-- Book: Chapter 4, Section 4.4, soundness direction of the PDA-to-CFG
-- construction: every word generated by the constructed grammar is accepted by
-- the original PDA.
theorem pda_to_cfg_accepts_of_generates
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input}
    (h : w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation)) :
    PDA.Accepts M w :=
  PDA.toCFG_accepts_of_generates h

-- Book: Chapter 4, Section 4.4, reverse-direction local constructor for the
-- PDA-to-CFG start production.
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

-- Book: Chapter 4, Section 4.4, reverse-direction local constructor for the
-- reflexive empty-stack-tail summary production.
theorem pda_to_cfg_empty_refl_derives
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {q : state} :
    CFG.Derives (PDAToCFG M presentation)
      [Symbol.nonterminal (PDA.ToCFGNonterminal.empty q q)]
      (SententialForm.terminalWord (Word.Empty : Word input)) :=
  PDA.toCFG_emptyRefl_derives

-- Book: Chapter 4, Section 4.4, reverse-direction local constructor for a
-- one-symbol-pop transition production.
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

-- Book: Chapter 4, Section 4.4, reverse-direction local constructor for an
-- empty-pop transition that preserves the current stack tail.
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

-- Book: Chapter 4, Section 4.4, reverse-direction local constructor for an
-- empty-pop transition taken before removing the current top stack symbol.
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

-- Book: Chapter 4, Section 4.4, a decomposed derivation for a pushed stack
-- word is equivalent to a `ToCFGChain` RHS with generated pieces.
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

-- Book: Chapter 4, Section 4.4, reconstruct the decomposed derivation for a
-- pushed stack word from a `ToCFGChain` RHS and generated pieces.
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

-- Book: Chapter 4, Section 4.4, use a decomposed pushed-word derivation in a
-- one-symbol-pop production.
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

-- Book: Chapter 4, Section 4.4, use a decomposed pushed-word derivation in an
-- empty-pop tail-preserving production.
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

-- Book: Chapter 4, Section 4.4, use a decomposed pushed-word derivation in an
-- empty-pop production taken before removing the current top symbol.
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

-- Book: Chapter 4, Section 4.4, read-transition specialization of the
-- one-symbol-pop chain-decomposition constructor.
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

-- Book: Chapter 4, Section 4.4, epsilon-transition specialization of the
-- one-symbol-pop chain-decomposition constructor.
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

-- Book: Chapter 4, Section 4.4, read-transition specialization of the
-- empty-pop tail-preserving chain-decomposition constructor.
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

-- Book: Chapter 4, Section 4.4, epsilon-transition specialization of the
-- empty-pop tail-preserving chain-decomposition constructor.
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

-- Book: Chapter 4, Section 4.4, read-transition specialization of the
-- empty-pop before-top chain-decomposition constructor.
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

-- Book: Chapter 4, Section 4.4, epsilon-transition specialization of the
-- empty-pop before-top chain-decomposition constructor.
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

-- Book: Chapter 4, Section 4.4, a read step that starts and ends with empty
-- stack gives the matching tail-preserving PDA-to-CFG derivation.
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

-- Book: Chapter 4, Section 4.4, an epsilon step that starts and ends with
-- empty stack gives the matching tail-preserving PDA-to-CFG derivation.
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

-- Book: Chapter 4, Section 4.4, a read step that removes exactly the current
-- top stack symbol gives the matching `between` PDA-to-CFG derivation.
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

-- Book: Chapter 4, Section 4.4, an epsilon step that removes exactly the
-- current top stack symbol gives the matching `between` PDA-to-CFG derivation.
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

-- Book: Chapter 4, Section 4.4, a step that starts and ends with empty stack
-- either consumes epsilon or one input symbol, with the matching
-- tail-preserving PDA-to-CFG derivation.
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

-- Book: Chapter 4, Section 4.4, a step that removes the current stack top
-- either consumes epsilon or one input symbol, with the matching `between`
-- PDA-to-CFG derivation.
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

-- Book: Chapter 4, Section 4.4, a one-step top-pop computation that ends
-- with empty stack must have started with empty stack or a singleton stack.
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

-- Book: Chapter 4, Section 4.4, zero-step empty-stack computations give an
-- `empty p q` PDA-to-CFG derivation of the consumed input segment.
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

-- Book: Chapter 4, Section 4.4, one-step empty-stack computations give an
-- `empty p q` PDA-to-CFG derivation of the consumed input segment.
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

-- Book: Chapter 4, Section 4.4, zero- and one-step empty-stack computations
-- give an `empty p q` PDA-to-CFG derivation of the consumed input segment.
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

-- Book: Chapter 4, Section 4.4, one-step top-pop computations give a
-- `between p A q` PDA-to-CFG derivation of the consumed input segment.
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

-- Book: Chapter 4, Section 4.4, two-step empty-stack computations of a
-- top-pop PDA give an `empty p q` derivation of the consumed input segment.
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

-- Book: Chapter 4, Section 4.4, zero-, one-, and two-step empty-stack
-- computations of a top-pop PDA give an `empty p q` derivation of the
-- consumed input segment.
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

-- Book: Chapter 4, Section 4.4, zero-step accepting computations are
-- generated by the PDA-to-CFG construction.
theorem pda_to_cfg_generates_of_accepts_in_zero
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : PDA.ComputesIn M 0 (PDA.initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_acceptsIn_zero haccept hcomp

-- Book: Chapter 4, Section 4.4, first reverse-language theorem for the
-- PDA-to-CFG construction: any one-step accepting computation is generated by
-- the constructed grammar.
theorem pda_to_cfg_generates_of_accepts_in_one
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : PDA.ComputesIn M 1 (PDA.initial M w)
      { state := qf, unread := [], stack := [] }) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_acceptsIn_one haccept hcomp

-- Book: Chapter 4, Section 4.4, any two-step accepting computation of a
-- top-pop PDA is generated by the constructed PDA-to-CFG grammar.
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

-- Book: Chapter 4, Section 4.4, the zero- and one-step base cases for the
-- reverse PDA-to-CFG language direction.
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

-- Book: Chapter 4, Section 4.4, the zero-, one-, and two-step base cases for
-- the reverse PDA-to-CFG language direction.
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

-- Book: Chapter 4, Section 4.4, length-indexed PDA traces whose stack is
-- empty at every step.  This is a reusable reverse-direction branch for the
-- PDA-to-CFG construction before the full pushed-stack splitting theorem is
-- available.
def EmptyStackPDAComputesIn (M : PDA input stack state)
    (n : Nat) (p : state) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  PDA.EmptyStackComputesIn M n p sourceInput q targetInput

-- Book: Chapter 4, Section 4.4, an empty-stack trace is a bounded PDA
-- computation with empty stack at both endpoints.
theorem pda_empty_stack_trace_is_bounded_computation
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackPDAComputesIn M n p sourceInput q targetInput) :
    PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  PDA.emptyStackComputesIn_computesIn h

-- Book: Chapter 4, Section 4.4, an empty-stack trace is an ordinary PDA
-- computation with empty stack at both endpoints.
theorem pda_empty_stack_trace_is_computation
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackPDAComputesIn M n p sourceInput q targetInput) :
    PDA.Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  PDA.emptyStackComputesIn_computes h

-- Book: Chapter 4, Section 4.4, any finite empty-stack trace gives an
-- `empty p q` PDA-to-CFG derivation of the consumed input segment.
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

-- Book: Chapter 4, Section 4.4, any accepting empty-stack trace is generated
-- by the PDA-to-CFG construction.
theorem pda_to_cfg_generates_of_empty_stack_accepts_in
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptyStackPDAComputesIn M n M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_emptyStackAcceptsIn haccept hcomp

-- Book: Chapter 4, Section 4.4, grammar-aligned traces that remove an
-- explicit stack word while preserving the stack tail.  This is the
-- decomposition target for pushed stack segments in the PDA-to-CFG reverse
-- direction.
def StackSummaryPDAComputesIn (M : PDA input stack state)
    (n : Nat) (p : state) (stackWord : Word stack)
    (sourceInput : Word input) (q : state)
    (targetInput : Word input) : Prop :=
  PDA.StackSummaryComputesIn M n p stackWord sourceInput q targetInput

-- Book: Chapter 4, Section 4.4, grammar-aligned empty-stack traces that may
-- push stack words, remove them through stack-summary traces, and then
-- continue with empty stack.
def EmptySummaryPDAComputesIn (M : PDA input stack state)
    (n : Nat) (p : state) (sourceInput : Word input)
    (q : state) (targetInput : Word input) : Prop :=
  PDA.EmptySummaryComputesIn M n p sourceInput q targetInput

-- Book: Chapter 4, Section 4.4, a stack-summary trace is a bounded PDA
-- computation that removes the explicit stack prefix and preserves any tail.
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

-- Book: Chapter 4, Section 4.4, a stack-summary trace is an ordinary PDA
-- computation that removes the explicit stack prefix and preserves any tail.
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

-- Book: Chapter 4, Section 4.4, an empty-summary trace is a bounded PDA
-- computation with empty stack at both endpoints.
theorem pda_empty_summary_trace_is_bounded_computation
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputesIn M n p sourceInput q targetInput) :
    PDA.ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  PDA.emptySummaryComputesIn_computesIn h

-- Book: Chapter 4, Section 4.4, an empty-summary trace is an ordinary PDA
-- computation with empty stack at both endpoints.
theorem pda_empty_summary_trace_is_computation
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptySummaryPDAComputesIn M n p sourceInput q targetInput) :
    PDA.Computes M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] } :=
  PDA.emptySummaryComputesIn_computes h

-- Book: Chapter 4, Section 4.4, an empty-stack trace is a special case of
-- the grammar-aligned empty-summary trace relation.
theorem pda_empty_summary_trace_of_empty_stack_trace
    {M : PDA input stack state}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (h : EmptyStackPDAComputesIn M n p sourceInput q targetInput) :
    EmptySummaryPDAComputesIn M n p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_emptyStackComputesIn h

-- Book: Chapter 4, Section 4.4, a single PDA step from empty stack to empty
-- stack gives a grammar-aligned empty-summary trace.
theorem pda_empty_summary_trace_of_step_empty_stack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hstep : PDA.Step M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryPDAComputesIn M 1 p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_step_emptyStack hstep

-- Book: Chapter 4, Section 4.4, a zero-step empty-stack computation gives a
-- grammar-aligned empty-summary trace.
theorem pda_empty_summary_trace_of_computes_in_zero_empty_stack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : PDA.ComputesIn M 0
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryPDAComputesIn M 0 p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_computesIn_zero_emptyStack hcomp

-- Book: Chapter 4, Section 4.4, a one-step empty-stack computation gives a
-- grammar-aligned empty-summary trace.
theorem pda_empty_summary_trace_of_computes_in_one_empty_stack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : PDA.ComputesIn M 1
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryPDAComputesIn M 1 p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_computesIn_one_emptyStack hcomp

-- Book: Chapter 4, Section 4.4, a single top-pop PDA step gives a
-- grammar-aligned stack-summary trace for the removed top symbol.
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

-- Book: Chapter 4, Section 4.4, a one-step top-pop computation gives a
-- grammar-aligned stack-summary trace for the removed top symbol.
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

-- Book: Chapter 4, Section 4.4, any two-step empty-stack computation of a
-- top-pop PDA decomposes into the grammar-aligned empty-summary trace
-- relation.
theorem pda_empty_summary_trace_of_computes_in_two_empty_stack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PDA.PopsAtMostOne M)
    (hcomp : PDA.ComputesIn M 2
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    EmptySummaryPDAComputesIn M 2 p sourceInput q targetInput :=
  PDA.emptySummaryComputesIn_of_computesIn_two_emptyStack hnorm hcomp

-- Book: Chapter 4, Section 4.4, any zero-, one-, or two-step empty-stack
-- computation of a top-pop PDA decomposes into the grammar-aligned
-- empty-summary trace relation.
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

-- Book: Chapter 4, Section 4.4, stack-summary traces give decomposed
-- `ToCFGChainDerives` witnesses for the removed stack word.
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

-- Book: Chapter 4, Section 4.4, empty-summary traces give `empty p q`
-- PDA-to-CFG derivations of the consumed input segment.
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

-- Book: Chapter 4, Section 4.4, the zero-, one-, and two-step empty-stack
-- derivation theorem can be routed through the grammar-aligned summary trace
-- decomposition.
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

-- Book: Chapter 4, Section 4.4, accepting empty-summary traces are generated
-- by the PDA-to-CFG construction.
theorem pda_to_cfg_generates_of_empty_summary_accepts_in
    {M : PDA input stack state}
    {presentation : PDA.FinitePresentation M}
    {n : Nat} {w : Word input} {qf : state}
    (haccept : M.accept qf)
    (hcomp : EmptySummaryPDAComputesIn M n M.start w qf []) :
    w ∈ CFG.GeneratedLanguage (PDAToCFG M presentation) :=
  PDA.toCFG_generates_of_emptySummaryAcceptsIn haccept hcomp

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

-- Book: Chapter 4, Section 4.4, the concrete PDA accepts `a^n b^n`.
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

-- Book: Chapter 4, Section 4.4, the concrete PDA accepts only `a^n b^n`.
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

-- Book: Chapter 4, Section 4.4, exact language of the concrete PDA.
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

-- Book: Chapter 4, Section 4.4, a PDA for `{a^n b^m | n <= m <= 2*n}`.
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

-- Book: Chapter 4, Section 4.4, exact accepted language of the range PDA.
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

-- Book: Chapter 4, Section 4.4, representative PDA computation for
-- `{a^n b^m | n/2 <= m <= n}`: `a^3 b^2`.
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

-- Book: Chapter 4, Section 4.4, the half-range PDA accepts
-- `{a^n b^m | m <= n <= 2*m}`.
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

-- Book: Chapter 4, Section 4.4, exact accepted language of the half-range PDA.
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

-- Book: Chapter 4, Section 4.4, deterministic PDA variant for `a^n b^n`.
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

-- Book: Chapter 4, Section 4.4, exact language of the deterministic PDA.
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

-- Book: Chapter 4, Section 4.4, stack-copy PDA for `{w c w^R}`.
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

-- Book: Chapter 4, Section 4.4, exact accepted language of the stack-copy PDA.
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
