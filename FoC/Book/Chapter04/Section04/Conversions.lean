import FoC.Book.Chapter04.Section04.Basic

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

open Languages
open Grammars

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

end Section04
end Chapter04
end Book
end FoC
