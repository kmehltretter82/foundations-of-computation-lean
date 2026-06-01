import FoC.Grammars.GeneralGrammar

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
Book: Chapter 4, Section 4.6, General Grammars.
-/

open Languages
open Grammars

-- Book: Chapter 4, Section 4.6, one general-grammar step is a derivation.
theorem general_yields_implies_derives {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : GeneralGrammar.Yields G x y) :
    GeneralGrammar.Derives G x y :=
  GeneralGrammar.yields_derives h

-- Book: Chapter 4, Section 4.6, derivations are transitive.
theorem general_derives_transitive {G : GeneralGrammar terminal nonterminal}
    {x y z : SententialForm terminal nonterminal}
    (hxy : GeneralGrammar.Derives G x y) (hyz : GeneralGrammar.Derives G y z) :
    GeneralGrammar.Derives G x z :=
  GeneralGrammar.derives_trans hxy hyz

-- Book: Chapter 4, Section 4.6, every CFG rule is a valid general-grammar rule.
def GeneralGrammarFromCFG (G : CFG terminal nonterminal) :
    GeneralGrammar terminal nonterminal :=
  GeneralGrammar.FromCFG G

-- Book: Chapter 4, Section 4.6, CFG derivations embed in general grammars.
theorem cfg_derivation_is_general_derivation {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : CFG.Derives G x y) :
    GeneralGrammar.Derives (GeneralGrammar.FromCFG G) x y :=
  GeneralGrammar.cfg_derives_embeds h

-- Book: Chapter 4, Section 4.6, CFG-generated words are general-grammar generated.
theorem cfg_generated_word_is_general_generated (G : CFG terminal nonterminal)
    {w : Word terminal} (h : w ∈ CFG.GeneratedLanguage G) :
    w ∈ GeneralGrammar.GeneratedLanguage (GeneralGrammar.FromCFG G) :=
  GeneralGrammar.cfg_generated_language_embeds G h

end Section06
end Chapter04
end Book
end FoC
