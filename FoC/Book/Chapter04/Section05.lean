import FoC.Grammars.CFL

namespace FoC
namespace Book
namespace Chapter04
namespace Section05

/-!
Book: Chapter 4, Section 4.5, Non-context-free Languages.
-/

open Languages
open Grammars

-- Book: Chapter 4, Section 4.5, pumping-lemma decomposition vocabulary.
def CFLPumpingDecomposition (L : Language terminal) (K : Nat) (w : Word terminal) :
    Prop :=
  CFL.PumpingDecomposition L K w

-- Book: Chapter 4, Section 4.5, pumping length vocabulary.
def CFLPumpingLength (L : Language terminal) (K : Nat) : Prop :=
  CFL.PumpingLength L K

-- Book: Chapter 4, Section 4.5, pumping property vocabulary.
def CFLHasPumpingProperty (L : Language terminal) : Prop :=
  CFL.HasPumpingProperty L

-- Book: Chapter 4, Section 4.5, the original word is the n = 1 pumped word.
theorem pumping_decomposition_original_word_mem {L : Language terminal}
    {K : Nat} {w : Word terminal}
    (h : CFLPumpingDecomposition L K w) : w ∈ L :=
  CFL.pumping_decomposition_original_word_mem h

-- Book: Chapter 4, Section 4.5, contrapositive schema for pumping arguments.
theorem not_context_free_of_no_pumping_property {L : Language terminal}
    (pumpingLemma : CFL.PumpingLemmaConclusion L)
    (hNoPump : ¬ CFLHasPumpingProperty L) :
    ¬ CFL.ContextFreeLanguage L :=
  CFL.not_context_free_of_no_pumping_property pumpingLemma hNoPump

/-!
The full context-free pumping lemma and the non-context-free proofs for
`a^n b^n c^n` and `{ww}` require parse-tree height and finite-branching
infrastructure.  This section records the quantified property and the
contrapositive proof schema without treating the pumping lemma itself as a
proved theorem.
-/

end Section05
end Chapter04
end Book
end FoC
