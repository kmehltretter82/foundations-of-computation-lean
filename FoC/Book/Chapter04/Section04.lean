import FoC.Grammars.PDA

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

-- Book: Chapter 4, Section 4.4, accepted language of a PDA.
def PDAAcceptedLanguage (M : PDA input stack state) : Language input :=
  PDA.AcceptedLanguage M

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

end Section04
end Chapter04
end Book
end FoC
