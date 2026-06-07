import FoC.Computability.Program
import FoC.Grammars.GeneralGrammar

set_option doc.verso true

/-!
# General grammar recognizers

## Derivations as staged recognition

Finite derivations of a general grammar are finite-stage evidence.  This file
turns the length-indexed derivation relation from
{module}`FoC.Grammars.GeneralGrammar` into an acceptance trace and a staged
program recognizer.

The construction stays at the staged-program layer.  Compiling this recognizer
to a concrete one-tape Turing machine is the later universal/interpreter
development.

## Book coordinates

Used by:
- Chapter 5, Section 5.2: the direction from finite general grammars to
  recursively enumerable behavior.
-/

namespace FoC
namespace Computability

open Languages
open Grammars

/-!
# Grammar derivation traces
-/

def GeneralGrammarDerivationTrace
    (G : GeneralGrammar terminal nonterminal)
    (w : Word terminal) (n : Nat) : Prop :=
  GeneralGrammar.DerivesIn G n
    [Symbol.nonterminal G.start]
    (SententialForm.terminalWord w)

theorem generalGrammar_derivationTrace_acceptance
    (G : GeneralGrammar terminal nonterminal) :
    AcceptanceTrace
      (GeneralGrammarDerivationTrace G)
      (GeneralGrammar.GeneratedLanguage G) := by
  intro w
  constructor
  · intro h
    cases h with
    | intro _ hn =>
        exact GeneralGrammar.derivesIn_derives hn
  · intro h
    exact GeneralGrammar.derives_derivesIn h

noncomputable def GeneralGrammarRecognizerProgram
    (G : GeneralGrammar terminal nonterminal) :
    StagedProgram terminal Unit :=
  by
    classical
    exact
      { run := fun w n =>
          if GeneralGrammarDerivationTrace G w n then some [] else none }

theorem generalGrammarRecognizerProgram_run_of_trace
    {G : GeneralGrammar terminal nonterminal}
    {w : Word terminal} {n : Nat}
    (h : GeneralGrammarDerivationTrace G w n) :
    (GeneralGrammarRecognizerProgram G).run w n = some [] := by
  classical
  simp [GeneralGrammarRecognizerProgram, h]
  rfl

theorem generalGrammarRecognizerProgram_acceptsLanguage
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptsLanguage
      (GeneralGrammarRecognizerProgram G)
      (GeneralGrammar.GeneratedLanguage G) := by
  intro w
  constructor
  · intro h
    cases h with
    | intro n hn =>
        by_cases htrace : GeneralGrammarDerivationTrace G w n
        · exact (generalGrammar_derivationTrace_acceptance G w).mp
            (Exists.intro n htrace)
        · simp [GeneralGrammarRecognizerProgram, htrace] at hn
  · intro h
    cases (generalGrammar_derivationTrace_acceptance G w).mpr h with
    | intro n hn =>
        exact Exists.intro n
          (generalGrammarRecognizerProgram_run_of_trace hn)

theorem generalGrammar_generatedLanguage_programAcceptable
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptable (GeneralGrammar.GeneratedLanguage G) :=
  Exists.intro (GeneralGrammarRecognizerProgram G)
    (generalGrammarRecognizerProgram_acceptsLanguage G)

theorem generalGrammar_generated_programAcceptable
    {L : Language terminal}
    (h : GeneralGrammar.Generated L) :
    ProgramAcceptable L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          exact programAcceptable_of_equal
            (generalGrammar_generatedLanguage_programAcceptable G) hG

theorem finiteProductionGenerated_programAcceptable
    {L : Language terminal}
    (h : GeneralGrammar.FiniteProductionGenerated L) :
    ProgramAcceptable L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          exact programAcceptable_of_equal
            (generalGrammar_generatedLanguage_programAcceptable G)
            hG.right

theorem generalGrammar_generatedLanguage_recursivelyEnumerable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    (G : GeneralGrammar terminal nonterminal) :
    RecursivelyEnumerable (GeneralGrammar.GeneratedLanguage G) :=
  recursivelyEnumerable_of_programCompiler hcompile
    (generalGrammar_generatedLanguage_programAcceptable G)

theorem generalGrammar_generated_recursivelyEnumerable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    {L : Language terminal}
    (h : GeneralGrammar.Generated L) :
    RecursivelyEnumerable L :=
  recursivelyEnumerable_of_programCompiler hcompile
    (generalGrammar_generated_programAcceptable h)

theorem finiteProductionGenerated_recursivelyEnumerable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    {L : Language terminal}
    (h : GeneralGrammar.FiniteProductionGenerated L) :
    RecursivelyEnumerable L :=
  recursivelyEnumerable_of_programCompiler hcompile
    (finiteProductionGenerated_programAcceptable h)

end Computability
end FoC
