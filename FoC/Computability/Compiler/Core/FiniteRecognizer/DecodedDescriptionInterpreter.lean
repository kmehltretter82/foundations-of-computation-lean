import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode

set_option doc.verso true

/-!
# Decoded-description interpreter boundary

Finite-state construction boundary for one uniform interpreter over encoded
machine-description data.  The contract is total over source words:
malformed inputs are rejected, while canonical generated inputs are accepted
exactly when the decoded description halts within the decoded fuel.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer

/--
Finite-state decoded-description interpreter construction.
-/
def DecodedDescriptionInterpreterFinStateConstruction : Prop :=
  exists n : Nat,
  exists runner : TuringMachine MachineCodeSymbol (Fin n),
    DecodedDescriptionInterpreterTotalSpec runner

/--
Decoded-description interpreter construction over an arbitrary finite state
type.
-/
def DecodedDescriptionInterpreterConstruction : Prop :=
  exists state : Type,
  exists runner : TuringMachine MachineCodeSymbol state,
    DecodedDescriptionInterpreterTotalSpec runner

theorem decodedDescriptionInterpreterConstruction_of_finState
    (hfin : DecodedDescriptionInterpreterFinStateConstruction) :
    DecodedDescriptionInterpreterConstruction := by
  rcases hfin with ⟨n, runner, hrunner⟩
  exact ⟨Fin n, runner, hrunner⟩

theorem decodedDescriptionInterpreterFinStateConstruction_of_construction
    (hconstruction : DecodedDescriptionInterpreterConstruction) :
    DecodedDescriptionInterpreterFinStateConstruction := by
  rcases hconstruction with ⟨state, runner, hrunner⟩
  refine
    ⟨runner.statesFinite.elems.length,
      TuringMachine.indexed runner, ?_⟩
  intro tokens
  exact
    Iff.trans
      (TuringMachine.indexed_haltsOnInput_iff runner tokens)
      (hrunner tokens)

theorem decodedDescriptionInterpreterConstruction_iff_finState :
    DecodedDescriptionInterpreterConstruction <->
      DecodedDescriptionInterpreterFinStateConstruction := by
  constructor
  · exact decodedDescriptionInterpreterFinStateConstruction_of_construction
  · exact decodedDescriptionInterpreterConstruction_of_finState

/--
Remaining concrete finite-table leaf for the uniform decoded-description
interpreter.
-/
theorem decodedDescriptionInterpreterFiniteLeaf :
    DecodedDescriptionInterpreterConstruction := by
  sorry

theorem decodedDescriptionInterpreterFinStateFiniteLeaf :
    DecodedDescriptionInterpreterFinStateConstruction := by
  exact
    decodedDescriptionInterpreterFinStateConstruction_of_construction
      decodedDescriptionInterpreterFiniteLeaf

end FiniteRecognizer

end Computability
end FoC
