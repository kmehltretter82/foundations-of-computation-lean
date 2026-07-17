import FoC.Computability.Compiler.DescriptionExecution
import FoC.Computability.DescriptionLanguages

set_option doc.verso true

/-!
# Finite description-backed code languages

This module fixes the canonical finite-description currency for recognizing
and deciding languages over
{name (full := FoC.Computability.MachineCodeSymbol)}`MachineCodeSymbol`. It extends the
halting-only decoded languages in
{module}`FoC.Computability.DescriptionLanguages` with normalized-output and
halt-stability requirements from the description execution layer.

## Contracts

A recognizer is one concrete well-formed description whose halting behavior
agrees with the language on every canonical block encoding. A decider is also
halt-stable and returns two distinct one-bit normalized outputs.

The answer symbols are explicit so complementing a decider swaps their roles
without changing its finite transition table. The conventional orientation is
{lit}`reject = false` and {lit}`accept = true`.

The input contract deliberately uses
{name (full := FoC.Computability.MachineDescription.encodeCodeWordAsInput)}`MachineDescription.encodeCodeWordAsInput`, which encodes each code
symbol as a four-bit block. It is not the pointwise {lit}`EncodeWord` of a
single-symbol map, so no generic
{name (full := FoC.Computability.StoppedTuringDecidable)}`StoppedTuringDecidable` projection is
claimed here.
-/

namespace FoC
namespace Computability

open Languages

/-- A well-formed finite description recognizes a code-symbol language. -/
def DescriptionRecognizesCodeLanguage
    (D : MachineDescription) (L : Language MachineCodeSymbol) : Prop :=
  D.WellFormed ∧
    Language.Equal (MachineDescription.EncodedInputLanguage D) L

/-- A code-symbol language has a well-formed finite-description recognizer. -/
def DescriptionRecognizableCodeLanguage
    (L : Language MachineCodeSymbol) : Prop :=
  exists D : MachineDescription, DescriptionRecognizesCodeLanguage D L

/--
A halt-stable finite description decides a code-symbol language using two
distinct normalized one-bit answers.
-/
def StoppedDescriptionDecidesCodeLanguage
    (D : MachineDescription) (reject accept : Bool)
    (L : Language MachineCodeSymbol) : Prop :=
  D.HaltTransitionFree ∧ D.WellFormed ∧ reject ≠ accept ∧
    forall w : Word MachineCodeSymbol,
      (w ∈ L ->
        D.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput w) [accept]) ∧
      (¬ w ∈ L ->
        D.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput w) [reject])

/-- A code-symbol language has a halt-stable finite-description decider. -/
def DescriptionDecidableCodeLanguage
    (L : Language MachineCodeSymbol) : Prop :=
  exists D : MachineDescription, exists reject accept : Bool,
    StoppedDescriptionDecidesCodeLanguage D reject accept L

namespace DescriptionRecognizesCodeLanguage

theorem wellFormed
    {D : MachineDescription} {L : Language MachineCodeSymbol}
    (h : DescriptionRecognizesCodeLanguage D L) : D.WellFormed := by
  exact h.left

theorem correct
    {D : MachineDescription} {L : Language MachineCodeSymbol}
    (h : DescriptionRecognizesCodeLanguage D L)
    (w : Word MachineCodeSymbol) :
    D.HaltsOnInput (MachineDescription.encodeCodeWordAsInput w) <->
      w ∈ L := by
  exact h.right w

theorem of_equal
    {D : MachineDescription} {L K : Language MachineCodeSymbol}
    (h : DescriptionRecognizesCodeLanguage D L)
    (hLK : Language.Equal L K) :
    DescriptionRecognizesCodeLanguage D K := by
  refine ⟨h.wellFormed, ?_⟩
  intro w
  exact (h.right w).trans (hLK w)

end DescriptionRecognizesCodeLanguage

theorem descriptionRecognizableCodeLanguage_of_equal
    {L K : Language MachineCodeSymbol}
    (h : DescriptionRecognizableCodeLanguage L)
    (hLK : Language.Equal L K) :
    DescriptionRecognizableCodeLanguage K := by
  rcases h with ⟨D, hD⟩
  exact ⟨D, hD.of_equal hLK⟩

namespace StoppedDescriptionDecidesCodeLanguage

theorem haltTransitionFree
    {D : MachineDescription} {reject accept : Bool}
    {L : Language MachineCodeSymbol}
    (h : StoppedDescriptionDecidesCodeLanguage D reject accept L) :
    D.HaltTransitionFree := by
  exact h.left

theorem wellFormed
    {D : MachineDescription} {reject accept : Bool}
    {L : Language MachineCodeSymbol}
    (h : StoppedDescriptionDecidesCodeLanguage D reject accept L) :
    D.WellFormed := by
  exact h.right.left

theorem answers_ne
    {D : MachineDescription} {reject accept : Bool}
    {L : Language MachineCodeSymbol}
    (h : StoppedDescriptionDecidesCodeLanguage D reject accept L) :
    reject ≠ accept := by
  exact h.right.right.left

theorem correct
    {D : MachineDescription} {reject accept : Bool}
    {L : Language MachineCodeSymbol}
    (h : StoppedDescriptionDecidesCodeLanguage D reject accept L)
    (w : Word MachineCodeSymbol) :
    (w ∈ L ->
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput w) [accept]) ∧
    (¬ w ∈ L ->
      D.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput w) [reject]) := by
  exact h.right.right.right w

theorem output_eq_of_haltsWithOutput
    {D : MachineDescription} {reject accept : Bool}
    {L : Language MachineCodeSymbol}
    (h : StoppedDescriptionDecidesCodeLanguage D reject accept L)
    {w : Word MachineCodeSymbol} {out : Word Bool}
    (hout : D.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput w) out) :
    (w ∈ L -> out = [accept]) ∧
      (¬ w ∈ L -> out = [reject]) := by
  constructor
  · intro hw
    exact MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
      h.haltTransitionFree hout ((h.correct w).left hw)
  · intro hw
    exact MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
      h.haltTransitionFree hout ((h.correct w).right hw)

theorem of_equal
    {D : MachineDescription} {reject accept : Bool}
    {L K : Language MachineCodeSymbol}
    (h : StoppedDescriptionDecidesCodeLanguage D reject accept L)
    (hLK : Language.Equal L K) :
    StoppedDescriptionDecidesCodeLanguage D reject accept K := by
  refine ⟨h.haltTransitionFree, h.wellFormed, h.answers_ne, ?_⟩
  intro w
  constructor
  · intro hw
    exact (h.correct w).left ((hLK w).mpr hw)
  · intro hw
    apply (h.correct w).right
    intro hwL
    exact hw ((hLK w).mp hwL)

theorem complement
    {D : MachineDescription} {reject accept : Bool}
    {L : Language MachineCodeSymbol}
    (h : StoppedDescriptionDecidesCodeLanguage D reject accept L) :
    StoppedDescriptionDecidesCodeLanguage
      D accept reject (Language.Compl L) := by
  classical
  refine ⟨h.haltTransitionFree, h.wellFormed, h.answers_ne.symm, ?_⟩
  intro w
  constructor
  · exact (h.correct w).right
  · intro hw
    apply (h.correct w).left
    apply Classical.byContradiction
    intro hn
    exact hw hn

end StoppedDescriptionDecidesCodeLanguage

theorem descriptionDecidableCodeLanguage_of_equal
    {L K : Language MachineCodeSymbol}
    (h : DescriptionDecidableCodeLanguage L)
    (hLK : Language.Equal L K) :
    DescriptionDecidableCodeLanguage K := by
  rcases h with ⟨D, reject, accept, hD⟩
  exact ⟨D, reject, accept, hD.of_equal hLK⟩

theorem descriptionDecidableCodeLanguage_complement
    {L : Language MachineCodeSymbol}
    (h : DescriptionDecidableCodeLanguage L) :
    DescriptionDecidableCodeLanguage (Language.Compl L) := by
  rcases h with ⟨D, reject, accept, hD⟩
  exact ⟨D, accept, reject, hD.complement⟩

end Computability
end FoC
