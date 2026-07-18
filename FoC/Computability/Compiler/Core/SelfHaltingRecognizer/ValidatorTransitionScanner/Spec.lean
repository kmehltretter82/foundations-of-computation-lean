import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorHeaderParser
import FoC.Computability.Compiler.Core.TransitionTableChecks

set_option doc.verso true

/-!
# Exact-code validator: counted transition scan and state-bound contract

This module pins M4 leaf 3 before its finite table is built.  The leaf starts
at the exact header-parser handoff, parses precisely the declared number of
transition records, checks every state-bound clause needed by
{name (full := FoC.Computability.MachineDescription.WellFormed)}`MachineDescription.WellFormed`,
and halts at the first suffix token after restoring all temporary markers.

The bounds are not limited to transition endpoints.  They also include
{lit}`0 < stateCount`, {lit}`start < stateCount`, and
{lit}`halt < stateCount`; omitting these would make the validator contract
strictly weaker than description well-formedness.

The intended backend remains one physical Boolean tape.  The source and target
are already exact one-tape composition boundaries, while a three-logical-tape
route would additionally require a new indexed materializer and an exact
projector back to this boundary.  Leaf 3 instead follows the existing
code-symbol transition parser's marker/shuttle algorithm with reserved invalid
four-bit tokens, restoring them before its handoff.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

/-!
## Semantic acceptance currency
-/

/-- Boolean form of every non-determinism state-bound clause. -/
def validatorStateBoundsBool
    (stateCount start halt : Nat)
    (transitions : List TransitionDescription) : Bool :=
  decide (0 < stateCount) &&
    decide (start < stateCount) &&
    decide (halt < stateCount) &&
    transitions.all (transitionWellFormedBool stateCount)

theorem validatorStateBoundsBool_eq_true_iff
    (stateCount start halt : Nat)
    (transitions : List TransitionDescription) :
    validatorStateBoundsBool stateCount start halt transitions = true <->
      0 < stateCount ∧
        start < stateCount ∧
        halt < stateCount ∧
        forall t : TransitionDescription,
          t ∈ transitions ->
            TransitionDescription.WellFormed stateCount t := by
  simp [validatorStateBoundsBool, transitionWellFormedBool,
    TransitionDescription.WellFormed, and_assoc]

/--
Semantic language of the counted scanner at the header-parser handoff.  The
suffix is deliberately arbitrary; exact suffix emptiness is leaf 4.
-/
def ValidatorTransitionScanAccepts
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) : Prop :=
  exists transitions : List TransitionDescription,
  exists suffix : Word MachineCodeSymbol,
    decodeTransitions transitionCount tokens = some (transitions, suffix) ∧
      validatorStateBoundsBool stateCount start halt transitions = true

theorem validatorTransitionScanAccepts_iff_exists_encoded
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    ValidatorTransitionScanAccepts
        stateCount start halt transitionCount tokens <->
      exists transitions : List TransitionDescription,
      exists suffix : Word MachineCodeSymbol,
        transitionCount = transitions.length ∧
          tokens = encodeTransitionsAppend transitions suffix ∧
          validatorStateBoundsBool
            stateCount start halt transitions = true := by
  constructor
  · rintro ⟨transitions, suffix, hdecode, hbounds⟩
    rcases decodeTransitions_eq_some_encodeTransitionsAppend hdecode with
      ⟨hcount, htokens⟩
    exact ⟨transitions, suffix, hcount, htokens, hbounds⟩
  · rintro ⟨transitions, suffix, hcount, htokens, hbounds⟩
    subst transitionCount
    subst tokens
    exact
      ⟨transitions, suffix,
        decodeTransitions_encodeTransitions_append transitions suffix,
        hbounds⟩

/-!
## Exact physical composition boundaries
-/

/-- Leaf-3 source: the exact header-parser handoff at the first row token. -/
def validatorTransitionScannerStartTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) : Tape Bool :=
  validatorHeaderFieldsHandoffTape
    stateCount start halt transitionCount tokens

/-- Code-symbol prefix lying left of the scanner's final head position. -/
def validatorTransitionScannerPrefix
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription) : Word MachineCodeSymbol :=
  List.append
    (validatorHeaderFieldsPrefix
      stateCount start halt transitionCount)
    (encodeTransitions transitions)

/--
Exact restored leaf-3 handoff.  All header fields and counted transition rows
are preserved to the left; the arbitrary suffix begins under the head.
-/
def validatorTransitionScannerHandoffTape
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Tape Bool :=
  tapeAtCells
    (List.append
      (((encodeCodeWordAsInput
        (validatorTransitionScannerPrefix
          stateCount start halt transitionCount transitions)).reverse).map
            some)
      [none])
    (List.append ((encodeCodeWordAsInput suffix).map some) [none])

theorem validatorTransitionScannerStartTape_encoded
    (stateCount start halt transitionCount : Nat)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    validatorTransitionScannerStartTape
        stateCount start halt transitionCount
        (encodeTransitionsAppend transitions suffix) =
      validatorHeaderFieldsHandoffTape
        stateCount start halt transitionCount
        (encodeTransitionsAppend transitions suffix) := by
  rfl

/-!
## Decomposition-collision audit

The decoded row count determines one unique row list and suffix.  Therefore a
single canonical source cannot demand two inequivalent leaf-3 handoffs through
different counted decompositions.
-/

theorem validatorTransitionScanner_decomposition_unique
    {transitionCount : Nat} {tokens : Word MachineCodeSymbol}
    {transitions₁ transitions₂ : List TransitionDescription}
    {suffix₁ suffix₂ : Word MachineCodeSymbol}
    (h₁ : decodeTransitions transitionCount tokens =
      some (transitions₁, suffix₁))
    (h₂ : decodeTransitions transitionCount tokens =
      some (transitions₂, suffix₂)) :
    transitions₁ = transitions₂ ∧ suffix₁ = suffix₂ := by
  rw [h₁] at h₂
  have hpairs := Prod.mk.inj (Option.some.inj h₂)
  exact hpairs

theorem encodeTransitionsAppend_inj_of_count
    {transitionCount : Nat}
    {transitions₁ transitions₂ : List TransitionDescription}
    {suffix₁ suffix₂ : Word MachineCodeSymbol}
    (hlength₁ : transitionCount = transitions₁.length)
    (hlength₂ : transitionCount = transitions₂.length)
    (hcode :
      encodeTransitionsAppend transitions₁ suffix₁ =
        encodeTransitionsAppend transitions₂ suffix₂) :
    transitions₁ = transitions₂ ∧ suffix₁ = suffix₂ := by
  have hdecode₁ :
      decodeTransitions transitionCount
          (encodeTransitionsAppend transitions₁ suffix₁) =
        some (transitions₁, suffix₁) := by
    rw [hlength₁]
    exact decodeTransitions_encodeTransitions_append transitions₁ suffix₁
  have hdecode₂ :
      decodeTransitions transitionCount
          (encodeTransitionsAppend transitions₂ suffix₂) =
        some (transitions₂, suffix₂) := by
    rw [hlength₂]
    exact decodeTransitions_encodeTransitions_append transitions₂ suffix₂
  rw [hcode, hdecode₂] at hdecode₁
  have hpairs := Prod.mk.inj (Option.some.inj hdecode₁)
  exact ⟨hpairs.1.symm, hpairs.2.symm⟩

end SelfHaltingRecognizer
end Computability
end FoC
