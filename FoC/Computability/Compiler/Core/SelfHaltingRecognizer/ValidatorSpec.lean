import FoC.Computability.DescriptionCodeValidity
import FoC.Computability.Compiler.UniversalAndRanges.Basic

set_option doc.verso true

/-!
# Exact-code validator: specification and finite-check decomposition (M4 / M7 route-A phase 1)

This module is the specification anchor for the exact-code validator — route-A
phase 1 of the self-halting recognizer (M6 audit
{lit}`docs/SELF_HALTING_RECOGNIZER_M6_AUDIT.md`), and the one route-A phase
without a closed reusable finite-machine leaf. It pins exactly what the
validator machine must compute by decomposing the semantic target
{name (full := FoC.Computability.MachineDescription.DescriptionCodeValid)}`MachineDescription.DescriptionCodeValid`
into three finite-checkable conditions, reusing the existing closed prefix
parser for the first.

## What the machine must check

A word {lit}`w` is a valid complete well-formed code exactly when:

1. **it prefix-decodes** — {lit}`decodeDescriptionPrefix w = some (D, suffix)` for
   some description {lit}`D`; the existing finite parser
   {name (full := FoC.Computability.CodePrefixParserNormalizerMachineConstruction)}`CodePrefixParserNormalizerMachineConstruction`
   already recognizes this (its normalize-success characterization is
   {name (full := FoC.Computability.codePrefixParser_normalize_success_iff)}`codePrefixParser_normalize_success_iff`);
2. **the suffix is empty** — no trailing junk, so the decode is complete
   ({name (full := FoC.Computability.MachineDescription.decodeDescription_eq_some_iff_decodeDescriptionPrefix_eq_some_nil)}`MachineDescription.decodeDescription_eq_some_iff_decodeDescriptionPrefix_eq_some_nil`);
   and
3. **the decoded description is well formed** — checked on the tape against the
   executable {lit}`machineDescriptionWellFormedBool`.

Conditions 2 and 3 are the genuinely new finite-machine work. Condition 1 is a
closed reusable leaf.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages

/--
Finite-check decomposition of exact-code validity: {lit}`w` decodes as a
*complete* code (empty prefix suffix) to a well-formed description. This is the
contract the validator machine realizes — the prefix parser supplies the decode,
and the machine additionally checks suffix-emptiness and well-formedness.
-/
theorem descriptionCodeValid_iff_prefix_nil_wellFormed
    (w : Word MachineCodeSymbol) :
    MachineDescription.DescriptionCodeValid w <->
      exists D : MachineDescription,
        MachineDescription.decodeDescriptionPrefix w = some (D, []) ∧
          D.WellFormed := by
  constructor
  · rintro ⟨D, hdecode, hwell⟩
    exact ⟨D,
      (MachineDescription.decodeDescription_eq_some_iff_decodeDescriptionPrefix_eq_some_nil).mp
        hdecode, hwell⟩
  · rintro ⟨D, hprefix, hwell⟩
    exact ⟨D,
      (MachineDescription.decodeDescription_eq_some_iff_decodeDescriptionPrefix_eq_some_nil).mpr
        hprefix, hwell⟩

/--
The executable validity oracle in machine-check form: {lit}`w` is valid exactly
when the prefix decode is complete and well formed. This is the Boolean the
validator machine must output {lit}`true` on.
-/
theorem descriptionCodeValidBool_eq_true_iff_prefix_nil_wellFormed
    (w : Word MachineCodeSymbol) :
    MachineDescription.descriptionCodeValidBool w = true <->
      exists D : MachineDescription,
        MachineDescription.decodeDescriptionPrefix w = some (D, []) ∧
          D.WellFormed :=
  (MachineDescription.descriptionCodeValidBool_eq_true_iff w).trans
    (descriptionCodeValid_iff_prefix_nil_wellFormed w)

/-!
# Validator machine target and required consumers

The validator frontier is a halt-stable finite description deciding
{lit}`DescriptionCodeValid` with two distinct normalized Boolean answers and no
halt-state transition — the {lit}`StoppedDescriptionDecidesCodeLanguage`
contract instantiated at the validity language. Per repository policy the shared
validator API needs two current compiling consumers in distinct families before
promotion (M6 audit §6):

1. the self-halting recognizer (validator as route-A phase-1 leaf); and
2. the standalone theorem that valid codes form a decidable code language.

The language the validator decides. Membership is exactly exact-code validity.
-/
def ValidCodeLanguage : Language MachineCodeSymbol :=
  fun w => MachineDescription.DescriptionCodeValid w

theorem mem_validCodeLanguage_iff (w : Word MachineCodeSymbol) :
    w ∈ ValidCodeLanguage <-> MachineDescription.DescriptionCodeValid w :=
  Iff.rfl

/--
Target predicate (M4 frontier, to be discharged by the finite construction): a
halt-stable finite description decides the valid-code language with distinct
normalized Boolean answers. Stated here as the exact obligation the validator
machine must meet; consumed by the self-halting recognizer and the standalone
valid-code decidability theorem.
-/
def ExactCodeValidatorConstruction : Prop :=
  DescriptionDecidableCodeLanguage ValidCodeLanguage

end SelfHaltingRecognizer
end Computability
end FoC
