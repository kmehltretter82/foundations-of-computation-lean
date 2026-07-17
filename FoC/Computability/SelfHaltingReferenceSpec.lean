import FoC.Computability.DescriptionCodeValidity
import FoC.Computability.DescriptionCodeLanguages

set_option doc.verso true

/-!
# Staged reference semantics for the self-halting recognizer (M6)

This module is the M6 audit anchor. It defines a *staged reference recognizer*
for the valid self-halting language as an explicit composition of the executable
phases any finite M7 machine must implement, and proves the staged predicate
characterizes {name}`FoC.Computability.CodeSelfHaltingLanguage` exactly. This is
reference semantics — a contract each machine phase must meet — not evidence of
a finite implementation.

The four staged phases are:

1. **Decode.** Completely decode the input word {lit}`w` to a description.
2. **Validate.** Check the decoded description is well formed. Phases 1–2
   together are the executable
   {name (full := FoC.Computability.MachineDescription.descriptionCodeValidBool)}`MachineDescription.descriptionCodeValidBool`
   gate — the M4 checker's contract.
3. **Simulate.** Run the decoded description on the canonical encoding
   {name (full := FoC.Computability.MachineDescription.encodeCodeWordAsInput)}`MachineDescription.encodeCodeWordAsInput`
   of the *original* code word {lit}`w`.
4. **Accept.** Accept exactly when that simulation halts.

Phase 3 is what forbids the naive prefix-runner route: the simulated input is
the canonical encoding of the whole valid code {lit}`w`, not an independently
supplied suffix. Phase 2's exact-code gate is what forbids the
canonical-code-plus-junk false positive.
-/

namespace FoC
namespace Computability

open Languages

/--
Staged reference recognizer for the valid self-halting language: the exact-code
validity gate accepts {lit}`w`, and the description it decodes to halts on the
canonical encoding of {lit}`w` itself. The universally quantified decode is
harmless because complete decoding is functional; it names *the* decoded
description without an existential witness in the executable path.
-/
def StagedSelfHaltingReference (w : Word MachineCodeSymbol) : Prop :=
  MachineDescription.descriptionCodeValidBool w = true ∧
    (forall D : MachineDescription,
      MachineDescription.decodeDescription w = some D ->
        D.HaltsOnInput (MachineDescription.encodeCodeWordAsInput w))

/--
The staged reference recognizer accepts exactly the valid self-halting
language. This pins the M7 target: a finite machine matching all four phases
recognizes {name}`CodeSelfHaltingLanguage`, and nothing weaker (a raw prefix
runner, or one skipping the well-formedness gate) does.
-/
theorem stagedSelfHaltingReference_iff_mem (w : Word MachineCodeSymbol) :
    StagedSelfHaltingReference w <-> w ∈ CodeSelfHaltingLanguage := by
  rw [mem_codeSelfHaltingLanguage_iff]
  constructor
  · rintro ⟨hvalid, hhalt⟩
    rcases (MachineDescription.descriptionCodeValidBool_eq_true_iff w).mp hvalid
      with ⟨D, hdecode, hwell⟩
    exact ⟨D, hdecode, hwell, hhalt D hdecode⟩
  · rintro ⟨D, hdecode, hwell, hhalt⟩
    refine ⟨?_, ?_⟩
    · exact (MachineDescription.descriptionCodeValidBool_eq_true_iff w).mpr
        ⟨D, hdecode, hwell⟩
    · intro D' hdecode'
      rw [hdecode] at hdecode'
      cases hdecode'
      exact hhalt

/--
Corollary: the exact-code validity gate is a necessary phase. Every member of
the valid self-halting language passes the executable validity checker, so a
recognizer omitting phase 2 would accept invalid codes it must reject.
-/
theorem descriptionCodeValidBool_eq_true_of_mem_codeSelfHalting
    {w : Word MachineCodeSymbol} (hw : w ∈ CodeSelfHaltingLanguage) :
    MachineDescription.descriptionCodeValidBool w = true :=
  ((stagedSelfHaltingReference_iff_mem w).mpr hw).left

/-!
## Mandatory counterexamples: spec-level resolutions

The M6 audit requires that the reference recognizer reject each known
false-positive shape. Every one of these is killed by phase 2 (the exact-code
validity gate) alone, before simulation, so the M7 machine's first leaf — the
M4 checker — is exactly what forecloses them. These are specification
obligations; the M7 collision audit must additionally verify the finite machine
realizes each rejection with the right tape/head/halt behavior.
-/

/-- If phase 2 fails, the staged recognizer rejects — the gate is decisive. -/
theorem not_stagedSelfHaltingReference_of_not_descriptionCodeValid
    {w : Word MachineCodeSymbol}
    (h : ¬ MachineDescription.DescriptionCodeValid w) :
    ¬ StagedSelfHaltingReference w := by
  intro hs
  exact h ((MachineDescription.descriptionCodeValidBool_eq_true_iff w).mp hs.left)

/-- Words the gate rejects are not in the valid self-halting language. -/
theorem not_mem_codeSelfHalting_of_not_descriptionCodeValid
    {w : Word MachineCodeSymbol}
    (h : ¬ MachineDescription.DescriptionCodeValid w) :
    ¬ w ∈ CodeSelfHaltingLanguage := by
  intro hw
  exact not_stagedSelfHaltingReference_of_not_descriptionCodeValid h
    ((stagedSelfHaltingReference_iff_mem w).mpr hw)

/-- Counterexample: the empty word is rejected. -/
theorem not_stagedSelfHaltingReference_nil :
    ¬ StagedSelfHaltingReference ([] : Word MachineCodeSymbol) :=
  not_stagedSelfHaltingReference_of_not_descriptionCodeValid
    MachineDescription.not_descriptionCodeValid_nil

/-- Counterexample: a lone header (incomplete code) is rejected. -/
theorem not_stagedSelfHaltingReference_header :
    ¬ StagedSelfHaltingReference ([MachineCodeSymbol.header] :
      Word MachineCodeSymbol) :=
  not_stagedSelfHaltingReference_of_not_descriptionCodeValid
    MachineDescription.not_descriptionCodeValid_header

/-- Counterexample: a canonical code with trailing junk is rejected. This is
the prefix-runner false positive that the exact-code gate forecloses. -/
theorem not_stagedSelfHaltingReference_encodeDescription_append
    (D : MachineDescription) {junk : Word MachineCodeSymbol}
    (hjunk : junk ≠ []) :
    ¬ StagedSelfHaltingReference
      (List.append (MachineDescription.encodeDescription D) junk) :=
  not_stagedSelfHaltingReference_of_not_descriptionCodeValid
    (MachineDescription.not_descriptionCodeValid_encodeDescription_append_of_ne_nil
      D hjunk)

/-- Counterexample: a raw-decodable but non-well-formed canonical code is
rejected by the well-formedness half of phase 2. -/
theorem not_stagedSelfHaltingReference_encodeDescription_of_not_wellFormed
    {D : MachineDescription} (hnot : ¬ D.WellFormed) :
    ¬ StagedSelfHaltingReference (MachineDescription.encodeDescription D) :=
  not_stagedSelfHaltingReference_of_not_descriptionCodeValid
    (MachineDescription.not_descriptionCodeValid_encodeDescription_of_not_wellFormed
      hnot)

/-!
## Route A feasibility bridge

Route A composes three phases: an exact-code validity gate, a source-preserving
duplicator {lit}`w ↦ w ++ w`, and the existing closed, unconditional
universal-prefix runner ({lit}`concrete_universal_prefix_runner_construction`),
which recognizes {name (full := FoC.Computability.MachineDescription.CodePrefixAccepts)}`MachineDescription.CodePrefixAccepts`.

The next theorem proves this decomposition is correct at the specification
level: on the valid subset, self-halting membership is exactly the prefix
runner accepting the self-appended word. This is why route A is collision-free.
The exact-code gate is what makes {lit}`w ++ w` safe — for a valid
{lit}`w = encodeDescription D` the self-delimiting prefix decoder splits it
cleanly into {lit}`D` and suffix {lit}`w`
({name (full := FoC.Computability.MachineDescription.codePrefixAccepts_encodeDescription_append_iff)}`MachineDescription.codePrefixAccepts_encodeDescription_append_iff`),
so no trailing-junk word ever reaches the runner. The runner then simulates
{lit}`D` on {lit}`encodeCodeWordAsInput w`, which is precisely phase 3 of the
reference recognizer.
-/
theorem mem_codeSelfHalting_iff_valid_and_codePrefixAccepts_selfAppend
    (w : Word MachineCodeSymbol) :
    w ∈ CodeSelfHaltingLanguage <->
      MachineDescription.DescriptionCodeValid w ∧
        MachineDescription.CodePrefixAccepts (List.append w w) := by
  rw [mem_codeSelfHaltingLanguage_iff]
  constructor
  · rintro ⟨D, hdecode, hwell, hhalt⟩
    have hw : w = MachineDescription.encodeDescription D :=
      MachineDescription.decodeDescription_eq_some_encodeDescription hdecode
    subst hw
    exact ⟨⟨D, hdecode, hwell⟩,
      (MachineDescription.codePrefixAccepts_encodeDescription_append_iff D
        (MachineDescription.encodeDescription D)).mpr hhalt⟩
  · rintro ⟨⟨D, hdecode, hwell⟩, hpref⟩
    have hw : w = MachineDescription.encodeDescription D :=
      MachineDescription.decodeDescription_eq_some_encodeDescription hdecode
    subst hw
    exact ⟨D, hdecode, hwell,
      (MachineDescription.codePrefixAccepts_encodeDescription_append_iff D
        (MachineDescription.encodeDescription D)).mp hpref⟩

end Computability
end FoC
