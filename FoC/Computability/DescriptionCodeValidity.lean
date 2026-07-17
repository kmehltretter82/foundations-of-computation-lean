import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.DescriptionLanguages

set_option doc.verso true

/-!
# Valid finite-description codes

This module connects complete description decoding with the executable
well-formedness checker. Raw parsing remains available through
{name (full := FoC.Computability.MachineDescription.decodeDescription)}`MachineDescription.decodeDescription` and
{name (full := FoC.Computability.MachineDescription.RawCodeAccepts)}`MachineDescription.RawCodeAccepts`; the canonical
{name (full := FoC.Computability.MachineDescription.DescriptionCodeValid)}`MachineDescription.DescriptionCodeValid` and
{name (full := FoC.Computability.MachineDescription.CodeAccepts)}`MachineDescription.CodeAccepts` relations require well-formed decoded
descriptions.
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

/-- Executably check complete decoding followed by description well-formedness. -/
def descriptionCodeValidBool
    (tokens : Word MachineCodeSymbol) : Bool :=
  match decodeDescription tokens with
  | none => false
  | some D => machineDescriptionWellFormedBool D

/-- With a known complete decode, validity is exactly decoded well-formedness. -/
theorem descriptionCodeValid_iff_of_decodeDescription_eq_some
    {tokens : Word MachineCodeSymbol} {D : MachineDescription}
    (hdecode : decodeDescription tokens = some D) :
    DescriptionCodeValid tokens <-> D.WellFormed := by
  constructor
  · intro h
    rcases h with ⟨decoded, hdecoded, hwell⟩
    rw [hdecode] at hdecoded
    cases hdecoded
    exact hwell
  · intro h
    exact ⟨D, hdecode, h⟩

/-- The executable complete-code checker is sound and complete. -/
theorem descriptionCodeValidBool_eq_true_iff
    (tokens : Word MachineCodeSymbol) :
    descriptionCodeValidBool tokens = true <->
      DescriptionCodeValid tokens := by
  cases hdecode : decodeDescription tokens with
  | none =>
      simp [descriptionCodeValidBool, hdecode, DescriptionCodeValid]
  | some D =>
      simp only [descriptionCodeValidBool, hdecode]
      exact (machineDescriptionWellFormedBool_eq_true_iff D).trans
        (descriptionCodeValid_iff_of_decodeDescription_eq_some hdecode).symm

/-- Valid words are exactly canonical encodings of well-formed descriptions. -/
theorem descriptionCodeValid_iff_exists_encodeDescription_wellFormed
    (tokens : Word MachineCodeSymbol) :
    DescriptionCodeValid tokens <->
      exists D : MachineDescription,
        tokens = encodeDescription D ∧ D.WellFormed := by
  constructor
  · intro h
    rcases h with ⟨D, hdecode, hwell⟩
    exact ⟨D, decodeDescription_eq_some_encodeDescription hdecode, hwell⟩
  · intro h
    rcases h with ⟨D, rfl, hwell⟩
    exact (descriptionCodeValid_encodeDescription_iff D).mpr hwell

/-- Failed complete decoding rules out valid-code membership. -/
theorem not_descriptionCodeValid_of_decodeDescription_eq_none
    {tokens : Word MachineCodeSymbol}
    (hdecode : decodeDescription tokens = none) :
    ¬ DescriptionCodeValid tokens := by
  intro h
  rcases h with ⟨D, hdecoded, _⟩
  rw [hdecode] at hdecoded
  cases hdecoded

/-- The empty word is not a complete description code. -/
theorem not_descriptionCodeValid_nil :
    ¬ DescriptionCodeValid ([] : Word MachineCodeSymbol) :=
  not_descriptionCodeValid_of_decodeDescription_eq_none rfl

/-- A lone header is an incomplete description code. -/
theorem not_descriptionCodeValid_header :
    ¬ DescriptionCodeValid ([MachineCodeSymbol.header] :
      Word MachineCodeSymbol) :=
  not_descriptionCodeValid_of_decodeDescription_eq_none rfl

/-- A canonical code is invalid when its decoded description is not well formed. -/
theorem not_descriptionCodeValid_encodeDescription_of_not_wellFormed
    {D : MachineDescription} (hnot : ¬ D.WellFormed) :
    ¬ DescriptionCodeValid (encodeDescription D) := by
  intro h
  exact hnot ((descriptionCodeValid_encodeDescription_iff D).mp h)

/-- A zero-state description has no valid canonical code. -/
theorem not_descriptionCodeValid_encodeDescription_of_stateCount_eq_zero
    {D : MachineDescription} (hzero : D.stateCount = 0) :
    ¬ DescriptionCodeValid (encodeDescription D) := by
  apply not_descriptionCodeValid_encodeDescription_of_not_wellFormed
  intro hwell
  simpa [hzero] using hwell.left

/-- An out-of-range start state invalidates the canonical code. -/
theorem not_descriptionCodeValid_encodeDescription_of_start_not_lt
    {D : MachineDescription} (hstart : ¬ D.start < D.stateCount) :
    ¬ DescriptionCodeValid (encodeDescription D) := by
  apply not_descriptionCodeValid_encodeDescription_of_not_wellFormed
  intro hwell
  exact hstart hwell.right.left

/-- An out-of-range halt state invalidates the canonical code. -/
theorem not_descriptionCodeValid_encodeDescription_of_halt_not_lt
    {D : MachineDescription} (hhalt : ¬ D.halt < D.stateCount) :
    ¬ DescriptionCodeValid (encodeDescription D) := by
  apply not_descriptionCodeValid_encodeDescription_of_not_wellFormed
  intro hwell
  exact hhalt hwell.right.right.left

/-- An out-of-range transition source invalidates the canonical code. -/
theorem not_descriptionCodeValid_encodeDescription_of_transition_source_not_lt
    {D : MachineDescription} {t : TransitionDescription}
    (ht : t ∈ D.transitions) (hsource : ¬ t.source < D.stateCount) :
    ¬ DescriptionCodeValid (encodeDescription D) := by
  apply not_descriptionCodeValid_encodeDescription_of_not_wellFormed
  intro hwell
  have htwell := hwell.right.right.right.left t ht
  exact hsource htwell.left

/-- An out-of-range transition target invalidates the canonical code. -/
theorem not_descriptionCodeValid_encodeDescription_of_transition_target_not_lt
    {D : MachineDescription} {t : TransitionDescription}
    (ht : t ∈ D.transitions) (htarget : ¬ t.target < D.stateCount) :
    ¬ DescriptionCodeValid (encodeDescription D) := by
  apply not_descriptionCodeValid_encodeDescription_of_not_wellFormed
  intro hwell
  have htwell := hwell.right.right.right.left t ht
  exact htarget htwell.right

/-- Conflicting rows with the same lookup key invalidate the canonical code. -/
theorem not_descriptionCodeValid_encodeDescription_of_conflicting_keys
    {D : MachineDescription} {t u : TransitionDescription}
    (ht : t ∈ D.transitions) (hu : u ∈ D.transitions)
    (hkey : TransitionDescription.SameKey t u)
    (hconflict : ¬ TransitionDescription.SameAction t u) :
    ¬ DescriptionCodeValid (encodeDescription D) := by
  apply not_descriptionCodeValid_encodeDescription_of_not_wellFormed
  intro hwell
  exact hconflict
    (hwell.right.right.right.right t u ht hu hkey)

/-- A canonical description followed by nonempty junk is not a complete code. -/
theorem decodeDescription_encodeDescription_append_eq_none_of_ne_nil
    (D : MachineDescription) {junk : Word MachineCodeSymbol}
    (hjunk : junk ≠ []) :
    decodeDescription (List.append (encodeDescription D) junk) = none := by
  cases hdecode :
      decodeDescription (List.append (encodeDescription D) junk) with
  | none => rfl
  | some decoded =>
      have hp :=
        (decodeDescription_eq_some_iff_decodeDescriptionPrefix_eq_some_nil
          (tokens := List.append (encodeDescription D) junk)
          (D := decoded)).mp hdecode
      have hprefix := decodeDescriptionPrefix_encodeDescription_append D junk
      have heq : some (D, junk) = some (decoded, []) := hprefix.symm.trans hp
      have hpair : (D, junk) = (decoded, []) := Option.some.inj heq
      have hjunkEmpty : junk = [] := congrArg Prod.snd hpair
      exact False.elim (hjunk hjunkEmpty)

/-- A canonical description followed by nonempty junk is not valid. -/
theorem not_descriptionCodeValid_encodeDescription_append_of_ne_nil
    (D : MachineDescription) {junk : Word MachineCodeSymbol}
    (hjunk : junk ≠ []) :
    ¬ DescriptionCodeValid (List.append (encodeDescription D) junk) :=
  not_descriptionCodeValid_of_decodeDescription_eq_none
    (decodeDescription_encodeDescription_append_eq_none_of_ne_nil D hjunk)

end MachineDescription
end Computability
end FoC
