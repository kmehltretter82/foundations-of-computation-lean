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
Canonical generated-input behavior for the uniform decoded-description
interpreter.  On a canonical description prefix plus an outer fuel field, the
runner agrees with the decoded description's bounded halting predicate.
-/
def DecodedDescriptionCanonicalStageSpec
    (runner : TuringMachine MachineCodeSymbol runnerState) : Prop :=
  forall D : MachineDescription,
  forall input : Word MachineCodeSymbol,
  forall fuel : Nat,
    TuringMachine.HaltsOnInput runner
        (GeneratedCode.stageCode
          (List.append (MachineDescription.encodeDescription D) input)
          fuel) <->
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input)

/--
Any halted input to the total decoded-description interpreter must have the
outer generated fuel and a canonical description-prefix payload.
-/
def DecodedDescriptionTotalShapeSpec
    (runner : TuringMachine MachineCodeSymbol runnerState) : Prop :=
  forall tokens : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput runner tokens ->
      exists fuel : Nat,
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeNat tokens =
          some (fuel,
            List.append (MachineDescription.encodeDescription D) input)

theorem decodedDescriptionCanonicalStageSpec_of_total
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (htotal : DecodedDescriptionInterpreterTotalSpec runner) :
    DecodedDescriptionCanonicalStageSpec runner := by
  intro D input fuel
  constructor
  · intro hhalt
    rcases
        (htotal
          (GeneratedCode.stageCode
            (List.append (MachineDescription.encodeDescription D) input)
            fuel)).mp hhalt with
      ⟨fuel', D', input', hdecode, hhalts⟩
    have hdecodeStage :
        MachineDescription.decodeNat
            (GeneratedCode.stageCode
              (List.append (MachineDescription.encodeDescription D)
                input) fuel) =
          some (fuel,
            List.append (MachineDescription.encodeDescription D) input) :=
      GeneratedCode.stageCode_decodeNat
        (List.append (MachineDescription.encodeDescription D) input)
        fuel
    rw [hdecodeStage] at hdecode
    have hpair :
        (fuel,
          List.append (MachineDescription.encodeDescription D) input) =
          (fuel',
            List.append (MachineDescription.encodeDescription D')
              input') :=
      Option.some.inj hdecode
    have hfuel : fuel = fuel' := congrArg Prod.fst hpair
    have hpayload :
        List.append (MachineDescription.encodeDescription D) input =
          List.append (MachineDescription.encodeDescription D') input' :=
      congrArg Prod.snd hpair
    have hprefix :
        MachineDescription.decodeDescriptionPrefix
            (List.append (MachineDescription.encodeDescription D) input) =
          some (D, input) :=
      MachineDescription.decodeDescriptionPrefix_encodeDescription_append
        D input
    have hprefix' :
        MachineDescription.decodeDescriptionPrefix
            (List.append (MachineDescription.encodeDescription D) input) =
          some (D', input') := by
      rw [hpayload]
      exact
        MachineDescription.decodeDescriptionPrefix_encodeDescription_append
          D' input'
    rw [hprefix] at hprefix'
    have hdesc : D' = D := by
      exact (Prod.mk.inj (Option.some.inj hprefix')).left.symm
    have hinput : input' = input := by
      exact (Prod.mk.inj (Option.some.inj hprefix')).right.symm
    subst D'
    subst input'
    subst fuel'
    simpa using hhalts
  · intro hhalts
    exact
      (htotal
        (GeneratedCode.stageCode
          (List.append (MachineDescription.encodeDescription D) input)
          fuel)).mpr
        ⟨fuel, D, input,
          GeneratedCode.stageCode_decodeNat
            (List.append (MachineDescription.encodeDescription D) input)
            fuel,
          hhalts⟩

theorem decodedDescriptionTotalShapeSpec_of_total
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (htotal : DecodedDescriptionInterpreterTotalSpec runner) :
    DecodedDescriptionTotalShapeSpec runner := by
  intro tokens hhalt
  rcases (htotal tokens).mp hhalt with
    ⟨fuel, D, input, hdecode, _hhalts⟩
  exact ⟨fuel, D, input, hdecode⟩

theorem decodedDescriptionInterpreterTotalSpec_of_components
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hcanonical : DecodedDescriptionCanonicalStageSpec runner)
    (hshape : DecodedDescriptionTotalShapeSpec runner) :
    DecodedDescriptionInterpreterTotalSpec runner := by
  intro tokens
  constructor
  · intro hhalt
    rcases hshape tokens hhalt with
      ⟨fuel, D, input, hdecode⟩
    rcases (hcanonical D input fuel).mp
        (by
          have htokens :
              tokens =
                GeneratedCode.stageCode
                  (List.append
                    (MachineDescription.encodeDescription D) input)
                  fuel :=
            GeneratedCode.stageCode_eq_of_decodeNat hdecode
          simpa [htokens] using hhalt) with
      hhalts
    exact ⟨fuel, D, input, hdecode, hhalts⟩
  · intro htarget
    rcases htarget with ⟨fuel, D, input, hdecode, hhalts⟩
    have htokens :
        tokens =
          GeneratedCode.stageCode
            (List.append (MachineDescription.encodeDescription D) input)
            fuel :=
      GeneratedCode.stageCode_eq_of_decodeNat hdecode
    rw [htokens]
    exact (hcanonical D input fuel).mpr hhalts

theorem decodedDescriptionInterpreterTotalSpec_iff_components
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    DecodedDescriptionInterpreterTotalSpec runner <->
      DecodedDescriptionCanonicalStageSpec runner ∧
        DecodedDescriptionTotalShapeSpec runner := by
  constructor
  · intro htotal
    exact
      ⟨decodedDescriptionCanonicalStageSpec_of_total htotal,
        decodedDescriptionTotalShapeSpec_of_total htotal⟩
  · intro h
    exact
      decodedDescriptionInterpreterTotalSpec_of_components
        h.left h.right

theorem decodedDescriptionInterpreterSpec_of_canonicalStage
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hcanonical : DecodedDescriptionCanonicalStageSpec runner) :
    DecodedDescriptionInterpreterSpec runner GeneratedCode.stageCode := by
  intro encoded input D fuel hdecode
  have hencoded :
      encoded =
        List.append (MachineDescription.encodeDescription D) input :=
    MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
      hdecode
  rw [hencoded]
  exact hcanonical D input fuel

theorem decodedDescriptionInterpreterSpec_of_total
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (htotal : DecodedDescriptionInterpreterTotalSpec runner) :
    DecodedDescriptionInterpreterSpec runner GeneratedCode.stageCode :=
  decodedDescriptionInterpreterSpec_of_canonicalStage
    (decodedDescriptionCanonicalStageSpec_of_total htotal)

/--
Component-level construction target for the uniform decoded-description
interpreter.
-/
def DecodedDescriptionInterpreterComponentsConstruction : Prop :=
  exists state : Type,
  exists runner : TuringMachine MachineCodeSymbol state,
    DecodedDescriptionCanonicalStageSpec runner ∧
      DecodedDescriptionTotalShapeSpec runner

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

theorem decodedDescriptionInterpreterConstruction_of_components
    (hcomponents : DecodedDescriptionInterpreterComponentsConstruction) :
    DecodedDescriptionInterpreterConstruction := by
  rcases hcomponents with
    ⟨state, runner, hcanonical, hshape⟩
  exact
    ⟨state, runner,
      decodedDescriptionInterpreterTotalSpec_of_components
        hcanonical hshape⟩

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
interpreter components.
-/
theorem decodedDescriptionInterpreterComponentsFiniteLeaf :
    DecodedDescriptionInterpreterComponentsConstruction := by
  sorry

/--
Remaining concrete finite-table leaf for the uniform decoded-description
interpreter.
-/
theorem decodedDescriptionInterpreterFiniteLeaf :
    DecodedDescriptionInterpreterConstruction := by
  exact
    decodedDescriptionInterpreterConstruction_of_components
      decodedDescriptionInterpreterComponentsFiniteLeaf

theorem decodedDescriptionInterpreterFinStateFiniteLeaf :
    DecodedDescriptionInterpreterFinStateConstruction := by
  exact
    decodedDescriptionInterpreterFinStateConstruction_of_construction
      decodedDescriptionInterpreterFiniteLeaf

end FiniteRecognizer

end Computability
end FoC
