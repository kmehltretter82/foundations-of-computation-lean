import FoC.Computability.Compiler.Core.FiniteRecognizer.DecodedDescriptionInterpreter

set_option doc.verso true

/-!
# Decoded-description interpreter route contracts

This module packages the semantic and ordinary-halting construction surfaces
for the uniform decoded-description interpreter. The concrete finite-table leaf
remains in
{module}`FoC.Computability.Compiler.Core.FiniteRecognizer.DecodedDescriptionInterpreter`;
the route contracts here record the reusable path from canonical generated
inputs to the total interpreter contract used by generated-program and
controller code. Literal exact-empty-output routes are intentionally absent:
the input context is nonempty and tape context cannot shrink.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer

/-!
## Canonical generated-input shape
-/

structure DecodedDescriptionInterpreterStageShape
    (D : MachineDescription)
    (input : Word MachineCodeSymbol)
    (fuel : Nat) : Prop where
  stageDecode :
    MachineDescription.decodeNat
        (GeneratedCode.stageCode
          (List.append (MachineDescription.encodeDescription D) input)
          fuel) =
      some (fuel,
        List.append (MachineDescription.encodeDescription D) input)
  prefixDecode :
    MachineDescription.decodeDescriptionPrefix
        (List.append (MachineDescription.encodeDescription D) input) =
      some (D, input)
  runStageCodeIff :
    decodedDescriptionInterpreterRun
        (GeneratedCode.stageCode
          (List.append (MachineDescription.encodeDescription D) input)
          fuel) =
        some ([] : Word MachineCodeSymbol) <->
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input)
  runStageCodeOfHalts :
    D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input) ->
      decodedDescriptionInterpreterRun
          (GeneratedCode.stageCode
            (List.append (MachineDescription.encodeDescription D) input)
            fuel) =
        some ([] : Word MachineCodeSymbol)
  haltsOfRunStageCode :
    decodedDescriptionInterpreterRun
        (GeneratedCode.stageCode
          (List.append (MachineDescription.encodeDescription D) input)
          fuel) =
        some ([] : Word MachineCodeSymbol) ->
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input)
  outputEmptyOfRun :
    forall output : Word MachineCodeSymbol,
      decodedDescriptionInterpreterRun
          (GeneratedCode.stageCode
            (List.append (MachineDescription.encodeDescription D) input)
            fuel) =
          some output ->
        output = ([] : Word MachineCodeSymbol)
  runEqSomeShape :
    forall tokens : Word MachineCodeSymbol,
      decodedDescriptionInterpreterRun tokens =
          some ([] : Word MachineCodeSymbol) ->
        exists decodedFuel : Nat,
        exists decodedDescription : MachineDescription,
        exists decodedInput : Word MachineCodeSymbol,
          MachineDescription.decodeNat tokens =
            some (decodedFuel,
              List.append
                (MachineDescription.encodeDescription decodedDescription)
                decodedInput)
  runEqSomeIff :
    forall tokens output : Word MachineCodeSymbol,
      decodedDescriptionInterpreterRun tokens = some output <->
        exists decodedFuel : Nat,
        exists decodedDescription : MachineDescription,
        exists decodedInput : Word MachineCodeSymbol,
          MachineDescription.decodeNat tokens =
            some (decodedFuel,
              List.append
                (MachineDescription.encodeDescription decodedDescription)
                decodedInput) /\
            output = ([] : Word MachineCodeSymbol) /\
            decodedDescription.HaltsIn decodedFuel
              (MachineDescription.encodeCodeWordAsInput decodedInput)
  canonicalTokensOfDecode :
    forall tokens : Word MachineCodeSymbol,
      MachineDescription.decodeNat tokens =
          some (fuel,
            List.append (MachineDescription.encodeDescription D) input) ->
        tokens =
          GeneratedCode.stageCode
            (List.append (MachineDescription.encodeDescription D) input)
            fuel

theorem decodedDescriptionInterpreterStageShape
    (D : MachineDescription)
    (input : Word MachineCodeSymbol)
    (fuel : Nat) :
    DecodedDescriptionInterpreterStageShape D input fuel :=
  { stageDecode :=
      GeneratedCode.stageCode_decodeNat
        (List.append (MachineDescription.encodeDescription D) input)
        fuel
    prefixDecode :=
      MachineDescription.decodeDescriptionPrefix_encodeDescription_append
        D input
    runStageCodeIff :=
      decodedDescriptionInterpreterRun_stageCode_eq_some_iff
        D input fuel
    runStageCodeOfHalts := by
      intro hhalts
      exact
        (decodedDescriptionInterpreterRun_stageCode_eq_some_iff
          D input fuel).mpr hhalts
    haltsOfRunStageCode := by
      intro hrun
      exact
        (decodedDescriptionInterpreterRun_stageCode_eq_some_iff
          D input fuel).mp hrun
    outputEmptyOfRun := by
      intro output hrun
      exact
        decodedDescriptionInterpreterRun_eq_some_empty_of_eq_some
          hrun
    runEqSomeShape := by
      intro tokens hrun
      exact decodedDescriptionInterpreterRun_eq_some_shape hrun
    runEqSomeIff := by
      intro tokens output
      exact decodedDescriptionInterpreterRun_eq_some_iff tokens output
    canonicalTokensOfDecode := by
      intro tokens hdecode
      exact GeneratedCode.stageCode_eq_of_decodeNat hdecode }

theorem decodedDescriptionInterpreterRun_stageCode_of_halts
    (D : MachineDescription)
    (input : Word MachineCodeSymbol)
    (fuel : Nat)
    (hhalts :
      D.HaltsIn fuel
        (MachineDescription.encodeCodeWordAsInput input)) :
    decodedDescriptionInterpreterRun
        (GeneratedCode.stageCode
          (List.append (MachineDescription.encodeDescription D) input)
          fuel) =
      some ([] : Word MachineCodeSymbol) :=
  (decodedDescriptionInterpreterStageShape D input fuel).runStageCodeOfHalts
    hhalts

theorem decodedDescriptionInterpreterRun_stageCode_halts_of_eq_some
    (D : MachineDescription)
    (input : Word MachineCodeSymbol)
    (fuel : Nat)
    (hrun :
      decodedDescriptionInterpreterRun
          (GeneratedCode.stageCode
            (List.append (MachineDescription.encodeDescription D) input)
            fuel) =
        some ([] : Word MachineCodeSymbol)) :
    D.HaltsIn fuel
      (MachineDescription.encodeCodeWordAsInput input) :=
  (decodedDescriptionInterpreterStageShape D input fuel).haltsOfRunStageCode
    hrun

theorem decodedDescriptionInterpreterRun_stageCode_output_empty
    (D : MachineDescription)
    (input output : Word MachineCodeSymbol)
    (fuel : Nat)
    (hrun :
      decodedDescriptionInterpreterRun
          (GeneratedCode.stageCode
            (List.append (MachineDescription.encodeDescription D) input)
            fuel) =
        some output) :
    output = ([] : Word MachineCodeSymbol) :=
  (decodedDescriptionInterpreterStageShape D input fuel).outputEmptyOfRun
    output hrun

theorem decodedDescriptionInterpreterRun_tokens_shape
    {tokens : Word MachineCodeSymbol}
    (hrun :
      decodedDescriptionInterpreterRun tokens =
        some ([] : Word MachineCodeSymbol)) :
    exists fuel : Nat,
    exists D : MachineDescription,
    exists input : Word MachineCodeSymbol,
      MachineDescription.decodeNat tokens =
        some (fuel,
          List.append (MachineDescription.encodeDescription D) input) :=
  decodedDescriptionInterpreterRun_eq_some_shape hrun

/-!
## Ordinary total-interpreter component routes
-/

structure DecodedDescriptionInterpreterComponentsRoute
    (runnerState : Type)
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    Prop where
  canonicalStage :
    DecodedDescriptionCanonicalStageSpec runner
  totalShape :
    DecodedDescriptionTotalShapeSpec runner
  totalSpec :
    DecodedDescriptionInterpreterTotalSpec runner
  publicGeneratedSpec :
    DecodedDescriptionInterpreterSpec runner GeneratedCode.stageCode
  acceptsCanonicalStageIff :
    forall D : MachineDescription,
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      TuringMachine.HaltsOnInput runner
          (GeneratedCode.stageCode
            (List.append (MachineDescription.encodeDescription D) input)
            fuel) <->
        D.HaltsIn fuel
          (MachineDescription.encodeCodeWordAsInput input)
  haltedTokensShape :
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens ->
        exists fuel : Nat,
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeNat tokens =
            some (fuel,
              List.append (MachineDescription.encodeDescription D) input)
  acceptsTokensIff :
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens <->
        exists fuel : Nat,
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeNat tokens =
            some (fuel,
              List.append (MachineDescription.encodeDescription D) input) /\
            D.HaltsIn fuel
              (MachineDescription.encodeCodeWordAsInput input)

def DecodedDescriptionInterpreterComponentsRouteConstruction :
    Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    DecodedDescriptionInterpreterComponentsRoute runnerState runner

theorem decodedDescriptionInterpreterComponentsRoute_of_components
    (h :
      DecodedDescriptionInterpreterComponentsConstruction) :
    DecodedDescriptionInterpreterComponentsRouteConstruction := by
  rcases h with
    ⟨runnerState, runner, hcanonical, hshape⟩
  let htotal :
      DecodedDescriptionInterpreterTotalSpec runner :=
    decodedDescriptionInterpreterTotalSpec_of_components
      hcanonical hshape
  refine ⟨runnerState, runner, ?_⟩
  exact
    { canonicalStage := hcanonical
      totalShape := hshape
      totalSpec := htotal
      publicGeneratedSpec :=
        decodedDescriptionInterpreterSpec_of_total htotal
      acceptsCanonicalStageIff := hcanonical
      haltedTokensShape := hshape
      acceptsTokensIff := htotal }

theorem decodedDescriptionInterpreterComponentsRoute_of_construction
    (h :
      DecodedDescriptionInterpreterConstruction) :
    DecodedDescriptionInterpreterComponentsRouteConstruction := by
  rcases h with ⟨runnerState, runner, htotal⟩
  refine ⟨runnerState, runner, ?_⟩
  exact
    { canonicalStage :=
        decodedDescriptionCanonicalStageSpec_of_total htotal
      totalShape :=
        decodedDescriptionTotalShapeSpec_of_total htotal
      totalSpec := htotal
      publicGeneratedSpec :=
        decodedDescriptionInterpreterSpec_of_total htotal
      acceptsCanonicalStageIff :=
        decodedDescriptionCanonicalStageSpec_of_total htotal
      haltedTokensShape :=
        decodedDescriptionTotalShapeSpec_of_total htotal
      acceptsTokensIff := htotal }

/-!
## Runner route projections
-/

structure DecodedDescriptionInterpreterRunnerRoute
    (runnerState : Type)
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    Prop where
  totalSpec :
    DecodedDescriptionInterpreterTotalSpec runner
  canonicalStage :
    DecodedDescriptionCanonicalStageSpec runner
  totalShape :
    DecodedDescriptionTotalShapeSpec runner
  publicGeneratedSpec :
    DecodedDescriptionInterpreterSpec runner GeneratedCode.stageCode
  acceptsOfCanonical :
    forall D : MachineDescription,
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      D.HaltsIn fuel
          (MachineDescription.encodeCodeWordAsInput input) ->
        TuringMachine.HaltsOnInput runner
          (GeneratedCode.stageCode
            (List.append (MachineDescription.encodeDescription D) input)
            fuel)
  canonicalOfAccepts :
    forall D : MachineDescription,
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      TuringMachine.HaltsOnInput runner
          (GeneratedCode.stageCode
            (List.append (MachineDescription.encodeDescription D) input)
            fuel) ->
        D.HaltsIn fuel
          (MachineDescription.encodeCodeWordAsInput input)
  acceptsOfDecodedNat :
    forall tokens : Word MachineCodeSymbol,
    forall fuel : Nat,
    forall D : MachineDescription,
    forall input : Word MachineCodeSymbol,
      MachineDescription.decodeNat tokens =
          some (fuel,
            List.append (MachineDescription.encodeDescription D) input) ->
      D.HaltsIn fuel
          (MachineDescription.encodeCodeWordAsInput input) ->
        TuringMachine.HaltsOnInput runner tokens
  decodedNatOfAccepts :
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens ->
        exists fuel : Nat,
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeNat tokens =
            some (fuel,
              List.append (MachineDescription.encodeDescription D) input)

def DecodedDescriptionInterpreterRunnerRouteConstruction : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    DecodedDescriptionInterpreterRunnerRoute runnerState runner

theorem decodedDescriptionInterpreterRunnerRoute_of_construction
    (h :
      DecodedDescriptionInterpreterConstruction) :
    DecodedDescriptionInterpreterRunnerRouteConstruction := by
  rcases h with ⟨runnerState, runner, htotal⟩
  let hcanonical :
      DecodedDescriptionCanonicalStageSpec runner :=
    decodedDescriptionCanonicalStageSpec_of_total htotal
  let hshape :
      DecodedDescriptionTotalShapeSpec runner :=
    decodedDescriptionTotalShapeSpec_of_total htotal
  refine ⟨runnerState, runner, ?_⟩
  exact
    { totalSpec := htotal
      canonicalStage := hcanonical
      totalShape := hshape
      publicGeneratedSpec :=
        decodedDescriptionInterpreterSpec_of_total htotal
      acceptsOfCanonical := by
        intro D input fuel hhalts
        exact (hcanonical D input fuel).mpr hhalts
      canonicalOfAccepts := by
        intro D input fuel hhalt
        exact (hcanonical D input fuel).mp hhalt
      acceptsOfDecodedNat := by
        intro tokens fuel D input hdecode hhalts
        exact (htotal tokens).mpr
          ⟨fuel, D, input, hdecode, hhalts⟩
      decodedNatOfAccepts := hshape }

theorem decodedDescriptionInterpreterRunnerRoute_of_components
    (h :
      DecodedDescriptionInterpreterComponentsConstruction) :
    DecodedDescriptionInterpreterRunnerRouteConstruction :=
  decodedDescriptionInterpreterRunnerRoute_of_construction
    (decodedDescriptionInterpreterConstruction_of_components h)

theorem decodedDescriptionInterpreterRunnerRoute_of_finState
    (h :
      DecodedDescriptionInterpreterFinStateConstruction) :
    DecodedDescriptionInterpreterRunnerRouteConstruction :=
  decodedDescriptionInterpreterRunnerRoute_of_construction
    (decodedDescriptionInterpreterConstruction_of_finState h)

/-!
## Finite route bundle
-/

structure DecodedDescriptionInterpreterFiniteRoute : Prop where
  finStateConstruction :
    DecodedDescriptionInterpreterFinStateConstruction
  construction :
    DecodedDescriptionInterpreterConstruction
  componentsRoute :
    DecodedDescriptionInterpreterComponentsRouteConstruction
  runnerRoute :
    DecodedDescriptionInterpreterRunnerRouteConstruction
  semanticShape :
    forall D : MachineDescription,
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      DecodedDescriptionInterpreterStageShape D input fuel

def DecodedDescriptionInterpreterFiniteRouteConstruction : Prop :=
  DecodedDescriptionInterpreterFiniteRoute

theorem decodedDescriptionInterpreterFiniteRoute_of_finState
    (hfin : DecodedDescriptionInterpreterFinStateConstruction) :
    DecodedDescriptionInterpreterFiniteRoute := by
  let hconstruction :
      DecodedDescriptionInterpreterConstruction :=
    decodedDescriptionInterpreterConstruction_of_finState hfin
  exact
    { finStateConstruction := hfin
      construction := hconstruction
      componentsRoute :=
        decodedDescriptionInterpreterComponentsRoute_of_construction
          hconstruction
      runnerRoute :=
        decodedDescriptionInterpreterRunnerRoute_of_construction
          hconstruction
      semanticShape := by
        intro D input fuel
        exact decodedDescriptionInterpreterStageShape D input fuel }

theorem decodedDescriptionInterpreterFiniteRoute_finiteLeaf :
    DecodedDescriptionInterpreterFiniteRoute :=
  decodedDescriptionInterpreterFiniteRoute_of_finState
    decodedDescriptionInterpreterFinStateFiniteLeaf

theorem decodedDescriptionInterpreterFiniteRouteConstruction_finiteLeaf :
    DecodedDescriptionInterpreterFiniteRouteConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf

theorem DecodedDescriptionInterpreterFiniteRoute.runnerConstruction
    (hroute : DecodedDescriptionInterpreterFiniteRoute) :
    DecodedDescriptionInterpreterConstruction :=
  hroute.construction

theorem DecodedDescriptionInterpreterFiniteRoute.finState
    (hroute : DecodedDescriptionInterpreterFiniteRoute) :
    DecodedDescriptionInterpreterFinStateConstruction :=
  hroute.finStateConstruction

theorem DecodedDescriptionInterpreterFiniteRoute.componentsRouteConstruction
    (hroute : DecodedDescriptionInterpreterFiniteRoute) :
    DecodedDescriptionInterpreterComponentsRouteConstruction :=
  hroute.componentsRoute

theorem DecodedDescriptionInterpreterFiniteRoute.runnerRouteConstruction
    (hroute : DecodedDescriptionInterpreterFiniteRoute) :
    DecodedDescriptionInterpreterRunnerRouteConstruction :=
  hroute.runnerRoute

end FiniteRecognizer

end Computability
end FoC
