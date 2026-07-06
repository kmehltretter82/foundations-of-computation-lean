import FoC.Computability.Compiler.Core.FiniteRecognizer.DecodedDescriptionInterpreter

set_option doc.verso true

/-!
# Decoded-description interpreter route contracts

This module packages the semantic and construction-chain surfaces for the
uniform decoded-description interpreter.  The concrete finite-table leaf
remains in
{module}`FoC.Computability.Compiler.Core.FiniteRecognizer.DecodedDescriptionInterpreter`;
the route contracts here record the reusable path from canonical generated
inputs, through exact-output decoding, to the ordinary total interpreter
contract used by generated-program and controller code.
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
## Exact-output primitive route
-/

structure DecodedDescriptionInterpreterExactOutputPrimitiveRoute
    (runnerState : Type)
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    Prop where
  exactSpec :
    ExactFuel.StageProgram.ExactOutputSpec
      runner decodedDescriptionInterpreterRun
  canonical :
    ExactFuel.StageProgram.ExactOutputCanonicalSpec
      runner decodedDescriptionInterpreterRun
  haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled runner
  haltsWithExactOutputIff :
    forall tokens output : Word MachineCodeSymbol,
      TuringMachine.HaltsWithExactOutput runner tokens output <->
        decodedDescriptionInterpreterRun tokens = some output
  haltsWithEmptyIff :
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsWithExactOutput runner tokens
          ([] : Word MachineCodeSymbol) <->
        decodedDescriptionInterpreterRun tokens =
          some ([] : Word MachineCodeSymbol)
  acceptsIffEmptyRun :
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput runner tokens <->
        decodedDescriptionInterpreterRun tokens =
          some ([] : Word MachineCodeSymbol)
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

def DecodedDescriptionInterpreterExactOutputPrimitiveRouteConstruction :
    Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    DecodedDescriptionInterpreterExactOutputPrimitiveRoute
      runnerState runner

theorem decodedDescriptionInterpreterExactOutputPrimitiveRoute_of_construction
    (h :
      DecodedDescriptionInterpreterExactOutputPrimitiveConstruction) :
    DecodedDescriptionInterpreterExactOutputPrimitiveRouteConstruction := by
  rcases h with
    ⟨runnerState, runner, hexact, hcanonical, hstop⟩
  have haccepts :
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          decodedDescriptionInterpreterRun tokens =
            some ([] : Word MachineCodeSymbol) :=
    ExactFuel.StageProgram.haltsOnInput_iff_some_empty_of_exactOutput
      hexact hcanonical
      (by
        intro tokens output hrun
        exact
          decodedDescriptionInterpreterRun_eq_some_empty_of_eq_some
            hrun)
  refine ⟨runnerState, runner, ?_⟩
  exact
    { exactSpec := hexact
      canonical := hcanonical
      haltingTransitionsDisabled := hstop
      haltsWithExactOutputIff := by
        intro tokens output
        exact hexact tokens output
      haltsWithEmptyIff := by
        intro tokens
        exact hexact tokens ([] : Word MachineCodeSymbol)
      acceptsIffEmptyRun := haccepts
      acceptsCanonicalStageIff := by
        intro D input fuel
        exact Iff.trans
          (haccepts
            (GeneratedCode.stageCode
              (List.append (MachineDescription.encodeDescription D) input)
              fuel))
          (decodedDescriptionInterpreterRun_stageCode_eq_some_iff
            D input fuel) }

theorem decodedDescriptionInterpreterExactOutputPrimitiveRoute_of_finState
    (h :
      DecodedDescriptionInterpreterExactOutputPrimitiveFinStateConstruction) :
    DecodedDescriptionInterpreterExactOutputPrimitiveRouteConstruction :=
  decodedDescriptionInterpreterExactOutputPrimitiveRoute_of_construction
    (decodedDescriptionInterpreterExactOutputPrimitiveConstruction_of_finState
      h)

/-!
## Decoded exact-output route
-/

structure DecodedDescriptionInterpreterDecodedExactOutputPrimitiveRoute
    (runnerState : Type)
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    Prop where
  decodedSpec :
    DecodedDescriptionInterpreterDecodedExactOutputSpec runner
  exactSpec :
    ExactFuel.StageProgram.ExactOutputSpec
      runner decodedDescriptionInterpreterRun
  canonical :
    ExactFuel.StageProgram.ExactOutputCanonicalSpec
      runner decodedDescriptionInterpreterRun
  haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled runner
  forward :
    DecodedDescriptionInterpreterDecodedExactOutputForwardSpec runner
  closed :
    DecodedDescriptionInterpreterDecodedExactOutputClosedSpec runner
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

def DecodedDescriptionInterpreterDecodedExactOutputPrimitiveRouteConstruction :
    Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    DecodedDescriptionInterpreterDecodedExactOutputPrimitiveRoute
      runnerState runner

theorem decodedDescriptionInterpreterDecodedExactOutputPrimitiveRoute_of_construction
    (h :
      DecodedDescriptionInterpreterDecodedExactOutputPrimitiveConstruction) :
    DecodedDescriptionInterpreterDecodedExactOutputPrimitiveRouteConstruction := by
  rcases h with
    ⟨runnerState, runner, hdecoded, hcanonical, hstop⟩
  let hexact :
      ExactFuel.StageProgram.ExactOutputSpec
        runner decodedDescriptionInterpreterRun :=
    (decodedDescriptionInterpreterExactOutputSpec_iff_decoded
      runner).mpr hdecoded
  have haccepts :
      forall tokens : Word MachineCodeSymbol,
        TuringMachine.HaltsOnInput runner tokens <->
          decodedDescriptionInterpreterRun tokens =
            some ([] : Word MachineCodeSymbol) :=
    ExactFuel.StageProgram.haltsOnInput_iff_some_empty_of_exactOutput
      hexact hcanonical
      (by
        intro tokens output hrun
        exact
          decodedDescriptionInterpreterRun_eq_some_empty_of_eq_some
            hrun)
  refine ⟨runnerState, runner, ?_⟩
  exact
    { decodedSpec := hdecoded
      exactSpec := hexact
      canonical := hcanonical
      haltingTransitionsDisabled := hstop
      forward := hdecoded.left
      closed := hdecoded.right
      acceptsCanonicalStageIff := by
        intro D input fuel
        exact Iff.trans
          (haccepts
            (GeneratedCode.stageCode
              (List.append (MachineDescription.encodeDescription D) input)
              fuel))
          (decodedDescriptionInterpreterRun_stageCode_eq_some_iff
            D input fuel)
      haltedTokensShape := by
        intro tokens hhalt
        exact decodedDescriptionInterpreterRun_eq_some_shape
          ((haccepts tokens).mp hhalt) }

theorem decodedDescriptionInterpreterDecodedExactOutputPrimitiveRoute_of_exactRoute
    {runnerState : Type}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    (hroute :
      DecodedDescriptionInterpreterExactOutputPrimitiveRoute
        runnerState runner) :
    DecodedDescriptionInterpreterDecodedExactOutputPrimitiveRoute
      runnerState runner :=
  { decodedSpec :=
      (decodedDescriptionInterpreterExactOutputSpec_iff_decoded
        runner).mp hroute.exactSpec
    exactSpec := hroute.exactSpec
    canonical := hroute.canonical
    haltingTransitionsDisabled := hroute.haltingTransitionsDisabled
    forward :=
      ((decodedDescriptionInterpreterExactOutputSpec_iff_decoded
        runner).mp hroute.exactSpec).left
    closed :=
      ((decodedDescriptionInterpreterExactOutputSpec_iff_decoded
        runner).mp hroute.exactSpec).right
    acceptsCanonicalStageIff :=
      hroute.acceptsCanonicalStageIff
    haltedTokensShape := by
      intro tokens hhalt
      exact decodedDescriptionInterpreterRun_eq_some_shape
        ((hroute.acceptsIffEmptyRun tokens).mp hhalt) }

theorem decodedDescriptionInterpreterDecodedExactOutputPrimitiveRoute_of_finState
    (h :
      DecodedDescriptionInterpreterDecodedExactOutputPrimitiveFinStateConstruction) :
    DecodedDescriptionInterpreterDecodedExactOutputPrimitiveRouteConstruction := by
  exact
    decodedDescriptionInterpreterDecodedExactOutputPrimitiveRoute_of_construction
      ((decodedDescriptionInterpreterExactOutputPrimitiveConstruction_iff_decoded).mp
        (decodedDescriptionInterpreterExactOutputPrimitiveConstruction_of_finState
          ((decodedDescriptionInterpreterExactOutputPrimitiveFinStateConstruction_iff_decoded).mpr
            h)))

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

theorem decodedDescriptionInterpreterComponentsRoute_of_exactOutputPrimitive
    (h :
      DecodedDescriptionInterpreterExactOutputPrimitiveConstruction) :
    DecodedDescriptionInterpreterComponentsRouteConstruction :=
  decodedDescriptionInterpreterComponentsRoute_of_components
    (decodedDescriptionInterpreterComponentsConstruction_of_exactOutputPrimitive
      h)

theorem decodedDescriptionInterpreterComponentsRoute_of_decodedExactOutputPrimitive
    (h :
      DecodedDescriptionInterpreterDecodedExactOutputPrimitiveConstruction) :
    DecodedDescriptionInterpreterComponentsRouteConstruction :=
  decodedDescriptionInterpreterComponentsRoute_of_exactOutputPrimitive
    ((decodedDescriptionInterpreterExactOutputPrimitiveConstruction_iff_decoded).mpr
      h)

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
  decodedExactOutputPrimitiveFinState :
    DecodedDescriptionInterpreterDecodedExactOutputPrimitiveFinStateConstruction
  exactOutputPrimitiveFinState :
    DecodedDescriptionInterpreterExactOutputPrimitiveFinStateConstruction
  exactOutputPrimitive :
    DecodedDescriptionInterpreterExactOutputPrimitiveConstruction
  decodedExactOutputRoute :
    DecodedDescriptionInterpreterDecodedExactOutputPrimitiveRouteConstruction
  exactOutputRoute :
    DecodedDescriptionInterpreterExactOutputPrimitiveRouteConstruction
  components :
    DecodedDescriptionInterpreterComponentsConstruction
  componentsRoute :
    DecodedDescriptionInterpreterComponentsRouteConstruction
  construction :
    DecodedDescriptionInterpreterConstruction
  runnerRoute :
    DecodedDescriptionInterpreterRunnerRouteConstruction
  finStateConstruction :
    DecodedDescriptionInterpreterFinStateConstruction
  semanticShape :
    forall D : MachineDescription,
    forall input : Word MachineCodeSymbol,
    forall fuel : Nat,
      DecodedDescriptionInterpreterStageShape D input fuel

def DecodedDescriptionInterpreterFiniteRouteConstruction : Prop :=
  DecodedDescriptionInterpreterFiniteRoute

theorem decodedDescriptionInterpreterFiniteRoute_of_decodedExactOutput
    (hdecoded :
      DecodedDescriptionInterpreterDecodedExactOutputPrimitiveFinStateConstruction) :
    DecodedDescriptionInterpreterFiniteRoute := by
  let hexactFin :
      DecodedDescriptionInterpreterExactOutputPrimitiveFinStateConstruction :=
    (decodedDescriptionInterpreterExactOutputPrimitiveFinStateConstruction_iff_decoded).mpr
      hdecoded
  let hexact :
      DecodedDescriptionInterpreterExactOutputPrimitiveConstruction :=
    decodedDescriptionInterpreterExactOutputPrimitiveConstruction_of_finState
      hexactFin
  let hcomponents :
      DecodedDescriptionInterpreterComponentsConstruction :=
    decodedDescriptionInterpreterComponentsConstruction_of_exactOutputPrimitive
      hexact
  let hconstruction :
      DecodedDescriptionInterpreterConstruction :=
    decodedDescriptionInterpreterConstruction_of_components
      hcomponents
  let hfin :
      DecodedDescriptionInterpreterFinStateConstruction :=
    decodedDescriptionInterpreterFinStateConstruction_of_construction
      hconstruction
  exact
    { decodedExactOutputPrimitiveFinState := hdecoded
      exactOutputPrimitiveFinState := hexactFin
      exactOutputPrimitive := hexact
      decodedExactOutputRoute :=
        decodedDescriptionInterpreterDecodedExactOutputPrimitiveRoute_of_finState
          hdecoded
      exactOutputRoute :=
        decodedDescriptionInterpreterExactOutputPrimitiveRoute_of_finState
          hexactFin
      components := hcomponents
      componentsRoute :=
        decodedDescriptionInterpreterComponentsRoute_of_components
          hcomponents
      construction := hconstruction
      runnerRoute :=
        decodedDescriptionInterpreterRunnerRoute_of_construction
          hconstruction
      finStateConstruction := hfin
      semanticShape := by
        intro D input fuel
        exact decodedDescriptionInterpreterStageShape D input fuel }

theorem decodedDescriptionInterpreterFiniteRoute_finiteLeaf :
    DecodedDescriptionInterpreterFiniteRoute :=
  decodedDescriptionInterpreterFiniteRoute_of_decodedExactOutput
    decodedDescriptionInterpreterDecodedExactOutputPrimitiveFinStateFiniteLeaf

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

theorem DecodedDescriptionInterpreterFiniteRoute.componentsConstruction
    (hroute : DecodedDescriptionInterpreterFiniteRoute) :
    DecodedDescriptionInterpreterComponentsConstruction :=
  hroute.components

theorem DecodedDescriptionInterpreterFiniteRoute.exactOutputConstruction
    (hroute : DecodedDescriptionInterpreterFiniteRoute) :
    DecodedDescriptionInterpreterExactOutputPrimitiveConstruction :=
  hroute.exactOutputPrimitive

theorem DecodedDescriptionInterpreterFiniteRoute.decodedExactOutputRouteConstruction
    (hroute : DecodedDescriptionInterpreterFiniteRoute) :
    DecodedDescriptionInterpreterDecodedExactOutputPrimitiveRouteConstruction :=
  hroute.decodedExactOutputRoute

theorem DecodedDescriptionInterpreterFiniteRoute.exactOutputRouteConstruction
    (hroute : DecodedDescriptionInterpreterFiniteRoute) :
    DecodedDescriptionInterpreterExactOutputPrimitiveRouteConstruction :=
  hroute.exactOutputRoute

theorem DecodedDescriptionInterpreterFiniteRoute.componentsRouteConstruction
    (hroute : DecodedDescriptionInterpreterFiniteRoute) :
    DecodedDescriptionInterpreterComponentsRouteConstruction :=
  hroute.componentsRoute

theorem DecodedDescriptionInterpreterFiniteRoute.runnerRouteConstruction
    (hroute : DecodedDescriptionInterpreterFiniteRoute) :
    DecodedDescriptionInterpreterRunnerRouteConstruction :=
  hroute.runnerRoute

/-!
## Public finite-leaf aliases
-/

theorem decodedDescriptionInterpreterDecodedExactOutputPrimitiveFinStateFiniteLeaf_route :
    DecodedDescriptionInterpreterDecodedExactOutputPrimitiveFinStateConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf
    |>.decodedExactOutputPrimitiveFinState

theorem decodedDescriptionInterpreterExactOutputPrimitiveFinStateFiniteLeaf_route :
    DecodedDescriptionInterpreterExactOutputPrimitiveFinStateConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf
    |>.exactOutputPrimitiveFinState

theorem decodedDescriptionInterpreterExactOutputPrimitiveFiniteLeaf_route :
    DecodedDescriptionInterpreterExactOutputPrimitiveConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf
    |>.exactOutputPrimitive

theorem decodedDescriptionInterpreterComponentsFiniteLeaf_route :
    DecodedDescriptionInterpreterComponentsConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf
    |>.components

theorem decodedDescriptionInterpreterFiniteLeaf_route :
    DecodedDescriptionInterpreterConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf
    |>.construction

theorem decodedDescriptionInterpreterFinStateFiniteLeaf_route :
    DecodedDescriptionInterpreterFinStateConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf
    |>.finStateConstruction

theorem decodedDescriptionInterpreterRunnerRoute_finiteLeaf :
    DecodedDescriptionInterpreterRunnerRouteConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf
    |>.runnerRoute

theorem decodedDescriptionInterpreterComponentsRoute_finiteLeaf :
    DecodedDescriptionInterpreterComponentsRouteConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf
    |>.componentsRoute

theorem decodedDescriptionInterpreterExactOutputPrimitiveRoute_finiteLeaf :
    DecodedDescriptionInterpreterExactOutputPrimitiveRouteConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf
    |>.exactOutputRoute

theorem decodedDescriptionInterpreterDecodedExactOutputPrimitiveRoute_finiteLeaf :
    DecodedDescriptionInterpreterDecodedExactOutputPrimitiveRouteConstruction :=
  decodedDescriptionInterpreterFiniteRoute_finiteLeaf
    |>.decodedExactOutputRoute

end FiniteRecognizer

end Computability
end FoC
