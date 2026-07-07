import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerInvocation

set_option doc.verso true

/-!
# Controller invocation route contracts

This module packages the controller stage-attempt invocation hierarchy.  The
concrete framed finite-table leaf remains in
{module}`FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerInvocation`;
the route contracts here expose the witnessed, framed, protected, public
encoder-facing, and handoff-facing surfaces used by the controller search
driver.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-!
## Framed exact-output endpoint shape
-/

structure ControllerStageAttemptFramedOutputShape
    (C : DovetailControllerLayout)
    (result : Word Bool) : Prop where
  normalizedOutput :
    Tape.normalizedOutput
        (CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
          C result) =
      encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult C result))
  cells :
    Tape.cells
        (CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
          C result) =
      match
        encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult C result))
      with
      | [] => [none]
      | bit :: rest => some bit :: rest.map some
  outputHaltsWithOutput :
    forall invoker : MachineDescription,
      invoker.HaltsWithTape
          (encodeCodeWordAsInput (DovetailControllerLayout.encode C))
          (CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
            C result) ->
        invoker.HaltsWithOutput
          (encodeCodeWordAsInput (DovetailControllerLayout.encode C))
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.withResult C result)))

theorem controllerStageAttemptFramedOutputShape
    (C : DovetailControllerLayout)
    (result : Word Bool) :
    ControllerStageAttemptFramedOutputShape C result :=
  { normalizedOutput :=
      CommonGround.ControllerInvocation.stageAttemptFramedOutputTape_normalizedOutput
        C result
    cells :=
      CommonGround.ControllerInvocation.stageAttemptFramedOutputTape_cells
        C result
    outputHaltsWithOutput := by
      intro invoker hTape
      have houtput := haltsWithOutput_of_haltsWithTape hTape
      simpa
        [CommonGround.ControllerInvocation.stageAttemptFramedOutputTape_normalizedOutput
          C result] using houtput }

/-!
## Witnessed and framed route surfaces
-/

structure ControllerStageAttemptWitnessedInvocationRoute
    (attempt invoker : MachineDescription) : Prop where
  realizes :
    CommonGround.ControllerInvocation.StageAttemptWitnessedRealizes
      attempt invoker
  subroutineReady :
    invoker.SubroutineReady
  witnessedForward :
    CommonGround.ControllerInvocation.StageAttemptWitnessedForwardSpec
      attempt invoker
  framedClosed :
    CommonGround.ControllerInvocation.StageAttemptFramedClosedSpec
      attempt invoker
  framedRealizes :
    CommonGround.ControllerInvocation.StageAttemptFramedRealizes
      attempt invoker
  protectedRealizes :
    CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
      attempt invoker
  protectedIff :
    forall C : DovetailControllerLayout,
    forall result : Word Bool,
      invoker.HaltsWithOutput
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C))
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.withResult C result))) <->
        attempt.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C))
          (encodeCodeWordAsInput (encodeBoolWord result))

structure ControllerStageAttemptFramedInvocationRoute
    (attempt invoker : MachineDescription) : Prop where
  realizes :
    CommonGround.ControllerInvocation.StageAttemptFramedRealizes
      attempt invoker
  subroutineReady :
    invoker.SubroutineReady
  framedForward :
    CommonGround.ControllerInvocation.StageAttemptFramedForwardSpec
      attempt invoker
  framedClosed :
    CommonGround.ControllerInvocation.StageAttemptFramedClosedSpec
      attempt invoker
  witnessedRealizes :
    CommonGround.ControllerInvocation.StageAttemptWitnessedRealizes
      attempt invoker
  witnessedForward :
    CommonGround.ControllerInvocation.StageAttemptWitnessedForwardSpec
      attempt invoker
  protectedRealizes :
    CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
      attempt invoker
  protectedIff :
    forall C : DovetailControllerLayout,
    forall result : Word Bool,
      invoker.HaltsWithOutput
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C))
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.withResult C result))) <->
        attempt.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C))
          (encodeCodeWordAsInput (encodeBoolWord result))
  outputOfWitness :
    forall C : DovetailControllerLayout,
    forall result : Word Bool,
    forall n : Nat,
      attempt.HaltsWithOutputIn n
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput (encodeBoolWord result)) ->
      invoker.HaltsWithOutput
        (encodeCodeWordAsInput (DovetailControllerLayout.encode C))
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult C result)))
  witnessOfOutput :
    forall C : DovetailControllerLayout,
    forall result : Word Bool,
      invoker.HaltsWithOutput
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C))
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.withResult C result))) ->
        exists n : Nat,
          attempt.HaltsWithOutputIn n
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageInputCode C))
            (encodeCodeWordAsInput (encodeBoolWord result))

theorem controllerStageAttemptWitnessedInvocationRoute_of_realizes
    {attempt invoker : MachineDescription}
    (h :
      CommonGround.ControllerInvocation.StageAttemptWitnessedRealizes
        attempt invoker) :
    ControllerStageAttemptWitnessedInvocationRoute attempt invoker :=
  { realizes := h
    subroutineReady := h.left
    witnessedForward := h.right.left
    framedClosed := h.right.right
    framedRealizes :=
      CommonGround.ControllerInvocation.stageAttemptFramedRealizes_of_witnessed
        h
    protectedRealizes :=
      CommonGround.ControllerInvocation.stageAttemptProtectedRealizes_of_framed
        (CommonGround.ControllerInvocation.stageAttemptFramedRealizes_of_witnessed
          h)
    protectedIff := by
      intro C result
      exact
        (CommonGround.ControllerInvocation.stageAttemptProtectedRealizes_of_framed
          (CommonGround.ControllerInvocation.stageAttemptFramedRealizes_of_witnessed
            h)).right C result }

theorem controllerStageAttemptFramedInvocationRoute_of_realizes
    {attempt invoker : MachineDescription}
    (h :
      CommonGround.ControllerInvocation.StageAttemptFramedRealizes
        attempt invoker) :
    ControllerStageAttemptFramedInvocationRoute attempt invoker :=
  { realizes := h
    subroutineReady := h.left
    framedForward := h.right.left
    framedClosed := h.right.right
    witnessedRealizes :=
      CommonGround.ControllerInvocation.stageAttemptWitnessedRealizes_of_framed
        h
    witnessedForward :=
      CommonGround.ControllerInvocation.stageAttemptWitnessedForwardSpec_of_framed
        h.right.left
    protectedRealizes :=
      CommonGround.ControllerInvocation.stageAttemptProtectedRealizes_of_framed
        h
    protectedIff := by
      intro C result
      exact
        (CommonGround.ControllerInvocation.stageAttemptProtectedRealizes_of_framed
          h).right C result
    outputOfWitness := by
      intro C result n hrun
      exact h.right.left C result ⟨n, hrun⟩
    witnessOfOutput := by
      intro C result hrun
      exact h.right.right C result hrun }

/-!
## Protected invocation route
-/

structure ControllerStageAttemptProtectedInvocationRoute
    (attempt invoker : MachineDescription) : Prop where
  realizes :
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker
  commonGroundRealizes :
    CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
      attempt invoker
  subroutineReady :
    invoker.SubroutineReady
  protectedIff :
    forall C : DovetailControllerLayout,
    forall result : Word Bool,
      invoker.HaltsWithOutput
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C))
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.withResult C result))) <->
        attempt.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageInputCode C))
          (encodeCodeWordAsInput (encodeBoolWord result))
  framedRealizes :
    CommonGround.ControllerInvocation.StageAttemptFramedRealizes
      attempt invoker
  framedRoute :
    ControllerStageAttemptFramedInvocationRoute attempt invoker
  attemptOutputFunctional :
    forall C : DovetailControllerLayout,
    forall result1 result2 : Word Bool,
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput (encodeBoolWord result1)) ->
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput (encodeBoolWord result2)) ->
        result1 = result2
  rawOutputFunctional :
    forall C : DovetailControllerLayout,
    forall result1 result2 out1 out2 : Word Bool,
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput (encodeBoolWord result1)) ->
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput (encodeBoolWord result2)) ->
      PairedRecognizerDovetailControllerRawOutput result1 = some out1 ->
      PairedRecognizerDovetailControllerRawOutput result2 = some out2 ->
        out1 = out2
  rawOutputBoolFunctional :
    forall C : DovetailControllerLayout,
    forall result1 result2 : Word Bool,
    forall b1 b2 : Bool,
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput (encodeBoolWord result1)) ->
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput (encodeBoolWord result2)) ->
      PairedRecognizerDovetailControllerRawOutput result1 = some [b1] ->
      PairedRecognizerDovetailControllerRawOutput result2 = some [b2] ->
        b1 = b2

theorem controllerStageAttemptProtectedInvocationRoute_of_realizes
    {attempt invoker : MachineDescription}
    (h :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker) :
    ControllerStageAttemptProtectedInvocationRoute attempt invoker :=
  { realizes := h
    commonGroundRealizes := h
    subroutineReady := h.left
    protectedIff := h.right
    framedRealizes :=
      CommonGround.ControllerInvocation.stageAttemptFramedRealizes_of_protected
        h
    framedRoute :=
      controllerStageAttemptFramedInvocationRoute_of_realizes
        (CommonGround.ControllerInvocation.stageAttemptFramedRealizes_of_protected
          h)
    attemptOutputFunctional := by
      intro C result1 result2 h1 h2
      exact
        pairedRecognizerDovetailStageAttemptProtectedInvocation_attempt_output_functional
          h C h1 h2
    rawOutputFunctional := by
      intro C result1 result2 out1 out2 h1 h2 hraw1 hraw2
      exact
        pairedRecognizerDovetailStageAttemptProtectedInvocation_rawOutput_functional
          h C h1 h2 hraw1 hraw2
    rawOutputBoolFunctional := by
      intro C result1 result2 b1 b2 h1 h2 hraw1 hraw2
      exact
        pairedRecognizerDovetailStageAttemptProtectedInvocation_rawOutput_bool_functional
          h C h1 h2 hraw1 hraw2 }

/-!
## Exact framed route
-/

structure ControllerStageAttemptFramedExactInvocationRoute
    (attempt invoker : MachineDescription) : Prop where
  exactSpec :
    CommonGround.ControllerInvocation.StageAttemptFramedExactSpec
      attempt invoker
  subroutineReady :
    invoker.SubroutineReady
  exactForwardTape :
    forall C : DovetailControllerLayout,
    forall result : Word Bool,
    forall n : Nat,
      attempt.HaltsWithOutputIn n
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailControllerStageInputCode C))
        (encodeCodeWordAsInput (encodeBoolWord result)) ->
      invoker.HaltsWithTape
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode C))
        (CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
          C result)
  framedClosed :
    CommonGround.ControllerInvocation.StageAttemptFramedClosedSpec
      attempt invoker
  framedRealizes :
    CommonGround.ControllerInvocation.StageAttemptFramedRealizes
      attempt invoker
  framedRoute :
    ControllerStageAttemptFramedInvocationRoute attempt invoker
  protectedRoute :
    ControllerStageAttemptProtectedInvocationRoute attempt invoker

def ControllerStageAttemptFramedExactInvocationRouteConstruction :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists invoker : MachineDescription,
        ControllerStageAttemptFramedExactInvocationRoute attempt invoker

theorem controllerStageAttemptFramedExactInvocationRoute_of_spec
    {attempt invoker : MachineDescription}
    (h :
      CommonGround.ControllerInvocation.StageAttemptFramedExactSpec
        attempt invoker) :
    ControllerStageAttemptFramedExactInvocationRoute attempt invoker := by
  let hframed :
      CommonGround.ControllerInvocation.StageAttemptFramedRealizes
        attempt invoker :=
    CommonGround.ControllerInvocation.stageAttemptFramedRealizes_of_exact h
  let hprotected :
      CommonGround.ControllerInvocation.StageAttemptProtectedRealizes
        attempt invoker :=
    CommonGround.ControllerInvocation.stageAttemptProtectedRealizes_of_framed
      hframed
  exact
    { exactSpec := h
      subroutineReady := h.left
      exactForwardTape := h.right.left
      framedClosed := h.right.right
      framedRealizes := hframed
      framedRoute :=
        controllerStageAttemptFramedInvocationRoute_of_realizes hframed
      protectedRoute :=
        controllerStageAttemptProtectedInvocationRoute_of_realizes
          hprotected }

theorem controllerStageAttemptFramedExactInvocationRouteConstruction_of_exact
    (h :
      CommonGround.ControllerInvocation.StageAttemptFramedExactConstruction) :
    ControllerStageAttemptFramedExactInvocationRouteConstruction := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨invoker, hinvoker⟩
  exact
    ⟨invoker,
      controllerStageAttemptFramedExactInvocationRoute_of_spec hinvoker⟩

/-!
## Public encoder-facing invocation route
-/

structure ControllerStageAttemptInvocationRoute
    (attempt encoder invoker : MachineDescription) : Prop where
  realizes :
    PairedRecognizerDovetailStageAttemptInvocationRealizes
      attempt encoder invoker
  subroutineReady :
    invoker.SubroutineReady
  forward :
    PairedRecognizerDovetailStageAttemptInvocationForwardSpec
      attempt encoder invoker
  closed :
    PairedRecognizerDovetailStageAttemptInvocationClosedSpec
      attempt encoder invoker
  invocationIff :
    forall C : DovetailControllerLayout,
    forall result : Word Bool,
      invoker.HaltsWithOutput
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C))
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.withResult C result))) <->
        encoder.HaltsWithOutput
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode C))
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageInputCode C)) ∧
          attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerStageInputCode C))
            (encodeCodeWordAsInput (encodeBoolWord result))
  protectedRoute :
    exists protectedInvoker : MachineDescription,
      ControllerStageAttemptProtectedInvocationRoute
        attempt protectedInvoker

def ControllerStageAttemptInvocationRouteConstruction : Prop :=
  forall attempt encoder : MachineDescription,
    attempt.SubroutineReady ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder ->
    exists invoker : MachineDescription,
      ControllerStageAttemptInvocationRoute attempt encoder invoker

theorem controllerStageAttemptInvocationRoute_of_realizes
    {attempt encoder invoker : MachineDescription}
    (h :
      PairedRecognizerDovetailStageAttemptInvocationRealizes
        attempt encoder invoker)
    (hprotected :
      exists protectedInvoker : MachineDescription,
        ControllerStageAttemptProtectedInvocationRoute
          attempt protectedInvoker) :
    ControllerStageAttemptInvocationRoute attempt encoder invoker :=
  { realizes := h
    subroutineReady := h.left
    forward := by
      intro C result hrun
      exact (h.right C result).mpr hrun
    closed := by
      intro C result hrun
      exact (h.right C result).mp hrun
    invocationIff := h.right
    protectedRoute := hprotected }

theorem controllerStageAttemptInvocationRouteConstruction_of_data
    (hdata :
      PairedRecognizerDovetailStageAttemptInvocationConstructionData)
    (hprotected :
      PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData) :
    ControllerStageAttemptInvocationRouteConstruction := by
  intro attempt encoder hattempt hencoder
  rcases hdata attempt encoder hattempt hencoder with
    ⟨invoker, hready, hforward, hclosed⟩
  rcases hprotected attempt hattempt with
    ⟨protectedInvoker, hprotectedInvoker⟩
  let hrealizes :
      PairedRecognizerDovetailStageAttemptInvocationRealizes
        attempt encoder invoker :=
    pairedRecognizerDovetailStageAttemptInvocationRealizes_of_forward_closed
      hready hforward hclosed
  exact
    ⟨invoker,
      controllerStageAttemptInvocationRoute_of_realizes hrealizes
        ⟨protectedInvoker,
          controllerStageAttemptProtectedInvocationRoute_of_realizes
            hprotectedInvoker⟩⟩

theorem controllerStageAttemptInvocationRouteConstruction_of_construction
    (h :
      PairedRecognizerDovetailStageAttemptInvocationConstruction)
    (hprotected :
      PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData) :
    ControllerStageAttemptInvocationRouteConstruction := by
  intro attempt encoder hattempt hencoder
  rcases h attempt encoder hattempt hencoder with ⟨invoker, hinvoker⟩
  rcases hprotected attempt hattempt with
    ⟨protectedInvoker, hprotectedInvoker⟩
  exact
    ⟨invoker,
      controllerStageAttemptInvocationRoute_of_realizes hinvoker
        ⟨protectedInvoker,
          controllerStageAttemptProtectedInvocationRoute_of_realizes
            hprotectedInvoker⟩⟩

/-!
## Handoff and closed-handoff route surfaces
-/

structure ControllerStageAttemptInvocationHandoffRoute : Prop where
  outputConstruction :
    PairedRecognizerDovetailStageAttemptInvocationConstruction
  handoffConstruction :
    PairedRecognizerDovetailStageAttemptInvocationHandoffConstruction
  closedHandoffConstruction :
    PairedRecognizerDovetailStageAttemptInvocationClosedHandoffConstruction
  routeConstruction :
    ControllerStageAttemptInvocationRouteConstruction

def ControllerStageAttemptInvocationHandoffRouteConstruction : Prop :=
  ControllerStageAttemptInvocationHandoffRoute

theorem controllerStageAttemptInvocationHandoffRoute_of_output
    (houtput :
      PairedRecognizerDovetailStageAttemptInvocationConstruction)
    (hprotected :
      PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData) :
    ControllerStageAttemptInvocationHandoffRoute :=
  { outputConstruction := houtput
    handoffConstruction :=
      pairedRecognizerDovetailStageAttemptInvocationHandoffConstruction_of_output
        houtput
    closedHandoffConstruction :=
      pairedRecognizerDovetailStageAttemptInvocationClosedHandoffConstruction_of_handoff
        (pairedRecognizerDovetailStageAttemptInvocationHandoffConstruction_of_output
          houtput)
    routeConstruction :=
      controllerStageAttemptInvocationRouteConstruction_of_construction
        houtput hprotected }

/-!
## Finite construction bundle
-/

structure ControllerStageAttemptInvocationFiniteRoute : Prop where
  framedConstruction :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData
  protectedConstruction :
    PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData
  invocationData :
    PairedRecognizerDovetailStageAttemptInvocationConstructionData
  invocationConstruction :
    PairedRecognizerDovetailStageAttemptInvocationConstruction
  handoffConstruction :
    PairedRecognizerDovetailStageAttemptInvocationHandoffConstruction
  closedHandoffConstruction :
    PairedRecognizerDovetailStageAttemptInvocationClosedHandoffConstruction
  routeConstruction :
    ControllerStageAttemptInvocationRouteConstruction
  handoffRoute :
    ControllerStageAttemptInvocationHandoffRoute
  framedRoute :
    forall attempt : MachineDescription,
      attempt.SubroutineReady ->
        exists invoker : MachineDescription,
          ControllerStageAttemptFramedInvocationRoute attempt invoker
  protectedRoute :
    forall attempt : MachineDescription,
      attempt.SubroutineReady ->
        exists invoker : MachineDescription,
          ControllerStageAttemptProtectedInvocationRoute attempt invoker

def ControllerStageAttemptInvocationFiniteRouteConstruction : Prop :=
  ControllerStageAttemptInvocationFiniteRoute

theorem controllerStageAttemptInvocationFiniteRoute_of_framed
    (hframed :
      PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData) :
    ControllerStageAttemptInvocationFiniteRoute := by
  let hprotected :
      PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData :=
    pairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData_of_framedRun
      hframed
  let hdata :
      PairedRecognizerDovetailStageAttemptInvocationConstructionData :=
    pairedRecognizerDovetailStageAttemptInvocationConstructionData_of_protected
      hprotected
  let hconstruction :
      PairedRecognizerDovetailStageAttemptInvocationConstruction :=
    pairedRecognizerDovetailStageAttemptInvocationConstruction_of_data
      hdata
  exact
    { framedConstruction := hframed
      protectedConstruction := hprotected
      invocationData := hdata
      invocationConstruction := hconstruction
      handoffConstruction :=
        pairedRecognizerDovetailStageAttemptInvocationHandoffConstruction_of_output
          hconstruction
      closedHandoffConstruction :=
        pairedRecognizerDovetailStageAttemptInvocationClosedHandoffConstruction_of_handoff
          (pairedRecognizerDovetailStageAttemptInvocationHandoffConstruction_of_output
            hconstruction)
      routeConstruction :=
        controllerStageAttemptInvocationRouteConstruction_of_data
          hdata hprotected
      handoffRoute :=
        controllerStageAttemptInvocationHandoffRoute_of_output
          hconstruction hprotected
      framedRoute := by
        intro attempt hattempt
        rcases hframed attempt hattempt with ⟨invoker, hinvoker⟩
        exact
          ⟨invoker,
            controllerStageAttemptFramedInvocationRoute_of_realizes
              hinvoker⟩
      protectedRoute := by
        intro attempt hattempt
        rcases hprotected attempt hattempt with ⟨invoker, hinvoker⟩
        exact
          ⟨invoker,
            controllerStageAttemptProtectedInvocationRoute_of_realizes
              hinvoker⟩ }

theorem controllerStageAttemptInvocationFiniteRoute_finiteLeaf :
    ControllerStageAttemptInvocationFiniteRoute :=
  controllerStageAttemptInvocationFiniteRoute_of_framed
    pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_scaffold

theorem controllerStageAttemptInvocationFiniteRouteConstruction_finiteLeaf :
    ControllerStageAttemptInvocationFiniteRouteConstruction :=
  controllerStageAttemptInvocationFiniteRoute_finiteLeaf

/-!
## Public finite-leaf aliases
-/

theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_route :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData :=
  controllerStageAttemptInvocationFiniteRoute_finiteLeaf.framedConstruction

theorem pairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData_route :
    PairedRecognizerDovetailStageAttemptProtectedInvocationConstructionData :=
  controllerStageAttemptInvocationFiniteRoute_finiteLeaf.protectedConstruction

theorem pairedRecognizerDovetailStageAttemptInvocationConstructionData_route :
    PairedRecognizerDovetailStageAttemptInvocationConstructionData :=
  controllerStageAttemptInvocationFiniteRoute_finiteLeaf.invocationData

theorem pairedRecognizerDovetailStageAttemptInvocationConstruction_route :
    PairedRecognizerDovetailStageAttemptInvocationConstruction :=
  controllerStageAttemptInvocationFiniteRoute_finiteLeaf.invocationConstruction

theorem pairedRecognizerDovetailStageAttemptInvocationHandoffConstruction_route :
    PairedRecognizerDovetailStageAttemptInvocationHandoffConstruction :=
  controllerStageAttemptInvocationFiniteRoute_finiteLeaf.handoffConstruction

theorem pairedRecognizerDovetailStageAttemptInvocationClosedHandoffConstruction_route :
    PairedRecognizerDovetailStageAttemptInvocationClosedHandoffConstruction :=
  controllerStageAttemptInvocationFiniteRoute_finiteLeaf.closedHandoffConstruction

theorem controllerStageAttemptInvocationRouteConstruction_finiteLeaf :
    ControllerStageAttemptInvocationRouteConstruction :=
  controllerStageAttemptInvocationFiniteRoute_finiteLeaf.routeConstruction

theorem controllerStageAttemptInvocationHandoffRouteConstruction_finiteLeaf :
    ControllerStageAttemptInvocationHandoffRouteConstruction :=
  controllerStageAttemptInvocationFiniteRoute_finiteLeaf.handoffRoute

end Computability
end FoC
