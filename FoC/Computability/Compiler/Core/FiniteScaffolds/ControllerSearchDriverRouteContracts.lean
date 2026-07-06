import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerSearchDriver
import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerFuelPairSearchRouteContracts
import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerInvocationRouteContracts
import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerOutputLevelSimulatorRouteContracts

set_option doc.verso true

/-!
# Controller search-driver route contracts

This module packages the controller search-driver composition surface.  The
component finite leaves remain in the invocation, simulator, and fuel-pair
modules; the route contracts here expose the public path from protected
stage-attempt invocation and exact-fuel pair search to the finite stage-loop
controller construction.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-!
## Total stage-attempt search-driver route
-/

structure ControllerStageAttemptSearchDriverRoute
    (attempt decider : MachineDescription) : Prop where
  realizes :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
      attempt decider
  wellFormed :
    decider.WellFormed
  searchIff :
    forall w : Word Bool,
    forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]
  forward :
    PairedRecognizerDovetailFiniteStageLoopForwardSpec
      attempt decider
  closed :
    PairedRecognizerDovetailFiniteStageLoopClosedSpec
      attempt decider
  toAttemptOutput :
    forall w : Word Bool,
    forall b : Bool,
      decider.HaltsWithOutput w [b] ->
        exists limit : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]
  ofAttemptOutput :
    forall w : Word Bool,
    forall b : Bool,
    forall limit : Nat,
    forall result : Word Bool,
      attempt.HaltsWithOutput
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (encodeCodeWordAsInput (encodeBoolWord result)) ->
      PairedRecognizerDovetailControllerRawOutput result = some [b] ->
        decider.HaltsWithOutput w [b]

def ControllerStageAttemptSearchDriverRouteConstruction :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists decider : MachineDescription,
        ControllerStageAttemptSearchDriverRoute attempt decider

theorem controllerStageAttemptSearchDriverRoute_of_realizes
    {attempt decider : MachineDescription}
    (h :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider) :
    ControllerStageAttemptSearchDriverRoute attempt decider :=
  { realizes := h
    wellFormed := h.left
    searchIff := h.right
    forward := by
      intro w b htarget
      exact (h.right w b).mpr htarget
    closed := by
      intro w b hhalt
      exact (h.right w b).mp hhalt
    toAttemptOutput := by
      intro w b hhalt
      exact (h.right w b).mp hhalt
    ofAttemptOutput := by
      intro w b limit result hattempt hraw
      exact (h.right w b).mpr ⟨limit, result, hattempt, hraw⟩ }

theorem controllerStageAttemptSearchDriverRoute_of_forward_closed
    {attempt decider : MachineDescription}
    (hwell : decider.WellFormed)
    (hforward :
      PairedRecognizerDovetailFiniteStageLoopForwardSpec
        attempt decider)
    (hclosed :
      PairedRecognizerDovetailFiniteStageLoopClosedSpec
        attempt decider) :
    ControllerStageAttemptSearchDriverRoute attempt decider :=
  controllerStageAttemptSearchDriverRoute_of_realizes
    (pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_forward_closed
      hwell hforward hclosed)

theorem controllerStageAttemptSearchDriverRouteConstruction_of_construction
    (h :
      PairedRecognizerDovetailFiniteStageLoopControllerConstruction) :
    ControllerStageAttemptSearchDriverRouteConstruction := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨decider, hdecider⟩
  exact
    ⟨decider,
      controllerStageAttemptSearchDriverRoute_of_realizes hdecider⟩

/-!
## Fuel-search driver route
-/

structure ControllerStageAttemptFuelSearchDriverRoute
    (attempt decider : MachineDescription) : Prop where
  fuelRealizes :
    PairedRecognizerDovetailTotalStageAttemptControllerFuelSearchDriverRealizes
      attempt decider
  wellFormed :
    decider.WellFormed
  fuelSearchIff :
    forall w : Word Bool,
    forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists fuel : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutputIn fuel
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]
  totalRealizes :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
      attempt decider
  totalRoute :
    ControllerStageAttemptSearchDriverRoute attempt decider
  toFuelOutput :
    forall w : Word Bool,
    forall b : Bool,
      decider.HaltsWithOutput w [b] ->
        exists limit : Nat,
        exists fuel : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutputIn fuel
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]
  ofFuelOutput :
    forall w : Word Bool,
    forall b : Bool,
    forall limit fuel : Nat,
    forall result : Word Bool,
      attempt.HaltsWithOutputIn fuel
        (encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (encodeCodeWordAsInput (encodeBoolWord result)) ->
      PairedRecognizerDovetailControllerRawOutput result = some [b] ->
        decider.HaltsWithOutput w [b]

def ControllerStageAttemptFuelSearchDriverRouteConstruction :
    Prop :=
  forall attempt invoker : MachineDescription,
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker ->
      exists decider : MachineDescription,
        ControllerStageAttemptFuelSearchDriverRoute attempt decider

theorem controllerStageAttemptFuelSearchDriverRoute_of_realizes
    {attempt decider : MachineDescription}
    (h :
      PairedRecognizerDovetailTotalStageAttemptControllerFuelSearchDriverRealizes
        attempt decider) :
    ControllerStageAttemptFuelSearchDriverRoute attempt decider :=
  { fuelRealizes := h
    wellFormed := h.left
    fuelSearchIff := h.right
    totalRealizes :=
      pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_fuel
        h
    totalRoute :=
      controllerStageAttemptSearchDriverRoute_of_realizes
        (pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_fuel
          h)
    toFuelOutput := by
      intro w b hhalt
      exact (h.right w b).mp hhalt
    ofFuelOutput := by
      intro w b limit fuel result hattempt hraw
      exact (h.right w b).mpr
        ⟨limit, fuel, result, hattempt, hraw⟩ }

theorem controllerStageAttemptFuelSearchDriverRouteConstruction_of_construction
    (h :
      PairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction) :
    ControllerStageAttemptFuelSearchDriverRouteConstruction := by
  intro attempt invoker hinvoker
  rcases h attempt invoker hinvoker with ⟨decider, hdecider⟩
  exact
    ⟨decider,
      controllerStageAttemptFuelSearchDriverRoute_of_realizes hdecider⟩

/-!
## Protected search-driver route
-/

structure ProtectedControllerStageAttemptSearchDriverRoute
    (attempt invoker decider : MachineDescription) : Prop where
  protectedInvocation :
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker
  searchRealizes :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
      attempt decider
  searchRoute :
    ControllerStageAttemptSearchDriverRoute attempt decider
  wellFormed :
    decider.WellFormed
  searchIff :
    forall w : Word Bool,
    forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
        exists result : Word Bool,
          attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]

def ProtectedControllerStageAttemptSearchDriverRouteConstruction :
    Prop :=
  forall attempt invoker : MachineDescription,
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker ->
      exists decider : MachineDescription,
        ProtectedControllerStageAttemptSearchDriverRoute
          attempt invoker decider

theorem protectedControllerStageAttemptSearchDriverRoute_of_realizes
    {attempt invoker decider : MachineDescription}
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (hdecider :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider) :
    ProtectedControllerStageAttemptSearchDriverRoute
      attempt invoker decider :=
  { protectedInvocation := hinvoker
    searchRealizes := hdecider
    searchRoute :=
      controllerStageAttemptSearchDriverRoute_of_realizes hdecider
    wellFormed := hdecider.left
    searchIff := hdecider.right }

theorem protectedControllerStageAttemptSearchDriverRouteConstruction_of_construction
    (h :
      PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction) :
    ProtectedControllerStageAttemptSearchDriverRouteConstruction := by
  intro attempt invoker hinvoker
  rcases h attempt invoker hinvoker with ⟨decider, hdecider⟩
  exact
    ⟨decider,
      protectedControllerStageAttemptSearchDriverRoute_of_realizes
        hinvoker hdecider⟩

theorem protectedControllerStageAttemptSearchDriverRouteConstruction_of_fuel
    (h :
      PairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction) :
    ProtectedControllerStageAttemptSearchDriverRouteConstruction :=
  protectedControllerStageAttemptSearchDriverRouteConstruction_of_construction
    (pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction_of_fuel
      h)

/-!
## Search-driver construction bundle
-/

structure ProtectedControllerStageAttemptSearchDriverConstructionRoute :
    Prop where
  exactFuelRunner :
    PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction
  fuelPairSearch :
    PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction
  fuelConstruction :
    PairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction
  searchConstruction :
    PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction
  fuelRouteConstruction :
    ControllerStageAttemptFuelSearchDriverRouteConstruction
  protectedRouteConstruction :
    ProtectedControllerStageAttemptSearchDriverRouteConstruction

def ProtectedControllerStageAttemptSearchDriverConstructionRouteConstruction :
    Prop :=
  ProtectedControllerStageAttemptSearchDriverConstructionRoute

theorem protectedControllerStageAttemptSearchDriverConstructionRoute_of_components
    (hrunner :
      PairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction)
    (hsearch :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchConstruction) :
    ProtectedControllerStageAttemptSearchDriverConstructionRoute := by
  let hfuel :
      PairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction :=
    pairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction_of_exactFuelRunner_and_pairSearch
      hrunner hsearch
  let hprotected :
      PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction :=
    pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction_of_fuel
      hfuel
  exact
    { exactFuelRunner := hrunner
      fuelPairSearch := hsearch
      fuelConstruction := hfuel
      searchConstruction := hprotected
      fuelRouteConstruction :=
        controllerStageAttemptFuelSearchDriverRouteConstruction_of_construction
          hfuel
      protectedRouteConstruction :=
        protectedControllerStageAttemptSearchDriverRouteConstruction_of_construction
          hprotected }

/-!
## Finite stage-loop sequencing route
-/

structure FiniteStageLoopSequencingRoute
    (attempt initializer encoder invoker emitter continuer decider :
      MachineDescription) : Prop where
  wellFormed :
    decider.WellFormed
  forward :
    PairedRecognizerDovetailFiniteStageLoopForwardSpec
      attempt decider
  closed :
    PairedRecognizerDovetailFiniteStageLoopClosedSpec
      attempt decider
  totalRealizes :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
      attempt decider
  totalRoute :
    ControllerStageAttemptSearchDriverRoute attempt decider
  initializerRealizes :
    PairedRecognizerDovetailControllerInputInitializerRealizes
      initializer
  encoderCompiled :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder
  invokerRealizes :
    PairedRecognizerDovetailStageAttemptInvocationRealizes
      attempt encoder invoker
  emitterRealizes :
    PairedRecognizerDovetailControllerResultEmitterRealizes
      emitter
  continuerRealizes :
    PairedRecognizerDovetailControllerContinueRealizes
      continuer

def FiniteStageLoopSequencingRouteConstruction : Prop :=
  forall attempt initializer encoder invoker emitter continuer :
      MachineDescription,
    attempt.SubroutineReady ->
    PairedRecognizerDovetailControllerInputInitializerRealizes
      initializer ->
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      encoder ->
    PairedRecognizerDovetailStageAttemptInvocationRealizes
      attempt encoder invoker ->
    PairedRecognizerDovetailControllerResultEmitterRealizes
      emitter ->
    PairedRecognizerDovetailControllerContinueRealizes
      continuer ->
    exists decider : MachineDescription,
      FiniteStageLoopSequencingRoute
        attempt initializer encoder invoker emitter continuer decider

theorem finiteStageLoopSequencingRouteConstruction_of_data
    (h :
      PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData) :
    FiniteStageLoopSequencingRouteConstruction := by
  intro attempt initializer encoder invoker emitter continuer
    hattempt hinitializer hencoder hinvoker hemitter hcontinuer
  rcases h attempt initializer encoder invoker emitter continuer
      hattempt hinitializer hencoder hinvoker hemitter hcontinuer with
    ⟨decider, hwell, hforward, hclosed⟩
  let htotal :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider :=
    pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_forward_closed
      hwell hforward hclosed
  exact
    ⟨decider,
      { wellFormed := hwell
        forward := hforward
        closed := hclosed
        totalRealizes := htotal
        totalRoute :=
          controllerStageAttemptSearchDriverRoute_of_realizes htotal
        initializerRealizes := hinitializer
        encoderCompiled := hencoder
        invokerRealizes := hinvoker
        emitterRealizes := hemitter
        continuerRealizes := hcontinuer }⟩

theorem finiteStageLoopSequencingRouteConstruction_of_construction
    (h :
      PairedRecognizerDovetailFiniteStageLoopSequencingConstruction) :
    FiniteStageLoopSequencingRouteConstruction := by
  intro attempt initializer encoder invoker emitter continuer
    hattempt hinitializer hencoder hinvoker hemitter hcontinuer
  rcases h attempt initializer encoder invoker emitter continuer
      hattempt hinitializer hencoder hinvoker hemitter hcontinuer with
    ⟨decider, hdecider⟩
  exact
    ⟨decider,
      { wellFormed := hdecider.left
        forward := by
          intro w b htarget
          exact (hdecider.right w b).mpr htarget
        closed := by
          intro w b hhalt
          exact (hdecider.right w b).mp hhalt
        totalRealizes := hdecider
        totalRoute :=
          controllerStageAttemptSearchDriverRoute_of_realizes hdecider
        initializerRealizes := hinitializer
        encoderCompiled := hencoder
        invokerRealizes := hinvoker
        emitterRealizes := hemitter
        continuerRealizes := hcontinuer }⟩

/-!
## Protected finite stage-loop sequencing route
-/

structure ProtectedFiniteStageLoopSequencingRoute
    (attempt initializer invoker emitter continuer decider :
      MachineDescription) : Prop where
  wellFormed :
    decider.WellFormed
  forward :
    PairedRecognizerDovetailFiniteStageLoopForwardSpec
      attempt decider
  closed :
    PairedRecognizerDovetailFiniteStageLoopClosedSpec
      attempt decider
  totalRealizes :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
      attempt decider
  totalRoute :
    ControllerStageAttemptSearchDriverRoute attempt decider
  initializer :
    PairedRecognizerDovetailControllerInputInitializerRealizes
      initializer
  protectedInvoker :
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker
  emitter :
    PairedRecognizerDovetailControllerResultEmitterRealizes
      emitter
  continuer :
    PairedRecognizerDovetailControllerContinueRealizes
      continuer

def ProtectedFiniteStageLoopSequencingRouteConstruction : Prop :=
  forall attempt initializer invoker emitter continuer : MachineDescription,
    PairedRecognizerDovetailControllerInputInitializerRealizes
      initializer ->
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker ->
    PairedRecognizerDovetailControllerResultEmitterRealizes
      emitter ->
    PairedRecognizerDovetailControllerContinueRealizes
      continuer ->
    exists decider : MachineDescription,
      ProtectedFiniteStageLoopSequencingRoute
        attempt initializer invoker emitter continuer decider

theorem protectedFiniteStageLoopSequencingRouteConstruction_of_data
    (h :
      PairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData) :
    ProtectedFiniteStageLoopSequencingRouteConstruction := by
  intro attempt initializer invoker emitter continuer
    hinitializer hinvoker hemitter hcontinuer
  rcases h attempt initializer invoker emitter continuer
      hinitializer hinvoker hemitter hcontinuer with
    ⟨decider, hwell, hforward, hclosed⟩
  let htotal :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider :=
    pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_forward_closed
      hwell hforward hclosed
  exact
    ⟨decider,
      { wellFormed := hwell
        forward := hforward
        closed := hclosed
        totalRealizes := htotal
        totalRoute :=
          controllerStageAttemptSearchDriverRoute_of_realizes htotal
        initializer := hinitializer
        protectedInvoker := hinvoker
        emitter := hemitter
        continuer := hcontinuer }⟩

/-!
## Controller assembly route
-/

structure FiniteStageLoopControllerRoute
    (attempt decider : MachineDescription) : Prop where
  controllerConstruction :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction
  attemptReady :
    attempt.SubroutineReady
  searchRoute :
    ControllerStageAttemptSearchDriverRoute attempt decider
  searchRealizes :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
      attempt decider
  wellFormed :
    decider.WellFormed

def FiniteStageLoopControllerRouteConstruction : Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      exists decider : MachineDescription,
        FiniteStageLoopControllerRoute attempt decider

theorem finiteStageLoopControllerRouteConstruction_of_construction
    (h :
      PairedRecognizerDovetailFiniteStageLoopControllerConstruction) :
    FiniteStageLoopControllerRouteConstruction := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨decider, hdecider⟩
  exact
    ⟨decider,
      { controllerConstruction := h
        attemptReady := hattempt
        searchRoute :=
          controllerStageAttemptSearchDriverRoute_of_realizes hdecider
        searchRealizes := hdecider
        wellFormed := hdecider.left }⟩

/-!
## Finite construction bundle
-/

structure ControllerSearchDriverFiniteRoute : Prop where
  protectedFuelSearch :
    PairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction
  protectedSearch :
    PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction
  protectedSearchRoute :
    ProtectedControllerStageAttemptSearchDriverRouteConstruction
  fuelSearchRoute :
    ControllerStageAttemptFuelSearchDriverRouteConstruction
  protectedSequencingData :
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData
  protectedSequencingRoute :
    ProtectedFiniteStageLoopSequencingRouteConstruction
  sequencingData :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData
  sequencing :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstruction
  sequencingRoute :
    FiniteStageLoopSequencingRouteConstruction
  handoff :
    PairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction
  controller :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction
  controllerRoute :
    FiniteStageLoopControllerRouteConstruction

def ControllerSearchDriverFiniteRouteConstruction : Prop :=
  ControllerSearchDriverFiniteRoute

theorem controllerSearchDriverFiniteRoute_finiteLeaf :
    ControllerSearchDriverFiniteRoute :=
  { protectedFuelSearch :=
      pairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction_finite_leaf
    protectedSearch :=
      pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction_finite_leaf
    protectedSearchRoute :=
      protectedControllerStageAttemptSearchDriverRouteConstruction_of_construction
        pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction_finite_leaf
    fuelSearchRoute :=
      controllerStageAttemptFuelSearchDriverRouteConstruction_of_construction
        pairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction_finite_leaf
    protectedSequencingData :=
      pairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData_scaffold
    protectedSequencingRoute :=
      protectedFiniteStageLoopSequencingRouteConstruction_of_data
        pairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData_scaffold
    sequencingData :=
      pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_scaffold
    sequencing :=
      pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold
    sequencingRoute :=
      finiteStageLoopSequencingRouteConstruction_of_construction
        pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold
    handoff :=
      pairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction_scaffold
    controller :=
      pairedRecognizerDovetailFiniteStageLoopControllerConstruction_scaffold
    controllerRoute :=
      finiteStageLoopControllerRouteConstruction_of_construction
        pairedRecognizerDovetailFiniteStageLoopControllerConstruction_scaffold }

theorem controllerSearchDriverFiniteRouteConstruction_finiteLeaf :
    ControllerSearchDriverFiniteRouteConstruction :=
  controllerSearchDriverFiniteRoute_finiteLeaf

/-!
## Public finite-leaf aliases
-/

theorem pairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction_route :
    PairedRecognizerDovetailProtectedStageAttemptControllerFuelSearchDriverConstruction :=
  controllerSearchDriverFiniteRoute_finiteLeaf.protectedFuelSearch

theorem pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction_route :
    PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverConstruction :=
  controllerSearchDriverFiniteRoute_finiteLeaf.protectedSearch

theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData_route :
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData :=
  controllerSearchDriverFiniteRoute_finiteLeaf.protectedSequencingData

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_route :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData :=
  controllerSearchDriverFiniteRoute_finiteLeaf.sequencingData

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_route :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstruction :=
  controllerSearchDriverFiniteRoute_finiteLeaf.sequencing

theorem pairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction_route :
    PairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction :=
  controllerSearchDriverFiniteRoute_finiteLeaf.handoff

theorem pairedRecognizerDovetailFiniteStageLoopControllerConstruction_route :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction :=
  controllerSearchDriverFiniteRoute_finiteLeaf.controller

theorem controllerStageAttemptSearchDriverRouteConstruction_finiteLeaf :
    ProtectedControllerStageAttemptSearchDriverRouteConstruction :=
  controllerSearchDriverFiniteRoute_finiteLeaf.protectedSearchRoute

theorem controllerStageAttemptFuelSearchDriverRouteConstruction_finiteLeaf :
    ControllerStageAttemptFuelSearchDriverRouteConstruction :=
  controllerSearchDriverFiniteRoute_finiteLeaf.fuelSearchRoute

theorem finiteStageLoopSequencingRouteConstruction_finiteLeaf :
    FiniteStageLoopSequencingRouteConstruction :=
  controllerSearchDriverFiniteRoute_finiteLeaf.sequencingRoute

theorem finiteStageLoopControllerRouteConstruction_finiteLeaf :
    FiniteStageLoopControllerRouteConstruction :=
  controllerSearchDriverFiniteRoute_finiteLeaf.controllerRoute

end Computability
end FoC
