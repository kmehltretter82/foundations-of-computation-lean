import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerOutputLevelSimulator
import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerSearchDriverContracts
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.BoundedFuelPairSearch.Assembly

set_option doc.verso true

/-!
# Finite-source dovetail scaffolds

This module is part of the finite-source manifest for the dovetail controller
route.  It keeps concrete finite construction leaves separated from the wrapper
that re-exports them.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

theorem pairedRecognizerDovetailStageAttemptProtectedInvocationRealizes_of_invocation
    {attempt encoder invoker : MachineDescription}
    (hencoder :
      TapeCodePrimitiveOutputCompiledSubroutineByDescription
        PairedRecognizerDovetailControllerStageInputCodePrimitive
        encoder)
    (hinvoker :
      PairedRecognizerDovetailStageAttemptInvocationRealizes
        attempt encoder invoker) :
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker := by
  constructor
  · exact hinvoker.left
  · intro C result
    constructor
    · intro hrun
      exact ((hinvoker.right C result).mp hrun).right
    · intro hrun
      exact
        (hinvoker.right C result).mpr
          ⟨tapeCodePrimitiveOutputCompiledSubroutineByDescription_haltsWithOutput_of_transform_eq_some
              hencoder
              (pairedRecognizerDovetailControllerStageInputCode_encode C),
            hrun⟩

private def pairedRecognizerDovetailFiniteStageLoopStageLayout
    (w : Word Bool) (limit : Nat) :
    DovetailControllerLayout :=
  { input := w, stage := limit, result := [] }

/-- Forward behavior of one fixed-Boolean fiber of the protected sequencer. -/
def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberForwardSpec
    (initializer invoker emitter decider : MachineDescription)
    (b : Bool) : Prop :=
  forall w : Word Bool,
    (exists limit : Nat,
      exists result : Word Bool,
        initializer.HaltsWithOutput w
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerInitialCode w)) ∧
          invoker.HaltsWithOutput
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                (pairedRecognizerDovetailFiniteStageLoopStageLayout
                  w limit)))
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                (DovetailControllerLayout.withResult
                  (pairedRecognizerDovetailFiniteStageLoopStageLayout
                    w limit)
                  result))) ∧
          emitter.HaltsWithOutput
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                (DovetailControllerLayout.withResult
                  (pairedRecognizerDovetailFiniteStageLoopStageLayout
                    w limit)
                  result)))
            [b]) ->
      decider.HaltsWithOutput w [b]

/-- Closed behavior of one fixed-Boolean fiber of the protected sequencer. -/
def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberClosedSpec
    (initializer invoker emitter decider : MachineDescription)
    (b : Bool) : Prop :=
  forall w : Word Bool,
    decider.HaltsWithOutput w [b] ->
      exists limit : Nat,
      exists result : Word Bool,
        initializer.HaltsWithOutput w
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailControllerInitialCode w)) ∧
          invoker.HaltsWithOutput
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                (pairedRecognizerDovetailFiniteStageLoopStageLayout
                  w limit)))
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                (DovetailControllerLayout.withResult
                  (pairedRecognizerDovetailFiniteStageLoopStageLayout
                    w limit)
                  result))) ∧
          emitter.HaltsWithOutput
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encode
                (DovetailControllerLayout.withResult
                  (pairedRecognizerDovetailFiniteStageLoopStageLayout
                    w limit)
                  result)))
            [b]

/-- Continuation behavior shared by every fixed-Boolean sequencer fiber. -/
def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberContinueSpec
    (continuer : MachineDescription) : Prop :=
  forall C : DovetailControllerLayout,
    PairedRecognizerDovetailControllerRawOutput C.result = none ->
      continuer.HaltsWithOutput
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode C))
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C)))

/-- The first sequencer consumer in honest fixed-Boolean currency. -/
def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberRealizes
    (initializer invoker emitter continuer decider : MachineDescription)
    (b : Bool) : Prop :=
  decider.WellFormed ∧
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberContinueSpec
      continuer ∧
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberForwardSpec
      initializer invoker emitter decider b ∧
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberClosedSpec
      initializer invoker emitter decider b

theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberRealizes_of_searchDriverFamily
    {attempt initializer invoker emitter continuer : MachineDescription}
    {family : Bool -> MachineDescription}
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverFamilyRealizes
        attempt family)
    (hinitializer :
      PairedRecognizerDovetailControllerInputInitializerRealizes initializer)
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (hemitter :
      PairedRecognizerDovetailControllerResultEmitterRealizes emitter)
    (hcontinuer :
      PairedRecognizerDovetailControllerContinueRealizes continuer)
    (b : Bool) :
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberRealizes
      initializer invoker emitter continuer (family b) b := by
  rcases hdriver b with ⟨hwell, hdriverSpec⟩
  refine ⟨hwell, ?_, ?_, ?_⟩
  · intro C hraw
    exact (hcontinuer.right C).mpr hraw
  · intro w hstage
    rcases hstage with
      ⟨limit, result, _hinitialized, hinvoked, hemitted⟩
    apply (hdriverSpec w).mpr
    refine ⟨limit, result, ?_, ?_⟩
    · exact (hinvoker.right
        (pairedRecognizerDovetailFiniteStageLoopStageLayout w limit)
        result).mp hinvoked
    · exact (hemitter.right
        (DovetailControllerLayout.withResult
          (pairedRecognizerDovetailFiniteStageLoopStageLayout w limit)
          result)
        b).mp hemitted
  · intro w hhalt
    rcases (hdriverSpec w).mp hhalt with
      ⟨limit, result, hattempt, hraw⟩
    refine ⟨limit, result, hinitializer.right w, ?_, ?_⟩
    · exact (hinvoker.right
        (pairedRecognizerDovetailFiniteStageLoopStageLayout w limit)
        result).mpr hattempt
    · exact (hemitter.right
        (DovetailControllerLayout.withResult
          (pairedRecognizerDovetailFiniteStageLoopStageLayout w limit)
          result)
        b).mpr hraw

/-- Construction data for the first sequencer consumer, retaining the Boolean
index instead of requesting one scalar decider. -/
def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFamilyConstructionData :
    Prop :=
  forall attempt initializer invoker emitter continuer : MachineDescription,
    PairedRecognizerDovetailControllerInputInitializerRealizes initializer ->
    PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
      attempt invoker ->
    PairedRecognizerDovetailControllerResultEmitterRealizes emitter ->
    PairedRecognizerDovetailControllerContinueRealizes continuer ->
      exists family : Bool -> MachineDescription,
        forall b : Bool,
          PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberRealizes
            initializer invoker emitter continuer (family b) b

theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencerFamilyConstructionData_of_searchDriverFamily
    (hsearch :
      PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction) :
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFamilyConstructionData := by
  intro attempt initializer invoker emitter continuer
    hinitializer hinvoker hemitter hcontinuer
  rcases hsearch attempt invoker hinvoker with ⟨family, hfamily⟩
  exact
    ⟨family, fun b =>
      pairedRecognizerDovetailFiniteStageLoopProtectedSequencerFiberRealizes_of_searchDriverFamily
        hfamily hinitializer hinvoker hemitter hcontinuer b⟩

theorem pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction_of_searchFamily
    (hsearch :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamilyConstruction) :
    PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction :=
  pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction_of_route
    (protectedControllerStageAttemptFuelSearchDriverFamilyRouteConstruction_of_exactFuelRunner_and_searchFamily
      pairedRecognizerDovetailProtectedStageAttemptExactFuelRunnerConstruction_finite_leaf
      hsearch)

/-- The concrete output-indexed fuel-pair search supplies the first protected
controller search-driver family consumer. -/
theorem pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction_finiteLeaf :
    PairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction :=
  pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction_of_searchFamily
    StructuredConstructionTargets.boundedFuelPairSearchFamilyConstruction_core

theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencerFamilyConstructionData_of_searchFamily
    (hsearch :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamilyConstruction) :
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerFamilyConstructionData :=
  pairedRecognizerDovetailFiniteStageLoopProtectedSequencerFamilyConstructionData_of_searchDriverFamily
    (pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction_of_searchFamily
      hsearch)

/-- Assemble the arbitrary-attempt finite controller in family currency.  A
single scalar decider requires a later consumer with an honest cross-limit
premise and is deliberately not constructed here. -/
theorem pairedRecognizerDovetailFiniteStageLoopControllerFamilyConstruction_of_searchFamily
    (hsearch :
      PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamilyConstruction) :
    PairedRecognizerDovetailFiniteStageLoopControllerFamilyConstruction := by
  intro attempt hattempt
  rcases pairedRecognizerDovetailControllerStageInputEncoderConstruction_scaffold with
    ⟨encoder, hencoder⟩
  rcases
      pairedRecognizerDovetailStageAttemptInvocationConstruction_scaffold
        attempt encoder hattempt hencoder with
    ⟨invoker, hinvoker⟩
  exact
    pairedRecognizerDovetailProtectedStageAttemptControllerSearchDriverFamilyConstruction_of_searchFamily
      hsearch attempt invoker
      (pairedRecognizerDovetailStageAttemptProtectedInvocationRealizes_of_invocation
        hencoder hinvoker)

end Computability
end FoC
