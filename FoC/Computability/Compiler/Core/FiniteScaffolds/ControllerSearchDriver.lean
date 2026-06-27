import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerInvocation

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

def PairedRecognizerDovetailFiniteStageLoopForwardSpec
    (attempt decider : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall b : Bool,
    (exists limit : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]) ->
      decider.HaltsWithOutput w [b]

def PairedRecognizerDovetailFiniteStageLoopClosedSpec
    (attempt decider : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall b : Bool,
    decider.HaltsWithOutput w [b] ->
      exists limit : Nat,
      exists result : Word Bool,
        attempt.HaltsWithOutput
            (encodeCodeWordAsInput
              (PairedRecognizerDovetailStageInputCode w limit))
            (encodeCodeWordAsInput
              (encodeBoolWord result)) ∧
          PairedRecognizerDovetailControllerRawOutput result = some [b]

theorem pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_forward_closed
    {attempt decider : MachineDescription}
    (hwell : decider.WellFormed)
    (hforward :
      PairedRecognizerDovetailFiniteStageLoopForwardSpec
        attempt decider)
    (hclosed :
      PairedRecognizerDovetailFiniteStageLoopClosedSpec
        attempt decider) :
    PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
      attempt decider := by
  constructor
  · exact hwell
  · intro w b
    constructor
    · exact hclosed w b
    · exact hforward w b

def PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData :
    Prop :=
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
      decider.WellFormed ∧
        PairedRecognizerDovetailFiniteStageLoopForwardSpec
          attempt decider ∧
        PairedRecognizerDovetailFiniteStageLoopClosedSpec
          attempt decider

def PairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData :
    Prop :=
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
      decider.WellFormed ∧
        PairedRecognizerDovetailFiniteStageLoopForwardSpec
          attempt decider ∧
        PairedRecognizerDovetailFiniteStageLoopClosedSpec
          attempt decider

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

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_of_protected
    (h :
      PairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData) :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData := by
  intro attempt initializer encoder invoker emitter continuer
    _hattempt hinitializer hencoder hinvoker hemitter hcontinuer
  exact
    h attempt initializer invoker emitter continuer
      hinitializer
      (pairedRecognizerDovetailStageAttemptProtectedInvocationRealizes_of_invocation
        hencoder hinvoker)
      hemitter hcontinuer

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_of_data
    (h :
      PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData) :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstruction := by
  intro attempt initializer encoder invoker emitter continuer
    hattempt hinitializer hencoder hinvoker hemitter hcontinuer
  rcases h attempt initializer encoder invoker emitter continuer
      hattempt hinitializer hencoder hinvoker hemitter hcontinuer with
    ⟨decider, hwell, hforward, hclosed⟩
  exact
    ⟨decider,
      pairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes_of_forward_closed
        hwell hforward hclosed⟩

private def pairedRecognizerDovetailFiniteStageLoopStageLayout
    (w : Word Bool) (limit : Nat) :
    DovetailControllerLayout :=
  { input := w, stage := limit, result := [] }

private def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerForwardSpec
    (initializer invoker emitter decider : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall b : Bool,
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

private def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerClosedSpec
    (initializer invoker emitter decider : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall b : Bool,
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

private def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerContinueSpec
    (continuer : MachineDescription) : Prop :=
  forall C : DovetailControllerLayout,
    PairedRecognizerDovetailControllerRawOutput C.result = none ->
      continuer.HaltsWithOutput
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode C))
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.nextStage C)))

private def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes
    (initializer invoker emitter continuer decider : MachineDescription) :
    Prop :=
  decider.WellFormed ∧
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerContinueSpec
      continuer ∧
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerForwardSpec
      initializer invoker emitter decider ∧
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerClosedSpec
      initializer invoker emitter decider

private def PairedRecognizerDovetailFiniteStageLoopProtectedSequencerSearchDriverData :
    Prop :=
  forall attempt : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider

private theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes_of_searchDriver
    {attempt initializer invoker emitter continuer decider : MachineDescription}
    (hdriver :
      PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverRealizes
        attempt decider)
    (hinitializer :
      PairedRecognizerDovetailControllerInputInitializerRealizes
        initializer)
    (hinvoker :
      PairedRecognizerDovetailStageAttemptProtectedInvocationRealizes
        attempt invoker)
    (hemitter :
      PairedRecognizerDovetailControllerResultEmitterRealizes
        emitter)
    (hcontinuer :
      PairedRecognizerDovetailControllerContinueRealizes
        continuer) :
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes
      initializer invoker emitter continuer decider := by
  rcases hdriver with ⟨hwell, hdriverSpec⟩
  refine ⟨hwell, ?_, ?_, ?_⟩
  · intro C hraw
    exact (hcontinuer.right C).mpr hraw
  · intro w b hstage
    rcases hstage with
      ⟨limit, result, _hinitialized, hinvoked, hemitted⟩
    apply (hdriverSpec w b).mpr
    refine ⟨limit, result, ?_, ?_⟩
    · exact (hinvoker.right
        (pairedRecognizerDovetailFiniteStageLoopStageLayout w limit)
        result).mp hinvoked
    · exact (hemitter.right
        (DovetailControllerLayout.withResult
          (pairedRecognizerDovetailFiniteStageLoopStageLayout w limit)
          result)
        b).mp hemitted
  · intro w b hhalt
    rcases (hdriverSpec w b).mp hhalt with
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

private theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencerConstructionData_of_searchDriver
    (hsearch :
      PairedRecognizerDovetailFiniteStageLoopProtectedSequencerSearchDriverData) :
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
        PairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes
          initializer invoker emitter continuer decider := by
  intro attempt initializer invoker emitter continuer
    hinitializer hinvoker hemitter hcontinuer
  rcases hsearch attempt with ⟨decider, hdriver⟩
  exact
    ⟨decider,
      pairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes_of_searchDriver
        hdriver hinitializer hinvoker hemitter hcontinuer⟩

private theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencerConstructionData_finite_leaf :
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
        PairedRecognizerDovetailFiniteStageLoopProtectedSequencerRealizes
          initializer invoker emitter continuer decider := by
  apply
    pairedRecognizerDovetailFiniteStageLoopProtectedSequencerConstructionData_of_searchDriver
  intro attempt
  -- Remaining finite-table obligation: build the unbounded controller search
  -- driver for the protected stage-attempt machine.
  sorry

/--
Finite-machine leaf for sequencing initializer, protected invocation, result
emission, and continuation into the finite controller loop.
-/
theorem pairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData_scaffold :
    PairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData := by
  intro attempt initializer invoker emitter continuer
    hinitializer hinvoker hemitter hcontinuer
  rcases
      pairedRecognizerDovetailFiniteStageLoopProtectedSequencerConstructionData_finite_leaf
        attempt initializer invoker emitter continuer
        hinitializer hinvoker hemitter hcontinuer with
    ⟨decider, hwell, _hcontinue, hforward, hclosed⟩
  refine ⟨decider, hwell, ?_, ?_⟩
  · intro w b hsearch
    rcases hsearch with ⟨limit, result, hattempt, hraw⟩
    let C :=
      pairedRecognizerDovetailFiniteStageLoopStageLayout w limit
    apply hforward w b
    refine ⟨limit, result, hinitializer.right w, ?_, ?_⟩
    · exact (hinvoker.right C result).mpr hattempt
    · exact (hemitter.right
        (DovetailControllerLayout.withResult C result)
        b).mpr (by
          simpa [C, DovetailControllerLayout.withResult]
            using hraw)
  · intro w b hhalt
    rcases hclosed w b hhalt with
      ⟨limit, result, _hinitialized, hinvoked, hemitted⟩
    let C :=
      pairedRecognizerDovetailFiniteStageLoopStageLayout w limit
    refine ⟨limit, result, ?_, ?_⟩
    · exact (hinvoker.right C result).mp (by
        simpa [C] using hinvoked)
    · exact (hemitter.right
        (DovetailControllerLayout.withResult C result)
        b).mp (by
          simpa [C] using hemitted)

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_scaffold :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstructionData :=
  pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_of_protected
    pairedRecognizerDovetailFiniteStageLoopProtectedSequencingConstructionData_scaffold

theorem pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold :
    PairedRecognizerDovetailFiniteStageLoopSequencingConstruction :=
  pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_of_data
    pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_scaffold

theorem pairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction_scaffold :
    PairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction :=
  pairedRecognizerDovetailFiniteStageLoopSequencingHandoffConstruction_of_output
    pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold

theorem pairedRecognizerDovetailFiniteStageLoopControllerConstruction_scaffold :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction :=
  pairedRecognizerDovetailFiniteStageLoopControllerConstruction_of_components
    pairedRecognizerDovetailControllerInputInitializerConstruction_scaffold
    pairedRecognizerDovetailControllerStageInputEncoderConstruction_scaffold
    pairedRecognizerDovetailStageAttemptInvocationConstruction_scaffold
    pairedRecognizerDovetailControllerResultEmitterConstruction_scaffold
    pairedRecognizerDovetailControllerContinueConstruction_scaffold
    pairedRecognizerDovetailFiniteStageLoopSequencingConstruction_scaffold


end Computability
end FoC
