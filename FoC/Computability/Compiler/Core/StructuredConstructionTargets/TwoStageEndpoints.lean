import FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base

set_option doc.verso true

/-!
# Two-stage structured endpoints

These contracts separate syntactic input materialization from semantic witness
recovery.  Materializer inversion is restricted to canonical word starts;
semantic witnesses are recovered only after the structured core has run.
-/

namespace FoC
namespace Computability
namespace StructuredConstructionTargets

open Languages
open MachineDescription
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/--
Indexed tape-equivalence closedness restricted to canonical word starts.
-/
def EquivClosedIndexedFromWordStart {ι : Type}
    (D : MachineDescription)
    (inputBits : ι -> Word Bool)
    (target : ι -> Tape Bool) : Prop :=
  forall w : Word Bool, forall T : Tape Bool,
    D.HaltsFromTape (Tape.input w) T ->
      exists i : ι, w = inputBits i ∧ Tape.Equiv T (target i)

/--
A syntactic input materializer.  Its index contains only data encoded in the
public input word.
-/
structure Structured3EndpointWordStartEquivMaterializerSpec {ι : Type}
    (inputBits : ι -> Word Bool)
    (initialized : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop where
  forward :
    forall i : ι,
      materializer.HaltsFromTapeEquiv
        (Tape.input (inputBits i)) (initialized i)
  closedIndex :
    EquivClosedIndexedFromWordStart materializer inputBits initialized

/-- Existence wrapper for syntactic word-start materializers. -/
def Structured3EndpointWordStartEquivMaterializerConstruction {ι : Type}
    (inputBits : ι -> Word Bool)
    (initialized : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    materializer.SubroutineReady ∧
      Structured3EndpointWordStartEquivMaterializerSpec
        inputBits initialized materializer

namespace Structured3EndpointWordStartEquivMaterializerSpec

/-- Per-index closedness follows from forward behavior and determinism. -/
theorem closed
    {ι : Type}
    {inputBits : ι -> Word Bool}
    {initialized : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hspec :
      Structured3EndpointWordStartEquivMaterializerSpec
        inputBits initialized materializer)
    (hready : materializer.SubroutineReady)
    (i : ι) :
    materializer.ClosedFromTapeEquiv
      (Tape.input (inputBits i)) (initialized i) :=
  closedFromTapeEquiv_of_haltsFromTapeEquiv_of_subroutineReady
    hready (hspec.forward i)

end Structured3EndpointWordStartEquivMaterializerSpec

/--
Equivalence-facing structured-core behavior with semantic inversion.

The syntax index describes the materialized input.  The semantic index carries
the witness recovered from a successful core run.
-/
structure Structured3EndpointEquivSemanticCoreSpec
    {σ ι : Type}
    (syntaxOf : ι -> σ)
    (initialized : σ -> Tape Bool)
    (lowered : ι -> Tape Bool)
    (core : MachineDescription) : Prop where
  forward :
    forall i : ι,
      core.HaltsFromTapeEquiv
        (initialized (syntaxOf i)) (lowered i)
  closedIndex :
    forall s : σ, forall T : Tape Bool,
      core.HaltsFromTape (initialized s) T ->
        exists i : ι,
          s = syntaxOf i ∧ Tape.Equiv T (lowered i)

/--
Exact local structured-core behavior on the physical sequencer handoff tape.
-/
structure Structured3EndpointExactSemanticCoreSpec
    {σ ι : Type}
    (syntaxOf : ι -> σ)
    (initialized : σ -> Tape Bool)
    (lowered : ι -> Tape Bool)
    (core : MachineDescription) : Prop where
  forward :
    forall i : ι,
      core.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape (initialized (syntaxOf i)))
        (lowered i)
  closedIndex :
    forall s : σ, forall T : Tape Bool,
      core.HaltsFromTape
          (canonicalPrimitiveSeqHandoffTape (initialized s)) T ->
        exists i : ι, s = syntaxOf i ∧ T = lowered i

namespace Structured3EndpointExactSemanticCoreSpec

/-- View an exact semantic core through the equivalence-facing contract. -/
theorem toEquivSemanticCoreSpec
    {σ ι : Type}
    {syntaxOf : ι -> σ}
    {initialized : σ -> Tape Bool}
    {lowered : ι -> Tape Bool}
    {core : MachineDescription}
    (hspec :
      Structured3EndpointExactSemanticCoreSpec
        syntaxOf initialized lowered core) :
    Structured3EndpointEquivSemanticCoreSpec
      syntaxOf initialized lowered core := by
  constructor
  · intro i
    exact
      HaltsFromTapeEquiv_of_input_equiv
        (D := core)
        (Tin :=
          canonicalPrimitiveSeqHandoffTape
            (initialized (syntaxOf i)))
        (Tin' := initialized (syntaxOf i))
        (Tout := lowered i)
        (canonicalPrimitiveSeqHandoffTape_equiv
          (initialized (syntaxOf i)))
        (hspec.forward i)
  · intro s T hhalt
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := core)
          (Tin := initialized s)
          (Tin' := canonicalPrimitiveSeqHandoffTape (initialized s))
          (Tout := T)
          (Tape.Equiv.symm
            (canonicalPrimitiveSeqHandoffTape_equiv (initialized s)))
          hhalt with
      ⟨Tactual, hactual, hTactual⟩
    rcases hspec.closedIndex s Tactual hactual with
      ⟨i, hs, hTactualEq⟩
    refine ⟨i, hs, ?_⟩
    rw [← hTactualEq]
    exact Tape.Equiv.symm hTactual

end Structured3EndpointExactSemanticCoreSpec

/--
Public equivalence endpoint behavior with word-start-only inversion.
-/
structure Structured3EndpointWordStartEquivIndexedFamilySpec
    {ι : Type}
    (W : Structured3EndpointWrapper)
    (inputBits : ι -> Word Bool)
    (output : ι -> Tape Bool) : Prop where
  forward :
    forall i : ι,
      W.machine.HaltsFromTapeEquiv
        (Tape.input (inputBits i)) (output i)
  closedIndex :
    EquivClosedIndexedFromWordStart W.machine inputBits output

/--
Structured core data for a two-stage equivalence endpoint, before installing
the syntactic materializer and shared projector.
-/
structure Structured3EndpointEquivSemanticCoreComponents
    {σ ι : Type}
    (syntaxOf : ι -> σ)
    (initialized : σ -> Tape Bool)
    (lowered output tape0 tape1 : ι -> Tape Bool) where
  core : CommonGround.FiniteTransducers.Structured.Description
  coreWellFormed : core.WellFormed
  coreHaltTransitionFree : core.HaltTransitionFree
  coreSupportsRows : SupportsReadWriteRows3 core
  loweredShape :
    forall i : ι,
      lowered i =
        encodedGuardedStructured3Tapes
          (tape0 i) (tape1 i) (output i)
  semanticCore :
    Structured3EndpointEquivSemanticCoreSpec
      syntaxOf initialized lowered (lowerStructured3Description core)

/-- Existence wrapper for equivalence semantic-core components. -/
def Structured3EndpointEquivSemanticCoreConstruction
    {σ ι : Type}
    (syntaxOf : ι -> σ)
    (initialized : σ -> Tape Bool)
    (lowered output tape0 tape1 : ι -> Tape Bool) : Prop :=
  Nonempty
    (Structured3EndpointEquivSemanticCoreComponents
      syntaxOf initialized lowered output tape0 tape1)

/--
Exact local core data for a two-stage endpoint.  It can be weakened to the
equivalence component shape for public composition.
-/
structure Structured3EndpointExactSemanticCoreComponents
    {σ ι : Type}
    (syntaxOf : ι -> σ)
    (initialized : σ -> Tape Bool)
    (lowered output tape0 tape1 : ι -> Tape Bool) where
  core : CommonGround.FiniteTransducers.Structured.Description
  coreWellFormed : core.WellFormed
  coreHaltTransitionFree : core.HaltTransitionFree
  coreSupportsRows : SupportsReadWriteRows3 core
  loweredShape :
    forall i : ι,
      lowered i =
        encodedGuardedStructured3Tapes
          (tape0 i) (tape1 i) (output i)
  semanticCore :
    Structured3EndpointExactSemanticCoreSpec
      syntaxOf initialized lowered (lowerStructured3Description core)

/-- Existence wrapper for exact semantic-core components. -/
def Structured3EndpointExactSemanticCoreConstruction
    {σ ι : Type}
    (syntaxOf : ι -> σ)
    (initialized : σ -> Tape Bool)
    (lowered output tape0 tape1 : ι -> Tape Bool) : Prop :=
  Nonempty
    (Structured3EndpointExactSemanticCoreComponents
      syntaxOf initialized lowered output tape0 tape1)

namespace Structured3EndpointExactSemanticCoreComponents

/-- Forget exact handoff details for equivalence-facing endpoint composition. -/
def toEquivSemanticCoreComponents
    {σ ι : Type}
    {syntaxOf : ι -> σ}
    {initialized : σ -> Tape Bool}
    {lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3EndpointExactSemanticCoreComponents
        syntaxOf initialized lowered output tape0 tape1) :
    Structured3EndpointEquivSemanticCoreComponents
      syntaxOf initialized lowered output tape0 tape1 where
  core := C.core
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  loweredShape := C.loweredShape
  semanticCore := C.semanticCore.toEquivSemanticCoreSpec

end Structured3EndpointExactSemanticCoreComponents

/-- Exact semantic-core construction implies equivalence semantic-core data. -/
theorem structured3EndpointEquivSemanticCoreConstruction_of_exact
    {σ ι : Type}
    {syntaxOf : ι -> σ}
    {initialized : σ -> Tape Bool}
    {lowered output tape0 tape1 : ι -> Tape Bool}
    (hcore :
      Structured3EndpointExactSemanticCoreConstruction
        syntaxOf initialized lowered output tape0 tape1) :
    Structured3EndpointEquivSemanticCoreConstruction
      syntaxOf initialized lowered output tape0 tape1 := by
  rcases hcore with ⟨C⟩
  exact ⟨C.toEquivSemanticCoreComponents⟩

/--
Compose a syntactic word-start materializer, a semantic structured core, and
the shared tape-2 projector into the public endpoint contract.
-/
theorem structured3EndpointWordStartEquivIndexedConstruction_of_components
    {σ ι : Type}
    {inputBits : σ -> Word Bool}
    {syntaxOf : ι -> σ}
    {initialized : σ -> Tape Bool}
    {lowered output tape0 tape1 : ι -> Tape Bool}
    (hmaterializer :
      Structured3EndpointWordStartEquivMaterializerConstruction
        inputBits initialized)
    (hcore :
      Structured3EndpointEquivSemanticCoreConstruction
        syntaxOf initialized lowered output tape0 tape1)
    (hprojector : Structured3EndpointTape2ProjectorConstruction) :
    exists W : Structured3EndpointWrapper,
      Structured3EndpointWordStartEquivIndexedFamilySpec
        W (fun i => inputBits (syntaxOf i)) output := by
  rcases hmaterializer with
    ⟨initializer, hinitializerReady, hmaterializerSpec⟩
  rcases hcore with ⟨C⟩
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  let W : Structured3EndpointWrapper :=
    { core := C.core
      initializer := initializer
      projector := projector
      coreWellFormed := C.coreWellFormed
      coreHaltTransitionFree := C.coreHaltTransitionFree
      coreSupportsRows := C.coreSupportsRows
      initializerSubroutineReady := hinitializerReady
      projectorSubroutineReady := hprojectorSpec.subroutineReady }
  refine ⟨W, ?_⟩
  constructor
  · intro i
    exact
      W.haltsFromTapeEquivGeneral
        (hmaterializerSpec.forward (syntaxOf i))
        (C.semanticCore.forward i)
        (by
          rw [C.loweredShape i]
          exact
            hprojectorSpec.forward
              (tape0 i) (tape1 i) (output i))
  · intro w T hhalt
    rcases
        canonicalPrimitiveSeqDescription_haltsFromTape_inv
          (canonicalPrimitiveSeqDescription_subroutineReady
            W.initializerSubroutineReady W.lowered_subroutineReady)
          W.projectorSubroutineReady
          (by
            simpa [Structured3EndpointWrapper.machine] using! hhalt) with
      ⟨TloweredActual, hfirst, hprojectorActual⟩
    rcases
        canonicalPrimitiveSeqDescription_haltsFromTape_inv
          W.initializerSubroutineReady
          W.lowered_subroutineReady
          hfirst with
      ⟨TinitActual, hinitializerActual, hloweredActual⟩
    rcases
        hmaterializerSpec.closedIndex w TinitActual hinitializerActual with
      ⟨s, hw, hTinit⟩
    have hLoweredInput :
        Tape.Equiv
          (canonicalPrimitiveSeqHandoffTape TinitActual)
          (initialized s) :=
      Tape.Equiv.trans
        (canonicalPrimitiveSeqHandoffTape_equiv TinitActual)
        hTinit
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := W.lowered)
          (Tin := canonicalPrimitiveSeqHandoffTape TinitActual)
          (Tin' := initialized s)
          (Tout := TloweredActual)
          hLoweredInput
          hloweredActual with
      ⟨TloweredFromSyntax, hloweredFromSyntax,
        hTloweredFromSyntax⟩
    rcases
        C.semanticCore.closedIndex
          s TloweredFromSyntax hloweredFromSyntax with
      ⟨i, hsyntax, hTloweredSemantic⟩
    have hTlowered :
        Tape.Equiv TloweredActual (lowered i) :=
      Tape.Equiv.trans
        (Tape.Equiv.symm hTloweredFromSyntax)
        hTloweredSemantic
    have hProjectorInput :
        Tape.Equiv
          (canonicalPrimitiveSeqHandoffTape TloweredActual)
          (lowered i) :=
      Tape.Equiv.trans
        (canonicalPrimitiveSeqHandoffTape_equiv TloweredActual)
        hTlowered
    rw [C.loweredShape i] at hProjectorInput
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := W.projector)
          (Tin := canonicalPrimitiveSeqHandoffTape TloweredActual)
          (Tin' :=
            encodedGuardedStructured3Tapes
              (tape0 i) (tape1 i) (output i))
          (Tout := T)
          hProjectorInput
          hprojectorActual with
      ⟨TprojectedFromIndex, hprojectorFromIndex,
        hTprojectedFromIndex⟩
    have hTprojected :
        Tape.Equiv TprojectedFromIndex (output i) :=
      hprojectorSpec.closed
        (tape0 i) (tape1 i) (output i)
        TprojectedFromIndex hprojectorFromIndex
    refine ⟨i, ?_, ?_⟩
    · simpa [hsyntax] using hw
    · exact
        Tape.Equiv.trans
          (Tape.Equiv.symm hTprojectedFromIndex)
          hTprojected

end StructuredConstructionTargets
end Computability
end FoC
