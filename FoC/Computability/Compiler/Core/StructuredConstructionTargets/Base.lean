import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.Basic
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer
import FoC.Computability.Compiler.Structured.Lowering.Composition
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh
import FoC.Computability.Compiler.Structured.HeadRoutes.Endpoints
import FoC.Computability.Compiler.Structured.HeadRoutes

set_option doc.verso true

/-!
# Structured construction target adapters

This module records target-specific bridges from three-logical-tape structured
descriptions to the public finite-scaffold construction targets.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-!
The structured-core leaves are not public one-tape machines by themselves.
They run on the guarded encoding expected by the three-logical-tape lowerer.
The public construction target is the endpoint wrapper: an input materializer,
the lowered structured core, and an output projector.
-/

/--
A reusable endpoint package for a three-logical-tape structured core.

The package records only the structural facts needed to build the public
one-tape wrapper.  Target-specific construction leaves still prove their own
public contract for the packaged machine defined below.
-/
structure Structured3EndpointWrapper where
  core : CommonGround.FiniteTransducers.Structured.Description
  initializer : MachineDescription
  projector : MachineDescription
  coreWellFormed : core.WellFormed
  coreHaltTransitionFree : core.HaltTransitionFree
  coreSupportsRows : SupportsReadWriteRows3 core
  initializerSubroutineReady : initializer.SubroutineReady
  projectorSubroutineReady : projector.SubroutineReady

/-- The one-tape machine obtained by lowering the structured core. -/
def Structured3EndpointWrapper.lowered
    (W : Structured3EndpointWrapper) : MachineDescription :=
  lowerStructured3Description W.core

/--
The public one-tape endpoint exposed to existing finite-scaffold contracts.
-/
def Structured3EndpointWrapper.machine
    (W : Structured3EndpointWrapper) : MachineDescription :=
  structured3EndpointBridgeDescription
    W.initializer W.lowered W.projector

theorem Structured3EndpointWrapper.lowered_wellFormed
    (W : Structured3EndpointWrapper) :
    W.lowered.WellFormed := by
  simpa [Structured3EndpointWrapper.lowered] using
    lowerStructured3Description_wellFormed
      W.coreWellFormed W.coreSupportsRows

theorem Structured3EndpointWrapper.lowered_subroutineReady
    (W : Structured3EndpointWrapper) :
    W.lowered.SubroutineReady := by
  simpa [Structured3EndpointWrapper.lowered] using
    lowerStructured3Description_subroutineReady
      W.coreWellFormed W.coreSupportsRows

theorem Structured3EndpointWrapper.machine_subroutineReady
    (W : Structured3EndpointWrapper) :
    W.machine.SubroutineReady := by
  simpa [Structured3EndpointWrapper.machine] using
    structured3EndpointBridgeDescription_subroutineReady
      W.initializerSubroutineReady
      W.lowered_subroutineReady
      W.projectorSubroutineReady

/--
General forward endpoint composition for a packaged structured core, stated up
to tape equivalence.
-/
theorem Structured3EndpointWrapper.haltsFromTapeEquivGeneral
    (W : Structured3EndpointWrapper)
    {Tin Tinit Tlowered Tout : Tape Bool}
    (hinitializerRun :
      W.initializer.HaltsFromTapeEquiv Tin Tinit)
    (hloweredRun :
      W.lowered.HaltsFromTapeEquiv Tinit Tlowered)
    (hprojectorRun :
      W.projector.HaltsFromTapeEquiv Tlowered Tout) :
    W.machine.HaltsFromTapeEquiv Tin Tout := by
  have hfirst :
      (canonicalPrimitiveSeqDescription W.initializer W.lowered)
          |>.HaltsFromTapeEquiv Tin Tlowered :=
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      W.initializerSubroutineReady
      W.lowered_subroutineReady
      hinitializerRun
      hloweredRun
  simpa [Structured3EndpointWrapper.machine] using
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        W.initializerSubroutineReady
        W.lowered_subroutineReady)
      W.projectorSubroutineReady
      hfirst
      hprojectorRun

/--
General closed endpoint composition for a packaged structured core, stated up
to tape equivalence.
-/
theorem Structured3EndpointWrapper.closedFromTapeEquivGeneral
    (W : Structured3EndpointWrapper)
    {Tin Tinit Tlowered Tout : Tape Bool}
    (hinitializerClosed :
      W.initializer.ClosedFromTapeEquiv Tin Tinit)
    (hloweredClosed :
      W.lowered.ClosedFromTapeEquiv Tinit Tlowered)
    (hprojectorClosed :
      W.projector.ClosedFromTapeEquiv Tlowered Tout) :
    W.machine.ClosedFromTapeEquiv Tin Tout := by
  have hfirst :
      (canonicalPrimitiveSeqDescription W.initializer W.lowered)
          |>.ClosedFromTapeEquiv Tin Tlowered :=
    canonicalPrimitiveSeqDescription_closedFromTapeEquiv
      W.initializerSubroutineReady
      W.lowered_subroutineReady
      hinitializerClosed
      hloweredClosed
  simpa [Structured3EndpointWrapper.machine] using
    canonicalPrimitiveSeqDescription_closedFromTapeEquiv
      (canonicalPrimitiveSeqDescription_subroutineReady
        W.initializerSubroutineReady
        W.lowered_subroutineReady)
      W.projectorSubroutineReady
      hfirst
      hprojectorClosed

/--
Forward endpoint composition for a packaged structured core.

This is the wrapper-level form of
{name}`structured3EndpointBridgeDescription_haltsFromTapeEquiv`.
-/
theorem Structured3EndpointWrapper.haltsFromTapeEquiv
    (W : Structured3EndpointWrapper)
    {Tin T0 T1 T2 U0 U1 U2 Tout : Tape Bool}
    (hinitializerRun :
      W.initializer.HaltsFromTapeEquiv Tin
        (encodedGuardedStructured3Tapes T0 T1 T2))
    (hloweredRun :
      W.lowered.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        (encodedGuardedStructured3Tapes U0 U1 U2))
    (hprojectorRun :
      W.projector.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes U0 U1 U2)
        Tout) :
    W.machine.HaltsFromTapeEquiv Tin Tout := by
  exact
    W.haltsFromTapeEquivGeneral
      hinitializerRun
      hloweredRun
      hprojectorRun

/--
Closed endpoint composition for a packaged structured core.

This is the wrapper-level form of
{name}`structured3EndpointBridgeDescription_closedFromTapeEquiv`.
-/
theorem Structured3EndpointWrapper.closedFromTapeEquiv
    (W : Structured3EndpointWrapper)
    {Tin T0 T1 T2 U0 U1 U2 Tout : Tape Bool}
    (hinitializerClosed :
      W.initializer.ClosedFromTapeEquiv Tin
        (encodedGuardedStructured3Tapes T0 T1 T2))
    (hloweredClosed :
      W.lowered.ClosedFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        (encodedGuardedStructured3Tapes U0 U1 U2))
    (hprojectorClosed :
      W.projector.ClosedFromTapeEquiv
        (encodedGuardedStructured3Tapes U0 U1 U2)
        Tout) :
    W.machine.ClosedFromTapeEquiv Tin Tout := by
  exact
    W.closedFromTapeEquivGeneral
      hinitializerClosed
      hloweredClosed
      hprojectorClosed

/--
Exact forward endpoint composition for a packaged structured core.

The lowered core and projector hypotheses are stated on the exact bounced
handoff tapes produced by {name}`canonicalPrimitiveSeqDescription`.
-/
theorem Structured3EndpointWrapper.haltsFromTape
    (W : Structured3EndpointWrapper)
    {Tin Tinit Tlowered Tout : Tape Bool}
    (hinitializerRun :
      W.initializer.HaltsFromTape Tin Tinit)
    (hloweredRun :
      W.lowered.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape Tinit)
        Tlowered)
    (hprojectorRun :
      W.projector.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape Tlowered)
        Tout) :
    W.machine.HaltsFromTape Tin Tout := by
  simpa [Structured3EndpointWrapper.machine] using
    structured3EndpointBridgeDescription_haltsFromTape
      W.initializerSubroutineReady
      W.lowered_subroutineReady
      W.projectorSubroutineReady
      hinitializerRun
      hloweredRun
      hprojectorRun

/--
Exact closed endpoint composition for a packaged structured core.

This is the wrapper-level form of
{name}`structured3EndpointBridgeDescription_exactClosedFromTape`.
-/
theorem Structured3EndpointWrapper.exactClosedFromTape
    (W : Structured3EndpointWrapper)
    {Tin Tinit Tlowered Tout : Tape Bool}
    (hinitializerClosed :
      ExactClosedFromTape W.initializer Tin Tinit)
    (hloweredClosed :
      ExactClosedFromTape W.lowered
        (canonicalPrimitiveSeqHandoffTape Tinit)
        Tlowered)
    (hprojectorClosed :
      ExactClosedFromTape W.projector
        (canonicalPrimitiveSeqHandoffTape Tlowered)
        Tout) :
    ExactClosedFromTape W.machine Tin Tout := by
  simpa [Structured3EndpointWrapper.machine] using
    structured3EndpointBridgeDescription_exactClosedFromTape
      W.initializerSubroutineReady
      W.lowered_subroutineReady
      W.projectorSubroutineReady
      hinitializerClosed
      hloweredClosed
      hprojectorClosed

/--
Endpoint-family data for public contracts that are only defined up to
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv`.

The middle tapes are the logical endpoint tapes, not the exact bounced handoff
tapes; the canonical endpoint bridge handles the handoff equivalence.
-/
structure Structured3EndpointEquivFamilySpec
    {ι : Type} (W : Structured3EndpointWrapper)
    (input initialized lowered output : ι -> Tape Bool) : Prop where
  initializerForward :
    forall i : ι,
      W.initializer.HaltsFromTapeEquiv (input i) (initialized i)
  loweredForward :
    forall i : ι,
      W.lowered.HaltsFromTapeEquiv (initialized i) (lowered i)
  projectorForward :
    forall i : ι,
      W.projector.HaltsFromTapeEquiv (lowered i) (output i)
  initializerClosed :
    forall i : ι,
      W.initializer.ClosedFromTapeEquiv (input i) (initialized i)
  loweredClosed :
    forall i : ι,
      W.lowered.ClosedFromTapeEquiv (initialized i) (lowered i)
  projectorClosed :
    forall i : ι,
      W.projector.ClosedFromTapeEquiv (lowered i) (output i)

namespace Structured3EndpointEquivFamilySpec

theorem forward
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointEquivFamilySpec
        W input initialized lowered output)
    (i : ι) :
    W.machine.HaltsFromTapeEquiv (input i) (output i) :=
  W.haltsFromTapeEquivGeneral
    (hspec.initializerForward i)
    (hspec.loweredForward i)
    (hspec.projectorForward i)

theorem closed
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointEquivFamilySpec
        W input initialized lowered output)
    (i : ι) :
    W.machine.ClosedFromTapeEquiv (input i) (output i) :=
  W.closedFromTapeEquivGeneral
    (hspec.initializerClosed i)
    (hspec.loweredClosed i)
    (hspec.projectorClosed i)

theorem haltsFromTapeWithOutput
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointEquivFamilySpec
        W input initialized lowered output)
    (i : ι) :
    W.machine.HaltsFromTapeWithOutput
      (input i) (Tape.normalizedOutput (output i)) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
    (forward hspec i)

end Structured3EndpointEquivFamilySpec

/--
Endpoint-family data for public contracts that require exact final tapes.

The lowered core and projector are specified on
{name}`canonicalPrimitiveSeqHandoffTape`, because that is the literal tape
passed by the canonical wrapper.
-/
structure Structured3EndpointExactFamilySpec
    {ι : Type} (W : Structured3EndpointWrapper)
    (input initialized lowered output : ι -> Tape Bool) : Prop where
  initializerForward :
    forall i : ι,
      W.initializer.HaltsFromTape (input i) (initialized i)
  loweredForward :
    forall i : ι,
      W.lowered.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape (initialized i))
        (lowered i)
  projectorForward :
    forall i : ι,
      W.projector.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape (lowered i))
        (output i)
  initializerClosed :
    forall i : ι,
      ExactClosedFromTape W.initializer
        (input i) (initialized i)
  loweredClosed :
    forall i : ι,
      ExactClosedFromTape W.lowered
        (canonicalPrimitiveSeqHandoffTape (initialized i))
        (lowered i)
  projectorClosed :
    forall i : ι,
      ExactClosedFromTape W.projector
        (canonicalPrimitiveSeqHandoffTape (lowered i))
        (output i)

namespace Structured3EndpointExactFamilySpec

theorem forward
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointExactFamilySpec
        W input initialized lowered output)
    (i : ι) :
    W.machine.HaltsFromTape (input i) (output i) :=
  W.haltsFromTape
    (hspec.initializerForward i)
    (hspec.loweredForward i)
    (hspec.projectorForward i)

theorem closed
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointExactFamilySpec
        W input initialized lowered output)
    (i : ι) :
    ExactClosedFromTape W.machine (input i) (output i) :=
  W.exactClosedFromTape
    (hspec.initializerClosed i)
    (hspec.loweredClosed i)
    (hspec.projectorClosed i)

theorem closed_eq
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointExactFamilySpec
        W input initialized lowered output)
    (i : ι) {T : Tape Bool}
    (hhalt : W.machine.HaltsFromTape (input i) T) :
    T = output i :=
  closed hspec i T hhalt

theorem closed_equiv
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointExactFamilySpec
        W input initialized lowered output)
    (i : ι) :
    W.machine.ClosedFromTapeEquiv (input i) (output i) := by
  intro T hhalt
  rw [closed_eq hspec i hhalt]
  exact Tape.Equiv.refl (output i)

end Structured3EndpointExactFamilySpec

/--
Exact indexed closedness for a component.

Any halt from any public tape must come from one of the indexed source tapes
and must finish at that index's exact target tape.
-/
def ExactClosedIndexedFromTape {ι : Type}
    (D : MachineDescription)
    (source target : ι -> Tape Bool) : Prop :=
  forall Tin T : Tape Bool,
    D.HaltsFromTape Tin T ->
      exists i : ι, Tin = source i ∧ T = target i

/--
Forward and indexed-closed materializer data for canonical endpoint leaves.

The per-index exact closedness field of the exact materializer spec is derivable from
{name (full := FoC.Computability.MachineDescription.SubroutineReady)}`MachineDescription.SubroutineReady`
and exact forward behavior by determinism.  The genuinely target-specific
closed obligation is the indexed inversion statement: any materializer halt
must have started from one of the intended public inputs.
-/
structure Structured3EndpointIndexedMaterializerSpec {ι : Type}
    (input initialized : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop where
  forward :
    forall i : ι,
      materializer.HaltsFromTape (input i) (initialized i)
  closedIndex :
    ExactClosedIndexedFromTape materializer input initialized

/--
Existence wrapper for target-specific indexed input materializers.
-/
def Structured3EndpointIndexedMaterializerConstruction {ι : Type}
    (input initialized : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    materializer.SubroutineReady ∧
      Structured3EndpointIndexedMaterializerSpec
        input initialized materializer

namespace Structured3EndpointIndexedMaterializerSpec

/--
Derive exact per-index closedness from forward behavior and subroutine
determinism.
-/
theorem closed
    {ι : Type}
    {input initialized : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hspec :
      Structured3EndpointIndexedMaterializerSpec
        input initialized materializer)
    (hready : materializer.SubroutineReady)
    (i : ι) :
    ExactClosedFromTape materializer (input i) (initialized i) :=
  exactClosedFromTape_of_haltsFromTape_of_subroutineReady
    hready (hspec.forward i)

end Structured3EndpointIndexedMaterializerSpec

/--
Reusable exact materializer component for canonical endpoint leaves.

The materializer must map each public input tape to the exact initialized
three-logical-tape encoding and be closed over that indexed source family.
-/
structure Structured3EndpointExactMaterializerSpec {ι : Type}
    (input initialized : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop where
  forward :
    forall i : ι,
      materializer.HaltsFromTape (input i) (initialized i)
  closed :
    forall i : ι,
      ExactClosedFromTape materializer (input i) (initialized i)
  closedIndex :
    ExactClosedIndexedFromTape materializer input initialized

namespace Structured3EndpointIndexedMaterializerSpec

/--
Upgrade forward/indexed materializer data to the exact materializer component
expected by the canonical endpoint wrapper.
-/
theorem toExactMaterializerSpec
    {ι : Type}
    {input initialized : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hspec :
      Structured3EndpointIndexedMaterializerSpec
        input initialized materializer)
    (hready : materializer.SubroutineReady) :
    Structured3EndpointExactMaterializerSpec
      input initialized materializer where
  forward := hspec.forward
  closed := hspec.closed hready
  closedIndex := hspec.closedIndex

end Structured3EndpointIndexedMaterializerSpec

/--
Reusable exact lowered-core component for canonical endpoint leaves.

The lowered machine sees the literal handoff tape produced by the canonical
physical sequencer after the materializer finishes.
-/
structure Structured3EndpointExactLoweredCoreSpec {ι : Type}
    (initialized lowered : ι -> Tape Bool)
    (core : MachineDescription) : Prop where
  forward :
    forall i : ι,
      core.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape (initialized i))
        (lowered i)
  closed :
    forall i : ι,
      ExactClosedFromTape core
        (canonicalPrimitiveSeqHandoffTape (initialized i))
        (lowered i)

/--
Reusable exact projector component for canonical endpoint leaves.

The projector sees the literal handoff tape produced by the canonical physical
sequencer after the lowered structured core finishes.
-/
structure Structured3EndpointExactProjectorSpec {ι : Type}
    (lowered output : ι -> Tape Bool)
    (projector : MachineDescription) : Prop where
  forward :
    forall i : ι,
      projector.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape (lowered i))
        (output i)
  closed :
    forall i : ι,
      ExactClosedFromTape projector
        (canonicalPrimitiveSeqHandoffTape (lowered i))
        (output i)

/--
Generic canonical exact endpoint spec shared by the four construction leaves.

Target-specific sections choose the indexed public inputs, initialized
three-tape encodings, lowered-core outputs, and public output tapes.  This
generic spec packages the component obligations against a
{name}`Structured3EndpointWrapper`.
-/
structure Structured3CanonicalExactIndexedEndpointSpec
    {ι : Type}
    (W : Structured3EndpointWrapper)
    (input initialized lowered output : ι -> Tape Bool) : Prop where
  materializer :
    Structured3EndpointExactMaterializerSpec
      input initialized W.initializer
  core :
    Structured3EndpointExactLoweredCoreSpec
      initialized lowered W.lowered
  projector :
    Structured3EndpointExactProjectorSpec
      lowered output W.projector

/--
Generic canonical exact endpoint construction.
-/
def Structured3CanonicalExactIndexedEndpointConstruction
    {ι : Type}
    (input initialized lowered output : ι -> Tape Bool) : Prop :=
  exists W : Structured3EndpointWrapper,
    Structured3CanonicalExactIndexedEndpointSpec
      W input initialized lowered output

/--
Concrete component data for a canonical exact endpoint.

This is the construction-facing form of
{name}`Structured3CanonicalExactIndexedEndpointConstruction`: it separates the
structured core, input parser/materializer, lowered-core contract, and output
projector.  The input component is intentionally indexed and closed over the
target family; for the current leaves it is not just the generic "copy any
public tape into tape 0" materializer, because invalid public inputs must not
enter the endpoint.
-/
structure Structured3CanonicalExactEndpointComponents
    {ι : Type}
    (input initialized lowered output : ι -> Tape Bool) where
  core : CommonGround.FiniteTransducers.Structured.Description
  initializer : MachineDescription
  projector : MachineDescription
  coreWellFormed : core.WellFormed
  coreHaltTransitionFree : core.HaltTransitionFree
  coreSupportsRows : SupportsReadWriteRows3 core
  initializerSubroutineReady : initializer.SubroutineReady
  projectorSubroutineReady : projector.SubroutineReady
  materializer :
    Structured3EndpointExactMaterializerSpec
      input initialized initializer
  loweredCore :
    Structured3EndpointExactLoweredCoreSpec
      initialized lowered (lowerStructured3Description core)
  projectorSpec :
    Structured3EndpointExactProjectorSpec
      lowered output projector

/--
Existence wrapper for concrete canonical exact endpoint components.
-/
def Structured3CanonicalExactEndpointComponentConstruction
    {ι : Type}
    (input initialized lowered output : ι -> Tape Bool) : Prop :=
  Nonempty
    (Structured3CanonicalExactEndpointComponents
      input initialized lowered output)

namespace Structured3CanonicalExactEndpointComponents

/--
Package concrete endpoint components as the reusable wrapper record.
-/
def wrapper
    {ι : Type}
    {input initialized lowered output : ι -> Tape Bool}
    (C :
      Structured3CanonicalExactEndpointComponents
        input initialized lowered output) :
    Structured3EndpointWrapper where
  core := C.core
  initializer := C.initializer
  projector := C.projector
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  initializerSubroutineReady := C.initializerSubroutineReady
  projectorSubroutineReady := C.projectorSubroutineReady

/--
The generic exact endpoint spec induced by concrete endpoint components.
-/
theorem spec
    {ι : Type}
    {input initialized lowered output : ι -> Tape Bool}
    (C :
      Structured3CanonicalExactEndpointComponents
        input initialized lowered output) :
    Structured3CanonicalExactIndexedEndpointSpec
      C.wrapper input initialized lowered output where
  materializer := C.materializer
  core := by
    simpa [wrapper, Structured3EndpointWrapper.lowered] using
      C.loweredCore
  projector := C.projectorSpec

end Structured3CanonicalExactEndpointComponents

/--
Concrete endpoint components imply the existential canonical endpoint
construction used by the four leaf adapters.
-/
theorem structured3CanonicalExactIndexedEndpointConstruction_of_components
    {ι : Type}
    {input initialized lowered output : ι -> Tape Bool}
    (h :
      Structured3CanonicalExactEndpointComponentConstruction
        input initialized lowered output) :
    Structured3CanonicalExactIndexedEndpointConstruction
      input initialized lowered output := by
  rcases h with ⟨C⟩
  exact
    ⟨C.wrapper,
      Structured3CanonicalExactEndpointComponents.spec C⟩

/--
Closedness derived from an equivalence-forward deterministic subroutine.
-/
theorem closedFromTapeEquiv_of_haltsFromTapeEquiv_of_subroutineReady
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (hD : D.SubroutineReady)
    (hforward : D.HaltsFromTapeEquiv Tin Tout) :
    D.ClosedFromTapeEquiv Tin Tout := by
  intro T hhalt
  rcases hforward with ⟨actual, hactual, hequiv⟩
  have hT : T = actual :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hD.right hhalt hactual
  rw [hT]
  exact hequiv

/--
Transport an actual deterministic halt to the target tape named by an
equivalence-forward run.
-/
theorem haltsFromTape_equiv_target_of_forward
    {D : MachineDescription} {Tin Tactual Ttarget : Tape Bool}
    (hready : D.SubroutineReady)
    (hactual : D.HaltsFromTape Tin Tactual)
    (hforward : D.HaltsFromTapeEquiv Tin Ttarget) :
    Tape.Equiv Tactual Ttarget := by
  rcases hforward with ⟨Tforward, hforwardActual, hTforward⟩
  have hTactual : Tactual = Tforward :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hready.right hactual hforwardActual
  rw [hTactual]
  exact hTforward

/--
Equivalence-facing shared tape-2 projector route for canonical three-tape
endpoints.
-/
structure Structured3EndpointTape2ProjectorSpec
    (projector : MachineDescription) : Prop where
  subroutineReady : projector.SubroutineReady
  forward :
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        T2
  closed :
    forall T0 T1 T2 : Tape Bool,
      projector.ClosedFromTapeEquiv
        (encodedGuardedStructured3Tapes T0 T1 T2)
        T2

/-- Existence wrapper for the equivalence-facing shared tape-2 projector. -/
def Structured3EndpointTape2ProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    Structured3EndpointTape2ProjectorSpec projector

/-- The lower equivalence tape-2 projector is the shared endpoint projector. -/
theorem structured3EndpointTape2ProjectorSpec_of_tape2ProjectorSpec
    {projector : MachineDescription}
    (hprojector : StructuredTape2ProjectorSpec projector) :
    Structured3EndpointTape2ProjectorSpec projector where
  subroutineReady := hprojector.left
  forward := hprojector.right
  closed := by
    intro T0 T1 T2
    exact
      closedFromTapeEquiv_of_haltsFromTapeEquiv_of_subroutineReady
        hprojector.left
        (hprojector.right T0 T1 T2)

theorem structured3EndpointTape2ProjectorConstruction_of_tape2ProjectorConstruction
    (hprojector : StructuredTape2ProjectorConstruction) :
    Structured3EndpointTape2ProjectorConstruction := by
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact
    ⟨projector,
      structured3EndpointTape2ProjectorSpec_of_tape2ProjectorSpec
        hprojectorSpec⟩

/--
The shared endpoint tape-2 projector used by equivalence-facing structured
construction targets.
-/
theorem structured3EndpointTape2ProjectorConstruction_core :
    Structured3EndpointTape2ProjectorConstruction :=
  structured3EndpointTape2ProjectorConstruction_of_tape2ProjectorConstruction
    structuredTape2ProjectorConstruction_core

/--
Canonical endpoint components that share an equivalence-facing tape-2
projector route.
-/
structure Structured3CanonicalEquivEndpointSharedProjectorComponents
    {ι : Type}
    (input initialized lowered output tape0 tape1 : ι -> Tape Bool) where
  core : CommonGround.FiniteTransducers.Structured.Description
  initializer : MachineDescription
  projector : MachineDescription
  coreWellFormed : core.WellFormed
  coreHaltTransitionFree : core.HaltTransitionFree
  coreSupportsRows : SupportsReadWriteRows3 core
  initializerSubroutineReady : initializer.SubroutineReady
  projectorSubroutineReady : projector.SubroutineReady
  loweredShape :
    forall i : ι,
      lowered i =
        encodedGuardedStructured3Tapes
          (tape0 i) (tape1 i) (output i)
  materializer :
    Structured3EndpointExactMaterializerSpec
      input initialized initializer
  loweredCore :
    Structured3EndpointExactLoweredCoreSpec
      initialized lowered (lowerStructured3Description core)
  projectorRoute :
    Structured3EndpointTape2ProjectorSpec projector

/--
Existence wrapper for endpoint components that share an equivalence-facing
tape-2 projector route.
-/
def Structured3CanonicalEquivEndpointSharedProjectorConstruction
    {ι : Type}
    (input initialized lowered output tape0 tape1 : ι -> Tape Bool) : Prop :=
  Nonempty
    (Structured3CanonicalEquivEndpointSharedProjectorComponents
      input initialized lowered output tape0 tape1)

/--
Canonical endpoint components before installing the shared output projector.

This is the target-specific part of the structured endpoint construction:
materialize the public input, run the lowered structured core, and prove that
the lowered output places the public result on logical tape 2.  The actual
tape-2 projector is supplied once by
{name}`structured3EndpointTape2ProjectorConstruction_core`.

The materializer field carries only exact forward behavior plus indexed
closedness.  Per-index exact closedness is installed when these components are
converted to full endpoint components, using the
{name (full := FoC.Computability.MachineDescription.SubroutineReady)}`MachineDescription.SubroutineReady`
field and machine determinism.
-/
structure Structured3CanonicalExactEndpointCoreComponents
    {ι : Type}
    (input initialized lowered output tape0 tape1 : ι -> Tape Bool) where
  core : CommonGround.FiniteTransducers.Structured.Description
  initializer : MachineDescription
  coreWellFormed : core.WellFormed
  coreHaltTransitionFree : core.HaltTransitionFree
  coreSupportsRows : SupportsReadWriteRows3 core
  initializerSubroutineReady : initializer.SubroutineReady
  loweredShape :
    forall i : ι,
      lowered i =
        encodedGuardedStructured3Tapes
          (tape0 i) (tape1 i) (output i)
  materializer :
    Structured3EndpointIndexedMaterializerSpec
      input initialized initializer
  loweredCore :
    Structured3EndpointExactLoweredCoreSpec
      initialized lowered (lowerStructured3Description core)

/--
Existence wrapper for the target-specific parser/core part of a canonical
endpoint, excluding the reusable tape-2 projector.
-/
def Structured3CanonicalExactEndpointCoreComponentConstruction
    {ι : Type}
    (input initialized lowered output tape0 tape1 : ι -> Tape Bool) : Prop :=
  Nonempty
    (Structured3CanonicalExactEndpointCoreComponents
      input initialized lowered output tape0 tape1)

/--
Target-specific lowered structured core data, before installing an input
materializer.

This separates the two remaining target-specific jobs: first recognize and
materialize the public input family, then run the lowered structured core from
the canonical initialized three-tape layout to a lowered output whose logical
tape 2 carries the public output.
-/
structure Structured3CanonicalExactEndpointLoweredCoreComponents
    {ι : Type}
    (initialized lowered output tape0 tape1 : ι -> Tape Bool) where
  core : CommonGround.FiniteTransducers.Structured.Description
  coreWellFormed : core.WellFormed
  coreHaltTransitionFree : core.HaltTransitionFree
  coreSupportsRows : SupportsReadWriteRows3 core
  loweredShape :
    forall i : ι,
      lowered i =
        encodedGuardedStructured3Tapes
          (tape0 i) (tape1 i) (output i)
  loweredCore :
    Structured3EndpointExactLoweredCoreSpec
      initialized lowered (lowerStructured3Description core)

/--
Existence wrapper for target-specific lowered structured core data.
-/
def Structured3CanonicalExactEndpointLoweredCoreConstruction
    {ι : Type}
    (initialized lowered output tape0 tape1 : ι -> Tape Bool) : Prop :=
  Nonempty
    (Structured3CanonicalExactEndpointLoweredCoreComponents
      initialized lowered output tape0 tape1)

namespace Structured3CanonicalExactEndpointLoweredCoreComponents

/--
Install a concrete indexed materializer in front of lowered structured core
data to obtain no-projector endpoint core components.
-/
def toCoreComponents
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalExactEndpointLoweredCoreComponents
        initialized lowered output tape0 tape1)
    {initializer : MachineDescription}
    (hinitializerReady : initializer.SubroutineReady)
    (hmaterializer :
      Structured3EndpointIndexedMaterializerSpec
        input initialized initializer) :
    Structured3CanonicalExactEndpointCoreComponents
      input initialized lowered output tape0 tape1 where
  core := C.core
  initializer := initializer
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  initializerSubroutineReady := hinitializerReady
  loweredShape := C.loweredShape
  materializer := hmaterializer
  loweredCore := C.loweredCore

end Structured3CanonicalExactEndpointLoweredCoreComponents

/--
Indexed materializer construction plus lowered structured core construction
give the target-specific no-projector endpoint components.
-/
theorem structured3CanonicalExactEndpointCoreComponentConstruction_of_materializer_loweredCore
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (hmaterializer :
      Structured3EndpointIndexedMaterializerConstruction
        input initialized)
    (hcore :
      Structured3CanonicalExactEndpointLoweredCoreConstruction
        initialized lowered output tape0 tape1) :
    Structured3CanonicalExactEndpointCoreComponentConstruction
      input initialized lowered output tape0 tape1 := by
  rcases hmaterializer with
    ⟨initializer, hinitializerReady, hmaterializerSpec⟩
  rcases hcore with ⟨C⟩
  exact
    ⟨C.toCoreComponents hinitializerReady hmaterializerSpec⟩

namespace Structured3CanonicalExactEndpointCoreComponents

/--
Install an equivalence-facing shared projector into target-specific endpoint
core components.
-/
def toEquivSharedProjectorComponents
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalExactEndpointCoreComponents
        input initialized lowered output tape0 tape1)
    {projector : MachineDescription}
    (hprojector :
      Structured3EndpointTape2ProjectorSpec projector) :
    Structured3CanonicalEquivEndpointSharedProjectorComponents
      input initialized lowered output tape0 tape1 where
  core := C.core
  initializer := C.initializer
  projector := projector
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  initializerSubroutineReady := C.initializerSubroutineReady
  projectorSubroutineReady := hprojector.subroutineReady
  loweredShape := C.loweredShape
  materializer :=
    C.materializer.toExactMaterializerSpec
      C.initializerSubroutineReady
  loweredCore := C.loweredCore
  projectorRoute := hprojector

end Structured3CanonicalExactEndpointCoreComponents

/--
Target-specific core components plus the shared equivalence tape-2 projector
give the equivalence shared-projector endpoint component package.
-/
theorem structured3CanonicalEquivEndpointSharedProjectorConstruction_of_coreComponents
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (hcore :
      Structured3CanonicalExactEndpointCoreComponentConstruction
        input initialized lowered output tape0 tape1)
    (hprojector :
      Structured3EndpointTape2ProjectorConstruction) :
    Structured3CanonicalEquivEndpointSharedProjectorConstruction
      input initialized lowered output tape0 tape1 := by
  rcases hcore with ⟨C⟩
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact
    ⟨C.toEquivSharedProjectorComponents hprojectorSpec⟩

namespace Structured3CanonicalEquivEndpointSharedProjectorComponents

/--
Package equivalence shared-projector components as the reusable wrapper record.
-/
def wrapper
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalEquivEndpointSharedProjectorComponents
        input initialized lowered output tape0 tape1) :
    Structured3EndpointWrapper where
  core := C.core
  initializer := C.initializer
  projector := C.projector
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  initializerSubroutineReady := C.initializerSubroutineReady
  projectorSubroutineReady := C.projectorSubroutineReady

end Structured3CanonicalEquivEndpointSharedProjectorComponents

/--
Equivalence indexed closedness for a component.

This is the indexed analogue of
{name (full := FoC.Computability.MachineDescription.ClosedFromTapeEquiv)}`MachineDescription.ClosedFromTapeEquiv`.
-/
def EquivClosedIndexedFromTape {ι : Type}
    (D : MachineDescription)
    (source target : ι -> Tape Bool) : Prop :=
  forall Tin T : Tape Bool,
    D.HaltsFromTape Tin T ->
      exists i : ι, Tin = source i ∧ Tape.Equiv T (target i)

/--
Equivalence-forward indexed materializer data for endpoint leaves.

This is the Phase-3-facing variant of
{name}`Structured3EndpointIndexedMaterializerSpec`: valid inputs only have to
reach an equivalent initialized tape, while the closed-index clause still
inverts arbitrary halts back to the target input family.
-/
structure Structured3EndpointEquivIndexedMaterializerSpec {ι : Type}
    (input initialized : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop where
  forward :
    forall i : ι,
      materializer.HaltsFromTapeEquiv (input i) (initialized i)
  closedIndex :
    EquivClosedIndexedFromTape materializer input initialized

/--
Existence wrapper for equivalence-forward indexed input materializers.
-/
def Structured3EndpointEquivIndexedMaterializerConstruction {ι : Type}
    (input initialized : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    materializer.SubroutineReady ∧
      Structured3EndpointEquivIndexedMaterializerSpec
        input initialized materializer

def Structured3EndpointEquivInputMaterializerInitialized
    {ι : Type}
    (input output : ι -> Tape Bool) : ι -> Tape Bool :=
  fun i =>
    CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
      (input i) (output i)

/--
Endpoint-facing view of the reusable CommonGround structured-input
materializer.

The CommonGround spec supplies the forward {lit}`HaltsFromTapeEquiv` behavior into
the canonical guarded three-tape input.  Endpoint components still require the
indexed closedness/inversion fact, so this adapter keeps that proof as an
explicit field instead of hiding it in target-specific wrappers.
-/
structure Structured3EndpointEquivInputMaterializerSpec {ι : Type}
    (input output : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop where
  inputSpec :
    CommonGround.FiniteTransducers.Structured3InputMaterializerSpec
      input output materializer
  closedIndex :
    EquivClosedIndexedFromTape materializer input
      (Structured3EndpointEquivInputMaterializerInitialized input output)

/--
Existence wrapper for endpoint materializers built through the reusable
CommonGround structured-input materializer contract.
-/
def Structured3EndpointEquivInputMaterializerConstruction {ι : Type}
    (input output : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    Structured3EndpointEquivInputMaterializerSpec
      input output materializer

/-!
# Closed-recognizer input materializers

The following adapter is the shared version of the FuelSimulator materializer
pilot route.  Target files provide a public code-family recognizer; the common
emitter and sequencing route live here.
-/

/--
Embedding-emitter phase for guarded three-logical-tape inputs whose public
source is an ordinary input tape.

This is intentionally indexed by {lean}`Word Bool`, not by arbitrary
{lean}`Tape Bool`.
The current endpoint materializer route only hands the emitter canonical
{lit}`Tape.input bits` sources after the recognizer phase.  Keeping that
narrower contract leaves the remaining finite-machine obligation as a stream
transducer over the scanned input word.
-/
def Structured3InputEmbeddingEmitterConstruction : Prop :=
  Structured3InputMaterializerConstruction
    (fun bits : Word Bool => Tape.input bits)
    (fun _bits : Word Bool => Tape.blank)

/-- Encoded logical-tape segment for a guarded public input word. -/
def guardedInputWordLogicalTapeCode (bits : Word Bool) :
    List (Option Bool) :=
  List.append (logicalCellCode (none : Option Bool))
    (List.append headMarkerCells
      (List.append
        (match bits with
        | [] => logicalCellCode (none : Option Bool)
        | bit :: rest =>
            List.append (logicalCellCode (some bit))
              (logicalCellListCode (rest.map some)))
        (logicalCellCode (none : Option Bool))))

theorem guardedInputWordLogicalTapeCode_eq_logicalTapeCode
    (bits : Word Bool) :
    guardedInputWordLogicalTapeCode bits =
      logicalTapeCode (guardLogicalTape (Tape.input bits)) := by
  cases bits with
  | nil =>
      rfl
  | cons bit rest =>
      change
        List.append (logicalCellCode (none : Option Bool))
          (List.append headMarkerCells
            (List.append
              (List.append (logicalCellCode (some bit))
                (logicalCellListCode (rest.map some)))
              (logicalCellCode (none : Option Bool)))) =
        List.append (logicalCellListCode [none])
          (List.append headMarkerCells
            (List.append (logicalCellCode (some bit))
              (logicalCellListCode (List.append (rest.map some) [none]))))
      simp [logicalCellListBits, List.append_assoc]

/-- Encoded logical-tape segment for a guarded blank tape. -/
def guardedBlankLogicalTapeCode : List (Option Bool) :=
  guardedInputWordLogicalTapeCode []

theorem guardedBlankLogicalTapeCode_eq_logicalTapeCode :
    guardedBlankLogicalTapeCode =
      logicalTapeCode (guardLogicalTape Tape.blank) := by
  rfl

/--
Explicit physical cells for the narrowed input-tape embedding emitter target.
-/
def structured3InputEmbeddingEmitterTargetCells
    (bits : Word Bool) : List (Option Bool) :=
  List.append tapeSeparatorCells
    (List.append (guardedInputWordLogicalTapeCode bits)
      (List.append tapeSeparatorCells
        (List.append guardedBlankLogicalTapeCode
          (List.append tapeSeparatorCells
            (List.append guardedBlankLogicalTapeCode
              tapeSeparatorCells)))))

theorem structured3InputEmbeddingEmitterTargetCells_eq
    (bits : Word Bool) :
    structured3InputEmbeddingEmitterTargetCells bits =
      Tape.cells
        (structured3InputMaterializerTargetTape
          (Tape.input bits) Tape.blank) := by
  rw [structured3InputEmbeddingEmitterTargetCells,
    guardedInputWordLogicalTapeCode_eq_logicalTapeCode,
    guardedBlankLogicalTapeCode_eq_logicalTapeCode,
    structured3InputMaterializerTargetTape,
    encodedGuardedStructured3Tapes_cells]

/-- Exact tape represented by the explicit input-embedding target cells. -/
def structured3InputEmbeddingEmitterTargetTape
    (bits : Word Bool) : Tape Bool :=
  tapeAtCells [] (structured3InputEmbeddingEmitterTargetCells bits)

theorem structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget
    (bits : Word Bool) :
    structured3InputEmbeddingEmitterTargetTape bits =
      structured3InputMaterializerTargetTape
        (Tape.input bits) Tape.blank := by
  unfold structured3InputEmbeddingEmitterTargetTape
  unfold structured3InputEmbeddingEmitterTargetCells
  rw [guardedInputWordLogicalTapeCode_eq_logicalTapeCode]
  rw [guardedBlankLogicalTapeCode_eq_logicalTapeCode]
  rfl

/--
Control state for the stream-expansion phase below the narrowed shared
embedding emitter.

The phase needs to distinguish the initial blank of {lit}`Tape.input []` from
the blank just to the right of a nonempty input word.
-/
inductive OptionCellExpandAppendScanState where
  | fresh
  | afterBit
  deriving DecidableEq, Repr

/-- Static cells written before scanning the public input word. -/
def optionCellExpandAppendPrefixCells : List (Option Bool) :=
  List.append tapeSeparatorCells
    (List.append (logicalCellCode (none : Option Bool)) headMarkerCells)

/-- Physical cells emitted for one scanned public input bit. -/
def optionCellExpandAppendBitCells (bit : Bool) : List (Option Bool) :=
  logicalCellCode (some bit)

/--
Physical cells emitted from the scanned input window before the right guard.
The empty source word contributes the blank head cell of {lit}`Tape.input []`;
the nonempty source word contributes the logical-cell code of each input bit.
-/
def optionCellExpandAppendScannedCells
    (bits : Word Bool) : List (Option Bool) :=
  match bits with
  | [] => logicalCellCode (none : Option Bool)
  | bit :: rest =>
      List.append (optionCellExpandAppendBitCells bit)
        (logicalCellListCode (rest.map some))

/-- Right guard after the public input logical-tape segment. -/
def optionCellExpandAppendRightGuardCells : List (Option Bool) :=
  logicalCellCode (none : Option Bool)

/-- Static suffix for blank scratch tape, blank output tape, and final separator. -/
def optionCellExpandAppendSuffixCells : List (Option Bool) :=
  List.append tapeSeparatorCells
    (List.append guardedBlankLogicalTapeCode
      (List.append tapeSeparatorCells
        (List.append guardedBlankLogicalTapeCode tapeSeparatorCells)))

/--
Exact physical target for the option-cell expansion primitive.

The eventual finite table should write these cells and rewind to the first
separator.  This is the reusable missing primitive called out by the
FuelSimulator materializer pilot plan.
-/
def optionCellExpandAppendTargetCells
    (bits : Word Bool) : List (Option Bool) :=
  List.append optionCellExpandAppendPrefixCells
    (List.append (optionCellExpandAppendScannedCells bits)
      (List.append optionCellExpandAppendRightGuardCells
        optionCellExpandAppendSuffixCells))

theorem optionCellExpandAppendTargetCells_eq_structured3
    (bits : Word Bool) :
    optionCellExpandAppendTargetCells bits =
      structured3InputEmbeddingEmitterTargetCells bits := by
  cases bits with
  | nil =>
      rfl
  | cons bit rest =>
      simp [optionCellExpandAppendTargetCells,
        structured3InputEmbeddingEmitterTargetCells,
        optionCellExpandAppendPrefixCells,
        optionCellExpandAppendScannedCells,
        optionCellExpandAppendRightGuardCells,
        optionCellExpandAppendSuffixCells,
        guardedInputWordLogicalTapeCode,
        optionCellExpandAppendBitCells,
        guardedBlankLogicalTapeCode, List.append_assoc]

/--
Concrete run contract for the option-cell expansion primitive below the shared
embedding emitter.
-/
structure OptionCellExpandAppendRunSpec
    (emitter : MachineDescription) : Prop where
  ready : emitter.SubroutineReady
  forward :
    forall bits : Word Bool,
      emitter.HaltsFromTape
        (Tape.input bits)
        (tapeAtCells [] (optionCellExpandAppendTargetCells bits))

/--
Concrete finite table placeholder for the stream expansion and left rewind.
-/
def optionCellExpandAppendDescription : MachineDescription :=
  { stateCount := 1
    start := 0
    halt := 0
    transitions := [] }

theorem optionCellExpandAppendDescription_runSpec :
    OptionCellExpandAppendRunSpec optionCellExpandAppendDescription := by
  -- Finite-machine obligation: scan the canonical input word, expand each
  -- logical cell into its two physical cells, append the guarded blank tapes,
  -- and rewind to the left boundary separator.
  sorry

/--
Exact finite-machine run contract for the narrowed shared embedding emitter.

This is the concrete machine boundary below the public
{name}`Structured3InputMaterializerSpec`: the emitter must write the explicit
physical cells for the guarded three-logical-tape input and stop with the head
on the left boundary separator.
-/
def Structured3InputEmbeddingEmitterTargetCellsRunSpec
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall bits : Word Bool,
      emitter.HaltsFromTape
        (Tape.input bits)
        (structured3InputEmbeddingEmitterTargetTape bits)

theorem structured3InputEmbeddingEmitterSpec_of_targetCellsRunSpec
    {emitter : MachineDescription}
    (hspec :
      Structured3InputEmbeddingEmitterTargetCellsRunSpec emitter) :
    Structured3InputMaterializerSpec
      (fun bits : Word Bool => Tape.input bits)
      (fun _bits : Word Bool => Tape.blank)
      emitter := by
  constructor
  · exact hspec.left
  · intro bits
    refine
      ⟨structured3InputEmbeddingEmitterTargetTape bits,
        hspec.right bits, ?_⟩
    rw [structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget]
    exact Tape.Equiv.refl
      (structured3InputMaterializerTargetTape
        (Tape.input bits) Tape.blank)

/--
Recognizer contract for a public code family used as the first phase of an
indexed endpoint materializer.

The canonical-layout recognizer spec supplies the standard forward and
input-word inversion facts.  The additional indexed closedness field is the
stronger property needed by endpoint wrappers: any halt from any starting tape
must have started from one of the indexed canonical input tapes and must finish
at that index's handoff tape.
-/
structure ClosedInputFamilyRecognizerSpec
    {α : Type}
    (decode : Word MachineCodeSymbol -> Option α)
    (encode : α -> Word MachineCodeSymbol)
    (recognizer : MachineDescription) : Prop where
  canonical :
    EncRewriters.CanonicalLayouts.ClosedRecognizerSpec
      decode encode recognizer
  closedIndex :
    forall Tin T : Tape Bool,
      recognizer.HaltsFromTape Tin T ->
        exists a : α,
          Tin = EncRewriters.CanonicalLayouts.InputTape encode a ∧
            T = EncRewriters.CanonicalLayouts.HandoffTape encode a

/-- Existence wrapper for closed public code-family recognizers. -/
def ClosedInputFamilyRecognizerConstruction
    {α : Type}
    (decode : Word MachineCodeSymbol -> Option α)
    (encode : α -> Word MachineCodeSymbol) : Prop :=
  exists recognizer : MachineDescription,
    ClosedInputFamilyRecognizerSpec decode encode recognizer

/--
Concrete emitter that expands a public input word into the guarded
three-logical-tape input with blank scratch and blank output buffer.
-/
def structured3InputEmbeddingEmitterDescription : MachineDescription :=
  optionCellExpandAppendDescription

theorem structured3InputEmbeddingEmitterDescription_targetCellsRunSpec :
    Structured3InputEmbeddingEmitterTargetCellsRunSpec
      structured3InputEmbeddingEmitterDescription := by
  constructor
  · exact optionCellExpandAppendDescription_runSpec.ready
  · intro bits
    unfold structured3InputEmbeddingEmitterDescription
    unfold structured3InputEmbeddingEmitterTargetTape
    rw [← optionCellExpandAppendTargetCells_eq_structured3 bits]
    exact optionCellExpandAppendDescription_runSpec.forward bits

theorem structured3InputEmbeddingEmitterDescription_spec :
    Structured3InputMaterializerSpec
      (fun bits : Word Bool => Tape.input bits)
      (fun _bits : Word Bool => Tape.blank)
      structured3InputEmbeddingEmitterDescription :=
  structured3InputEmbeddingEmitterSpec_of_targetCellsRunSpec
    structured3InputEmbeddingEmitterDescription_targetCellsRunSpec

theorem structured3InputEmbeddingEmitterConstruction_core :
    Structured3InputEmbeddingEmitterConstruction :=
  ⟨structured3InputEmbeddingEmitterDescription,
    structured3InputEmbeddingEmitterDescription_spec⟩

/--
The reusable two-phase materializer table for a closed public code-family
recognizer followed by the shared structured-input embedding emitter.
-/
def closedRecognizerStructuredInputMaterializerDescription
    (recognizer emitter : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine recognizer emitter
    tapeCodePrimitiveCodeWordHandoffMove

theorem closedRecognizerStructuredEquivInputMaterializer_closedIndex_of_parts
    {α : Type}
    {decode : Word MachineCodeSymbol -> Option α}
    {encode : α -> Word MachineCodeSymbol}
    (hencodeCons :
      forall a : α,
        exists symbol : MachineCodeSymbol,
        exists tail : Word MachineCodeSymbol,
          encode a = symbol :: tail)
    {recognizer emitter : MachineDescription}
    (hrecognizer :
      ClosedInputFamilyRecognizerSpec
        decode encode recognizer)
    (hemitter :
      Structured3InputMaterializerSpec
        (fun bits : Word Bool => Tape.input bits)
        (fun _bits : Word Bool => Tape.blank)
        emitter) :
    EquivClosedIndexedFromTape
      (closedRecognizerStructuredInputMaterializerDescription
        recognizer emitter)
      (fun a : α =>
        EncRewriters.CanonicalLayouts.InputTape encode a)
      (Structured3EndpointEquivInputMaterializerInitialized
        (fun a : α =>
          EncRewriters.CanonicalLayouts.InputTape encode a)
        (fun _a => Tape.blank)) := by
  intro Tin T hhalt
  rcases
      MachineDescription.seqSubroutine_haltsFromTape_closed_exists_mid
        hrecognizer.canonical.left hemitter.left hhalt with
    ⟨Tmid, hrecognizerRun, hemitterRun⟩
  rcases hrecognizer.closedIndex Tin Tmid hrecognizerRun with
    ⟨a, hTin, hTmid⟩
  refine ⟨a, hTin, ?_⟩
  have hhandoff :
      Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid =
        EncRewriters.CanonicalLayouts.InputTape encode a := by
    rw [hTmid]
    exact
      EncRewriters.CanonicalLayouts.handoffTape_handoff
        hencodeCons a
  have hemitterActual :
      emitter.HaltsFromTape
        (EncRewriters.CanonicalLayouts.InputTape encode a) T := by
    simpa [hhandoff] using hemitterRun
  exact
    haltsFromTape_equiv_target_of_forward
      hemitter.left
      hemitterActual
      (hemitter.right
        (EncRewriters.CanonicalLayouts.Bits encode a))

theorem closedRecognizerStructuredEquivInputMaterializerSpec_of_parts
    {α : Type}
    {decode : Word MachineCodeSymbol -> Option α}
    {encode : α -> Word MachineCodeSymbol}
    (hencodeCons :
      forall a : α,
        exists symbol : MachineCodeSymbol,
        exists tail : Word MachineCodeSymbol,
          encode a = symbol :: tail)
    {recognizer emitter : MachineDescription}
    (hrecognizer :
      ClosedInputFamilyRecognizerSpec
        decode encode recognizer)
    (hemitter :
      Structured3InputMaterializerSpec
        (fun bits : Word Bool => Tape.input bits)
        (fun _bits : Word Bool => Tape.blank)
        emitter) :
    Structured3EndpointEquivInputMaterializerSpec
      (fun a : α =>
        EncRewriters.CanonicalLayouts.InputTape encode a)
      (fun _a => Tape.blank)
      (closedRecognizerStructuredInputMaterializerDescription
        recognizer emitter) := by
  constructor
  · constructor
    · exact
        MachineDescription.seqSubroutine_subroutineReady
          hrecognizer.canonical.left hemitter.left
    · intro a
      rcases hrecognizer.canonical.right.left a with ⟨nR, hR⟩
      let Tmid :=
        EncRewriters.CanonicalLayouts.HandoffTape encode a
      have hRfrom :
          recognizer.HaltsFromTape
            (EncRewriters.CanonicalLayouts.InputTape encode a)
            Tmid := by
        refine ⟨nR, ?_⟩
        simpa [EncRewriters.CanonicalLayouts.InputTape,
          EncRewriters.CanonicalLayouts.Bits, Tmid] using hR
      have hhandoff :
          Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid =
            EncRewriters.CanonicalLayouts.InputTape encode a := by
        simpa [Tmid] using
          EncRewriters.CanonicalLayouts.handoffTape_handoff
            hencodeCons a
      have hE :
          emitter.HaltsFromTapeEquiv
            (EncRewriters.CanonicalLayouts.InputTape encode a)
            (structured3InputMaterializerTargetTape
              (EncRewriters.CanonicalLayouts.InputTape encode a)
              Tape.blank) :=
        by
          simpa [EncRewriters.CanonicalLayouts.InputTape] using
            hemitter.right
              (EncRewriters.CanonicalLayouts.Bits encode a)
      simpa [closedRecognizerStructuredInputMaterializerDescription] using
        CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
          hrecognizer.canonical.left hemitter.left hRfrom hhandoff hE
  · exact
      closedRecognizerStructuredEquivInputMaterializer_closedIndex_of_parts
        hencodeCons hrecognizer hemitter

theorem closedRecognizerStructuredEquivInputMaterializerConstruction_of_parts
    {α : Type}
    {decode : Word MachineCodeSymbol -> Option α}
    {encode : α -> Word MachineCodeSymbol}
    (hencodeCons :
      forall a : α,
        exists symbol : MachineCodeSymbol,
        exists tail : Word MachineCodeSymbol,
          encode a = symbol :: tail)
    (hrecognizer :
      ClosedInputFamilyRecognizerConstruction
        decode encode)
    (hemitter : Structured3InputEmbeddingEmitterConstruction) :
    Structured3EndpointEquivInputMaterializerConstruction
      (fun a : α =>
        EncRewriters.CanonicalLayouts.InputTape encode a)
      (fun _a => Tape.blank) := by
  rcases hrecognizer with ⟨recognizer, hrecognizerSpec⟩
  rcases hemitter with ⟨emitter, hemitterSpec⟩
  exact
    ⟨closedRecognizerStructuredInputMaterializerDescription
        recognizer emitter,
      closedRecognizerStructuredEquivInputMaterializerSpec_of_parts
        hencodeCons hrecognizerSpec hemitterSpec⟩

namespace Structured3EndpointEquivIndexedMaterializerSpec

/--
Derive per-index equivalence closedness from equivalence-forward behavior and
subroutine determinism.
-/
theorem closed
    {ι : Type}
    {input initialized : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hspec :
      Structured3EndpointEquivIndexedMaterializerSpec
        input initialized materializer)
    (hready : materializer.SubroutineReady)
    (i : ι) :
    materializer.ClosedFromTapeEquiv (input i) (initialized i) :=
  closedFromTapeEquiv_of_haltsFromTapeEquiv_of_subroutineReady
    hready (hspec.forward i)

end Structured3EndpointEquivIndexedMaterializerSpec

namespace Structured3EndpointEquivInputMaterializerSpec

theorem subroutineReady
    {ι : Type}
    {input output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hspec :
      Structured3EndpointEquivInputMaterializerSpec
        input output materializer) :
    materializer.SubroutineReady :=
  hspec.inputSpec.left

theorem toEquivIndexedMaterializerSpec
    {ι : Type}
    {input output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hspec :
      Structured3EndpointEquivInputMaterializerSpec
        input output materializer) :
    Structured3EndpointEquivIndexedMaterializerSpec
      input
      (Structured3EndpointEquivInputMaterializerInitialized input output)
      materializer where
  forward := fun i =>
    CommonGround.FiniteTransducers.structured3InputMaterializerSpec_haltsFromTapeEquiv
      hspec.inputSpec i
  closedIndex := hspec.closedIndex

end Structured3EndpointEquivInputMaterializerSpec

namespace Structured3EndpointIndexedMaterializerSpec

/--
View exact indexed materializer data as equivalence-forward indexed
materializer data.
-/
theorem toEquivIndexedMaterializerSpec
    {ι : Type}
    {input initialized : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hspec :
      Structured3EndpointIndexedMaterializerSpec
        input initialized materializer) :
    Structured3EndpointEquivIndexedMaterializerSpec
      input initialized materializer where
  forward := fun i => (hspec.forward i).toEquiv
  closedIndex := by
    intro Tin T hhalt
    rcases hspec.closedIndex Tin T hhalt with
      ⟨i, hTin, hT⟩
    exact ⟨i, hTin, by rw [hT]; exact Tape.Equiv.refl _⟩

end Structured3EndpointIndexedMaterializerSpec

/--
Exact indexed materializer construction implies the equivalence-forward
indexed materializer construction.
-/
theorem structured3EndpointEquivIndexedMaterializerConstruction_of_exact
    {ι : Type}
    {input initialized : ι -> Tape Bool}
    (hmaterializer :
      Structured3EndpointIndexedMaterializerConstruction
        input initialized) :
    Structured3EndpointEquivIndexedMaterializerConstruction
      input initialized := by
  rcases hmaterializer with
    ⟨materializer, hready, hspec⟩
  exact
    ⟨materializer, hready,
      hspec.toEquivIndexedMaterializerSpec⟩

theorem structured3EndpointEquivIndexedMaterializerConstruction_of_inputMaterializer
    {ι : Type}
    {input output : ι -> Tape Bool}
    (hmaterializer :
      Structured3EndpointEquivInputMaterializerConstruction input output) :
    Structured3EndpointEquivIndexedMaterializerConstruction
      input
      (Structured3EndpointEquivInputMaterializerInitialized input output) := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      hspec.subroutineReady,
      hspec.toEquivIndexedMaterializerSpec⟩

theorem structured3EndpointEquivInputMaterializerSpec_of_indexed
    {ι : Type}
    {input initialized output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hready : materializer.SubroutineReady)
    (hspec :
      Structured3EndpointIndexedMaterializerSpec
        input initialized materializer)
    (hinitialized :
      forall i : ι,
        initialized i =
          Structured3EndpointEquivInputMaterializerInitialized
            input output i) :
    Structured3EndpointEquivInputMaterializerSpec
      input output materializer where
  inputSpec := by
    constructor
    · exact hready
    · intro i
      simpa [Structured3EndpointEquivInputMaterializerInitialized,
        hinitialized i] using
        (hspec.forward i).toEquiv
  closedIndex := by
    intro Tin T hhalt
    rcases hspec.closedIndex Tin T hhalt with
      ⟨i, hTin, hT⟩
    refine ⟨i, hTin, ?_⟩
    rw [hT, hinitialized i]
    exact Tape.Equiv.refl _

theorem structured3EndpointEquivInputMaterializerConstruction_of_indexed
    {ι : Type}
    {input initialized output : ι -> Tape Bool}
    (hmaterializer :
      Structured3EndpointIndexedMaterializerConstruction
        input initialized)
    (hinitialized :
      forall i : ι,
        initialized i =
          Structured3EndpointEquivInputMaterializerInitialized
            input output i) :
    Structured3EndpointEquivInputMaterializerConstruction
      input output := by
  rcases hmaterializer with
    ⟨materializer, hready, hspec⟩
  exact
    ⟨materializer,
      structured3EndpointEquivInputMaterializerSpec_of_indexed
        hready hspec hinitialized⟩

/--
Equivalence-forward lowered-core behavior for canonical endpoint leaves.

Unlike {name}`Structured3EndpointExactLoweredCoreSpec`, this spec is stated on
the logical initialized tape.  The endpoint sequencer absorbs the physical
handoff move through {name}`Tape.Equiv`.
-/
structure Structured3EndpointEquivLoweredCoreSpec {ι : Type}
    (initialized lowered : ι -> Tape Bool)
    (core : MachineDescription) : Prop where
  forward :
    forall i : ι,
      core.HaltsFromTapeEquiv (initialized i) (lowered i)
  closed :
    forall i : ι,
      core.ClosedFromTapeEquiv (initialized i) (lowered i)

namespace Structured3EndpointExactLoweredCoreSpec

/--
View exact lowered-core data on the physical sequencer handoff tape as
equivalence-forward data on the logical initialized tape.
-/
theorem toEquivLoweredCoreSpec
    {ι : Type}
    {initialized lowered : ι -> Tape Bool}
    {core : MachineDescription}
    (hspec :
      Structured3EndpointExactLoweredCoreSpec
        initialized lowered core) :
    Structured3EndpointEquivLoweredCoreSpec
      initialized lowered core where
  forward := by
    intro i
    exact
      HaltsFromTapeEquiv_of_input_equiv
        (D := core)
        (Tin := canonicalPrimitiveSeqHandoffTape (initialized i))
        (Tin' := initialized i)
        (Tout := lowered i)
        (canonicalPrimitiveSeqHandoffTape_equiv (initialized i))
        (hspec.forward i)
  closed := by
    intro i T hhalt
    rcases
        HaltsFromTapeEquiv_of_input_equiv
          (D := core)
          (Tin := initialized i)
          (Tin' := canonicalPrimitiveSeqHandoffTape (initialized i))
          (Tout := T)
          (Tape.Equiv.symm
            (canonicalPrimitiveSeqHandoffTape_equiv (initialized i)))
          hhalt with
      ⟨actual, hactual, hequiv⟩
    have hactualEq : actual = lowered i :=
      hspec.closed i actual hactual
    rw [hactualEq] at hequiv
    exact Tape.Equiv.symm hequiv

end Structured3EndpointExactLoweredCoreSpec

/--
Exact indexed endpoint data for the wrapped
materializer/lowered-core/projector pipeline.

The per-index fields give forward and exact closed behavior for valid inputs;
{lit}`initializerClosedIndex` is the public-input inversion fact used to prove that
arbitrary wrapper halts originate from one of those valid inputs.
-/
structure Structured3EndpointExactIndexedFamilySpec
    {ι : Type} (W : Structured3EndpointWrapper)
    (input initialized lowered output : ι -> Tape Bool) : Prop where
  initializerForward :
    forall i : ι,
      W.initializer.HaltsFromTape (input i) (initialized i)
  loweredForward :
    forall i : ι,
      W.lowered.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape (initialized i))
        (lowered i)
  projectorForward :
    forall i : ι,
      W.projector.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape (lowered i))
        (output i)
  initializerClosed :
    forall i : ι,
      ExactClosedFromTape W.initializer
        (input i) (initialized i)
  loweredClosed :
    forall i : ι,
      ExactClosedFromTape W.lowered
        (canonicalPrimitiveSeqHandoffTape (initialized i))
        (lowered i)
  projectorClosed :
    forall i : ι,
      ExactClosedFromTape W.projector
        (canonicalPrimitiveSeqHandoffTape (lowered i))
        (output i)
  initializerClosedIndex :
    ExactClosedIndexedFromTape W.initializer input initialized

namespace Structured3EndpointExactIndexedFamilySpec

theorem family
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W input initialized lowered output) :
    Structured3EndpointExactFamilySpec
      W input initialized lowered output where
  initializerForward := hspec.initializerForward
  loweredForward := hspec.loweredForward
  projectorForward := hspec.projectorForward
  initializerClosed := hspec.initializerClosed
  loweredClosed := hspec.loweredClosed
  projectorClosed := hspec.projectorClosed

theorem forward
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W input initialized lowered output)
    (i : ι) :
    W.machine.HaltsFromTape (input i) (output i) :=
  Structured3EndpointExactFamilySpec.forward (family hspec) i

theorem closed
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W input initialized lowered output)
    (i : ι) :
    ExactClosedFromTape W.machine (input i) (output i) :=
  Structured3EndpointExactFamilySpec.closed (family hspec) i

theorem closedIndex
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W input initialized lowered output) :
    ExactClosedIndexedFromTape W.machine input output := by
  intro Tin T hhalt
  rcases
      canonicalPrimitiveSeqDescription_haltsFromTape_inv
        (canonicalPrimitiveSeqDescription_subroutineReady
          W.initializerSubroutineReady W.lowered_subroutineReady)
        W.projectorSubroutineReady
        (by
          simpa [Structured3EndpointWrapper.machine] using hhalt) with
    ⟨TloweredActual, hfirst, hprojectorActual⟩
  rcases
      canonicalPrimitiveSeqDescription_haltsFromTape_inv
        W.initializerSubroutineReady
        W.lowered_subroutineReady
        hfirst with
    ⟨TinitActual, hinitializerActual, hloweredActual⟩
  rcases
      hspec.initializerClosedIndex Tin TinitActual
        hinitializerActual with
    ⟨i, hTin, hTinit⟩
  subst Tin
  subst TinitActual
  have hTlowered : TloweredActual = lowered i :=
    hspec.loweredClosed i TloweredActual
      (by
        simpa [canonicalPrimitiveSeqHandoffTape] using
          hloweredActual)
  subst TloweredActual
  have hT : T = output i :=
    hspec.projectorClosed i T
      (by
        simpa [canonicalPrimitiveSeqHandoffTape] using
          hprojectorActual)
  exact ⟨i, rfl, hT⟩

theorem closedIndex_eq
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W input initialized lowered output)
    {Tin T : Tape Bool}
    (hhalt : W.machine.HaltsFromTape Tin T) :
    exists i : ι, Tin = input i ∧ T = output i :=
  closedIndex hspec Tin T hhalt

end Structured3EndpointExactIndexedFamilySpec

/--
The generic canonical component spec implies the exact-indexed wrapper-family
spec used by public target adapters.
-/
theorem structured3EndpointExactIndexedFamilySpec_of_canonical
    {ι : Type}
    {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3CanonicalExactIndexedEndpointSpec
        W input initialized lowered output) :
    Structured3EndpointExactIndexedFamilySpec
      W input initialized lowered output where
  initializerForward := hspec.materializer.forward
  loweredForward := hspec.core.forward
  projectorForward := hspec.projector.forward
  initializerClosed := hspec.materializer.closed
  loweredClosed := hspec.core.closed
  projectorClosed := hspec.projector.closed
  initializerClosedIndex := hspec.materializer.closedIndex

/--
Equivalence indexed endpoint data for the wrapped endpoint pipeline.

This is useful for output-normalized contracts where the public final tape may
differ by harmless guard blanks, while the input inversion is still indexed.
-/
structure Structured3EndpointEquivIndexedFamilySpec
    {ι : Type} (W : Structured3EndpointWrapper)
    (input initialized lowered output : ι -> Tape Bool) : Prop where
  family :
    Structured3EndpointEquivFamilySpec
      W input initialized lowered output
  initializerClosedIndex :
    EquivClosedIndexedFromTape W.initializer input initialized

namespace Structured3EndpointEquivIndexedFamilySpec

theorem forward
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointEquivIndexedFamilySpec
        W input initialized lowered output)
    (i : ι) :
    W.machine.HaltsFromTapeEquiv (input i) (output i) :=
  Structured3EndpointEquivFamilySpec.forward hspec.family i

theorem closed
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointEquivIndexedFamilySpec
        W input initialized lowered output)
    (i : ι) :
    W.machine.ClosedFromTapeEquiv (input i) (output i) :=
  Structured3EndpointEquivFamilySpec.closed hspec.family i

theorem closedIndex
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointEquivIndexedFamilySpec
        W input initialized lowered output) :
    EquivClosedIndexedFromTape W.machine input output := by
  intro Tin T hhalt
  rcases
      canonicalPrimitiveSeqDescription_haltsFromTape_inv
        (canonicalPrimitiveSeqDescription_subroutineReady
          W.initializerSubroutineReady W.lowered_subroutineReady)
        W.projectorSubroutineReady
        (by
          simpa [Structured3EndpointWrapper.machine] using hhalt) with
    ⟨TloweredActual, hfirst, hprojectorActual⟩
  rcases
      canonicalPrimitiveSeqDescription_haltsFromTape_inv
        W.initializerSubroutineReady
        W.lowered_subroutineReady
        hfirst with
    ⟨TinitActual, hinitializerActual, hloweredActual⟩
  rcases
      hspec.initializerClosedIndex Tin TinitActual
        hinitializerActual with
    ⟨i, hTin, hTinit⟩
  have hLoweredInput :
      Tape.Equiv
        (canonicalPrimitiveSeqHandoffTape TinitActual)
        (initialized i) :=
    Tape.Equiv.trans
      (canonicalPrimitiveSeqHandoffTape_equiv TinitActual)
      hTinit
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (D := W.lowered)
        (Tin := canonicalPrimitiveSeqHandoffTape TinitActual)
        (Tin' := initialized i)
        (Tout := TloweredActual)
        hLoweredInput
        hloweredActual with
    ⟨TloweredFromIndex, hloweredFromIndex, hTloweredFromIndex⟩
  have hTlowered :
      Tape.Equiv TloweredActual (lowered i) :=
    Tape.Equiv.trans
      (Tape.Equiv.symm hTloweredFromIndex)
      (hspec.family.loweredClosed i
        TloweredFromIndex hloweredFromIndex)
  have hProjectorInput :
      Tape.Equiv
        (canonicalPrimitiveSeqHandoffTape TloweredActual)
        (lowered i) :=
    Tape.Equiv.trans
      (canonicalPrimitiveSeqHandoffTape_equiv TloweredActual)
      hTlowered
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        (D := W.projector)
        (Tin := canonicalPrimitiveSeqHandoffTape TloweredActual)
        (Tin' := lowered i)
        (Tout := T)
        hProjectorInput
        hprojectorActual with
    ⟨TprojectedFromIndex, hprojectorFromIndex,
      hTprojectedFromIndex⟩
  have hTprojected :
      Tape.Equiv TprojectedFromIndex (output i) :=
    hspec.family.projectorClosed i
      TprojectedFromIndex hprojectorFromIndex
  exact
    ⟨i, hTin,
      Tape.Equiv.trans
        (Tape.Equiv.symm hTprojectedFromIndex)
        hTprojected⟩

theorem closedIndex_equiv
    {ι : Type} {W : Structured3EndpointWrapper}
    {input initialized lowered output : ι -> Tape Bool}
    (hspec :
      Structured3EndpointEquivIndexedFamilySpec
        W input initialized lowered output)
    {Tin T : Tape Bool}
    (hhalt : W.machine.HaltsFromTape Tin T) :
    exists i : ι, Tin = input i ∧ Tape.Equiv T (output i) :=
  closedIndex hspec Tin T hhalt

end Structured3EndpointEquivIndexedFamilySpec

/--
Target-specific parser/core components for an equivalence-facing canonical
endpoint, before installing the shared tape-2 projector.

This is the prototype component shape for Phase 3: materializer and lowered
core obligations may be proved up to {name}`Tape.Equiv`, while arbitrary
initializer halts still carry an indexed inversion fact.
-/
structure Structured3CanonicalEquivEndpointCoreComponents
    {ι : Type}
    (input initialized lowered output tape0 tape1 : ι -> Tape Bool) where
  core : CommonGround.FiniteTransducers.Structured.Description
  initializer : MachineDescription
  coreWellFormed : core.WellFormed
  coreHaltTransitionFree : core.HaltTransitionFree
  coreSupportsRows : SupportsReadWriteRows3 core
  initializerSubroutineReady : initializer.SubroutineReady
  loweredShape :
    forall i : ι,
      lowered i =
        encodedGuardedStructured3Tapes
          (tape0 i) (tape1 i) (output i)
  materializer :
    Structured3EndpointEquivIndexedMaterializerSpec
      input initialized initializer
  loweredCore :
    Structured3EndpointEquivLoweredCoreSpec
      initialized lowered (lowerStructured3Description core)

/--
Existence wrapper for equivalence-facing parser/core endpoint components.
-/
def Structured3CanonicalEquivEndpointCoreComponentConstruction
    {ι : Type}
    (input initialized lowered output tape0 tape1 : ι -> Tape Bool) :
    Prop :=
  Nonempty
    (Structured3CanonicalEquivEndpointCoreComponents
      input initialized lowered output tape0 tape1)

/--
Target-specific lowered structured core data for an equivalence-facing
endpoint, before installing an input materializer.
-/
structure Structured3CanonicalEquivEndpointLoweredCoreComponents
    {ι : Type}
    (initialized lowered output tape0 tape1 : ι -> Tape Bool) where
  core : CommonGround.FiniteTransducers.Structured.Description
  coreWellFormed : core.WellFormed
  coreHaltTransitionFree : core.HaltTransitionFree
  coreSupportsRows : SupportsReadWriteRows3 core
  loweredShape :
    forall i : ι,
      lowered i =
        encodedGuardedStructured3Tapes
          (tape0 i) (tape1 i) (output i)
  loweredCore :
    Structured3EndpointEquivLoweredCoreSpec
      initialized lowered (lowerStructured3Description core)

/--
Existence wrapper for equivalence-facing lowered structured core data.
-/
def Structured3CanonicalEquivEndpointLoweredCoreConstruction
    {ι : Type}
    (initialized lowered output tape0 tape1 : ι -> Tape Bool) : Prop :=
  Nonempty
    (Structured3CanonicalEquivEndpointLoweredCoreComponents
      initialized lowered output tape0 tape1)

namespace Structured3CanonicalEquivEndpointLoweredCoreComponents

/--
Install an equivalence-forward indexed materializer in front of equivalence
lowered structured core data.
-/
def toCoreComponents
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalEquivEndpointLoweredCoreComponents
        initialized lowered output tape0 tape1)
    {initializer : MachineDescription}
    (hinitializerReady : initializer.SubroutineReady)
    (hmaterializer :
      Structured3EndpointEquivIndexedMaterializerSpec
        input initialized initializer) :
    Structured3CanonicalEquivEndpointCoreComponents
      input initialized lowered output tape0 tape1 where
  core := C.core
  initializer := initializer
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  initializerSubroutineReady := hinitializerReady
  loweredShape := C.loweredShape
  materializer := hmaterializer
  loweredCore := C.loweredCore

end Structured3CanonicalEquivEndpointLoweredCoreComponents

/--
Equivalence-forward indexed materializer construction plus equivalence
lowered structured core construction give equivalence endpoint-core
components.
-/
theorem structured3CanonicalEquivEndpointCoreComponentConstruction_of_materializer_loweredCore
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (hmaterializer :
      Structured3EndpointEquivIndexedMaterializerConstruction
        input initialized)
    (hcore :
      Structured3CanonicalEquivEndpointLoweredCoreConstruction
        initialized lowered output tape0 tape1) :
    Structured3CanonicalEquivEndpointCoreComponentConstruction
      input initialized lowered output tape0 tape1 := by
  rcases hmaterializer with
    ⟨initializer, hinitializerReady, hmaterializerSpec⟩
  rcases hcore with ⟨C⟩
  exact
    ⟨C.toCoreComponents hinitializerReady hmaterializerSpec⟩

namespace Structured3CanonicalExactEndpointLoweredCoreComponents

/--
Forget exact handoff-core behavior to the equivalence-facing lowered-core
component shape.
-/
def toEquivLoweredCoreComponents
    {ι : Type}
    {initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalExactEndpointLoweredCoreComponents
        initialized lowered output tape0 tape1) :
    Structured3CanonicalEquivEndpointLoweredCoreComponents
      initialized lowered output tape0 tape1 where
  core := C.core
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  loweredShape := C.loweredShape
  loweredCore := by
    simpa using C.loweredCore.toEquivLoweredCoreSpec

end Structured3CanonicalExactEndpointLoweredCoreComponents

/--
Exact lowered-core components imply equivalence-facing lowered-core
components.
-/
theorem structured3CanonicalEquivEndpointLoweredCoreConstruction_of_exact
    {ι : Type}
    {initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (hcore :
      Structured3CanonicalExactEndpointLoweredCoreConstruction
        initialized lowered output tape0 tape1) :
    Structured3CanonicalEquivEndpointLoweredCoreConstruction
      initialized lowered output tape0 tape1 := by
  rcases hcore with ⟨C⟩
  exact ⟨C.toEquivLoweredCoreComponents⟩

namespace Structured3CanonicalExactEndpointCoreComponents

/--
Forget exact materializer and handoff-core behavior to the equivalence-facing
endpoint-core component shape.
-/
def toEquivEndpointCoreComponents
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalExactEndpointCoreComponents
        input initialized lowered output tape0 tape1) :
    Structured3CanonicalEquivEndpointCoreComponents
      input initialized lowered output tape0 tape1 where
  core := C.core
  initializer := C.initializer
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  initializerSubroutineReady := C.initializerSubroutineReady
  loweredShape := C.loweredShape
  materializer :=
    C.materializer.toEquivIndexedMaterializerSpec
  loweredCore := by
    simpa using C.loweredCore.toEquivLoweredCoreSpec

end Structured3CanonicalExactEndpointCoreComponents

/--
Exact parser/core endpoint components imply the equivalence-facing component
construction.
-/
theorem structured3CanonicalEquivEndpointCoreComponentConstruction_of_exact
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (hcore :
      Structured3CanonicalExactEndpointCoreComponentConstruction
        input initialized lowered output tape0 tape1) :
    Structured3CanonicalEquivEndpointCoreComponentConstruction
      input initialized lowered output tape0 tape1 := by
  rcases hcore with ⟨C⟩
  exact ⟨C.toEquivEndpointCoreComponents⟩

/--
Full equivalence-facing canonical endpoint components, including the shared
tape-2 projector route.
-/
structure Structured3CanonicalEquivEndpointComponents
    {ι : Type}
    (input initialized lowered output tape0 tape1 : ι -> Tape Bool) where
  core : CommonGround.FiniteTransducers.Structured.Description
  initializer : MachineDescription
  projector : MachineDescription
  coreWellFormed : core.WellFormed
  coreHaltTransitionFree : core.HaltTransitionFree
  coreSupportsRows : SupportsReadWriteRows3 core
  initializerSubroutineReady : initializer.SubroutineReady
  projectorSubroutineReady : projector.SubroutineReady
  loweredShape :
    forall i : ι,
      lowered i =
        encodedGuardedStructured3Tapes
          (tape0 i) (tape1 i) (output i)
  materializer :
    Structured3EndpointEquivIndexedMaterializerSpec
      input initialized initializer
  loweredCore :
    Structured3EndpointEquivLoweredCoreSpec
      initialized lowered (lowerStructured3Description core)
  projectorRoute :
    Structured3EndpointTape2ProjectorSpec projector

/--
Existence wrapper for full equivalence-facing canonical endpoint components.
-/
def Structured3CanonicalEquivEndpointComponentConstruction
    {ι : Type}
    (input initialized lowered output tape0 tape1 : ι -> Tape Bool) :
    Prop :=
  Nonempty
    (Structured3CanonicalEquivEndpointComponents
      input initialized lowered output tape0 tape1)

namespace Structured3CanonicalEquivEndpointCoreComponents

/--
Install an equivalence-facing shared projector into equivalence-facing
parser/core endpoint components.
-/
def toEndpointComponents
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalEquivEndpointCoreComponents
        input initialized lowered output tape0 tape1)
    {projector : MachineDescription}
    (hprojector :
      Structured3EndpointTape2ProjectorSpec projector) :
    Structured3CanonicalEquivEndpointComponents
      input initialized lowered output tape0 tape1 where
  core := C.core
  initializer := C.initializer
  projector := projector
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  initializerSubroutineReady := C.initializerSubroutineReady
  projectorSubroutineReady := hprojector.subroutineReady
  loweredShape := C.loweredShape
  materializer := C.materializer
  loweredCore := C.loweredCore
  projectorRoute := hprojector

end Structured3CanonicalEquivEndpointCoreComponents

/--
Equivalence-facing parser/core components plus the shared tape-2 projector
give full equivalence-facing endpoint components.
-/
theorem structured3CanonicalEquivEndpointComponentConstruction_of_coreComponents
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (hcore :
      Structured3CanonicalEquivEndpointCoreComponentConstruction
        input initialized lowered output tape0 tape1)
    (hprojector :
      Structured3EndpointTape2ProjectorConstruction) :
    Structured3CanonicalEquivEndpointComponentConstruction
      input initialized lowered output tape0 tape1 := by
  rcases hcore with ⟨C⟩
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact ⟨C.toEndpointComponents hprojectorSpec⟩

namespace Structured3CanonicalEquivEndpointComponents

/--
Package equivalence-facing endpoint components as the reusable wrapper record.
-/
def wrapper
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalEquivEndpointComponents
        input initialized lowered output tape0 tape1) :
    Structured3EndpointWrapper where
  core := C.core
  initializer := C.initializer
  projector := C.projector
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  initializerSubroutineReady := C.initializerSubroutineReady
  projectorSubroutineReady := C.projectorSubroutineReady

/--
The equivalence-indexed endpoint family induced by equivalence-facing
components.
-/
theorem equivIndexedFamilySpec
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalEquivEndpointComponents
        input initialized lowered output tape0 tape1) :
    Structured3EndpointEquivIndexedFamilySpec
      C.wrapper input initialized lowered output where
  family := by
    constructor
    · exact C.materializer.forward
    · exact C.loweredCore.forward
    · intro i
      rw [C.loweredShape i]
      exact C.projectorRoute.forward (tape0 i) (tape1 i) (output i)
    · intro i
      exact
        C.materializer.closed C.initializerSubroutineReady i
    · exact C.loweredCore.closed
    · intro i T hhalt
      rw [C.loweredShape i] at hhalt
      exact
        C.projectorRoute.closed
          (tape0 i) (tape1 i) (output i) T hhalt
  initializerClosedIndex := C.materializer.closedIndex

end Structured3CanonicalEquivEndpointComponents

namespace Structured3CanonicalEquivEndpointSharedProjectorComponents

/--
The equivalence-indexed endpoint family induced by equivalence shared-projector
components.
-/
theorem equivIndexedFamilySpec
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalEquivEndpointSharedProjectorComponents
        input initialized lowered output tape0 tape1) :
    Structured3EndpointEquivIndexedFamilySpec
      C.wrapper input initialized lowered output where
  family := by
    constructor
    · intro i
      exact (C.materializer.forward i).toEquiv
    · intro i
      exact
        HaltsFromTapeEquiv_of_input_equiv
          (D := C.wrapper.lowered)
          (Tin := canonicalPrimitiveSeqHandoffTape (initialized i))
          (Tin' := initialized i)
          (Tout := lowered i)
          (canonicalPrimitiveSeqHandoffTape_equiv (initialized i))
          (by
            simpa [wrapper, Structured3EndpointWrapper.lowered] using
              C.loweredCore.forward i)
    · intro i
      rw [C.loweredShape i]
      exact
        C.projectorRoute.forward
          (tape0 i) (tape1 i) (output i)
    · intro i T hhalt
      rw [C.materializer.closed i T hhalt]
      exact Tape.Equiv.refl (initialized i)
    · intro i T hhalt
      rcases
          HaltsFromTapeEquiv_of_input_equiv
            (D := C.wrapper.lowered)
            (Tin := initialized i)
            (Tin' := canonicalPrimitiveSeqHandoffTape (initialized i))
            (Tout := T)
            (Tape.Equiv.symm
              (canonicalPrimitiveSeqHandoffTape_equiv (initialized i)))
            hhalt with
        ⟨actual, hactual, hequiv⟩
      have hactual : actual = lowered i :=
        C.loweredCore.closed i actual
          (by
            simpa [wrapper, Structured3EndpointWrapper.lowered] using
              hactual)
      rw [hactual] at hequiv
      exact Tape.Equiv.symm hequiv
    · intro i T hhalt
      rw [C.loweredShape i] at hhalt
      exact
        C.projectorRoute.closed
          (tape0 i) (tape1 i) (output i) T hhalt
  initializerClosedIndex := by
    intro Tin T hhalt
    rcases C.materializer.closedIndex Tin T hhalt with
      ⟨i, hTin, hT⟩
    exact ⟨i, hTin, by rw [hT]; exact Tape.Equiv.refl _⟩

end Structured3CanonicalEquivEndpointSharedProjectorComponents

/--
Generic public target shape for structured-core endpoint wrappers.

The {lit}`publicContract` argument is one of the ordinary one-tape
{name}`MachineDescription` contracts used by the finite scaffolds.
-/
def Structured3EndpointWrappedConstruction
    (publicContract : MachineDescription -> Prop) : Prop :=
  exists W : Structured3EndpointWrapper,
    publicContract W.machine

/-- Convert an exact tape halt from {lit}`Tape.input` into the usual word-input halt. -/
theorem haltsWithTape_of_haltsFromTape_input
    {D : MachineDescription} {w : Word Bool} {T : Tape Bool}
    (h : D.HaltsFromTape (Tape.input w) T) :
    D.HaltsWithTape w T := by
  rcases h with ⟨n, hn⟩
  exact
    ⟨n, by
      simpa [HaltsWithTapeIn, HaltsFromTapeIn, initial] using hn⟩

/-- Convert a word-input halt into an exact tape halt from {lit}`Tape.input`. -/
theorem haltsFromTape_input_of_haltsWithTape
    {D : MachineDescription} {w : Word Bool} {T : Tape Bool}
    (h : D.HaltsWithTape w T) :
    D.HaltsFromTape (Tape.input w) T := by
  rcases h with ⟨n, hn⟩
  exact
    ⟨n, by
      simpa [HaltsWithTapeIn, HaltsFromTapeIn, initial] using hn⟩


end StructuredConstructionTargets

end Computability
end FoC
