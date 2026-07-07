import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Composition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ConcreteRefresh
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ProjectionHeadEndpointConstructions
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ProjectionHeadRoutes

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
Exact shared tape-2 projector route for canonical three-tape endpoints.

This is the stronger version of the current equivalence-based tape-2
projector contract: it must project the third guarded logical tape to the
literal represented tape, after the standard canonical-sequence handoff bounce.
-/
structure Structured3EndpointExactTape2ProjectorSpec
    (projector : MachineDescription) : Prop where
  subroutineReady : projector.SubroutineReady
  forward :
    forall T0 T1 T2 : Tape Bool,
      projector.HaltsFromTape
        (canonicalPrimitiveSeqHandoffTape
          (encodedGuardedStructured3Tapes T0 T1 T2))
        T2
  closed :
    forall T0 T1 T2 : Tape Bool,
      ExactClosedFromTape projector
        (canonicalPrimitiveSeqHandoffTape
          (encodedGuardedStructured3Tapes T0 T1 T2))
        T2

/--
Existence wrapper for the exact shared tape-2 projector route.
-/
def Structured3EndpointExactTape2ProjectorConstruction : Prop :=
  exists projector : MachineDescription,
    Structured3EndpointExactTape2ProjectorSpec projector

/--
The lower tape-2 exact projector route is the shared endpoint projector route
expected by canonical three-tape endpoint components.
-/
theorem structured3EndpointExactTape2ProjectorSpec_of_tape2ExactProjectorSpec
    {projector : MachineDescription}
    (hprojector :
      StructuredTape2ExactProjectorSpec projector) :
    Structured3EndpointExactTape2ProjectorSpec projector where
  subroutineReady := hprojector.subroutineReady
  forward := hprojector.forward
  closed := hprojector.closed

/--
Construction-level adapter from the lower exact tape-2 projector construction
to the shared endpoint projector construction.
-/
theorem structured3EndpointExactTape2ProjectorConstruction_of_tape2ExactProjectorConstruction
    (hprojector :
      StructuredTape2ExactProjectorConstruction) :
    Structured3EndpointExactTape2ProjectorConstruction := by
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact
    ⟨projector,
      structured3EndpointExactTape2ProjectorSpec_of_tape2ExactProjectorSpec
        hprojectorSpec⟩

/--
Exact selected-head decoding supplies the shared endpoint tape-2 projector.
-/
theorem structured3EndpointExactTape2ProjectorConstruction_of_exactHeadDecoder
    (hdecoder :
      StructuredSelectedHeadSegmentDecoderExactConstruction) :
    Structured3EndpointExactTape2ProjectorConstruction :=
  structured3EndpointExactTape2ProjectorConstruction_of_tape2ExactProjectorConstruction
    (structuredTape2ExactProjectorConstruction_of_exactHeadDecoder
      hdecoder)

/--
The shared endpoint tape-2 projector used by the structured construction
targets.

Its remaining finite-table obligations live in
{module}`FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ProjectionHeadEndpointConstructions`;
the four target leaves below should not duplicate that projector proof.
-/
theorem structured3EndpointExactTape2ProjectorConstruction_core :
    Structured3EndpointExactTape2ProjectorConstruction :=
  structured3EndpointExactTape2ProjectorConstruction_of_tape2ExactProjectorConstruction
    structuredTape2ExactProjectorConstruction_core

namespace Structured3EndpointExactTape2ProjectorSpec

/--
Specialize the shared exact tape-2 projector route to one indexed endpoint
family.
-/
theorem toEndpointProjectorSpec
    {ι : Type}
    {lowered output tape0 tape1 : ι -> Tape Bool}
    {projector : MachineDescription}
    (hprojector :
      Structured3EndpointExactTape2ProjectorSpec projector)
    (hlowered :
      forall i : ι,
        lowered i =
          encodedGuardedStructured3Tapes
            (tape0 i) (tape1 i) (output i)) :
    Structured3EndpointExactProjectorSpec
      lowered output projector where
  forward := by
    intro i
    simpa [hlowered i] using
      hprojector.forward (tape0 i) (tape1 i) (output i)
  closed := by
    intro i
    simpa [hlowered i] using
      hprojector.closed (tape0 i) (tape1 i) (output i)

end Structured3EndpointExactTape2ProjectorSpec

/--
Concrete endpoint components where the output projector is supplied by one
shared exact tape-2 projector route.

The {lit}`loweredShape` field records that the lowered structured core leaves the
public output on logical tape 2.  This lets all four leaves share the same
projector obligation while keeping their materializers and structured cores
target-specific.
-/
structure Structured3CanonicalExactEndpointSharedProjectorComponents
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
    Structured3EndpointExactTape2ProjectorSpec projector

/--
Existence wrapper for endpoint components that share an exact tape-2 projector
route.
-/
def Structured3CanonicalExactEndpointSharedProjectorConstruction
    {ι : Type}
    (input initialized lowered output tape0 tape1 : ι -> Tape Bool) : Prop :=
  Nonempty
    (Structured3CanonicalExactEndpointSharedProjectorComponents
      input initialized lowered output tape0 tape1)

/--
Canonical endpoint components before installing the shared output projector.

This is the target-specific part of the structured endpoint construction:
materialize the public input, run the lowered structured core, and prove that
the lowered output places the public result on logical tape 2.  The actual
tape-2 projector is supplied once by
{name}`structured3EndpointExactTape2ProjectorConstruction_core`.

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
Install a concrete shared projector into target-specific endpoint core
components.
-/
def toSharedProjectorComponents
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalExactEndpointCoreComponents
        input initialized lowered output tape0 tape1)
    {projector : MachineDescription}
    (hprojector :
      Structured3EndpointExactTape2ProjectorSpec projector) :
    Structured3CanonicalExactEndpointSharedProjectorComponents
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
Target-specific core components plus the shared exact tape-2 projector give
the shared-projector endpoint component package.
-/
theorem structured3CanonicalExactEndpointSharedProjectorConstruction_of_coreComponents
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (hcore :
      Structured3CanonicalExactEndpointCoreComponentConstruction
        input initialized lowered output tape0 tape1)
    (hprojector :
      Structured3EndpointExactTape2ProjectorConstruction) :
    Structured3CanonicalExactEndpointSharedProjectorConstruction
      input initialized lowered output tape0 tape1 := by
  rcases hcore with ⟨C⟩
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact
    ⟨C.toSharedProjectorComponents hprojectorSpec⟩

namespace Structured3CanonicalExactEndpointSharedProjectorComponents

/--
Forget the shared-projector view back to the concrete component record.
-/
def toComponents
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (C :
      Structured3CanonicalExactEndpointSharedProjectorComponents
        input initialized lowered output tape0 tape1) :
    Structured3CanonicalExactEndpointComponents
      input initialized lowered output where
  core := C.core
  initializer := C.initializer
  projector := C.projector
  coreWellFormed := C.coreWellFormed
  coreHaltTransitionFree := C.coreHaltTransitionFree
  coreSupportsRows := C.coreSupportsRows
  initializerSubroutineReady := C.initializerSubroutineReady
  projectorSubroutineReady := C.projectorSubroutineReady
  materializer := C.materializer
  loweredCore := C.loweredCore
  projectorSpec :=
    C.projectorRoute.toEndpointProjectorSpec C.loweredShape

end Structured3CanonicalExactEndpointSharedProjectorComponents

/--
Shared-projector components imply ordinary concrete endpoint components.
-/
theorem structured3CanonicalExactEndpointComponentConstruction_of_sharedProjector
    {ι : Type}
    {input initialized lowered output tape0 tape1 : ι -> Tape Bool}
    (h :
      Structured3CanonicalExactEndpointSharedProjectorConstruction
        input initialized lowered output tape0 tape1) :
    Structured3CanonicalExactEndpointComponentConstruction
      input initialized lowered output := by
  rcases h with ⟨C⟩
  exact
    ⟨Structured3CanonicalExactEndpointSharedProjectorComponents.toComponents
      C⟩

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

def FuelSimulatorStructuredIndex : Type :=
  Sigma (fun _w : Word Bool => Nat × Nat)

def fuelSimulatorStructuredInputCode
    (i : FuelSimulatorStructuredIndex) : Word MachineCodeSymbol :=
  PairedRecognizerDovetailControllerStageAttemptFuelInputCode
    i.1 i.2.1 i.2.2

def fuelSimulatorStructuredInputTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  Tape.input
    (encodeCodeWordAsInput
      (fuelSimulatorStructuredInputCode i))

def fuelSimulatorStructuredOutputTape
    (attempt : MachineDescription)
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  PairedRecognizerDovetailControllerStageAttemptFuelSimulatorOutputTape
    attempt i.1 i.2.1 i.2.2

def FuelSimulatorStructuredEndpointExactIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered : FuelSimulatorStructuredIndex -> Tape Bool,
    Structured3EndpointExactIndexedFamilySpec
      W
      fuelSimulatorStructuredInputTape
      initialized
      lowered
      (fuelSimulatorStructuredOutputTape attempt)

/--
Canonical blank output buffer used when materializing public fuel-simulator
parser inputs into the three-logical-tape core.
-/
def fuelSimulatorStructuredOutputBuffer
    (_i : FuelSimulatorStructuredIndex) : Tape Bool :=
  Tape.blank

/--
Canonical endpoint input to the lowered fuel-simulator structured core.

Tape 0 contains the public generated fuel-input code, tape 1 is blank scratch,
and tape 2 starts as a blank output buffer.
-/
def fuelSimulatorStructuredInitializedTape
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (fuelSimulatorStructuredInputTape i)
    (fuelSimulatorStructuredOutputBuffer i)

/--
Canonical endpoint output of the lowered fuel-simulator structured core.

The core preserves the public source on logical tape 0, keeps tape 1 blank, and
writes the exact simulator-layout output tape on logical tape 2.
-/
def fuelSimulatorStructuredLoweredTape
    (attempt : MachineDescription)
    (i : FuelSimulatorStructuredIndex) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (fuelSimulatorStructuredInputTape i)
    Tape.blank
    (fuelSimulatorStructuredOutputTape attempt i)

/--
Exact materializer behavior needed by the canonical fuel-simulator endpoint.
-/
def FuelSimulatorStructuredExactMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointExactMaterializerSpec
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    materializer

/--
Target-specific fuel-simulator materializer obligation before deterministic
per-input exact closedness is installed by the shared endpoint infrastructure.
-/
def FuelSimulatorStructuredIndexedMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerSpec
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    materializer

/--
Exact lowered-core behavior for the canonical fuel-simulator endpoint.
-/
def FuelSimulatorStructuredExactLoweredCoreSpec
    (attempt : MachineDescription)
    (lowered : MachineDescription) : Prop :=
  Structured3EndpointExactLoweredCoreSpec
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    lowered

/--
Exact projector behavior for the canonical fuel-simulator endpoint.
-/
def FuelSimulatorStructuredExactProjectorSpec
    (attempt : MachineDescription)
    (projector : MachineDescription) : Prop :=
  Structured3EndpointExactProjectorSpec
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    projector

/--
Canonical component-level fuel-simulator endpoint spec.
-/
def FuelSimulatorStructuredCanonicalEndpointSpec
    (attempt : MachineDescription)
    (W : Structured3EndpointWrapper) : Prop :=
  Structured3CanonicalExactIndexedEndpointSpec
    W
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)

/--
Canonical fuel-simulator endpoint construction with fixed materializer/core/
projector handoff tapes.
-/
def FuelSimulatorStructuredCanonicalEndpointConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    FuelSimulatorStructuredCanonicalEndpointSpec attempt W

/--
Concrete component data for the canonical fuel-simulator endpoint.

This is the finite-table construction target: an indexed public-input parser,
one three-tape structured core, and an exact tape-2 projector.
-/
def FuelSimulatorStructuredCanonicalEndpointComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)

/--
Existence form of the concrete fuel-simulator endpoint components.
-/
def FuelSimulatorStructuredCanonicalEndpointComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointComponentConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)

/--
Concrete fuel-simulator components imply the canonical wrapper endpoint
construction consumed by the public scaffold adapter.
-/
theorem fuelSimulatorStructuredCanonicalEndpointConstruction_of_components
    {attempt : MachineDescription}
    (hcomponents :
      FuelSimulatorStructuredCanonicalEndpointComponentConstruction
        attempt) :
    FuelSimulatorStructuredCanonicalEndpointConstruction attempt := by
  simpa [FuelSimulatorStructuredCanonicalEndpointConstruction,
    FuelSimulatorStructuredCanonicalEndpointSpec,
    FuelSimulatorStructuredCanonicalEndpointComponentConstruction] using
    structured3CanonicalExactIndexedEndpointConstruction_of_components
      hcomponents

/--
Fuel-simulator component data with the output projector factored through the
shared exact tape-2 projector route.
-/
def FuelSimulatorStructuredCanonicalEndpointSharedProjectorComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointSharedProjectorComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Existence form of the shared-projector fuel-simulator endpoint components.
-/
def FuelSimulatorStructuredCanonicalEndpointSharedProjectorConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointSharedProjectorConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Fuel-simulator parser/core components before installing the shared exact
tape-2 projector.
-/
def FuelSimulatorStructuredCanonicalEndpointCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointCoreComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Existence form for the fuel-simulator parser/core components without the
reusable endpoint projector.
-/
def FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointCoreComponentConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Fuel-simulator input parser/materializer construction, separated from the
lowered structured simulator core.
-/
def FuelSimulatorStructuredIndexedMaterializerConstruction : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInputTape i)
    (fun i => fuelSimulatorStructuredInitializedTape i)

/--
Fuel-simulator lowered structured core data after input materialization.
-/
def FuelSimulatorStructuredLoweredCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointLoweredCoreComponents
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Existence form for the fuel-simulator lowered structured core.
-/
def FuelSimulatorStructuredLoweredCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointLoweredCoreConstruction
    (fun i : FuelSimulatorStructuredIndex =>
      fuelSimulatorStructuredInitializedTape i)
    (fun i => fuelSimulatorStructuredLoweredTape attempt i)
    (fun i => fuelSimulatorStructuredOutputTape attempt i)
    (fun i => fuelSimulatorStructuredInputTape i)
    (fun _i : FuelSimulatorStructuredIndex => Tape.blank)

/--
Combine the fuel-simulator parser/materializer and lowered core into the
no-projector endpoint component obligation.
-/
theorem fuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    {attempt : MachineDescription}
    (hmaterializer :
      FuelSimulatorStructuredIndexedMaterializerConstruction)
    (hcore :
      FuelSimulatorStructuredLoweredCoreConstruction attempt) :
    FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction
      attempt := by
  simpa [FuelSimulatorStructuredIndexedMaterializerConstruction,
    FuelSimulatorStructuredLoweredCoreConstruction,
    FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction] using
    structured3CanonicalExactEndpointCoreComponentConstruction_of_materializer_loweredCore
      hmaterializer hcore

/--
Install the shared exact tape-2 projector into fuel-simulator core components.
-/
theorem fuelSimulatorStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
    {attempt : MachineDescription}
    (hcore :
      FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction
        attempt)
    (hprojector :
      Structured3EndpointExactTape2ProjectorConstruction) :
    FuelSimulatorStructuredCanonicalEndpointSharedProjectorConstruction
      attempt := by
  simpa [FuelSimulatorStructuredCanonicalEndpointCoreComponentConstruction,
    FuelSimulatorStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointSharedProjectorConstruction_of_coreComponents
      hcore hprojector

/--
Shared-projector fuel-simulator components imply ordinary concrete endpoint
components.
-/
theorem fuelSimulatorStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
    {attempt : MachineDescription}
    (hcomponents :
      FuelSimulatorStructuredCanonicalEndpointSharedProjectorConstruction
        attempt) :
    FuelSimulatorStructuredCanonicalEndpointComponentConstruction
      attempt := by
  simpa [FuelSimulatorStructuredCanonicalEndpointComponentConstruction,
    FuelSimulatorStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointComponentConstruction_of_sharedProjector
      hcomponents

theorem fuelSimulatorStructuredExactIndexedSpec_of_canonical
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    (hspec :
      FuelSimulatorStructuredCanonicalEndpointSpec attempt W) :
    Structured3EndpointExactIndexedFamilySpec
      (ι := FuelSimulatorStructuredIndex)
      W
      (fun i => fuelSimulatorStructuredInputTape i)
      (fun i => fuelSimulatorStructuredInitializedTape i)
      (fun i => fuelSimulatorStructuredLoweredTape attempt i)
      (fun i => fuelSimulatorStructuredOutputTape attempt i) :=
  structured3EndpointExactIndexedFamilySpec_of_canonical hspec

theorem fuelSimulatorStructuredEndpointExactIndexedConstruction_of_canonical
    {attempt : MachineDescription}
    (hcanonical :
      FuelSimulatorStructuredCanonicalEndpointConstruction attempt) :
    FuelSimulatorStructuredEndpointExactIndexedConstruction attempt := by
  rcases hcanonical with ⟨W, hspec⟩
  exact
    ⟨W,
      fuelSimulatorStructuredInitializedTape,
      fuelSimulatorStructuredLoweredTape attempt,
      fuelSimulatorStructuredExactIndexedSpec_of_canonical hspec⟩

/--
Remaining structured-core endpoint obligation for the fuel-simulator parser.
The proof must build the wrapped endpoint for every compiled attempt machine.
-/
def FuelSimulatorStructuredCoreEndpointConstruction : Prop :=
  forall attempt : MachineDescription,
    FuelSimulatorStructuredEndpointExactIndexedConstruction attempt

/--
Canonical fuel-simulator endpoint obligations imply the existing flexible
exact-indexed core endpoint obligation.
-/
theorem fuelSimulatorStructuredCoreEndpointConstruction_of_canonical
    (hcanonical :
      forall attempt : MachineDescription,
        FuelSimulatorStructuredCanonicalEndpointConstruction attempt) :
    FuelSimulatorStructuredCoreEndpointConstruction := by
  intro attempt
  exact
    fuelSimulatorStructuredEndpointExactIndexedConstruction_of_canonical
      (hcanonical attempt)

theorem fuelSimulatorStructuredInputCode_eq_of_inputTape_eq
    {code : Word MachineCodeSymbol}
    {i : FuelSimulatorStructuredIndex}
    (h :
      Tape.input (encodeCodeWordAsInput code) =
        fuelSimulatorStructuredInputTape i) :
    code = fuelSimulatorStructuredInputCode i := by
  apply encodeCodeWordAsInput_injective
  exact
    Tape.input_injective
      (by
        simpa [fuelSimulatorStructuredInputTape] using h)

theorem fuelSimulatorRightShiftedSpec_of_endpointExactIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered : FuelSimulatorStructuredIndex -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W
        fuelSimulatorStructuredInputTape
        initialized
        lowered
        (fuelSimulatorStructuredOutputTape attempt)) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpec
      attempt W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro w limit fuel
    simpa [fuelSimulatorStructuredInputTape,
      fuelSimulatorStructuredInputCode,
      fuelSimulatorStructuredOutputTape] using
      haltsWithTape_of_haltsFromTape_input
        (Structured3EndpointExactIndexedFamilySpec.forward
          hspec ⟨w, (limit, fuel)⟩)
  · intro code T hhalt
    have hfrom :
        W.machine.HaltsFromTape
          (Tape.input (encodeCodeWordAsInput code)) T :=
      haltsFromTape_input_of_haltsWithTape hhalt
    rcases
        Structured3EndpointExactIndexedFamilySpec.closedIndex
          hspec
          (Tape.input (encodeCodeWordAsInput code)) T
          hfrom with
      ⟨i, hinput, hT⟩
    have hcode : code = fuelSimulatorStructuredInputCode i :=
      fuelSimulatorStructuredInputCode_eq_of_inputTape_eq hinput
    exact
      ⟨i.1, i.2.1, i.2.2,
        by
          simpa [fuelSimulatorStructuredInputCode] using hcode,
        by
          simpa [fuelSimulatorStructuredOutputTape] using hT⟩

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction :
    Prop :=
  forall attempt : MachineDescription,
    Structured3EndpointWrappedConstruction
      (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpec
        attempt)

theorem fuelSimulatorStructuredConstruction_of_endpointExactIndexed
    (h :
      forall attempt : MachineDescription,
        FuelSimulatorStructuredEndpointExactIndexedConstruction attempt) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction := by
  intro attempt
  rcases h attempt with ⟨W, initialized, lowered, hspec⟩
  exact
    ⟨W,
      fuelSimulatorRightShiftedSpec_of_endpointExactIndexed
        (attempt := attempt)
        (W := W)
        (initialized := initialized)
        (lowered := lowered)
        hspec⟩

theorem fuelSimulatorStructuredConstruction_of_coreEndpoint
    (h : FuelSimulatorStructuredCoreEndpointConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction :=
  fuelSimulatorStructuredConstruction_of_endpointExactIndexed h

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction := by
  exact
    pairedRecognizerDovetailControllerStageAttemptFuelSimulatorCodeRightShiftedConstruction_of_spec
      (by
        intro attempt
        rcases h attempt with ⟨W, hspec⟩
        exact ⟨W.machine, hspec⟩)

theorem pairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction_structuredLeaf :
    PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction := by
  exact
    fuelSimulatorStructuredConstruction_of_coreEndpoint
      (fuelSimulatorStructuredCoreEndpointConstruction_of_canonical
        (by
          intro attempt
          exact
            fuelSimulatorStructuredCanonicalEndpointConstruction_of_components
              (fuelSimulatorStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
                (fuelSimulatorStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
                  (by
                    -- Remaining structured finite-table obligation: build the
                    -- concrete parser/materializer and simulator core whose
                    -- lowered output places the exact simulator-layout output
                    -- on logical tape 2.
                    sorry)
                  structured3EndpointExactTape2ProjectorConstruction_core))))

def PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      Structured3EndpointWrappedConstruction
        (CommonGround.ControllerInvocation.StageAttemptFramedExactSpec
          attempt)

/--
Index for framed invocation endpoint runs: a controller layout, a boolean-word
result, and a concrete fuel witness for the underlying attempt run.
-/
structure StageAttemptFramedStructuredIndex
    (attempt : MachineDescription) where
  C : DovetailControllerLayout
  result : Word Bool
  fuel : Nat
  attempt_halts :
    attempt.HaltsWithOutputIn fuel
      (encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageInputCode C))
      (encodeCodeWordAsInput (encodeBoolWord result))

def stageAttemptFramedStructuredInputTape
    {attempt : MachineDescription}
    (i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  Tape.input
    (encodeCodeWordAsInput
      (DovetailControllerLayout.encode i.C))

def stageAttemptFramedStructuredOutputTape
    {attempt : MachineDescription}
    (i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
    i.C i.result

def StageAttemptFramedStructuredEndpointExactIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered :
      StageAttemptFramedStructuredIndex attempt -> Tape Bool,
    Structured3EndpointExactIndexedFamilySpec
      W
      stageAttemptFramedStructuredInputTape
      initialized
      lowered
      stageAttemptFramedStructuredOutputTape

/--
Canonical blank output buffer used when materializing framed-invocation public
inputs into the three-logical-tape core.
-/
def stageAttemptFramedStructuredOutputBuffer
    {attempt : MachineDescription}
    (_i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  Tape.blank

/--
Canonical endpoint input to the lowered framed-invocation structured core.

Tape 0 contains the public controller-layout input, tape 1 is blank scratch,
and tape 2 starts as a blank output buffer.
-/
def stageAttemptFramedStructuredInitializedTape
    {attempt : MachineDescription}
    (i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (stageAttemptFramedStructuredInputTape i)
    (stageAttemptFramedStructuredOutputBuffer i)

/--
Canonical endpoint output of the lowered framed-invocation structured core.

The core preserves the source layout on logical tape 0, keeps tape 1 blank, and
writes the exact framed controller-output tape on logical tape 2.
-/
def stageAttemptFramedStructuredLoweredTape
    {attempt : MachineDescription}
    (i : StageAttemptFramedStructuredIndex attempt) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (stageAttemptFramedStructuredInputTape i)
    Tape.blank
    (stageAttemptFramedStructuredOutputTape i)

/--
Exact materializer behavior needed by the canonical framed-invocation endpoint.
-/
def StageAttemptFramedStructuredExactMaterializerSpec
    (attempt : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointExactMaterializerSpec
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    materializer

/--
Target-specific framed-invocation materializer obligation before deterministic
per-input exact closedness is installed by the shared endpoint infrastructure.
-/
def StageAttemptFramedStructuredIndexedMaterializerSpec
    (attempt : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerSpec
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    materializer

/--
Exact lowered-core behavior for the canonical framed-invocation endpoint.
-/
def StageAttemptFramedStructuredExactLoweredCoreSpec
    (attempt : MachineDescription)
    (lowered : MachineDescription) : Prop :=
  Structured3EndpointExactLoweredCoreSpec
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    lowered

/--
Exact projector behavior for the canonical framed-invocation endpoint.
-/
def StageAttemptFramedStructuredExactProjectorSpec
    (attempt : MachineDescription)
    (projector : MachineDescription) : Prop :=
  Structured3EndpointExactProjectorSpec
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    projector

/--
Canonical component-level framed-invocation endpoint spec.
-/
def StageAttemptFramedStructuredCanonicalEndpointSpec
    (attempt : MachineDescription)
    (W : Structured3EndpointWrapper) : Prop :=
  Structured3CanonicalExactIndexedEndpointSpec
    W
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)

/--
Canonical framed-invocation endpoint construction with fixed
materializer/core/projector handoff tapes.
-/
def StageAttemptFramedStructuredCanonicalEndpointConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    StageAttemptFramedStructuredCanonicalEndpointSpec attempt W

/--
Concrete component data for the canonical framed-invocation endpoint.

The indexed input family includes the proof that the delegated attempt halts
with the boolean-word result, so the structured core only has to handle the
closed framed wrapper contract at that witnessed endpoint.
-/
def StageAttemptFramedStructuredCanonicalEndpointComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointComponents
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)

/--
Existence form of the concrete framed-invocation endpoint components.
-/
def StageAttemptFramedStructuredCanonicalEndpointComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointComponentConstruction
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)

/--
Concrete framed-invocation components imply the canonical wrapper endpoint
construction consumed by the public scaffold adapter.
-/
theorem stageAttemptFramedStructuredCanonicalEndpointConstruction_of_components
    {attempt : MachineDescription}
    (hcomponents :
      StageAttemptFramedStructuredCanonicalEndpointComponentConstruction
        attempt) :
    StageAttemptFramedStructuredCanonicalEndpointConstruction
      attempt := by
  simpa [StageAttemptFramedStructuredCanonicalEndpointConstruction,
    StageAttemptFramedStructuredCanonicalEndpointSpec,
    StageAttemptFramedStructuredCanonicalEndpointComponentConstruction] using
    structured3CanonicalExactIndexedEndpointConstruction_of_components
      hcomponents

/--
Framed-invocation component data with the output projector factored through
the shared exact tape-2 projector route.
-/
def StageAttemptFramedStructuredCanonicalEndpointSharedProjectorComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointSharedProjectorComponents
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Existence form of the shared-projector framed-invocation endpoint components.
-/
def StageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointSharedProjectorConstruction
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Framed-invocation parser/core components before installing the shared exact
tape-2 projector.
-/
def StageAttemptFramedStructuredCanonicalEndpointCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointCoreComponents
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Existence form for framed-invocation parser/core components without the
reusable endpoint projector.
-/
def StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointCoreComponentConstruction
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Framed-invocation input parser/materializer construction, separated from the
lowered structured framed wrapper core.
-/
def StageAttemptFramedStructuredIndexedMaterializerConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInputTape i)
    (fun i => stageAttemptFramedStructuredInitializedTape i)

/--
Framed-invocation lowered structured core data after input materialization.
-/
def StageAttemptFramedStructuredLoweredCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointLoweredCoreComponents
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Existence form for the framed-invocation lowered structured core.
-/
def StageAttemptFramedStructuredLoweredCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointLoweredCoreConstruction
    (fun i : StageAttemptFramedStructuredIndex attempt =>
      stageAttemptFramedStructuredInitializedTape i)
    (fun i => stageAttemptFramedStructuredLoweredTape i)
    (fun i => stageAttemptFramedStructuredOutputTape i)
    (fun i => stageAttemptFramedStructuredInputTape i)
    (fun _i : StageAttemptFramedStructuredIndex attempt => Tape.blank)

/--
Combine the framed-invocation parser/materializer and lowered core into the
no-projector endpoint component obligation.
-/
theorem stageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    {attempt : MachineDescription}
    (hmaterializer :
      StageAttemptFramedStructuredIndexedMaterializerConstruction
        attempt)
    (hcore :
      StageAttemptFramedStructuredLoweredCoreConstruction attempt) :
    StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction
      attempt := by
  simpa [StageAttemptFramedStructuredIndexedMaterializerConstruction,
    StageAttemptFramedStructuredLoweredCoreConstruction,
    StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction] using
    structured3CanonicalExactEndpointCoreComponentConstruction_of_materializer_loweredCore
      hmaterializer hcore

/--
Install the shared exact tape-2 projector into framed-invocation core
components.
-/
theorem stageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
    {attempt : MachineDescription}
    (hcore :
      StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction
        attempt)
    (hprojector :
      Structured3EndpointExactTape2ProjectorConstruction) :
    StageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction
      attempt := by
  simpa [
    StageAttemptFramedStructuredCanonicalEndpointCoreComponentConstruction,
    StageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointSharedProjectorConstruction_of_coreComponents
      hcore hprojector

/--
Shared-projector framed-invocation components imply ordinary concrete
endpoint components.
-/
theorem stageAttemptFramedStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
    {attempt : MachineDescription}
    (hcomponents :
      StageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction
        attempt) :
    StageAttemptFramedStructuredCanonicalEndpointComponentConstruction
      attempt := by
  simpa [StageAttemptFramedStructuredCanonicalEndpointComponentConstruction,
    StageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointComponentConstruction_of_sharedProjector
      hcomponents

theorem stageAttemptFramedStructuredExactIndexedSpec_of_canonical
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    (hspec :
      StageAttemptFramedStructuredCanonicalEndpointSpec attempt W) :
    Structured3EndpointExactIndexedFamilySpec
      (ι := StageAttemptFramedStructuredIndex attempt)
      W
      (fun i => stageAttemptFramedStructuredInputTape i)
      (fun i => stageAttemptFramedStructuredInitializedTape i)
      (fun i => stageAttemptFramedStructuredLoweredTape i)
      (fun i => stageAttemptFramedStructuredOutputTape i) :=
  structured3EndpointExactIndexedFamilySpec_of_canonical hspec

theorem stageAttemptFramedStructuredEndpointExactIndexedConstruction_of_canonical
    {attempt : MachineDescription}
    (hcanonical :
      StageAttemptFramedStructuredCanonicalEndpointConstruction attempt) :
    StageAttemptFramedStructuredEndpointExactIndexedConstruction
      attempt := by
  rcases hcanonical with ⟨W, hspec⟩
  exact
    ⟨W,
      stageAttemptFramedStructuredInitializedTape,
      stageAttemptFramedStructuredLoweredTape,
      stageAttemptFramedStructuredExactIndexedSpec_of_canonical hspec⟩

/--
Remaining structured-core endpoint obligation for framed stage-attempt
invocation.  The attempt readiness hypothesis is part of the target contract.
-/
def StageAttemptFramedStructuredCoreEndpointConstruction : Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      StageAttemptFramedStructuredEndpointExactIndexedConstruction attempt

/--
Canonical framed-invocation endpoint obligations imply the existing flexible
exact-indexed core endpoint obligation.
-/
theorem stageAttemptFramedStructuredCoreEndpointConstruction_of_canonical
    (hcanonical :
      forall attempt : MachineDescription,
        attempt.SubroutineReady ->
          StageAttemptFramedStructuredCanonicalEndpointConstruction
            attempt) :
    StageAttemptFramedStructuredCoreEndpointConstruction := by
  intro attempt hattempt
  exact
    stageAttemptFramedStructuredEndpointExactIndexedConstruction_of_canonical
      (hcanonical attempt hattempt)

theorem stageAttemptFramedInput_layout_eq_of_inputTape_eq
    {attempt : MachineDescription}
    {C : DovetailControllerLayout}
    {i : StageAttemptFramedStructuredIndex attempt}
    (h :
      Tape.input
          (encodeCodeWordAsInput
            (DovetailControllerLayout.encode C)) =
        stageAttemptFramedStructuredInputTape i) :
    C = i.C := by
  apply DovetailControllerLayout.encode_injective
  apply encodeCodeWordAsInput_injective
  exact
    Tape.input_injective
      (by
        simpa [stageAttemptFramedStructuredInputTape] using h)

theorem stageAttemptFramedOutput_result_eq_of_tape_eq
    {attempt : MachineDescription}
    {C : DovetailControllerLayout}
    {result : Word Bool}
    {i : StageAttemptFramedStructuredIndex attempt}
    {T : Tape Bool}
    (hT : T = stageAttemptFramedStructuredOutputTape i)
    (houtput :
      Tape.normalizedOutput T =
        encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult C result)))
    (hC : C = i.C) :
    i.result = result := by
  have hout :
      Tape.normalizedOutput
          (stageAttemptFramedStructuredOutputTape i) =
        encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult i.C i.result)) := by
    simpa [stageAttemptFramedStructuredOutputTape] using
      CommonGround.ControllerInvocation.stageAttemptFramedOutputTape_normalizedOutput
        i.C i.result
  have hbits :
      encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult i.C i.result)) =
        encodeCodeWordAsInput
          (DovetailControllerLayout.encode
            (DovetailControllerLayout.withResult i.C result)) := by
    rw [← hout, ← hT, houtput, hC]
  have hcode :
      DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult i.C i.result) =
        DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult i.C result) :=
    encodeCodeWordAsInput_injective hbits
  have hlayout :
      DovetailControllerLayout.withResult i.C i.result =
        DovetailControllerLayout.withResult i.C result :=
    DovetailControllerLayout.encode_injective hcode
  have hresult := congrArg DovetailControllerLayout.result hlayout
  simpa [DovetailControllerLayout.withResult] using hresult

theorem stageAttemptFramedExactSpec_of_endpointExactIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered :
      StageAttemptFramedStructuredIndex attempt -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W
        stageAttemptFramedStructuredInputTape
        initialized
        lowered
        stageAttemptFramedStructuredOutputTape) :
    CommonGround.ControllerInvocation.StageAttemptFramedExactSpec
      attempt W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro C result fuel hattempt
    let i : StageAttemptFramedStructuredIndex attempt :=
      { C := C
        result := result
        fuel := fuel
        attempt_halts := hattempt }
    simpa [stageAttemptFramedStructuredInputTape,
      stageAttemptFramedStructuredOutputTape, i] using
      haltsWithTape_of_haltsFromTape_input
        (Structured3EndpointExactIndexedFamilySpec.forward hspec i)
  · intro C result hhalt
    let inputBits :=
      encodeCodeWordAsInput
        (DovetailControllerLayout.encode C)
    let outputBits :=
      encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult C result))
    rcases hhalt with ⟨fuel, hhaltFuel⟩
    let T :=
      (W.machine.runConfig fuel (W.machine.initial inputBits)).tape
    have hfrom :
        W.machine.HaltsFromTape (Tape.input inputBits) T := by
      exact
        ⟨fuel,
          by
            rcases hhaltFuel with ⟨hstate, _houtput⟩
            exact ⟨hstate, rfl⟩⟩
    rcases
        Structured3EndpointExactIndexedFamilySpec.closedIndex
          hspec (Tape.input inputBits) T hfrom with
      ⟨i, hinput, hT⟩
    have hC : C = i.C := by
      exact
        stageAttemptFramedInput_layout_eq_of_inputTape_eq
          (attempt := attempt)
          (C := C)
          (i := i)
          (by
            simpa [inputBits] using hinput)
    have houtput :
        Tape.normalizedOutput T =
          encodeCodeWordAsInput
            (DovetailControllerLayout.encode
              (DovetailControllerLayout.withResult C result)) := by
      rcases hhaltFuel with ⟨_hstate, hnormalized⟩
      simpa [T, outputBits] using hnormalized
    have hresult : i.result = result :=
      stageAttemptFramedOutput_result_eq_of_tape_eq
        (attempt := attempt)
        (C := C)
        (result := result)
        (i := i)
        (T := T)
        hT houtput hC
    exact
      ⟨i.fuel,
        by
          simpa [hC, hresult] using i.attempt_halts⟩

theorem stageAttemptFramedStructuredConstruction_of_endpointExactIndexed
    (h :
      forall attempt : MachineDescription,
        attempt.SubroutineReady ->
          StageAttemptFramedStructuredEndpointExactIndexedConstruction
            attempt) :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData := by
  intro attempt hattempt
  rcases h attempt hattempt with ⟨W, initialized, lowered, hspec⟩
  exact
    ⟨W,
      stageAttemptFramedExactSpec_of_endpointExactIndexed
        (attempt := attempt)
        (W := W)
        (initialized := initialized)
        (lowered := lowered)
        hspec⟩

theorem stageAttemptFramedStructuredConstruction_of_coreEndpoint
    (h : StageAttemptFramedStructuredCoreEndpointConstruction) :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData :=
  stageAttemptFramedStructuredConstruction_of_endpointExactIndexed h

theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationConstructionData_of_structured
    (h :
      PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData) :
    CommonGround.ControllerInvocation.StageAttemptFramedConstruction := by
  exact
    CommonGround.ControllerInvocation.stageAttemptFramedConstruction_of_exact
      (by
        intro attempt hattempt
        rcases h attempt hattempt with ⟨W, hspec⟩
        exact ⟨W.machine, hspec⟩)

theorem pairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData_structuredLeaf :
    PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData := by
  exact
    stageAttemptFramedStructuredConstruction_of_coreEndpoint
      (stageAttemptFramedStructuredCoreEndpointConstruction_of_canonical
        (by
          intro attempt hattempt
          exact
            stageAttemptFramedStructuredCanonicalEndpointConstruction_of_components
              (stageAttemptFramedStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
                (stageAttemptFramedStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
                  (by
                    -- Remaining structured finite-table obligation: build the
                    -- framed-invocation parser/materializer and structured
                    -- core that installs the simulated boolean-word result on
                    -- logical tape 2.
                    sorry)
                  structured3EndpointExactTape2ProjectorConstruction_core))))

def fuelOutputStructuredInputTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  Tape.input
    (encodeCodeWordAsInput
      (PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
        i))

def FuelOutputStructuredEndpointExactIndexedConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt -> Tape Bool,
    Structured3EndpointExactIndexedFamilySpec
      W
      fuelOutputStructuredInputTape
      initialized
      lowered
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape

/--
Canonical blank output buffer used when materializing a public simulator-layout
input into the three-logical-tape fuel-output extractor core.
-/
def fuelOutputStructuredOutputBuffer
    {attempt : MachineDescription}
    (_i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  Tape.blank

/--
Canonical endpoint input to the lowered fuel-output structured core.

Tape 0 contains the public simulator-layout code, tape 1 is blank scratch, and
tape 2 starts as a blank output buffer.
-/
def fuelOutputStructuredInitializedTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (fuelOutputStructuredInputTape i)
    (fuelOutputStructuredOutputBuffer i)

/--
Canonical endpoint output of the lowered fuel-output structured core.

The structured core preserves the source code on tape 0 for debugging and
closedness accounting, keeps tape 1 blank, and writes the exact public output
tape on logical tape 2.  The endpoint projector then exposes tape 2 as the
public final tape.
-/
def fuelOutputStructuredLoweredTape
    {attempt : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (fuelOutputStructuredInputTape i)
    Tape.blank
    (PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)

/--
Exact materializer behavior needed by the canonical fuel-output endpoint.
-/
def FuelOutputStructuredExactMaterializerSpec
    (attempt : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointExactMaterializerSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    materializer

/--
Target-specific fuel-output materializer obligation before deterministic
per-input exact closedness is installed by the shared endpoint infrastructure.
-/
def FuelOutputStructuredIndexedMaterializerSpec
    (attempt : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    materializer

/--
Exact lowered-core behavior for the canonical fuel-output endpoint.
-/
def FuelOutputStructuredExactLoweredCoreSpec
    (attempt : MachineDescription)
    (lowered : MachineDescription) : Prop :=
  Structured3EndpointExactLoweredCoreSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    lowered

/--
Exact projector behavior for the canonical fuel-output endpoint.
-/
def FuelOutputStructuredExactProjectorSpec
    (attempt : MachineDescription)
    (projector : MachineDescription) : Prop :=
  Structured3EndpointExactProjectorSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredLoweredTape i)
    (fun i => PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    projector

/--
Canonical component-level fuel-output endpoint spec.

This fixes the endpoint tapes that the remaining structured finite-table proof
must target, while still exposing the reusable exact-indexed endpoint API to
the public scaffold adapters.
-/
def FuelOutputStructuredCanonicalEndpointSpec
    (attempt : MachineDescription)
    (W : Structured3EndpointWrapper) : Prop :=
  Structured3CanonicalExactIndexedEndpointSpec
    W
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)

/--
Canonical fuel-output endpoint construction with fixed materializer/core/
projector handoff tapes.
-/
def FuelOutputStructuredCanonicalEndpointConstruction
    (attempt : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    FuelOutputStructuredCanonicalEndpointSpec attempt W

/--
Concrete component data for the canonical fuel-output endpoint.

This is the current first real extractor target from the middle-path plan:
the parser validates a public halted simulator layout, the three-tape core
extracts the result code onto logical tape 2, and the projector exposes that
exact tape as the public output.
-/
def FuelOutputStructuredCanonicalEndpointComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)

/--
Existence form of the concrete fuel-output endpoint components.
-/
def FuelOutputStructuredCanonicalEndpointComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointComponentConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)

/--
Concrete fuel-output components imply the canonical wrapper endpoint
construction consumed by the public scaffold adapter.
-/
theorem fuelOutputStructuredCanonicalEndpointConstruction_of_components
    {attempt : MachineDescription}
    (hcomponents :
      FuelOutputStructuredCanonicalEndpointComponentConstruction
        attempt) :
    FuelOutputStructuredCanonicalEndpointConstruction attempt := by
  simpa [FuelOutputStructuredCanonicalEndpointConstruction,
    FuelOutputStructuredCanonicalEndpointSpec,
    FuelOutputStructuredCanonicalEndpointComponentConstruction] using
    structured3CanonicalExactIndexedEndpointConstruction_of_components
      hcomponents

/--
Fuel-output component data with the output projector factored through the
shared exact tape-2 projector route.
-/
def FuelOutputStructuredCanonicalEndpointSharedProjectorComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointSharedProjectorComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Existence form of the shared-projector fuel-output endpoint components.
-/
def FuelOutputStructuredCanonicalEndpointSharedProjectorConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointSharedProjectorConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Fuel-output parser/core components before installing the shared exact tape-2
projector.
-/
def FuelOutputStructuredCanonicalEndpointCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointCoreComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Existence form for fuel-output parser/core components without the reusable
endpoint projector.
-/
def FuelOutputStructuredCanonicalEndpointCoreComponentConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointCoreComponentConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Fuel-output input parser/materializer construction, separated from the lowered
structured extractor core.
-/
def FuelOutputStructuredIndexedMaterializerConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInputTape i)
    (fun i => fuelOutputStructuredInitializedTape i)

/--
Fuel-output lowered structured extractor core data after input materialization.
-/
def FuelOutputStructuredLoweredCoreComponents
    (attempt : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointLoweredCoreComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Existence form for the fuel-output lowered structured extractor core.
-/
def FuelOutputStructuredLoweredCoreConstruction
    (attempt : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointLoweredCoreConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      fuelOutputStructuredInitializedTape i)
    (fun i => fuelOutputStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i)
    (fun i => fuelOutputStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt =>
      Tape.blank)

/--
Combine the fuel-output parser/materializer and lowered extractor core into
the no-projector endpoint component obligation.
-/
theorem fuelOutputStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    {attempt : MachineDescription}
    (hmaterializer :
      FuelOutputStructuredIndexedMaterializerConstruction
        attempt)
    (hcore :
      FuelOutputStructuredLoweredCoreConstruction attempt) :
    FuelOutputStructuredCanonicalEndpointCoreComponentConstruction
      attempt := by
  simpa [FuelOutputStructuredIndexedMaterializerConstruction,
    FuelOutputStructuredLoweredCoreConstruction,
    FuelOutputStructuredCanonicalEndpointCoreComponentConstruction] using
    structured3CanonicalExactEndpointCoreComponentConstruction_of_materializer_loweredCore
      hmaterializer hcore

/--
Install the shared exact tape-2 projector into fuel-output core components.
-/
theorem fuelOutputStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
    {attempt : MachineDescription}
    (hcore :
      FuelOutputStructuredCanonicalEndpointCoreComponentConstruction
        attempt)
    (hprojector :
      Structured3EndpointExactTape2ProjectorConstruction) :
    FuelOutputStructuredCanonicalEndpointSharedProjectorConstruction
      attempt := by
  simpa [FuelOutputStructuredCanonicalEndpointCoreComponentConstruction,
    FuelOutputStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointSharedProjectorConstruction_of_coreComponents
      hcore hprojector

/--
Shared-projector fuel-output components imply ordinary concrete endpoint
components.
-/
theorem fuelOutputStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
    {attempt : MachineDescription}
    (hcomponents :
      FuelOutputStructuredCanonicalEndpointSharedProjectorConstruction
        attempt) :
    FuelOutputStructuredCanonicalEndpointComponentConstruction
      attempt := by
  simpa [FuelOutputStructuredCanonicalEndpointComponentConstruction,
    FuelOutputStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointComponentConstruction_of_sharedProjector
      hcomponents

theorem fuelOutputStructuredExactIndexedSpec_of_canonical
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    (hspec :
      FuelOutputStructuredCanonicalEndpointSpec attempt W) :
    Structured3EndpointExactIndexedFamilySpec
      (ι :=
        PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
          attempt)
      W
      (fun i => fuelOutputStructuredInputTape i)
      (fun i => fuelOutputStructuredInitializedTape i)
      (fun i => fuelOutputStructuredLoweredTape i)
      (fun i =>
        PairedRecognizerDovetailControllerStageAttemptFuelOutputTape i) :=
  structured3EndpointExactIndexedFamilySpec_of_canonical hspec

theorem fuelOutputStructuredEndpointExactIndexedConstruction_of_canonical
    {attempt : MachineDescription}
    (hcanonical :
      FuelOutputStructuredCanonicalEndpointConstruction attempt) :
    FuelOutputStructuredEndpointExactIndexedConstruction attempt := by
  rcases hcanonical with ⟨W, hspec⟩
  exact
    ⟨W,
      fuelOutputStructuredInitializedTape,
      fuelOutputStructuredLoweredTape,
      fuelOutputStructuredExactIndexedSpec_of_canonical hspec⟩

/--
Remaining structured-core endpoint obligation for the simulator-output
extractor, indexed by halted simulator layouts and their exact output code.
-/
def FuelOutputStructuredCoreEndpointConstruction : Prop :=
  forall attempt : MachineDescription,
    FuelOutputStructuredEndpointExactIndexedConstruction attempt

/--
Canonical fuel-output endpoint obligations imply the existing flexible
exact-indexed core endpoint obligation.
-/
theorem fuelOutputStructuredCoreEndpointConstruction_of_canonical
    (hcanonical :
      forall attempt : MachineDescription,
        FuelOutputStructuredCanonicalEndpointConstruction attempt) :
    FuelOutputStructuredCoreEndpointConstruction := by
  intro attempt
  exact
    fuelOutputStructuredEndpointExactIndexedConstruction_of_canonical
      (hcanonical attempt)

theorem fuelOutputInputCode_eq_of_inputTape_eq
    {attempt : MachineDescription}
    {code : Word MachineCodeSymbol}
    {i :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt}
    (h :
      Tape.input (encodeCodeWordAsInput code) =
        fuelOutputStructuredInputTape i) :
    code =
      PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
        i := by
  apply encodeCodeWordAsInput_injective
  exact
    Tape.input_injective
      (by
        simpa [fuelOutputStructuredInputTape] using h)

theorem fuelOutputCodeSubroutineSpec_of_endpointExactIndexed
    {attempt : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputIndex
        attempt -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W
        fuelOutputStructuredInputTape
        initialized
        lowered
        PairedRecognizerDovetailControllerStageAttemptFuelOutputTape) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
      attempt W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro i
    simpa [fuelOutputStructuredInputTape] using
      haltsWithTape_of_haltsFromTape_input
        (Structured3EndpointExactIndexedFamilySpec.forward hspec i)
  · intro code T hhalt
    have hfrom :
        W.machine.HaltsFromTape
          (Tape.input (encodeCodeWordAsInput code)) T :=
      haltsFromTape_input_of_haltsWithTape hhalt
    rcases
        Structured3EndpointExactIndexedFamilySpec.closedIndex
          hspec
          (Tape.input (encodeCodeWordAsInput code)) T
          hfrom with
      ⟨i, hinput, hT⟩
    have hcode :
        code =
          PairedRecognizerDovetailControllerStageAttemptFuelOutputInputCode
            i :=
      fuelOutputInputCode_eq_of_inputTape_eq hinput
    exact ⟨i, hcode, hT⟩

def PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction :
    Prop :=
  forall attempt : MachineDescription,
    Structured3EndpointWrappedConstruction
      (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
        attempt)

theorem fuelOutputStructuredConstruction_of_endpointExactIndexed
    (h :
      forall attempt : MachineDescription,
        FuelOutputStructuredEndpointExactIndexedConstruction attempt) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction := by
  intro attempt
  rcases h attempt with ⟨W, initialized, lowered, hspec⟩
  exact
    ⟨W,
      fuelOutputCodeSubroutineSpec_of_endpointExactIndexed
        (attempt := attempt)
        (W := W)
        (initialized := initialized)
        (lowered := lowered)
        hspec⟩

theorem fuelOutputStructuredConstruction_of_coreEndpoint
    (h : FuelOutputStructuredCoreEndpointConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction :=
  fuelOutputStructuredConstruction_of_endpointExactIndexed h

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction) :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction := by
  exact
    pairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineConstruction_of_spec
      (by
        intro attempt
        rcases h attempt with ⟨W, hspec⟩
        exact ⟨W.machine, hspec⟩)

theorem pairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction_structuredLeaf :
    PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction := by
  exact
    fuelOutputStructuredConstruction_of_coreEndpoint
      (fuelOutputStructuredCoreEndpointConstruction_of_canonical
        (by
          intro attempt
          exact
            fuelOutputStructuredCanonicalEndpointConstruction_of_components
              (fuelOutputStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
                (fuelOutputStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
                  (by
                    -- Remaining structured finite-table obligation: build the
                    -- fuel-output parser/materializer and structured core
                    -- whose logical tape 2 is the normalized boolean-word
                    -- result code for halted simulator layouts.
                    sorry)
                  structured3EndpointExactTape2ProjectorConstruction_core))))

def boundedFuelPairEnumeratorStructuredInputTape
    {runner : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  Tape.input i.input

def BoundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction
    (runner : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
  exists initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner -> Tape Bool,
    Structured3EndpointExactIndexedFamilySpec
      W
      boundedFuelPairEnumeratorStructuredInputTape
      initialized
      lowered
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape

/--
Canonical blank output buffer used when materializing bounded fuel-pair
enumerator inputs into the three-logical-tape core.
-/
def boundedFuelPairEnumeratorStructuredOutputBuffer
    {runner : MachineDescription}
    (_i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  Tape.blank

/--
Canonical endpoint input to the lowered bounded fuel-pair enumerator core.

Tape 0 contains the public right-shifted enumerator input, tape 1 is blank
scratch, and tape 2 starts as a blank output buffer.
-/
def boundedFuelPairEnumeratorStructuredInitializedTape
    {runner : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
    (boundedFuelPairEnumeratorStructuredInputTape i)
    (boundedFuelPairEnumeratorStructuredOutputBuffer i)

/--
Canonical endpoint output of the lowered bounded fuel-pair enumerator core.

The core preserves the public source on logical tape 0, keeps tape 1 blank, and
writes the exact right-shifted enumerator output tape on logical tape 2.
-/
def boundedFuelPairEnumeratorStructuredLoweredTape
    {runner : MachineDescription}
    (i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (boundedFuelPairEnumeratorStructuredInputTape i)
    Tape.blank
    (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
      i)

/--
Exact materializer behavior needed by the canonical bounded enumerator endpoint.
-/
def BoundedFuelPairEnumeratorStructuredExactMaterializerSpec
    (runner : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointExactMaterializerSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    materializer

/--
Target-specific bounded-enumerator materializer obligation before deterministic
per-input exact closedness is installed by the shared endpoint infrastructure.
-/
def BoundedFuelPairEnumeratorStructuredIndexedMaterializerSpec
    (runner : MachineDescription)
    (materializer : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    materializer

/--
Exact lowered-core behavior for the canonical bounded enumerator endpoint.
-/
def BoundedFuelPairEnumeratorStructuredExactLoweredCoreSpec
    (runner : MachineDescription)
    (lowered : MachineDescription) : Prop :=
  Structured3EndpointExactLoweredCoreSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    lowered

/--
Exact projector behavior for the canonical bounded enumerator endpoint.
-/
def BoundedFuelPairEnumeratorStructuredExactProjectorSpec
    (runner : MachineDescription)
    (projector : MachineDescription) : Prop :=
  Structured3EndpointExactProjectorSpec
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    projector

/--
Canonical component-level bounded fuel-pair enumerator endpoint spec.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointSpec
    (runner : MachineDescription)
    (W : Structured3EndpointWrapper) : Prop :=
  Structured3CanonicalExactIndexedEndpointSpec
    W
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)

/--
Canonical bounded fuel-pair enumerator endpoint construction with fixed
materializer/core/projector handoff tapes.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction
    (runner : MachineDescription) : Prop :=
  exists W : Structured3EndpointWrapper,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointSpec runner W

/--
Concrete component data for the canonical bounded fuel-pair enumerator
endpoint.

The structured core is allowed to use the ready exact-fuel runner supplied by
the surrounding leaf obligation, but the public wrapper still has one fixed
parser/core/projector endpoint shape.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponents
    (runner : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)

/--
Existence form of the concrete bounded fuel-pair enumerator endpoint
components.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction
    (runner : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointComponentConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)

/--
Concrete bounded fuel-pair enumerator components imply the canonical wrapper
endpoint construction consumed by the public scaffold adapter.
-/
theorem boundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction_of_components
    {runner : MachineDescription}
    (hcomponents :
      BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction
        runner) :
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction
      runner := by
  simpa [BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointSpec,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction] using
    structured3CanonicalExactIndexedEndpointConstruction_of_components
      hcomponents

/--
Bounded fuel-pair enumerator component data with the output projector factored
through the shared exact tape-2 projector route.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorComponents
    (runner : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointSharedProjectorComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Existence form of the shared-projector bounded fuel-pair enumerator endpoint
components.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction
    (runner : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointSharedProjectorConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Bounded fuel-pair enumerator parser/core components before installing the
shared exact tape-2 projector.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponents
    (runner : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointCoreComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Existence form for bounded fuel-pair enumerator parser/core components without
the reusable endpoint projector.
-/
def BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction
    (runner : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointCoreComponentConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Bounded-enumerator input parser/materializer construction, separated from the
lowered structured enumerator core.
-/
def BoundedFuelPairEnumeratorStructuredIndexedMaterializerConstruction
    (runner : MachineDescription) : Prop :=
  Structured3EndpointIndexedMaterializerConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInputTape i)
    (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)

/--
Bounded-enumerator lowered structured core data after input materialization.
-/
def BoundedFuelPairEnumeratorStructuredLoweredCoreComponents
    (runner : MachineDescription) : Type :=
  Structured3CanonicalExactEndpointLoweredCoreComponents
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Existence form for the bounded-enumerator lowered structured core.
-/
def BoundedFuelPairEnumeratorStructuredLoweredCoreConstruction
    (runner : MachineDescription) : Prop :=
  Structured3CanonicalExactEndpointLoweredCoreConstruction
    (fun i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      boundedFuelPairEnumeratorStructuredInitializedTape i)
    (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
    (fun i =>
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
        i)
    (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
    (fun _i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner =>
      Tape.blank)

/--
Combine the bounded-enumerator parser/materializer and lowered core into the
no-projector endpoint component obligation.
-/
theorem boundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
    {runner : MachineDescription}
    (hmaterializer :
      BoundedFuelPairEnumeratorStructuredIndexedMaterializerConstruction
        runner)
    (hcore :
      BoundedFuelPairEnumeratorStructuredLoweredCoreConstruction
        runner) :
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction
      runner := by
  simpa [
    BoundedFuelPairEnumeratorStructuredIndexedMaterializerConstruction,
    BoundedFuelPairEnumeratorStructuredLoweredCoreConstruction,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction] using
    structured3CanonicalExactEndpointCoreComponentConstruction_of_materializer_loweredCore
      hmaterializer hcore

/--
Install the shared exact tape-2 projector into bounded fuel-pair enumerator
core components.
-/
theorem boundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
    {runner : MachineDescription}
    (hcore :
      BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction
        runner)
    (hprojector :
      Structured3EndpointExactTape2ProjectorConstruction) :
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction
      runner := by
  simpa [
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointCoreComponentConstruction,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointSharedProjectorConstruction_of_coreComponents
      hcore hprojector

/--
Shared-projector bounded fuel-pair enumerator components imply ordinary
concrete endpoint components.
-/
theorem boundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
    {runner : MachineDescription}
    (hcomponents :
      BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction
        runner) :
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction
      runner := by
  simpa [
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction,
    BoundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction] using
    structured3CanonicalExactEndpointComponentConstruction_of_sharedProjector
      hcomponents

theorem boundedFuelPairEnumeratorStructuredExactIndexedSpec_of_canonical
    {runner : MachineDescription}
    {W : Structured3EndpointWrapper}
    (hspec :
      BoundedFuelPairEnumeratorStructuredCanonicalEndpointSpec runner W) :
    Structured3EndpointExactIndexedFamilySpec
      (ι :=
        PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
          runner)
      W
      (fun i => boundedFuelPairEnumeratorStructuredInputTape i)
      (fun i => boundedFuelPairEnumeratorStructuredInitializedTape i)
      (fun i => boundedFuelPairEnumeratorStructuredLoweredTape i)
      (fun i =>
        PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape
          i) :=
  structured3EndpointExactIndexedFamilySpec_of_canonical hspec

theorem boundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction_of_canonical
    {runner : MachineDescription}
    (hcanonical :
      BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction
        runner) :
    BoundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction
      runner := by
  rcases hcanonical with ⟨W, hspec⟩
  exact
    ⟨W,
      boundedFuelPairEnumeratorStructuredInitializedTape,
      boundedFuelPairEnumeratorStructuredLoweredTape,
      boundedFuelPairEnumeratorStructuredExactIndexedSpec_of_canonical
        hspec⟩

/--
Remaining structured-core endpoint obligation for bounded {lit}`(limit, fuel)`
enumeration against a ready exact-fuel runner.
-/
def BoundedFuelPairEnumeratorStructuredCoreEndpointConstruction
    (runner : MachineDescription) : Prop :=
    runner.SubroutineReady ->
    BoundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction
      runner

/--
Canonical bounded fuel-pair enumerator endpoint obligations imply the existing
flexible exact-indexed core endpoint obligation.
-/
theorem boundedFuelPairEnumeratorStructuredCoreEndpointConstruction_of_canonical
    (hcanonical :
      forall runner : MachineDescription,
        runner.SubroutineReady ->
          BoundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction
            runner) :
    forall runner : MachineDescription,
      BoundedFuelPairEnumeratorStructuredCoreEndpointConstruction runner := by
  intro runner hrunner
  exact
    boundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction_of_canonical
      (hcanonical runner hrunner)

theorem boundedFuelPairEnumeratorInput_eq_of_inputTape_eq
    {runner : MachineDescription}
    {w : Word Bool}
    {i :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner}
    (h :
      Tape.input w =
        boundedFuelPairEnumeratorStructuredInputTape i) :
    w = i.input := by
  exact
    Tape.input_injective
      (by
        simpa [boundedFuelPairEnumeratorStructuredInputTape] using h)

theorem boundedFuelPairEnumeratorRightShiftedSpec_of_endpointExactIndexed
    {runner : MachineDescription}
    {W : Structured3EndpointWrapper}
    {initialized lowered :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorWitness
        runner -> Tape Bool}
    (hspec :
      Structured3EndpointExactIndexedFamilySpec
        W
        boundedFuelPairEnumeratorStructuredInputTape
        initialized
        lowered
        PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedOutputTape) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpec
      runner W.machine := by
  constructor
  · exact W.machine_subroutineReady
  constructor
  · intro i
    simpa [boundedFuelPairEnumeratorStructuredInputTape] using
      haltsWithTape_of_haltsFromTape_input
        (Structured3EndpointExactIndexedFamilySpec.forward hspec i)
  · intro w T hhalt
    have hfrom :
        W.machine.HaltsFromTape (Tape.input w) T :=
      haltsFromTape_input_of_haltsWithTape hhalt
    rcases
        Structured3EndpointExactIndexedFamilySpec.closedIndex
          hspec (Tape.input w) T hfrom with
      ⟨i, hinput, hT⟩
    have hw : w = i.input :=
      boundedFuelPairEnumeratorInput_eq_of_inputTape_eq hinput
    exact ⟨i, hw, hT⟩

def PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction :
    Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      Structured3EndpointWrappedConstruction
        (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpec
          runner)

theorem boundedFuelPairEnumeratorStructuredConstruction_of_endpointExactIndexed
    (h :
      forall runner : MachineDescription,
        runner.SubroutineReady ->
          BoundedFuelPairEnumeratorStructuredEndpointExactIndexedConstruction
            runner) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction := by
  intro runner hrunner
  rcases h runner hrunner with ⟨W, initialized, lowered, hspec⟩
  exact
    ⟨W,
      boundedFuelPairEnumeratorRightShiftedSpec_of_endpointExactIndexed
        (runner := runner)
        (W := W)
        (initialized := initialized)
        (lowered := lowered)
        hspec⟩

theorem boundedFuelPairEnumeratorStructuredConstruction_of_coreEndpoint
    (h :
      forall runner : MachineDescription,
        BoundedFuelPairEnumeratorStructuredCoreEndpointConstruction
          runner) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction :=
  boundedFuelPairEnumeratorStructuredConstruction_of_endpointExactIndexed h

theorem pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction := by
  intro runner hrunner
  rcases h runner hrunner with ⟨W, hspec⟩
  exact ⟨W.machine, hspec⟩

theorem pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction_structuredLeaf :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction := by
  exact
    boundedFuelPairEnumeratorStructuredConstruction_of_coreEndpoint
      (boundedFuelPairEnumeratorStructuredCoreEndpointConstruction_of_canonical
        (by
          intro runner hrunner
          exact
            boundedFuelPairEnumeratorStructuredCanonicalEndpointConstruction_of_components
              (boundedFuelPairEnumeratorStructuredCanonicalEndpointComponentConstruction_of_sharedProjector
                (boundedFuelPairEnumeratorStructuredCanonicalEndpointSharedProjectorConstruction_of_coreComponents
                  (by
                    -- Remaining structured finite-table obligation: build the
                    -- bounded fuel-pair parser/materializer and structured
                    -- core that enumerates bounded fuel pairs, invokes the
                    -- exact-fuel runner endpoint, and leaves the right-shifted
                    -- classifier handoff tape on logical tape 2.
                    sorry)
                  structured3EndpointExactTape2ProjectorConstruction_core))))

end StructuredConstructionTargets

end Computability
end FoC
