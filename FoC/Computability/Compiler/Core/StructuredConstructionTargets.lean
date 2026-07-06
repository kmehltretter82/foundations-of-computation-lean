import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Composition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ConcreteRefresh

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

def PairedRecognizerDovetailControllerStageAttemptFuelSimulatorStructuredCodeRightShiftedConstruction :
    Prop :=
  forall attempt : MachineDescription,
    Structured3EndpointWrappedConstruction
      (PairedRecognizerDovetailControllerStageAttemptFuelSimulatorRightShiftedSpec
        attempt)

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
  intro attempt
  -- Remaining structured finite-table obligation: give a three-logical-tape
  -- parser description whose lowered machine maps generated `(w, limit, fuel)`
  -- inputs to the canonical simulator-layout code word and halts one cell
  -- right of it.
  sorry

def PairedRecognizerDovetailStageAttemptFramedRunInvocationStructuredConstructionData :
    Prop :=
  forall attempt : MachineDescription,
    attempt.SubroutineReady ->
      Structured3EndpointWrappedConstruction
        (CommonGround.ControllerInvocation.StageAttemptFramedExactSpec
          attempt)

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
  intro attempt hattempt
  -- Remaining structured finite-table obligation: give a three-logical-tape
  -- framed invoker whose lowered machine installs the simulated boolean-word
  -- result in the controller layout and is closed over framed outputs.
  sorry

def PairedRecognizerDovetailControllerStageAttemptFuelOutputStructuredCodeSubroutineConstruction :
    Prop :=
  forall attempt : MachineDescription,
    Structured3EndpointWrappedConstruction
      (PairedRecognizerDovetailControllerStageAttemptFuelOutputCodeSubroutineSpec
        attempt)

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
  intro attempt
  -- Remaining structured finite-table obligation: give a three-logical-tape
  -- extractor whose lowered machine emits the normalized boolean-word result
  -- code on halted simulator layouts and rejects all other inputs.
  sorry

def PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction :
    Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      Structured3EndpointWrappedConstruction
        (PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpec
          runner)

theorem pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction_of_structured
    (h :
      PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction) :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorRightShiftedSpecConstruction := by
  intro runner hrunner
  rcases h runner hrunner with ⟨W, hspec⟩
  exact ⟨W.machine, hspec⟩

theorem pairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction_structuredLeaf :
    PairedRecognizerDovetailControllerStageAttemptBoundedFuelPairEnumeratorStructuredRightShiftedSpecConstruction := by
  intro runner hrunner
  -- Remaining structured finite-table obligation: enumerate bounded
  -- `(limit, fuel)` pairs, invoke the exact-fuel runner, preserve its encoded
  -- boolean-word output, and halt one cell right of that output for classifier
  -- handoff.
  sorry

end StructuredConstructionTargets

end Computability
end FoC
