import Lean
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base

set_option doc.verso true

namespace FoC
namespace Computability
namespace StructuredConstructionTargets

open Languages
open MachineDescription
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open Lean
open Lean.Parser

macro "declare_structured_endpoint" 
  "Prefix:" P:ident 
  "lowerPrefix:" p:ident 
  "Param:" "(" param:ident ":" paramTy:term ")"
  "Index:" idxTy:term 
  "InputTape:" inTape:term 
  "OutputTape:" outTape:term : command => do

  let EndpointExactIndexedConstruction := mkIdentFrom P (P.getId.appendAfter "EndpointExactIndexedConstruction")
  let EndpointEquivIndexedConstruction := mkIdentFrom P (P.getId.appendAfter "EndpointEquivIndexedConstruction")
  let OutputBuffer := mkIdentFrom p (p.getId.appendAfter "OutputBuffer")
  let InitializedTape := mkIdentFrom p (p.getId.appendAfter "InitializedTape")
  let LoweredTape := mkIdentFrom p (p.getId.appendAfter "LoweredTape")
  let ExactMaterializerSpec := mkIdentFrom P (P.getId.appendAfter "ExactMaterializerSpec")
  let IndexedMaterializerSpec := mkIdentFrom P (P.getId.appendAfter "IndexedMaterializerSpec")
  let ExactLoweredCoreSpec := mkIdentFrom P (P.getId.appendAfter "ExactLoweredCoreSpec")
  let CanonicalEndpointSpec := mkIdentFrom P (P.getId.appendAfter "CanonicalEndpointSpec")
  let CanonicalEndpointConstruction := mkIdentFrom P (P.getId.appendAfter "CanonicalEndpointConstruction")
  let CanonicalEndpointComponents := mkIdentFrom P (P.getId.appendAfter "CanonicalEndpointComponents")
  let CanonicalEndpointComponentConstruction := mkIdentFrom P (P.getId.appendAfter "CanonicalEndpointComponentConstruction")
  let CanonicalEndpointConstruction_of_components := mkIdentFrom p (p.getId.appendAfter "CanonicalEndpointConstruction_of_components")
  let CanonicalEndpointEquivSharedProjectorComponents := mkIdentFrom P (P.getId.appendAfter "CanonicalEndpointEquivSharedProjectorComponents")
  let CanonicalEndpointEquivSharedProjectorConstruction := mkIdentFrom P (P.getId.appendAfter "CanonicalEndpointEquivSharedProjectorConstruction")
  let CanonicalEndpointCoreComponents := mkIdentFrom P (P.getId.appendAfter "CanonicalEndpointCoreComponents")
  let CanonicalEndpointCoreComponentConstruction := mkIdentFrom P (P.getId.appendAfter "CanonicalEndpointCoreComponentConstruction")
  let IndexedMaterializerConstruction := mkIdentFrom P (P.getId.appendAfter "IndexedMaterializerConstruction")
  let LoweredCoreComponents := mkIdentFrom P (P.getId.appendAfter "LoweredCoreComponents")
  let LoweredCoreConstruction := mkIdentFrom P (P.getId.appendAfter "LoweredCoreConstruction")
  let CanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore := mkIdentFrom p (p.getId.appendAfter "CanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore")
  let CanonicalEndpointEquivSharedProjectorConstruction_of_coreComponents := mkIdentFrom p (p.getId.appendAfter "CanonicalEndpointEquivSharedProjectorConstruction_of_coreComponents")
  let EndpointEquivIndexedConstruction_of_equivSharedProjector := mkIdentFrom p (p.getId.appendAfter "EndpointEquivIndexedConstruction_of_equivSharedProjector")
  let EndpointEquivIndexedConstruction_core := mkIdentFrom p (p.getId.appendAfter "EndpointEquivIndexedConstruction_core")
  let ExactIndexedSpec_of_canonical := mkIdentFrom p (p.getId.appendAfter "ExactIndexedSpec_of_canonical")
  let EndpointExactIndexedConstruction_of_canonical := mkIdentFrom p (p.getId.appendAfter "EndpointExactIndexedConstruction_of_canonical")

  `(
    def $EndpointExactIndexedConstruction ($param : $paramTy) : Prop :=
      exists W : Structured3EndpointWrapper,
      exists initialized lowered : $idxTy -> Tape Bool,
        Structured3EndpointExactIndexedFamilySpec
          W
          $inTape
          initialized
          lowered
          $outTape

    def $EndpointEquivIndexedConstruction ($param : $paramTy) : Prop :=
      exists W : Structured3EndpointWrapper,
      exists initialized lowered : $idxTy -> Tape Bool,
        Structured3EndpointEquivIndexedFamilySpec
          W
          $inTape
          initialized
          lowered
          $outTape

    def $OutputBuffer { $param : $paramTy } (_i : $idxTy) : Tape Bool :=
      Tape.blank

    def $InitializedTape { $param : $paramTy } (i : $idxTy) : Tape Bool :=
      CommonGround.FiniteTransducers.structured3InputMaterializerTargetTape
        ($inTape i)
        ($OutputBuffer i)

    def $LoweredTape { $param : $paramTy } (i : $idxTy) : Tape Bool :=
      encodedGuardedStructured3Tapes
        ($inTape i)
        Tape.blank
        ($outTape i)

    def $ExactMaterializerSpec ($param : $paramTy) (materializer : MachineDescription) : Prop :=
      Structured3EndpointExactMaterializerSpec
        (fun i : $idxTy => $inTape i)
        (fun i => $InitializedTape i)
        materializer

    def $IndexedMaterializerSpec ($param : $paramTy) (materializer : MachineDescription) : Prop :=
      Structured3EndpointIndexedMaterializerSpec
        (fun i : $idxTy => $inTape i)
        (fun i => $InitializedTape i)
        materializer

    def $ExactLoweredCoreSpec ($param : $paramTy) (lowered : MachineDescription) : Prop :=
      Structured3EndpointExactLoweredCoreSpec
        (fun i : $idxTy => $InitializedTape i)
        (fun i => $LoweredTape i)
        lowered

    def $CanonicalEndpointSpec ($param : $paramTy) (W : Structured3EndpointWrapper) : Prop :=
      Structured3CanonicalExactIndexedEndpointSpec
        W
        (fun i : $idxTy => $inTape i)
        (fun i => $InitializedTape i)
        (fun i => $LoweredTape i)
        (fun i => $outTape i)

    def $CanonicalEndpointConstruction ($param : $paramTy) : Prop :=
      exists W : Structured3EndpointWrapper,
        $CanonicalEndpointSpec $param W

    def $CanonicalEndpointComponents ($param : $paramTy) : Type :=
      Structured3CanonicalExactEndpointComponents
        (fun i : $idxTy => $inTape i)
        (fun i => $InitializedTape i)
        (fun i => $LoweredTape i)
        (fun i => $outTape i)

    def $CanonicalEndpointComponentConstruction ($param : $paramTy) : Prop :=
      Structured3CanonicalExactEndpointComponentConstruction
        (fun i : $idxTy => $inTape i)
        (fun i => $InitializedTape i)
        (fun i => $LoweredTape i)
        (fun i => $outTape i)

    theorem $CanonicalEndpointConstruction_of_components
        { $param : $paramTy }
        (hcomponents : $CanonicalEndpointComponentConstruction $param) :
        $CanonicalEndpointConstruction $param := by
      simpa [$CanonicalEndpointConstruction:ident,
        $CanonicalEndpointSpec:ident,
        $CanonicalEndpointComponentConstruction:ident] using
        structured3CanonicalExactIndexedEndpointConstruction_of_components
          hcomponents

    def $CanonicalEndpointEquivSharedProjectorComponents ($param : $paramTy) : Type :=
      Structured3CanonicalEquivEndpointSharedProjectorComponents
        (fun i : $idxTy => $inTape i)
        (fun i => $InitializedTape i)
        (fun i => $LoweredTape i)
        (fun i => $outTape i)
        (fun i => $inTape i)
        (fun _i : $idxTy => Tape.blank)

    def $CanonicalEndpointEquivSharedProjectorConstruction ($param : $paramTy) : Prop :=
      Structured3CanonicalEquivEndpointSharedProjectorConstruction
        (fun i : $idxTy => $inTape i)
        (fun i => $InitializedTape i)
        (fun i => $LoweredTape i)
        (fun i => $outTape i)
        (fun i => $inTape i)
        (fun _i : $idxTy => Tape.blank)

    def $CanonicalEndpointCoreComponents ($param : $paramTy) : Type :=
      Structured3CanonicalExactEndpointCoreComponents
        (fun i : $idxTy => $inTape i)
        (fun i => $InitializedTape i)
        (fun i => $LoweredTape i)
        (fun i => $outTape i)
        (fun i => $inTape i)
        (fun _i : $idxTy => Tape.blank)

    def $CanonicalEndpointCoreComponentConstruction ($param : $paramTy) : Prop :=
      Structured3CanonicalExactEndpointCoreComponentConstruction
        (fun i : $idxTy => $inTape i)
        (fun i => $InitializedTape i)
        (fun i => $LoweredTape i)
        (fun i => $outTape i)
        (fun i => $inTape i)
        (fun _i : $idxTy => Tape.blank)

    def $IndexedMaterializerConstruction ($param : $paramTy) : Prop :=
      Structured3EndpointIndexedMaterializerConstruction
        (fun i : $idxTy => $inTape i)
        (fun i => $InitializedTape i)

    def $LoweredCoreComponents ($param : $paramTy) : Type :=
      Structured3CanonicalExactEndpointLoweredCoreComponents
        (fun i : $idxTy => $InitializedTape i)
        (fun i => $LoweredTape i)
        (fun i => $outTape i)
        (fun i => $inTape i)
        (fun _i : $idxTy => Tape.blank)

    def $LoweredCoreConstruction ($param : $paramTy) : Prop :=
      Structured3CanonicalExactEndpointLoweredCoreConstruction
        (fun i : $idxTy => $InitializedTape i)
        (fun i => $LoweredTape i)
        (fun i => $outTape i)
        (fun i => $inTape i)
        (fun _i : $idxTy => Tape.blank)

    theorem $CanonicalEndpointCoreComponentConstruction_of_materializer_loweredCore
        { $param : $paramTy }
        (hmaterializer : $IndexedMaterializerConstruction $param)
        (hcore : $LoweredCoreConstruction $param) :
        $CanonicalEndpointCoreComponentConstruction $param := by
      simpa [$IndexedMaterializerConstruction:ident,
        $LoweredCoreConstruction:ident,
        $CanonicalEndpointCoreComponentConstruction:ident] using
        structured3CanonicalExactEndpointCoreComponentConstruction_of_materializer_loweredCore
          hmaterializer hcore

    theorem $CanonicalEndpointEquivSharedProjectorConstruction_of_coreComponents
        { $param : $paramTy }
        (hcore : $CanonicalEndpointCoreComponentConstruction $param)
        (hprojector : Structured3EndpointTape2ProjectorConstruction) :
        $CanonicalEndpointEquivSharedProjectorConstruction $param := by
      simpa [$CanonicalEndpointCoreComponentConstruction:ident,
        $CanonicalEndpointEquivSharedProjectorConstruction:ident] using
        structured3CanonicalEquivEndpointSharedProjectorConstruction_of_coreComponents
          hcore hprojector

    theorem $EndpointEquivIndexedConstruction_of_equivSharedProjector
        { $param : $paramTy }
        (hcomponents : $CanonicalEndpointEquivSharedProjectorConstruction $param) :
        $EndpointEquivIndexedConstruction $param := by
      rcases hcomponents with ⟨C⟩
      exact
        ⟨C.wrapper,
          $InitializedTape,
          $LoweredTape,
          C.equivIndexedFamilySpec⟩

    theorem $ExactIndexedSpec_of_canonical
        { $param : $paramTy }
        { W : Structured3EndpointWrapper }
        (hspec : $CanonicalEndpointSpec $param W) :
        Structured3EndpointExactIndexedFamilySpec
          (ι := $idxTy)
          W
          (fun i => $inTape i)
          (fun i => $InitializedTape i)
          (fun i => $LoweredTape i)
          (fun i => $outTape i) :=
      structured3EndpointExactIndexedFamilySpec_of_canonical hspec

    theorem $EndpointExactIndexedConstruction_of_canonical
        { $param : $paramTy }
        (hcanonical : $CanonicalEndpointConstruction $param) :
        $EndpointExactIndexedConstruction $param := by
      rcases hcanonical with ⟨W, hspec⟩
      exact
        ⟨W,
          $InitializedTape,
          $LoweredTape,
          $ExactIndexedSpec_of_canonical hspec⟩
   )

end StructuredConstructionTargets
end Computability
end FoC
