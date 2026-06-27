import FoC.Computability.Compiler.Core.CommonGround.Controller
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.Assembly
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.BoolWordQuoter

set_option doc.verso true

/-!
# Common Boolean-word quoters

This module exposes the initializer-derived quoters that are shared with
controller input initialization and selected projection proofs.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace BoolWordQuoters

export DovetailInitialLayoutInitializer
  ( stageInputBits
    inputTapeBits
    AppendInputTapeReturnForwardSpec
    AppendInputTapeReturnSpec
    appendInputTapeReturnSpec_realizer
    checkedNonemptyBoolWordQuoteDirectSourceBits
    checkedNonemptyBoolWordQuoteDirectSourceBits_eq
    checkedNonemptyBoolWordQuoteDirectCopiedTrailerBits
    checkedNonemptyBoolWordQuoteDirectSourceBits_encodeNatAppend
    CheckedRawBoolWordAppendCodeWordReturnDescription
    checkedRawBoolWordAppendCodeWordReturnDescription_subroutineReady
    checkedRawBoolWordAppendCodeWordReturnDescription_run
    checkedRawBoolWordAppendCodeWordReturnDescription_haltsFromTape
    CheckedRawBoolWordAppendHeaderReturnDescription
    checkedRawBoolWordAppendHeaderReturnDescription_subroutineReady
    checkedRawBoolWordAppendHeaderReturnDescription_run
    checkedRawBoolWordAppendHeaderReturnDescription_haltsFromTape )

def RawBoolWordHeaderEmitterSpec
    (suffix : Word MachineCodeSymbol)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall w : Word Bool,
      emitter.HaltsWithOutput w
        (encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend w suffix))

def RawBoolWordHeaderEmitterConstruction
    (suffix : Word MachineCodeSymbol) : Prop :=
  exists emitter : MachineDescription,
    RawBoolWordHeaderEmitterSpec suffix emitter

theorem controllerInitialRawBoolWordHeaderEmitterConstruction :
    RawBoolWordHeaderEmitterConstruction
      ControllerLayouts.initialSuffix := by
  refine
    ⟨_root_.FoC.Computability.DovetailInitialLayoutInitializer.ControllerInitialRawBoolWordHeaderEmitterDescription,
      ?_⟩
  constructor
  · exact
      _root_.FoC.Computability.DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterDescription_subroutineReady
  · intro w
    simpa [RawBoolWordHeaderEmitterSpec,
      ControllerLayouts.initialSuffix,
      _root_.FoC.Computability.DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterOutput,
      _root_.FoC.Computability.DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterSuffix] using
      _root_.FoC.Computability.DovetailInitialLayoutInitializer.controllerInitialRawBoolWordHeaderEmitterDescription_haltsWithOutput
          w

end BoolWordQuoters
end CommonGround

end Computability
end FoC
