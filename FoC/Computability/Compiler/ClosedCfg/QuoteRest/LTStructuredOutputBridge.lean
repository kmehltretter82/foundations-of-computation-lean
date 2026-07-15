import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterOutput
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterStructuredQuote

set_option doc.verso true

/-!
# Structured live-tail emitter output bridge

This module exposes the structured emitter configurations used by the direct
joined QuoteRest endpoint.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

def structuredLiveTailEmitterAssemblyInputBits
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  assemblySourceRestFinishSourceBits p.w p.sourceRestBits p.stage

def structuredLiveTailEmitterAssemblyOutputPrefix
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  assemblySourceRestFinishTargetPrefixBits p.w p.sourceRestBits p.stage

def structuredLiveTailEmitterAssemblyInitialConfig
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) : Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailCountConfig
    0 [] (structuredLiveTailEmitterAssemblyInputBits p) 0 outputBits

def structuredLiveTailEmitterAssemblyRunSteps
    (p : AssemblySourceRestLiveTailEmitterParam) : Nat :=
  structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps
    (structuredLiveTailEmitterAssemblyInputBits p)

def structuredLiveTailEmitterAssemblyOutputBits
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) : Word Bool :=
  List.append outputBits
    (structuredLiveTailEmitterAssemblyOutputPrefix p)

def structuredLiveTailEmitterAssemblyFinalConfig
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) : Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
    499
    (structuredLiveTailEmitterAssemblyInputBits p).reverse
    []
    (structuredLiveTailEmitterAssemblyInputBits p).length
    (structuredLiveTailEmitterAssemblyOutputBits p outputBits)

def structuredLiveTailEmitterAssemblySourceTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
    (assemblySourceRestLiveTailEmitterLeftRev p)
    (assemblySourceRestLiveTailEmitterQuoteScan p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_assembly
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailEmitterDescription.runConfig
        (structuredLiveTailEmitterAssemblyRunSteps p)
        (structuredLiveTailEmitterAssemblyInitialConfig p outputBits) =
      structuredLiveTailEmitterAssemblyFinalConfig p outputBits := by
  cases p with
  | mk w sourceRestBits stage =>
      simpa [
        structuredLiveTailEmitterAssemblyRunSteps,
        structuredLiveTailEmitterAssemblyInitialConfig,
        structuredLiveTailEmitterAssemblyFinalConfig,
        structuredLiveTailEmitterAssemblyInputBits,
        structuredLiveTailEmitterAssemblyOutputBits,
        structuredLiveTailEmitterAssemblyOutputPrefix]
        using
          structuredMixedOptionCellQuoteLiveTailEmitterDescription_run_assemblyFullSource
            w sourceRestBits outputBits stage

end SelectedProjectionInputQuoterFiniteLeaf
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
