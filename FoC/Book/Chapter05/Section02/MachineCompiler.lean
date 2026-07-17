import FoC.Computability.Compiler.Core.BoundedTrace
import FoC.Computability.Compiler.Core.Closeout
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.SearchDrivers

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2: Machine Compiler

This page records the compiler architecture used by the Section 5.2 results.
The executable definitions, construction contracts, and proofs begin in
{module}`FoC.Computability.Compiler.Core.ConstructionTargets`; the links below
point directly to the canonical compiler API.

## Code-output boundary

Compilation distinguishes exact physical tape output from normalized word
output. The exact generic target is
{name}`Computability.MachineDescriptionTapeCodeExactCompilerConstruction`, and
{name}`Computability.not_machineDescriptionTapeCodeExactCompilerConstruction`
shows that it is impossible: an erasing primitive cannot shrink every
nonempty represented tape window to the exact empty representative.

The viable generic interface is
{name}`Computability.MachineDescriptionTapeCodeOutputCompilerConstruction`,
whose realizers are compared through normalized output. Concrete identity,
erasure, fixed-symbol append, singleton-Boolean output, unary comparison, and
one-step tape actions are collected by
{name}`Computability.machineDescriptionPrimitiveCompilerCore`. Their
halt-transition-free subroutine interfaces are collected separately by
{name}`Computability.machineDescriptionPrimitiveSubroutineCore`.

## Fixed-description simulation

For one transition of a fixed description,
{name}`Computability.FixedDescriptionStepCode` is the canonical code
primitive and {name}`Computability.fixedDescriptionStepCode_realizes` is its
semantic correctness theorem. The equivalence between configuration-oriented
and normalized-output construction contracts is
{name}`Computability.fixedDescriptionStepCodeConfigurationRealizerConstruction_iff_outputRealizerConstruction`.

Iteration is packaged by
{name}`Computability.FixedDescriptionBoundedSimulatorCode`. Its two canonical
bridges into the table-level simulator contract are
{name}`Computability.fixedDescriptionBoundedSimulatorTableCompiler_of_codeCompiler`
and
{name}`Computability.fixedDescriptionBoundedSimulatorTableCompiler_of_codeOutputRealizer`.
The first preserves exact code output; the second uses the normalized-output
currency required by the general compiler route.

## Paired-recognizer controller

The finite paired-recognizer route starts from
{name}`Computability.PairedRecognizerDovetailLayoutCode`, whose correctness is
{name}`Computability.pairedRecognizerDovetailLayoutCode_realizes`. A total
single-stage attempt is represented by
{name}`Computability.PairedRecognizerDovetailTotalStageAttemptCode`; its
controller-result contract is
{name}`Computability.pairedRecognizerDovetailTotalStageAttemptCode_controllerResultRealizes`.

The controller distinguishes a no-hit stage from an accepting or rejecting
singleton result. The continue and emit branches are characterized together
by
{name}`Computability.pairedRecognizerDovetailControllerContinueEmitCode_branch`,
and the bounded runner is connected to the semantic dovetail output by
{name}`Computability.pairedRecognizerDovetailLayout_initial_output`.

## API entry points

The reusable construction fields are grouped in
{name}`Computability.MachineDescriptionCompilerCloseout`. When a caller has a
generic normalized-output compiler, the canonical assembly function is
{name}`Computability.machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler`.
Clients needing only one compiler layer should use its foundational theorem
above rather than introducing a book-local forwarding declaration.
-/

end Section02
end Chapter05
end Book
end FoC
