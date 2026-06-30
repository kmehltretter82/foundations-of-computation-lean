import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Basic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.AppendWord
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.AlternatingOptionAppend
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.Compaction
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.DeleteWindow
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.EraseAppend
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.GapPayloadScan
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.LeftShiftCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.MapAppend
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OptionAppend
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OptionSpecializations
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.PaddedIdentity
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RewriteWrites
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.SentinelGapCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StatefulOptionAppend
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StatefulOptionAppendGenerated
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TwoStateOptionAppend

set_option doc.verso true

/-!
# Certified finite transducer helpers

This compatibility module re-exports the finite-transducer core, generated
append-word, erase-append, bit-map append, optional-output append, generated
arbitrary-state and two-state optional-output, and alternating optional-output
compiler slices, their specialization links, the physical compaction shape
helpers, the padded-input identity contract, the generic stateful optional-output
append invariant, and the reusable right-edge rewind adapter.
-/
