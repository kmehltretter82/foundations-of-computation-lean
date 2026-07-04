import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.Layout
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.Primitives
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorBasic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorSeek
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.CursorHead
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.Rows

set_option doc.verso true

/-!
# Structured multi-tape lowering

Compatibility wrapper for the structured multi-tape lowering modules.

The implementation is split into physical layout facts, primitive lowering
contracts, cursor routines, concrete row machines, and head-cell routines.  This
module preserves the original import path for downstream files.
-/
