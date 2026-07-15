import FoC.Computability.Compiler.Structured.Lowering.Layout
import FoC.Computability.Compiler.Structured.Lowering.Primitives
import FoC.Computability.Compiler.Structured.Lowering.Composition
import FoC.Computability.Compiler.Structured.Lowering.CursorBasic
import FoC.Computability.Compiler.Structured.Lowering.CursorBoundaryGap
import FoC.Computability.Compiler.Structured.Lowering.CursorBoundaryGapCreator
import FoC.Computability.Compiler.Structured.Lowering.StructuredRefresh
import FoC.Computability.Compiler.Structured.Lowering.SelectedSeparatorRefresh
import FoC.Computability.Compiler.Structured.Lowering.SelectedSeparatorRefreshRuns
import FoC.Computability.Compiler.Structured.Lowering.SingletonRefresh
import FoC.Computability.Compiler.Structured.Lowering.ConcreteRefresh
import FoC.Computability.Compiler.Structured.Lowering.CursorComposition
import FoC.Computability.Compiler.Structured.Lowering.CursorSeek
import FoC.Computability.Compiler.Structured.Lowering.CursorHead
import FoC.Computability.Compiler.Structured.Lowering.CursorPipelines
import FoC.Computability.Compiler.Structured.Lowering.PrimitivePipelines
import FoC.Computability.Compiler.Structured.Lowering.ActionSlack
import FoC.Computability.Compiler.Structured.Lowering.Rows
import FoC.Computability.Compiler.Structured.Lowering.RefreshedRows
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic
import FoC.Computability.Compiler.Structured.Lowering.TailedThreeTapeDebug
import FoC.Computability.Compiler.Structured.Lowering.Runs
import FoC.Computability.Compiler.Structured.Lowering.RunsStructuredSingleton3
import FoC.Computability.Compiler.Structured.Lowering.Dispatcher
import FoC.Computability.Compiler.Structured.Lowering.DispatcherAssembly
import FoC.Computability.Compiler.Structured.Lowering.Projection
import FoC.Computability.Compiler.Structured.HeadRoutes
import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.EndpointFrontier
import FoC.Computability.Compiler.Structured.Lowering.PairEncodedOptionCellCompactor
import FoC.Computability.Compiler.Structured.Lowering.TypedStateTable

set_option doc.verso true

/-!
# Structured multi-tape lowering

Barrel module for the structured multi-tape lowering modules.

The implementation is split into physical layout facts, primitive lowering
contracts, primitive composition, cursor routines, cursor composition, concrete
cursor pipelines, primitive pipelines, chainable action slack, row machines,
refreshed row machines, run-level trace composition, dispatcher scaffolding,
head-cell routines, and static dispatcher reader-assembly infrastructure. This
module provides a short import path for downstream files.
-/
