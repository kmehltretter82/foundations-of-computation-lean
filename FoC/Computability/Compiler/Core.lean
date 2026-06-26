import FoC.Computability.Compiler.Core.Language
import FoC.Computability.Compiler.Core.BoundedTrace
import FoC.Computability.Compiler.Core.DovetailCode
import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.Compiler.Core.TapeCodePrimitives
import FoC.Computability.Compiler.Core.TapeCodePrimitiveSequencing
import FoC.Computability.Compiler.Core.EncodingLemmas
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.ControllerCloseout
import FoC.Computability.Compiler.Core.EncodedRewriters
import FoC.Computability.Compiler.Core.CommonGround
import FoC.Computability.Compiler.Core.ControllerStageInputProjection
import FoC.Computability.Compiler.Core.FiniteScaffolds
import FoC.Computability.Compiler.Core.SearchDrivers
import FoC.Computability.Compiler.Core.Closeout

set_option doc.verso true

/-!
# Compiler core

This module re-exports the split compiler-core development.  The declarations
that used to live here now sit in focused submodules for language-level
compiler boundaries, tape-code primitives, encoded rewriters, controller
scaffolds, search-driver bridges, and final closeouts.
-/
