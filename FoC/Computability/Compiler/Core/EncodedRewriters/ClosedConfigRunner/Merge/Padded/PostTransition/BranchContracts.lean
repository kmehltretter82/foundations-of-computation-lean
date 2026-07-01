import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.Adapters
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.ParsedInner

set_option doc.verso true

/-!
# Padded merge post-transition branch contracts

This wrapper preserves the public branch-contract import while the
implementation is split by responsibility:

- {module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.Specs`
  contains the construction-family contracts for the nested-layout parser and
  accepting/rejecting inner emitters.
- {module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.ParsedInner`
  contains the branch-parametric parsed-inner finite-machine leaf.
- {module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.Adapters`
  contains the branch-composition adapters that connect those finite leaves to
  the post-transition padded construction.
- {module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.NestedLayoutShape`
  contains the source-fields and nested-layout parsed tape facts.
- {module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.BranchHandoffShape`
  contains the accepting/rejecting decoded handoff target facts.
- {module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Merge.Padded.PostTransition.ParsedInnerWindows`
  names the marked source windows and unmarked branch target windows used by
  the parsed-inner field replacement leaf.
-/
