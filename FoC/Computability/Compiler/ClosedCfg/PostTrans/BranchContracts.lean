import FoC.Computability.Compiler.ClosedCfg.PostTrans.Adapters
import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInner
import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerContracts

set_option doc.verso true

/-!
# Padded merge post-transition branch contracts

This wrapper preserves the public branch-contract import while the
implementation is split by responsibility:

- {module}`FoC.Computability.Compiler.ClosedCfg.PostTrans.Specs`
  contains the construction-family contracts for the nested-layout parser and
  accepting/rejecting inner emitters.
- {module}`FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInner`
  contains the branch-parametric parsed-inner finite-machine leaf.
- {module}`FoC.Computability.Compiler.ClosedCfg.PostTrans.Adapters`
  contains the branch-composition adapters that connect those finite leaves to
  the post-transition padded construction.
- {module}`FoC.Computability.Compiler.ClosedCfg.PostTrans.NestedLayoutShape`
  contains the source-fields and nested-layout parsed tape facts.
- {module}`FoC.Computability.Compiler.ClosedCfg.PostTrans.BranchHandoffShape`
  contains the accepting/rejecting decoded handoff target facts.
- {module}`FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerWindows`
  names the marked source windows and unmarked branch target windows used by
  the parsed-inner field replacement leaf.
-/
