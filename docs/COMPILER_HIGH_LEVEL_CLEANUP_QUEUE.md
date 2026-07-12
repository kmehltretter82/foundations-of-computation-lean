# Compiler high-level cleanup queue

This queue is generated from the post-deletion declaration inventory, import
graph, and exact theorem-type baseline. It records places where deleting a
lower route exposed a higher redundant layer, or where one missing canonical
theorem could replace repeated proof blocks.

The current checked declaration export contains 23,571 Compiler declarations
and 144 exact duplicate theorem-type groups. A duplicate type is an audit
signal, not sufficient evidence for deletion.

## Ready or completed

### Facade-only materializer route bundles — completed

`StructuredInputMaterializerContracts.lean` and
`FST/CountWindow/Contracts.lean` contained 1,668 lines of self-referential
route records, construction bundles, and aliases. No declaration had a source,
book, or documentation consumer outside its own file. Removed in `5f557820`;
the live materializer, CountWindow implementation, and raw-source bridge pass.

### Superseded Dispatcher reader layout — completed

The old contiguous tape-0/1/2 reader offsets, scratch banks, jumps, and run
wrappers in `Structured/Lowering/Dispatcher.lean` had no consumer; the live
assembly uses the compact state layout. Removed 292 lines/37 declarations in
`123eb193`.

### Finite-scaffold route bundles — completed

`ControllerInvocationContracts.lean` is now a 16-line #6/#7 acceptance
boundary, and `ControllerSearchDriverContracts.lean` retains only the honest
Boolean-indexed #12 family consumer. The unused scalar routes, aggregate
finite-route bundles, and sorry-dependent aliases were removed in
`59985a4d`: 16 insertions, 1,371 deletions. Both direct modules and the
`FiniteScaffolds.lean` barrel pass.

## High-value next audits

### Quoter raw-cell execution stack

`Projection/Quoter/RawCells.lean` is 1,584 lines. Its first roughly 900 lines
reprove the same `AssemblyPrefixDescription` state-100 through state-210 runs
that are already exposed as `*_core` theorems by
`ClosedCfg/QuoteAssembly/MarkingLoop.lean` and `Finish.lean`. There are 29
matching core phase theorems, including the complete
`run_stageInput_to_sourceRest_boundary_cells_withBase_core` route. The only
external consumer of the duplicated stack needs the final exact
source-to-prefix-boundary result, not the intermediate unsuffixed lemmas.

The import graph confirms that `RawCells.lean` may import
`QuoteAssembly/Finish.lean` without a cycle. Replace its public final theorem
with a thin specialization of the with-base core, then delete the private/local
replay rather than adding another execution abstraction. Expected saving:
approximately 700–900 lines, subject to a focused `RawCellsOutput.lean` and
`Quoter/Main.lean` check.

### HeadRoutes projection aliases — completed

The #17 declaration-reference audit found no external consumer of the lossy
selected-head route bundle or its eleven projection aliases. The checked
source-collision guardrail refuted the route's construction contract, so the
closure deletion removed `Pipeline.lean`, `Projectors.lean`, and
`RepresentativeProjectors.lean` and retained only the minimal guardrail
shapes in `ExactCleanup.lean` and `RepresentativeCleanup.lean`. The live
marker-preserving replacement is `Structured/HeadRoutes/Tape2Projector/`.

### Structured-prefix eraser endpoint lattice

The duplicate inventory reports six groups between
`StructuredPrefixEraserHandoff/Base.lean` and
`StructuredPrefixEraserShape.lean`, plus repeated normalized-output equalities
across `StructuredPrefixEraserBoundaryPhases.lean`, `Output.lean`, and
`Endpoint.lean`. Audit whether one canonical endpoint-shape theorem can replace
the branch/output restatements. The implementation is live, so migrate direct
consumers before deleting aliases.

## Missing theorem/API candidates

### Neutral certified transition block — deferred

`DispatcherAssembly` has about 875 lines of repeated source-disjointness
families, but its compact numeric state IDs and prefix-history arities are
proof-relevant. A bare `Fin 3` index would add dependent casts. The missing
abstraction would need to package a transition block's source interval,
well-formedness, determinism, append/flatMap composition, inclusion, and run
transfer.

Do not add it yet. It must first have two current consumers, plausibly
DispatcherAssembly and one other physical block family, and the introducing
change must delete existing proof stacks immediately. Preserve the current
quiet-cache `DispatcherAssembly/SelectedRuns.lean` check time of 3.28 seconds
as the performance ceiling.

### Construction-bundle projection policy

Many exact duplicate groups are a structure field plus a top-level theorem of
the same type. No new generic theorem is needed: consumers should use the
structure projection directly. Keep a top-level alias only when it is a real
stable public boundary with an external consumer.

### Combined finite-transition readiness

The existing `machineDescription_subroutineReady_of_transition_checks` theorem
already fills this gap. The first migration removed 300 net lines across nine
modules in `8d84d908`. Search for further private well-formedness plus
halt-transition-free pairs before inventing another checker. Chunked transition
tables need a separate helper only after two current chunked machines can
delete their local proofs in the same change.

### One-tape execution composition and list-loop induction

The Compiler still contains 1,224 textual uses of `runConfig_add`. Many are
legitimate phase boundaries, but the repeated fixed-cost list scans and
multi-phase chains are candidates for stronger reusable lemmas rather than
another machine-specific proof.

First promote the already triplicated theorem that equal transition tables
give equal `MachineDescription.runConfig` executions. Then pilot a one-tape
counterpart of the structured `runConfig_listLoop` theorem and a small
phase-chain tactic on two distinct machine families. Promotion requires an
immediate net LOC reduction and no focused elaboration-time regression; a
syntax-only tactic that merely hides long proof terms without deleting the
underlying local invariants does not pass the gate.

## Review rule

For each candidate, record external declaration references—not merely module
imports—then run direct consumers and the growth checker. If a module is an
active acceptance surface for an open leaf, prefer reducing it to one honest
consumer over deleting the evidence entirely. Record every retired concept in
`COMPILER_DELETION_LEDGER.md`.
