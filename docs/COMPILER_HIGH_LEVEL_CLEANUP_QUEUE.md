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

## High-value next audits

### Finite-scaffold route bundles

Files:

- `Core/FiniteScaffolds/ControllerInvocationContracts.lean` — 692 lines;
- `Core/FiniteScaffolds/ControllerSearchDriverContracts.lean` — 836 lines.

Evidence:

- no declaration in `ControllerInvocationContracts.lean` is referenced outside
  that file or `ControllerSearchDriverContracts.lean`;
- no declaration in `ControllerSearchDriverContracts.lean` is referenced
  outside that file;
- the duplicate baseline contains five invocation route/scaffold pairs and
  seven search-driver route/scaffold pairs;
- the final public `_route` aliases duplicate already available `_scaffold` or
  `_finite_leaf` theorem types.

Constraint: the search-driver file contains the current output-indexed family
surface for repaired sorry #12, while the invocation file is intended as an
acceptance surface for #6/#7. Do not delete those honest currencies blindly.
First reduce the search-driver module to the actually checked family consumer,
then determine whether the legacy scalar and finite-route bundles can be
retired until their direct leaves are axiom-clean. Plausible saving: 800–1,300
lines.

### HeadRoutes projection aliases

`Structured/HeadRoutes/Pipeline.lean` still has eleven exact duplicate groups:
top-level `selectedHeadRoute_*` theorems repeat projections from
`StructuredSelectedHeadDecoderRouteConstruction`. Only `Endpoints.lean` and
`RepresentativeProjectors.lean` consume a subset. Migrate those consumers to
the bundle fields and remove unused projection aliases. This should be a small,
low-risk reduction; retain the bundle and honest equivalence contracts.

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

## Review rule

For each candidate, record external declaration references—not merely module
imports—then run direct consumers and the growth checker. If a module is an
active acceptance surface for an open leaf, prefer reducing it to one honest
consumer over deleting the evidence entirely. Record every retired concept in
`COMPILER_DELETION_LEDGER.md`.
