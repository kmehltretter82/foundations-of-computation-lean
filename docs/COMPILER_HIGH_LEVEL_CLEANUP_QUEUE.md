# Compiler high-level cleanup queue

This queue is generated from the post-deletion declaration inventory, import
graph, and exact theorem-type baseline. It records places where deleting a
lower route exposed a higher redundant layer, or where one missing canonical
theorem could replace repeated proof blocks.

The current checked declaration export contains 24,634 Compiler declarations
and 93 exact duplicate theorem-type groups. A duplicate type is an audit
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

### Completed Chapter 5.2 campaign loans — retired

The completed #6, #7, #19/#20, #24, and #26 campaigns were rechecked and
retired on 2026-07-15. Their final cumulative nets from the original pinned
bases are respectively +1,840, +7,563, +1,585, +2,008, and +1,099 Compiler
lines: +14,095 total. Fresh focused checks passed for `StageAttemptFramed`,
`ControllerInvocation`, `NestedLayoutParser`, `QuoteRest.Output`, `QuoteRest`,
`RawCells`, and `RawCellsOutput`. The retained frontiers and their real
consumers depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The final Chapter 5.2 retirement rechecked #12, #13, #15, #17, and #22 after
all Chapter 5.2 frontiers had closed. Their cumulative nets from the original
pinned bases were respectively +12,183, +2,866, -5,063, +1,264, and +9,962
Compiler lines. Every required frontier, guardrail, and live consumer depends
only on `propext`, `Classical.choice`, and `Quot.sound`. Removing these five
completed manifests releases another 28,000 lines of aggregate outstanding
allowance; it neither removes source lines from the independent global
measurement nor resets any pinned base.

The aggregate outstanding-loan cap is 50,000 lines, the independent global
raw-growth cap is 70,000 lines, and the ordinary per-campaign ceiling remains
10,000. Any reopened work on a retired frontier requires a new campaign and a
new pinned base.

### Chapter 5.3 #3 product runner — completed

The closing change replaces the positive-state product-runner hole with the
fixed `ProductPairMaterializer` machine, exact empty/nonempty schedules, and
the existing cyclic-probe product composition. The cumulative campaign change
from its pinned base is +15,325/-765, net +14,560 Compiler lines. The frontier,
its arbitrary-state wrapper, and the immediate `GenCall/Product` consumer
compile and depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The causal audit retains the concise context-length counterexample for the
impossible exact-empty physical contract and finds no zero-consumer production
module in the completed Product route. The promoted `PairMaterializer/Machine`
and `PairMaterializer/Runs` modules replace the final two #3 scratch artifacts,
which are removed in the same change. The reviewed campaign manifest remains
active until a separate permanent-growth review; its pinned base is not reset.

### Chapter 5.3 #4 decoded-description interpreter — completed

The #4 source frontier is production-closed through
`Core/FiniteRecognizer/Interpreter/{Parser,Initializer,Runtime,Outer}` and the
`DecodedDescriptionInterpreter.lean` facade. The facade, route contracts,
normalized-runner consumer, broad finite-recognizer barrel, and Compiler facade
compile. The public interpreter leaves and normalized-runner consumers depend
only on `propext`, `Classical.choice`, and `Quot.sound`. The declaration export
introduces no exact-duplicate theorem-type regression, and the campaign records
+54,483 net Compiler lines against its reviewed +60,000 allowance. The exact
production Compiler direct-sorry census is now zero after the subsequent #1
and #2 tuple-search closures. The campaign manifest stays pinned until the
post-closure deletion and permanent-growth review.

### Chapter 5.3 #1 unbounded tuple search — completed

The shared tuple scheduler is production-organized under
`Core/FiniteRecognizer/TupleSearch/Scheduler`, with stable namespaces for its
layout, candidate materializer, finite cycle, reachability proof, initializers,
and rollover phases. `Scheduler/PublicCore.lean` exposes the common relational
cycle contracts, while `Scheduler/Unbounded.lean` provides the acyclic public
construction consumed by `TupleSearch/Program.lean`.

The unbounded module, Program facade, route contracts, and real
`StageSearchController/GenCall/Pairs` consumer compile. The public unbounded
leaf and the code-prefix consumer depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Current cumulative growth is +20,113 net
Compiler lines against the reviewed +22,000 allowance. The bounded #2 leaf is
now closed by the thin wrapper recorded below. The #1 campaign remains pinned
for the post-closure deletion and permanent-growth review.

### Chapter 5.3 #2 bounded tuple search — completed

`Scheduler/Bounded.lean` reuses the shared scheduler and bounded initializer
owned by #1 and exposes the acyclic finite-state construction consumed by
`TupleSearch/Program.lean`. The bounded module, Program facade, route
contracts, and real `StageSearchController/GenCall/Pairs` consumer compile.
The public bounded leaf and code-prefix consumer depend only on `propext`,
`Classical.choice`, and `Quot.sound`, and the production Compiler direct-sorry
census is zero.

The narrow #2 campaign paths measure +52/-19, net +33 Compiler lines, against
the +2,000 allowance. Its manifest remains pinned for the post-closure deletion
and permanent-growth review.

### #18 exact terminal facade and duplicate construction — completed

The public migration in `206a31b2` left the equivalence-valued padded-emitter
scaffold as the only externally used acceptance surface. Commit `ed1bc3a6`
then removed the uninhabited exact post-scan theorem, its scratch/FST adapter
lattice, seven dead wrapper modules, and unused diagnostics for a net reduction
of 820 Compiler lines. Commit `b00c26a6` removed the last unreferenced
finite-realization alias, and `d59ece33` removed a duplicate premise-free
construction theorem so the stable scaffold is the sole public theorem with
that construction type. Commit `66f821b8` then reused canonical proof facts in
place of five newly exposed duplicate declarations. The fresh declaration
export reports no exact-duplicate regression, and the full Compiler build and
the #12/#14 consumers compile through the surviving tape-equivalence route.
The post-closure kernel dependency audit then removed another 2,715 net lines:
standalone fixed-step/loop machines, executable semantic-decoder prototypes,
the retired exact-closeout contract lattice, the pre-guard serializer route,
and two zero-live modules. The audit included every retained #18 axiom-clean
acceptance declaration as a root; the public padded-emitter scaffold and its
two real consumer modules compile through the integrated dispatcher and
guarded-serializer route.

The final permanent campaign review on 2026-07-15 records +28,966/-4,119,
net +24,847, from the original #18 base. The frozen +14,507 historical
checkpoint was not raised. Instead, after the proof frontier closed, repeated
causal deletion passes, an axiom audit, and fresh builds of both real consumers,
the completed historical manifest was retired. Global raw Compiler size is
365,811 lines, or +18,745 against the independently reviewed +50,000 ceiling;
the source baseline remains pinned at 347,066. Any future #18 construction
work requires a new current campaign and cannot reuse the retired debt record.

### Quoter raw-cell execution stack — completed

The declaration-reference audit found no external reference to any of the 34
local state-100 through state-210 replay theorems in
`Projection/Quoter/RawCells.lean`. The sole externally consumed final theorem
now specializes the canonical with-base execution from
`QuoteAssembly/Finish.lean`. This removes 866 net Compiler lines; the direct
module, `RawCellsOutput.lean`, `Quoter/Main.lean`, and the full Compiler build
pass.

### Post-#18 source shapes and Dovetail return predecessors — completed

The post-migration #18 audit removed 921 net lines of unused source-shape,
exact/FST, and right-shift adapters while preserving direct terminal tapes,
the public equivalence scaffold, and the #14/#12 consumers. A separate
Dovetail audit kept the live `ReturnAppend`/`ReturnAppendDirect` stack but
removed 251 lines of superseded start machines and unchecked wrappers. The
deletion ledger records the exact live replacements and recovery conditions.

## High-value next audits

### HeadRoutes projection aliases — completed

The #17 declaration-reference audit found no external consumer of the lossy
selected-head route bundle or its eleven projection aliases. The checked
source-collision guardrail refuted the route's construction contract, so the
closure deletion removed `Pipeline.lean`, `Projectors.lean`, and
`RepresentativeProjectors.lean` and retained only the minimal guardrail
shapes in `ExactCleanup.lean` and `RepresentativeCleanup.lean`. The live
marker-preserving replacement is `Structured/HeadRoutes/Tape2Projector/`.

### False raw-head ingress and unused normalizer — completed

The #16 declaration-reference audit found no external consumer of the
raw-head source/target families, ingress adapters, endpoint wrappers, or the
checked three-tape normalizer. Their only declaration references formed a
closed island across `HeadRoutes/Base.lean`, `RawHeadNormalizer.lean`, and
`Endpoints.lean`; two higher modules imported `Endpoints.lean` only to reach
the independent tape-2 projector.

The promoted outer-blank collision proves the ingress target family
impossible. The closure deletion retained that self-contained guardrail,
replaced the transitive imports with the actual projector boundary, and
removed 1,305 lines of obsolete route implementation and contracts. No
replacement contract was introduced because there is no current consumer to
justify one; a future consumer must first supply a collision-safe boundary.

### Structured-prefix eraser endpoint lattice — generic output tranche complete

The first audit removed the 328-line self-contained generic branch-output
lattice from `StructuredPrefixEraserOutput.lean`; every deleted declaration was
referenced only inside that block, while canonical output specs and all current
consumers remain. The duplicate inventory still reports six groups between
`StructuredPrefixEraserHandoff/Base.lean` and
`StructuredPrefixEraserShape.lean`, plus repeated normalized-output equalities
across `StructuredPrefixEraserBoundaryPhases.lean` and `Endpoint.lean`. Audit
whether one canonical endpoint-shape theorem can replace those remaining
restatements. The implementation is live, so migrate direct consumers before
deleting aliases.

### Final Chapter 5.2 unreachable route cleanup — completed

The post-closure import and declaration-reference audit removed 9,646 net raw
Compiler lines (`+36/-9,682`). The direct joined QuoteRest endpoint uses the
structured emitter but not the old structured joiner, output-projector, restore,
or generic endpoint-component lattice; pruning that isolated branch accounts
for 5,484 net lines. It was also the sole production consumer of the 1,999-line
generic raw-tail insertion machine; deleting that machine and its umbrella
import accounts for another 2,000 lines. The lowered pair compactor and
projectable-focus machine were imported only by an unreachable optional barrel,
and their generic split-target contract lattice was self-only. The retained
166-line base exposes exactly the pair-encoding and guarded-ingress shapes used
by the live #15 marker compactor and collision guardrails; this accounts for
another 1,521 net lines. The optional barrel now exposes only those live shapes,
stale allowlist entries for deleted modules are gone, and the intentionally
optional tailed three-tape debugger is classified explicitly as debug support.

A final declaration-only pass removed another 641 net lines. The #17
`HeadRoutes/Base.lean` module now retains only the two source shapes used by
the collision guardrails and cleanup adapters; the marker-preserving tape-2
projector remains the live construction. The #12 search contracts also lost
one zero-use runner-family wrapper and one zero-use witness equivalence. Their
attempt-facing family and explicit witness structure remain the live APIs.

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
