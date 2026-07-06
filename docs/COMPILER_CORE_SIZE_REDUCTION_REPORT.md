# Compiler Core Size Reduction Report

This report tracks the source-size reduction work for
`FoC/Computability/Compiler/Core`.

## Baseline

Before the first pilot edit, the local tree matched
`../COMPILER_CORE_SIZE_REDUCTION_PLAN.md`:

- Lean files: 292
- Source bytes: 9,090,812
- Source lines: 223,745
- Declaration-head scan: 11,104 declarations
- Declaration-site name bytes: about 561,698
- Declared-name occurrence bytes: about 3,315,842
- Occurrences of names of length at least 80: about 268 KB

## After Structured Prefix Eraser Pilot

After removing thin case-specific wrappers from
`FoC/Computability/Compiler/Core/EncRewriters/ClosedCfgRunner/Projection/Padded/TailCleanup/StructuredPrefixEraserHandoff.lean`:

- Lean files: 292
- Source bytes: 9,051,582
- Source lines: 223,016
- Declaration-head scan: 10,932 declarations
- Declaration-site name bytes: 553,906
- Tokenized declared-name occurrence bytes: 3,283,153
- Declarations with names of length at least 80: 1,145
- Tokenized occurrences of those long declaration names: 2,802
- Tokenized occurrence bytes for those long declaration names: 258,351

The pilot file changed from 1,654 lines to 925 lines.

## After Threaded Bridge Pilot

After also collapsing local construction-chain wrappers in
`FoC/Computability/Compiler/Core/EncRewriters/ClosedCfgRunner/Projection/Padded/TailCleanup/ScratchExtCountWindowBridgeThreaded.lean`:

- Lean files: 292
- Source bytes: 9,039,660
- Source lines: 222,807
- Declaration-head scan: 10,913 declarations
- Declaration-site name bytes: 551,622
- Tokenized declared-name occurrence bytes: 3,273,291
- Declarations with names of length at least 80: 1,126
- Tokenized occurrences of those long declaration names: 2,733
- Tokenized occurrence bytes for those long declaration names: 250,946

The threaded bridge file changed from 919 lines to 710 lines.

## After Selected Footprint Compaction Pilot

After also deleting local selected-footprint case wrappers from
`FoC/Computability/Compiler/Core/EncRewriters/ClosedCfgRunner/Projection/Padded/TailCleanup/SelectedFootprintCompaction.lean`:

- Lean files: 292
- Source bytes: 9,003,574
- Source lines: 222,034
- Declaration-head scan: 10,843 declarations
- Declaration-site name bytes: 545,185
- Tokenized declared-name occurrence bytes: 3,253,120
- Declarations with names of length at least 80: 1,079
- Tokenized occurrences of those long declaration names: 2,644
- Tokenized occurrence bytes for those long declaration names: 242,047

The selected-footprint file changed from 1,800 lines to 1,027 lines.

## Largest Files

| File | Bytes | Lines |
| --- | ---: | ---: |
| `CommonGround/FiniteTransducers/StructuredTapeLowering/SingletonRefresh.lean` | 122,213 | 2,933 |
| `CommonGround/FiniteTransducers/StructuredTapeLowering/CursorPipelines.lean` | 121,248 | 3,086 |
| `EncRewriters/ClosedCfgRunner/Projection/Padded/TailCleanup/ScratchExtCountWindowBridge.lean` | 121,237 | 2,649 |
| `CommonGround/FiniteTransducers/StructuredTapeLowering/Dispatcher.lean` | 120,940 | 3,088 |
| `CommonGround/FiniteTransducers/StructuredTapeLowering/SelectedSeparatorRefresh.lean` | 118,717 | 2,821 |
| `CommonGround/FiniteTransducers/StructuredTapeLowering/CursorBasic.lean` | 117,238 | 2,878 |
| `EncRewriters/ClosedCfgRunner/Projection/Quoter/SourceRestFinishCore/LTEmitterStructured.lean` | 115,453 | 2,361 |
| `CommonGround/FiniteTransducers/StructuredTapeLowering/CursorBoundaryGap.lean` | 113,067 | 2,678 |
| `CommonGround/FiniteTransducers/StructuredTapeLowering/DispatcherAssembly/StaticMachine.lean` | 112,167 | 2,618 |
| `CommonGround/FiniteTransducers/StructuredTapeLowering/CursorBoundaryGapCreator.lean` | 109,470 | 2,557 |

## Case-Family Suffix Counts

| Suffix | Remaining Declarations |
| --- | ---: |
| `_nil_nil` | 2 |
| `_nil_none` | 1 |
| `_nil_some` | 0 |
| `_cons_nil` | 0 |
| `_cons_none` | 3 |
| `_cons_some` | 0 |
| `_nil_cons` | 0 |
| `_cons_cons` | 24 |

## Repeated Prefix Clusters

The strongest remaining repeated prefixes by declaration-site weight are:

| Decls | Prefix Length | Weighted Bytes | Files | Prefix |
| ---: | ---: | ---: | ---: | --- |
| 39 | 62 | 2,418 | 2 | `selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_` |
| 46 | 43 | 1,978 | 3 | `inputTapeRightCellsDirectCopierDescription_` |
| 42 | 46 | 1,932 | 2 | `controllerInitialRawBoolWordHeaderEmitter_run_` |
| 30 | 62 | 1,860 | 2 | `selectedSegmentLogicalTapeDecoderDensifierFootprintTargetTape_` |
| 44 | 42 | 1,848 | 2 | `controllerInitialRawBoolWordHeaderEmitter_` |
| 46 | 32 | 1,472 | 5 | `assemblySkeletonDescription_run_` |
| 25 | 57 | 1,425 | 1 | `structuredMixedOptionCellQuoteLiveTailEmitterDescription_` |
| 28 | 49 | 1,372 | 1 | `structuredRawBoundaryRightEdgeEmitterDescription_` |
| 41 | 33 | 1,353 | 2 | `singletonShapeRefreshDescription_` |
| 31 | 42 | 1,302 | 3 | `rightBoundaryGuardSlackRefreshDescription_` |

## Wrapper-Like Files

The short-body scan counts theorem and lemma blocks with small `exact`,
`simpa`, or `rw` bodies. It is intentionally heuristic, but it identifies good
next candidates for wrapper-family deletion.

| Count | File |
| ---: | --- |
| 55 | `EncRewriters/ClosedCfgRunner/Projection/Padded/TailCleanup/ScratchExtCountWindowBridge.lean` |
| 42 | `EncRewriters/ClosedCfgRunner/Projection/Quoter/SourceRestFinishCore/Views.lean` |
| 30 | `EncRewriters/ClosedCfgRunner/Projection/Padded/TailCleanup/SelectedFootprintCompaction.lean` |
| 30 | `EncRewriters/ClosedCfgRunner/Projection/Quoter/SourceRestFinishCore/LTEmitterRuns.lean` |
| 26 | `EncRewriters/ClosedCfgRunner/Projection/Quoter/SourceRestFinishCore/LTJoinerRuns.lean` |
| 24 | `EncRewriters/ClosedCfgRunner/Projection/Padded/TailCleanup/StructuredPrefixEraserHandoff.lean` |
| 23 | `EncRewriters/ClosedCfgRunner/Merge/Padded/PostTransition/ParsedInnerWindows.lean` |
| 22 | `EncRewriters/ClosedCfgRunner/Merge/Padded/CleanupBase.lean` |
| 21 | `EncRewriters/ClosedCfgRunner/Projection/Padded/TailCleanup/PostErase.lean` |

## Next Target

The two pilot files from the plan are done, and the wrapper-heavy selected
footprint file has also been pruned. The strongest wrapper-heavy next candidate
is
`EncRewriters/ClosedCfgRunner/Projection/Padded/TailCleanup/ScratchExtCountWindowBridge.lean`.
For the plan's later assembly-family work, the repeated-prefix scan still shows
`assemblySkeletonDescription_run_` as a cross-file cluster.
