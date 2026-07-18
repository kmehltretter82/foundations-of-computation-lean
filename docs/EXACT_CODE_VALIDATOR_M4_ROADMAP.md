# M4 — Exact-code validator construction roadmap

Date: 2026-07-17. Route-A phase 1 of the self-halting recognizer (M6 audit).
Campaign: `compiler-campaigns/self-halting-recognizer.json`. Spec anchor:
`FoC/Computability/Compiler/Core/SelfHaltingRecognizer/ValidatorSpec.lean`
(committed `8b789bfa`).

**Allowance reviews (2026-07-18).** The project owner first approved a narrow
+5,000 contingency, raising this campaign from +20,000 to +25,000 while
preserving its original pinned base. After the computed leaf-5 readiness
certificate proved memory-heavy, the owner approved reallocating at most
+2,000 of that contingency to a verbose structural proof. Leaf 5 closed at
+21,997 cumulative growth after its deletion pass. Leaf 6 then closed at
+23,022, leaving +1,978 for leaf 7 (exact-validator composition) plus
recognizer composition. The campaign ceiling and pinned base are unchanged.

## Target

`ExactCodeValidatorConstruction : Prop := DescriptionDecidableCodeLanguage ValidCodeLanguage`
— a halt-stable finite `MachineDescription` that, on canonical
`encodeCodeWordAsInput w`, halts with normalized output `[true]` iff
`DescriptionCodeValid w`, `[false]` otherwise, and is `HaltTransitionFree`.

Proved decomposition (`descriptionCodeValid_iff_prefix_nil_wellFormed`):
`DescriptionCodeValid w ↔ ∃ D, decodeDescriptionPrefix w = some (D, []) ∧ D.WellFormed`.

## Pre-construction audit findings

- **Decider idiom (confirmed):** hand-built explicit transition tables with
  `WellFormed`/`HaltTransitionFree` discharged by
  `rcases ht with rfl | … ; all_goals simp`. Reference deciders:
  `BoolOutputDescription` (`DescriptionExecution.lean:1112`, emits `[b]`),
  `FixedBoolPresenceScannerDescription` (`BoolOutputAcceptor.lean:29`),
  `EncodedCodeWordRecognizerDescription` (`DescriptionExecution.lean:1244`,
  closed 8-state table, no run lemma).
- **Reusable closed leaves:** `CodeWordAlignedPreScannerDescription`
  (`Dovetail/Scanner/TokenAligned.lean:40`) certifies "nonempty canonical
  code-word encoding" with forward + inverse halts-iff — a ready sub-gate for
  the token-alignment layer. The prefix parser
  `CodePrefixParserNormalizerMachineConstruction` (`UniversalAndRanges/Basic.lean:313`)
  is a finite machine recognizing prefix-decodability.
- **Output shape decision:** Boolean `[true]`/`[false]` halt-stable decider (not
  accept-by-halting), because consumer 2 (valid codes are a decidable code
  language) needs the decider, and the route-A composition can branch on the
  Boolean.
- **Input contract:** operate on `encodeCodeWordAsInput w` (Bool tape, four bits
  per `MachineCodeSymbol`), matching the `StoppedDescriptionDecidesCodeLanguage`
  contract.

## Buildable leaf decomposition (each a closed leaf; build + measure per leaf)

1. **Token-alignment gate** — reuse `CodeWordAlignedPreScannerDescription`;
   reject words that are not nonempty canonical four-bit code-word streams.
   *Status: closed 2026-07-18 in `ValidatorTokenGate.lean`: valid complete
   codes pass with an exact source-preserving handoff; all-word inversion
   characterizes precisely the nonempty canonical encodings; empty input is
   rejected. M7 cumulative growth is +209 / +25000 after the deletion pass.*
2. **Header/field parser on tape** — parse the header token then the fixed
   `decodeNat` fields (stateCount, start, halt, transition count), leaving the
   transition-record region. The unbounded field values remain in their
   preserved unary tape encodings; finite control cannot carry arbitrary
   naturals. `HeaderParser.lean` remains the semantic reference on its direct
   finite-`TuringMachine` route.
   *Status: closed 2026-07-18 under `ValidatorHeaderParser/`: `Basic.lean`
   defines the 21-state Boolean machine, `Runs.lean` proves the exact forward
   execution, and `Inversion.lean` proves canonical-code closed inversion plus
   the unique exact physical handoff. MCP verification reports only the
   standard project axioms. Cumulative M7 growth is +1235 / +25000; leaf 2 is
   +1026 after its 17-line causally-connected deletion pass.*
3. **Transition-record scan + all state bounds** — parse each counted
   `(source, read, write, move, target)` record and check the complete
   non-determinism bound currency: `0 < stateCount`, `start < stateCount`,
   `halt < stateCount`, and every `source,target < stateCount`. Track
   `decodeTransitions count tokens` (not the header scanner).
   *Status: closed 2026-07-18 under `ValidatorTransitionScanner/`. The finite
   same-head construction first checks all three header bounds, then parses
   exactly `count` rows in `decodeTransitions count tokens` currency while
   checking every source and target bound. It restores every reserved marker
   and exposes the exact suffix handoff. `Construction.lean` proves forward
   acceptance and all-word closed inversion (`accepts_of_haltsFromTape` and
   `exists_haltsFromTape_iff_accepts`); both report only the standard project
   axioms and the scanner tree has no direct sorry. The connected deletion pass
   replaced downstream cloned scan helpers with the shared run API. Cumulative
   M7 growth is +13560 / +25000 after file-size and naming cleanup.*
4. **Suffix-emptiness check** — after the counted records, verify the tape head
   is at the end (empty suffix). This is condition 2 of the decomposition and
   the exact-code (no-trailing-junk) guarantee.
   *Status: closed 2026-07-18 in `ValidatorSuffixGate.lean`. The leaf-3 handoff
   reads blank exactly when its decoded suffix is empty, formally separating
   empty and nonempty sources. A three-state blank gate bounces left/right and
   preserves the successful tape exactly; its all-suffix inversion proves that
   every halt forces `suffix = []`. Axiom output contains only the standard
   project axioms. The connected deletion pass removed a cloned halt-output
   uniqueness proof from leaf 3. Cumulative M7 growth is +13773 / +25000.*
5. **Determinism check** — verify no two parsed records share a lookup key with
   different actions (`transitionDeterministicPairBool`,
   `transitionWellFormedBool` from `TransitionTableChecks.lean` are the semantic
   oracles to match). New leaf; the hardest, needs a pairwise-key scan.
   *Status: closed 2026-07-18 under `ValidatorDeterminismGate/`. The 102-state
   logical block machine performs the triangular outer/inner row scan, compares
   source, read, write, move, and target fields, reaches an explicit nonhalting
   conflict state for equal keys with unequal actions, restores all markers on
   success, and halts on the original boundary. `Runs/Physical.lean` proves the
   exact successful target, conflict nonhalting, all-word closedness, and both
   upper-pair and full-pair iff contracts. `Lookup.lean` proves
   determinism, endpoint bounds, halt-freedom, and shared-entry readiness by
   row-family structure; this reduced the leaf readiness check from 179 seconds
   to 1.8 seconds. The connected deletion pass retired cloned four-left entry
   machines, local scan proofs, an unused selected-pair route, and obsolete
   certificate scaffolding. Focused axiom output contains only the standard
   project axioms. Cumulative M7 growth is +21,997 / +25,000.*
6. **Boolean emit + halt-stability** — on all-checks-pass emit `[true]`, else
   `[false]`; wire through `BoolOutputDescription`-style tails. Prove
   `HaltTransitionFree` and distinct outputs.
   *Status: closed 2026-07-18 in `ValidatorBooleanCloseout.lean`. The generic
   structural wrapper preserves every base transition, redirects the first
   base halt to an accept tail, completes every missing nonhalt lookup with a
   reject tail, and has no outgoing transition at its fresh halt state. Both
   tails rewind to the left boundary, erase the contiguous input, and halt on
   the exact normalized output `[true]` or `[false]`. The module proves
   `SubroutineReady`, base-step transfer, first-halt transfer, missing-key
   rejection, exact output, and distinct answers without a computed table
   certificate. Its focused check takes about 2.6 seconds. The connected
   deletion review found no obsolete leaf-local route to retire. Cumulative M7
   growth is +23,022 / +25,000.*
7. **Closeout** — compose 1–6 into `ExactCodeValidatorConstruction`; prove
   forward correctness and closed inversion on ALL words (not only canonical
   encodings), discharging `descriptionCodeValidBool_eq_true_iff_prefix_nil_wellFormed`
   against the concrete machine.

## Consumers (both required before promoting the validator API)

- **C1:** the self-halting recognizer — validator as phase-1 leaf, then the
  duplicator + closed prefix runner (route-A bridge already proved:
  `mem_codeSelfHalting_iff_valid_and_codePrefixAccepts_selfAppend`).
- **C2:** a standalone book theorem that `ValidCodeLanguage` is a
  `RecursiveCodeLanguage` (decidable code language).

## Scope note

This is the plan's "Medium–large" milestone (~person-weeks). Leaves 1–6 are now
closed with no direct sorry and cumulative growth of +23,022. Leaf 7 must
compose the exact validator, followed by the recognizer consumer, without
exceeding the remaining +1,978 campaign headroom. The token-alignment gate,
header parser, transition scanner, suffix gate, determinism gate, Boolean
closeout, and prefix parser are reusable closed starting points.
