# M4 — Exact-code validator construction roadmap

Date: 2026-07-17. Route-A phase 1 of the self-halting recognizer (M6 audit).
Campaign: `compiler-campaigns/self-halting-recognizer.json`. Spec anchor:
`FoC/Computability/Compiler/Core/SelfHaltingRecognizer/ValidatorSpec.lean`
(committed `8b789bfa`).

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
   rejected. M7 cumulative growth is +209 / +20000 after the deletion pass.*
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
   standard project axioms. Cumulative M7 growth is +1235 / +20000; leaf 2 is
   +1026 after its 17-line causally-connected deletion pass.*
3. **Transition-record scan + bounds** — for each of the counted records, parse
   `(source, read, write, move, target)` and check `source,target < stateCount`.
   New leaf; track `decodeTransitions count tokens` (not the header scanner).
4. **Suffix-emptiness check** — after the counted records, verify the tape head
   is at the end (empty suffix). This is condition 2 of the decomposition and
   the exact-code (no-trailing-junk) guarantee. New leaf.
5. **Determinism check** — verify no two parsed records share a lookup key with
   different actions (`transitionDeterministicPairBool`,
   `transitionWellFormedBool` from `TransitionTableChecks.lean` are the semantic
   oracles to match). New leaf; the hardest, needs a pairwise-key scan.
6. **Boolean emit + halt-stability** — on all-checks-pass emit `[true]`, else
   `[false]`; wire through `BoolOutputDescription`-style tails. Prove
   `HaltTransitionFree` and distinct outputs.
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

This is the plan's "Medium–large" milestone (~person-weeks). Leaves 3–5 remain
the substantive new finite machines; each must be built closed (no sorry, the
Compiler tree is sorry-free), with a causally-connected deletion pass and a
growth measurement after each, staying within the campaign's +20000 allowance.
The token-alignment gate (leaf 1), header parser (leaf 2), and prefix parser are
reusable closed starting points.
