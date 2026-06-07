# Deferred Formalization Work

This file summarizes the main Lean formalization work that is still deferred
because it is construction-heavy or requires larger infrastructure. The
repository does not have hidden proof placeholders for these items; they are
tracked as explicit theorem shapes, construction principles, closeout records,
or coverage notes.

For the full source-of-truth status, see [`data/coverage.yaml`](data/coverage.yaml).

## Hard Deferred Work

### Chapter 1

- **Unconditional Dedekind-real division form of the geometric series.** The
  natural-number, quotient-rational, embedded-rational real, abstract algebraic,
  and conditional Dedekind-real multiplication forms are formalized. The fully
  unconditional arbitrary-real Dedekind-cut division statement remains deferred
  because it needs the general real ring-law package and arbitrary-real
  inverse/division infrastructure.

### Chapter 4

- **Exactness for harder unrestricted grammars.** The constructive generation
  direction is present for the unary square grammar and the power-of-two grammar,
  but the reverse generated-only direction is still isolated as named hard work:
  - `SquareDerivationShapeCompleteness`
  - `PowerTwoGeneratedOnlyLanguageConstruction`
- **Larger unrestricted grammar exercise exactness.** Representative derivations,
  invariants, finite-production witnesses, and several exact-language theorems
  are present, but exact generated-language proofs for every larger sample
  grammar remain deferred.

### Chapter 5

- **General decider-to-acceptor transition construction.** The concrete
  head-output stopped-decider transformation is formalized. The arbitrary
  normalized-output decider version is deferred because the halted head might
  not be on the output symbol, so it needs an output-scanning construction.
- **Concrete Section 5.2 compiler constructions.** The semantic and staged
  equivalences are formalized, but several finite machine-description compilers
  remain explicit construction surfaces:
  - dovetailing decider compiler from paired recognizers;
  - partial unary range/listing/program description compilers;
  - general-grammar recognizer description compiler;
  - recursively-enumerable-to-finite-production-general-grammar construction.
- **Concrete Section 5.3 universal machine.** The encoding, interpreter,
  compiled-machine simulation, decoder rows, diagonalization, and row-coverage
  wrappers are present. The remaining closeout is exactly:
  - `ConcreteEncodedInputProgramAcceptorCompilationConstruction`
  - `ConcreteUniversalRunnerConstruction`
- **Final concrete halting and pair-halting closeout.** The diagonal pair map
  computability is formalized. What remains is the generic or direct
  decidable-preimage transport needed to remove the last hypotheses from the
  concrete halting/pair-halting theorem shapes.

## Deferred Application Material

The following are intentionally lower priority because they are presentation,
programming-language, or exercise-enumeration artifacts rather than missing
formal cores:

- circuit drawings and design exercises;
- Java, C++, JavaScript, SQL, and DBMS runtime behavior;
- editor-specific regular-expression syntax, anchors, escaping, and
  search/replace behavior;
- executable parser-generator algorithms;
- large application-oriented BNF listing enumerations;
- extra deterministic-CFL exercise examples;
- extra pumping examples such as `{ww}`.
