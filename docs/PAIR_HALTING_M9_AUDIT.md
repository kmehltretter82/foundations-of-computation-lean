# M9 Pair-Halting Composition Audit

Date: 2026-07-19

Pinned pre-campaign commit: `aafc752029a6ad52734829d1834dcd4528818baa`

## Decision

M9 will use the self-delimiting concatenation currency rather than the tagged
`PairCodeSymbol` currency.  A canonical pair word consists of one *complete*
finite-description code followed by the separately supplied code-symbol input.
Membership requires successful prefix decoding, decoded-description
well-formedness, and halting on the canonical four-bit encoding of the suffix.
Consequently the first component has a unique boundary whenever the word is a
member.  Failed prefix decoding and decoded but non-well-formed descriptions
are both outside the language.

For a valid complete code `w`, prefix decoding of `w ++ w` returns exactly the
description decoded by `w` and the second copy of `w`.  Thus membership of
`w ++ w` in the pair language is equivalent to `CodeAccepts w w`.  This is the
unambiguous self-delimiting alternative permitted by M9; the old tagged pair
language remains a compatibility surface rather than the canonical finite
description theorem.

## Checked construction route

Given an arbitrary `MachineDescription` that halt-stably decides the canonical
pair language, construct a self-halting decider by sequencing:

1. `ExactCodeValidator.GateDescription`, preserving the valid source word;
2. `rightEdgeRewindDescription`, returning the head to the left input edge;
3. a finite self-append materializer obtained by running
   `SelfAppendRunner.machine` with an immediate-halt runner and lowering it
   through `CodeAlphabetLowering`;
4. the supplied pair decider.

The existing `SameHeadComposition.leftRightSeqDescription` combinator supplies
well-formed sequencing, forward composition, exact closed inversion, stuck-run
lifting, and tape-equivalence transport.  A campaign-local structural wrapper
will preserve ordinary completion at the composed machine's halt and route
only missing nonhalt transitions to a rewind/erase/emit-reject tail.  Therefore
valid runs retain the supplied decider's normalized output, while every invalid
validator run becomes a stable reject result.

## Boundary and collision audit

- **Empty input:** not a complete description code; the validator reaches a
  nonhalt missing transition and the completion wrapper rejects.
- **Incomplete header:** rejected by the validator before materialization.
- **Raw decodable but non-well-formed code:** rejected by the bounds or
  determinism gate before materialization.
- **Canonical code plus nonempty junk:** rejected by the exact suffix gate;
  the prefix parser alone is not used as the validity test.
- **Valid source head:** the exact validator stops at its validated right
  boundary.  The existing right-edge rewind returns to the first encoded bit.
- **Materializer handoff:** the lowered self-append machine starts at the first
  four-bit block and stops at the first block of `w ++ w`, modulo `Tape.Equiv`.
  The following description observes only the represented tape, so no physical
  context normalizer is required.
- **Output stability:** the supplied decider's halt and tape are preserved by
  the missing-only wrapper.  Its reject tail is used only for an actually
  missing nonhalt transition and constrains only normalized output.
- **Equivalent-start collision:** the proposed target for materialization is
  stated modulo `Tape.Equiv`; trailing blank-window differences therefore do
  not demand inequivalent exact targets.
- **Malformed diagonal words:** no theorem claims that blindly mapping every
  `w` to `w ++ w` preserves membership.  That statement is false in the
  presence of prefix/junk collisions.  The finite construction first proves
  `w` is a complete valid code and queries the pair decider only on that branch.

## Rejected alternatives

- Directly lowering the existing faithful tagged diagonal machine would need a
  new general block-alphabet compiler: its work alphabet has substantially
  more symbols than the current four-bit code alphabet.
- Blind concatenation without the exact-code gate is unsound because an
  invalid first copy can combine with the second copy into a different valid
  prefix.
- Reusing `ValidatorBooleanCloseout` directly would erase the valid source and
  replace the supplied pair decider's output, so M9 needs the smaller
  missing-only completion described above.

## Budget estimate and campaign gate

The route reuses all large machine leaves.  Expected production growth is a
small lowering endpoint bridge, one immediate-halt materializer, one local
missing-only completion wrapper, composition proofs, semantic packaging, and
book consumers.  This is expected to fit the ordinary cumulative `+10,000`
Compiler-line allowance.  At the gate, M7 measures `+27,428 / +30,000`, the
aggregate active-loan circuit has `90,000` lines free, and the independent
global raw-growth circuit has `23,100` lines free.  The M9 campaign therefore
opens at the pinned commit above without changing either the M7 allowance or
the global baseline.

## Closeout measurement and deletion pass

The checked route closed with all three campaign modules reachable from
`FoC.lean`, zero direct sorries, and `+856 / +10,000` net Compiler lines against
the pinned M9 commit.  M7 remained at `+27,703 / +30,000`; total raw Compiler
size was 510,097 lines, or `+163,031 / +185,000` over the global baseline.

The causally connected deletion pass ran immediately after the final reduction
theorem compiled.  It removed a campaign-local proof of converting
`HaltsFromTapeEquiv` into normalized output and reused the existing
`MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv` API instead,
for a measured eight-line net Compiler reduction.  Declaration-reference review
found no other obsolete M9 scaffold: the three finite phases, their composition
proof, and the malformed-input completion are all on the public theorem's live
route.  The rejected tagged-lowering, blind-concatenation, and source-erasing
closeout alternatives were audited before implementation and therefore left no
code to delete.
