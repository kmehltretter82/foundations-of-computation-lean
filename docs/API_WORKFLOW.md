# API Documentation Workflow

This project should not maintain broad API inventories by hand. The stable
source of API documentation is the Lean source itself: module docstrings,
declaration docstrings, names, imports, and generated documentation output.

## Current Rule

- Put reading guidance in `/-! ... -/` module docstrings near the declarations
  it describes.
- Put declaration-level explanations on public construction targets, closeout
  records, route contracts, and theorem surfaces that downstream files are
  expected to use directly.
- Keep wrapper modules as route maps and re-export boundaries. Do not add
  manually synchronized cross-reference modules listing declarations from many
  files.
- Short working maps such as `docs/COMPUTABILITY_WORKING_MAP.md` may point to
  module families, proof patterns, and search commands. Keep them navigational;
  do not turn them into hand-maintained theorem inventories.
- When an old public alias or route name is removed, update downstream users
  instead of preserving a forwarding alias only for documentation continuity.

## Generated Reference

Mathlib-style API reference is generated from Lean declarations and docstrings,
not maintained as a Lean module. If this project adds a full generated API
reference, use a pinned documentation tool such as `doc-gen4` and keep it as an
explicit documentation target or workflow.

The generated-reference workflow should be optional:

- Do not run generated API documentation during ordinary proof work.
- Do not make generated documentation part of every local `lake build`.
- Prefer a manually triggered CI workflow, a release workflow, or a clearly
  named local command for generated documentation.
- Do not commit generated HTML output.

Until that tooling is added, the Verso literate site remains the public reading
surface. The package target `lake build :docs` is intentionally an alias for
that site, so users have one stable documentation command while API navigation
improves by strengthening module and declaration docstrings in the Lean files
themselves.

## Local Checks

Documentation-only Lean edits still need Lean syntax checking. Use focused
checks such as:

```sh
lake env lean FoC/Computability.lean
```

Build the generated documentation with:

```sh
lake build :docs
```

Run full `lake build` only at stable checkpoints, before commits that affect
imports or broad API surfaces, or when focused checks are not enough.

## Declaration CSV

For local API audits, generate declaration data from Lean's elaborated
environment instead of parsing source text:

```sh
lake env lean --run scripts/export-declarations.lean \
  FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorInputMaterializer \
  FoC.Computability.StructuredConstructionTargets \
  > .lake/structured-target-decls.csv
```

Columns are `name`, `kind`, `module`, `file`, `is_private`, `is_generated`,
`has_sorry`, kernel `type`, and `normalized_type`.  The normalized type
beta/reducible-reduces the type and erases binder and universe parameter names
before printing.  The first argument is the module to import; the second is the
declaration-name prefix to include.  Exporting all of `FoC.Computability` is
possible once the imported `.olean`s are current, but focused module exports
are much cheaper during proof work.

Find exact duplicate type surfaces with:

```sh
scripts/find-duplicate-declaration-types.py --kind theorem \
  .lake/structured-target-decls.csv
```

Pass `--normalized` to group by the normalized type column:

```sh
scripts/find-duplicate-declaration-types.py --kind theorem --normalized \
  .lake/structured-target-decls.csv
```

Both modes are audit signals, not proofs that no semantic duplicates exist.
The normalized mode catches more alpha/unfolding noise, but it can still miss
statements that are equivalent only after simplification or theorem proving.
Generated equation/helper declarations and private declarations are filtered by
default; pass `--include-generated` or `--include-private` to include them.

For a broader manual review queue, summarize declaration smells:

```sh
scripts/summarize-declaration-smells.py .lake/structured-target-decls.csv
```

This reports sorry-backed declarations, long names/types, axiom/opaque rows,
and exact/normalized duplicate type groups.  Treat the output as a triage list
for human or AI review, not as an automated refactoring instruction.
