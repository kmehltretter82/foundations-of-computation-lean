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
surface, and API navigation should improve by strengthening module and
declaration docstrings in the Lean files themselves.

## Local Checks

Documentation-only Lean edits still need Lean syntax checking. Use focused
checks such as:

```sh
lake env lean FoC/Computability.lean
```

Run full `lake build` only at stable checkpoints, before commits that affect
imports or broad API surfaces, or when focused checks are not enough.
