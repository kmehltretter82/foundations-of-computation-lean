import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.Physical

set_option doc.verso true

/-!
# Exact-code validator pairwise determinism gate

This wrapper exports the finite aligned-block machine together with its exact
forward and closed physical contracts.  It halts precisely when the parsed
transition table satisfies the canonical pairwise determinism check and
restores the transition-scanner handoff tape exactly.
-/
