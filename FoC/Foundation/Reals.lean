import FoC.Foundation.Reals.Basic

set_option doc.verso true

/-!
# Reals

This wrapper exposes the Dedekind-cut real-number layer used by the early book
chapters. The implementation is split below {module}`FoC.Foundation.Reals.Basic`
and its supporting rational infrastructure; this module is the public entry
point for order, arithmetic, inverse/division, and the example lemmas used by
Chapter 1.

The real-number development is infrastructural for the companion, not a
general-purpose analysis library. Classical choice appears only at the witness
selection boundaries documented in the child modules.
-/
