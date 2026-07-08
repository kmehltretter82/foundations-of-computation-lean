import FoC.Foundation.Reals.Basic

set_option doc.verso true

/-!
# Reals

This wrapper exposes the Dedekind-cut real-number layer used by the early book
chapters. The implementation is split below {module}`FoC.Foundation.Reals.Basic`
and its supporting rational infrastructure; this module is the public entry
point for order, arithmetic, inverse/division, and the example lemmas used by
Chapter 1.

The commutative-ring laws are certified for {lit}`Real`: additive
associativity, commutativity, identities, and inverses
({name}`FoC.Foundation.Real.add_assoc`, {name}`FoC.Foundation.Real.add_comm`,
{name}`FoC.Foundation.Real.add_neg_cancel`), multiplicative associativity,
commutativity, and identities ({name}`FoC.Foundation.Real.mul_assoc`,
{name}`FoC.Foundation.Real.mul_comm`, {name}`FoC.Foundation.Real.one_mul`), and
both distributivity laws ({name}`FoC.Foundation.Real.left_distrib`,
{name}`FoC.Foundation.Real.right_distrib`). The field axiom is not certified:
existence of multiplicative inverses for arbitrary nonzero cuts is not proved,
and {name}`FoC.Foundation.Real.divByNonzero` is a classical selector specified
only on exact products via
{name}`FoC.Foundation.Real.divByNonzero_mul_cancel`.

The real-number development is infrastructural for the companion, not a
general-purpose analysis library. Classical choice appears only at the witness
selection boundaries documented in the child modules.
-/
