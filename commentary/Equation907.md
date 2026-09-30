Left multiplications are surjective and therefore bijective in finite models.

Every sufficiently large **odd** order has an idempotent model, proved in Lean by
gluing seeds of orders 3 and 23 over pairwise balanced designs. No numerical
cutoff has been extracted. Orders **2, 4, 5, 6, and 8** are excluded in Lean;
the order-8 proof checks all 45 canonical first-row forms.

Whether any even-order model exists remains unknown; **10** is the first open
even order. Commutative models are Steiner quasigroups and have odd order.
More generally, every finite model constructed as `x*y = f(x)g(y)c` from
endomorphisms of a group has odd order: E907 forces the maps to be
automorphisms and the group to be abelian. This obstruction is also proved
in Lean and includes noncommuting coefficient maps and arbitrary constants.

Lean sources: `Spectrum.E907.eventually_odd` in
`Spectrum/Equation907/OddTail.lean`, `Spectrum.not_order_907_8` in
`Spectrum/Equation907Eight.lean`, and `Spectrum.E907.GroupAffine.odd_card`
in `Spectrum/Equation907/GroupAffine.lean`. See also the
[research notes](../docs/e907_even_order_research_20260930.md).

This law cannot hold in a non-trivial semigroup (associative magma).
