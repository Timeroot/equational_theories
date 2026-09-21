# Two more unrestricted term-structural separations

Date: 2026-09-21. Arrows below are source → target.

Lean now refutes **E65 → E1491** and **E1648 → E124** for term-structural
interpretation on arbitrary carriers. Both pairs remain equivalent on finite
carriers. These results settle two more unrestricted equivalence questions;
they make no FO-structural claim.

The remaining unrestricted inventory has **32 unresolved class pairs / 152
raw unordered equation pairs**, down from 34 / 160. There are still 739
currently proved unrestricted classes and exactly 716 finite classes.
The pairs removed are `{65, 261}` versus `{1491, 2061}`, and `{124, 206}`
versus `{1648, 1924}`.

Closure adds eight directed negative equation pairs, comprising two class
cells, on the unrestricted term-structural board. The other nine boards are
unchanged. E1491 → E65 was already proved; E124 → E1648 remains open on
arbitrary carriers.

## The common obstruction

Let `S(x) = x*x`. In an E1491 magma, Lean proves

```text
(x*x)*x = x*x,
(x*x)*(x*x) = x*(x*x),
S³(x) = x.
```

The complete multiplication table on `x, S(x), S²(x)` is

| Left argument | x | S(x) | S²(x) |
|---|---|---|---|
| x | S(x) | S²(x) | x |
| S(x) | S(x) | S²(x) | x |
| S²(x) | S(x) | S²(x) | x |

The entries may coincide. Induction on terms proves that every unary term
is uniformly one of `id`, `S`, and `S²`. In particular, every unary term is
a bijection, since `S³ = id`.

For E124 the analogous identities are

```text
(x*x)*x = x*x,
x*(x*x) = x,
S²(x) = x.
```

The two-element table is again independent of its left argument and advances
the right argument once around the cycle. Every unary term is `id` or `S`,
and hence is a bijection.

Now suppose an operation `M` could be recovered by a binary term `v` from
either target operation `N`. Its square map would be the unary term
`x ↦ vᴺ(x,x)`, so it would be injective. This rules out **every** companion
and recovery term whenever `M` has a noninjective square map. No restriction
on the length of the defining terms is needed, and the forward term is not
used in the contradiction.

## The infinite source models

Both witnesses live on the natural numbers. Existing extension theorems
complete small partial operations while preserving their specified values.

For E65, the seed has the five entries

```text
0*0 = 0,  1*1 = 0,  1*0 = 2,  1*2 = 1,  2*2 = 1.
```

Its completed obligations are the instances of E65 at `(0,0)` and `(1,1)`.
The seed satisfies all conditions of `Asterix.PartialSolution`, and
`Asterix.closure_prop` proves E65 on its completion. The two square values
at 0 and 1 remain equal.

For E1648, the seed consists only of `0*0 = 0` and `1*1 = 0`.
It satisfies the three partial-operation rules of `Eq1648.PartialSolution`.
The existing completion theorem gives E1648 on all natural numbers and
preserves both entries. Again the square map is not injective.

The source constructions and all unary-term invariants are formalized in
[UnaryThreeCycle.lean](../equational_theories/Definability/UnaryThreeCycle.lean)
and [UnaryTwoCycle.lean](../equational_theories/Definability/UnaryTwoCycle.lean).
The exported conclusions are

* `Equation1491_not_termStructuralFrom_Equation65_unaryThreeCycle`;
* `Equation124_not_termStructuralFrom_Equation1648_unaryTwoCycle`.

Both have transitive axiom guards permitting only `propext`,
`Classical.choice`, and `Quot.sound`. Proof search suggested the unary
identities; the final Lean proofs do not trust an external ATP certificate.

## Validation and scope

The full 16,975-job `Definability` build passed. All ten quotient closure
calculations matched the full-matrix reference; the import-closure check and
19 bookkeeping tests passed. Comparing the before/after snapshots confirmed
exactly eight new unrestricted term-structural negatives and no changes to
the other nine relations.

Build `equational_theories.Definability`, then regenerate the board with
`OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --verify-closure`.
Regenerate both equivalence inventories with
`scripts/definability_term_structural_equivalence_gaps.py --write` and
`scripts/definability_structural_equivalence_gaps.py --write`, using the same
`OPENBLAS_NUM_THREADS=2` setting.

These are arbitrary-carrier term-structural negatives. They cannot be
finite negatives because the finite positive equivalences are already proved.
They cannot be upgraded to one-way term-definability negatives: the right
projection satisfies both E1491 and E124. The FO-structural questions remain
open.
