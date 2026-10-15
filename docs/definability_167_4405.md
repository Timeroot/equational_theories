# E167 does not finitely FO-define E4405

The arrow is **negative, proved in Lean**. E167 is `x = (y*x)*(x*y)`; E4405 is
`x*(x*y) = (y*x)*x`, or `L_x² = R_x²`. An eight-element E167 model admits the
Klein four group acting freely on two four-point orbits. The existing theorem
`noprn8h4a_Law4405` already excludes every operation satisfying E4405 and
preserving that action. Every parameter-free definable operation must preserve
these automorphisms, so no such operation exists on this finite source.

`Definability/BookendEight.lean` proves
`Equation4405_not_definableFromFin_Equation167` and
`Equation4405_not_definableFrom_Equation167`. The new source law and all four
automorphisms are checked by kernel reduction on the 64-entry table. The target
exclusion reuses the earlier native exhaustive-search theorem unchanged; this
adds no certificate or repeated exhaustive check. The new module builds in
4.9 seconds.

The discovery used a 0.004-second source SAT call and a 0.429-second target
UNSAT call. These external results are superseded by the Lean proofs. The
full automorphism group of the source is exactly V4 by independent exhaustive
enumeration, although the Lean argument only needs the displayed subgroup.
Data are in `data/definability_167_4405_separation.json`; run
`scripts/definability_167_4405_separation_check.py` to check the tables, symmetry,
and relabeling, optionally with `--search` to repeat the discovery calls.

## A simple constructive source family

There is also a direct construction, independently checked at order eight,
which explains why the V4 action is compatible with E167. Let V be an
elementary abelian 2-group, choose u in V and a homomorphism
`chi : V -> F2` with `chi(u)=1`, and use the carrier `V x F2`. Write inputs
`x=(a,i)`, `y=(b,j)` and `c=chi(a+b)`. Define the product by:

- If x=y, return x.
- If i=j=0 and a differs from b, return `(a,1)`.
- If i=j=1 and a differs from b, return `(b,0)`.
- If i differs from j and c=0, return `(a+i*u,i)`.
- If i differs from j and c=1, return `(b+(1-i)*u,j)`.

For distinct inputs in the same layer, the two intermediate products move
to the other layer, and applying the product again returns x. For inputs in
different layers, each intermediate product changes exactly one vector by u;
therefore the next value of c is `1-c`, and the opposite cross-layer rule
returns x. Equal inputs are idempotent. This proves E167. All translations
`(a,i) -> (a+v,i)` preserve the product. Taking `V=F2^2` gives the required V4
action on eight points. This general construction is a paper argument; the
Lean separation uses the original source table, whose verification is small.

The following sections preserve the restrictions that guided the search.

## A new symmetry restriction, formalized in Lean

Let σ be any involutive automorphism of an E167 magma and define

```
t(x) = x * σ(x).
```

Then

```
t(t(x)) = (x*σ(x)) * (σ(x)*x) = σ(x).
```

Thus t is a permutation square root of σ, with inverse `σ(x)*x`. Moreover t
commutes with every source automorphism commuting with σ. Neither fact needs
finiteness. On a finite carrier, σ consequently has sign +1: the sign of a
permutation square is +1. In particular a fixed-point-free involutive
automorphism has an even number of two-cycles. If σ is central in the source
automorphism group, t and the partition into its four-element orbits in the
fixed-point-free case are preserved by that group. The group can still permute these orbits;
this alone does not construct an E4405 operation.

These statements are proved in
`Definability/BookendSymmetry.lean`: `root`, `root_twice`, `root_sq`,
`involutive_auto_even`, and `root_commutes`.

The useful diagonal reduction was already present in the repository:
`QFOp.idem_167` in `Definability/CaseSplit.lean` proves that replacing `x*x` by x
preserves E167 and gives a quantifier-free definable idempotent operation.
Consequently restricting the source searches below to idempotent models loses
no possible action-level obstruction.

## Two classes where finite FO definability still follows

The following constructions are pen-and-paper arguments, not new Lean theorems.
They use the existing finite bridge between automorphism invariance and
parameter-free definability (`Definability/FiniteBridge.lean`).

If the full automorphism group of any finite magma has **odd order**, it admits
an invariant commutative conservative operation. Choose an endpoint on each
orbit of unordered pairs and transport it around that orbit. A setwise pair
stabilizer cannot interchange its endpoints, since an odd-order group has no
permutation of order two on a two-element set. The choice is therefore
well-defined. This gives E4405 without using E167.

If the full automorphism group of a finite E167 magma has **order two**, it
also admits an invariant E4405 operation. A fixed point of its generator gives
an invariant constant operation. Otherwise the newly proved sign restriction
pairs its two-cycles into invariant four-element blocks. On each block use
this table, invariant under `(0 1)(2 3)`:

```
0 2 0 2
3 1 3 1
3 1 2 0
0 2 1 3
```

The table satisfies E4405, although it is not commutative. Order the invariant
blocks arbitrarily; on arguments in different blocks return the argument from
the earlier block. This ordered sum preserves E4405: when the blocks differ,
both sides are either the earlier argument or its square, and when they agree
the block law applies. The resulting operation is invariant under the entire
automorphism group and hence definable on the finite source. Empty carriers
are trivial. Thus a finite counterexample must have an even automorphism group
of order at least four.

## A further cyclic-action exclusion

This is also a pen-and-paper result. Suppose a cyclic automorphism group acts
freely with m orbits of length n, where `n ≡ 0 mod 4`. Then **m must be even**.

Indeed the equivariant map `T(x,y)=(x*y,y*x)` squares to coordinate swap. On the
quotient of ordered pairs by the cyclic action, the swap permutes triples
`(i,j,d)` by `(i,j,d) ↦ (j,i,-d)`. Its number of transpositions is

```
m*(n-2)/2 + n*m*(m-1)/2,
```

whose parity is m. An odd m would make it an odd permutation, although the
induced T is its square root. In particular an even-order E167 magma cannot
have an automorphism consisting of one full cycle. This also excludes the
three disjoint four-cycles action on twelve elements.

## Bounded experiments and their limits

`scripts/definability_167_4405_probe.py` tested 32 permutation actions of degree
at most 24, using three-second CaDiCaL limits and no proof traces. It found:

- 21 source UNSAT results, external and not certified in Lean;
- nine actions with independently verified E167 and compatible E4405 tables;
- two source timeouts, subsequently excluded by the cyclic-action argument
  above: one sixteen-cycle and three four-cycles.

Compatibility under the supplied generators is **not** a proof of FO
definability on a saved source: its full automorphism group may be larger.
No automorphism obstruction was found in that first pass. Separately, exhaustive enumeration on
four points under `(0 1)(2 3)` found 48 E167 operations and four E4405 operations.
Each source has full automorphism group exactly C2, and all four targets are
compatible with it. The script reproduces this enumeration as well.

The saved tables, actions, counts, and scope notes are in
`data/definability_167_4405_probe.json`. The next targeted test added the missing
V4 action on two regular orbits,
which produced the separation above. Thus the earlier lower bound of four on
the automorphism-group order is attained.
