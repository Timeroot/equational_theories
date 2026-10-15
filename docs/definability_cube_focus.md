# E3342 versus E3545: focused pass

**E3342 → E3545 is refuted for finite and unrestricted term-structural
interpretation.** The countermodel has 27 elements. The reverse direction
remains open, but the two equivalence classes are now proved distinct in both
variants. This settles the last finite equivalence question: there are exactly
**716 finite term-structural equivalence classes** among the catalogued laws.

**E3342 and E3545 are now proved finite FO-structurally equivalent.** The
forward construction in
[`CubeForwardStructural.lean`](../equational_theories/Definability/CubeForwardStructural.lean)
and the reverse construction in
[`CubeReverseFO.lean`](../equational_theories/Definability/CubeReverseFO.lean)
are exact inverses on finite carriers. The reverse direction also gives
**E3545 → E3342 for unrestricted FO-definability**. A simpler, potentially
nonreversible quantifier-free finite E3342 → E3545 construction remains in
[`CubeConditional.lean`](../equational_theories/Definability/CubeConditional.lean).
Neither outstanding term-definability arrow nor either unrestricted
FO-structural arrow is established by these constructions.

## The reversible finite construction (12 October 2026)

Write `q(x)=x*x`, `s(x)=x*(x*x)`, and `t(x)=(x*x)*x` in an E3342 source.
The left cube has stable kernel: `s²(x)=s²(y)` implies `s(x)=s(y)`.
Consequently, on a finite carrier, `s` permutes its own image `I`. Extend this
permutation to the whole carrier by setting `P(z)=s(z)` for `z∈I` and `P(z)=z`
otherwise. Now define

```
x □ y = if q(x)=q(y) then x*y else P(x*y).
```

Every right cube `t(x)` belongs to `I`. To see this, take `a∈I` with
`s(a)=s(x)`, using the permutation of I. Twisted commutativity gives equal
squares and equal right cubes for a and x, while `t` fixes I; thus `t(x)=a`.
The finite absorption identities already proved for E3342 give `s(t(x))=s(x)`.
It follows that the new operation has square q and right cube s. Over an
idempotent square the two source cubes coincide, which handles the other
branch. E3342's twisted commutativity is therefore exactly E3545 for □.

Recovery uses the same square-equality test and applies `P⁻¹` to an output
in the unequal-square branch. Both q and s are visible in □ as its square and
right cube. Membership in I is the formula `∃a, s(a)=z`, and the inverse is
uniquely characterized inside I, so this is a parameter-free FO construction
in both directions. It is exactly the earlier reverse construction, now
proved inverse on **every** finite E3342 source. Together with the previous
inverse identity on E3545 sources, this also supplies a bijection between the
two sets of labeled models on any fixed finite carrier.

The public theorem is
`Equation3545_structuralFromFin_Equation3342_cubeImage`. Its axiom guard lists
only `propext`, `Classical.choice`, and `Quot.sound`; there are no new finite
searches, certificates, or `sorry` obligations. The new module built in 3.2
seconds with its dependencies cached. The older 27-element obstruction below
still separates the **term-structural** classes.

The refreshed audit has **711 finite FO-structural classes**, down from 712.
The merged class contains E3342, E3545, E3964, and E4167. Closure settles 24
previously open directed equation pairs, including the class-level arrows
E3342 → E8, E411, E1020, E1223, and E3545. The finite FO-definability count
remains 87: that weaker merger was already obtained by the earlier construction.

`scripts/definability_cube_conditional_check.py` checks the reversible version
on 11 saved E3342 sources, 36 pair-products, and 8 saved E3545 sources. Each
check verifies both the target law and exact recovery of the input table.

## The 27-element obstruction

[Cube3342Root.lean](../equational_theories/Definability/Cube3342Root.lean)
proves the separation for the product of a three-element magma `P` and a
nine-element magma `F`. Both factors satisfy E3342.

The table of `P` is

```text
0 0 1
0 0 1
1 1 2
```

Its binary term clone has eight operations. Seven preserve the relation
`R = {(a,b) : a ≠ b or a = 0}`; the original multiplication does not, since
`(0,2)` and `(2,0)` belong to `R` but their coordinatewise product `(1,1)`
does not. A term operation from which the source multiplication can be
recovered must therefore induce the original multiplication on `P`.

The eight-operation composition table imposes a stronger syntactic condition:
a term inducing that multiplication has a root with a unary term in `x` on
one side and a unary term in `y` on the other, in either order. This condition
is proved inductively, so it applies to terms of every size.

The second factor has carrier `(Z/3Z) × (Z/3Z)`. Its multiplication is

```text
(i,u) * (i,v)     = (i+1, 0)
(i,u) * (i+1,v)   = (i, u-v+1)
(i+1,u) * (i,v)   = (i, v-u).
```

All coordinates are modulo three. Its unary term clone contains 27 operations.
Thus the preceding root condition restricts a possible companion operation on
`F` to one of `2 × 27² = 1458` parametrizations. Exactly 54 satisfy E3545;
these represent six distinct operations, each with image of size six.

Choose a value `c` missing from the companion's image. The original
multiplication has inputs `a,b ≠ c` with `a*b = c`. Every companion term
applied to these inputs avoids `c`: a variable gives `a` or `b`, and a
nonvariable term gives a value in the companion's image. Recovery is
therefore impossible. On the product, the same argument uses the second
coordinates of `(0,a)` and `(0,b)`.

The Lean proof packages both restrictions as clone invariants and applies
them to arbitrary defining and recovery terms. It does not enumerate the
27-element binary clone or assume a term-size bound.

The [finite certificate](../equational_theories/Definability/Generated/Cube3342RootData.lean)
is checked by ordinary `decide`. Both final theorem axiom guards list only
`propext`, `Classical.choice`, and `Quot.sound`. The
[reproducer](../scripts/definability_cube_root_certificate.py) constructs the
factors and clones from scratch and checks the
[saved data](../data/definability_cube_root_obstruction.json):

```sh
python3 scripts/definability_cube_root_certificate.py
lake build equational_theories.Definability.Cube3342Root
```

This proves a term-structural negative. It does not assert an FO-structural
or term-definable negative. The positive examples below remain valid: in
particular, the nine-element factor itself admits a term-equivalent E3545
operation. The product with `P` supplies the additional restriction needed
for the counterexample.

## Uniform recovery on a larger family

[The successor-family proof](../scripts/check_definability_successor_fiber.lean)
constructs mutually term-definable E3342 and E3545 operations on
`Option (I × A)`, where:

* `A` is any group, possibly infinite and noncommutative;
* `e` is a central element of `A`;
* `s : I → I` satisfies `s(i) ≠ i` and `s(s(i)) ≠ i`.

There is no injectivity or finiteness assumption on `s`. This includes finite
cycles of every length at least three, infinite successor chains, and maps with
branches feeding into cycles. The extra element `none` is an absorbing zero.

For nonzero inputs `(i,u)` and `(j,v)`, the operations are:

| Condition | E3342 operation | E3545 operation |
|---|---|---|
| `i = j` | `(s(i), 1)` | `(s(i), 1)` |
| `s(i) = j` | `(i, u v⁻¹ e)` | `(i, u v⁻¹ e²)` |
| `i = s(j)` | `(j, v u⁻¹)` | `(j, v u⁻¹ e)` |
| Otherwise | `none` | `none` |

The hypotheses on `s` make the three nonzero cases disjoint.

The forward term has 10 leaves. Writing `u = x*y` and `v = y*x`, it is

```text
((u*x)*u) * ((u*y)*v).
```

The newly found recovery term has **16 leaves**, improving on the previous
24-leaf term for the three-cycle family. Writing `qx = x*x`, `qy = y*y`, and
`v = y*x`, it is

```text
(((x*qx)*qx) * ((v*y)*y)) * ((y*qy) * ((v*x)*x)).
```

Each expression uses the operation from which it is interpreting the other.
The terms work uniformly; they do not depend on cycle length, group order,
or the order of `e`. The original 24-leaf recovery term fails on longer cycles,
but that failure does not give a separation: the new 16-leaf term repairs it.

The [direct nonabelian three-cycle proof](../scripts/check_definability_nonabelian_fiber.lean)
also verifies the shorter recovery term without adjoining zero. The
[machine-readable terms](../data/definability_successor_fiber_recovery.json)
record the generalized construction.

The successor-family law proofs use only `propext`; its two term-structural
theorems use only `propext` and `Quot.sound`. All four are checked by axiom guards.
These family results do not apply to the known infinite `Eq3342.op` example,
whose additional inequalities restrict when a product is nonzero.

## Recovery must be checked separately

[A new three-element certificate](../scripts/check_definability_3342_candidate_recovery.lean)
shows that the earlier 42-leaf candidate can satisfy E3545 while losing any
possibility of recovering the source operation. On

```text
source:       candidate:
0 0 1         0 0 0
0 0 1         0 0 0
1 1 2         0 0 2
```

the source satisfies E3342 and the candidate satisfies E3545. Every candidate
term preserves `{0,2}`, while the source sends `(0,2)` to `1`. Consequently no
recovery term exists for this candidate, irrespective of term length. The Lean
proof uses ordinary kernel checking. This refutes the candidate, not the full
term-structural direction.

The guided searches now require the proposed operation to preserve the source's
product image and idempotents, as necessary conditions for mutual recovery on
these nonprojection examples. The searches found no common candidate in
2,000,000 signatures for E3342 → E3545 and 1,456,059 signatures in the reverse
direction. Neither search exhausted a clone.

## Higher-arity checks on the saved finite companions

The previously saved eight- and nine-element
[companion pairs](../data/definability_3342_mixed_companions.json) pass all
three-position interpolation tests, in both directions and with mixed factors.
There are 145 operation-table positions across the two factors, hence
`2 × binomial(145,3) = 995,280` tests. A passing test says that some binary term
matches the desired operation at those three positions; different triples may
use different terms.

Four-position sampling also passed: 945,362 evaluations after rejecting tuples
with repeated coordinates, across both directions and all five factor patterns.
Samples can repeat, and this was not exhaustive. These tests do not establish
full term recovery or equality of the term clones. A bounded search for common
majority terms also found none; that is not a nonexistence result.

[The saved checks](../data/definability_cube_focus_checks.json) retain the exact
triple counts, four-position sampling parameters, and bounded search summaries.

## Reproduce the checks

```sh
lake env lean scripts/check_definability_successor_fiber.lean
lake env lean scripts/check_definability_nonabelian_fiber.lean
lake env lean scripts/check_definability_3342_candidate_recovery.lean
g++ -std=c++17 -O3 scripts/definability_cube_interpolation3.cpp -o /tmp/cube_interpolation3
python3 scripts/definability_cube_focus_check.py --interpolator /tmp/cube_interpolation3
```

The independent Python checker verifies both terms on 35 finite family pairs,
including noninjective successor maps and the noncommutative group `S₃ × C₃`.
The optional C++ check reproduces all 995,280 triple-interpolation tests.

## E3342 → E3545 on finite carriers: a conditional construction

This is a complete Lean proof in
[`CubeConditional.lean`](../equational_theories/Definability/CubeConditional.lean),
exported as `Equation3545_definableFromFin_Equation3342_conditional`. It uses
only the standard axioms, with no computational certificate. Write
`q(x)=f(x,x)`, `σ(x)=f(x,q(x))`, and `τ(x)=f(q(x),x)`, and define

```text
g(x,y) = if q(x)=q(y) then f(x,y) else σ(f(x,y)).
```

The old finite E3342 consequences E3522 and E4118 say that replacing either
argument by its right cube τ leaves the product unchanged. They imply
`q(τx)=qx` and `σ(τx)=σx`. If `q²x=qx`, its idempotence also makes
`σ(qx)=qx`; E3342 at `(qx,x)` then gives `τx=σx`. The new operation retains
q as its square map. Its right cube is τx in the equal-square branch and
`σ(τx)` otherwise, so in both cases it is **σx**. Finally E3342 is
`f(x,y)=f(y,σx)`, and `q(σx)=qx` makes the guards on the two sides agree.
Applying the same conditional output map gives `g(x,y)=g(y,σx)`, precisely
E3545 because σ is the new right cube.

The formula defining g is quantifier-free. This proves a finite FO arrow,
without claiming term-definability or recovery of the old operation. The
finiteness is essential to this particular recipe: on the existing infinite
`Eq3342.op` example, at `x=y=some (0,0)` the target equation has left side
`some (0,1)` and right side `none`. The theorem `infinite_recipe_failure`
checks this failure in Lean. It does **not** refute all possible unrestricted
FO definitions from E3342 to E3545.

The original experimental checks are retained as regressions:
`python3 scripts/definability_cube_conditional_check.py` checks 11 saved
sources and 36 pair-products. The optional bounded solver probes are no
longer evidence needed for the proof. The elementary twist identities in
[`CubeTwists.lean`](../equational_theories/Definability/CubeTwists.lean)
remain useful: simultaneous twist invariance preserves squares;
E3342 has `τ∘σ=σ`, and E3545 has `σ=τ²`.

## E3545 → E3342: canonical inverse on the cube image

This construction is fully proved in
[`CubeReverse.lean`](../equational_theories/Definability/CubeReverse.lean)
and its first-order formulas in
[`CubeReverseFO.lean`](../equational_theories/Definability/CubeReverseFO.lean).
The public theorems are
`Equation3342_definableFrom_Equation3545_cubeInverse` and
`Equation3342_structuralFromFin_Equation3545_cubeInverse`.
Both use only `propext`, `Classical.choice`, and `Quot.sound`; there are no
computational certificates, `native_decide` axioms, or `sorry` obligations.

Let an E3545 operation be `f`, with square `q` and right cube `τ`. Applying
E3545 twice gives `f(τx,τy)=f(x,y)` and hence `q(τx)=q(x)`. The crucial new
observation is that **τ is injective on its own image**, even on an infinite
carrier. Indeed, if `τ²x=τ²y`, square preservation gives `qx=qy`; applying
simultaneous invariance twice to `τx=f(qx,x)` and `τy=f(qy,y)` then gives
`τx=τy`. Thus there is at most one `w` in `range τ` with `τw=z`.

Define `u(z)` to be that unique `w` when it exists, and `z` otherwise. Its
graph is the explicit parameter-free formula

```text
u(z)=w  iff  ((exists a, τa=w) and τw=z)
              or ((not exists a, τ²a=z) and w=z).
```

In particular, `u(τ²x)=τx`, without a finiteness assumption. Define

```text
g(x,y) = if qx=qy then f(x,y) else u(f(x,y)).
```

The square map remains `q`, and the **left cube of g is τ**. To see this,
E3545 gives `f(x,qx)=τ²x`. If `qx≠q²x`, the new left cube is therefore
`u(τ²x)=τx`. If `qx=q²x`, then `τ(qx)=qx`, and simultaneous invariance of
`f(qx,x)` gives `τ²x=τx` directly. Finally, in the source equality
`f(x,y)=f(y,τx)`, the guards `qx=qy` and `qy=q(τx)` agree, so applying the
same conditional output map to both sides proves
`g(x,y)=g(y,τx)`. This is exactly E3342 because its new left cube is τ.

On a **finite** carrier, τ is a permutation of `I=range τ`, so
`range τ²=I`. Then `u` is the inverse permutation on I and the identity
outside I. Its inverse is the definable function
`v(z)=τz` for `z∈I`, and `v(z)=z` otherwise. Both `q` and `τ` are visible
in g as its square and left cube, respectively, and the original operation
is recovered by

```text
f(x,y) = if qx=qy then g(x,y) else v(g(x,y)).
```

This proves finite FO-structural definability, not just existence of a target
operation. The unrestricted one-way construction remains valid when
`range τ²` is properly contained in `range τ`; the finite recovery argument
then no longer applies. No assertion about unrestricted FO-structural or
term-structural definability is made here.
