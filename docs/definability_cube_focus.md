# E3342 versus E3545: focused pass

**E3342 → E3545 is refuted for finite and unrestricted term-structural
interpretation.** The countermodel has 27 elements. The reverse direction
remains open, but the two equivalence classes are now proved distinct in both
variants. This settles the last finite equivalence question: there are exactly
**716 finite term-structural equivalence classes** among the catalogued laws.

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
