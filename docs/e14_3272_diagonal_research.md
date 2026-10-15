# E14 to E3272: an invertible diagonal construction

Research status, 2026-10-11: **the general finite FO-definability arrow remains
open**. The same finite term-definability arrow remains open. The conditional
results below are proved in Lean in
[`DiagonalSemisymmetric.lean`](../equational_theories/Definability/DiagonalSemisymmetric.lean).
They are magma-level theorems, not unconditional entries in the implication
catalogue.

Write the source operation as `*`, and its diagonal as `D(x) = x*x`. The source
law E14 is `x = y*(x*y)`. The target E3272 is
`x□x = y□(x□(y□y))`.

## Bijective squaring gives a reversible construction

Suppose `D` is a bijection. Define

```
x □ y = D⁻¹(x * D(y)).
```

E14 with equal variables gives `x*D(x)=x`, so the new diagonal is
`D□(x)=D⁻¹(x)`. Consequently

```
y □ (x □ (y □ y))
  = D⁻¹(y * (x * y))
  = D⁻¹(x)
  = x □ x.
```

The change is reversible: applying it to `□`, whose diagonal is `D⁻¹`, gives
`D(x □ D⁻¹(y)) = x*y`. In particular it is FO-structural, not just a one-way
FO definition. In either direction the **same atomic formula** defines the
output `z` from inputs `x,y`:

```
z*z = x*(y*y).
```

Nothing here assumes that `D` preserves multiplication. The construction works
on infinite carriers as well. For finite carriers the inverse permutation is a
power of `D`, so both directions are terms made by repeated squaring. The Lean
results are `structuralOn_of_bijective_diagonal` and
`termStructuralOn_of_bijective_diagonal`; the underlying identities are
`twist_diagonal`, `twist_satisfies_3272`, and `twist_twice`.

If the automorphism group is transitive on a finite source, `D` is necessarily
bijective: its image is nonempty and invariant. More directly, given any `y`,
an automorphism carrying `D(y)` to `y` exhibits a square root of `y`. Thus a
finite counterexample to the requested FO arrow must have **more than one
automorphism orbit and nonbijective squaring**. The stronger term-structural
statement is `termStructuralOn_of_transitive`.

## The commutative odd-order subclass is covered

For a commutative E14 source, every left translation `L_x(z)=x*z` is an
involution. Its fixed points are precisely the square roots of `x`:

```
x*z = z    iff    z*z = x.
```

The nonfixed points of an involution occur in pairs, so every diagonal fiber
has the same parity as the whole carrier. On an odd carrier each fiber is
nonempty; finiteness then makes `D` bijective. Thus every odd-order commutative
E14 source admits the reversible term construction above. This includes
nonidempotent sources. On an even carrier each nonempty diagonal fiber instead
has positive even size, and `|image D| ≤ |G|/2`.

Lean proves the fixed-point description, involution property, fiber parity,
and odd-order term-structural corollary as `fixed_iff_square`,
`left_involutive`, `card_square_fiber_modEq`, and
`termStructuralOn_of_commutative_odd`.

## Shortcuts that do not work

The small checked tables are preserved in
[`research_examples.json`](../data/definability/e14_3272/research_examples.json).
They are research examples checked by exhaustive Python evaluation, not Lean
certificates. Run

```
python3 scripts/check_e14_3272_research_examples.py
```

The checker verifies E14, the diagonal, periodic points, commutativity when
claimed, the fiber parity, and the stated failures of closure. On the
bijective-diagonal example it also checks the E3272 construction and recovery.

* A **six-element E14 source** has diagonal `[0,0,2,1,0,5]`. Its periodic points
  are `{0,2,5}`, but `0*2=3` is transient.
* This failure persists with commutativity. A **ten-element commutative E14
  source** has diagonal `[0,0,2,1,5,5,1,9,2,9]`. Its periodic points are
  `{0,2,5,9}`, but again `0*2=3` is transient. Each nonempty diagonal fiber has
  size two, as required by the parity lemma.
* A **nine-element commutative E14 source** on `Z/9Z` has
  `x*y=x+p(y-x)`, with `p=[1,0,5,7,6,2,4,3,8]`. Its diagonal is `D(x)=x+1`, a
  nine-cycle. Thus squaring need not have order dividing three, even in the
  commutative, automorphism-transitive, bijective-diagonal case.

The first two tables were found by tiny finite searches, fixing
`D(0)=0`, `D(1)=0`, `D(2)=2`, `D(3)=1`, and `0*2=3`; the second search additionally
required commutativity. These examples rule out simply restricting the source
operation to periodic points. They are **not** counterexamples to
FO-definability: they do not show that all invariant target operations fail.

The existing finite term-structural negative route passes through the
four-element exact-endomorphism family in `Definability/ExactEnd4B.lean`
(source E2789, then E14). That family has an automorphism-fixed element, so
constant target operations are available for FO definability. Its
endomorphism obstruction therefore does not directly close the FO question.

The surviving task is to construct a target, or an automorphism obstruction,
for sources with nonbijective diagonal and multiple automorphism orbits. The
commutative even-order case remains a useful restricted version of that task.

## A second construction: duplicated fibers

A separate checked module,
[`SplitRetraction3272.lean`](../equational_theories/Definability/SplitRetraction3272.lean),
constructs E3272 from two equivariant maps `e,s` satisfying

```
e(e(x)) = e(x),      e(s(x)) = e(x),      s(x) ≠ e(x).
```

Define `q(x,y)` to be `e(x)` when `e(x)=e(y)`; otherwise let it be `s(x)` if
`y=e(y)`, and `e(y)` if `y≠e(y)`. Its diagonal is `e(x)`. When the two base
points differ, `q(x,e(y))=s(x)` and the outer operation returns
`q(y,s(x))=e(x)`; when they agree the law holds immediately. Thus q satisfies
E3272. On a finite carrier, equivariance under the source automorphisms makes
its graph parameter-free FO-definable. This argument needs no source equation.

The simplest instance is `X×{0,1}` with `e(a,i)=(a,0)` and `s(a,i)=(a,1)`.
The target is invariant under **every permutation of X**. Consequently two
isomorphic automorphism orbits can support E3272 even when a single copy
cannot; natural four-point symmetric-group actions are an example. This does
not require an E14 operation on the base.

More significantly, suppose **every nonempty squaring fiber has exactly two
elements**. There is then a unique other point `S(x)≠x` with `D(S(x))=D(x)`,
and automorphisms preserve S. Choose a positive idempotent iterate `e=D^N`
(which exists for every self-map of a finite set), and put `s(x)=S(e(x))`.
Since N is positive, `D(s(x))=D(e(x))` implies `e(s(x))=e(e(x))=e(x)`.
The other two conditions follow by idempotence and distinctness. Therefore
**every finite magma with square fibers of size zero or two has an
FO-definable E3272 operation**, independently of E14 or commutativity.

The Lean theorem `definableOn_of_unique_square_partner` states the equivalent
unique-sibling condition directly. `definableOn_of_split_retraction` is the
general construction, and `exists_idempotent_iterate` proves the finite
self-map fact. These are conditional magma-level results and add no
unconditional arrow to the catalogue. This new argument covers the
commutative ten-point example above despite the failure of periodic-point
closure.

## Testing a proper orbit cover

An equivariant second section is not always available. To investigate that
remaining geometry, let the dihedral group of order `2m` act on its m vertices
and, disjointly, on its regular `2m`-point orbit. The regular orbit maps onto
vertices, but the map has no equivariant section: a vertex reflection fixes a
vertex and fixes no regular point. This is a genuinely different situation
from two identical orbits.

For `m=9`, a bounded finite search found an E14 operation on the resulting
**27-point set** with squaring equal to projection onto the nine vertices. All
square fibers have size three. The same group action also admits an
**idempotent E3272 target**, so it does not furnish a definability obstruction.
Both tables and the two group generators are preserved as
`dihedral_proper_cover_order27` in the research JSON, and the independent
checker verifies both laws and their equivariance. In this example the
periodic image is again not closed: the saved table has `0*2=21`.

The search used the rotation and reflection equations to restrict invariant
operation tables; finding and checking the source took under a second and
finding the target about 1.5 seconds. These tables establish the stated
finite constructions, not a theorem for all proper covers. An exhaustive
small permutation search found no E14 operation on the nine-vertex orbit
alone invariant under this dihedral action, so merely retracting to that orbit
would miss the available target on all 27 points.

For comparison, the same collapsed-diagonal source is impossible for even m:
a reflection fixes exactly two vertices and no regular points. Its fixed-point
set would then be a two-point idempotent E14 submagma, which cannot exist.
This explains the quick negative restricted searches at `m=6,12` without
relying on their UNSAT outputs. The existing `prn8h8b` E3272 obstruction in
`AutSearch.lean` does not help here: its action is regular, so the bijective
squaring argument already rules out an E14 source with that action.
