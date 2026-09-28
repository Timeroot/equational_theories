# E1486: a graph construction and an explicit cofinite spectrum

26 September 2026. The construction and proof below extend Bruno Le Floch's
28 November 2024 construction of order `n² + 2`. This is a new mathematical
argument. The binary graph construction, the cutoff-27 lower bound, and the
shifted-square family are now formalized in Lean. The original
construction and discussion are in the [Zulip archive](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Understanding.20Finite.201486.20Magmas.html).

**Theorem.** Let H be a finite simple graph on n vertices such that every
vertex has a distinct nonneighbor. There is an E1486 magma of order
`n² + 2|E(H)|`. Consequently E1486 has a model at every order at least 63.
This is an existence theorem, not an exact-spectrum classification. The
asymmetric matching extension below improves the cutoff from 63 to 27.

## Construction

Linearly order the vertex set A. For each nonedge ordered pair `(a,b)`,
including loops, take one ordinary point `[a,b]`. For every edge ordered
pair `(a,b)`, take two marked points `[a,b,0]` and `[a,b,1]`. Each undirected
edge therefore adds two points to the ordinary square carrier.

Every point has first and second coordinates. Define its type t in `{0,1}`:

* An ordinary point `[a,b]` has type 1 precisely when `a=b`.
* A marked point `[a,b,e]` has type e if `a<b`, and type `1-e` if `b<a`.

Write `s(a,b,e)` for `[a,b,e]` when `{a,b}` is an edge, and `[a,b]`
otherwise. Choose a nonneighbor `d(a) != a` for each a and put
`r(a,1)=[a,a]`, `r(a,0)=[d(a),a]`. These are ordinary points with
second coordinate a and the stated type.

For points x with second coordinate b and y with first coordinate c,
first set `w=s(b,c,t(x))`. Define:

* If y is ordinary, let `x*y=w`.
* If y is marked `[c,d,e]` and `t(w)=e`, again let `x*y=w`.
* Otherwise let `x*y=r(c,e)`.

## Verification

Three observations give a short proof.

1. Every product `u*v` has second coordinate equal to the first coordinate
   of v. If v is marked with label e, then `t(u*v)=e`.
2. Every square is ordinary. For an ordinary `[a,b]`, its square is `[b,a]`.
   For a marked `[a,b,e]`, the tentative square is `s(b,a,t([a,b,e]))`.
   Its type is `1-e`, since reversing an edge reverses the definition of type.
   Thus the fallback applies, and the square is ordinary. Conversely every
   ordinary point is the square of its reversal.
3. For any ordinary q with first coordinate c, `x*q=s(b,c,t(x))`.

To check E1486, fix x, y, z and set `u=y*x`, `v=x*(z*z)`.
Write x's coordinates as `(a,b)`. By observation 1, u's second coordinate
is a. By observations 2 and 3, `v=s(b,c,t(x))` for some c.
The tentative value of `u*v` is therefore `s(a,b,t(u))`, which equals x:
if x is ordinary it is the only point on its coordinates, and if x is
marked, observation 1 says its label is `t(u)`. Finally, if v is marked,
its label is `t(x)`, so this tentative value has exactly the required type.
There is no fallback in the outer product. Hence

```
(y*x) * (x*(z*z)) = x.
```

## Cardinalities and the bound 63

An edge cover of the complete graph on n vertices uses `ceil(n/2)` edges
when n>=2. Its complement has no universal vertex and has
`floor(n(n-2)/2)` edges. Every subgraph of that complement also has no
universal vertex. Taking arbitrary subsets of its edges gives every order

```
n² + 2m,  0 <= m <= floor(n(n-2)/2).
```

The upper endpoint is `2n²-2n` for even n and `2n²-2n-1` for odd n.
The first useful intervals, with step two, are:

| n | Orders supplied |
|---|---|
| 3 | 9, 11 |
| 4 | 16, 18, 20, 22, 24 |
| 5 | 25, 27, ..., 39 |
| 6 | 36, 38, ..., 60 |
| 7 | 49, 51, ..., 83 |
| 8 | 64, 66, ..., 112 |

For n>=7, the upper endpoint reaches at least `(n+2)²-2`, so successive
intervals of the same parity leave no gaps. This supplies every odd order
at least 49 and every even order at least 64, hence every order at least 63.

## Comparison with E1483

E1483 constrains `(y*x)*(x*(y*z))`, whereas E1486 only constrains the right
input through squares. The construction deliberately makes all marked
points nonsquares. Their columns can therefore be repaired by the fallback
without affecting the inner multiplication by a square. This freedom is
absent from the corresponding E1483 identity. For example, the order-11
case cannot satisfy E1483 according to its separately checked large LRAT
certificate. That 734 MiB bundle is not distributed, and the default Lean
source contains a registered `proofAvailable` `sorry`; it is not a completed
Lean exclusion in the current source build. See the [precise trust status](definability_1483_order_eleven.md).
The graph construction does not supply E1483 models.

## Asymmetric matching expansions: every order at least 27

There is a stronger version using a matching rather than an arbitrary graph.
Give the two directed sides of each matching edge independently `k` and `l`
marked states, where `2 <= k,l <= n-1`. Thus replacing that edge's two
ordinary points contributes `k+l-2` additional points. These state counts
need not be equal.

For a marked point `[a,b,e]` with `a<b`, give it type 1 when `e=1` and
otherwise type 0. For `b<a`, give it type 1 when `e=0` and otherwise type 0.
Every vertex a has at most one matching partner, so there are at least n-1
ordinary points whose second coordinate is a. Assign their types so that
all labels `0,...,k_a-1` occur, where k_a is the number of marked states on
the outgoing directed pair from a (use type 0 when a has no partner).
Choose one such ordinary point as `r(a,e)` for each required label e.

Use the same selection and fallback operation as above. Selection of a
marked state is always defined: all points with second coordinate a have
type less than k_a. Ordinary points have that property by assignment, and
marked points have type 0 or 1, with k_a>=2.

The recovery argument is unchanged. For the square check, the types across
opposite marked pairs interchange labels 0 and 1. Any label at least 2
has type 0, so its tentative square has type 0 or 1 and cannot have the
original label. Therefore every marked square triggers the ordinary
fallback, as required.

For n>=4, one matching edge supplies every increment `2,...,2n-4` over
n². Two disjoint matching edges supply every increment `4,...,4n-8`.
Their union is the entire interval `2,...,4n-8`. Therefore all orders in

```
[n²+2, n²+4n-8]
```

occur. For n>=5 the upper endpoint is at least `(n+1)²+1`, so these
intervals are consecutive or overlap. The first two are `[27,37]` and
`[38,52]`. Hence **every order at least 27 occurs**. The n=4 construction
also supplies every order from 18 through 24; order25 is an ordinary square.

The executable generator [spectrum_1486_matching.py](../scripts/spectrum_1486_matching.py)
checks the defining identity independently and emits compact Lean certificates.
Its factorization check uses only n possible inner-column states, rather than
repeating the same check for all n² ordinary squares. The saved bridge
witnesses have orders 19,23,28,30,32,34,41,43,45,47,62. Together with the
binary graph theorem and pre-existing witnesses, these suffice to formalize
the lower bound with cutoff 27 without formalizing variable state counts.
The general asymmetric construction is proved mathematically above.


## Lean proof and reproducibility

* [Graph.lean](../equational_theories/Spectrum/Equation1486/Graph.lean)
  proves the arbitrary-graph construction by algebraic case splits.
* [GraphCounts.lean](../equational_theories/Spectrum/Equation1486/GraphCounts.lean)
  proves the optimal edge counts, selection of arbitrary numbers of edges,
  and the graph construction's cutoff 63.
* [FiniteBounds.lean](../equational_theories/Spectrum/Equation1486/FiniteBounds.lean)
  combines the graph family with 11 compact certificates. Its public theorems
  `all_large`, `lower_spectrum`, `cofinite`, and `shifted_squares` are complete.

The main lower-bound declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. The finite witnesses are checked by kernel reduction and use
only `propext` and `Quot.sound`. No positive assertion depends on an external
model search, admitted theorem, or native computation axiom.

```sh
python3 scripts/spectrum_1486_matching.py
lake build equational_theories.Spectrum.Equation1486.FiniteBounds
```

The cutoff 27 proof currently retains 11 table certificates totaling about 42 KiB
of Lean source. The full variable-multiplicity matching theorem would eliminate
these tables, but is not required for the checked all-orders lower bound.

## Bounded E1483 comparison

The two saved E1483 examples of orders 8 and 9 satisfy idempotence of all maps
`P_b(t)=a*(t*b)` and preservation of each other's fixed points. This observation
is finite test evidence only. A new bounded Twee pass supplied E1483 together
with its already-proved dual and translation regularity, and sought the general
idempotence identity. It returned `GaveUp` with term-size 24 and critical-pair
depth 6 restrictions. Thus this pass proves no new E1483 rank-divisibility or
spectrum theorem. In particular, the E1485 sharp-edge cardinality argument
cannot yet be reused for E1483.

## Remaining small orders

The completed lower bound leaves only
`2,3,5,6,7,8,10,12,14,15,17,26` as possible exceptions.
Orders 2 and 3 were excluded previously. This pass additionally proves the
exclusions at 5, 6, 7, and 8 by Lean's registered native LRAT checker. These four
negative results use computational axioms explicitly registered in the
spectrum status machinery; the positive lower bound does not depend on them.

A separate compact SAT encoding returned UNSAT at 7 in 3.3 seconds. The first
raw bitvector Lean replay timed out at 180 seconds, but a replay using the
proved two-label normalization succeeded. Order 7 is therefore a completed
Lean exclusion as well.
The initial searches at 8,10,12,14,15,17,26 each reached a 60-second limit.
The order-8 timeout was superseded by the complete exclusion below. Only
**10,12,14,15,17,26 remain unknown**. Additional searches at orders 10 and 12,
using the new rank bound, each reached a 60-second limit in both normalized
cases. See the [saved outcomes](../data/spectrum/1486_search_followup.json).

```sh
python3 scripts/spectrum_1486_exclusions.py
lake build equational_theories.Spectrum.Equation1486.Exclusions
python3 scripts/spectrum_1486_eight.py
```


The existing E1483 exclusions at orders 5 and 6 were audited and are already
complete (`Spectrum.not_order_1483_5` and `Spectrum.not_order_1483_6`). A new
normalized bitvector replay for order 7 reached its 180-second solver cap without
a certificate, so its previous `proofAvailable` status is unchanged. No new
admitted assertion was added. Exact inputs and logs for this comparison are
in the [small research archive](../data/spectrum/1486_followup_sources.tar.gz).

Subsequent E1483 work supersedes that order-seven status: a nine-case
normalized LRAT replay now proves `Spectrum.not_order_1483_7` completely in
Lean. The same pass excludes order ten and characterizes the constant-row
subclass; see the [E1483 follow-up](1483_spectrum_progress.md).

For the remaining E1486 order 26, a uniform two-fold lift of the known 13-point
model is impossible: a fiber over any idempotent would be a forbidden
2-element subalgebra. Three nonuniform alternatives gave the three idempotent
fibers sizes 4,1,1 in turn, and every other fiber size 2, totaling 26. All three
restricted encodings returned UNSAT quickly. These are solver reports only,
and they do not imply that every 26-element model is impossible.


## A square-row bound and the exclusion of order 8

For an E1486 magma write `R(x)={x*(z*z) : z in G}`. The defining law implies

```
x * ((x*(y*y))*(z*z)) = x*(y*y).
```

Indeed, the law first gives `(x*x)*(x*(y*y))=x`; apply it again with
middle variable `x*(y*y)` and left variable `x*x`. Consequently, if
`a,b in R(x)` are distinct then `R(a)` and `R(b)` are disjoint: any shared
value u would satisfy both `x*u=a` and `x*u=b`.

In a finite nonempty magma, choose x with minimum square-row size r. The r
disjoint sets `R(a)` for `a in R(x)` each contain at least r points. Thus
**r² <= |G|**. Moreover, every square lies in their union, since
`(x*(z*z))*((z*z)*(z*z))=z*z`. All these facts are proved in
[SquareRows.lean](../equational_theories/Spectrum/Equation1486/SquareRows.lean).

At order 8 the minimum row has size at most 2. Relabel its vertex as 0.
Relabeling its image, while fixing 0, puts that image in either `{0,1}`
or `{1,2}`. The complete permutation argument is in
[EightNormalization.lean](../equational_theories/Spectrum/Equation1486/EightNormalization.lean).
The two remaining finite cases are refuted by Lean's native LRAT checker in
[EightRefutation.lean](../equational_theories/Spectrum/Equation1486/EightRefutation.lean).
The public theorem is `Spectrum.not_order_1486_8` in
[Exclusion8.lean](../equational_theories/Spectrum/Equation1486/Exclusion8.lean).
The algebra and normalization use only the standard logical axioms; the final
finite checks have registered computational axioms, like the other small
exclusions. Both parts are complete Lean proofs.

The independent compact SAT encoding originally split into four cases:
minimum rank 1 or 2, with or without 0 in its image. All four were UNSAT,
taking at most 1.3 seconds each. The simpler two-case encoding also refuted
each case in under a second. Exact inputs and logs are preserved in the
[order-8 research archive](../data/spectrum/1486_order8_sources.tar.gz).
These external solver runs motivated the Lean proof and are not its axioms.

## A singleton square-row forces triviality

This restriction holds for infinite magmas too. Suppose `a*(z*z)=b` for every z.
Repeated use of E1486 gives the following identities, in order:

```
b*((u*u)*(v*v)) = u*u,
(u*b)*(v*v) = b,
b*(u*u) = b,
u*u = b,
b = a.
```

For the third identity, replace b in `b*(u*u)` by
`a*((b*b)*(b*b))`, use the second identity to replace `(b*b)*(b*b)` by b,
and apply the second identity again. The fourth follows from the first and
third; substituting the constant square map into E1486 gives the fifth.
Now all squares equal a and `(u*v)*(v*a)=v`. Setting v=a shows
`(u*a)*a=a`; setting both variables to `u*a` then gives `u*a=a`.
Thus `(u*v)*(v*a)=v` reduces to `a=v`, proving triviality.

This is formalized as `eq_of_singleton_row`, `two_le_row_card`, and `four_le_card` in
[SingletonRow.lean](../equational_theories/Spectrum/Equation1486/SingletonRow.lean).
The equality theorem uses no axioms at all: only ordinary equational reasoning.
The finite cardinality corollaries use the standard logical axioms.
Together with the rank bound it explains why every nontrivial finite E1486
model has order at least 4. E1483 differs already here: its two-element NAND
model has a constant full row `0*y=1`. The E1483 catalogue now explicitly
includes the previously known squares and twice-squares construction; this
exposure of an existing result does not constitute a new general E1483 theorem.
