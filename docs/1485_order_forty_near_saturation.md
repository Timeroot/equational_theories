# Order forty: fifteen degree-five vertices are impossible

Research note, 19 September 2026. In the order-forty branch with
minimum degree and central count both four and least noncentral
degree five, write `Z,A,B,T` for the degree classes `4,5,8,10`.
**The case `|A|=15, |B|=5` is impossible.** This is an analytic
research proof, not yet a Lean theorem. No finite enumeration is used.

Together with the
[saturated-profile reduction](1485_order_forty_saturated_profiles.md)
and [single-coset exclusion](1485_order_forty_single_coset.md), it improves
the bounds in the [large degree-five class analysis](1485_min_four_large_five_class.md)
to

\[
10\le |A|\le14,\qquad 6\le|B|\le10.
\]

This does not exclude the other central-incidence branches of order
forty or prove the full spectrum conjecture.

**Subsequent improvement:** the [universal return-matching proof](1485_order_forty_fourteen_exclusion.md)
now excludes fourteen as well, entirely analytically. The subsequent
[thirteen-vertex obstruction](1485_order_forty_thirteen_directions.md)
excludes thirteen with the stated finite incidence dependencies. The current
bounds are `10≤|A|≤12` and `8≤|B|≤10`. The fourteen-vertex incidence
and affine-profile reductions retained below describe the earlier route;
their finite check is no longer needed for that exclusion.

## A top-return pair has small combined sharp degree

Let `j_b` be the number of sharp predecessors or successors of
`b∈B`. These counts agree by weighted balance. Every `A` vertex has
one sharp `B` predecessor and successor, so

\[
1\le j_b\le4,\qquad\sum_{b\in B}j_b=|A|.
\]

Every vertex has four top neighbors in each direction. The internal
ordinary `B` graph therefore has both in- and out-degree `4−j_b`
at `b`. There are no ordinary `A→A` edges, since `5²<40`.

If `b,d∈B` and `e=b*d∈T`, the good-return fiber matching gives

\[
j_b+j_d\le4. \tag{1}
\]

For completeness, set `X=L_e⁻¹(d)` and `Y=R_e⁻¹(b)`. Both fibers
have size `40/10=4`. E1485 and its dual show that

\[
x\longmapsto x*b
\]

is a bijection `X→Y`, with inverse `y↦d*y`; each matched pair is
an ordinary edge. The set `X` contains the `j_d` sharp `A`
successors of `d`, and `Y` contains the `j_b` sharp `A`
predecessors of `b`. The matching cannot pair an `A` vertex with
another `A` vertex. Hence their two counts sum to at most four.
This is the same argument used for
[order forty-eight](1485_order_forty_eight_min_four.md#6-good-returns-exclude-equality).

## Excluding the fifteen/five split

Suppose `|A|=15` and `|B|=5`.

If `j_b=4`, the vertex `b` has no ordinary neighbors inside `B`.
Its ordinary two-step paths to `B`, with middle in `A∪B`, can
therefore only pass through its four sharp `A` successors. Each
of these has just one `B` successor, giving at most four possible
endpoints. There are five endpoints in `B`, so for some `d∈B`
there is no such middle. A central middle is impossible as well.
Consequently the good middle `b*d` must be top. But (1) gives
`4+j_d≤4`, contradicting `j_d≥1`.

Thus every `j_b≤3`. Since their sum is fifteen over five vertices,
every sharp count is exactly three. Every `B` vertex then has one
ordinary successor inside `B`. Fix `b∈B` again. Its two-step paths
to `B`, through `A∪B`, number at most

\[
3\cdot1+1\cdot1=4.
\]

The first term counts the three sharp `A` successors, the second
the one internal `B` successor and its own one internal successor.
Again some `d∈B` has a top good middle `b*d`; now (1) would give
`3+3≤4`. This contradiction excludes the split.

## Fourteen degree-five vertices: a finite reduction, not an exclusion

Now suppose `|A|=14`, so `|B|=6`. The same argument excludes any
`j_b=4`, since four two-step endpoints cannot cover six targets.
Let `n_i` count the vertices of sharp degree `i`. Then

\[
n_1+n_2+n_3=6,\qquad n_1+2n_2+3n_3=14,
\qquad n_3-n_1=2.
\]

If `n_1=0`, every sharp-degree-three vertex has at most
`3+2=5` two-step endpoints in `B`: its one internal `B` successor
has internal degree at most two. A top-return partner exists but
would have sharp degree at least two, contradicting (1). Thus only

\[
(n_1,n_2,n_3)=(1,2,3)\quad\hbox{or}\quad(2,0,4) \tag{2}
\]

can occur.

The following check **excludes the first distribution**, and reduces
the second to **three internal incidence types**. These remaining
types are not asserted to be realizable magmas. The fourteen/six
split is not excluded by this check alone; it is now excluded by
the later analytic argument linked above.

```sh
python3 scripts/1485_n40_fourteen_internal_check.py
```

The [standalone check](../scripts/1485_n40_fourteen_internal_check.py)
takes about **0.23 seconds** locally. Its mathematical inputs and
exhaustiveness are as follows.

### Two six-by-six matrices

Let `D` be ordinary adjacency inside `B`, with in- and out-degree
`4−j_i`. Let `C_ij=1` when there is a sharp two-edge path
`b_i⇒a⇒b_j`. Such a middle is unique. Thus `C` is binary with
row and column sums `j_i`, and its fourteen ones index the actual
vertices of `A`.

For `B` endpoint pairs, strict degree descent gives:

* If `(D²)_ij≥2`, then `C_ij=1`: two different degree-eight middles
  cannot include a good one, so their good replacement is in `A`.
* If `(D²)_ij=0` and `C_ij=0`, then `b_i*b_j` is top. By (1),
  this is possible only if `j_i+j_j≤4`.

These conditions specify some mandatory ones of `C`. The script
enumerates every binary `D` of the required row and column sums,
then every completion of the mandatory ones to the required row
and column sums of `C`. Loops are allowed throughout.

### Five-cycle conditions

Every ordinary two-edge path in `A∪B` that meets `A` is good,
because it contains a sharp edge. A path entirely in `B` is bad
exactly when its endpoint pair is marked by `C`.

On a directed five-cycle with one `A` vertex, only two consecutive
positions could be bad. The universal five-cycle rule excludes an
isolated bad position, so those two statuses agree. In matrix terms,
for every internal path `a→b→c→d` with `C_da=1`,

\[
C_{ac}=C_{bd}. \tag{3}
\]

On an all-`B` five-cycle, the allowed bad-position sets are empty,
two consecutive positions, or all five. Here is why the stronger
statement follows in this setting. The universal rule excludes
isolated bad positions. If an adjacent mixed pair had a bad opposite
return, the good return middle could not be top, because an ordinary
degree-eight return middle already exists. If it lay in `A`, the
three closure paths meeting that sharp middle would be good and
would force the mixed pair to have equal statuses. Thus the good
return is in `B`, where equality of degrees forces the original
return middle to be good, a contradiction. This rules out blocks of
three and four bad positions. This is the same local argument as in
the [four-degree cycle lemma](1485_four_degree_regular_gap.md);
it needs neither a full central core nor sharp regularity here.

The script checks (3) and all all-`B` five-cycles. Cycles may have
repeated vertices. Five-cycles with two `A` vertices have all their
two-edge paths good and impose no additional condition.

### Enumeration results and the three remaining types

| Sharp-degree list | Internal `D` graphs | Completed pairs `(D,C)` | Pairs surviving five-cycle tests |
| --- | ---: | ---: | ---: |
| `(1,2,2,3,3,3)` | 3,358 | 24 | 0 |
| `(1,1,3,3,3,3)` | 1,032 | 336 | 48 |

The 48 remaining labeled pairs have four isomorphism types. The
script quotients by all relabelings preserving sharp degree, namely
`S₂×S₄`; it makes no additional unproved symmetry assumption.

Label the low-sharp vertices `0,1` and the others `2,3,4,5`. All
four types have `C_00=C_11=1`, no other `C` entries involving `0,1`,
and their high block is `J₄` minus a permutation matrix. The low
internal successor sets are always

\[
D(0)=\{1,2,3\},\qquad D(1)=\{0,4,5\}.
\]

| Type | `D(2),D(3),D(4),D(5)` | Omitted columns of high `C` rows `2,3,4,5` | Labeled count |
| --- | --- | --- | ---: |
| I | `{0},{0},{1},{1}` | `3,2,5,4` | 6 |
| II | `{0},{0},{1},{1}` | `3,2,4,5` | 12 |
| III | `{0},{0},{1},{1}` | `2,3,4,5` | 6 |
| IV | `{0},{1},{0},{1}` | `2,4,3,5` | 24 |

Type IV is ruled out by the return matching, without another
enumeration. Its reverse product `b_4*b_0` is top, and
`j_4+j_0=3+1=4`. The size-four return matching therefore has
exactly one `A` endpoint in every matched edge. But

\[
b_0\longrightarrow b_3\longrightarrow b_1\longrightarrow b_4
\]

is a good-good path entirely in `B`: `C_01=C_34=0`. Closing it
by its good top return places its middle `B→B` edge in that
matching, a contradiction.

For completeness the script also checks the corresponding general
necessary bound: at a top-return pair `b_d*b_a`, the number of
good-good three-edge paths entirely in `B` from `a` to `d` is at
most `4−j_a−j_d`. This excludes exactly the 24 labeled Type-IV
pairs and leaves Types I–III.

Thus any hypothetical fourteen/six model must have sharp degrees
`(1,1,3,3,3,3)` and one of the three aligned internal types above.
No multiplication operation has been constructed for these types,
and no exclusion of them is claimed here.

## Affine profiles of the remaining sharp-degree-three B vertices

There is a further analytic reduction for the three surviving types.
Here "high-sharp" means the four vertices of `B` having `j=3`,
not the top class `T`.

By the [large-class profile theorem](1485_min_four_large_five_class.md),
at least one of the two `A` profile families is a single `V₄` coset.
Reverse the operation if necessary so it is the predecessor family,
and denote its four lines by `P_p`. The successor profiles belong to
the other one or two cosets of the same permutation parity.

Each high-sharp `B` vertex has three sharp `A` predecessors with
three distinct `P` profiles. Its three sharp `A` successors have
three distinct successor profiles in a single coset, because those
profiles are pairwise disjoint. All of these `A` vertices have both
sharp endpoints among the four high-sharp vertices, since their
sharp-path matrix is `J₄` minus a permutation matrix.

There are no ordinary edges between high-sharp `B` vertices in any
of the three remaining types. Thus every product of a high-sharp
`B` vertex and one of these twelve `A` vertices, in either order,
has a unique top middle: a `B` middle would require such a missing
internal edge, and there are no ordinary `A→A` edges.

Consequently every high-sharp `B` top-successor set meets each
`P` profile occurring among those twelve `A` vertices exactly once.
At least three different profiles occur, because a sharp-predecessor
triple already supplies three. These three exact singleton
intersections force the fourth intersection to be a singleton too:
the fourth point cannot lie on any of the three already-counted
lines. Hence every such `B` top-successor set is a transversal of
the entire `P` family.

Identify the common central alphabet with `F₂²` and write
`P_p: C=M H+p`. A top-successor set has distinct central successor
labels by centrality, so its function

\[
\phi_b(p)=C\bigl(\operatorname{TopSucc}(b)\cap P_p\bigr)
\]

is a permutation of four points, hence affine over `F₂`. Thus these
four high-sharp successor profiles have an affine description.
Their offsets and slopes need **not** be the same; their sets have
not been proved disjoint.

Dually, if a successor-profile coset occurs among the twelve `A`
vertices, it occurs in some high-sharp row, which supplies three
distinct lines. Every high-sharp `B` top-predecessor set meets all
three exactly once and therefore meets the fourth exactly once.
So it is a transversal of each whole coset that occurs there.

In particular, if both possible successor-profile cosets occur
among these twelve vertices, the high-sharp predecessor profiles
have a particularly restricted form. Write the other slopes as
`MΩ` and `MΩ²`, where `Ω` has order three. Centrality makes a
predecessor set a graph `C=f(H)`. Its parameter on an `MΩ` line
is `f(H)+MΩH`, a permutation, so `f(H)=D H+c` is affine.
Transversality to both cosets says

\[
M^{-1}D+\Omega\quad\hbox{and}\quad M^{-1}D+\Omega^2
\quad\hbox{are invertible}.
\]

These two conditions force `M⁻¹D` to be either `0` or `I`.
One small verification is to put `F=M⁻¹D+Ω∈GL₂(F₂)`; the other
condition is that `F+I` be invertible. Of the six matrices in
`GL₂(F₂)`, precisely the two order-three matrices have this
property. Thus `D=0` or `D=M`. Each high-sharp predecessor set is
therefore an entire central-successor column or one of the `P`
lines.

This affine reduction supplies finite parameters for further work;
it is not an exclusion of the three remaining types.

## Two-point intersections at the remaining low-sharp vertices

There is also an exact restriction on the profiles not covered by
the affine lemma. Let `b` be high-sharp and let `l` be its unique
internal `B` successor. In the three aligned types, `l` is also
its unique internal predecessor. Let `l'` be the other low-sharp
vertex. Among the non-top elements of `Row(l)`, exactly three
belong to `L_b⁻¹(l)`:

* the unique `A` vertex on the sharp loop at `l`;
* `l'`;
* the high-sharp vertex omitted by the row of `C` at `b`.

The first gives a sharp good path. For the other two, the unique
internal middle is `l` and there is no sharp `A` replacement.
The other high-sharp neighbor of `l` instead gives an `A` product.
Since this fiber has size `40/8=5`, it has exactly two top inputs.

The three sharp `A` successors of `b` have three distinct successor
lines in one coset. Every point on these lines gives an `A` product
under `L_b`, so the two top inputs in the `l` fiber lie on the
fourth, missing line. Conversely a point of `TopSucc(l)` on that
line has middle `l` and cannot have a lower-degree replacement:
all possible `A` replacements are precisely the three excluded
sharp successors. Thus

\[
\boxed{|\operatorname{TopSucc}(l)\cap
\text{missing successor line at }b|=2.}
\]

Dually, `TopPred(l)` meets the missing predecessor `P` line of
the three sharp `A` predecessors of `b` in exactly two points.
Each low-sharp vertex has two attached high-sharp vertices, so its
profiles must satisfy both of their two-point conditions. These
are proved necessary conditions. The later
[fourteen/six exclusion](1485_order_forty_fourteen_exclusion.md)
shows that they cannot extend to a model; its shortest proof uses
universal return matching rather than these affine profiles.
