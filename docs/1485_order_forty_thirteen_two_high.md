# Order forty: the thirteen-vertex class cannot have two high-sharp partners

Research note, 19 September 2026. This page gives a **finite-assisted
exclusion** of the sharp-degree distribution `(1,1,1,2,2,3,3)`
in the thirteen/seven branch at order forty. The mathematical reduction
is analytic; a short standard-Python program exhausts two seven-point
binary incidence matrices. It does not search forty-point multiplication
tables, call a SAT solver, or rely on an unpublished certificate.
This is not yet a Lean theorem.

Together with the separate
[analytic three-high-sharp exclusion](1485_order_forty_thirteen_three_high.md),
this initially left only zero or one sharp-degree-three partner.
The [one-high-sharp companion check](1485_order_forty_thirteen_one_high.md)
now excludes one as well. The last distribution is excluded by the
[final profile argument](1485_order_forty_thirteen_directions.md),
completing the thirteen/seven branch. This page supplies only the
two-high-sharp component, not that entire proof.

## Incidence data and necessary constraints

Use the degree classes `Z,A,B,T` of degrees `4,5,8,10` and
sizes `4,13,7,16`. Label the seven vertices of `B` so their
balanced sharp degrees are

\[
j=(1,1,1,2,2,3,3).
\]

Let `D` be ordinary adjacency inside `B`, and let `C_bd=1`
mean that a sharp path `b⇒a⇒d` passes through `A`. Every
member of `A` has exactly one sharp predecessor and successor.
Distinct sharp middles cannot share an endpoint pair, so `C` is
binary. Both row and column sums are

\[
\deg_D(b)=4-j_b,\qquad \deg_C(b)=j_b.                     \tag{1}
\]

The checker uses the following necessary conditions only.

### Multiple internal middles and the degree of a return

If `(D²)_bd≥2`, their equal degrees mean neither can be good.
The good replacement is in `A`, so `C_bd=1`. If `C_bd=0`,
there is at most one internal middle. With one middle the product
lies in `B`; with none it lies in `T`. There can be no central
middle for these endpoint degrees.

The [universal return-matching bound](1485_general_return_matching.md)
for the independent set `A` gives

\[
j_b+j_d\le40/d(b*d).
\]

Thus `j_b+j_d>5` forces `C_bd=1`, whether or not an internal
middle exists. If `(D²)_bd=0` and `j_b+j_d>4`, it again
forces `C_bd=1`. These are the three rules for initially forced
entries of `C`.

### Bad-extension balance on an internal edge

For each `D_bd=1`, use

\[
\sum_x D_{dx}C_{bx}=\sum_y D_{yb}C_{yd}.                  \tag{2}
\]

The two sides count bad extensions and bad predecessors of that
edge. Their equality is proved without any finite enumeration in
[the return-matching note](1485_general_return_matching.md#5-bad-extension-balance-on-every-internal-edge).

### A five-walk with one degree-five vertex

If

\[
D_{ab}D_{bc}D_{cd}C_{da}=1,
\]

then

\[
C_{ac}=C_{bd}.                                           \tag{3}
\]

Indeed append the unique sharp middle on `d⇒A⇒a` to obtain
an ordinary closed five-walk. Three of its two-step positions touch
a sharp edge and are good. Its only possibly bad positions are
the consecutive internal paths `a→b→c` and `b→c→d`.
Exactly one bad position is forbidden by E1485 five-cycle goodness,
which proves (3). The checker allows repeated vertices throughout.

### Count the good-good three-paths at every return

Let

\[
g(d,b)=\#\{(x,y)\in B^2:
D_{dx}D_{xy}D_{yb}=1, C_{dy}=C_{xb}=0\}.
\]

The two successive two-paths in each counted path are good. In
the return matching for `e=b*d`, these are exactly the matched
edges whose two endpoints lie in `B`. The `j_d` sharp successors
of `d` and `j_b` sharp predecessors of `b` account for distinct
matched edges meeting the independent set `A`. Therefore

\[
\boxed{g(d,b)\le f(b,d)-j_b-j_d,}                        \tag{4}
\]

where the fiber size is determined entirely by `C,D`:

\[
f(b,d)=
\begin{cases}
8,&C_{bd}=1,\\
5,&C_{bd}=0\text{ and }(D^2)_{bd}=1,\\
4,&C_{bd}=0\text{ and }(D^2)_{bd}=0.
\end{cases}
\]

In particular the equality case at a high/medium `B` return has
zero budget for such all-`B` paths. Equation (4) applies equally
to top, degree-eight and degree-five returns; it is not restricted
to top-valued products.

## Complete finite check

Run

```sh
python3 scripts/1485_n40_thirteen_two_high_check.py
```

The [checker](../scripts/1485_n40_thirteen_two_high_check.py) first
enumerates every binary `D` with the row and column sums (1).
Rows are chosen as subsets; the remaining column capacities give
only elementary pruning. For each `D`, it inserts all forced
`C` entries, then completes all remaining rows subject to the
specified row and column sums. Thus no isomorphism assumption or
unproved normal form is used in the exclusion.

The exact counts, asserted by the program, are:

| Stage | Number remaining |
| --- | ---: |
| Internal matrices `D` with the prescribed margins | 488,266 |
| Internal matrices whose forced `C` entries fit the margins | 984 |
| Completed pairs `(D,C)` | 1,512 |
| After edge balance (2) | 336 |
| After one-`A` five-walk closure (3) | 48 |
| After the return-path budgets (4) | **0** |

All arithmetic is exact. The program additionally groups the last
48 pairs up to relabeling within sharp-degree classes and prints a
representative and an explicit violating return-path collection for
each type. That grouping is for explanation only: all 48 labeled
pairs are individually checked in (4).

There are two types, each with 24 labelings. In the canonical labels
printed by the program, their respective obstructions are

* a top return `5*2`, with zero budget but good-good path
  `2→0→2→5`;
* a top return `5*0`, with zero budget but good-good path
  `0→4→1→5`.

Thus even the top-return part of (4) already rejects the final two
types. The complete run took about **30.8 seconds** in this workspace.

The zero final count proves the claimed subcase exclusion, conditional
only on the analytic necessary conditions above. It makes no assertion
about the other sharp-degree distributions.
