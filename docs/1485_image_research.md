# Finite mixed projections: strict degree decrease and a counting limitation

Research note, 18 September 2026. This proves that a mixed projection
strictly decreases degree whenever it moves a point of its associated
row. It also records a finite counterexample to a different counting
shortcut in the image-intersection problem from
[the graph research note](1485_graph_research.md). Neither result
establishes intersection closure or the finite spectrum conjecture.

## Fixed-parameter counts and strict degree decrease

Let `M` be a nonempty finite E1485 magma of order `n`. Use the established
facts that row and column cardinalities agree at every element, denoting
their common value by `d(x)`, and that every nonempty fiber of either
translation at `x` has size `n/d(x)`.

Fix `a`, write `P_b(t)=a*(t*b)`, and take `u∈Row(a)`. Define

\[
 F_a(u)=\{b\in M:P_b(u)=u\}.
\]

The weak central law and its dual give the equivalence

\[
 P_b(u)=u\quad\Longleftrightarrow\quad(b*a)*u=a.
 \tag{1}
\]

For the forward implication use `(b*a)*P_b(u)=a`. For the reverse
implication use `((b*a)*u)*(u*b)=u`.

Since `a→u`, the fiber `R_u^{-1}(a)` is nonempty. Every element `x` of
this fiber satisfies `x*u=a`, so the good path `x→a→u` shows that
`x∈Col(a)`. Thus (1) expresses `F_a(u)` as the inverse image under `R_a`
of the whole nonempty fiber `R_u^{-1}(a)`. The latter has `n/d(u)`
elements, each with `n/d(a)` inverse images under `R_a`. Consequently

\[
 \boxed{|F_a(u)|=\frac{n^2}{d(a)d(u)}.} \tag{2}
\]

Now let `v=P_c(u)`. The band identity `P_bP_cP_b=P_cP_b` implies

\[
 b\in F_a(u)\quad\Longrightarrow\quad
 P_b(v)=P_bP_cP_b(u)=P_cP_b(u)=v.
\]

Hence `F_a(u)⊆F_a(v)`. If `v≠u`, then `c∉F_a(u)`, while
idempotence `P_c²=P_c` gives `c∈F_a(v)`. In that case the inclusion is
strict. Applying the exact finite counts (2) proves

\[
 \boxed{
 d(P_c(u))\le d(u),\qquad
 P_c(u)\ne u\ \Longrightarrow\ d(P_c(u))<d(u)
 \quad (u\in\operatorname{Row}(a)).
 } \tag{3}
\]

In particular, equality of the two degrees forces `P_c(u)=u`. This is
a finite theorem: it uses the proved uniform-fiber counts, and its
strict inequality is not justified by an infinite-cardinality argument.

The same statement holds for any word `T` of the generators. Apply (3)
successively; all intermediate points remain in `Row(a)`. Thus

\[
 F_a(u)\subseteq F_a(T(u)),\qquad
 T(u)\ne u\ \Longrightarrow\ d(T(u))<d(u). \tag{4}
\]

There is therefore a partial order on `Row(a)`: put `u≼v` if a word of
generators, possibly empty, sends `u` to `v`. Reflexivity and transitivity
are immediate, and antisymmetry follows from strict degree decrease.
Every strict chain has strictly decreasing degrees. Since degrees divide
`n`, the number of strict steps is less than the number of distinct
degree values occurring in `Row(a)`.

The maximal elements of this order are precisely the common fixed
points `K(a)`, or sharp successors of `a`. By the established sharp-edge
criterion they all have degree `n/d(a)`. This does not show that there
are `r=min_x d(x)` such maximal elements: a projection can still merge
several higher-degree points into one lower-degree point. In particular,
(3) and (4) alone do not prove image-intersection closure or rule out a
rank drop below `r` in a product of generators.

This limitation persists even if one retains the precise local count
(2) and a uniform generator of minimum rank. As an abstract example on
`{0,...,5}`, define

```text
E = (0,1,2,1,2,2),
P = (0,0,2,0,2,2),
Q = (0,1,0,1,0,0),
```

and take six indexed generators `E,E,P,P,Q,Q`. These transformations
are commuting idempotents, so satisfy both band identities. Their ranks
are three, two, and two; `P` has two fibers of size three; and their
common fixed set is `{0}`. Their generated semigroup contains the
constant-zero map `PQ`, whose image is not a generator image.

Put `Row={0,1,2}`, `n=6`, `d(a)=3`, and assign the three row points
degrees `d(0)=2`, `d(1)=d(2)=3`. Their numbers of fixed generator indices
are respectively six, four, and four, exactly `n²/(d(a)d(u))`. Every
nontrivial move strictly decreases the assigned degree. This is not an
E1485 magma: it shows that the newly proved constraints at a single
fixed `a` still permit rank drop. Further relations between the
different fixed-left families are needed for a general proof.

## Central coordinates need not have uniform reverse fibers

Let `h` be central, let `r` be the minimum degree, and put `n=rs`.
The graph note proves that `L_a R_h` has rank `r` and uniform fibers of
size `s`. Its reversed composite `R_h L_a` also has rank `r`, and indeed

\[
\operatorname{im}(R_hL_a)=\operatorname{Col}(h).
\]

The inclusion into `Col(h)` is immediate. For `v=x*h`, centrality in
its right-hand form gives `(a*v)*h=v`, proving the reverse inclusion.
Nevertheless, **the fibers of `R_h L_a` need not be uniform**.

Consider the following order-eight table, number 2 with zero-based
indexing in Kevin M's `n8_unique.txt` archive:

```text
1 0 0 1 2 2 3 3
0 0 0 0 3 3 3 3
4 4 4 5 5 4 5 5
6 4 4 6 7 7 5 5
1 0 0 1 2 2 5 5
6 4 4 6 7 7 3 3
0 0 0 0 3 3 3 3
4 4 4 5 5 4 5 5
```

Here the elements are numbered `0,...,7`. Direct substitution verifies
all 512 instances of E1485. The degree vector is
`(4,2,2,4,4,4,2,2)`, and `h=6` is central; its 64 centrality instances
also check directly. For `a=4`, the two transformations, listed in input
order, are

```text
L_4 R_6 = (1,1,2,2,2,1,1,2),
R_6 L_4 = (3,3,3,3,5,5,3,3).
```

Thus the first has fibers of size four and four, whereas the second has
fibers of size six and two. Both have rank two.

There is an equivalent partition formulation. Centrality implies that
the sets `Col(v)`, for `v∈Col(h)`, partition the whole magma: they are
the fibers `R_h^{-1}(v)` of size `s`. In the example,

\[
\operatorname{Col}(6)=\{3,5\},\qquad
\operatorname{Row}(4)=\{0,1,2,5\},
\]

and

\[
\operatorname{Row}(4)\cap\operatorname{Col}(3)=\{0,1,5\},\qquad
\operatorname{Row}(4)\cap\operatorname{Col}(5)=\{2\}.
\]

An arbitrary row therefore need not meet these equal-sized central
coordinate blocks in equal-sized parts. Any counting proof of image
intersection closure that requires this extra uniformity needs a
different argument.

One valid count survives. If `P_b=L_aR_b` and a product of generators
has `P_h` as its rightmost factor, every nonempty fiber of that product
has cardinality a positive multiple of `s`. Indeed, `P_h` first partitions
the domain into `r` fibers of size `s`, and the remaining factors can
only merge those fibers. The band identities also ensure that the image
stays inside `im(P_h)`. This fact permits rank drops; it supplies no
lower bound of `r` on the final rank.
