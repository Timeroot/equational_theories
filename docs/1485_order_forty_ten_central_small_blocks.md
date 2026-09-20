# Order forty with ten central elements: three top counts are excluded

Research note, 20 September 2026. The results here are analytic and have
been independently audited. They use no enumeration, SAT premise, or
Lean declaration. These are intermediate reductions; the subsequent
[ten-central theorem](1485_order_forty_ten_central_exclusion.md) excludes
the entire branch analytically using the bound proved here.

Assume a finite E1485 magma has order forty, minimum degree four, and
central class `Z` of size ten. Write `T` for its top class, `h=|T|`,
and `P_t,C_t` for a top's central predecessor and successor blocks.
The degree classes are `4,5,8,10`, and the first noncentral top-output
degree is five. This follows from the
[order-forty reduction](1485_order_forty_four_central_exclusion.md#4-precisely-what-remains-at-order-forty).

**Theorem.** Every central block has size at most three, and

\[
\boxed{|T|\in\{17,18\}.}
\]

These two values remain possibilities under this theorem, not asserted
models. The subsequent [unified exclusion](1485_order_forty_ten_central_exclusion.md)
eliminates both values analytically. The
[full-block theorem](1485_order_forty_ten_central_full_blocks.md)
now excludes the size-four-block case: it would force four top neighbors
everywhere, which permits at most six central elements at order forty.
The rest of this proof therefore works with blocks of size at most three.

## 1. The initial interval is sixteen through twenty

Every vertex's top predecessors have `P`-blocks partitioning the ten
central labels, and its top successors have `C`-blocks doing likewise.
With block sizes at most three, each of these top counts is at least
four. A central row has four tops, whose numbers of top successors
sum to `h` by `BD=J`. Therefore `h≥16`.

Put `e_t=3−|P_t|` and `f_t=3−|C_t|`, both in `{0,1,2}`.
The central incidence moments give

\[
\sum e_t=\sum f_t=3h-40,\qquad
\sum e_tf_t=9h-140.
\tag{1}
\]

Since `e_tf_t≤2e_t`, we get `h≤20`. Each central partition
into four blocks is necessarily `3+3+3+1` or `3+3+2+2`.
This pointwise restriction is stronger than the moment equations.

## 2. Uniform top neighborhoods exclude sixteen tops

Suppose `h=16`. The sum, over all forty vertices, of their top-successor
counts is `10h=160`, since each top has ten ordinary predecessors.
Each summand is at least four, so every vertex has exactly four top
successors. The dual argument gives four top predecessors everywhere.
The [global good-pair bound](1485_order_forty_uniform_top_counts.md)
then forces at most six central elements, contrary to `m=10`.

This replaces the earlier, longer argument through individual auxiliary
membership counts. It needs only the global count of bad internal paths,
not equality of predecessor and extension counts on each internal edge.

## 3. Nineteen tops contradict central partitions alone

Suppose `h=19`. Equation (1) gives sums seventeen and product sum
thirty-one, hence

\[
\sum e_t(2-f_t)=\sum f_t(2-e_t)=3.
\tag{6}
\]

Types `(e,f)=(2,0),(0,2)` are impossible because they contribute
four to one sum. Only `(1,1)` contributes an odd amount, so its
multiplicity is one or three.

If it is three, those entries exhaust both sums. The remaining types
are `(0,0),(2,2)`, giving nine tops with blocks `(3,3)`, seven
with `(1,1)`, and three with `(2,2)`. In every central row there
are either zero or two double successor blocks. Consequently the
three two-element `P`-sets of the double/double tops form a loopless
multigraph whose nonzero vertex degrees are all two. With three edges
this is a triangle: a parallel pair would leave a single edge with
degree-one endpoints. The dual argument makes their three `C`-sets
a triangle too. Any two of these tops therefore have intersecting
`P`-sets and intersecting `C`-sets, so their central rectangles
overlap. This is impossible.

If the multiplicity of `(1,1)` is one, the remaining contributions
in (6) force one type from `{(1,0),(2,1)}` and one from
`{(0,1),(1,2)}`. Their total `e` sum must be odd, since the
remaining `(2,2)` types contribute even sums to seventeen.
This leaves only two dual possibilities. In one, the three exceptional
tops all have `P` size two and respective `C` sizes one, two, three;
the others have blocks `(1,1)` or `(3,3)`. There is exactly one
top with a double `C`-block. A central row containing it would have
exactly one double block, contrary to the only possible partitions
`3331` and `3322`. The dual case fails in a central column.

Thus `h=19` is excluded without any degree-five profile argument.

## 4. Twenty tops force a forbidden central-column profile

Suppose `h=20`. Equation (1) gives sums twenty and product sum forty.
Equality in `ef≤2e` and its dual forces `e=f∈{0,2}` at every
top. There are ten unit/unit tops and ten triple/triple tops.

Each central row and column contains exactly one unit top, since
its four block sizes must be `1,3,3,3`. Write these tops as
`u_x`, with `P_(u_x)={x}`, `C_(u_x)={π(x)}`, where `π` is a
permutation of the central labels. The permutation is not assumed
to be the identity.

Let `B',C'` be the two central incidence matrices restricted to the
ten triple/triple tops. The central rectangle partition says

\[
B'C'=J-Q,
\tag{7}
\]

where `Q` is the permutation matrix of `π`. This matrix is invertible
over the rationals: multiplication by `Q^{-1}` gives `J-I`, whose
eigenvalues are nine and minus one. In particular `B'` is invertible.

Choose a degree-five element, which exists. Its top-profile size is
four since `10>3²`. Its predecessor `P`-partition consequently has
one unit top `u_x` and three triple tops. Those three `P`-columns
sum to `1−e_x`. The central column `Col(π(x))` contains the
same unit top and also has three triple `P`-columns summing to
`1−e_x`. Invertibility of `B'` makes the two triples identical.
Therefore this element's top-predecessor profile is

\[
U=Col(\pi(x)).
\]

The first-output central-middle matrix on `U×V` is a permutation
matrix. Its row at `u_x` must meet a column `v∈V` with
`π(x)∈P_v`, because `C_(u_x)={π(x)}`. But every member
of `U=Col(π(x))` has `π(x)` in its `C`-block. That column
therefore has four ones, contradicting its required sum one.
This excludes `h=20` and completes the theorem.

The subsequent [unit-or-large theorem](1485_unit_large_central_tiles.md)
excludes this extremal pattern at **every first-output degree**, for
minimum `q+1` and `q²+1` central elements, for every `q≥2`.
Thus the exclusions of nineteen and twenty tops here do not depend
on the total order being forty. Only the sixteen-top argument in §2
uses that order.
