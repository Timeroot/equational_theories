# A general bound on joint outside-label fibers

Research note, 20 September 2026. This is an analytic central-incidence
lemma. Its boundary-spectrum application uses the previously established
[common singleton-label theorem](1485_boundary_singleton_overlap.md).
There is no enumeration or solver premise, and no Lean formalization yet.

Let a finite E1485 magma have minimum translation degree `r` and central
class `Z` of size `m`. Suppose `J⊆Z`, `|J|=k`, and two central labels
`y,z` have the following singleton rectangles for every `c∈J`:

\[
(P,C)=(\{y\},\{c\}),\qquad
(P,C)=(\{c\},\{z\}).
\]

**Theorem.**

\[
\boxed{m-k\le(r-k)^2.}
\]

Indeed `Row(y)` has `r` tops, including the `k` listed singleton-`C`
tops. Its other `r-k` successor blocks partition `Z∖J`. Likewise the
`r-k` remaining predecessor blocks in `Col(z)` partition `Z∖J`.
Every block of the latter partition meets each block of the former
in at most one point, by central-endpoint uniqueness. It consequently
has size at most `r-k`. Summing over its `r-k` blocks gives the bound.
This also handles `k=r`: the residual set must then be empty.

## Boundary application

At `m=p=2r-1`, a common singleton label `c∈S_P∩S_C` gives the two
rectangles above, with outside labels `y(c),z(c)`. A fiber of their
joint map therefore satisfies

\[
2r-1-k\le(r-k)^2.
\]

Equivalently, writing `t=r-k`,

\[
t(t-1)\ge r-1.
\]

For `r=4,m=7`, a two-element joint fiber would require `5≤4`.
Thus the joint map is injective:

\[
\boxed{y(c)=y(d),\ z(c)=z(d)\quad\Longrightarrow\quad c=d.}
\]

This excludes the same-double-fiber normalization of the
[three-common-label analysis](1485_seven_central_overlap_three.md)
analytically. It also excludes the case of two common labels with
both outside maps constant. It does not by itself say that either
outside map is injective separately.

## Two different outside fibers give a stronger inequality

In the boundary setting, fix outside labels `y,z` and write

`A_y={c:y(c)=y}`, `B_z={c:z(c)=z}`,

with sizes `k,l` and intersection size `j`. The `r-k` residual
successor blocks on `Row(y)` partition `Z∖A_y`; the `r-l` residual
predecessor blocks on `Col(z)` partition `Z∖B_z`. Their pairwise
intersections partition `Z∖(A_y∪B_z)`, and every intersection has
size at most one. Therefore

\[
\boxed{m-k-l+j\le(r-k)(r-l).}
\]

The earlier joint-fiber inequality is the special case in which the
two selected fibers coincide. For general fibers, both their sizes and
their overlap matter.

Let `a=|S_P∖S_C|`, `b=|S_C∖S_P|`, and `i=|S_P∩S_C|`.
Sum the displayed inequality over all `a b` pairs of outside labels.
Each common label belongs to one fiber of each map, so the sums of
the fiber sizes are `i`, and the sum of all intersection sizes is also
`i`. We obtain

\[
abm-bi-ai+i\le abr^2-r(a+b)i+i^2.
\]

At `m=2r-1`, this is

\[
\boxed{\bigl(a(r-1)-i\bigr)\bigl(b(r-1)-i\bigr)\ge i.}
\]

The [boundary overlap bound](1485_boundary_singleton_overlap.md) gives
`i≤2r-5`. If `r≥4` and equality holds, it also gives `a=b=2`.
The new inequality then reduces to `9≥2r-5`, hence `r≤7`.
Consequently the general overlap bound improves analytically to

\[
\boxed{r\ge8\quad\Longrightarrow\quad i\le2r-6.}
\]

This is a bound on common singleton labels under the boundary first-output
assumption, not a full-core or spectrum characterization.

## A block meeting another outside fiber is small

Continue to assume `m=p=2r-1`. Fix an outside predecessor label `y`,
and suppose its common-label fiber `A_y` has size `k`. Let a successor
block `F` on `Row(y)` contain a common label `e∉A_y`; write `b=|F|`.
Then

\[
\boxed{b\le r-\left\lceil\frac{k}{2}\right\rceil.}
\]

Indeed the top `w` with `C_w=F` belongs to `Col(e)`. That column has
the unique singleton predecessor block `{y(e)}` and all its other
predecessor blocks are pairs. Since `P_w` contains `y≠y(e)`, it is a
pair `{y,h}` with `h≠y`.

On `Row(h)`, none of the `k` common labels of `A_y` can be a singleton
successor block: each such singleton top has predecessor block `{y}`.
Moreover these labels all lie outside `F`, since `F` is disjoint from
the `k` singleton blocks on `Row(y)`. They must therefore lie in
nonsingleton blocks among the other `r-1` blocks of `Row(h)`.

Those `r-1` blocks contain `2r-1-b` labels in total, so their excess
over singleton blocks is `r-b`. Blocks of sizes `s≥2` satisfy
`s≤2(s-1)`, so together the nonsingleton blocks contain at most
`2(r-b)` labels. Thus `k≤2(r-b)`, proving the bound.

There is a dual bound for predecessor blocks meeting another outside
successor-label fiber.

## The extremal overlap is impossible for every minimum degree at least four

**Theorem.** Under the boundary assumptions `m=p=2r-1`,

\[
\boxed{r\ge4\quad\Longrightarrow\quad |S_P\cap S_C|\le2r-6.}
\]

This extends the preceding `r≥8` consequence to all `r≥4`.
For `r=4`, it is the analytic
[three-common-label exclusion](1485_seven_central_overlap_three.md).
That proof uses the joint-fiber inequality, but not this general
extremal-overlap theorem, so the dependency is not circular.

Suppose henceforth `r≥5` and, for a contradiction, `i=2r-5`.
The previous boundary overlap theorem makes the two outside-label sets
`A={y₀,y₁}`, `B={z₀,z₁}` complementary to the common labels.
Every outside fiber has size at most `r-2`; since each map has two
fibers summing to `2r-5`, their sizes are `r-2` and `r-3`.
Label the larger fibers

`Y₀={c:y(c)=y₀}`, `Z₀={c:z(c)=z₀}`.

Their intersection has size at least one, because their union lies in
a set of size `2r-5`. The two-fiber inequality gives

\[
3+|Y_0\cap Z_0|\le4.
\]

Thus their intersection has size exactly one and their union is all
of `I`. The sets `Y₀∖Z₀`, `Z₀∖Y₀` both have size `r-3`.

After removing its `r-2` common singleton blocks, `Row(y₀)` has two
residual successor blocks. Similarly `Col(z₀)` has two residual
predecessor blocks. Their four intersections partition the four-element
outside set `H=Z∖I=A⊔B`. Every intersection has size at most one,
so each has size one. In particular each residual block contains exactly
two outside labels.

A residual successor block therefore has size `2+t`, where `t` of its
labels belong to `Z₀∖Y₀`; the two values of `t` sum to `r-3`.
If `t>0`, it meets another outside fiber, so the block bound above gives

\[
2+t\le r-\left\lceil\frac{r-2}{2}\right\rceil,
\qquad
t\le\left\lfloor\frac{r-2}{2}\right\rfloor.
\]

Neither of the two residual successor blocks can have `t=0`.
Otherwise the other has `t=r-3`, which violates this bound when `r≥5`.
Hence both have size at least three and contain common labels.
Dually both residual predecessor blocks do as well.

Finally consider the central cell `(y₀,z₀)`. Its top belongs to a
residual block of `Row(y₀)`, because `z₀` is outside the common
singleton labels, and to a residual block of `Col(z₀)` for the same
reason. Both its predecessor and successor blocks consequently have
size at least three and meet `I`. But any top whose predecessor block
meets `I` belongs to a common central row, where every successor block
has size at most two. This is a contradiction.

The extremal value `i=2r-5` is therefore impossible. Combined with the
previous upper bound, this proves the theorem.

## One outside map has strictly smaller fibers

There is a structural corollary for every `r≥4`: the two outside maps
cannot both have a fiber of size `r-2`. For such a pair, the two-fiber
inequality would make their intersection size at most one. Their union
would then contain at least `2r-5` common labels, contradicting the new
upper bound `i≤2r-6`.

Consequently, after possibly exchanging predecessor and successor
directions, the fiber bounds improve to

\[
\boxed{|y^{-1}(a)|\le r-3,\qquad |z^{-1}(b)|\le r-2.}
\]

At minimum degree four, one of the two outside maps must therefore
be injective. This is an analytic consequence; the stronger bound of
at most one common label at `r=4,m=p=7` also uses the separate
[two-label finite check](1485_seven_central_overlap_two.md).
