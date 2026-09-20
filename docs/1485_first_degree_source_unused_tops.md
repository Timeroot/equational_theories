# First-degree sources: an exact unused-top identity

Analytic finite E1485 lemma, 20 September 2026. Its identities and
the consequences below have been independently audited; it is not a
Lean formalization. No finite search or SAT premise is used.

Let the minimum degree be `r`, the central set be `Z` of size `m`,
and the top set be `T` of size `h`. Assume the first noncentral
top-output degree is `r+1`, and write `A` for that degree class.
As usual `P_u=Col(u)∩Z`, `C_u=Row(u)∩Z` for a top `u`.

## 1. Removing any selected collection of first-degree outputs

Fix a top `u` with `c=|C_u|`, and choose any `k` distinct successors
`a∈A` of `u`. Let `U_a,V_a` be their equal-size top profiles,
of size `t_a≤r`. Define

\[
 S=\bigcup_{z\in C_u}Row(z).
\]

The `r`-element top sets `Row(z)` are pairwise disjoint here:
their intersection would give a top `v` with `|P_v∩C_u|≥2`,
contrary to central-middle uniqueness. Therefore `|S|=rc`.
Each `Row(z)` has successor blocks partitioning `Z`, so the
`C` blocks indexed by `S` have constant multiplicity `c`.

The first-output central matrix on `U_a×V_a` is a permutation.
Its row at `u` gives exactly one `d_a∈V_a∩S`. The good set

\[
                       G_a=V_a\setminus\{d_a\}
\]

consists of the top inputs whose product with `u` is `a`.
These good sets are pairwise disjoint and lie outside `S`; their
`C` blocks partition `Z\C_(d_a)`.

Let `W=T\(S∪⋃_aG_a)` be the unused tops. Counting top identities
and then the multiplicity of each central label gives the exact formulas

\[
\begin{aligned}
 |W|&=h-rc-\sum_a(t_a-1),\\
 \sum_{w\in W}\mathbf1_{z\in C_w}
     &=r-c-k+\sum_a\mathbf1_{z\in C_{d_a}}\qquad(z\in Z),\\
 \sum_{w\in W}|C_w|
     &=\sum_a|C_{d_a}|-m(k-r+c).                       \tag{1}
\end{aligned}
\]

The retained tops `d_a` may repeat; all sums count their multiplicities.
No uniform reverse-fiber assertion is used.

Since every unused block is nonempty, (1) also yields

\[
 h\le rc+\sum_a(t_a-1)+\sum_a|C_{d_a}|-m(k-r+c).       \tag{2}
\]

This includes the same finite cover mechanism as the
[singleton-source saturation theorem](1485_singleton_source_first_degree_saturation.md),
but does not require the source block to be a singleton or its capacity
to be saturated.

## 2. A maximal central source cannot leave no unused top

Suppose `c=r−1`, and select just one successor `a∈A`. The
middle formula in (1) says that the unused successor blocks partition
the nonempty block `C_(d_a)`. In particular `W` is nonempty, so

\[
                         \boxed{h\ge r(r-1)+t_a.}      \tag{3}
\]

At equality there is one unused top `w`, and `C_w=C_(d_a)`.
More generally, if all central blocks have size at most `M`, then
`1≤|W|≤|C_(d_a)|≤M`. The exact cardinality in (1) consequently
also gives the upper bound

\[
                  \boxed{h\le r(r-1)+t_a-1+M.}        \tag{3a}
\]

The hypothesis bounding *all* central blocks by `M` is explicit:
this statement does not assume a universal bound `M=r−1`.

At minimum four and fifteen tops, (3) says that every degree-five
successor of a top with `|C|=3` has profile size three, not four.
The dual statement holds for predecessors when `|P|=3`.

At order forty, minimum four, eight central elements, and eighteen
tops, the already proved central-block bound is `M=3`. Thus (3a)
says `h≤14+t_a`. A size-three central source cannot have a
degree-five successor of profile size three. If it has a size-four
successor, then the retained block has size three and there are
exactly three unused tops, all with singleton successor blocks.
The dual conclusions hold for predecessor blocks and neighbors.

## 3. Fifteen tops and eight central elements

Now assume order forty, minimum degree four, eight central elements,
and fifteen tops. Let `a` count degree-five elements and let `q>0`
count those of profile size three. The others have profile size four.

The [one-hole maximal-block bound](1485_one_hole_first_output_grid.md)
and the central moments force the inventory

\[
 n_{13}=n_{31}=n_{23}=n_{32}=2,
 \qquad n_{22}=7,
\]

with no other types: the singleton counts are at most two, and
`n11+n33−n13−n31=−4` forces equality. This inventory does not
assume a particular value of `a`.

Write `α_u` for the degree-five successor count, and `γ_u` for
the three-profile successor count. A type `13` top cannot precede
a three-profile, whose central predecessor partition is `332`.
By (3), it cannot precede a four-profile either. Thus all `P=1`
tops have `α=0`. At type `23`, (3) gives `α=γ≤1`.

The exact moments give

\[
 \sum(P-2)\alpha=2q,
 \qquad\sum\alpha=4a-q.
\]

Consequently `Σ_(P=3)α=2q` and `Σ_(P=2)α=4a−3q`.
Put `s=Σ_(23)α=Σ_(23)γ`, so `0≤s≤2` and
`Σ_(22)γ=q−s`. At a double-double top, the unused input count is

\[
                             R=15-8-3\alpha+\gamma
                              =7-3\alpha+\gamma\ge0.
\]

Thus `α=3` forces `γ≥2`. The seven double-double tops satisfy

\[
 \sum_{22}\alpha\le14+\left\lfloor\frac{q-s}{2}\right\rfloor.
\]

It follows that

\[
 4a-3q\le14+s+\left\lfloor\frac{q-s}{2}\right\rfloor
        \le15+\left\lfloor\frac q2\right\rfloor,
 \qquad\boxed{8a-7q\le30.}                           \tag{4}
\]

The final integer inequality is equivalent to the preceding one by
parity. In particular ten degree-five elements are impossible, since
the [order-forty small-profile bound](1485_order_forty_eight_central_six_three_profiles.md)
gives `q≤6`, whereas `8·10−7·6=38>30`.

## 4. At most two of the degree-five profiles are large

Every three-profile has exactly two maximal predecessor blocks, so
`Σ_(P=3)γ=2q`. Together with `Σ_(P=3)α=2q` and `γ≤α`,
this says that no `P=3` top precedes a four-profile. There are no
`P=1` predecessors either. The only remaining possibilities are
`22` and `23`, and (3) excludes `23`. Therefore every four-profile
has all four top predecessors among the seven double-double tops.
Dually all four of its top successors lie in that same seven-top set.

Two four-profile predecessor sets are four-subsets of seven tops,
so they intersect. If their intersection had size at least two,
their successor sets would be disjoint by the first-output matching
condition. Two four-subsets of seven cannot be disjoint. Hence any
two such predecessor sets meet in exactly one top.

Three four-subsets with pairwise intersections one have union of size
at least `12−3=9`, not at most seven. There can be at most two
four-profiles. Thus

\[
                              \boxed{a-q\le2.}         \tag{5}
\]

Combining (4), (5), `q≤6`, and sharp-neighbor coverage
`17−a≤a+q`, the only necessary fifteen-top class sizes remaining
are

\[
                    (a,q)=(6,5),(6,6),(7,5),(7,6),(8,6).
\]

This is a purely analytic reduction, not a construction of any of
these possibilities or an exclusion of all fifteen-top models.
The subsequent [finite five-profile obstruction](1485_order_forty_eight_central_fifteen_profile_bound.md)
gives `q≤4` and excludes all these remaining pairs at order forty.

## 5. Extension to every first-output degree gap

The same counting mechanism is not limited to gap one. Let `p=r+k`,
`k≥1`, be the least degree of a noncentral **top-top product**.
Fix a top `u`, put `c=|C_u|`, and select `ℓ` distinct successors
`a` of `u` that are top-top products of this degree. The
[general first-output theorem](1485_first_top_output_fibers.md) gives
equal top-profile sizes `t_a` and `k`-regular central matrices, with

\[
                         k+1\le t_a\le r+k-1.
\]

For `k>1` one must not replace the last upper bound by `r`.
Nor is a general degree-`p` vertex assumed to be a top-top product.

Define `S=⋃_(z∈C_u)Row(z)` as in §1. The retained set
`D_a=V_a∩S` now has exactly `k` tops, by the central-matrix
row sum. Its successor blocks form a disjoint union `E_a⊆Z`.
The good inputs `G_a=V_a\D_a` have size `t_a−k`, their blocks
partition `Z\E_a`, and these good input sets are disjoint for
distinct outputs. Thus, with `W=T\(S∪⋃G_a)`,

\[
\begin{aligned}
 |W|&=h-rc-\sum_a(t_a-k),\\
 \sum_{w\in W}\mathbf1_{z\in C_w}
     &=r-c-\ell+\sum_a\mathbf1_{z\in E_a},\\
 \sum_{w\in W}|C_w|
     &=\sum_a|E_a|-m(\ell-r+c).                      \tag{6}
\end{aligned}
\]

This is the same proof as (1), with a retained union in place of a
single retained block. The sets `D_a` may overlap between different
outputs; the displayed sums retain those multiplicities.

For one selected output and `c=r−1`, the unused blocks partition
`E_a`. This union is nonempty because `k≥1`, and proper because
`t_a>k` leaves a nonempty good block. If all central blocks have
size at most `M`, then

\[
 \boxed{r(r-1)+t_a-k+1\le h
       \le r(r-1)+t_a-k+\min(kM,m-1).}               \tag{7}
\]

These general-gap identities and bounds were independently audited.
They are available for the still-open first-output degrees six and
seven at minimum four, but no exclusion of those whole branches is
claimed here.
