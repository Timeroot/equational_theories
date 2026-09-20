# There cannot be exactly one top-valued product of two tops

Research lemma, 20 September 2026. This is an analytic finite E1485
consequence, not a Lean theorem or a full spectrum exclusion.

Let `T,Z` be the top and central classes of a nonconstant-degree
finite model. For `u∈T`, write `P_u=Col(u)∩Z`, `C_u=Row(u)∩Z`.
Both are nonempty, and every `P_u∩C_v` has size at most one.

**Lemma.** The number of ordered pairs `(u,v)∈T²` whose product
is top is either zero or at least two.

Suppose instead there is exactly one such pair, with `u*v=t∈T`.
For any `c∈P_u`, write `c=z*u`. E1485 gives

\[
t*(v*c)=(u*v)*(v*(z*u))=v.
\]

All three displayed elements are top, since a product with a central
factor is top. Uniqueness of the top-valued top pair forces this pair
to be `(u,v)` with output `t`. Thus `t=u`, `v=t`, and all three
are one element, with `t*t=t`. It also forces `t*c=t` for every
`c∈P_t`, which implies `P_t⊆C_t`.

The dual identity gives `(d*t)*t=t` for every `d∈C_t`; uniqueness
likewise gives `d*t=t` and `C_t⊆P_t`. Hence `P_t=C_t={c}` for
one central element `c`, and `t*c=c*t=t`. Centrality at `c` now gives

\[
c=(t*c)*(c*t)=t*t=t,
\]

contrary to the disjointness of the central and top classes when degrees
are nonconstant. This proves the lemma. In particular a separately
proved upper bound of one actually forces the top-valued top-pair
count to be zero; it does not establish that the count is positive.

## A weighted return bijection

The same identity has a useful exact counting form. For each top-valued
top product `u*v=t`, mark one central predecessor `c∈P_u`. The map

\[
(u,v,t,c)\longmapsto(t,v*c,v,c)
\]

is a bijection onto top-valued top products whose second input is marked
by a central successor. Its inverse sends `(t,w,v,c)` to
`(c*t,v,t,c)`. Indeed `c∈C_w` means `w=z*c`; E1485 yields
`(c*t)*(t*w)=t`. Central endpoint uniqueness gives `v*c=w`
and recovers `c*t=u` in the forward direction. Consequently

\[
\sum_{u,v\in T:\ u*v\in T}|P_u|
=\sum_{u,v\in T:\ u*v\in T}|C_v|.
\]

The bijection is a necessary identity, not an argument that both sums
vanish. No assertion that a positive count must exceed two is made here.

## Common support and bounds on a single row or column

Let `N` count the ordered pairs of tops whose product is top. If
`N>0`, the sets of first inputs, second inputs, and outputs of these
products coincide. Indeed, from `u*v=t`, the two return identities

\[
                       t*(v*c)=v\quad(c\in P_u),\qquad
                       (d*u)*t=u\quad(d\in C_v)
\]

place `t` among both kinds of inputs, and place `u,v` among the
outputs. The central blocks are nonempty, so these give all inclusions
needed to identify the three supports. Write `S` for their common set.

If the row at `u` has `j` top-valued top products, it uses `j`
distinct second inputs, so `|S|≥j`. Each of the other `|S|−1`
first inputs contributes at least one further product. Thus

\[
                           N\ge2j-1.                    \tag{1}
\]

Dually, if the column at `v` has `k` such products, then
`N≥2k−1`. These inequalities also hold for empty rows, columns,
or `N=0`. In particular `N≤4` permits at most two entries in any
one row or column, and `N≤6` permits at most three.

There are also central-block-weighted bounds:

\[
                           N\ge j|P_u|,\qquad
                           N\ge k|C_v|.                 \tag{2}
\]

For the first inequality, apply the return map to every row entry and
every central predecessor:

\[
 (v,c)\longmapsto(t,v*c,v),\qquad u*v=t,\quad c\in P_u.
\]

Its images are top-valued top-product triples. Distinct values of `v`
give distinct outputs. For fixed `v`, if `v*c=v*c'=w`, then both
`c,c'` lie in `P_u∩C_w`, which has size at most one. Thus the map
is injective, proving `j|P_u|≤N`. The dual map
`(u,d)↦(d*u,t,u)`, with `u*v=t` and `d∈C_v`, proves the
second bound using `C_v∩P_(d*u)`.

These are general finite E1485 return-counting lemmas. They do not
assume order forty, minimum degree four, any particular central count,
or the absence of products in another degree class.
