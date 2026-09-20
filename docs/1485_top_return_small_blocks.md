# Top-valued top products only involve small central blocks

Research lemma, 20 September 2026. This is an independently audited
analytic finite E1485 consequence, not a full-core theorem or a Lean
declaration.

Let the minimum and maximum translation degrees be `r,s`, with `r>1`,
and write `P_t,C_t` for a top vertex's nonempty central predecessor
and successor blocks. Put

\[
q=\left\lfloor\frac{r^2-s}{r-1}\right\rfloor.
\]

**Theorem.** If `u,v,t` are top and `u*v=t`, then all six central
blocks of `u,v,t` have size at most `q`.

The [central-block packing inequality](1485_refined_top_product_packing.md)
first gives

\[
|P_u|\le q,\qquad |C_v|\le q.
\tag{1}
\]

Choose `c∈P_u` and `d∈C_v`. The return identities give

\[
t*(v*c)=v,\qquad (d*u)*t=u.
\tag{2}
\]

For example, writing `c=z*u` and using E1485 yields the first
identity; the second is its dual. All factors and outputs in (2)
are top, since a product with a central factor is top. Applying (1)
to these two products bounds both `P_t` and `C_t` by `q`.
We have therefore proved that the output of **every** top-valued
top product has both blocks bounded by `q`. Applying this output
conclusion to (2) bounds both blocks of `v` and of `u` as well.
This proves the theorem without an assumption that all top products
are top.

## Consequences

Let `S={t∈T: |P_t|≤q and |C_t|≤q}`. Every top-valued top
product lies in `S×S→S`. In particular, a top outside `S` has
no incoming or outgoing top-to-top edge in any central auxiliary
relation `B_z`.

Indeed an auxiliary edge `u B_z t` with top endpoints has
`t=u*v` for some `v∈Col(z)⊆T`. The theorem applies to this
triple. The analogous incoming assertion is the same statement.

If `N` is the number of top-valued ordered top pairs, the
[weighted return identity](1485_top_product_count_gap.md#a-weighted-return-bijection)
and the theorem give

\[
N\le Q:=\sum_{u,v\in T,\ u*v\in T}|C_v|
=\sum_{u,v\in T,\ u*v\in T}|P_u|\le qN.
\]

At order forty with minimum degree four, `s=10` and `q=2`.
Thus all three vertices of a top-valued top product have types
`(1,1),(1,2),(2,1),(2,2)`. Every top with a size-three or
size-four central block is absent from all auxiliary top-to-top
edges. This restriction does **not** assert that the remaining
top-valued products exist or that their count is zero.
