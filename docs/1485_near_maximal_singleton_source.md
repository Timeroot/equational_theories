# A near-maximal singleton source forces an antichain

Research note, 20 September 2026. This is an analytic necessary
condition, not an exclusion of the entire profile.

Assume minimum degree `r≥4`, central count `m=2r−1`, and least
noncentral top-product degree `p=2r−1`. Let a top source `u` satisfy

`P_u=A`, `|A|=r−1`, `C_u={c}`.

**Theorem.** The predecessor blocks of the `r` tops on `Row(c)`
are pairwise incomparable under inclusion. Moreover, if `c∈A`, the
singleton-successor replacement obtained by omitting `u` has a
predecessor block of size exactly two.

This uses the new analytic
[uniform singleton-label separation theorem](1485_boundary_output_singleton_separation.md),
but no finite profile exclusion.

## 1. Omissions of size at most two give crowns

For any omitted top `d∈Row(c)`, arbitrary-omission exact replacement
produces a first-output vertex `a` with top profile size `t≥r`,
whose predecessor profile contains `u`. Its other `t−1` nonempty
predecessor blocks partition `Z\A`, of size `r`. Hence

`r≤t≤r+1`.

If `t=r+1`, all these other predecessor blocks are singleton, so
`Z\A⊆S_P`. Singleton separation then gives `S_C⊆A`.

The successor profile retains `r−1` tops of `Row(c)` and has two
new tops, whose nonempty successor blocks partition `C_d`. If
`|C_d|=1`, this is already impossible. If `|C_d|=2`, both new
successor blocks are singleton, so `C_d⊆S_C⊆A`. But `A=P_u`
is a global predecessor block and must meet `C_d` in at most one
point, another contradiction.

Thus every omission with `|C_d|≤2` has `t=r` and gives the crown
matrix `J_r−I_r`.

## 2. Every pair of central-row tops can be retained in such a crown

Take any two distinct tops `v,w∈Row(c)`. At least one of the
other `r−2` tops has a successor block of size at most two. Otherwise
the central partition would have size at least

`1+1+3(r−2)=3r−4>2r−1`,

where the strict inequality uses `r≥4`. Omit such a top. The
resulting crown retains both `v,w`.

If `P_v⊆P_w`, their two columns are entrywise ordered and each
has sum `r−1`. They would therefore be identical, whereas distinct
crown columns have different zero positions. This proves the
antichain assertion, including exclusion of equal predecessor blocks.

## 3. The omitted-source replacement cannot be singleton

Now suppose `c∈A`. Then `u∈Row(c)`, and omitting `u` gives a
crown with replacement top `w` satisfying `C_w={c}`, `w∉Row(c)`.
On the central column at `c`, the predecessor partition consists of
`A` and `r−1` blocks covering `Z\A`, so the latter blocks are
one pair and `r−2` singletons. Thus `P_w` has size one or two.

Suppose `P_w={i}`. Since `w∉Row(c)`, one has `i≠c`. The crown
column at `w` is zero in row `u` and one in its other `r−1` rows.
All those other row tops therefore have successor blocks containing
`i`. Their predecessor blocks partition `Z\A`, so they constitute
`r−1` tops on `Col(i)` covering precisely that predecessor set.
The remaining top `v∈Col(i)` has predecessor block `P_v=A`.

This top differs from `u`, because `i≠c` and `C_u={c}`. Since
`c∈A`, both `u,v` belong to `Row(c)`, contradicting the antichain
theorem. Therefore `|P_w|=2`.

There is a dual statement. At `r=4,m=p=7`, the result gives
additional analytic structure to the `(3,1)` case, but does not
replace its completed finite exclusion by an analytic proof.
