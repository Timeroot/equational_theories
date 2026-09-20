# A maximal central block excludes the boundary first-output degree

Research note, 20 September 2026. This is an analytic finite E1485
theorem, not a Lean declaration. No enumeration or solver result is used.

Write `r` for the minimum translation degree, `Z` for the central
class, `m=|Z|`, and `T` for the top class. For `u∈T`, write
`P_u=Col(u)∩Z` and `C_u=Row(u)∩Z`. Let `p` be the least
degree of a noncentral product of two tops, when such a product exists.

**Theorem.** Suppose `r≥3` and some top `u` satisfies

\[
|C_u|=1,\qquad |P_u|=m-r+1.
\]

Then

\[
\boxed{p\le 2r-2.}                                      \tag{1}
\]

There is a dual statement with `P,C` exchanged. The block size
`m-r+1` is the largest possible in a partition of `m` labels
into `r` nonempty blocks. The theorem concerns the first **top
product**, not necessarily the least noncentral ordinary degree.

## 1. Boundary outputs would have crown profiles

Put `C_u={c}` and `A=P_u`. For every central `z`, the set
`S=u*Col(z)` has `r` distinct members, exactly one of them
central, namely `c`. The
[ordered auxiliary-degree bound](1485_auxiliary_ordered_degree_bound.md)
puts a least noncentral member of `S` at degree at most `2r-1`.
Thus `p≤2r-1`. Suppose for a contradiction that `p=2r-1`.
Every such least member of every `S` then has degree exactly `p`.

Let `a` be any degree-`p` product in row `u`, with top profiles
`U=TopPred(a)`, `V=TopSucc(a)`. The
[first-output fiber theorem](1485_first_top_output_fibers.md)
gives `|U|=|V|=t≥r`. The central predecessor blocks of `U`
partition `Z` and include the block `A`, of size `m-r+1`.
Therefore `t≤r`, and equality holds. The other `r-1` members
of `U` have singleton predecessor blocks partitioning `Z∖A`.

The central-middle matrix on `U×V` is `(p-r)`-regular, hence
`(r-1)`-regular of size `r`. It is the crown matrix `J_r-I_r`
after reindexing. In particular its rows are distinct, its columns
are distinct, and each has precisely one zero.

## 2. Every omitted central-row point occurs

For each `d∈Row(c)`, choose `z∈C_d`, and choose a least
noncentral member `a` of `u*Col(z)`. The preceding section makes
its degree `p`. The exact replacement identity is

\[
\boxed{Row(a)=L_u^{-1}(a)\ \sqcup\ (Row(c)\setminus\{d\}).}
                                                               \tag{2}
\]

Here is the fiber argument, included to fix the quantifier **every
`d`**. The first-output argument puts `Row(a)` inside the union
of the fiber at `a` and the central fiber `L_u^{-1}(c)=Row(c)`.
No other smaller noncentral top output is available. These disjoint
fibers each have `r` elements. Their union meets `Col(z)` at the
two distinct inputs giving `a` and `c`, whereas `Row(a)` meets
that central column only at the first input. The second input is
exactly `c*z=d`. Removing it leaves `2r-1=p` elements, forcing
equality in (2).

Since `a` has exactly `r` top successors, its successor profile
retains `r-1` of the `r` tops in `Row(c)` and replaces `d` by
one new top `w`. The successor central blocks of these profiles
partition `Z`, so

\[
C_w=C_d.                                                 \tag{3}
\]

Consequently the predecessor blocks on `Row(c)` are pairwise
distinct. Otherwise choose an omitted point different from two
tops having equal predecessor blocks; this is possible because
`r≥3`. The successor crown profile would retain those two tops
and have two equal columns, a contradiction.

There is also no singleton predecessor block on `Row(c)`.
Such a block would be `{c}`. Choose an omission retaining that
top. The crown row at `u` has ones at all the retained central-row
tops, and a zero at the replacement. No other predecessor-profile
member can have `c` in its successor block: it would have the
same `r-1` ones and hence the same crown row. A retained column
with predecessor block `{c}` would therefore have just one one,
instead of `r-1≥2`.

## 3. The maximal block forces a repeated crown column

First `c∈A`. If not, the predecessor partition of any output
in Section 1 includes a top with predecessor block `{c}` among
its `r-1` singletons. That top belongs to `Row(c)`, contradicting
the preceding paragraph.

Thus `u∈Row(c)`. Apply Section 2 with omitted point `d=u`.
Its replacement `w` has `C_w={c}` and is different from `u`.
In the central column `Col(c)`, the predecessor blocks partition
`Z` into `A` and `r-1` singletons. Hence

\[
P_w=\{i\}\quad\text{for some }i\notin A.
\]

In the resulting crown, the column at `w` has zero in the row
at `u`, because `i≠c`. Its other `r-1` entries are all one.
Thus every other predecessor-profile member `x` has `i∈C_x`.
These are `r-1` distinct tops in `Col(i)`, whose predecessor
blocks are exactly the singletons of `Z∖A`. The remaining top
`v∈Col(i)` must have predecessor block `P_v=A`.

Since `c∈A`, this top `v` belongs to `Row(c)`. It differs
from `u`, whose successor block `{c}` does not contain `i`.
We have obtained two distinct members `u,v` of `Row(c)` with
the same predecessor block `A`, contradicting Section 2.
This excludes `p=2r-1` and proves (1).

## Consequence at minimum four and central count six

At `r=4,m=6`, a top of central profile `(3,1)` or `(1,3)`
therefore forces `p≤6`. This was an intermediate step in the
[six-central profile analysis](1485_min_four_six_central_seven_profiles.md).
Together with singleton-label and containment arguments it now
contributes to the [complete exclusion of first-output degree seven](1485_min_four_six_central_seven_exclusion.md).
The stronger result extends to [two extra central vertices for every
minimum degree at least four](1485_two_extra_central_first_output_gap.md).
These results still do not exclude every six-central configuration
or establish full core at minimum four.
