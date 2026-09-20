# Order forty: global good-pair bounds with variable top counts

Research note, 20 September 2026. These analytic necessary conditions
were independently audited. They do not exclude all the remaining
order-forty branches and are not Lean declarations.

Assume minimum degree four and order forty. Write `m,h,a,b` for the
cardinalities of the degree classes `4,10,5,8`, respectively, and denote
the latter two classes by `A,B`. Assume **every member of `A` has
four top neighbors in each direction**, hence one sharp neighbor in `B`.
This holds automatically when `m=10`; at smaller central counts it is
an additional hypothesis. Then `a+b=40-m-h` and `a≥b`.

## 1. Exact and aggregate counts at a degree-eight vertex

For `x∈B`, let `I_x,O_x` be its top predecessor and successor counts,
and let `j_x` be its number of sharp successors in `A`. Its internal
successor count is `v_x=8-O_x-j_x`. Let `τ_x` count bad internal
two-edge paths with middle `x`.

For an internal edge `x→y`, the fiber `R_y^{-1}(x)` has size five.
Its non-top input count is `8-I_x-η(x,y)`, so its top input count
is `I_x-3+η(x,y)`. Counting the four-element top-translation fibers
at `x` gives the exact top-product count

\[
g_x=4I_x-I_xj_x-v_x(I_x-3)-\tau_x
=I_x(O_x-4)+24-3O_x-3j_x-\tau_x.
\tag{1}
\]

As in the [uniform-top-count proof](1485_order_forty_uniform_top_counts.md),
counting bad paths by their starting vertex gives
`Στ_x≤Σj_xv_x`. This is a global bound, not an edgewise balance
assumption. Put

\[
H(I,O,j)=I(O-4)+24-3O-3j-j(8-O-j).
\]

Then `Σg_x≥ΣH(I_x,O_x,j_x)`. Also `Σj_x=a` and
`Σ(I_x-O_x)=0`: the total `B` in/out degrees agree, the internal
edges cancel, and there are exactly `a` sharp edges in each direction
between `A` and `B`.

## 2. Three top neighbors suffice for a useful bound

Suppose `I_x,O_x≥3` for every `x∈B`. The identity

\[
H(I,O,j)-\bigl(10-5j-(I-O)\bigr)
=(O-3)(I+j-4)+(j-1)(j-2)
\]

has a nonnegative right side for integer `j≥1`. Thus

\[
\boxed{\sum_{x\in B}g_x\ge10b-5a.}
\tag{2}
\]

There are `h²` top pairs. Central elements contribute `16m` and
degree-five elements contribute `12a`. Therefore

\[
h²\ge16m+7a+10b=400+6m-10h-3a,
\qquad 12a\le h²-16m.
\]

Combining the two inequalities yields

\[
\boxed{h²+8h\ge320+8m.}
\tag{3}
\]

For example, at `m=9`, top counts fifteen and sixteen violate (3).
Thus an order-forty model with nine central elements and sixteen tops
would have to contain a degree-five vertex with a **three-element**
top profile. The three-neighbor hypothesis in this application follows
from the central shadow and the already proved absence of size-four
central blocks at central counts seven through ten.

## 3. Four top neighbors give an exact positive-excess improvement

Suppose instead `I_x,O_x≥4`. Reciprocal-neighbor balance says
`I_x-O_x=3(j_x^- -j_x)`. Each top count lies between four and seven.
A difference of three would force the side with seven tops to have
sharp count one, and the opposite side to have sharp count zero.
Thus the top counts and sharp counts balance individually. Write

\[
I_x=O_x=t_x=4+e_x,\qquad 0\le e_x\le3,
\qquad j_x+e_x\le4.
\]

Substitution in (1) and the global bad-path bound gives

\[
\boxed{\sum_{x\in B}g_x
\ge12b-7a+\sum_x\bigl(j_x²+e_x(j_x+1)+e_x²\bigr).}
\tag{4}
\]

In particular, using `j²≥3j−2`,

\[
\sum_{x\in B}g_x
\ge10b-4a+\sum_xe_x(t_x+j_x-3).
\tag{5}
\]

Every unit of top-neighbor excess contributes at least three to the
last sum. When all excesses vanish, this recovers the earlier uniform
bound without any assumption about the top vertices' own top counts.

## 4. Initial consequences for ten central elements

Now take `m=10`, so all central blocks have size at most three and
the remaining top counts are `h=17,18`. Every vertex has at least
four top neighbors. For a top `u`, put `δ_u=|TopSucc(u)|−4`.
The central row equation bounds `0≤δ_u≤h−16`, and summing it gives

\[
\sum_{u\in T}|P_u|\delta_u=10(h-16).
\]

Let `E=Σ_(x∈B)e_x`. Counting all edges ending in `T` gives
`Σ_uδ_u+E=10(h−16)`. Since `Σ_u(3−|P_u|)=3h−40`,

\[
20(h-16)-3E
=\sum_u(3-|P_u|)\delta_u
\le(h-16)(3h-40).
\]

Consequently `E≥3` at `h=17`, and `E≥4` at `h=18`.
Sharp-neighbor existence and `j_x+e_x≤4` also give
`a=Σj_x≤4b-E`. Hence the possible class sizes are reduced to

| Top count | Remaining `(a,b)` possibilities |
| ---: | --- |
| 17 | `(7,6)`, `(8,5)`, `(9,4)` |
| 18 | `(6,6)`, `(7,5)`, `(8,4)` |

These are necessary numerical cases, not models. Formula (4), the
central incidence constraints, and the
[one-top-product gap](1485_top_product_count_gap.md) give further
tests; no elimination of all these cases is claimed on this page.
The subsequent [unified ten-central proof](1485_order_forty_ten_central_exclusion.md)
excludes both rows analytically. The counts here are intermediate
restrictions, not the current open frontier.

## 5. Cancel bad paths against auxiliary parameter supports

Keep the hypotheses of §3: every degree-five vertex has four top
neighbors, and every degree-eight vertex has balanced top count
`4+e_x`. No additional bound on individual central blocks is needed
for this argument. Let `K=4b-a-E` count internal ordinary `B`
edges, and let `τ` count bad internal two-edge paths. The exact
top-pair count from (1) is

\[
N=h^2-16m-12a-\sum_x(4+e_x)e_x-3K+\tau,
\]

where `N` counts top-valued ordered top pairs.
For an internal edge `x→y`, its central support
`H_xy={z∈Z:x B_z y}` is the disjoint union of the `P`-blocks
of the top inputs of `R_y^{-1}(x)`. There are
`s=1+e_x+η(x,y)` such inputs. These belong to the `4+e_x`
nonempty blocks partitioning `Z` at `x`. Omitting the other blocks
gives

\[
|H_{xy}|\le m-(4+e_x-s)=m-3+\eta(x,y).
\]

Let `Q` count all auxiliary top-to-top edges, summed over central
parameters. Equivalently
`Q=Σ_(u,v∈T,u*v∈T)|C_v|≥N`: multiplication by `u` is
injective on each central column. Four-regularity of each auxiliary
relation, and its fixed sharp edges between `A` and `B`, give

\[
m(4b+2a-4h+4m)+Q
=\sum_{x\to y\text{ in }B}|H_{xy}|
\le(m-3)K+\tau.
\]

Substitute the exact expression for `N`, use `Q≥N`, and cancel
`τ`. With `K=4b-a-E`, the result is

\[
\boxed{(h-2m)^2+(3m-12)a+
\sum_xe_x(m-4-e_x)\le16m.}
\tag{6}
\]

This strengthens the degree-only budgets by retaining the finite set
of central parameters supporting each edge. At `m=10,h=18` it is
`18a+Σe_x(6-e_x)≤156`. Since `E≥4` and `0≤e_x≤3`,
the case `a=8,b=4` is impossible: its sum would have to equal twelve,
forcing `E=4` with every excess zero or three. The
[eighteen-top note](1485_order_forty_ten_central_eighteen_tops.md#5-auxiliary-support-excludes-eight-degree-five-and-four-degree-eight-elements)
details this specialization. A separate
[degree-five edge-capacity argument](1485_order_forty_ten_central_exclusion.md)
now excludes the other two splits as well; it does not depend on (6).
