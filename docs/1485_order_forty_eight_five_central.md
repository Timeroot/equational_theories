# Order forty-eight with five central vertices

Research note, 19 September 2026. These are analytic necessary
conditions, not an exclusion of this case and not Lean declarations.

Assume minimum degree four, order 48, and exactly five central
vertices. The degrees are exactly `4,6,8,12`: the first noncentral
top-output degree is at most six by the
[five-central theorem](1485_min_four_five_central_seven_exclusion.md),
so it must be six; complementation supplies degree eight. Write
`Z,A,B,T` for these four classes, and put `a=|A|`, `b=|B|`.

The central moment calculation gives an integer `d∈{0,1,2}` with

\[
(N_{11},N_{12},N_{21},N_{22})=(5+4d,5-2d,5-2d,d),
\qquad |T|=15+d,
\qquad a+b=28-d.                                      \tag{1}
\]

Every vertex has between three and five top neighbors on each side.
Each member of `A` has only sharp `B` neighbors off the top class.
Its sharp in- and out-counts agree by reciprocal-neighbor balance;
denote this count by `k`. Thus `k∈{1,2,3}`, and its common top
profile size and good top-pair count are

| `k` | Top-profile size | Good top pairs |
| ---: | ---: | ---: |
| 1 | 5 | 15 |
| 2 | 4 | 8 |
| 3 | 3 | 3 |

Put `K=Σ_{x∈A}k_x`.

## 1. Central successor count two forbids a top output

Suppose `u*v=t` with all three vertices top, and choose a central
successor `z` of `v`. The four distinct members of

\[
S=u*Col(z)
\]

have disjoint four-element fibers under `L_u`. Their union is the
sixteen-element fixed-parameter set `F_{z*u}(u)`, which contains
`Row(t)`.

If `u` had two central successors, exactly two members of `S`
would be central. Their two fibers contain eight top inputs.
Each of the other two fibers contains its original top input from
`Col(z)`. Thus the fixed-parameter set would contain at least ten
tops.

But `d(t)=12`, and `t` has at most five top successors. Its row
supplies at least seven non-top points to the same set. The total
would be at least seventeen, a contradiction. Consequently

\[
\boxed{u,v,u*v\in T\quad\Longrightarrow\quad
|C_u|=1,\quad |P_v|=1.}                            \tag{2}
\]

The second assertion is the dual argument. This restricts the
inputs of top-valued top products, not the central profile of their
output.

## 2. Auxiliary edge counts

Fix a central parameter `z`, and let `R_z` count edges inside
`B` of the four-regular canonical relation `B_z`. That relation
contains every sharp edge. Its block counts are

\[
\#(A\mathrel{B_z}B)=\#(B\mathrel{B_z}A)=K,
\]

\[
\#(T\mathrel{B_z}A)=\#(A\mathrel{B_z}T)=4a-K,
\]

\[
\#(T\mathrel{B_z}B)=\#(B\mathrel{B_z}T)=4b-K-R_z.
\]

The central/top blocks each have twenty edges. Counting all
auxiliary edges out of `T` and using (1) therefore gives

\[
\#(T\mathrel{B_z}T)=-72+8d+2K+R_z.                 \tag{3}
\]

A top auxiliary row contains at most one top output. Indeed the
[ordered-degree bound](1485_auxiliary_ordered_degree_bound.md)
requires a degree-twelve output to have three strictly lower-degree
members in that four-element row. By (2), only the `10+2d` tops
with central successor count one can have such an output. Equation
(3) consequently gives

\[
\boxed{72-8d\le2K+R_z\le82-6d.}                   \tag{4}
\]

There is a further rowwise lower bound. For every top `u` with
`|C_u|=1`, a least noncentral member of `u*Col(z)` has degree
at most `4+3=7`. Its degree must therefore be six. Each such
row contributes at least one auxiliary edge into `A`, proving

\[
\boxed{4a-K\ge10+2d.}                             \tag{5}
\]

These inequalities hold for every central parameter separately;
no parameter independence is assumed. They do not currently
exclude any of the three central-moment cases in (1). A subsequent
[finite profile check](1485_order_forty_eight_five_central_d2.md)
does exclude `d=2`, using the mandatory-output condition behind (5).
The cases `d=0,1` remain open.

## 3. Finer rowwise capacities

Suppose `S=u*Col(z)` contains a top member `t`. Section 1
gives `|C_u|=1`. Section 2 supplies at least one degree-six
member, and there cannot be another top member by the
ordered-degree bound. Thus `S` contains one or two members of
`A`; denote their sharp counts by `k_1,…,k_l`, with `l=1`
or `2`. All other noncentral members, except `t`, lie in `B`.

The central fiber has four top points. Each `A` fiber has
exactly `4−k_i` top points, and each other noncentral fiber
has at least one. Applying the
[exact fiber-capacity inequality](1485_top_row_fiber_capacity.md)
to the twelve-element row of `t` gives

\[
\boxed{|\operatorname{TopSucc}(t)|
       \ge3+\sum_{i=1}^{l}(3-k_i).}                  \tag{6}
\]

For example, an accompanying sharp-count-one member of `A`
forces `t` to have five top successors. If there are two `A`
members, their sharp counts sum to at least four. These are
pointwise restrictions, not just averages over the top class.

There is a complementary rigidity statement in rows with
`|C_u|=2`. If `S` has no member of `A`, its two noncentral
members both lie in `B`, since Section 1 forbids a top member.
Let `b` be either of them. For a non-top `x∈Row(b)`, fixed-set
closure gives `u*x∈S`. If `u*x≠b`, strict descent makes its
degree smaller than eight. It would therefore be central, which
is impossible for a non-top input. Hence every non-top successor
of `b` lies in its own four-element fiber under `L_u`.

That fiber has a top input from `Col(z)`, so `b` has at most
three non-top successors. Since its degree is eight and every
vertex has at most five top successors, equality is forced:

\[
\boxed{|\operatorname{TopSucc}(b)|=5,
\qquad |T\cap L_u^{-1}(b)|=1.}                       \tag{7}
\]

The dual assertions hold for predecessor counts. Thus a
central-count-two top row without a degree-six output can only
use degree-eight outputs at the maximum possible top-successor
count.

In the `d=1` case, if the four double predecessor blocks share
a central vertex and the four double successor blocks share a
central vertex, a weighting argument makes every top profile
have size four. The
[constant-profile restriction](1485_order_forty_eight_constant_top_profiles.md)
then gives the sharper analytic class bound `9≤|A|≤14`.
This is conditional on those block families being stars; it is
not yet known for every `d=1` tiling.
