# Order twenty-four cannot have six central vertices at minimum degree three

Research note, 18 September 2026. This is a pen-and-paper exclusion,
not a finite enumeration or a Lean declaration.

**Theorem.** No E1485 magma of order 24 and minimum translation degree
three has exactly six central vertices.

Use the finite degree, centrality, sharp-neighbor, and uniform-fiber
theorems, together with the
[small-central incidence restrictions](1485_order_twenty_four_small_central.md).
Write `Z,A,B,T` for the degree classes `3,4,6,8`, of sizes
`6,f,g,h`, respectively. Those restrictions leave `h=9` or `h=10`.

## Degree-four vertices have sharp degree one

For any vertex `x`, the map

\[
 Z\longrightarrow\operatorname{TopSucc}(x)\times
                   \operatorname{TopPred}(x),
 \qquad z\longmapsto(x*z,z*x)
\]

is injective: both factors are top, and centrality recovers
`z=(x*z)*(z*x)`. Thus

\[
 6\le |\operatorname{TopSucc}(x)|\,
       |\operatorname{TopPred}(x)|. \tag{1}
\]

A degree-four vertex has neighbors only in `B` and `T`; its `B`
neighbors are precisely its sharp neighbors. Reciprocal-degree balance
makes its sharp in-degree and out-degree equal, and hence its top
in-degree and out-degree equal as well. Existence of sharp neighbors
bounds this common top degree by three. Inequality (1) forces it to
be three, so every `A` vertex has exactly one sharp neighbor in each
direction. Consequently `g≤f`.

For a top vertex `t`, write `k_t^-`, `k_t^+` for its central
predecessor and successor counts, and `α_t` for its number of `A`
successors. Central incidence gives

\[
 \sum k^- =\sum k^+=18,
 \qquad \sum k^-k^+=36,
 \qquad 1\le k^-,k^+\le3. \tag{2}
\]

Each central output of `L_t` consumes three top inputs. Each `A`
output consumes two top inputs, its third input being its sharp `B`
successor. Summing these counts gives

\[
 54+6f\le h^2. \tag{3}
\]

If `h=9`, then `f+g=9` and `g≤f` give `f≥5`, contrary to
`54+6f≤81`. Hence `h=10` and `f+g=8`.

## Four vertices in each middle degree class

Put `u_t=k_t^-−1`, `v_t=k_t^+−1`, so both belong to `{0,1,2}`.
Equation (2) gives

\[
 \sum u=\sum v=8,\qquad\sum uv=10. \tag{4}
\]

The local top-input bound is `3k_t^++2α_t≤10`, or equivalently

\[
 \alpha_t\le3-v_t-\mathbf1_{v_t=2}. \tag{5}
\]

Every `A` vertex has three top predecessors, whose `k^-` weights
sum to six. Therefore `Σα=3f`, `Σk^-α=6f`, and `Σuα=3f`.
Multiply (5) by `u_t` and sum to obtain

\[
 3f\le14-\sum_{v_t=2}u_t\le14.
\]

Since `f+g=8` and `g≤f`, we get `f=g=4`. In particular

\[
 \sum_{v=2}u\le2,
 \qquad \sum_{u=2}v\le2, \tag{6}
\]

where the second inequality is the column-dual argument.

## Exactly two central profiles remain

Let `x,a,b,c` count the respective `(u,v)` types
`(2,2),(1,2),(2,1),(1,1)`. Then (4)--(6) give

\[
 a+2x\le2,\qquad b+2x\le2,
 \qquad c+2a+2b+4x=10. \tag{7}
\]

Thus `x` is zero or one. If `x=1`, then `a=b=0`, `c=6`.
Those seven vertices already exhaust the two marginal sums in (4);
the remaining three have `(u,v)=(0,0)`.

If `x=0`, then `c=10−2a−2b`. The `u` marginal gives
`8≥c+a+2b=10−a`, so `a≥2`; by (7), `a=2`.
Dually `b=2`, and then `c=2`. Again the marginal sums are exhausted,
leaving four vertices of type `(0,0)`.

In terms of `(k^-,k^+)`, the complete alternatives are

| Profile | Top types and multiplicities |
| --- | --- |
| I | four `(1,1)`, two `(2,2)`, two `(2,3)`, two `(3,2)` |
| II | three `(1,1)`, six `(2,2)`, one `(3,3)` |

This exhaustion uses only the displayed inequalities, not a search.

## Profile II overlaps its large rectangle

For any top `t`, let `R_t,C_t⊆Z` be its central predecessor and
successor sets. The rectangles `R_t×C_t` partition `Z×Z`, and
`|C_t∩R_s|≤1` for every pair of top vertices.

Every central row has three top neighbors with successor weights
summing to six, hence weight pattern `(1,2,3)` or `(2,2,2)`.
The dual statement holds for columns.

In profile II, let `R×C` be the unique three-by-three rectangle.
Each of the three rows in `R` contains the weight-three top vertex
and therefore has pattern `(1,2,3)`. Each needs a singleton rectangle.
The three `(1,1)` vertices consequently have all their predecessor
points in `R`. Dually all their successor points lie in `C`.
Their singleton rectangles would lie inside the already occupied
rectangle `R×C`, a contradiction.

## Profile I forces a particular rectangle arrangement

Call the two `(2,3)` vertices `U_1,U_2`, and write their central
rectangles as `R_i×W_i`, where `|R_i|=2`, `|W_i|=3`.
Call the two `(3,2)` vertices `V_1,V_2`, with rectangles
`T_j×S_j`, where `|T_j|=3`, `|S_j|=2`.

No central row can contain two successor weights three. Thus `R_1,R_2`
are disjoint, and leave a two-element set `O` in `Z`. Dually `S_1,S_2`
are disjoint and leave a two-element set `N`.
The four singleton rectangles have distinct predecessor points, exactly
`R_1∪R_2`, and distinct successor points, exactly `S_1∪S_2`: these
are the four rows and four columns whose weight pattern contains a three,
and hence also a one.

Consider the two-by-two incidence matrix
`X_ij=1` when `R_i∩T_j` is nonempty. Each column is nonempty,
because a three-element `T_j` cannot lie inside `O`.
Each row has at most one entry: if `R_i` met both `T_1,T_2`, rectangle
disjointness would force `W_i` to avoid both `S_1,S_2`, leaving it
inside the two-element set `N`. Thus `X` is a permutation matrix.
Relabel so that its diagonal entries are one.

Put `a_i=|R_i∩T_i|≥1`. Rectangle disjointness gives `W_i∩S_i=∅`,
so `b_i=|W_i∩S_{3-i}|≥1`. Each row in `R_i∩T_i` has one singleton
rectangle, whose successor must lie in `S_{3-i}\W_i`.
Those singleton successor points are distinct, so

\[
 1\le a_i\le2-b_i\le1.
\]

Hence `a_i=b_i=1`. Write `R_i={e_i,f_i}`, with
`R_i∩T_i={e_i}`. Then

\[
 T_i=O\cup\{e_i\},\qquad
 W_i=N\cup\{c_{3-i}\},\qquad S_i=\{c_i,d_i\}.
 \tag{8}
\]

The symbols in each of the two decompositions
`Z=O⊔{e_1,f_1,e_2,f_2}` and
`Z=N⊔{c_1,d_1,c_2,d_2}` are distinct. These decompositions need
not use the same labels for their underlying central elements.

Each row of `O` already lies in both `V` rectangles, which cover
`S_1∪S_2`; its third rectangle must have successor pair `N`.
Every column of `N` already lies in both `U` rectangles, which cover
`R_1∪R_2`. Therefore that two-by-two rectangle is exactly `O×N`.

The remaining two-by-two rectangle has predecessor set `{f_1,f_2}`:
those two rows belong to no `V` rectangle and require a weight-two
rectangle besides their `U` and singleton rectangles. Dually its
successor set is `{d_1,d_2}`. The six nonsingleton rectangles are
therefore forced to have these sides:

| Top vertex | Central predecessor set | Central successor set |
| --- | --- | --- |
| `U_1` | `{e_1,f_1}` | `N∪{c_2}` |
| `U_2` | `{e_2,f_2}` | `N∪{c_1}` |
| `V_1` | `O∪{e_1}` | `{c_1,d_1}` |
| `V_2` | `O∪{e_2}` | `{c_2,d_2}` |
| first `(2,2)` | `O` | `N` |
| second `(2,2)` | `{f_1,f_2}` | `{d_1,d_2}` |

## Eight pairs cannot avoid eight other pairs on six points

Count unordered pairs of distinct central elements that occur together
in at least one predecessor set from this table. Writing `O={o_1,o_2}`,
they are

\[
 \{o_1,o_2\},\quad\{f_1,f_2\},\quad
 \{e_1,f_1\},\quad\{e_2,f_2\},\quad
 \{o_j,e_i\}\ (i,j\in\{1,2\}).
\]

These are eight distinct pairs. Dually, the successor sets contain
eight distinct pairs: the pair inside `N`, the pair `{d_1,d_2}`,
the two pairs `{c_i,d_i}`, and the four pairs consisting of one
element of `N` and one `c_i`.

There are only `binom(6,2)=15` unordered pairs in the common central
set. The two collections of eight must intersect. Thus some distinct
central elements lie together in a predecessor set `R_t` and in a
successor set `C_s`. This gives `|C_s∩R_t|≥2`, or two central
middles between the same top endpoints, contrary to unique goodness.

Both profiles have been excluded. Together with the earlier top-size
reduction, this proves the theorem.
