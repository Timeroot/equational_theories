# Three central vertices require degree five

Research note, 19 September 2026. This is an analytic necessary
condition for finite E1485 magmas, not a Lean declaration.

**Theorem.** If the minimum translation degree is three and there are
exactly three central vertices, degree five occurs. Degree four already
occurs, so such a hypothetical model has order divisible by sixty.

The proof excludes the entire degree-five-absent branch. It does not
exclude the branch in which degree five is present.

Write `Z,T,A,B` for the central, top, degree-four, and reciprocal
degree-`n/4` classes. We use the established facts that `|Z|=3`,
`|T|=9`, every vertex has three top neighbors in each direction,
and every member of `A` has one sharp neighbor in each direction.
The [degree-four theorem](1485_three_central_minimum_top_output.md)
gives `A≠∅`, and the [saturated-class exclusion](1485_three_central_saturated_four.md)
gives `|A|≤8`.

The order is divisible by twelve. Order twelve is already excluded
by the two-degree theorem, so the classes used here are distinct and
degree-four vertices are not top.

Suppose throughout the proof that degree five is absent.

## 1. Each central-column triple has a degree-four output

Fix `u∈T` and `z∈Z`. The three outputs of `L_u` on `Col(z)`
are distinct: equality of two outputs would give two good middles
from that output to the central endpoint `z`. Exactly one output
is central. Write the three-element output set as `S`, and put
`t=z*u∈T`.

E1485 gives `t*a=u` for all `a∈S`. The top fiber `L_t^{-1}(u)`
has size three, so it is exactly `S`. The fixed-parameter set

\[
F_t(u)=\{x:t*(u*x)=u\}=L_u^{-1}(S)
\]

has nine elements, and contains `Row(a)` for each `a∈S`.

The two noncentral outputs cannot both have degree at least six.
Choose one, `a`, of smaller degree. Its at least three non-top
successors lie in `F_t(u)`. For such a successor `x`, the product
`u*x` lies in `S` and has degree at most `d(a)`. It cannot be the
other noncentral output, by strict middle-degree descent, and cannot
be central: a top fiber at a central output is entirely top. Thus
all those non-top successors map to `a` under `L_u`, as does the
original top input. This exceeds its three-element fiber.

By absence of degree five, one output is therefore in `A`. If the
other output is `c`, its non-top successors can map only to that
degree-four output or to `c`. The degree-four output's top fiber
has exactly one non-top input; the fiber at `c` has at most two,
because it already has a top input. Hence `d(c)-3≤3`, or `d(c)≤6`.

Consequently every noncentral top product has degree four or six,
and the two noncentral outputs in every central-column triple
cannot both have degree six. The dual statements hold for rows.

There are 27 such triples, each supplying a degree-four top-product
cell. Each degree-four vertex accounts for six cells. Thus

\[
6|A|\ge27,\qquad |A|\ge5.
\]

## 2. The missing degree-four profiles form a partial matching

Let `F,G:A→B` be the sharp successor and predecessor maps. They
are surjective, and sharp two-path uniqueness gives `|A|≤|B|²`.
Thus `|B|≥3`. The established
[opposite-parity profile argument](1485_three_central_saturated_four.md#the-saturated-profile-grid)
applies: top predecessor profiles of `A` belong to one family of
three permutation transversals `P_p`, and top successor profiles
belong to the opposite-parity family `Q_q`. Put `t_pq=P_p∩Q_q`.
At most one degree-four vertex occupies each profile cell `(p,q)`.

No row of this profile grid can have two missing cells. If it did,
fix a top predecessor `u` in that row's transversal. Choose the
central-column triple whose centrally valued input belongs to the
third `Q`-profile. Its other two inputs belong to the two missing
profiles, so both products would have degree six, contradicting §1.
Dually there cannot be two missing cells in one column.

Thus the missing cells form a partial matching. Since `|A|≤8`,
there is at least one missing cell. Every noncentral endpoint pair
in its `3×3` top rectangle has a degree-six product. Only six
endpoint pairs in that rectangle are noncentral.

## 3. Six-point packing around one missing cell

Fix any missing cell and give it profile indices `(0,0)`. Use
coordinates over `F_3` in which the central successor and predecessor
labels of top vertices are

\[
C(t_{pq})=p+q,\qquad
H(t_{pq})=\varepsilon(p-q)+\delta,
\quad \varepsilon\in\{1,-1\}.
\]

Such coordinates exist because the two central-label arrays are
orthogonal Latin squares of order three. The offset `δ` is retained;
no normalization of it is assumed.

Define

\[
u_x=t_{0x},\qquad
\beta_y=\varepsilon(y-\delta),\qquad
w_y=t_{\beta_y,0}.
\]

Then `C(u_x)=x`, `H(w_y)=y`. The noncentral pairs in the missing
rectangle are exactly `(u_x,w_y)` with `x≠y`.

Let `c=u_x*w_y`, so `d(c)=6`, and put

\[
e=\varepsilon(y-x)\ne0.
\]

The central column `Col(z_{\beta_y})` contains `w_y`, one
centrally valued input, and one input whose product with `u_x` is
the degree-four vertex `a_0e`. That vertex exists because row zero
has only one missing cell. Write `b_e=F(a_0e)`.

The nine-element fixed-parameter set used in §1 contains the central
row with label `x`, the central column with label `β_y`, and
`Row(a_0e)=Q_e∪{b_e}`. Its known top points are exactly the
six-element set

\[
S(x,y)=\{t:H(t)=x\}\cup\{t:C(t)=\beta_y\}\cup Q_e.
                                                        \tag{1}
\]

Indeed the first two lines intersect once, while `Q_e` meets each
once at different points and contributes one further point. The row
of `c` lies in the same fixed-parameter set and has three non-top
elements. Those exhaust its remaining three positions. Therefore

\[
TopSucc(c)\subseteq S(x,y),\qquad b_e\in Row(c).
                                                        \tag{2}
\]

The dual argument, using the other noncentral input in the central
row containing `u_x`, gives

\[
b'_f:=G(a_{f0})\in Col(c),\qquad f=y-x.
                                                        \tag{3}
\]

Here `a_f0` exists because column zero also has only one missing
cell. Formula (3) follows directly by writing that companion input
as `t_(f,f+x)`; the nonzero alternative to the central input is
`f=y-x`.

## 4. A degree-six output has at most one good pair in a missing cell

From (1),

\[
S(x,y)\cap Q_0=\{w_x,w_y\}.
\]

The pair `(u_x,w_x)` is central. Thus no second good pair for `c`
in this rectangle can share the same left endpoint. The dual argument
excludes sharing a right endpoint.

If two good pairs existed, the two crossed pairs would also be paths
through `c`. Any noncentral crossed pair has degree-six product,
so strict descent forces that path to be good, violating the preceding
one-per-row or one-per-column conclusion. Hence both crossed pairs
must be central. The original pairs are therefore `(x,y)` and
`(y,x)` in the displayed central labels.

Let `z` be the third label. The top successors of `c` would include
`w_x,w_y`, and a third point with central successor label `β_z`.
That point must lie in both `S(x,y)` and `S(y,x)`. On the column
`C=β_z`, these memberships require either

\[
H=x,\ q=-e,
\qquad\text{or}\qquad
H=y,\ q=e.
\]

But on that column `H=z+εq`. The first alternative forces `z=y`
and the second `z=x`, both impossible. This excludes two good pairs.

This argument applies to every missing profile cell, not just the
one used to introduce the coordinates.

## 5. The other two top successors are inactive

For `c=u_x*w_y`, there can be no additional top predecessor of
`c` in `P_0`. Such a predecessor would have no good top extension:
row zero has only one missing cell, and §4 already accounts for its
one possible good pair there. Its three-element fiber at `c` would
therefore consist of all three non-top successors of `c`, including
`b_e` from (2). Yet every `u∈P_0` satisfies `u*b_e=a_0e`, by the
sharp edge `a_0e⇒b_e`. This is a contradiction.

Dually (3) shows there is no additional successor of `c` in `Q_0`.
Thus `TopSucc(c)∩Q_0={w_y}`.

Its other two successors, with central successor labels `β_x,β_z`,
must both belong to `Q_e`. To see this directly from (1), on column
`β_x` the option `H=x` is the forbidden additional point `w_x`,
so `q=e` is forced. On column `β_z`, the option `H=x` itself
gives `q=ε(x-z)=ε(y-x)=e`.

Neither of these two `Q_e` successors can participate in any good
top pair with middle `c`. If it did, that pair would be in a missing
cell of column `e`; applying the preceding paragraph to that cell
would say that `c` has exactly one successor in `Q_e`, whereas it
has two. If column `e` has no missing cell, inactivity is immediate.

Consequently `c` has exactly one good ordered top pair globally.

## 6. Three distinct outputs cannot fit into the same top fiber

Fix either nonzero `e`. The three pairs

\[
(u_x,w_{x+\varepsilon e}),\qquad x\in F_3,
\]

give three distinct degree-six outputs, by §5. They all have the
same non-top predecessor

\[
b'=G(a_{\varepsilon e,0})
\]

from (3). Each output has two inactive successors in the same
three-element set `Q_e`.

For such an inactive successor `v`, the fiber `R_v^{-1}(c)` has
size three and contains no top input. It therefore consists of all
three non-top predecessors of `c`, in particular `b'`. Hence
`b'*v=c`.

The two-element successor sets for two of the distinct outputs must
intersect inside `Q_e`. Their intersection would be mapped by `L_b'`
to both outputs, a contradiction. This completes the exclusion of
the degree-five-absent branch.
