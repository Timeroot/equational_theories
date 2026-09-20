# Eight central elements with ten degree-five elements

Research note, 20 September 2026. These are independently audited
analytic restrictions, not an exclusion of the whole eight-central-element branch. No
enumeration, SAT premise, or Lean declaration is used.

Assume order forty, minimum degree four, `|Z|=8`, and `|A|=10`,
where `Z,T,A,B` denote the degree classes `4,10,5,8`. Put
`h=|T|`, `b=|B|`, and let `q` count the degree-five vertices
with top-profile size three. The other `10−q` have size four.
All central blocks have size at most three by the
[full-block theorem](1485_order_forty_ten_central_full_blocks.md).

**Theorem.** The only cases not excluded by this note are

\[
\boxed{h=15,\ b=7,\ 6\le q\le9,
\qquad\text{or}\qquad
h=16,\ b=6,\ 0\le q\le8.}
\]

These are necessary possibilities, not constructions.

## 1. A two-fold central cover

For a top `u`, write `α_u=#(Row(u)∩A)`, and define

\[
w_u=7-2|C_u|-\alpha_u.
\]

The [degree-five edge-support bound](1485_order_forty_eight_central_high_five.md#1-central-parameter-capacity-excludes-twelve-degree-five-elements)
gives `α_u≤4,3,1` for `|C_u|=1,2,3`, respectively. Thus
`w_u≥0`, and `w_u≥1` whenever `|C_u|=1`.

Every central row contains four tops, its `C` blocks sum to eight,
and its `α` values sum to ten. Therefore its `w` values sum to
`28−16−10=2`. Each top occurs in a central row, so

\[
0\le w_u\le2,\qquad
\sum_{u\in T}|P_u|w_u=16.
\tag{1}
\]

Since `Σ|C_u|=32` and `Σα_u=40−q`,

\[
L:=\sum_{u\in T}w_u=7h-104+q.
\tag{2}
\]

The dual weights `w_u^-`, defined using predecessor counts and
`P_u`, have the same total `L`, satisfy `Σ|C_u|w_u^-=16`,
and are at least one whenever `|P_u|=1`.

From `1≤|P_u|≤3` and (1),

\[
6\le L\le16.
\]

Since `0≤q≤10`, (2) leaves only `h=15,16,17`. For `h=16`
it gives `q≤8`, and for `h=17` it gives `q≤1`.

## 2. Seventeen tops are impossible

Suppose `h=17`. Put `ε=1−q∈{0,1}`. The two weighted slacks
are

\[
\sum(|P_u|-1)w_u
=\sum(|C_u|-1)w_u^-=16-L=\varepsilon.
\tag{3}
\]

Let `n_pc` count central block types. A type-`(3,1)` top has
`w_u≥1` and would contribute at least two to the first sum;
thus `n31=0`. Dually `n13=0`. A type-`(1,2)` top contributes
at least one to the dual sum, so `n12≤ε`.

The mixed central moment is

\[
n_{11}+n_{33}-n_{13}-n_{31}
=\sum(|P|-2)(|C|-2)=4h-64=4.
\]

Hence `n11≤4`, and the total number of singleton `P` blocks is
`n11+n12≤4+ε=5−q`.

On the other hand, tops with `|P_u|>1` carry total `w` weight at
most `ε`, by (3). Singleton `P` blocks therefore carry weight
at least `L−ε=14+2q`. Since each `w_u≤2`, there must be at
least `7+q` singleton `P` blocks. This contradicts `5−q` and
excludes seventeen tops.

## 3. The weighted top-pair budget at fifteen tops

Let `F` count top pairs with output in `B∪T`, and let `W`
count all auxiliary edges `T→B∪T`, summed over central parameters.
The [weighted counting argument](1485_order_forty_eight_central_high_five.md#4-weighted-top-pairs-exclude-the-last-three-cases)
gives

\[
F=h^2-248+6q,\qquad W=8(4h-62+q),\qquad F\le W\le3F.
\]

At `h=15`, the upper bound is

\[
8q-16\le18q-69,
\]

so `q≥6`.

## 4. Ten size-three profiles force an impossible sharp matrix

Suppose `h=15,q=10`. Then `b=7`, and every member of `A`
has exactly two sharp predecessors and two sharp successors in `B`.
For `x∈B`, let `j_x^-`, `j_x^+` count its sharp `A` neighbors.
Let `C_xy` record whether `x*y∈A`, equivalently whether there
is a two-sharp-edge path from `x` to `y` through `A`.

Good-middle uniqueness makes `C` zero-one. Each sharp `A`
neighbor of `x` supplies two distinct endpoints, and different
neighbors supply disjoint endpoints. Thus the row and column sums
of `C` are `2j_x^+` and `2j_x^-`. In particular `j_x^±≤3`.
Their totals are both twenty, so each direction has six threes
and one two.

Let `I_x,O_x` be the top-neighbor counts. Central shadow counting
gives `I_x,O_x≥3`, and reciprocal-neighbor balance gives

\[
3(j_x^+-j_x^-)=O_x-I_x.
\]

If one sharp count were three and the other two, the corresponding
top-count difference would be three. But the side with sharp count
three has at most five top neighbors, while the other side has at
least three. This is impossible. Hence the sharp counts balance
pointwise: there are six high vertices of sharp count three and one
low vertex of sharp count two.

The set `A` is independent. For any ordered pair of high vertices,
the [return-matching bound](1485_general_return_matching.md#2-an-independent-set-bound-including-the-equality-case)
gives `6≤40/d(x*y)`. A central output is impossible for these
endpoints, and degrees eight and ten would give bounds five and
four. Thus every high-high product lies in `A`.

The matrix `C` is therefore all ones on the six-by-six high block.
Each high row and column has degree six and is saturated there.
The remaining low row would have to have degree four, but can only
meet the single low column. This contradiction excludes `q=10`,
completing the theorem.
