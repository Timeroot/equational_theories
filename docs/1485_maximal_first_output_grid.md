# Maximal first-output grids: a short top-count interval and a small exceptional class

Research theorem, 20 September 2026. This is a general analytic finite
restriction, independently audited, not an enumeration or a proof of
the full spectrum conjecture. No SAT refutation or Lean declaration
is used here.

Let a finite E1485 magma have minimum degree `r=t+1`, with `t≥3`,
and exactly `m=t²` central elements. Suppose its first noncentral
top-product degree is `r+1=t+2`, and at least one such vertex has
exactly `t` top predecessors and `t` top successors. Write `T` for
the top class and `h=|T|`.

**Theorem.** Under these hypotheses:

\[
       \boxed{(t+1)^2\le h\le t^2+3t+1,
              \quad\text{equivalently }r^2\le h\le r^2+r-1.} \tag{1}
\]

Moreover, among degree-`t+2` vertices there are at most four whose
top predecessor/successor counts equal `t`; for `t≥5` there are
at most three. Thus the smaller-profile exceptional class has size
at most four for `r=4,5`, and at most three for every `r≥6`.

For `t=3`, the theorem gives `16≤h≤19` and at most four degree-five
vertices of top-profile size three. The
[nine-central refinements](1485_nine_central_three_profile.md) and the
[checked eighteen-top exclusion](1485_nine_central_eighteen_top.md)
sharpen the top count to sixteen or seventeen in that particular case.

## 1. Central blocks and the chosen grid

For a top vertex `u`, put `P_u=Col(u)∩Z` and `C_u=Row(u)∩Z`.
They are nonempty, every central label belongs to `r` blocks in
each direction, and the rectangles `P_u×C_u` partition `Z×Z`.
Central-middle uniqueness gives

\[
                       |C_u\cap P_v|\le1.                \tag{2}
\]

Fix a degree-`t+2` vertex `a` with top profiles `U,V` of size
`t`. The [first-output profile theorem](1485_first_successor_degree_profiles.md)
says that `P_U,C_V` partition `Z`, every global central block has
size at most `t`, and `K[U,V]`, with entries `K_uv=|C_u∩P_v|`,
is a permutation matrix. Since `|Z|=t²`, all the blocks in these
two partitions have size exactly `t`. They give a full `t` by `t`
grid on `Z`.

Relabel `U={u_i}` and `V={v_i}` so that `K_(u_i,v_i)=1`.
The top inputs with `u_i*v=a` are exactly `V∖{v_i}`.
The [exact auxiliary-membership identity](1485_central_parameter_components.md)
therefore says that the blocks indexed by

\[
                         X_i=\{w\in T:w*a=u_i\}
\]

disjointly tile `Z∖C_(v_i)` by their `P_w`. Each has size at
most `t−1`: it meets every grid column in at most one point and
avoids column `i`. The index sets `X_i` are pairwise disjoint.
Writing `X=⋃X_i`, their blocks cover every central point exactly
`t−1` times, and

\[
                  |X|\ge t^2,
       \qquad\sum_{w\in X}|P_w|=t^2(t-1).              \tag{3}
\]

Dually there are disjoint tilings `Y_j={w:a*w=v_j}` of the
row complements by small `C`-blocks, with `|Y|≥t²`.

## 2. The maximal blocks cover once or twice

Let `p` be the number of global `P`-blocks of size `t`, and
`q` the number of `C`-blocks of size `t`. Equation (3) uses only
smaller blocks. Since the total `P`-weight is `(t+1)t²`,

\[
                           t\le p,q\le2t.               \tag{4}
\]

There is a pointwise strengthening. The index sets `X,U` are
disjoint, because their blocks are respectively smaller than `t`
and of size `t`. Their blocks cover every point `(t−1)+1=t`
times. All the remaining `P`-blocks consequently partition `Z`,
as the total central valency is `t+1`. Among this remaining
partition, let the small blocks tile `E⊆Z`. All maximal blocks
then have combined pointwise multiplicity

\[
          2-\mathbf1_E,\qquad |E|=t(2t-p).              \tag{5}
\]

Dually the maximal `C`-blocks have multiplicity `2−1_F`, where
`|F|=t(2t−q)`. Thus the `q` by `p` intersection matrix of
maximal `C`-blocks against maximal `P`-blocks has exactly

\[
                        \boxed{(2t-p)(2t-q)-|E\cap F|}   \tag{6}
\]

zero entries: subtract `Σ_z(2−1_E(z))(2−1_F(z))` from `pq`.
This formula uses only central uniqueness and the exact auxiliary
tilings; no alignment of other blocks with grid rows or columns
is assumed.

## 3. The strict interval for the top count

Put `α_u=t−|P_u|, β_u=t−|C_u|`, both between zero and `t−1`.
The central incidence moments give

\[
 \begin{split}
 \sum\alpha_u=\sum\beta_u&=th-(t+1)t^2,\\
 \sum\alpha_u\beta_u&=t^2(h-t^2-2t).
 \end{split}                                           \tag{7}
\]

Nonnegativity and `αβ≤(t−1)α` first give

\[
                         t^2+2t\le h\le2t^2+t.
\]

At the lower endpoint the product sum in (7) is zero. Every top
then has a maximal `P`-block or a maximal `C`-block, so the
small-block index sets `X,Y` are disjoint. Equation (3) would
give `h≥2t²`, whereas `t²+2t<2t²` for `t≥3`. This excludes
the lower endpoint.

To obtain the stronger upper bound, call a block size *intermediate*
if it lies in `2,...,t−1`. For `1≤i,j≤t`, define

\[
 \begin{split}
 D(i,j)&=(t-i)(j-1)+(t-j)(i-1),\\
 W(i,j)&=i\,\mathbf1_{2\le j\le t-1}
             +j\,\mathbf1_{2\le i\le t-1}.
 \end{split}
\]

The elementary pointwise inequality is

\[
                  (t-2)W(i,j)\le(t-1)D(i,j).             \tag{8}
\]

Here is an explicit verification. If neither size is intermediate,
`W=0`. If one is intermediate and the other equals one, the slack
is at least `(t−1)²−(t−2)>0`; if the other equals `t`, it is at
least `(t−1)²−t(t−2)=1`. If both are intermediate, the slack is
bilinear on `[2,t−1]²`, so its minimum is at a corner. Its values
at `(2,2)`, `(2,t−1)` and `(t−1,t−1)` are respectively

\[
 2(t-2)(t-3),\quad (t-3)(t^2-3t+1),\quad0;
\]

the fourth corner is symmetric. All are nonnegative for `t≥3`.

Let `L=Σ_(|P_u|=t)|C_u|` and `R=Σ_(|C_u|=t)|P_u|`. By (4),
`L+R≤t(p+q)≤4t²`. In a central row let `k,j,l` count the
maximal, intermediate, and singleton `C`-blocks. They partition
`t²` points and `k+j+l=t+1`, so

\[
 t^2\le kt+(t-1)j+l,
 \qquad (t-2)j\ge t^2-t-1-(t-1)k.
\]

Sum this over the central rows and dually over the columns.
The total number of intermediate occurrences is `Σ_u W(|P_u|,|C_u|)`,
whereas the total maximal occurrences are `L+R`. Thus

\[
 (t-2)\sum W\ge2t^2(t^2-t-1)-(t-1)(L+R)
                  \ge2t^2(t^2-3t+1).                  \tag{9}
\]

Put `δ=2t²+t−h`. The central moments give `ΣD=2tδ`.
Combining (8) and (9) yields

\[
 \delta\ge\frac{t(t^2-3t+1)}{t-1}
       =t^2-2t-\frac{t}{t-1}.
\]

Since `δ` is integral and `t≥3`, we get `δ≥t²−2t−1`, or
`h≤t²+3t+1`. Together with the strict lower bound this proves (1).

## 4. A class of at most four, or at most three

Let `\mathcal A` be the degree-`t+2` vertices with top-profile
size `t`, and let `a=|\mathcal A|`. Each has a permutation
central matrix and exactly `t(t−1)` good top endpoint pairs.
Indeed degree `r+1` is the least noncentral degree, and the
[least-degree fiber count](1485_unrestricted_central_incidence.md#the-least-noncentral-degree-has-balanced-sharp-counts)
gives sharp degree two and `t(t−1)` top representations. Every
bad top path through one of these vertices has a central
replacement, giving exactly its permutation-matrix complement.

Every central row contains a top with maximal `C`-block: otherwise
its `t+1` blocks cover at most `(t+1)(t−1)=t²−1` points.
Dually every central column contains a top with maximal `P`-block.
Thus the `P`-blocks indexed by maximal `C`-blocks cover `Z`, and
the `C`-blocks indexed by maximal `P`-blocks also cover `Z`.

For `z∈Z`, let `λ_z` and `μ_z` be these two cover multiplicities.
Both are at least one, and their sums are `L,R` from §3. The
number of centrally valued pairs in the rectangle with maximal
`P`-block sources and maximal `C`-block targets is exactly
`Σ_z λ_z μ_z`: uniqueness (2) prevents a pair from being counted
twice. Therefore this number is at least `L+R−t²≥t²`.

Every good pair representing `\mathcal A` lies in this same `p`
by `q` rectangle; different products have disjoint good pairs.
We obtain the sharper class-capacity formula

\[
       \boxed{a\,t(t-1)\le pq-L-R+t^2\le3t^2.}         \tag{10}
\]

In particular `a≤floor(3t/(t−1))`: at most four for `t=3,4`,
and at most three for `t≥5`. This proof needs no exceptional
small-case enumeration or combinatorial design argument.

These are conditional first-output restrictions. They do not assert
`|T|≥r²` for arbitrary central incidence systems, nor show that the
remaining four-or-fewer smaller profiles cannot coexist with
degree-`r+1` vertices having `r` top neighbors.
