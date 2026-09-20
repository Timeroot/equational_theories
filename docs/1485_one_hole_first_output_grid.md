# One-hole first-output grids have at most twice-minus-two maximal blocks

Independently audited analytic theorem, 20 September 2026. This is a necessary finite
E1485 restriction, not a full-core proof or a Lean theorem. No search
or SAT premise is used.

Let the minimum translation degree be `r=t+1`, where `t≥3`, and
suppose there are exactly `m=t²−1` central elements. Assume the
first noncentral top-output degree is `r+1=t+2`, and some such
output has exactly `t` top predecessors and `t` top successors.

Write `P_u,C_u` for the central predecessor and successor blocks
of a top. Let `p,q` count blocks of size `t` in the two directions.

**Theorem.**

\[
                     \boxed{t-1\le p,q\le2t-2.}          \tag{1}
\]

If both upper bounds are equalities, every size-`t` predecessor
block meets every size-`t` successor block exactly once. Moreover,
the central labels where the maximal predecessor blocks have total
multiplicity below two are disjoint from the analogous successor
deficiency set.

Writing `h` for the number of tops, the same hypotheses also give

\[
                  t^2+2t\le h\le t^2+4t-1.             \tag{4}
\]

For `t≥4` the lower bound improves to `t²+2t+1=r²`.

The degree-`r+1` class has at most twelve elements when `t=3`,
eleven when `t=4`, and `2t+2` when `t≥5`. At most seven have
the smaller top-profile size when `t=3`, and **at most four**
when `t≥4`; see §5. These bounds do not assume order forty.

At minimum four and eight central elements, a degree-five
three-profile therefore forces **at most four triple blocks in each
direction**, improving the earlier bound five. The triple-block
intersection statement applies when both counts equal four.

## 1. Maximal blocks cover each central label at most twice

Fix a first output `a` as in the hypotheses, with top profiles
`U={u_1,…,u_t}`, `V={v_1,…,v_t}`. By the
[first-output profile theorem](1485_first_successor_degree_profiles.md),
all central blocks have size at most `t`, the blocks `P_U,C_V`
partition the central set `Z`, and

\[
                   |C_{u_i}\cap P_{v_j}|=\mathbf1_{i=j}
\]

after matching the two indexings. Since the partitions have `t`
parts covering `t²−1` labels, each has `t−1` parts of size `t`
and one of size `t−1`. In particular `p,q≥t−1`.

Exactly as in the
[maximal-grid complement construction](1485_maximal_first_output_grid.md#1-central-blocks-and-the-chosen-grid),
the sets

\[
                         X_i=\{w\in T:w*a=u_i\}
\]

are pairwise disjoint and their `P_w` blocks disjointly tile
`Z\setminus C_{v_i}`. Each such block has size at most `t−1`:
it avoids one member of the `C_V` partition and meets each other
member at most once. Taken together, these small blocks cover every
central label exactly `t−1` times.

The total predecessor-block valency is `r=t+1`. Consequently the
maximal predecessor blocks have pointwise multiplicity

\[
         \lambda_z=\#\{u:|P_u|=t,\ z\in P_u\}\le2.
\]

Define `e_z=2−λ_z≥0`. Then

\[
                     \sum_z e_z=2(t^2-1)-tp.            \tag{2}
\]

The same statements hold dually, with multiplicity `μ_z` and
deficiency `f_z=2−μ_z`.

## 2. The disjoint maximal parts improve the cardinality bound

First `tp≤2(t²−1)` gives `p≤2t−1`. Suppose equality.
Then (2) gives `Σe_z=t−2`.

For any maximal successor block `C`, central-middle uniqueness
gives `|C∩P_u|≤1` for each of the `p` maximal predecessor
blocks. Therefore

\[
                 \sum_{z\in C}\lambda_z\le p,
                 \qquad \sum_{z\in C}e_z\ge2t-p=1.
\]

But the chosen partition `C_V` contains `t−1` disjoint maximal
blocks. They would require at least `t−1` units of deficiency,
more than the total `t−2`. This contradiction gives `p≤2t−2`.
The dual proof gives the bound for `q` and proves (1).

## 3. Simultaneous equality forces a complete intersection matrix

The total intersections between the two maximal-block families are

\[
 \begin{aligned}
 \sum_z\lambda_z\mu_z
 &=\sum_z(2-e_z)(2-f_z)\\
 &=2t(p+q)-4(t^2-1)+\sum_z e_zf_z.
 \end{aligned}
\]

Each pair intersects in at most one point, so this is at most `pq`.
Equivalently,

\[
            \sum_z e_zf_z\le(2t-p)(2t-q)-4.             \tag{3}
\]

If `p=q=2t−2`, the right side is zero. Thus the two deficiency
supports are disjoint, and the number of intersections is exactly
`pq`. Every pair of maximal blocks therefore meets exactly once,
as claimed.

## 4. A general top-count interval

Put `m=t²−1`. The exact central moments are

\[
 \sum P=\sum C=(t+1)m,\qquad\sum PC=m^2.
\]

Consequently

\[
 S:=\sum(t-P)(t-C)=t^2(h-t^2-2t)+2t+1\ge0.
\]

At least `h−p−q` tops have neither block maximal. Each contributes
at least one to `S`. Using the already proved `p,q≤2t−2` gives

\[
 S\ge h-p-q\ge h-4t+4,
 \qquad (t^2-1)h\ge t^4+2t^3-6t+3.
\]

Equivalently,

\[
                     h\ge t^2+2t+\frac{t-3}{t+1}.
\]

Integrality proves `h≥t²+2t` for `t=3` and the stronger
`h≥t²+2t+1=r²` for every `t≥4`. In particular the twenty-four-top
case at minimum five is excluded analytically, not by a finite check.

For the upper bound, define, for `1≤i,j≤t`,

\[
 \begin{aligned}
 D(i,j)&=(t-i)(j-1)+(t-j)(i-1),\\
 W(i,j)&=i\mathbf1_{2\le j\le t-1}
                   +j\mathbf1_{2\le i\le t-1}.
 \end{aligned}
\]

The [elementary block inequality](1485_maximal_first_output_grid.md#3-the-strict-interval-for-the-top-count)
is `(t−2)W≤(t−1)D`; the cited proof checks the boundary cases
and the four corners of the intermediate-size rectangle.

In a central row let `k,j,l` count maximal, intermediate, and
singleton successor blocks. They cover `m` labels with `t+1`
parts, so

\[
              (t-2)j\ge t^2-t-2-(t-1)k.
\]

Let `L=Σ_(P=t)C`, `R=Σ_(C=t)P`. Summing this inequality over
the central rows and columns and then applying the block inequality
gives

\[
 \begin{aligned}
 2m(t^2-t-2)-(t-1)(L+R)
 &\le(t-2)\sum W\\
 &\le(t-1)\sum D.
 \end{aligned}
\]

The already proved maximal-block bound gives `L+R≤t(p+q)≤4t(t−1)`,
while the moments give `ΣD=4(t+1)m−2th`. Substitution yields

\[
 \begin{aligned}
 2t(t-1)h
 &\le2t\big((t+1)m+2(t-1)^2\big),\\
 h&\le\frac{(t+1)(t^2-1)}{t-1}+2(t-1)
       =t^2+4t-1.
 \end{aligned}
\]

This proves (4). These intervals constrain the general one-hole
branch; they do not assert that any such non-full model exists.

## 5. Bounding the whole first-degree class and its smaller profiles

Let `A` be the degree-`r+1` class, `a=|A|`, and let `b` count
its elements with top-profile size `t`. All other elements of `A`
have profile size `t+1`. Indeed the least noncentral degree has
balanced top counts, the central grid bound makes their square at
least `t²−1`, and sharp-neighbor existence makes them at most `r`.

For a top `u`, put `α_u=|Row(u)∩A|`. A top-to-`A` auxiliary
edge has central support equal to `Z` minus one omitted block:
its top-input fiber contains all but one of the output's top
successors. Its support size is therefore at least `m−t`.
The `|C_u|` sharp central successors occupy an auxiliary slot at
every parameter, and every auxiliary relation is `r`-regular.
Consequently

\[
 \alpha_u\le f(|C_u|),\qquad
 f(c)=\left\lfloor\frac{(t^2-1)(t+1-c)}{t^2-t-1}\right\rfloor
     =t+1-c+\mathbf1_{c\le2}.                          \tag{5}
\]

For the last equality, write the fraction as
`t+1−c+t(t+1−c)/(t²−t−1)`. The second summand has floor
one for `c=1,2` and zero otherwise, for every `t≥3`.

In a central row the `α` values sum to `a`, and its `t+1`
successor blocks cover `m` labels. Thus (5) gives

\[
           a\le2t+2+\#\{\text{row blocks of size at most two}\}.
\]

Their total deficit from size `t` is `t(t+1)−m=t+1`.
Each block of size at most two costs at least `t−2`. Therefore

\[
               \boxed{a\le2t+2+
                      \left\lfloor\frac{t+1}{t-2}\right\rfloor.} \tag{6}
\]

There is a stronger global estimate when `t≥4`. In a central row
let `L` count blocks of size at most two and `k` count maximal
blocks. The `t+1−k` nonmaximal blocks cost at least one deficit
unit each, and the `L` small blocks cost at least `t−3` additional
units. Thus

\[
                t+1\ge(t+1-k)+(t-3)L,
                \qquad k\ge(t-3)L.
\]

The previous row estimate gives `L≥a−2t−2`. Meanwhile the total
number of maximal successor-block occurrences in central rows is
`Σ_(C=t)P≤tq≤2t(t−1)`. Sum over all `m=t²−1` rows to obtain

\[
 \begin{aligned}
 (t^2-1)(t-3)(a-2t-2)&\le2t(t-1),\\
 a&\le2t+2+\left\lfloor\frac{2t}{(t-3)(t+1)}\right\rfloor.
 \end{aligned}
\]

The floor is one at `t=4` and zero at every `t≥5`. Consequently
the whole class satisfies **`a≤11` at `t=4`**, and **`a≤2t+2`
at every `t≥5`**. Together with (6), this proves the class bounds
stated at the start of the note.

The exact moments for the smaller profiles are

\[
 \sum\alpha=(t+1)a-b,\qquad\sum P\alpha=(t^2-1)a,
 \qquad (t-1)b=\sum(P-t+1)\alpha.
\]

Only maximal predecessor blocks have a positive coefficient in the
last sum. Since `α≤t+1`, (1) gives

\[
              (t-1)b\le p(t+1)\le2(t-1)(t+1),
              \qquad b\le2t+2.                        \tag{7}
\]

When `t=3`, the nonnegative six-row potential from
[the eight-central profile argument](1485_order_forty_eight_central_six_three_profiles.md#1-a-nonnegative-local-potential)
has a proof of nonnegativity using only (5), and its exact sum is
`7(p+q)−8b`. Thus `p,q≤4` give `b≤7=2t+1` in this case
as well. This part does **not** use the later order-forty equality
contradiction in that note; no total-order hypothesis is imposed here.

For `t≥4`, the profile-matching condition gives a considerably
stronger bound, independent of the auxiliary capacity estimates:

\[
                 \boxed{b\le7\text{ if }t=3,
                        \qquad b\le4\text{ if }t\ge4.} \tag{8}
\]

Here is the full argument for the second bound. Put `k=t−1≥3`.
For every smaller-profile element `a_i`, let `U_i,V_i` be its
sets of maximal-block top predecessors and successors. Each has
cardinality `k`, and their respective ambient sets have sizes at
most `2k`, by (1).

Two distinct profiles sharing two top predecessors have disjoint
top-successor sets. Indeed, if they also shared a successor, the
two common predecessors and that successor would either violate
the central matching condition, or give a noncentral top pair two
different good middles. Consequently

\[
 |U_i\cap U_j|\ge2\ \Longrightarrow\ V_i\cap V_j=\varnothing,
 \qquad
 |V_i\cap V_j|\ge2\ \Longrightarrow\ U_i\cap U_j=\varnothing.
                                                               \tag{9}
\]

Make a graph on the `b` smaller profiles, joining `i,j` when
`|U_i∩U_j|≥2`. Along every edge the two `V` sets are disjoint
`k`-subsets of a set of size at most `2k`, hence exact complements.
There can be no odd cycle, since successive complementation around
it would make a nonempty set equal its own complement. The graph
is therefore bipartite. If `b≥5`, it has an independent triple.

For `k≥4`, its three `U` sets have pairwise intersections at most
one, so their union has size at least `3k−3>2k`. This is impossible.
It proves (8) for `t≥5`.

It remains to handle `k=3`. Choose an independent triple, indexed
`1,2,3`. Three triples with pairwise intersections at most one in
at most six points must have union exactly six, pairwise intersections
exactly one, and empty triple intersection. Their `V` sets also have
pairwise intersections at most one: otherwise (9) would make a pair
of the `U` sets disjoint. Thus the same exact description holds for
these three `V` sets.

Consider another profile `l`. If it were adjacent to, say, `1`,
then `V_l` would complement `V_1`. Since `V_1` meets `V_2,V_3`
in one point each, `V_l` meets each of them in two points. By (9),
`U_l` would be disjoint from `U_2∪U_3`, a five-point set inside
the six-point universe. A three-element `U_l` cannot fit in its
complement. Hence `l` is adjacent to none of `1,2,3`.

The union of `U_1,U_2,U_3` has three points belonging to two sets
and three points belonging to exactly one. A triple meeting each
`U_i` in at most one point must consist precisely of the latter
three points. Therefore every outside `U_l` is the same fixed
triple, meeting each initial `U_i` in one point. Equation (9) now
shows that its `V_l` meets each initial `V_i` in at most one point;
the same argument makes every outside `V_l` the same fixed triple.

Two outside profiles would consequently have identical `U` and `V`
triples, contradicting (9). There is at most one outside profile,
so `b≤4` here too. This completes the proof of (8).
