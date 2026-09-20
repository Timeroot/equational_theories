# Nine central elements and seventeen tops: analytic exclusion with a three-profile vertex

Research theorem, 20 September 2026. There is no order-forty E1485
magma with minimum degree four, nine central elements, seventeen tops,
and a degree-five vertex having three top neighbors. The proof below
is entirely analytic: no finite enumeration, SAT/SMT result, or local
optimization certificate is needed. It is not yet a Lean theorem.
The qualification about a three-profile vertex is essential to the
stated scope; this note does not exclude every seventeen-top model.

Assume an order-forty E1485 magma has minimum degree four, nine
central elements, seventeen tops, and at least one degree-five vertex
with three top neighbors. The degree classes are `Z,A,B,T`, of
degrees `4,5,8,10`. Write `a=|A|,b=|B|`, so `a+b=14`.
Split `A=A3⊔A4` by its top-neighbor count and put `a3=|A3|≥1`.
The opposite top-neighbor counts of a vertex of `A` agree.

Use `P_u,C_u` for the central blocks at a top and `N_ij` for
their size counts. All sizes are at most three. The
[three-profile complement argument](1485_nine_central_three_profile.md)
gives `3≤p,q≤6`, where `p,q` count global `P`- and `C`-triples.
The two singleton margins are now `p−2,q−2`; the double margins
are `19−2p,19−2q`.

## 1. At most two degree-five vertices have a three-element profile

Let `W_P` be the sum of the `C`-sizes on the `P`-singleton
tops, and `W_C` the sum of the `P`-sizes on the `C`-singleton
tops. The central partitions are `3321` or `3222`: pointwise,
their triple count equals one plus their singleton count.
Exactly as in the
[central coverage argument](1485_nine_central_class_capacities.md#1-a-sharper-total-bound-on-three-neighbor-vertices),
the rectangle of `P`-triple sources and `C`-triple targets has
at least `9+W_P+W_C` centrally valued pairs. It also contains
all six top pairs representing each member of `A3`. Hence

\[
                  6a_3\le pq-9-W_P-W_C.                 \tag{1}
\]

Put `x=N11`. Counting the other singleton types gives

\[
 W_P\ge2(p-2)-x,\qquad W_C\ge2(q-2)-x,
 \qquad x\le\min(p-2,q-2).
\]

Consequently

\[
                  6a_3\le pq-5-2\max(p,q).              \tag{2}
\]

Its largest possible right side is nineteen, so `a3≤3`.
Equality `a3=3` would require `p=q=6`. Here `x≤3`:
otherwise `x=4` uses all singleton tops of both kinds in type
`11`. Writing `s=N33`, the margins then force
`N23=N32=6−s` and `N22=1+s`. The product moment is
`81=80+s`, giving `s=1`. This contradicts the
[singleton-coverage inequality](1485_nine_central_three_profile.md#6-singleton-coverage-excludes-another-seventeen-top-table)
`N11≤3N33`.
Thus `W_P+W_C≥16−2x≥10`, and (1) gives
`6a3≤36−9−10=17`, excluding three. We have proved

\[
                         \boxed{1\le a_3\le2.}          \tag{3}
\]

The weaker bound (2) already gives a useful short list. Up to
duality, if `a3=1` the only possible `(p,q)` are
`(4,6),(5,5),(5,6),(6,6)`. If `a3=2`, only `(5,6),(6,6)`
remain. These lists come directly from `3≤p,q≤6` in (2).

## 2. There are six through nine degree-five vertices

Sharp-neighbor existence covers `B` by the sharp successors of
the vertices in `A`. There are `2a3+a4=a+a3` such incidences,
so `b≤a+a3`. Since `a+b=14`, (3) implies `a≥6`.
If `a3=1`, it instead implies `a≥7`.

The auxiliary support of a top-to-`A` edge has at least six central
labels, by the complement-block argument used in
[the sixteen-top capacity proof](1485_nine_central_sixteen_degree_counts.md#3-top-input-packing-improves-the-auxiliary-capacity-bound).
Thus a top whose `C`-size is one, two, or three has at most
four, three, or one successors in `A`, respectively.
There is a `C`-singleton because `q−2≥1`. Any central row
containing it has block sizes `3321`, so its four tops together
have at most `4+3+1+1=9` successors in `A`. They count every
member of `A` once. Therefore

\[
                 \boxed{6\le a\le9,\qquad a+b=14.}       \tag{4}
\]

In particular `a=6` forces `a3=2`. This is only an initial bound;
none of the remaining values in (4) is asserted realizable.

## 3. The only possible failure of balance on `B`

Write `I_x,O_x` for the top predecessor/successor counts of any
vertex. Their central blocks partition nine into blocks of size at
most three, so both counts are at least three. At most `p−2`
predecessor blocks can be singletons; hence `9≥2I_x−(p−2)`.
The dual argument gives

\[
 3\le I_x\le\left\lfloor\frac{p+7}{2}\right\rfloor\le6,
 \qquad
 3\le O_x\le\left\lfloor\frac{q+7}{2}\right\rfloor\le6.  \tag{5}
\]

For `x∈B`, let `j_x^+,j_x^-≥1` be its sharp successor and
predecessor counts in `A`. Reciprocal-neighbor balance and ordinary
degree give

\[
 O_x-I_x=3(j_x^+-j_x^-),\qquad
 O_x+j_x^+\le8,\quad I_x+j_x^-\le8.
\]

If `I_x≠O_x`, (5) forces the pair to be `(3,6)` or `(6,3)`.
The degree inequalities then determine the sharp counts as well.
Thus every vertex of `B` is either balanced, or one of exactly
these two unbalanced types:

\[
       (I_x,O_x,j_x^+,j_x^-)=(3,6,2,1)
                    \quad\text{or}\quad(6,3,1,2).        \tag{6}
\]

The two unbalanced types have equal cardinalities. Indeed the sums
of `I` and `O` over `B` agree: count edges incident to the top
class in the two directions, using the equal counts on `Z,A`
and the tautological equality of the two internal top-edge counts.

More quantitatively, the total sharp excess in either direction is
`Σ_B(j_x^±−1)=a+a3−b=2a+a3−14`. Hence the number of each
unbalanced type is at most this excess. When `a=6,a3=2`, it is
zero: every sharp degree is one, and all vertices of `B` really
are balanced in this particular subcase. Balance is **not** assumed
for the other cases.

## 4. Exact sharp-neighbor profiles at a three-profile vertex

For `a0∈A3`, its three top-output fibers of `R_(a0)` use
disjoint sets of small-`P` tops whose total `P`-weight is eighteen.
If their union is `X`, counting its singleton blocks gives

\[
            |X|=9+\tfrac12\#\{u\in X:|P_u|=1\}.
\]

The seventeen top inputs not in `X` split between the two sharp
`B` outputs. Their top-input counts are exactly the `I` counts
of those two vertices, since a sharp fiber is the full predecessor
set. If `p=6`, complement saturation uses all four `P`-singletons,
so `|X|=11` and both sharp predecessors have `I=3`.
If `p=4` or `5`, the singleton count in `X` is even and at
most three, hence zero or two. The two sharp predecessor counts
therefore sum to eight or seven. With (5), their unordered pair is

\[
 \begin{cases}
 \{3,3\},&p=6,\\
 \{3,4\},\ \{3,5\},\ \text{or }\{4,4\},&p=4\text{ or }5.
 \end{cases}                                               \tag{7}
\]

The dual statement uses `q` and the top-successor counts `O`.
If `e_x^±` count sharp `A3` successors and predecessors at `x∈B`,
then `Σe_x^±=2a3`, and summing (7) gives

\[
 \sum_B e_x^+I_x=
 \begin{cases}6a_3,&p=6,\\
 \text{a number in }[7a_3,8a_3],&p=4\text{ or }5.
 \end{cases}                                               \tag{8}
\]

There is an independent dual formula for `Σe_x^-O_x` and `q`.
In particular a sharp `A3` predecessor never has `I=6`, nor
does a sharp `A3` successor have `O=6`.

## 5. Global top-edge counts

Let `S` count ordered ordinary edges between two tops. Put
`U=Σ_B(I_x−3)=Σ_B(O_x−3)`, using the global balance proved
above. Counting all ordinary edges out of the seventeen tops gives

\[
 S+\sum_BI_x=170-36-(4a-a_3),
 \qquad
                    S=92-a+a_3-U.                        \tag{9}
\]

The central weighted top-count sums are `Σ_T|P_u|O_u=153`
and its dual. Since `Σ_T(3−|P_u|)=15`, (5) gives
`3S−153≤6·15`. Thus

\[
                             S\le81.                    \tag{10}
\]

If `p=4` or `q=4`, one directional top count is at most five;
using the appropriate dual weighted sum improves this to `S≤76`.
Neither identity (9) nor either upper bound assumes vertexwise balance
on `B`.

## 6. Joint capacity slack forces six degree-five vertices and six triples

For a top with block sizes `P,C`, let `α` count its successors
in `A`, let `f(1)=4,f(2)=3,f(3)=1`, and define its nonnegative
integral capacity slack `w=f(C)−α`. Put
`X=Σ_(C=1)P`. The central moments give

\[
 \sum f(C)=49-q,\qquad \sum P f(C)=90-X.
\]

For the second equality, the total `P` weight on `C`-triple tops
is `9+X`, as follows either from the two central moments or the
pointwise partition identity used in §1. Since
`Σα=4a−a3` and `ΣPα=9a`, we obtain

\[
 \sum w=49-q-4a+a_3,
 \qquad
 \sum(P-1)w=41+q-X-5a-a_3.                              \tag{11}
\]

In particular the slack on tops with `P>1` is at most the second
sum in (11). The remaining slack occurs on `P`-singleton tops.
Write `x=N11,y=N12,z=N21`, so

\[
 N_{13}=p-2-x-y,\qquad N_{31}=q-2-x-z,
 \qquad X=x+2z+3N_{31}.                                 \tag{12}
\]

Suppose `a≥7`. A `C`-singleton top belongs to a central row
of pattern `3321`; the other three tops have `A` capacity at
most five in total. Thus it has `α≥a−5≥2` and slack at most
two. The slack bounds on `P`-singleton types `11,12,13` are
therefore respectively `2,3,1`. Combining with (11) gives

\[
 49-q-4a+a_3
 \le2x+3y+N_{13}+41+q-X-5a-a_3.
\]

Substitute (12) and rearrange. Applying the dual argument as well
gives

\[
 \begin{split}
 3x+2y+z&\ge a+4+q-p+2a_3,\\
 3x+y+2z&\ge a+4+p-q+2a_3.
 \end{split}
\]

Their sum is impossible: the singleton margins give
`2x+y+z≤p+q−4≤8`, whereas these inequalities require

\[
 3(2x+y+z)\ge2a+8+4a_3\ge26>24.
\]

Consequently `a=6` and `a3=2`, by §§1–2.
For this value of `a`, a `C`-singleton has `α≥1`, so the
three singleton-type slack bounds are now `3,3,1`. Repeating the
same calculation gives

\[
 4x+2y+z\ge14+q-p,\qquad
 4x+y+2z\ge14+p-q.                                     \tag{13}
\]

Only `(p,q)=(5,6),(6,5),(6,6)` remain by §1. In the mixed
case, `x≤3` and `2x+y+z≤7`, whence
`8x+3y+3z≤21+2x≤27`. But (13) requires this sum to be
at least twenty-eight. We have proved

\[
                \boxed{a=6,\ b=8,\ a_3=2,\ p=q=6.}       \tag{14}
\]

The sharp-incidence total in each direction is `a+a3=8`,
equal to `b`. Thus every sharp degree on `B` is one and,
by §3, every vertex of `B` is balanced. Write its common top
count as `t_x∈{3,4,5,6}`. Its internal `B` degree in either
direction is `7−t_x`.

## 7. Four or five vertices have three top neighbors

Let `L={x∈B:t_x=3}`. Each member of `A3` has two sharp
predecessors in `B`, all in `L` by (7). These two pairs are
disjoint because every sharp degree on `B` is one. Hence
`|L|≥4`; the same applies to the sharp successor pairs.
Equations (9)–(10) now give

\[
                     S=88-U\le81,\qquad U\ge7.
\]

Six or more vertices with `t=3` would leave at most two vertices
to contribute at most three each to `U`, a contradiction. Therefore

\[
                              |L|=4\text{ or }5.          \tag{15}
\]

Keep the ordinary internal relation `D` and the sharp endpoint
relation `Q` on `B`:
`Q_xz=1` records a path `x⇒a⇒z` through some `a∈A`.
Such a middle is unique. Every member of `A3` supplies a two-by-two
rectangle and every member of `A4` one cell. In particular every
row and column of `Q` has at most two entries.
An internal two-edge path is bad exactly when its endpoint pair
belongs to `Q`. Repeated internal middles force such a replacement,
so `(D²)_xz≥2` implies `Q_xz=1`.

For an internal edge `xDy`, define

\[
 \eta(x,y)=\#\{z:zDx,\ Q_{zy}=1\},\qquad
 \beta(x,y)=\#\{z:yDz,\ Q_{xz}=1\}.
\]

The [exact good-pair formula](1485_nine_central_class_capacities.md#3-a-global-bad-path-count-without-edgewise-balance)
gives, at a vertex in `L`,

\[
              g_x=9-\tau_x,\qquad
              \tau_x=\sum_{y:xDy}\eta(x,y).              \tag{16}
\]

Every top pair with product in `L` has a `P`-triple first input
and a `C`-triple second input, since each relevant three-part
profile partitions nine into triples. The same six-by-six rectangle
already contains twelve pairs with product in `A3` and at least
nineteen central pairs: `N11≤3` when `p=q=6`, as proved in §1,
so `W_P+W_C≥10`. Thus

\[
                   \sum_{x\in L}g_x\le5,\qquad
                   \sum_{x\in L}\tau_x\ge9|L|-5.         \tag{17}
\]

## 8. Four low vertices are impossible

Suppose `|L|=4`. The two `A3` sharp predecessor pairs and the
two successor pairs each partition `L`. Thus `Q_L` is the
union of two disjoint two-by-two rectangles, with two entries in
each row and column; there are no sharp endpoint pairs between
`L` and its complement in `B`.

Let `F=D|_{L×L}`. It has at most ten entries. Indeed, if it
had at least eleven and a full row, at most two columns could
have degree at least two: otherwise the corresponding row of
`Q_L` would have at least three entries. The total would then
be at most `4+4+1+1=10`, a contradiction. Dually there is no
full column. With all degrees at most three, eleven entries force
three degree-three rows and three degree-three columns. Each such
row and column intersect twice, again forcing at least three entries
in a row of `Q_L`.

Each low vertex has internal degree four, so there are
`ℓ=16−|F|` edges from `L` to its complement. On a low-to-low
edge, `η≤2`. On a low-to-higher edge `xDy`, we have `η=1`.
To see this last assertion, the unique sharp predecessor of `y`
belongs to `A4`, by (7), so its column of `Q` has one entry
and `η≤1`. The
[weighted auxiliary-fiber identity](1485_general_return_matching.md#6-a-weighted-version-beyond-the-smallest-central-class)
expresses the edge support on the low side as `3η`. On the
other side, it is the sum of the nonempty central blocks of
`t_y−3+β≥1` top fiber members. It is positive, so `η≥1`.

Consequently

\[
             \sum_{x\in L}\tau_x\le2|F|+\ell
                        =16+|F|\le26,
\]

contrary to the lower bound thirty-one in (17).

## 9. Five low vertices are impossible

It remains that `|L|=5`. Let `H=B\setminus L`, of size three,
and again put `F=D|_{L×L}`. The twenty internal edges out of
`L` can have at most

\[
             \sum_{y\in H}(7-t_y)=12-U\le5
\]

targets in `H`. Thus `|F|≥15`. Every row and column of `F`
has degree at most four. If a row has degree four, every column
of degree at least three intersects it at least twice, and hence
forces an entry in that row of `Q_L`. There can be at most two
such columns, giving at most `2·4+3·2=14` entries in `F`,
a contradiction. Dually no column has degree four. Therefore every
row and column has degree three and `|F|=15`.

There are only four sharp incidences from `L` into `A3`, so
some low vertex has its unique sharp successor in `A4`. Its
row of `Q_L` has at most one entry. The corresponding row
of `F²` has sum nine, because `F` is three-regular. Its one
possible `Q_L` position has value at most three, and its other
four positions have value at most one. Its sum is thus at most
seven, a final contradiction.

This excludes both alternatives in (15), proving the stated theorem.
All steps are analytic, including the two small matrix bounds; neither
matrix bound depends on an exhaustive computation.
