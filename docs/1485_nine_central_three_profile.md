# Nine central vertices and a three-element degree-five profile

Research note, 20 September 2026. These are mathematical necessary
conditions, not Lean proofs and not an exclusion of order forty.

Assume minimum degree `r=4`, central set `Z` of size nine, and a
first noncentral top product `a` of degree five whose top predecessor
and successor sets `U,V` both have size three. Write `T` for the top
class and `h=|T|`. The
[first-profile theorem](1485_first_successor_degree_profiles.md)
gives partitions `P_U,C_V` of `Z`, all their parts have size three,
every global central block has size at most three, and

\[
 K_{uv}=|C_u\cap P_v|\quad(u\in U,v\in V)
\]

is a permutation matrix. Label `U={u_1,u_2,u_3}` and
`V={v_1,v_2,v_3}` so its ones are diagonal. The partitions give a
full three-by-three grid on `Z`. General central-middle uniqueness
gives `|C_s∩P_t|≤1` for all tops `s,t`.

**Conclusion proved below:**

\[
                         \boxed{16\le h\le18.}
\]

The proof does not need the total order to be forty. In that
order-forty application the other classes have degrees five and eight.
This note does not handle the alternative in which every degree-five
vertex has four top predecessors and successors.

The subsequent [eighteen-top exclusion](1485_nine_central_eighteen_top.md)
now sharpens the displayed bound to `h∈{16,17}`, using three analytic
cases and five retained, independently checked finite refutations.
The complement tilings and zero-count identity also extend to
`r=t+1,m=t²`; the [general theorem](1485_maximal_first_output_grid.md)
proves that at most four degree-`r+1` vertices can have top-profile
size `r−1` in that maximal-grid branch.

## 1. Three disjoint complement tilings

The exact auxiliary-membership identity is

\[
 \mathbf1_{s\,B_z\,b}
 =\sum_{t\in T}\mathbf1_{z\in P_t}\mathbf1_{t*b=s}
 =\sum_{v\in T}\mathbf1_{z\in C_v}\mathbf1_{s*v=b}.
                                                        \tag{1}
\]

Both sums are zero or one; see equation (15) of the
[central-parameter note](1485_central_parameter_components.md).
For `s=u_i,b=a`, the top solutions of `u_i*v=a` are exactly
`V∖{v_i}`: a top input must be a top successor of `a`, and the
good pairs within `U×V` are the complement of `K`.
Thus, putting

\[
 X_i=\{t\in T:t*a=u_i\},
\]

the blocks `P_t`, `t∈X_i`, disjointly tile `Z∖C_{v_i}`.
Each such block has size at most two, since it meets each of the
three columns `C_{v_j}` at most once and avoids column `i`.
The sets `X_i` are disjoint, so their union `X` satisfies

\[
 |X|\ge9,\qquad \sum_{t\in X}|P_t|=18.              \tag{2}
\]

More exactly, every central point belongs to two of these selected
blocks. The dual argument gives disjoint sets
`Y_j={t:a*t=v_j}`, whose `C`-blocks tile `Z∖P_{u_j}`;
their union `Y` satisfies the dual statements.

In particular there are at most six tops with `|P_t|=3`, and at
most six with `|C_t|=3`: the small `P`-blocks already have total
weight at least eighteen out of the global total thirty-six.
Neither construction assumes that arbitrary global blocks are
contained in the grid rows or columns.

When there are exactly six `P`-triples, all small `P`-blocks lie
in `X`; consequently the six triples cover every central point
exactly twice. Every `C`-triple then meets **all six** `P`-triples
once. The same statement follows dually if there are exactly six
`C`-triples.

## 2. Moment and size-two coverage constraints

Let `N_ij` count tops with `|P_t|=i, |C_t|=j`, for `1≤i,j≤3`.
Central valency four and the partition of `Z×Z` by `P_t×C_t`
give

\[
 \sum N_{ij}=h,\quad
 \sum iN_{ij}=\sum jN_{ij}=36,\quad
 \sum ijN_{ij}=81.                                    \tag{3}
\]

Put `α_t=3−|P_t|, β_t=3−|C_t|`. Then

\[
 \sum\alpha_t=\sum\beta_t=3h-36,\qquad
 \sum\alpha_t\beta_t=9h-135.
\]

Nonnegativity and `αβ≤2α` give `15≤h≤21`.
There is an additional constraint sometimes lost by using only
these moments. At each central point, its four outgoing tops have
`C`-blocks partitioning nine into four positive parts at most three.
The only possible lists are `(3,3,2,1)` and `(3,2,2,2)`.
Thus each central point is covered by a `P`-block whose paired
`C`-block has size two. Dually,

\[
             \sum_i iN_{i2}\ge9,\qquad
             \sum_j jN_{2j}\ge9.                       \tag{4}
\]

## 3. Excluding the four boundary values

If `h=15`, the product moment is zero, so every top has `P`-size
three or `C`-size three. Hence the sets `X,Y` in (2) are
disjoint, requiring `h≥18`, a contradiction.

If `h=21`, equality holds in both `αβ≤2α` and `αβ≤2β`.
Each top therefore has type `(1,1)` or `(3,3)`. But
`36=h+2N_33` is then impossible by parity.

For the other boundary values it is convenient to use

\[
 \begin{split}
 4N_{13}+2(N_{12}+N_{23})+N_{22}&=63-3h,\\
 4N_{31}+2(N_{21}+N_{32})+N_{22}&=63-3h.
 \end{split}                                           \tag{5}
\]

At `h=20`, (5) forces `N_13=N_31=0` and `N_22=1` or
three. Substituting the two margins in (3) leaves just these two
tables, displayed with rows indexed by `i`:

\[
 \begin{pmatrix}10&1&0\\1&1&0\\0&0&7\end{pmatrix},
 \qquad
 \begin{pmatrix}11&0&0\\0&1&1\\0&1&6\end{pmatrix}.
\]

Their first size-two cover in (4) has weight three or five, not
at least nine. Thus `h=20` is impossible.

At `h=19`, substituting the nonnegative integer solutions of (5)
in (3) and (4) leaves exactly

\[
 \begin{pmatrix}8&0&0\\0&4&1\\0&1&5\end{pmatrix},\quad
 \begin{pmatrix}9&0&0\\0&0&3\\0&3&4\end{pmatrix},\quad
 \begin{pmatrix}7&1&0\\1&4&0\\0&0&6\end{pmatrix}.        \tag{6}
\]

This is only a small nonnegative-integer case split, reproducible
by the standalone checker linked below. The middle table has seven
`P`-triples, contrary to (2). Each other table has six triples on
each side, so every `C`-triple meets every `P`-triple once by the
last paragraph of §1. Moreover, `U` contains at least two
`C`-triples, and `V` contains at least two `P`-triples: each table
has at most one top of type `(3,2)` or `(2,3)`, and none of type
`(3,1)` or `(1,3)`. The corresponding two-by-two submatrix of
`K[U,V]` is all ones. This contradicts its being a permutation
matrix, and excludes `h=19`.

The integer case split is independently executable with Python's
standard library:

```sh
python3 scripts/1485_nine_central_moments_check.py
```

The [checker](../scripts/1485_nine_central_moments_check.py)
exhausts the two slack equations (5), reconstructs the two diagonal
counts from a margin and the total, and tests all equations (3).
It asserts the exact displayed tables before applying further
profile restrictions. No solver or unproved alignment assumption
is involved.

## 4. A general weighted profile-packing test

Here additionally assume order forty and exactly the four degree
classes `4,5,8,10`. Write `A,B` for the degree-five/eight classes.
Every degree-five vertex has a top profile of size `t=3` or four,
and sharp degree `5−t` in each direction. For any fixed central
incidence system, enumerate its possible whole profiles `(U,V)`.
Two profiles whose good top endpoint pairs overlap cannot belong
to distinct vertices: those endpoints have only one product.

Sharp-neighbor existence covers `B` by the sharp successors of
`A`. Therefore any actual set of pairwise compatible profiles
satisfies

\[
 40-m-h=|A|+|B|
       \le\sum_{a\in A}(6-t_a).                         \tag{7}
\]

Thus an upper bound on the weighted independent-set number of
the profile-conflict graph, with weight three for `t=3` and two
for `t=4`, is a valid exclusion test. This does not license
enumerating only grid-aligned central blocks: the general blocks
are partial transversals to the opposite grid partition, and need
not be contained in its own rows or columns.

The elementary central moments alone genuinely lose information.
For example, start with the nine rectangles `row_i×col_j` in a
three-by-three grid (indices modulo three). Split a diagonal
rectangle into `row_i×{(i,i)}` and
`row_i×(col_i∖{(i,i)})`; split rectangle `(i,i+1)` into
`{(i,i)}×col_(i+1)` and
`(row_i∖{(i,i)})×col_(i+1)`; leave the other three intact.
The resulting fifteen rectangles satisfy all central valencies,
partition the central square, and have every cross-intersection
at most one. The three tops with blocks
`(row_i,{(i,i)})` and the three with
`({(i,i)},col_(i+1))` give a local size-three profile with
permutation `K`. This is **not a magma**: §3 excludes it using
the additional auxiliary tilings. It is a limitation of bare
local central-incidence arguments, not a spectrum counterexample.

## 5. A global triple-block zero count

There is a stronger version of the saturation argument. Let `p,q`
be the numbers of global `P`-triples and `C`-triples, respectively.
We know `3≤p,q≤6`. The blocks indexed by `X` cover every central
point twice, and the disjoint index set `U` covers it once. Since
the total `P`-valency is four, the remaining `P`-blocks partition
`Z`. Among those remaining blocks, the small ones disjointly tile
a set `E` of size `18−3p`. Hence the entire triple family has
pointwise multiplicity `2−1_E`. Dually the `C`-triples have
multiplicity `2−1_F` with `|F|=18−3q`.

The full `q` by `p` matrix of their intersections is zero-one.
Its number of zeros is exactly

\[
 pq-\sum_{z\in Z}(2-\mathbf1_E(z))(2-\mathbf1_F(z))
       =(6-p)(6-q)-|E\cap F|.                           \tag{8}
\]

If `s=N_33`, the profile `U` contains at least
`u=max(0,3−p+s)` `C`-triples, while `V` contains at least
`v=max(0,3−q+s)` `P`-triples. Their submatrix in the permutation
`K[U,V]` requires at least `uv−min(u,v)` zeros. Thus

\[
             uv-\min(u,v)\le(6-p)(6-q).                 \tag{9}
\]

Applying this to the moment tables leaves just two possibilities
when `h=18`:

\[
 \begin{pmatrix}6&0&0\\0&3&3\\0&3&3\end{pmatrix},
 \qquad
 \begin{pmatrix}5&1&0\\1&3&2\\0&2&4\end{pmatrix}.       \tag{10}
\]

The discarded two tables had `p=q=5` and `s≥4`: (8) allows at
most one zero, while a two-by-two permutation submatrix needs at
least two. The two displayed tables are the complete input to the
subsequent [eighteen-top exclusion](1485_nine_central_eighteen_top.md).
This is transparent finite integer case analysis, not enumeration
of magmas.

One further elementary profile filter is useful for the lower values
of `h`. If a top `w` lies in `U∩V`, then `C_w` belongs to the
partition `C_V`, so it meets every global `P`-triple once. Its row
in `K[U,V]` therefore forces `V` to contain exactly one `P`-triple.
Dually `U` contains exactly one `C`-triple. In terms of chosen
counts `u,v` (not just their lower bounds), an overlap can occur
only for `u=v=1`. The overlap is at least `max(0,u+v−s)` and
at most `min(u,v,1)`. The checker also applies these small bounds;
it never interprets a surviving count table as a realized magma.

## 6. Singleton coverage excludes another seventeen-top table

The same exceptional sets `E,F` give another useful pointwise
restriction. A central row has four tops. If it lies outside `E`,
exactly two of those tops are `P`-triples. If neither has `C`-size
one or three, their `C`-sizes are both two; neither of the other
two tops can then have `C`-size one, since the total size would be
at most `2+2+1+3=8`, not nine.

Each central row contains at most one `C`-singleton. Consequently
the `P`-blocks of tops of types `(1,1)` and `(2,1)` are pairwise
disjoint, and their union is contained in
`E ∪ ⋃_(t:type(3,3)) P_t`. Indeed a row containing such a
singleton cannot also contain a type `(3,1)` top. Thus

\[
 N_{11}+2N_{21}\le18-3p+3N_{33},\qquad
 N_{11}+2N_{12}\le18-3q+3N_{33}.                         \tag{11}
\]

For example, the otherwise surviving seventeen-top count table

\[
                  \begin{pmatrix}4&0&0\\0&2&5\\0&5&1\end{pmatrix}
\]

has `p=q=6` and `N_33=1`, so (11) would require `4≤3`.
Equivalently, all four singleton source labels would have to lie
in the three-point predecessor block of the unique `(3,3)` top.
This exclusion uses no solver. The finite integer checker now
includes both inequalities (11).

The [degree-class capacity note](1485_nine_central_class_capacities.md)
adds `6a_3≤pq−L−R+9`, with `a_3≥1`, excluding two further
seventeen-top tables. The current elementary integer filter leaves
36 count tables at sixteen tops and 18 at seventeen tops. These
surviving tables are necessary counts, not asserted realizations.
