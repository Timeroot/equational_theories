# No finite E1485 magma has order twelve

Research note, 18 September 2026. Use the finite structure theorems in
[the graph note](1485_graph_research.md), strict projection descent in
[the image note](1485_image_research.md), and the incidence reduction in
[the minimum-degree-two note](1485_min_degree_two.md).

**Theorem.** No finite E1485 magma has order twelve.

There is now a shorter proof using the subsequent
[global minimum-degree-two theorem](1485_two_central_exclusion.md).
The extremal product is `rs=12`. Minimum degree one is impossible by
the constant-row classification. At minimum degree two, degree three
cannot occur by that global theorem; reciprocity excludes degree four
as well. The only remaining degrees would be two and six, contradicting
the two-degree cardinality theorem. At minimum degree three, the degrees
would be three and four, again contradicting the two-degree theorem.
These exhaust the possible minimum degrees and prove the exclusion.

The longer independent argument below was obtained first and is retained
for its binary-coordinate and matrix-rank methods. The global theorem
does not depend on this order-twelve proof.

To make the reduction exhaustive, let `r` and `s` be the minimum and
maximum degrees. They satisfy `rs=12`. Minimum degree one gives a
constant row and hence power-of-two order, which is impossible here.
If `r=3`, the only possible degrees are three and four; the
[two-degree cardinality theorem](1485_two_degree_lower_bound.md) excludes
this. If `r=2`, then `s=6`; the possible intermediate degrees are three
and four, and degree reciprocity makes them occur together. If neither
occurs, the two-degree theorem again excludes the model. Thus the
occurring degrees must be exactly `2,3,4,6`.

Write their respective classes as `Z,A,B,T`. The minimum-degree-two
note excludes the cases with three or four central vertices and leaves
two possibilities. The first part of this note excludes

\[
 (|Z|,|A|,|B|,|T|)=(2,4,2,4). \tag{1}
\]

The final section excludes `(2,3,3,4)` by a matrix-rank argument.
Together these exclusions prove the theorem. Both arguments are
analytic; no exhaustive search is needed for the conclusion.

## Incidence and the initial product restrictions

Every vertex has two top predecessors and successors. Each `A` vertex
has one sharp `B` predecessor and successor. Each `B` vertex has two
sharp `A` predecessors and successors, and has no neighbor in `B`.
Each top vertex has one central predecessor and successor.

For a top vertex, ordinary and reciprocal-degree balance imply equality
between its numbers of `A` predecessors and successors, and likewise
for `B`. A top row contains at most two `A` vertices: distinct `A`
vertices in that row must have distinct sharp `B` successors, since
otherwise two good paths would have the same endpoints. The four `A`
vertices each have two top predecessors, so altogether there are eight
edges `T→A`. Thus every top vertex has exactly two `A` successors and
predecessors, and one `B` successor and predecessor.

Label `Z={z_0,z_1}` and `B={b_0,b_1}`. The four products `z_k*z_l`
are distinct and exhaust `T`: each top vertex has exactly one central
predecessor and successor. Write them as `t_{kl}`. Similarly, a `B`
vertex's two sharp `A` successors have different sharp `B` successors,
so every ordered pair of `B` vertices has exactly one sharp `A` middle.
The four products exhaust `A`; write `a_{ij}=b_i*b_j`. Hence

\[
 z_k\to t_{kl}\to z_l,
 \qquad b_i\Rightarrow a_{ij}\Rightarrow b_j.
 \tag{2}
\]

The two sharp `A` successors of a `B` vertex have disjoint ordinary
rows. Their two-element top-successor sets therefore partition `T`.
Dually, and using the two `A` neighbors of each top vertex, this gives

\[
 B*B\subseteq A,\quad B*T\subseteq A,\quad T*B\subseteq A.
 \tag{3}
\]

For endpoints in `A×B` or `B×A`, the only possible ordinary middles
are top vertices. Their good middle is consequently top, and no
second top middle can occur, by strict degree descent. Thus

\[
 A*B\subseteq T,\qquad B*A\subseteq T. \tag{4}
\]

For `t∈T`, each of its two `A` outputs has exactly two input preimages.
One is that `A` vertex's sharp `B` successor. The other must be one of
its two top successors. The central output of `L_t` has exactly two
preimages, both top, by sharpness. These exhaust all four top inputs,
so

\[
 T*T\subseteq Z\cup A. \tag{5}
\]

All products with a central factor lie in `T`. Also `A*A⊆B∪T`.

## Two additional unique-path identities

Let `P` be adjacency from `A` to `T`, and `Q` adjacency from `T` to
`A`. Both are four-by-four zero-one matrices with all row and column
sums two. We prove

\[
 PQ=QP=J_4. \tag{6}
\]

First fix `t∈T`, with unique central successor `z`, and a central
parameter `c`. The projection `F_c(x)=t*(x*c)` has rank two. Its
image lies in `Row(t)∩(Z∪A)` by (5), and contains `z`, which is sharp.
Thus its other image point is exactly one of the two `A` successors of
`t`. Exactly one of those `A` successors is fixed; strict degree
descent sends the other to `z`.

For any `v∈Row(z)`, choose a central successor `c` of `v`. Centrality
gives `z*c=v` and `t*v=z`. For an `A` successor `u` of `t`,

\[
 F_c(u)=z\quad\Longleftrightarrow\quad u*c=v
 \quad\Longleftrightarrow\quad u\to v. \tag{7}
\]

For the first forward implication, `F_c(u)=z` supplies the path
`z→u*c→c`, which is good by centrality; the converse is immediate.
The second equivalence follows because every path ending at `c` is
good. Therefore exactly one `A` middle occurs when the top endpoints
have a central good middle. For other top endpoints, (5) gives an `A`
good middle and strict descent excludes any other `A` middle. This
proves `QP=J_4`.

For `PQ`, fix `a∈A` with sharp successor `b∈B`. If `v∈Row(b)∩A`,
choose `c∈B` with `b*c=v`, using the bijection `B×B→A`. The projection
`F_c(x)=a*(x*c)` has rank two because `c*a∈T`. It fixes `b`, so exactly
one of the two top successors of `a` is fixed and the other moves to
`b`. For a top successor `u` of `a`,

\[
 F_c(u)=b\quad\Longleftrightarrow\quad u*c=v
 \quad\Longleftrightarrow\quad u\to v. \tag{8}
\]

Indeed `u*c∈A` by (3), so the path `b→u*c→c` supplied by the first
equality has sharp edges and is good. The reverse direction is immediate.
The last equivalence uses `v⇒c`. Thus an `A×A` endpoint pair with a
sharp `B` middle has exactly one top middle. Any other `A×A` pair has
a top good middle, and strict descent excludes a second top middle.
This proves `PQ=J_4`.

## Binary coordinates

All indices below belong to `{0,1}`, and `⊕` denotes addition modulo
two. The cross incidences can be written using bits `α_l,β_k,γ_{il},δ_{jk}`:

\[
 \begin{aligned}
 b_i&\to t_{i\oplus\alpha_l,l},
 &t_{k,j\oplus\beta_k}&\to b_j,\\
 a_{ij}&\to t_{j\oplus\gamma_{il},l},
 &t_{k,i\oplus\delta_{jk}}&\to a_{ij}.
 \end{aligned} \tag{9}
\]

Here each displayed formula lists the two neighbors as the unused top
coordinate varies. For the first row, products with a central factor
make each `B` top-neighbor set a transversal of the two central blocks;
each top vertex has just one `B` neighbor in each direction. For the
second row, centrality again gives these transversals, while the sharp
`B→A→T` and `T→A→B` paths force the two `A` vertices in each relevant
pair to use opposite coordinates.

Equation `PQ=J_4` implies:

\[
 \text{if a row of }\gamma\text{ is nonconstant, every row of }
 \delta\text{ is constant}. \tag{10}
\]

To see this, for fixed `i,j,p,q` the unique top middle from `a_{ij}`
to `a_{pq}` is specified by the unique bit `l` such that
`l⊕δ_{q,j⊕γ_{il}}=p`. The two values of this expression must differ,
so `δ_{q,j⊕γ_{i0}}=δ_{q,j⊕γ_{i1}}`. A nonconstant `γ` row makes the
two indices exhaust `{0,1}`.

Similarly `QP=J_4` implies

\[
 \text{if a column of }\delta\text{ is nonconstant, every column of }
 \gamma\text{ is constant}. \tag{11}
\]

For fixed top endpoints `t_{kl},t_{pq}`, uniqueness means that
`j↦j⊕γ_{l⊕δ_{jk},q}` is a permutation of the two bits. Thus
`γ_{l⊕δ_{0k},q}=γ_{l⊕δ_{1k},q}`, giving the assertion.

## E1485 forces a rigid coordinate pattern

Apply E1485 with

\[
 x=a_{ij},\qquad y=b_k,\qquad z=b_{1\oplus j}.
 \tag{12}
\]

Write `b_k*a_{ij}=t_{uv}` and
`a_{ij}*a_{1⊕j,k}=t_{pq}`. The latter product is top because these
`A` endpoints have no `B` common middle. E1485 says
`t_{uv}*t_{pq}=a_{ij}`. Since the central middle would occur exactly
when `v=p`, this requires

\[
 p=1\oplus v. \tag{13}
\]

We first show that every row of `δ` is constant. This already follows
from (10) if some row of `γ` is nonconstant. Otherwise write
`γ_{il}=g_i`. Then `p=j⊕g_i`, so (13) fixes
`v=1⊕j⊕g_i`, independently of `k`. Formula (9) gives
`u=k⊕α_v` and `v=i⊕δ_{ju}`. As `k` varies, `u` takes both values;
hence `δ_{j0}=δ_{j1}`. Write these constant rows as `δ_{jk}=d_j`.

In (12), the first product now has `v=i⊕d_j`, and the second has
`q=1⊕j⊕d_k` and `p=j⊕γ_{iq}`. Equation (13) becomes

\[
 \gamma_{i,1\oplus j\oplus d_k}
 =1\oplus i\oplus j\oplus d_j. \tag{14}
\]

If `d_0≠d_1`, varying `k` makes each row of `γ` constant, with value
`1⊕i⊕d_0`. These values differ for the two rows. But then the columns
of `δ` are nonconstant, so (11) says the columns of `γ` must be
constant, a contradiction. Consequently

\[
 \boxed{\delta_{jk}=d,\qquad \gamma_{il}=i\oplus l.} \tag{15}
\]

Finally every `A×B` pair has a unique top middle by (4). The two top
successors of `a_{ij}` now have first coordinates `i⊕j` and
`i⊕j⊕1`. Their `B` successors must differ, so (9) forces
`β_0=β_1=b` for one bit `b`.

## Two final instances of E1485 contradict one another

The forced coordinates give the following products:

\[
 a_{ij}*a_{pq}=
 \begin{cases}
 b_j,&j=p,\\
 t_{i\oplus1\oplus d,p\oplus d},&j\ne p,
 \end{cases}
 \qquad
 a_{ij}*b_k=t_{i\oplus j\oplus k\oplus b,k\oplus b}.
 \tag{16}
\]

Use E1485 with `x=a_{00}, y=a_{01}, z=a_{00}`. Its left-hand side is

\[
 t_{1\oplus d,d}*t_{b,b}.
\]

If `b=d`, this product has the central middle `z_d`, contradicting
that it equals `a_{00}`. Therefore `b≠d`.

Now use `x=a_{00}, y=a_{11}, z=a_{01}`. The left-hand side is

\[
 t_{d,d}*t_{1\oplus b,1\oplus b}.
\]

Since `b≠d`, we have `1⊕b=d`, so this product again equals the
central vertex `z_d`, contradicting E1485. This excludes (1).

## The remaining class sizes `(2,3,3,4)`

Suppose now that

\[
 (|Z|,|A|,|B|,|T|)=(2,3,3,4). \tag{17}
\]

Each `A` and each `B` vertex has sharp in-degree and out-degree one.
Label them so that

\[
 a_i\Rightarrow b_i\Rightarrow a_{\sigma(i)}
 \qquad(i\in\{0,1,2\}), \tag{18}
\]

where `σ` is a permutation. Each top vertex has one central neighbor
and two top neighbors in each direction. Ordinary and weighted degree
balance show that it has equally many `A` successors and predecessors:
subtracting its two degree-balance equations leaves this equality,
since the only remaining degrees are three and four. Denote the common
number by `α_t`. It has `3−α_t` neighbors in `B` in each direction.
Counting `T→A` edges gives

\[
 \sum_{t\in T}\alpha_t=6. \tag{19}
\]

### A uniform-fiber bound

Every nonempty fiber of `L_t` has size two. Its central output uses
two top inputs, by sharpness. Each `A` output uses its sharp `B`
successor as one input; its other input must be top, since the ordinary
row of that `A` vertex consists of this `B` successor and two top
successors. Thus its `α_t` different `A` outputs each use one further
top input. There are only four top inputs, so

\[
 \alpha_t\le2. \tag{20}
\]

If `α_t=2`, these inputs exhaust `T`, proving the additional fact

\[
 t*T\subseteq Z\cup A \qquad(\alpha_t=2). \tag{21}
\]

### At most one `A` middle between any top endpoints

Let `P` be adjacency `A→T`, now a three-by-four matrix, and let `Q`
be adjacency `T→A`, a four-by-three matrix. We claim that `QP` is
zero-one.

For top endpoints with no central common middle, the presence of an
`A` middle forces the good product to have degree at most three.
It cannot be central, so it is in `A`. Strict degree descent then
excludes any second `A` middle.

Consider endpoints `t,v` with a central good middle `z`. If `α_t≤1`,
there is already at most one possible `A` middle. If `α_t=2`, choose
a central successor `c` of `v`. The rank-two projection
`F_c(x)=t*(x*c)` has image in `Row(t)∩(Z∪A)` by (21), since `x*c`
is top. It fixes the unique central successor `z`; its other image
point is exactly one of the two `A` successors of `t`. Exactly one of
those `A` successors therefore moves to `z`.

The equivalence (7), with the same proof using centrality of `z,c`,
identifies these moved `A` successors with the `A` common middles from
`t` to `v`. Thus there is exactly one in this case. This proves that
every entry of `QP` is zero or one.

Each `A` vertex has two top neighbors at either end. The row and column
sums of `QP` are therefore `2α_t`. Equations (19)--(20) leave the
multisets `{0,2,2,2}` and `{1,1,2,2}`. The former is impossible: an
`α=2` row of the zero-one four-column matrix is all ones, whereas its
`α=0` column would have sum zero. Order the top vertices with the two
`α=1` vertices first. The `α=2` rows and columns are all ones, forcing

\[
 QP=
 \begin{pmatrix}
 0&0&1&1\\
 0&0&1&1\\
 1&1&1&1\\
 1&1&1&1
 \end{pmatrix}.
 \tag{22}
\]

In particular `rank(QP)=2` and `tr(QP)=2`.

### The reverse path matrix has incompatible rank

For `A` endpoints `a_i,a_j` with `j≠σ(i)`, there is no `B` common
middle by (18). The only possible ordinary middle is then top. Its
existence and strict degree descent give exactly one such middle.
Write

\[
 (PQ)_{ij}=1\quad(j\ne\sigma(i)),\qquad
 c_i=(PQ)_{i,\sigma(i)}\in\{0,1,2\}. \tag{23}
\]

The sum of all entries of `PQ`, counted through its top middle, is

\[
 \sum_{i,j}(PQ)_{ij}
 =\sum_{t\in T}\alpha_t^2=10.
\]

Its six off-permutation entries equal one, so `Σ_i c_i=4`. Also
`tr(PQ)=tr(QP)=2`. If `σ` were the identity, the trace would be four.
If `σ` were a three-cycle, all three diagonal entries would be one,
giving trace three. Thus `σ` is a transposition. Relabel so it swaps
zero and one and fixes two. The trace gives `c_2=0`, and the sum and
upper bounds then give `c_0=c_1=2`. Therefore

\[
 PQ=
 \begin{pmatrix}
 1&2&1\\
 2&1&1\\
 1&1&0
 \end{pmatrix},
 \qquad\det(PQ)=2. \tag{24}
\]

Over the rationals, invertibility of `PQ` makes `Q` injective and `P`
surjective. Consequently `rank(QP)=rank(P)=3`, contradicting (22).
This excludes (17) and completes the order-twelve proof.
