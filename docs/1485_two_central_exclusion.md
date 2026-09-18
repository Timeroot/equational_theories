# Minimum degree two forces four central vertices

Research note, 18 September 2026. This note proves the remaining global
minimum-degree-two exclusion:

**Theorem.** A finite E1485 magma whose minimum translation degree is two
cannot have exactly two central vertices.

Together with the [three-central-vertex exclusion](1485_three_central_exclusion.md)
and the incidence bounds in [the minimum-degree-two note](1485_min_degree_two.md),
this gives **exactly four central vertices in every finite E1485 magma
of minimum degree two**. The proof does not assume involutive squaring
or restrict the number of occurring degrees. No assertion here has been
added to Lean.

We use the finite degree, uniform-fiber, and sharp-edge theorems in
[the graph note](1485_graph_research.md), and strict degree descent and
the three-degree product bound in [the image note](1485_image_research.md).

## Setup and the small-order issue

Suppose that the order is `n`, the minimum degree is two, and the
central set is `Z={z_0,z_1}`. The maximum degree is `s=n/2`; its
class `T` has four vertices. Every vertex has exactly two predecessors
and two successors in `T`, and each top vertex has exactly one central
predecessor and successor. Every nonempty translation fiber at a top
vertex has size two.

Degree three occurs: the minimum-degree-two note proves that its
absence is equivalent to having four central vertices. Hence `6|n`.
The possibility `n=6` is already excluded by the
[two-degree cardinality theorem](1485_two_degree_lower_bound.md), since
its only possible degrees would be two and three. Thus `n≥12`.
In particular degree-three vertices are not top, and degree-four
vertices, when they occur, are not top either. This reduction uses no
part of the order-twelve exclusion.

The products of two central vertices label the four top vertices
bijectively:

\[
 t_{ij}=z_i*z_j,
 \qquad z_i\to t_{ij}\to z_j,
 \qquad i,j\in\{0,1\}. \tag{1}
\]

Indeed every central endpoint pair has a unique top good middle, and
each top vertex has only one central predecessor and successor. A top
endpoint pair `t_{ij},t_{kl}` has a central common middle precisely
when `j=k`, in which case its product is `z_j`.

Write `A={a:d(a)=3}` and `B={b:d(b)=n/3}`. A vertex in `A` has two
top neighbors and one other neighbor in each direction. Existence of
sharp neighbors and the sharp-edge degree criterion show that these
other neighbors are its unique sharp predecessor and successor, both
in `B`.

## Degree-three top neighborhoods are parity classes

Fix `a∈A`, and write `P_a` and `Q_a` for its top predecessor and
successor sets. For each central vertex, unique goodness of paths
starting there shows that `P_a` meets its top row exactly once.
Dually, `Q_a` meets each central top column exactly once. Thus

\[
 P_a=\{t_{0,j_0},t_{1,j_1}\},
 \qquad Q_a=\{t_{k_0,0},t_{k_1,1}\}. \tag{2}
\]

Fix `t∈P_a`. The two-element fiber `L_t^{-1}(a)` contains the sharp
successor of `a`, since the corresponding two-edge path has a sharp
edge. Its other element must be top, because every preimage is an
ordinary successor of `a`. Hence exactly one of the two paths
`t→a→v`, for `v∈Q_a`, is good.

Such a path is bad exactly when its endpoints have a central middle.
One direction follows from uniqueness. For the other, a bad path with
middle degree three has good replacement of strictly smaller degree,
which must be central. Thus for `t=t_{ij}` and `v=t_{kl}`, goodness
is equivalent to `j≠k`. The preceding one-good-extension count forces
`k_0≠k_1`. The dual count, with a fixed top successor, forces
`j_0≠j_1`.

Consequently both top neighborhoods are parity classes: for suitable
bits `ε_a,η_a`,

\[
 P_a=\{t_{ij}:i\oplus j=\varepsilon_a\},\qquad
 Q_a=\{t_{ij}:i\oplus j=\eta_a\}. \tag{3}
\]

Here `⊕` is addition modulo two. In the rectangle `P_a×Q_a`, exactly
two endpoint pairs satisfy `j=k` and have central good middle. The
other two have good middle `a`. In particular every degree-three
vertex occurs as exactly two products of top vertices.

## There is only one degree-three vertex and one reciprocal-degree vertex

Take any `a,c∈A`. Its possible common middles consist of top vertices
and the unique sharp successor of `a` in `B`. If this `B` vertex did
not lead to `c`, the good middle would have to be top. Strict degree
descent would then force exactly one ordinary top middle.

But the top common-middle set is `Q_a∩P_c`. By (3), its cardinality
is either zero or two, never one. Hence every `A×A` endpoint pair
has a sharp `B` middle.

Fixing the second endpoint shows that all vertices of `A` have the
same sharp successor `b∈B`, since that endpoint has only one sharp
predecessor. This `b` has every vertex of `A` as a sharp successor
too. Thus for every `a∈A` there is a good path

\[
 b\Rightarrow a\Rightarrow b.
\]

Unique goodness gives `|A|=1`; denote its element by `a`. Every vertex
of `B` needs sharp neighbors in `A`, and `a` has just one sharp
predecessor and successor. Therefore `B={b}` as well, and

\[
 a\Rightarrow b\Rightarrow a,
 \qquad a*a=b,\qquad b*b=a. \tag{4}
\]

## Six top endpoint pairs need degree-four middles

There are sixteen ordered top endpoint pairs. Exactly eight have a
central good middle: each of the two central vertices contributes
its two predecessors times its two successors. By (3), exactly two
have good middle `a`.

The three-degree product bound gives

\[
 d(t*v)\le\frac{n^2}{(n/2)^2}=4\qquad(t,v\in T).
\]

Since `a` is the only degree-three vertex, the other six endpoint pairs
must all have degree-four good middles. In particular degree four
occurs, so `4|n`.

## Those degree-four middles have forced complementary neighborhoods

Let `u` be a degree-four vertex occurring as a product of two top
vertices. Besides its two top successors, it has two non-top successors.
Their degrees are at least `n/4` and less than `n/2`. Degree divisibility
therefore leaves just `n/4` and `n/3`: their integer complementary
degrees lie strictly above two and at most four. Successors of degree
`n/4` are sharp; the only possible successor of degree `n/3` is `b`.

There is at least one sharp successor. There cannot be two: if
`t*v=u` with `t,v∈T`, both sharp successors would already occupy the
two-element fiber `L_t^{-1}(u)`, leaving no room for its top input `v`.
Hence `u` has one sharp successor `c_+`, and

\[
 \operatorname{Row}(u)=\{c_+,b\}\sqcup Q_u,
 \qquad d(c_+)=n/4,\quad |Q_u|=2. \tag{5}
\]

The same possibilities hold for predecessors. To verify explicitly
that the sharp in-degree is also one, let `k^+,k^-∈{1,2}` be the
numbers of sharp successors and predecessors. Reciprocal-degree
balance, after canceling the identical two top contributions, says

\[
 \frac{4k^++3(2-k^+)}n
 =\frac{4k^-+3(2-k^-)}n.
\]

Thus `k^-=k^+=1`. In particular `b→u`, and for a sharp predecessor
`c_-` we have

\[
 \operatorname{Col}(u)=\{c_-,b\}\sqcup P_u,
 \qquad d(c_-)=n/4,\quad |P_u|=2. \tag{6}
\]

The nonempty fibers of `L_b` have size three. Its fiber at `u` is
contained in `Row(u)`, contains `c_+` by the good path `b→u⇒c_+`,
and does not contain `b`, because `b*b=a≠u`. Equation (5) therefore
gives the exact fiber

\[
 L_b^{-1}(u)=\{c_+\}\sqcup Q_u.
\]

On the other hand, sharpness of `b⇒a` gives

\[
 L_b^{-1}(a)=\operatorname{Row}(a)=\{b\}\sqcup Q_a.
\]

These fibers are disjoint, so their two-element top parts are
complements in the four-element set `T`. The dual argument with
`R_b` gives the predecessor statement. Thus every degree-four top-top
output satisfies

\[
 \boxed{P_u=T\setminus P_a,\qquad Q_u=T\setminus Q_a.} \tag{7}
\]

## The final endpoint count

The two sets on the right side of (7) are again parity classes. Their
product rectangle has four endpoint pairs, exactly two of which have
a central common middle by the criterion `j=k` following (1).
Consequently all degree-four outputs of top-top products can occur
only on the other two endpoint pairs of this one fixed rectangle.

But six distinct ordered top endpoint pairs require degree-four good
middles. They cannot all belong to a two-element set. This contradiction
excludes exactly two central vertices.

## Consequences

The minimum-degree-two incidence theorem leaves central cardinalities
two, three, or four. This note excludes two, and the
[three-central-vertex theorem](1485_three_central_exclusion.md) excludes
three. Therefore every finite E1485 magma of minimum degree two has
exactly four central vertices and no degree-three vertices.

For every central `h`, its central coordinate rectangle
`B_h={u*v:u∈Row(h),v∈Col(h)}` has four elements and contains every
central vertex. Hence `B_h` is exactly the central set in this case.
This is a finite minimum-degree-two result, not a claim of unrestricted
central rectangle closure.
