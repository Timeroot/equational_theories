# A full central core excludes order six times a square

Research note, 18 September 2026. This is a pen-and-paper proof, not a
Lean declaration. It excludes order `6r²` when the minimum translation
degree is `r` and there are exactly `r²` central vertices. The latter
hypothesis is known for minimum degree two, but not for arbitrary `r`.

**Theorem.** A finite E1485 magma with minimum translation degree `r`
and exactly `r²` central vertices cannot have order `6r²`.

In particular, no E1485 magma of order 24 has minimum translation degree
two. This does not exclude the order-24 minimum-degree-three case.

We use the [finite graph and fiber theorems](1485_graph_research.md),
the [full central core](1485_full_central_core.md), and the
[full-core degree gaps and sharp-regularity theorem](1485_min_two_neighbor_gap.md).
The only linear-algebra input beyond matrix multiplication is the
standard peripheral-spectrum theorem for a finite irreducible
nonnegative matrix (Perron--Frobenius theory).

## The four degree classes

Suppose such a magma exists. Its maximum degree is `6r`. The degree-gap
theorem excludes degrees in `(r,2r)` and `(2r,3r)`. Complementary-degree
reciprocity then excludes `(3r,6r)` as well: the complement of any such
degree lies in `(r,2r)`. Thus only `r,2r,3r,6r` can occur. The same
gap theorem says the smallest noncentral degree is exactly `2r`, and
its complement `3r` also occurs.

Write `Z,A,B,T` for the degree classes `r,2r,3r,6r`, respectively.
The full-central-core theorem gives `|Z|=|T|=r²`. Every vertex has
exactly `r` sharp predecessors and `r` sharp successors: this is known
for the central and top vertices and for degrees `2r` and `3r`.
Sharp edges between `A` and `B` therefore give `r|A|=r|B|`.
Consequently, on putting `N=2r²`,

\[
 |A|=|B|=N=2r^2. \tag{1}
\]

Every vertex has exactly `r` top neighbors in each direction. The
ordinary-edge degree inequality and the sharp-edge characterization
therefore give these other neighbors:

* A vertex in `A` has `r` neighbors in `B`, all sharp, in each direction.
* A vertex in `B` has `r` neighbors in `A`, all sharp, and `r` ordinary
  neighbors in `B`, in each direction.

No vertex of `A∪B` is adjacent to a central vertex.

For a top vertex `t`, every nonempty fiber of `L_t` has size `r`.
For an output `v`, this fiber contains all `r` sharp successors of `v`:
each path `t→v⇒w` is good. It is therefore exactly that sharp
successor set. In particular, `t*x⇒x` for every `x`, and hence

\[
 T*A\subseteq B,\qquad T*B\subseteq A,\qquad T*T\subseteq Z.
 \tag{2}
\]

The dual conclusions also hold. Equivalently, the canonical `r`-regular
auxiliary relation from the full-central-core theorem is now exactly the
sharp relation.

## All paths within the two middle classes are good

Put `H=A∪B`. A two-edge path in `H` which contains an edge between
`A` and `B` is good, because that edge is sharp. It remains to consider
paths inside `B`.

An internal edge `b→c` in `B` has exactly `6r²/(3r)=2r` good extensions.
None is top: `b*T` is the sharp successor set of `b`, lying in `A`,
so a top input cannot give output `c∈B`. The `2r` non-top successors
of `c` are its `r` successors in each of `A` and `B`.
They must therefore all give good extensions. We have proved

\[
 \boxed{\text{Every two-edge path contained in }H\text{ is good}.}
 \tag{3}
\]

Let `P,Q,D` be the adjacency matrices of `A→B`, `B→A`, and `B→B`,
respectively. Each is an `N×N` zero-one matrix with every
row and column sum `r`. Thus adjacency on `H` is

\[
 \begin{pmatrix}0&P\\Q&D\end{pmatrix}.
\]

By (3) and unique goodness, its square has only zero-one entries.
In particular `PD`, `DQ`, and `D²` are zero-one. Its `B×B` block
is `QP+D²`, with every row sum `2r²=N`, and hence

\[
 \boxed{QP+D^2=J_N.} \tag{4}
\]

This also proves `B*B⊆H`.

## Five-cycles give two transpose identities

Consider a path `a→b→c→d` with all four vertices in `H`, and close
it by its unique good return `d→e→a`, where `e=d*a`.
The paths at positions `0,1,3` of this five-cycle are good by (3)
and the definition of `e`. The five-cycle law forces the remaining
two paths to be good as well.

If the first edge `a→b` lies inside `B`, then `e` cannot be top:
otherwise the path `e→a→b` would be good, whereas `T*B⊆A` says
its middle cannot lie in `B`. Dually, if the last edge lies inside
`B`, then `e` cannot be top. It cannot be central either, since
central vertices have only top neighbors.

Apply this first to paths with class pattern `B,B,B,A`. Their return
product lies in `H`; the only possible internal middle for an `A×B`
pair is in `B`. Therefore

\[
 \operatorname{supp}(D^2Q)\subseteq
 \operatorname{supp}((PD)^T).
\]

Each entry of `D²Q` is at most `r`, because `D²` is zero-one and
each column of `Q` has `r` ones. Its row sum is `r³`. The zero-one
matrix `(PD)^T` has row sum `r²`. Equality of these total bounds gives
the first identity below; paths of pattern `A,B,B,B` give the second:

\[
 \boxed{D^2Q=r(PD)^T,\qquad PD^2=r(DQ)^T.} \tag{5}
\]

## The internal graph of degree `3r` has no closed five-walk

Normalize `p=P/r`, `q=Q/r`, `d=D/r`, and put `J_0=J_N/N`.
These normalized matrices are doubly stochastic. Equations (4)--(5)
become

\[
 qp+d^2=2J_0,\qquad
 d^2q=d^Tp^T,\qquad pd^2=q^Td^T.
 \tag{6}
\]

Since multiplication by a doubly stochastic matrix leaves `J_0`
unchanged,

\[
 \begin{aligned}
 d^4&=(2J_0-qp)^2=(qp)^2,\\
 pqp&=p(2J_0-d^2)=2J_0-q^Td^T,\\
 d^4&=2J_0-qq^Td^T.
 \end{aligned}
\]

Taking the trace after multiplying by `d` gives

\[
 \operatorname{tr}(d^5)
 =2-\operatorname{tr}(qq^Td^Td)
 =2-\lVert dq\rVert_F^2=0. \tag{7}
\]

For the last equality, `DQ` is zero-one with `Nr²=2r⁴` ones, so
`dq=DQ/r²` has squared Frobenius norm `2r⁴/r⁴=2`.
Consequently `tr(D⁵)=0`: the digraph of `D` has no closed walk of
length five.

## Its graph must be bipartite

Multiplying the two identities in (5), and using (4), gives

\[
 \begin{aligned}
 D^2QP D^2&=r^4J_N-D^6,\\
 r^2D^TP^TQ^TD^T&=r^4J_N-r^2(D^T)^4.
 \end{aligned}
\]

The left sides agree. Thus `D⁶=r²(Dᵀ)⁴`. Transposing and cubing
this identity yields

\[
 D^{18}=r^6(D^T)^{12}=r^{10}D^8. \tag{8}
\]

Every nonzero eigenvalue of `D` therefore has modulus `r`.

Because every in-degree and out-degree of `D` is `r`, its strongly
connected components have no edges between them. For completeness,
the condensation graph is acyclic; a source component has zero net
outgoing flow by equality of total in-degree and out-degree, so it has
no outgoing edges either. Remove it and repeat.

In each component, take its cyclic classes, with the period of the
component as their number. Every vertex has `r²` distinct two-step
successors, all in one cyclic class, since `D²` is zero-one and has
row sum `r²`. Each cyclic class consequently has at least `r²` vertices.
With only `2r²` vertices altogether, the possibilities are:

* one primitive component of size `2r²`;
* two primitive components, each of size `r²`;
* one component of period two, with two cyclic classes of size `r²`.

Perron--Frobenius theory says that a primitive component has just one
eigenvalue of modulus `r`, namely `r`, with multiplicity one. By (8)
all its other eigenvalues are zero. Such a component contributes
`r⁵>0` to `tr(D⁵)`. A period-two component has the two peripheral
eigenvalues `r,−r`, again each simple, and all other eigenvalues zero;
its contribution is zero. Equation (7) therefore excludes both primitive
possibilities.

We obtain a bipartition `B=B_0⊔B_1`, with `r²` vertices in each part.
Every `D` edge crosses the parts, and

\[
 D^2=\begin{pmatrix}J_{r^2}&0\\0&J_{r^2}\end{pmatrix},\qquad
 QP=\begin{pmatrix}0&J_{r^2}\\J_{r^2}&0\end{pmatrix}.
 \tag{9}
\]

## One instance of E1485 is now impossible

The first identity in (5) makes each entry of `D²Q` either zero or
`r`. By (9), its entry in a row indexed by `B_i` is the number of
predecessors from `B_i` of the corresponding `A` vertex. Every column
of `Q` has `r` ones; all must therefore lie in the same part.

Let `A_i` be the vertices of `A` whose `r` sharp predecessors lie in
`B_i`. Counting `Q` edges gives `|A_i|=r²`. Equation (9) then forces
every `P` edge out of `A_i` to end in `B_{1-i}`. Thus internal
adjacency in `H` has the following class pattern:

\[
 A_i\to B_{1-i},\qquad B_i\to A_i,\qquad B_i\to B_{1-i}.
 \tag{10}
\]

There is no internal middle for a pair in `B_i×A_i`, so its good
middle must be top. The same holds for `A_i×B_{1-i}`. For a pair
in `B_i×B_i`, equation (9) gives a unique middle in `B_{1-i}`,
and its path is good by (3). Therefore

\[
 B_i*A_i\subseteq T,\qquad
 A_i*B_{1-i}\subseteq T,\qquad
 B_i*B_i\subseteq B_{1-i}. \tag{11}
\]

Choose `x∈A_i` and `y,z∈B_i`. Then `y*x∈T`, whereas
`z*y∈B_{1-i}` and consequently `x*(z*y)∈T`.
Equation E1485 asserts

\[
 x=(y*x)*(x*(z*y))\in T*T\subseteq Z.
\]

This contradicts `x∈A_i`, since the degree-`r` and degree-`2r` classes
are disjoint. The theorem follows.
