# Five central and ten top vertices are impossible at minimum degree three

Research note, 18 September 2026. This is an analytic finite proof,
not a Lean declaration or a finite search over multiplication tables.

**Theorem.** A finite E1485 magma with minimum translation degree
`r=3` cannot have five central vertices and ten maximum-degree
vertices. No restriction on its order or intervening degree classes
is imposed.

The proof uses central incidence, the original E1485 identity, uniform
top-translation fibers of size three, and existence of sharp neighbors.
It does not assume a full central core.

## 1. The central-incidence matrices are two five-cycles

Write `Z,T` for the central and top classes, and let `B:Z→T`,
`C:T→Z` be ordinary incidence. Thus `|Z|=5`, `|T|=10`,
every row of `B` and column of `C` has sum three, and

\[
BC=J_5,\qquad K=CB\le J_{10}.
\]

Let `k⁻,k⁺` be the central in-degrees and out-degrees on `T`.
Their first and second moments are

\[
\sum k^- =\sum k^+=15,\qquad \sum k^-k^+=25.
\]

No entry can equal three: the
[full-entry incidence lemma](1485_small_central_defects.md)
would then force `|T|=r²=9`. Thus all entries are one or two.
Each vector has five twos, and the second moment makes their
two-supports coincide. Partition `T=U⊔V`, where the five vertices
of `U` have `(k⁻,k⁺)=(1,1)` and the five of `V` have `(2,2)`.

Every central row and column has weight pattern `(1,2,2)`, because
its three neighboring central-degree weights sum to five. Label
`Z={z_i}` and `U={U_i}` so that `U_i` has central predecessor
`z_i`. Then

\[
B=[I\ R],\qquad C=\begin{bmatrix}P\\S\end{bmatrix},
\qquad RS=J_5-P,                                \tag{1}
\]

where `P` is a permutation matrix and `R,S` are five-by-five
zero-one matrices with all row and column sums two.

The matrix `J_5−P` is invertible over the rationals: if
`Px=(Σx)1`, then `x` is constant and must vanish. Hence `R,S`
are invertible. A two-regular bipartite graph on five row and five
column vertices is either one ten-cycle or a four-cycle plus a
six-cycle. The latter gives a singular two-by-two all-one block.
Thus both `R` and `S` are incidence matrices of single five-cycles.

The block `SR` of `K` is zero-one with row and column sums four,
so it is `J_5−Q` for another permutation matrix `Q`. Therefore

\[
K=\begin{pmatrix}P&PR\\S&J_5-Q\end{pmatrix},
\qquad PR=RQ,\qquad QS=SP.                     \tag{2}
\]

The last two identities follow by computing `RSR` and `SRS`
in both orders. Use row-map notation
`P_{i,p(i)}=1`, `Q_{u,q(u)}=1`. The graph on the five `V`
indices whose edges are the two-element rows of `R` is a five-cycle;
call it `G`. The relation `PR=RQ` says that `q` permutes the
edges of `G`, so `q` is an automorphism of this cycle.

## 2. The ordinary top block contains many degree-two rows and columns

Let ordinary adjacency on `T` be

\[
D=\begin{pmatrix}X&Y\\Z_0&W\end{pmatrix},
\]

in the partition `U⊔V`. Central-endpoint uniqueness gives
`BD=J_{5,10}` and `DC=J_{10,5}`. In particular,

\[
X+RZ_0=J,\quad Y+RW=J,\quad Z_0P+WS=J.
\]

All blocks are zero-one. Eliminating `Z_0` from the first equation
therefore gives

\[
RW\le J,\qquad WS\le J,\qquad RWS\ge J.       \tag{3}
\]

Each column of `W` has at most two ones, since its selected
two-element columns of `R` must be disjoint. Each row of `W`
similarly has at most two ones, using `WS≤J`.

If two row indices of `W` form an edge of `G`, their degrees have
sum at least three: the corresponding row sum of `RWS≥J` is
twice that sum and is at least five. Consequently no row of `W`
is zero, and its degree-one rows form an independent set in a
five-cycle. There are at most two degree-one rows, hence at least
three degree-two rows.

The column-dual argument uses the five-cycle formed by the two-element
columns of `S`. It gives no zero columns and at most two degree-one
columns. Summarizing,

\[
\boxed{\#\{\text{degree-two rows of }W\}\ge3,
\qquad\#\{\text{degree-one columns of }W\}\le2.} \tag{4}
\]

## 3. Witness intersections cannot connect three missing inputs

Fix a target `v∈V`. It has central in-degree two. For a top input
`u` with `u*v` noncentral, and for each central predecessor
`c∈Z∩Col(u)`, put `b=v*c`. As in the
[packing lemma](1485_boundary_central_defect.md), these are distinct
top successors of `v`, and E1485 gives

\[
(u*v)*b=v.
\]

Call this witness set `S_{u,v}`. If two missing inputs have a
common witness `b`, their products with `v` are equal: the fiber
`R_b^{-1}(v)` has size three and already contains the two central
predecessors of `v`, so it has only one noncentral input.

Thus all inputs in a connected component of the witness-intersection
graph have the same noncentral product. No component can contain
three top inputs. Indeed their common product `a` would have all
three in `R_v^{-1}(a)`, together with a non-top sharp predecessor
`f⇒a`, since `f⇒a→v` gives `f*v=a`. This would overfill the
size-three fiber. We have proved

\[
\boxed{\text{every witness-intersection component has size at most two.}}
                                                        \tag{5}
\]

The dual statement applies to a missing row with left endpoint in `V`.

## 4. Degree-two rows and columns of W must contain specified entries

Suppose row `v` of `W` has degree two. The row of
`Z_0P+WS=J` then makes row `v` of `Z_0` a singleton, say
`e_z`. Comparing with `R_{z,\cdot}S=1-P_{z,\cdot}` and using
invertibility of `S` gives

\[
W_{v,\cdot}=R_{z,\cdot}.                       \tag{6}
\]

The three top successors of `v` are consequently `U_z` and the
two `V` vertices indexed by row `z` of `R`. Their central-successor
sets partition `Z`: one singleton `{p(z)}` and two disjoint pairs.

There is exactly one missing input in `V` for the target `v`, namely
`u=q^{-1}(v)`, by the `V×V` block in (2). Its central-predecessor
set is the two-element column `R_{\cdot,u}`. The missing inputs
in `U` are exactly the other three central indices, because

\[
(PR)_{i,v}=R_{i,q^{-1}(v)}=R_{i,u}.
\]

The witnesses for `u` select the two cells of the displayed central
partition containing its two central predecessors. They are distinct:
otherwise one top endpoint pair would have two central middles.
If both selected cells were pairs, each would contain a different
additional point outside `R_{\cdot,u}`. These two additional points
are distinct missing `U` inputs whose singleton witness sets intersect
the two witnesses for `u`, respectively. This would make a component
of three missing inputs, contrary to (5).

Therefore the singleton is selected:
`R_{p(z),u}=1`. By `PR=RQ`, this is `R_{z,q^{-1}(u)}=1`.
Together with (6), it proves

\[
\boxed{\deg W_{v,\cdot}=2\Longrightarrow
       W_{v,q^{-2}(v)}=1.}                      \tag{7}
\]

For clarity, the column-dual permutation direction is explicit.
If column `u` of `W` has degree two, the equation `Y+RW=J`
and invertibility of `R` give

\[
W_{\cdot,u}=S_{\cdot,z},\qquad
Y_{\cdot,u}=e_{p^{-1}(z)}
\]

for some central index `z`. The unique missing `V` target is
`v=q(u)`. Applying the dual witness argument to the central-predecessor
partition forces `S_{v,p^{-1}(z)}=1`. The identity `QS=SP`
turns this into `S_{q(v),z}=1`, and hence

\[
\boxed{\deg W_{\cdot,u}=2\Longrightarrow
       W_{q^2(u),u}=1.}                         \tag{8}
\]

Set `θ=q^{-2}`. Thus degree-two rows contain their `θ` entry,
and degree-two columns contain their `θ^{-1}` entry. The permutation
`θ` is an automorphism of the five-cycle `G`.

## 5. An impossible injection into the degree-one columns

Take a degree-two row `v` of `W`. Besides its prescribed entry
at `θ(v)`, it has exactly one other entry, at some `w≠θ(v)`.
By (6), the pair `{θ(v),w}` is an edge of `G`.

Suppose column `w` also had degree two. Equation (8) would put
another entry in that column at row `θ^{-1}(w)`. Since `θ` is
an automorphism, `{v,θ^{-1}(w)}` is an edge of `G`, and its
two vertices are distinct. Some row of `R` therefore contains both.
Multiplying that row by column `w` of `W` gives an entry at least
two in `RW`, contradicting (3).

Thus the extra entry of every degree-two row lies in a degree-one
column. Different rows must use different such columns. This injects
at least three degree-two rows into at most two degree-one columns,
contrary to (4). The contradiction proves the theorem.

## Corollary: five central vertices force exactly nine top vertices

Still assume `r=3` and `|Z|=5`, but do not prescribe `h=|T|`.
If any central in-degree or out-degree is three, the full-entry
incidence lemma gives `h=9` immediately.

Otherwise all central degrees lie in `{1,2}`. Writing `n_ij` for
the number of top vertices with `(k⁻,k⁺)=(i,j)`, the three
incidence moments give

\[
n_{22}=h-5,\qquad n_{12}=n_{21}=20-2h,
\qquad n_{11}=4h-35.
\]

Nonnegativity forces `9≤h≤10`. The theorem excludes ten, so
in all cases `h=9`. This does not yet exclude five central vertices:
the nine-top case remains open in general.
