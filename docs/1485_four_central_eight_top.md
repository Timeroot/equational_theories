# Four central vertices and eight top vertices are impossible at minimum degree three

Research note, 18 September 2026. This is a pen-and-paper proof,
independent of the total order and not yet a Lean declaration.

**Theorem.** A finite E1485 magma with minimum translation degree
three cannot have four central vertices and eight top vertices.

The proof uses the finite uniform-fiber and sharp-neighbor theorems,
central incidence, and E1485. A small symbolic search suggested the
argument, but no enumeration or solver conclusion is a premise below.

## 1. The central incidence has two four-element top classes

Write `Z,T` for the central and top sets. Each central vertex has
three ordinary predecessors and successors. For a top vertex `t`,
write `k⁻_t,k⁺_t` for its central in-degree and out-degree.

No such degree is three: a full central in-degree or out-degree would
force `|T|=3²`, by the [incidence support argument](1485_small_central_defects.md).
Thus both degrees lie in `{1,2}`. The incidence moments

\[
\sum_T k^-=\sum_T k^+=12,\qquad
\sum_T k^-k^+=16
\]

force exactly four vertices of type `(2,1)` and four of type `(1,2)`.
Call these classes `A` and `B`, respectively.

Label the four central vertices by `0,1,2,3`. Label `A_j` by its
singleton central successor `j`, and `B_i` by its singleton central
predecessor `i`. These labels occur exactly once: in each central
row, three positive successor sizes sum to four, so exactly one of
the three top successors is of type `B`; use the dual argument for
`A`.

Let `M_ij` indicate that central vertex `i` precedes `A_j`.
Every row and column of `M` has sum two. The central successor set
of `B_i` is the complement of row `i` of `M`, because the
rectangles supplied by the top middles partition `Z×Z`.

Uniqueness of a central middle from `B_i` to `A_j` gives
`((J−M)M)_ij≤1`. Hence `M²≥J`, and its row sums, all four,
force `M²=J`. Put `N=J−M` and `N̄=J−N=M`. Both are
two-regular and

\[
N^2=\bar N^2=N\bar N=\bar NN=J_4.
\]

Let `K` record central-valued products of top endpoints, and
`F=J−K` the noncentral-valued ones. In the order `A,B`,

\[
K=\begin{pmatrix}\bar N&I\\J&N\end{pmatrix},
\qquad
F=\begin{pmatrix}N&J-I\\0&\bar N\end{pmatrix}. \tag{1}
\]

No classification of the possible matrix `N` is needed.

## 2. The finite packing rules used below

Every top left or right translation has nonempty fibers of size
three. A noncentral output has a non-top sharp predecessor and a
non-top sharp successor. Consequently no noncentral output can have
more than two top inputs in a fixed left or right translation.

Write `D` for ordinary adjacency within `T`. If top vertices
`u,v,b` satisfy `F_uv=1`, then E1485 and its dual give

\[
\begin{aligned}
D_{vb}=1,\ K_{bu}=1&\Longrightarrow (u*v)*b=v,\\
D_{bu}=1,\ K_{vb}=1&\Longrightarrow b*(u*v)=u.
\end{aligned}                                  \tag{2}
\]

For example, in the first line choose the central middle
`c=b*u`. The central path `v→b→c` gives `v*c=b`; choose top
`z` with `z*u=c` and apply E1485. The second line is dual.

For `D_vb=1`, the fiber `R_b⁻¹(v)` contains exactly the
`k⁻_v` central predecessors of `v`. Thus (2) can give at most
`3−k⁻_v` distinct noncentral inputs in that fiber. Dually the
left fiber at a top output `u` has `3−k⁺_u` noncentral inputs.

We also use the central-shadow identities

\[
Z*x=\operatorname{TopPred}(x),\qquad
x*Z=\operatorname{TopSucc}(x).                  \tag{3}
\]

For example, a top predecessor `t→x` has a central sharp
predecessor `z→t`; goodness gives `z*x=t`.

## 3. Reducing the possible top adjacency degrees

For each top vertex `x`, write its top out-degree as `2+t_x`
and its top in-degree as `2+s_x`. Central shadow counting gives

\[
\begin{array}{c|cc}
&A\text{ neighbors}&B\text{ neighbors}\\ \hline
\text{successors of }x&2t_x&2-t_x\\
\text{predecessors of }x&2-s_x&2s_x
\end{array}
\qquad t_x,s_x\in\{0,1,2\}.                   \tag{4}
\]

Indeed the successor counts satisfy `q_A+2q_B=4`, and the
predecessor counts satisfy `2p_A+p_B=4`.
Write `T_A=Σ_A t`, `T_B=Σ_B t`, and similarly `S_A,S_B`.
Counting edges in the four blocks gives

\[
2T_A+T_B=8,\qquad T_B=S_A,\qquad T_A=S_B.       \tag{5}
\]

First, no `v∈B` has `t_v=0`. Otherwise its two top successors
`b₁,b₂` both lie in `B`, and their central successor sets
partition `Z`. Its noncentral top inputs consist of three vertices
of `A` and two of `B`, by (1). At each `b_i`, the first line of
(2) applies to all three `A` inputs and exactly one `B` input;
the two `b_i` select different `B` inputs. This follows either
from the central partition or from `N N̄=J`.

Only two distinct noncentral inputs fit into `R_{b_i}⁻¹(v)`.
The three `A`-input values therefore have one repeated pair and
one singleton, since three equal top inputs are forbidden. The
additional `B`-input value must equal the singleton: it cannot be
a third distinct value, and joining the repeated pair would give
three inputs of the same value. Applying this to both `b_i` makes
the singleton value occur at three top inputs of `R_v`, a
contradiction. Dually no `x∈A` has `s_x=0`.

Next suppose `b∈B` has `t_b=2`, and let `v∈A` have the same
index, so `K_vb=1`. Both noncentral `A` inputs of column `v`
are ordinary successors of `b`. To see this, the central incidence
identity `DK=1(k⁻)ᵀ` gives

\[
DF=d_{\rm out}\mathbf1^T-\mathbf1(k^-)^T,
\]

whose entry `(b,v)` is `4−2=2`.

If `t_v≤1`, the two `A` inputs `u₁,u₂` of column `v`
have the same product with `v`. Each has two central predecessors;
their central predecessor sets partition `Z`, by `N̄N=J`.
Their two-element images under `c↦v*c` therefore cover
`TopSucc(v)`, of size at most three, and overlap. At an overlap,
the first line of (2) and the unique noncentral input of the
corresponding fiber force `u₁*v=u₂*v=a`.
But the second line of (2) gives `b*a=u₁` and `b*a=u₂`,
contradicting `u₁≠u₂`. Thus `t_v=2`.

This would give `T_A≥2`, while the already proved `t_x≥1` for
all four `x∈B` and `t_b=2` give `T_B≥5`, contradicting (5).
Therefore all four `B` vertices have `t=1`; (5) now gives

\[
T_A=2,\qquad S_A=4,\qquad S_B=2.
\]

Since every `A` vertex has `s≥1`, all of them have `s=1`.

## 4. Four useful matrix identities

Write

\[
D=\begin{pmatrix}X&Y\\Z_0&W\end{pmatrix}
\]

in the order `A,B`. The preceding counts make `Z₀` two-regular,
every column of `X` have sum one, and every row of `W` have sum
one. The top central-incidence identities, multiplied using (1), give

\[
\boxed{NX=W\bar N=Z_0,\qquad
Z_0N=\bar NZ_0=J.}                             \tag{6}
\]

For clarity, use
`DF=d_out 1ᵀ−1(k⁻)ᵀ` and
`FD=1 d_inᵀ−k⁺1ᵀ`. Their lower-left blocks give
`Z₀N=N̄Z₀=J`. The upper-left block of the second identity is
`NX+(J−I)Z₀=2J`, giving `NX=Z₀`. The lower-right block of
the first gives `Z₀(J−I)+WN̄=2J`, hence `WN̄=Z₀`.

There cannot be a vertex of `A` with `t=2`: since `T_A=2`,
`X` would have one row of four ones and all other rows zero.
Then `NX` would have two rows of four ones and two zero rows,
contrary to two-regularity of `Z₀`. Dually no `B` vertex has
`s=2`, using `WN̄=Z₀` and column sums. Hence

\[
t_x\le1\ (x\in A),\qquad s_x\le1\ (x\in B). \tag{7}
\]

## 5. The two boundary families of noncentral values

The overlap argument in section 3 now applies to every column
`v∈A`: its two noncentral `A` inputs have a common value `a_v`,
and

\[
a_v*b=v\qquad(b\in\operatorname{TopSucc}(v)).
\]

The union of their two central-parameter images is the whole top
successor set, which justifies the displayed assertion also at
points outside the initial overlap.

For central `h`, substitute `b=v*h`. The auxiliary-relation fiber
identity gives `(h*a_v)*v=a_v`. By (3), all top predecessors of
`a_v` are therefore top inputs of `R_v⁻¹(a_v)`. That fiber is
already exhausted by its two `A` inputs and one non-top sharp
predecessor. Thus

\[
\operatorname{TopPred}(a_v)=\{u\in A:N_{uv}=1\}. \tag{8}
\]

Dually each missing `B×B` row `u` has a common value `b_u`, with

\[
\operatorname{TopSucc}(b_u)
=\{v\in B:\bar N_{uv}=1\}.                    \tag{9}
\]

The families `{a_v}` and `{b_u}` are disjoint. Indeed a value
`b_u` has the top predecessor `u∈B`, whereas (8) puts all top
predecessors of every `a_v` in `A`.

## 6. The off-diagonal `A×B` table has incompatible singleton counts

The remaining noncentral `A×B` cells are exactly the twelve
off-diagonal cells, by (1). Each row has three such values.

Every `u∈A` has a unique `A` predecessor `f(u)`, since `X`
has column sums one. Apply the second line of (2) at that
predecessor. The eligible right inputs consist of all three
off-diagonal `B` inputs and one `A` input, with value
`a_{L(u)}`, where `L(u)` is the unique index satisfying

\[
N_{u,L(u)}=1,\qquad \bar N_{L(u),f(u)}=1.
\]

Only two noncentral inputs fit into the relevant left fiber. As in
section 3, the three off-diagonal row values must therefore consist
of a repeated pair and one singleton; the singleton is exactly
`a_{L(u)}`, and the pair has a different value.

Dually, if `g(v)` is the unique `B` successor of `v∈B`,
each off-diagonal column consists of a repeated pair and a distinct
singleton `b_{R(v)}`, where

\[
\bar N_{R(v),v}=1,\qquad N_{g(v),R(v)}=1.
\]

Both maps `L,R` are permutations. The number of preimages of
`v` under `L` is the diagonal entry `(N̄XN)_vv`; the number of
preimages of `u` under `R` is `(N̄WN)_uu`. Equation (6), the
column sums of `X`, and the row sums of `W` give

\[
\bar NXN=JXN-NXN=2J-Z_0N=J,
\qquad
\bar NWN=\bar N(J-Z_0)=2J-\bar NZ_0=J.
\]

Moreover the four values `a_v` are distinct. If `a_v=a_{v'}`
for distinct indices, (8) says that columns `v,v'` of `N`
coincide. Choose `u` with `L(u)=v`. The two `A` inputs
`v,v'` in row `u` then have this common value, as does its
off-diagonal row singleton `a_{L(u)}`. This gives three top
inputs of a noncentral value in a size-three fiber, which must
also contain a non-top sharp input: a contradiction. The four
values `b_u` are distinct by the dual argument.

We now have four distinct row-singleton colors `a_v` and four
distinct column-singleton colors `b_u`, with the two sets disjoint.
No cell can be a singleton both in its row and in its column.
The twelve-cell table therefore has four row-singleton cells, four
column-singleton cells, and only four cells belonging to repeated
pairs in both directions.

Every row-singleton `a_v` occurs once more in its column. That
second occurrence cannot be another row singleton, because the four
row-singleton colors are distinct. It is therefore a double-pair
cell. These require four different double-pair cells. The four
column-singleton colors similarly require four different double-pair
cells, distinct from the first four because the `a` and `b`
families are disjoint. This requires eight such cells, when only
four are available. The contradiction proves the theorem.
