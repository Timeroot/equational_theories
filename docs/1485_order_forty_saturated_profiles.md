# Saturated order-forty profiles cannot mix cosets

Research note, 19 September 2026. This is an analytic necessary
condition, not yet a Lean theorem. Assume an E1485 magma of order
40 has four central vertices, sixteen degree-five vertices, four
degree-eight vertices, and sixteen tops. Write these classes as
`Z,A,B,T`, respectively.

**Theorem.** Both top-profile families of `A` lie in single,
distinct Klein-four cosets. In particular the mixed-coset
possibility left by the
[large-class bound](1485_min_four_large_five_class.md) is impossible
at saturation. This note alone does not exclude the single-coset
possibility or the whole order.

## 1. The saturated profiles

Every vertex has four top neighbors in each direction. A vertex
of `A` has one sharp predecessor and successor in `B`; write
these as `G(a)` and `F(a)`. Each vertex of `B` has four sharp
neighbors on either side and no internal `B` neighbors. The map
`(G,F)` identifies `A` with `B×B`; write `a_ij` for the vertex
with `G(a_ij)=b_i` and `F(a_ij)=b_j`.

The preceding large-class theorem says that at least one of the
two profile families lies in one Klein-four coset. By duality,
assume this is the predecessor family `U_a=TopPred(a)`.
Each of its four transversals occurs four times. For a fixed
predecessor transversal, its four successor partners are all four
transversals of one other coset. This choice of successor coset
may initially depend on the predecessor transversal.

Identify the central alphabet with the two-dimensional vector space
`V=F₂²`, using the **same** identification for predecessor and
successor labels. Write `H(t),C(t)∈V` for the central predecessor
and successor of a top `t`. A top pair has central product exactly
when `C(t)=H(u)`.

Every permutation of four elements is affine over `V`: the affine
group has `4·6=24` elements. Klein-four cosets are exactly the
families with a fixed invertible linear part. Consequently the
predecessor transversals have the form

\[
U_p=\{t:C(t)=M H(t)+p\},\qquad p\in V,
\]

for a fixed `M∈GL(V)`. In a fixed sharp-predecessor row `i`,
the four successor transversals belong to one coset, so write

\[
U_{a_{ij}}=U_{p_{ij}},\qquad
V_{a_{ij}}=\{t:C(t)=N_iH(t)+q_{ij}\}.
\]

The `p_ij` in each column are a permutation of `V`, since the
four predecessor profiles in a sharp-successor fiber are disjoint.
The `q_ij` in each row are likewise a permutation of `V`.
The two profile cosets are distinct and have the same parity, so

\[
D_i=M+N_i\quad\text{is invertible}.
\]

Indeed their transversals meet exactly once. The fixed-partner-coset
rule supplies a function `D:V→GL(V)` such that

\[
D_i=D(p_{ij})\quad\text{for every }i,j.                 \tag{1}
\]

## 2. The top successor profiles of `B` partition the tops

For each predecessor profile `U_p`, the four associated successor
profiles partition `T`. Thus every top has four predecessors in
`A`. It also has one central predecessor and four top predecessors.
Its degree is ten, leaving exactly one predecessor in `B`.
The four sets `TopSucc(b_k)` therefore partition `T`.

The product `b_k*a_ij` must have a top middle: there are no
`A→A` or internal `B` edges, and neither endpoint permits a
central middle. Hence `TopSucc(b_k)∩U_p` is a singleton for
every `p`. Put

\[
\phi_k(p)=C\bigl(TopSucc(b_k)\cap U_p\bigr),
\]

where `C` is evaluated at that unique point. For each fixed `p`,
the four values `φ_k(p)` are distinct. Indeed the four points lie
in disjoint `B` successor profiles, and `C` is injective on `U_p`
because `M` is invertible.

## 3. One family of E1485 instances forces additive separation

Use

\[
(y*x)*(x*(z*y))=x
\]

with `x=a_ij`, `y=b_k`, and `z=b_l`, where `l≠j`.
We have `z*y=a_lk`. The product `a_ij*a_lk` is top, with
predecessor label

\[
H(a_{ij}*a_{lk})=D_i^{-1}(p_{lk}+q_{ij}).
\]

Here the sharp middle `b_j` is unavailable because `l≠j`;
the unique top middle is the intersection of the two displayed
affine transversals. Also `y*x=b_k*a_ij` is the top whose
successor label is `φ_k(p_ij)`.

The final product must be `a_ij`, not central. As `l` runs through
the three values different from `j`, the column-permutation property
makes the three forbidden predecessor labels all of `V` except
`D_i⁻¹(p_jk+q_ij)`. Thus

\[
\boxed{q_{ij}+p_{jk}=D_i\phi_k(p_{ij}).}                \tag{2}
\]

Subtract the equations for `k` and `k'`, using characteristic two.
For a fixed column `j`, the values `p_ij` run over `V`, and
(1) gives

\[
\phi_k(p)+\phi_{k'}(p)
=D(p)^{-1}(p_{jk}+p_{jk'})\qquad(p\in V).              \tag{3}
\]

The left side does not depend on `j`. Since `D(p)` is invertible,
neither does `p_jk+p_jk'`. Fixing a reference column therefore
gives vectors `d_i,e_j∈V` with

\[
\boxed{p_{ij}=d_i+e_j.}                                \tag{4}
\]

The four `e_j` are distinct: otherwise (3) would identify two
functions `φ_k,φ_k'`, contrary to their pointwise distinctness.
They therefore exhaust `V`.

For any fixed `i`, (1) and (4) now show that
`D(d_i+e_j)=D_i` for all four elements of `V`. Hence `D` is
constant. All `N_i=M+D_i` are the same, which proves that the
successor family also uses a single coset.

No enumeration of multiplication tables, sharp-regularity assumption,
or independent relabeling of the two central labels was used.
