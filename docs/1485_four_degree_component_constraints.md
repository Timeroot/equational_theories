# Sharp-path components and the minimum-six four-degree theorem

Research note, 18 September 2026. Assume a finite E1485 magma has a
full central core and exactly four degrees

\[
r,\quad2r,\quad b,\quad2b,\qquad n=2rb.
\]

Use the notation and established identities of the
[Top-return note](1485_four_degree_top_return_bounds.md). This note
proves that the conditional sharp-regularity theorem extends from
`r≤5` to `r≤6`; consequently these full-core four-degree models
have order `8r²`. It does not prove full central core in general,
exclude every all-irregular model for larger `r`, or settle spectra
with more than four degrees. No assertion here is a Lean declaration.

Throughout the component analysis suppose the model is irregular.
Then every high vertex is irregular, and

\[
2\le c:=\min k_a\le k_a\le r-c,\qquad b>3r,
\qquad m\le2r(r-c).
\tag{1}
\]

Put `t=b-3r`, `d₀=b-2r=r+t`, and `ℓ=r1-k`.

## A commuting nonnegative matrix

Recall the exact identities

\[
RK=G^T\operatorname{diag}(k),\qquad
KR=\operatorname{diag}(k)G^T. \tag{2}
\]

The row-stochastic matrix

\[
W=\frac1r\operatorname{diag}(k)^{-1}K
\]

has positive invariant measure `k`: indeed `K` has row and column
sums `rk`. The nonnegative integer matrix
`B=R diag(k)` commutes with `W`, because

\[
BW=\frac1r RK=\frac1rG^T\operatorname{diag}(k)=WB.
\tag{3}
\]

Partition `H` into the communicating components `H_i` of `K`.
They are all closed. One way to see this is that a finite directed
graph with equal in-degree and out-degree at each vertex has no edge
between distinct strongly connected components: sum the degree
balance over a source component of its condensation graph.

Each `A` vertex has nonempty sharp predecessor and successor sets;
every predecessor is joined by a `K=QP` edge to every successor.
Thus all these high vertices lie in the same component. This
partitions `A` into matching sets `A_i`, and makes `P,Q,K` block
diagonal. Write

\[
m_i=|A_i|,\qquad h_i=|H_i|,\qquad
S_i=\sum_{a\in H_i}k_a^2,\qquad s_i=S_i/m_i.
\]

Then `Σ_{H_i}k=rm_i`, and all `m_i,h_i` are positive.

For a pair of components, equation (3) gives
`W_i B_ij=B_ij W_j`. Therefore `B_ij1` is harmonic for the
finite irreducible stochastic matrix `W_i`, so it is constant.
There is a nonnegative integer `C_ij` with

\[
\boxed{R_{ij}k_j=C_{ij}\mathbf1.} \tag{4}
\]

For completeness, the dual weighted column sum is constant as well.
The row vector `k_i^T B_ij` is invariant under `W_j`, so it is a
multiple of the unique invariant row vector `k_j^T`. Comparing
total weighted sums gives

\[
\boxed{R_{ij}^Tk_i=\frac{m_i}{m_j}C_{ij}\mathbf1.} \tag{5}
\]

In particular `R_ii k_i=R_ii^T k_i=C_ii1`.

## Exact off-diagonal component counts

The identity `PDQ=r(J-(PQ)^T)` gives, for distinct components,

\[
P_iD_{ij}Q_j=rJ.
\]

The matrices `PD,DQ` are zero-one, each row of `P_i` and column
of `Q_j` has `r` ones, and every other relevant sharp degree is
positive. Entrywise saturation therefore forces

\[
\boxed{P_iD_{ij}=J,\qquad D_{ij}Q_j=J.} \tag{6}
\]

Summing these identities yields

\[
k_i^TD_{ij}=m_i\mathbf1^T,\qquad
D_{ij}k_j=m_j\mathbf1. \tag{7}
\]

Moreover `F` is supported on `K`, so both have zero off-diagonal
component blocks. Hence

\[
(D^2)_{ij}=E_{ij}=J-G_{ij}\quad(i\ne j). \tag{8}
\]

The following weighted calculation records all middle components,
including the two endpoint components. Global row and column
degrees of `D`, together with (7), give

\[
\begin{aligned}
k_i^TD_{ii}\mathbf1
&=rm_i(b-r)-S_i-m_i(h-h_i),\\
\mathbf1^TD_{ii}k_i
&=rm_i(b-r)-S_i-m_i(h-h_i).
\end{aligned}
\]

Consequently

\[
\begin{aligned}
k_i^T(D^2)_{ij}k_j
&=m_j\,k_i^TD_{ii}\mathbf1
 +m_i\,\mathbf1^TD_{jj}k_j
 +m_im_j\sum_{q\ne i,j}h_q\\
&=m_im_jm-m_jS_i-m_iS_j,
\end{aligned}
\]

where `m+h=2r(b-r)` is used in the final simplification. Subtract
this from `k_i^TJk_j=r²m_im_j` in (8):

\[
\boxed{k_i^TG_{ij}k_j
=m_im_j\bigl(r^2-m+s_i+s_j\bigr).} \tag{9}
\]

The block form of `GQ=r(PR)^T` gives
`G_ij k_j=r R_ji^T k_j`. Combining this with (4) and (9), with
indices exchanged where necessary, proves

\[
\boxed{C_{ij}=\frac{m_j}{r^2}
  \bigl(r^2-m+s_i+s_j\bigr)\quad(i\ne j).} \tag{10}
\]

The bracket is symmetric, so `C_ij>0` exactly when `C_ji>0`.

## The off-diagonal canonical component graph is a matching

If `C_ij>0`, equations (4)--(5) show that every vertex of `H_j`
has an incoming canonical `R` edge from `H_i`. Fix one such edge
`a R b`, with `a∈H_i`, `b∈H_j`. It has exactly `d₀=b-2r`
bad high extensions. The endpoints of every bad high path lie in
the same `K` component, because its replacement belongs to the
support of `K`. Thus all these extensions from `b` end in `H_i`.

If a component had canonical neighbors in two distinct other
components, each of its vertices would therefore have at least
`2d₀` high successors. Its actual high degree is `d₀+ℓ_a<2d₀`,
since `ℓ_a<r<d₀`. This is impossible. In conjunction with the
symmetry of positivity in (10), the positive off-diagonal component
pairs form a disjoint union of undirected edges: a matching.

There is a particularly useful small-minimum consequence. Since
`S_i≥cΣ_{H_i}k=crm_i`, equations (1) and (10) give

\[
r^2-m+s_i+s_j
\ge r^2-2r(r-c)+2rc=r(4c-r).
\]

If `r<4c`, every distinct component pair is positive. A complete
graph which is a matching has at most two vertices. Therefore

\[
\boxed{r<4c\quad\Longrightarrow\quad
K\text{ has at most two communicating components}.} \tag{11}
\]

## Minimum degree six: the one-component case

The previous bounds already show that any irregular case with `r=6`
must have

\[
c=2,\qquad k_a\in\{2,3,4\},\qquad
b\in\{19,20,21\},\qquad m\le48. \tag{12}
\]

Here `b=22` was excluded in the preceding note because its class
bounds force every `k_a=2`, contrary to the constant-sharp-degree
theorem. Also `h=12(b-6)-m≥108`.

Suppose first that `K` has one communicating component. Equation
(4) gives an integer constant `C` with `Rk=C1`. Summing and using
the column sums `ℓ` of `R` gives

\[
C=\frac1h\sum_a k_a(6-k_a).
\]

The summands are eight for `k=2,4` and nine for `k=3`. Thus
integrality forces either all `k=3`, or no `k=3`. The former is
an excluded constant irregular sharp degree, so only `k=2,4`
remain and `C=8`.

A `k=2` vertex has four `R` successors, whose sharp degrees are
at least two and sum to eight; all are therefore two. A `k=4`
vertex has two such successors, whose sharp degrees are at most
four and sum to eight; all are four. Thus `R` preserves `k`, and
`R^Tk=8·1` as well. The vector identities for `G` become

\[
Gk=G^Tk=48\mathbf1. \tag{13}
\]

Write `h₂,h₄` for the two sharp-degree counts. The endpoint bound
`G_da=1⇒k_a+k_d≤6` prohibits the `4→4` block of `G`.
Every row and column at a `k=4` vertex therefore has exactly 24
ones, all at `k=2` vertices. Summing (13) over the `k=2` rows
now gives

\[
\boxed{|G|=24h_2.} \tag{14}
\]

Explicitly, if `u` counts the `2→2` entries, the two cross-block
totals are both `24h₄`, and `2u+4(24h₄)=48h₂`. The total is
therefore `u+48h₄=24h₂`.

Put `T=m+h=12(b-6)`. The sharp incidence count gives

\[
h_4=4m-T,\qquad h_2=2T-5m.
\]

Substituting these and (14) into
`|G|=((144-m)/2)(h-m)-Σℓ²`, with
`Σℓ²=16h₂+4h₄`, simplifies to

\[
m^2-(6b-76)m-48b+288=0. \tag{15}
\]

But `b≥19` and `0<m≤48` imply that the left side is at most
`m²-38m-624`. This convex quadratic is strictly negative throughout
`[0,48]`, since its values at the endpoints are `-624` and `-144`.
This contradiction excludes the one-component case.

## Minimum degree six: the two-component case

It remains to consider exactly two components, since `6<4c=8`
and (11) applies. Put

\[
\alpha=36-m+s_1+s_2.
\]

Equation (10) gives `C₁₂=m₂α/36` and `C₂₁=m₁α/36`.
Using the column sums of `R` to sum `Rk` over columns of the first
component gives

\[
V_1:=\sum_{H_1}k_a(6-k_a)
=h_1C_{11}+h_2C_{21}.
\]

Since `C₁₁≥0` and `V₁=m₁(36-s₁)`, it follows that
`h₂α≤36(36-s₁)`. The other component gives
`h₁α≤36(36-s₂)`. Adding and using the definition of `α` yields

\[
\alpha(h+36)\le36(108-m). \tag{16}
\]

Cauchy--Schwarz gives `s_i=S_i/m_i≥36m_i/h_i`. Each ratio
`m_i/h_i` is at least `1/3`, because each sharp degree is at least
two, and their `h_i`-weighted mean is `m/h`. Therefore the sum
of the two ratios is at least `1/3+m/h`, and

\[
\alpha\ge48-m+36m/h. \tag{17}
\]

Combining (16)--(17) and multiplying by `h>0` gives

\[
F:=h^2(48-m)+36h(m-60)+1296m\le0. \tag{18}
\]

Set `u=48-m≥0` and
`v=192-(m+h)=12(22-b)>0`, so `h=144+u-v`.
An exact rearrangement of (18)'s left side is

\[
F=u\bigl(h^2-36h-1728\bigr)+432v.
\]

Since `h≥108`, the parenthesized factor is positive. Since
`v>0`, this gives `F>0`, contradicting (18). No integrality
assumption on the `C_ij` is needed in this two-component argument.

Both possibilities in (11) are excluded. Thus an irregular
minimum-six full-core four-degree model does not exist. Combining
with the earlier minimum-at-most-five result and the
[sharp-regular four-degree cardinality theorem](1485_four_degree_regular_gap.md),

\[
\boxed{\text{full central core, exactly four degrees, }r\le6
\quad\Longrightarrow\quad b=4r,\qquad n=8r^2.}
\]
