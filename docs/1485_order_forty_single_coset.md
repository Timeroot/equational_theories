# Order forty: the saturated single-coset case is impossible

Research note, 19 September 2026. **There is no E1485 magma with degree
classes `4,5,8,10`, class sizes `4,16,4,16`, and both degree-five profile
families single `V₄` cosets.** This is a pen-and-paper reduction followed
by a small, exact finite linear-algebra check, not yet a Lean proof.

The separate [saturated-profile reduction](1485_order_forty_saturated_profiles.md)
forces the single-coset hypothesis in this class-size configuration.
Together the two results exclude the whole saturated `|A₅|=16` branch.
They do **not** exclude all magmas of order forty or prove the general
square-or-double-square spectrum conjecture.

The check is [1485_n40_single_coset_check.py](../scripts/1485_n40_single_coset_check.py):

```sh
python3 scripts/1485_n40_single_coset_check.py
```

A local run took **4.12 seconds**. It uses only standard-library Python,
exact bit arithmetic, and explicit evaluations of E1485 and its dual.
It does not invoke SAT, an ATP, floating-point arithmetic, unpublished
certificates, or conjectural spectrum exclusions.

## 1. Sharp and profile coordinates

Write `Z,A,B,T` for the degree classes `4,5,8,10`. The
[large degree-five class analysis](1485_min_four_large_five_class.md)
supplies the saturated sharp coordinates

\[
 B=\{b_i:i\in\mathbb F_2^2\},\qquad
 A=\{a_{ij}:i,j\in\mathbb F_2^2\},\qquad
 b_i\Rightarrow a_{ij}\Rightarrow b_j,\qquad b_i*b_j=a_{ij}.
\]

Every `A` vertex has four top neighbors and one sharp `B` neighbor in
each direction. Every `B` vertex has four top and four sharp `A`
neighbors in each direction, so there are no ordinary `B→B` edges.
Every top vertex has one central, four `A`, one `B`, and four top
neighbors in each direction. Consequently the four top-predecessor
sets of `B` partition `T`; so do its four top-successor sets.

Let `P_p` and `Q_q` denote the two single-coset families of `A`
top-predecessor and top-successor profiles. They are distinct cosets
of the same permutation parity. Each `P_p` meets each `Q_q` exactly
once, so write `t_pq=P_p∩Q_q`, and set

\[
 \operatorname{TopPred}(a_{ij})=P_{p_{ij}},\qquad
 \operatorname{TopSucc}(a_{ij})=Q_{q_{ij}}.
\]

For every fixed `j`, the four `p_ij` are a permutation; for every
fixed `i`, the four `q_ij` are a permutation. Moreover the sixteen
pairs `(p_ij,q_ij)` are distinct: equal profile pairs would give
overlapping good top-endpoint pairs for different products. Thus all
sixteen profile pairs occur.

For two top endpoints, their product is central precisely when the
central successor of the first equals the central predecessor of the
second. Otherwise their product is the unique `A` vertex with profile
indices `(p(first),q(second))`. Indeed each `A` accounts for twelve
good top-endpoint pairs; these `16·12` pairs and the `64` central pairs
exhaust all `16²` pairs. In particular there are no `B` or `T` products
of top endpoints in this branch.

## 2. Affine normalization uses one common central alphabet

Identify the central alphabet with `V=F₂²`. All permutations of its
four elements are affine, and the normal Klein-four subgroup `V₄`
is exactly the translation subgroup. Thus the two profile cosets have
equations

\[
 P_c:\ C=M H+c,\qquad Q_d:\ C=N H+d,
\]

where `M,N∈GL₂(F₂)` have the same permutation parity and are distinct.
Here `H,C` are respectively the actual central predecessor and
successor labels, in the **same** alphabet. Independent relabeling of
those two alphabets is neither needed nor allowed.

The relative matrix `Ω=N M⁻¹` has order three; there are exactly two
possibilities in `GL₂(F₂)`. Put

\[
 p=N(M+N)^{-1}c,\quad q=M(M+N)^{-1}d.
\]

The matrices `M,N` need not commute, so this order matters. From
`(M+N)H=c+d` and `C=M H+c` we obtain

\[
 C=p+q,\qquad H=N^{-1}p+M^{-1}q.
\]

Thus, taking `L=N⁻¹`, we obtain

\[
 C(p,q)=p+q,\qquad H(p,q)=L(p+\Omega q), \tag{1}
\]

with `L∈GL₂(F₂)` and `Ω` one of its two order-three elements.
There is no constant term: `c,d` range over the entire translation
alphabet. The script enumerates all six choices of `L` and both
choices of `Ω`.

## 3. E1485 makes each B-profile family have a common slope

Every `A×B` and `B×A` endpoint pair has a unique ordinary top middle:
there are no ordinary `B→B` edges, and all possible middles have top
degree. Therefore write the `B` profiles as

\[
 \operatorname{TopPred}(b_k)=\{t_{R_k(q),q}:q\in V\},\qquad
 \operatorname{TopSucc}(b_k)=\{t_{p,S_k(p)}:p\in V\}.
\]

Centrality says `H(R_k(q),q)` is a permutation of `V`, as is
`C(p,S_k(p))`. Since every permutation of `V` is affine, write

\[
 R_k(q)=B_kq+r_k,\qquad S_k(p)=A_kp+s_k.
\]

The matrices `U_k=I+A_k` and `V_k=L(B_k+Ω)` are invertible.
**Do not assume** `R_k,S_k` themselves are permutations, nor that
`TopPred(b_k)` is transversal to both central directions. In particular,
whole central rows and columns are allowed `B` profiles.

As in equations (14)–(15) of the
[order-twenty-four proof](1485_order_twenty_four_three_central.md),
apply E1485 and its dual with `x=a_ij,y=b_k,z=b_ell`. Three choices
of `ell` exclude three central labels, leaving

\[
 \begin{aligned}
 p_{ij}+S_k(p_{ij})&=H(p_{jk},q_{ij}),\\
 p_{ij}+q_{ki}&=H(R_k(q_{ij}),q_{ij}).
 \end{aligned} \tag{2}
\]

Subtract the first equation for `k,k′`. Its right side is independent
of `i`, while `p_ij` runs over all four values. Hence `U_k=U_k′`.
The second equation, using the row-permutation property of `q`, gives
`V_k=V_k′`. Write these common invertible matrices as `U,V` and put
`W=LΩ`.

The four `R` profiles partition `T`; with common slope, their offsets
are all different. Relabel the four `B` vertices, and simultaneously
both sharp indices, so that `r_k=k`. This is just one common relabeling,
not independent permutations of the two sharp indices. Likewise the
four offsets `s_k` form a permutation of `V`. Equations (2) become

\[
 \begin{aligned}
 U p_{ij}+W q_{ij}+L p_{jk}&=s_k,\\
 p_{ij}+V q_{ij}+q_{ki}&=Lk.
 \end{aligned} \tag{3}
\]

For fixed `L,Ω,U,V,(s_k)`, these are 256 binary equations in the 64
bits of the arrays `p,q`. Thus there are exactly
`6·2·6·6·24=10,368` systems to consider. The script enumerates all of
them; it does not require any further necessary matrix identities to
discard slope choices.

## 4. Most of the multiplication table is forced

All products other than `Z*T` and `T*Z` are now determined. Some basic
formulas are

\[
 \begin{aligned}
 a_{ij}*a_{k\ell}&=
 \begin{cases}b_j&j=k,\\t_{p_{k\ell},q_{ij}}&j\ne k,\end{cases}\\
 a_{ij}*b_k&=t_{R_k(q_{ij}),q_{ij}},\qquad
 b_k*a_{ij}=t_{p_{ij},S_k(p_{ij})},\\
 b_i*t_{p,q}&=a_{i\ell}\quad(q_{i\ell}=q),\\
 t_{p,q}*b_j&=a_{mj}\quad(p_{mj}=p).
 \end{aligned} \tag{4}
\]

Products `Z*Z`, `Z*A`, `A*Z`, `Z*B`, and `B*Z` are the unique top
intersections specified by their central and ordinary profiles.

There are also explicit formulas for `A*T` and `T*A`. Let `v=t_pq`.
If `v∈TopSucc(b_j)`, then `a_ij*v=b_j`, using the sharp middle;
otherwise this product is top. Let `m` be determined by `p_mi=p`.
For the top case,

\[
 a_{ij}*v
 =t_{\,L^{-1}(p_{ij}+q_{mi})+\Omega q_{ij},\ q_{ij}}. \tag{5}
\]

To prove (5), apply the dual identity with `x=a_ij,y=v,z=b_k`.
As `k` varies, `v*b_k=a_mk`, with `p_mk=p`, ranges over the four
vertices having predecessor profile `P_p`. Their four successor
indices are different by the joint profile bijection. The three
choices `k≠i` give top intermediates and exclude three values of
`H(a_ij*v)`; the remaining value is `p_ij+q_mi`. The product's
successor-profile coordinate is `q_ij`, giving (5).

Dually, if `v∈TopPred(b_i)` then `v*a_ij=b_i`. Otherwise let `ell`
be determined by `q_jell=q`; then

\[
 v*a_{ij}=t_{\,p_{ij},\ H(p_{j\ell},q_{ij})+p_{ij}}. \tag{6}
\]

Here the ordinary identity with `x=a_ij,y=v,z=b_k` excludes the
three choices `k≠j`, leaving the displayed central successor label.
These formulas use only the already-proved column-permutation
property of `p`, row-permutation property of `q`, and joint profile
bijection. No extra Latin-square assumptions are made.

The script fills precisely `1472` entries using (1), (4)–(6), and
central intersections. The remaining `128` entries, exactly `Z*T`
and `T*Z`, are left unspecified.

## 5. Exact finite check and the final two candidates

The linear calculation gives:

| Result | Number |
| --- | ---: |
| Binary linear systems | 10,368 |
| Inconsistent | 10,224 |
| Consistent, each of rank 64 | 144 |
| Distinct consistent slope quadruples | 36 |
| Excluded by E1485 or its dual with `x∈A,y∈B,z∈Z` | 142 |
| Remaining candidates | 2 |

The script asserts rank 64 for every consistent system, reconstructs
the unique solution, and independently substitutes it back into all
equations (3). It checks the profile bijections before forming the
forced table. The first identity check only uses already-forced
entries; no guess of the remaining multiplication is made.

The last two candidates are conjugate under the automorphism of `F₄`.
They have

\[
 L=U=\Omega,\qquad V=I,\qquad s_k=\Omega k.
\]

For an explicit contradiction choose `Ω(1)=2,Ω(2)=3`. The arrays are

\[
 (p_{ij})=\begin{pmatrix}0&1&2&3\\3&2&1&0\\1&0&3&2\\2&3&0&1\end{pmatrix},
 \qquad
 (q_{ij})=\begin{pmatrix}0&1&2&3\\2&3&0&1\\3&2&1&0\\1&0&3&2\end{pmatrix}.
\]

Set `x=t_00,y=z_0`, and write `u=y*x`. Centrality leaves just four
possibilities:

\[
 u\in\operatorname{Row}(z_0)=\{t_{00},t_{21},t_{32},t_{13}\}.
\]

For `z=z_1`, we have `z*y=t_11` and `x*(z*y)=a_13`. Formula (6)
gives

| `u` | `t_00` | `t_21` | `t_32` | `t_13` |
| --- | --- | --- | --- | --- |
| `u*a_13` | `t_02` | `t_00` | `b_1` | `t_03` |
| `u*a_21` | `t_03` | `t_01` | `t_00` | `b_2` |

E1485 requires `u*a_13=x`, forcing `u=t_21`. But with `z=z_2`,
we have `z*y=t_22` and `x*(z*y)=a_21`; the same identity requires
`u*a_21=x`, forcing `u=t_32`. This is a contradiction.
The second candidate has the identical contradiction after swapping
the field labels `2,3`; the script checks it directly too.

This exhausts all necessary linear systems and proves the stated
single-coset exclusion. The proof status is **exact finite-assisted
research proof, not yet kernel-checked**.
