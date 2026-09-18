# Order twenty-four with three central vertices: excluding nine degree-four vertices

Research note, 18 September 2026. This is an analytic exclusion of one
remaining minimum-degree-three incidence case, not a complete exclusion
of order 24. The degree and central-incidence background is in the
[large-central-class note](1485_order_twenty_four_large_central.md).

Write `Z,A,B,T` for the classes of degrees `3,4,6,8`, respectively.
This note excludes the configuration

\[
 (|Z|,|A|,|B|,|T|)=(3,9,3,9). \tag{1}
\]

The [three-central incidence reduction](1485_order_twenty_four_three_central_reduction.md)
supplies the following facts.
Each top vertex has one central predecessor and successor, so the
nine top vertices are a `3×3` grid, with its rows and columns indexed
by central predecessors and successors. Each `A` vertex has three
top neighbors and one sharp `B` neighbor in each direction. Its top
predecessors and successors are permutation transversals of this grid.
All `A` predecessor transversals have one parity; all `A` successor
transversals have the opposite parity. Each of the three transversals
of either parity occurs three times.

These profile facts are proved in that reduction. The argument below
uses them; it does not infer them from the large-central-class note alone.

## Sharp coordinates and product restrictions

Every `B` vertex has three sharp `A` predecessors and successors.
There are nine sharp paths `B⇒A⇒B`. Two such paths cannot have the
same endpoints and different middles. They therefore account for all
nine ordered pairs of `B` endpoints. Label

\[
 B=\{b_0,b_1,b_2\},\qquad
 A=\{a_{ij}:0\le i,j<3\},\qquad
 b_i\Rightarrow a_{ij}\Rightarrow b_j,
 \quad b_i*b_j=a_{ij}. \tag{2}
\]

Every `B` vertex also has exactly three top predecessors and successors.
Together with its three sharp `A` neighbors these fill its degree six,
so there are no ordinary `B→B` edges. Consequently the only possible
ordinary middles for endpoint pairs in `A×B` or `B×A` are top vertices.
Existence of a good middle and strict degree descent show that each
such pair has exactly one ordinary top middle.

The three sharp `A` successors of a fixed `B` have disjoint ordinary
rows. Their three-element top successor sets therefore partition `T`.
Dually, the top predecessor sets of the three sharp `A` predecessors
of a `B` partition `T`. It follows that

\[
 B*T\subseteq A,\qquad T*B\subseteq A. \tag{3}
\]

## Two systems of transversal coordinates

Let `P_0,P_1,P_2` be the three top predecessor transversals of `A`,
and let `Q_0,Q_1,Q_2` be its three successor transversals. Transversals
of opposite parity meet in exactly one point, so write

\[
 t_{p,q}=P_p\cap Q_q.
\]

For each `a_ij`, define its profile indices by

\[
 \operatorname{TopPred}(a_{ij})=P_{p_{ij}},\qquad
 \operatorname{TopSucc}(a_{ij})=Q_{q_{ij}}. \tag{4}
\]

For each fixed `j`, the indices `p_0j,p_1j,p_2j` are a permutation
of the three values: these are the disjoint top predecessor sets of
the sharp predecessors of `b_j`. Similarly, for fixed `i`, the
indices `q_i0,q_i1,q_i2` are a permutation.

The unique-top-middle descriptions already give

\[
 \begin{aligned}
 a_{ij}*a_{\ell k}&=t_{p_{\ell k},q_{ij}}
 &&\text{if }\ell\ne j,\\
 a_{k\ell}*a_{ij}&=t_{p_{ij},q_{k\ell}}
 &&\text{if }\ell\ne i.
 \end{aligned} \tag{5}
\]

For the latter two formulas, the `A×A` endpoint pair has a sharp
`B` middle exactly when the two adjacent sharp indices agree.
Otherwise its unique top middle is its good middle.

## Central labels are affine functions

Use `F_3` for all profile labels and all central labels. Let `C(p,q)`
be the central successor of `t_pq`, and `H(p,q)` its central
predecessor. Each `P` or `Q` transversal meets each central row and
column exactly once. Thus both `C` and `H`, regarded as `3×3`
arrays in the profile coordinates, are Latin squares.

Every Latin square of order three, with any labeling of its rows,
columns, and symbols by `F_3`, has an affine expression. One quick
verification is that its rows, viewed as permutations, differ by the
two fixed-point-free permutations of three symbols; those are the
two nontrivial translations of `F_3`. All permutations of `F_3`
themselves are affine. Therefore write

\[
 C(p,q)=\alpha p+\beta q+\gamma,\qquad
 H(p,q)=\alpha' p+\beta' q+\gamma', \tag{7}
\]

where all four coefficients `α,β,α',β'` are nonzero.
Moreover `C,H` are orthogonal, since central predecessor and successor
labels identify a top vertex uniquely. Rescale the profile coordinates
and translate the central labels so that

\[
 C(p,q)=p+q,\qquad H(p,q)=\varepsilon(p-q)+\delta,
 \qquad \varepsilon\in\{1,-1\}. \tag{8}
\]

Indeed, after normalizing the two coefficients of `C`, the two
nonzero coefficients of `H` must differ: otherwise the affine map
`(C,H)` would be singular. Over `F_3` they are therefore opposites.

If `C(p,q)=H(p',q')`, the top endpoints `t_pq,t_p'q'` have a
central middle, and their product is that central vertex. In
particular, a top product equal to an `A` vertex requires these
two central labels to differ.

## The two possible orientations of each B-profile family

A `B` top predecessor set meets every central row once, by centrality.
It also meets every `Q_q` once, since every `A×B` pair has a unique
top middle and all three `Q_q` occur. Write its points as
`t_{R_k(q),q}`. The function `H(R_k(q),q)` is a permutation of `F_3`,
so it is affine with nonzero slope. Using (8), the slope of `R_k(q)`
is either zero or minus one. Thus this set is either a `P` line or
an entire central column:

\[
 R_k(q)=r_k\quad\hbox{or}\quad R_k(q)=-q+r_k. \tag{9}
\]

Dually write the `B` top successor set as
`{t_{p,S_k(p)}:p\in F_3}`. It meets every `P_p` and every central
column once, so

\[
 S_k(p)=s_k\quad\hbox{or}\quad S_k(p)=p+s_k. \tag{10}
\]

The latter possibility is an entire central row. These degenerate
row/column possibilities cannot be discarded merely by centrality.

Every top vertex has one central neighbor, three `A` neighbors, and
three top neighbors in each direction, leaving exactly one `B`
neighbor. Consequently the three `B` predecessor sets partition `T`,
as do the three successor sets. Lines of the two possible predecessor
orientations meet, so all three predecessor sets have the same
orientation. Similarly all three successor sets have one orientation.

Define signs `theta,phi\in{1,-1}` by

\[
 \begin{array}{c|cc}
 &+1&-1\\ \hline
 \theta&R_k(q)=r_k&R_k(q)=-q+r_k\\
 \phi&S_k(p)=s_k&S_k(p)=p+s_k.
 \end{array} \tag{11}
\]

The relevant central labels are therefore

\[
 C(p,S_k(p))=\phi p+s_k,\qquad
 H(R_k(q),q)=\varepsilon r_k-\varepsilon\theta q+\delta.
 \tag{12}
\]

The exact remaining mixed products are

\[
 a_{ij}*b_k=t_{R_k(q_{ij}),q_{ij}},\qquad
 b_k*a_{ij}=t_{p_{ij},S_k(p_{ij})}. \tag{13}
\]

## E1485 and its dual give the key equations

Apply

\[
 (y*x)*(x*(z*y))=x
\]

with `x=a_ij`, `y=b_k`, `z=b_ell`, where `ell≠j`. By (2), (5), and (13),

\[
 t_{p_{ij},S_k(p_{ij})}*t_{p_{\ell k},q_{ij}}=a_{ij}.
\]

Thus `C(p_ij,S_k(p_ij))≠H(p_ell k,q_ij)` for both `ell≠j`.
As `ell` runs over all three values, `p_ell k` is a permutation.
The only central label not excluded by these two inequalities is
therefore the remaining one:

\[
 C(p_{ij},S_k(p_{ij}))=H(p_{jk},q_{ij}). \tag{14}
\]

Next apply the dual identity

\[
 ((y*z)*x)*(x*y)=x
\]

with the same substitutions, now for `ell≠i`. This yields

\[
 t_{p_{ij},q_{k\ell}}*t_{R_k(q_{ij}),q_{ij}}=a_{ij}.
\]

The three `q_k ell` are a permutation. The same exclusion argument
gives

\[
 C(p_{ij},q_{ki})=H(R_k(q_{ij}),q_{ij}). \tag{15}
\]

Expanding (14) and (15) using (8) and (12), we obtain

\[
 \begin{aligned}
 \phi p_{ij}+\varepsilon q_{ij}
 &=\varepsilon p_{jk}-s_k+\delta,\\
 p_{ij}+\varepsilon\theta q_{ij}
 &=\varepsilon r_k-q_{ki}+\delta.
 \end{aligned} \tag{16}
\]

## Equal orientations are impossible

Suppose `theta=phi`. Multiply the first equation in (16) by `phi`.
Its left-hand side then agrees with the second equation's left-hand
side. The first makes that expression independent of `i`, and the
second makes it independent of `j`. It is therefore constant.
Fixing `k` in the first equation makes `p_jk` independent of `j`,
contradicting the column-permutation property. This excludes both
the nondegenerate/nondegenerate and the degenerate/degenerate choices.

## Mixed orientations are impossible

The two mixed choices are dual, so assume `theta=1,phi=-1`: the
`B` predecessors are `P` lines and the `B` successors central rows.
The two equations in (16) say that

\[
 \begin{aligned}
 U_j:=p_{ij}-\varepsilon q_{ij}
 &=-\varepsilon p_{jk}+s_k-\delta,\\
 V_i:=p_{ij}+\varepsilon q_{ij}
 &=\varepsilon r_k-q_{ki}+\delta
 \end{aligned} \tag{17}
\]

are well-defined independently of `i` and `j`, respectively.
Since division by two is multiplication by minus one in `F_3`,

\[
 p_{ij}=-U_j-V_i,\qquad
 q_{ij}=\varepsilon(U_j-V_i). \tag{18}
\]

Substituting (18) into the two equations of (17), for fixed `k`,
shows respectively that

\[
 U_j-\varepsilon V_j\text{ is constant in }j,\qquad
 V_i+\varepsilon U_i\text{ is constant in }i. \tag{19}
\]

The first says `U_i=epsilon V_i+d` for a constant `d`. The second
then makes `2V_i+epsilon d` constant. Thus all `V_i` are equal.
Equation (18) again makes every column of `p_ij` constant, the
required contradiction. Reversing all paths excludes the other
mixed choice, since E1485 and its dual interchange.

All four choices have been excluded, proving that (1) is impossible.
The other reduced three-central candidate,
`(|Z|,|A|,|B|,|T|)=(3,6,6,9)`, is excluded separately by the
[uniform-fiber argument](1485_order_twenty_four_six_six_profiles.md).
