# Order forty: fourteen degree-five vertices are impossible

Research note, 19 September 2026. **There is no order-forty E1485
magma with minimum degree and central count four and fourteen
degree-five vertices.** The short proof below is entirely analytic:
it uses no incidence enumeration, affine-profile classification or SAT.
It is not yet a Lean theorem and does not settle the other order-forty
branches or the full spectrum conjecture.

The longer affine proof, which first established the exclusion after
a finite incidence reduction, is retained below as an independent
alternative route. That older proof chain is no longer needed for
this exclusion.

## Short analytic proof by universal return matching

Write `A,B` for the degree-five and degree-eight classes, of sizes
fourteen and six. Let `j_b` be the common sharp in- and out-degree
of `b∈B`. The standard degree and weighted-balance facts give

\[
1\le j_b\le4,\qquad \sum_{b\in B}j_b=14.
\]

Every vertex has four top neighbors in each direction. The ordinary
internal adjacency matrix `D` of `B` thus has both in- and out-degree
`4−j_b`. Let `C_bd=1` mean that there is a sharp path `b⇒a⇒d`
through `A`. Such a middle is unique, so `C` is binary with row
and column sums `j_b`. Every ordinary edge between `A` and `B`
is sharp. There are no ordinary `A→A` edges, since `5²<40`.

The [universal return-matching theorem](1485_general_return_matching.md)
therefore applies to the independent set `A`. For `e=b*d`, it gives

\[
\boxed{j_b+j_d\le\frac{40}{d(e)}.} \tag{S1}
\]

The product cannot be central. Consequently its degree is five,
eight or ten, and the bounds in (S1) are respectively eight, five
or four. In particular any two sharp-degree-three vertices must
have their product in `A`.

### Possible sharp-degree distributions

A vertex with `j_b=4` has no internal `B` successors. Its ordinary
two-step paths to `B` through `A∪B` can only pass through its four
sharp `A` successors, each having one `B` successor. There are at
most four such endpoints among six possible targets. At another
target the good product must be top, contradicting `4+j_d≤4`.
Thus all `j_b≤3`.

Let `n_i` count the vertices with `j=i`. Then

\[
n_1+n_2+n_3=6,\qquad n_1+2n_2+3n_3=14,
\qquad n_3-n_1=2.
\]

If `n_1=0`, choose a sharp-degree-three vertex. Its three sharp
`A` successors and its one internal `B` successor give at most
`3+2=5` two-step endpoints in `B`, because every internal successor
has sharp degree at least two. A missing endpoint gives a top
return, contradicting `3+j_d≤4`. Thus `n_1≥1`.

If `n_1=2`, then `n_3=4`. All products of these four vertices
must lie in `A`, by (S1), so their `4×4` submatrix of `C` is
all ones. This contradicts row sum three. The only remaining
distribution is

\[
(n_1,n_2,n_3)=(1,2,3). \tag{S2}
\]

### The last distribution violates internal-edge capacity

Let `H` be the three sharp-degree-three vertices, `M` the two
sharp-degree-two vertices, and `l` the sharp-degree-one vertex.
The `H×H` block of `C` is all ones by (S1), already filling
the row and column sums of these vertices. Thus there are no
sharp `A` paths between `H` and `M` in either direction.

For `h∈H,m∈M`, a top product is also impossible by (S1), since
`3+2>4`. Hence both `h*m` and `m*h` lie in `B`. Each has a
unique ordinary internal middle. Equivalently,

\[
(D^2)_{hm}=(D^2)_{mh}=1
\quad\text{for every }h\in H,m\in M. \tag{S3}
\]

Each `h` has one internal successor and one internal predecessor.
By (S3), that successor must have both members of `M` as internal
successors, and that predecessor must have both members of `M`
as internal predecessors. Neither can lie in `H`, whose internal
degree is only one.

If a member `m∈M` receives any edge from `H`, its internal
successor set is exactly `M`. It sends no edge to `H` and has
a self-loop. Its internal in-degree is two, so it receives at
most one edge from `H`. Dually, if it sends an edge to `H`, it
receives none and sends at most one. The two members of `M`
therefore account for at most two edges in total between `M`
and `H`, counting both directions.

Put `a=|D∩(H×{l})|` and `b=|D∩({l}×H)|`. All six internal
in/out incidences of `H` go to `M∪{l}`, so

\[
a+b\ge4. \tag{S4}
\]

If `a>0`, equation (S3) forces both members of `M` to be internal
successors of `l`. Since its internal out-degree is three, this
gives `b≤1`. If `b>0`, the dual argument gives `a≤1`.
When both are positive their sum is at most two; when one is zero
the other is at most three. Either way `a+b≤3`, contradicting
(S4). This completes the analytic exclusion.

## Alternative affine-profile proof

The rest of this page retains the earlier route. Its input is the
[finite internal-incidence reduction](1485_order_forty_near_saturation.md)
to three aligned types, followed by the
[single-coset reduction](1485_order_forty_fourteen_profiles.md).
It is redundant for the theorem above, but records additional
geometric identities that may be useful elsewhere.

### 1. Setup and the relevant profile intersections

Write `Z,A,B,T` for the degree classes `4,5,8,10`, with sizes
`4,14,6,16`. The internal reduction supplies two low-sharp vertices
`l_0,l_1∈B`, each with one sharp predecessor and successor, and
four high-sharp vertices in `B`, each with three. Each low-sharp
vertex is attached to two high-sharp vertices. Each attached pair
has ordinary edges in both directions to its low-sharp vertex and
no other ordinary neighbors inside `B`; the low-sharp vertices
also have an ordinary edge in both directions between them.

There is a sharp-loop `A` vertex `a_l` at each low-sharp vertex,
and the other twelve `A` vertices have high-sharp endpoints. The
high-to-high sharp-path matrix is `J₄` minus a permutation matrix,
whose omitted entries remain within each attached two-element group.
In particular every high-sharp row and column contains three `A`
vertices. There are no ordinary edges between high-sharp vertices.

By the single-coset reduction, all `A` predecessor profiles are
four lines `P_p`, and all successor profiles are four lines `Q_q`.
Use `V=F₂²` for their labels. The central coordinates may be written

\[
C(p,q)=p+q,\qquad H(p,q)=L(p+\Omega q), \tag{1}
\]

where `L∈GL₂(F₂)` and `Ω` has order three. Write `t_pq=P_p∩Q_q`.
The fourteen distinct `A` profile pairs leave precisely two missing
pairs, called the **holes**. A central-label equality gives a central
product; otherwise an occupied profile pair gives its `A` product.

We will use the following exact intersections. For a high-sharp `b`
attached to `l`,

\[
|\operatorname{TopPred}(b)\cap P_{p_l}|=2,\qquad
|\operatorname{TopSucc}(b)\cap Q_{q_l}|=2, \tag{2}
\]

where `(p_l,q_l)` is the profile of `a_l`. For the other low-sharp
vertex `l′`,

\[
|\operatorname{TopPred}(l')\cap P_{p_l}|=2,\qquad
|\operatorname{TopSucc}(l')\cap Q_{q_l}|=2. \tag{3}
\]

Here is a direct fiber verification of the predecessor statements.
The fiber `R_l⁻¹(b)` has size five; its non-top inputs are precisely
the three sharp `A` predecessors of `b`. Its only possible `B` input
would be `l`, but `l*l=a_l≠b`. Thus it has two top inputs.
For `t∈TopPred(b)`, the product `t*l` equals `a_l` exactly when
`t∈P_p_l`; otherwise the ordinary middle `b` has no lower-degree
replacement and is good. Hence (2).

For `R_l⁻¹(l′)`, the three non-top inputs are `a_l′` and the two
high-sharp vertices attached to `l′`. They all give `l′`; the remaining
internal candidate `l` gives `a_l` instead. Again there are exactly
two top inputs. The same replacement argument proves (3). The
successor statements follow by reversing all paths. These are also
instances of the [internal-edge fiber counts](1485_order_forty_fourteen_top_products.md).

### 2. Every high-sharp profile has rank one and supports one hole

The high-sharp profiles are affine graphs

\[
\operatorname{TopPred}(b)=\{t_{R_b(q),q}:q\in V\},\qquad
\operatorname{TopSucc}(b)=\{t_{p,S_b(p)}:p\in V\}.
\]

Write `R_b(q)=B_bq+r_b` and `S_b(p)=A_bp+s_b`. Centrality says
`B_b+Ω` and `I+A_b` are invertible. The two-element fibers in (2)
force both `B_b,A_b` to have rank one.

Every high-sharp vertex has exactly two good top-endpoint pairs,
and these form a matching, as proved in
[the first profile reduction](1485_order_forty_fourteen_profiles.md#1-every-high-sharp-b-vertex-has-exactly-two-good-top-pairs).
At a hole `(p,q)`, its ordinary pairs form a rectangle of size

\[
|R_b^{-1}(p)|\times|S_b^{-1}(q)|.
\]

Each nonempty such rectangle is `2×2`. Its central pairs form a
partial matching: within a `P` line central successor labels are
distinct, and within a `Q` line central predecessor labels are
distinct. Thus every nonempty hole rectangle gives at least two
good pairs. Since there are exactly two altogether, precisely one
hole lies in `im(R_b)×im(S_b)`, and its `2×2` central pairs form
a perfect matching. The other two pairs are the good `b` pairs.

Let `d` be the nonzero difference between the two labels in
`im(S_b)`. Since `A_b` has rank one and `I+A_b` is invertible,
its image and kernel are the same one-dimensional subspace, with
nonzero vector `d`. Similarly `Ω⁻¹B_b` has rank one and invertible
sum with `I`, so

\[
\operatorname{im}(B_b)=\Omega\operatorname{ker}(B_b).
\]

At the active hole, the two central successor labels of the left
points differ by the nonzero kernel vector of `B_b`. The two
central predecessor labels of the right points differ by `Ld`.
The perfect central matching makes these differences equal.
Consequently the differences of the two image-label pairs obey

\[
\boxed{\text{difference in }\operatorname{im}(R_b)
=\Omega L\bigl(\text{difference in }\operatorname{im}(S_b)\bigr).} \tag{4}
\]

Also, (2) says that this support rectangle contains the actual
low-sharp profile `(p_l,q_l)` belonging to the attached vertex.

### 3. The holes and the low-sharp profiles are opposite diagonals

Let `u_p` be the number of `A` vertices with predecessor profile
`P_p`, and let `e_p=4-u_p`. The deficits sum to two and count
the holes with first coordinate `p`.

Each top point of `P_p` has `u_p` successors in `A`, four in `T`
and one central successor, leaving `1+e_p` successors in `B`.
Thus the total number of `B`-predecessor-profile incidences on
`P_p` is `4(1+e_p)`.

At the own label `p_l` of a low-sharp `A` vertex, its two attached
high-sharp profiles contribute four such incidences by (2). The
opposite low-sharp profile contributes two more by (3). Hence
`4(1+e_p_l)≥6`, so `e_p_l≥1`. In other words **each low-sharp
predecessor label is a first coordinate of a hole**. Dually each
low-sharp successor label is a second coordinate of a hole.

The holes cannot share their first coordinate. If they did, the
preceding conclusion would force every low-sharp `A` profile to
have that first coordinate and one of the two hole second
coordinates, making it a hole rather than an actual profile.
The same argument excludes a shared second coordinate.

Label the two holes and two low-sharp profiles as

\[
\begin{array}{c|c}
\text{holes}&(p_0,q_0),\ (p_1,q_1)\\
\text{profiles of }a_{l_0},a_{l_1}&(p_0,q_1),\ (p_1,q_0),
\end{array} \tag{5}
\]

where `p_0≠p_1` and `q_0≠q_1`. Put

\[
\Delta p=p_0+p_1,\qquad\Delta q=q_0+q_1,\qquad K=\Omega L.
\]

If `Δp=KΔq`, any support rectangle satisfying (4) and containing
one of the low-sharp profiles and either hole would contain both
holes. This is forbidden by §2. Therefore

\[
\Delta p\ne K\Delta q. \tag{6}
\]

### 4. Exactly one horizontal and one vertical support at each attachment

A high-sharp vertex attached to `l_0` has just two possible kinds
of support rectangle:

| Active hole | Predecessor image | Successor image | Name |
| --- | --- | --- | --- |
| `(p_0,q_0)` | `{p_0,p_0+KΔq}` | `{q_0,q_1}` | Vertical |
| `(p_1,q_1)` | `{p_0,p_1}` | `{q_1,q_1+K⁻¹Δp}` | Horizontal |

At `l_1`, exchange the subscripts `0,1` in this table. By (6),
the extra predecessor label in the vertical case is outside
`{p_0,p_1}`; the extra successor label in the horizontal case is
outside `{q_0,q_1}`.

There are eight total `B`-predecessor incidences on `P_p_0`, since
its deficit is one. The two vertices attached to `l_0` contribute
four, and `TopPred(l_1)` contributes two. Every horizontal vertex
attached to `l_1` contributes two more; a vertical one contributes
zero. Hence at most one of the two vertices attached to `l_1` can
be horizontal. Interchanging the groups gives the same conclusion
at `l_0`.

The dual count on `Q_q_1` says at most one vertex attached to
`l_1` is vertical, and similarly at `l_0`. Each group has two
vertices, so each has exactly one of each kind.

Equality in these counts also proves

\[
\begin{aligned}
&\operatorname{TopPred}(l_0)\cap P_{p_0}=\varnothing,
&&|\operatorname{TopPred}(l_0)\cap P_{p_1}|=2,\\
&\operatorname{TopPred}(l_1)\cap P_{p_1}=\varnothing,
&&|\operatorname{TopPred}(l_1)\cap P_{p_0}|=2,
\end{aligned} \tag{7}
\]

and dually each low-sharp successor profile avoids its own `Q`
label and meets the other low-sharp `Q` line in two points.

The twelve high-sharp `A` profiles are the entire `4×4` grid
except the rectangle in (5). Thus each of the two defective `P`
labels occurs twice among those twelve profiles; the other two
occur four times. Each high-sharp column is missing one `P`
label, so its missing label is always `p_0` or `p_1`.

The two-point missing-line theorem now determines which: a column
attached to `l_0` must be missing `p_1`, and a column attached to
`l_1` must be missing `p_0`, by (7). Dually the missing `Q`
label of a row attached to a low-sharp vertex is the other
low-sharp `A` vertex's successor label.

### 5. E1485 forces four incompatible central labels

First note an overlap restriction for the two high-sharp vertices
`b,b′` attached to the same `l`:

\[
\operatorname{TopSucc}(b)\cap\operatorname{TopSucc}(b')
\subseteq Q_{q_l},\qquad
\operatorname{TopPred}(b)\cap\operatorname{TopPred}(b')
\subseteq P_{p_l}. \tag{8}
\]

For example a point in the successor intersection supplies two
ordinary degree-eight middles between `l` and that point. Strict
descent requires the lower good middle `a_l`, proving the first
inclusion. The other inclusion is dual.

Fix `l`, let `l′` be the other low-sharp vertex, and take `x=a_l′`
and `y=b_k` attached to `l`. Let `z=b_ell` run over the three
high-sharp predecessors that give sharp `A` products `b_ell*b_k`.
Since all their indices are high-sharp, the two relevant products
in E1485 are top. If `(p′,q′)` is the profile of `a_l′`, the
central-successor label of `b_k*x` must avoid

\[
H(p_{\ell k},q')
\]

for all three actual predecessor labels in column `k`. Its missing
label is precisely `p′`, by §4. Hence

\[
C(b_k*a_{l'})=H(p',q'). \tag{9}
\]

Both attached high-sharp vertices have the same point `b_k*a_l′`:
their products lie on `P_p′`, and (9) fixes its central successor
label. By (8) that common point lies on `Q_q_l`. Therefore

\[
H(p',q')=p'+q_l. \tag{10}
\]

The dual identity, using the three actual successor labels in row
`k`, similarly forces

\[
H(a_{l'}*b_k)=C(p',q').
\]

These two products share their `Q_q′` profile and central
predecessor label. Their common point belongs to `P_p_l` by (8),
so

\[
H(p_l,q')=p'+q'. \tag{11}
\]

Apply (10)–(11) at both low-sharp vertices, using (5). This gives

\[
\begin{aligned}
H(p_0,q_0)&=p_1+q_0,&
H(p_0,q_1)&=p_0+q_0,\\
H(p_1,q_0)&=p_1+q_1,&
H(p_1,q_1)&=p_0+q_1.
\end{aligned} \tag{12}
\]

Taking differences and using (1),

\[
L\Delta p=\Delta q,\qquad L\Omega\Delta q=\Delta p.
\]

Thus `L²Ω` fixes the nonzero vector `Δq`. In `GL₂(F₂)`, an
element `L` is the identity, an involution, or one of the two
order-three matrices `Ω,Ω²`. The first two cases give `L²Ω=Ω`,
which has no nonzero fixed vector. The choice `L=Ω²` gives
`L²Ω=Ω²`, also with no nonzero fixed vector. Therefore `L=Ω`.

But then `LΩ=ΩL=K`, so the second difference equation says
`Δp=KΔq`, contradicting (6). This excludes all three aligned
types and completes the fourteen/six exclusion.
