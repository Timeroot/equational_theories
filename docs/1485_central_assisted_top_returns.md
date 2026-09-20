# Central-assisted products force unique top returns

Research note, 20 September 2026. This is an analytic finite E1485
lemma, with no enumeration or Lean dependency. Let `T` be the
maximum-translation-degree class and `Z` the central class.
Write `x→y` for ordinary adjacency.

**Theorem.** Let `u,v,q∈T` and put `a=u*v`. Then

\[
v*q\in Z,\quad q\to u
\quad\Longrightarrow\quad
\boxed{q*a=u,\qquad Row(q)\cap Col(a)=\{u\}.}             \tag{1}
\]

Dually,

\[
q*u\in Z,\quad v\to q
\quad\Longrightarrow\quad
\boxed{a*q=v,\qquad Row(a)\cap Col(q)=\{v\}.}             \tag{2}
\]

The product `a` need not have minimum noncentral degree, and
there is no restriction on the minimum degree or central cardinality.

## Proof

For (1), put `y=v*q∈Z`. Then `v→y→q`. Choose any
central predecessor `z∈P_v`; such a predecessor exists for
every top. The paths `z→v→y` and `y→q→u` have central
endpoints, so both are good:

\[
z*y=v,\qquad y*u=q.
\]

E1485 with `x=u` therefore gives

\[
u=(y*u)*(u*(z*y))=q*(u*v)=q*a.
\]

Any other ordinary middle between `q` and `a` would, by
[strict replacement descent](1485_image_research.md), have degree
strictly greater than the good middle `u`. This is impossible
because `u` has maximum degree. Hence the entire ordinary
row-column intersection is the singleton in (1), not merely its
top part.

For (2), put `y=q*u∈Z` and choose `z∈C_u`. Central
endpoint uniqueness gives `y*z=u` and `v*y=q`. The dual
E1485 identity yields

\[
v=((y*z)*v)*(v*y)=(u*v)*q=a*q.
\]

The same maximum-degree argument proves its singleton intersection.

## A necessary constraint on candidate top profiles

Suppose a noncentral vertex has top predecessors `U`, top
successors `V`, and known good top pairs `u_i*v_i=a`.
Let `D` be ordinary adjacency within `T`, and let
`K_{xy}=1` mean that `x*y` is central. The theorem gives

\[
K_{v_iq}=1,\ D_{qu_i}=1
\quad\Longrightarrow\quad
\sum_{u\in U}D_{qu}=1,
\]

\[
K_{qu_i}=1,\ D_{v_iq}=1
\quad\Longrightarrow\quad
\sum_{v\in V}D_{vq}=1.
\]

These restrictions use actual E1485 products and finite strict
descent, beyond the central incidence equations `BC=J`, `BD=J`,
and `DC=J`. They are necessary conditions, not a sufficient
criterion for extending incidence data to a magma.

## A quantified restriction at the first noncentral top output

Suppose `a` has the least degree `p` among noncentral products
of two tops. Write `U=TopPred(a)` and `V=TopSucc(a)`.
The [first-output theorem](1485_first_top_output_fibers.md) gives
`|U|=|V|=t`, and the bipartite good-pair graph

\[
G=\{(u,v)\in U\times V:u*v=a\}
\]

is `k`-regular on both sides, where `k=r+t−p>0`.
For every top `q`,

\[
\boxed{|Row(q)\cap U|\le\max\{1,t-|P_q|\},\qquad
|Col(q)\cap V|\le\max\{1,t-|C_q|\}.}                    \tag{3}
\]

To prove the first bound, put `X=Row(q)∩U` and suppose
`|X|≥2`. If `v∈N_G(X)`, choose `u∈X` with `u*v=a`.
The central-assisted return theorem says that `v*q` cannot be
central, since that would force `Row(q)∩U={u}`. Thus
`C_v∩P_q=∅` for every `v∈N_G(X)`.

The blocks `C_v`, for `v∈V`, partition `Z`, and each meets
`P_q` in at most one label. Consequently

\[
L=\{v\in V:C_v\cap P_q\ne\varnothing\}
\quad\text{has size }|P_q|.
\]

It is disjoint from `N_G(X)`. The `k`-regularity of `G`
gives `k|X|≤k|N_G(X)|`, so

\[
|X|+|P_q|\le |N_G(X)|+|L|\le t.
\]

This proves the first bound for `|X|≥2`; the remaining cases
give the maximum with one in (3). The second bound is its dual.
