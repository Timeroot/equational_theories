# Order forty: exact individual fibers and regular hole rectangles

Research note, 20 September 2026. These are analytic necessary conditions,
not a Lean theorem or an exclusion by themselves. They apply to the
four-central-vertex, twelve/eight case with both degree-five profile
families in single cosets. The rectangle conclusion uses the additional
balanced multiplicities `3333/3333`.

Use the notation of the
[joint-capacity note](1485_order_forty_twelve_joint_capacities.md):
`P_p,Q_q` are the predecessor/successor profile partitions of the
sixteen tops; `I_d,J_c` are the colors in the sharp `F,G` fibers;
and `D` is adjacency within the degree-eight class `B`.
Write `U_b=TopPred(b)`, `V_b=TopSucc(b)`, and
`M_bp=|U_b∩P_p|`, `N_bq=|V_b∩Q_q|`.

## 1. The exact good degree of an individual top endpoint

For every `u∈U_b∩P_p`, the number of `v∈V_b` with `u*v=b` is

\[
\boxed{e_{bp}=\sum_{d\in B}D_{bd}\,\mathbf1_{p\in I_d}.}
\tag{1}
\]

Indeed, the fiber `L_u⁻¹(b)` has exactly four elements. It is contained
in `Row(b)`, whose non-top elements consist of `j_b` sharp successors
in `A` and `4-j_b` internal successors in `B`. Every sharp successor
belongs to the fiber. For an internal successor `d`, the middle `b`
in `u→b→d` is bad exactly when a lower-degree `A` replacement is
available. Such a replacement exists precisely when `p∈I_d`.
There is no possible central middle, since a central vertex has only
top neighbors. Equal-degree alternative middles cannot replace a good
middle by the strict minimum-degree theorem. Thus the number of non-top
fiber elements is

\[
j_b+\sum_d D_{bd}(1-\mathbf1_{p\in I_d})=4-e_{bp},
\]

proving (1). In particular this good degree is the same for every top
point of `U_b` lying on the given predecessor line; no assertion about
uniform reverse joint-coordinate fibers is involved.

Dually, for every `v∈V_b∩Q_q`, the number of `u∈U_b` with `u*v=b` is

\[
\boxed{f_{bq}=\sum_{c\in B}D_{cb}\,\mathbf1_{q\in J_c}.}
\tag{2}
\]

Consequently `g_b=Σ_p M_bp e_bp=Σ_q N_bq f_bq`. The individual
equalities contain more information than this aggregate count.

## 2. A perfect-matching hole set forces regular rectangles

Now assume multiplicities `3333/3333`. Each profile line has exactly
one missing `A` profile, so the four holes form the graph of a
permutation `q=π(p)`.

Fix `b` and one such hole, and put

`X=U_b∩P_p`, `Y=V_b∩Q_π(p)`, `m=|X|`, `n=|Y|`.

All good top pairs with first endpoint in `X` have their second endpoint
in `Y`: any other profile cell is occupied by a strictly smaller-degree
`A` replacement. The dual assertion holds for endpoints in `Y`.
Equations (1)–(2) therefore make the good bipartite graph on `X×Y`
regular on each side, with degrees `e_bp` and `f_b,π(p)`.

On this hole a pair is bad precisely when it is central-valued. Along
a `P` line the adjacent central successor labels are distinct; along a
`Q` line the adjacent central predecessor labels are distinct. Hence
these central-valued pairs form a **matching** between `X` and `Y`.

Suppose `m,n>0`. If that matching has any edge, regularity forces every
vertex on each side to have exactly one matching edge. Thus `m=n`
and the matching is perfect. Otherwise it is empty. We obtain exactly
two possibilities:

| Central-valued pairs | Necessary counts | Good pairs in the hole |
|---|---|---:|
| None | `e=n`, `f=m` | `mn` |
| Perfect matching | `m=n`, `e=f=m−1` | `m(m−1)` |

Equivalently, the two sets of adjacent central labels on `X,Y` are
either disjoint or identical. Partial nonempty overlap is impossible.
If `m=0<n`, only `f=0` is required; if `n=0<m`, only `e=0` is
required. No degree condition is imposed at an absent endpoint.

This is stronger than the earlier lower bound `mn−min(m,n)`: the
matching cannot cover only part of a nonempty endpoint set. The proof
requires neither affine partner profiles nor the later all-`β=1`
conclusion. A numerical system satisfying these conditions is still
only necessary incidence data, not a magma construction.
