# A general degree-class bound near the square central count

Research theorem, 20 September 2026. These are analytic necessary
conditions for finite E1485 magmas, not Lean declarations. They extend
the degree-five capacity argument used in the
[order-forty, ten-central exclusion](1485_order_forty_ten_central_exclusion.md)
to arbitrary minimum degree.

Assume minimum degree `r=q+1≥4`, central count `m=q²+1`, and
`1≤|P_u|,|C_u|≤q` at every top `u`. Let `h=|T|`, and let `a`
be the number of vertices of degree `r+1`. Then

\[
\boxed{a\le2r-1.}
\]

The two largest class sizes have sharper consequences:

- If `a=2r−1`, then `h=r²`; every vertex has exactly `r` top
  predecessors and exactly `r` top successors.
- If `a=2r−2`, then `h≤r²+r−3`.

No condition on the remaining degree classes or total order is imposed.
The central block-size hypothesis is essential; this does not establish
the full-core or square-or-twice-square theorem.

## 1. A sharp integer capacity at each top

Every vertex has at least `ceil(m/q)=r` top neighbors in each
direction, because their central blocks partition `Z`. A degree-`r+1`
vertex has a non-top sharp neighbor, so its top count is exactly `r`,
and its unique non-top neighbor is sharp. The same is true dually.

If `u→x` with `u∈T` and `d(x)=r+1`, the `r`-element fiber
`L_u^{-1}(x)` contains the unique non-top successor of `x` and
`r−1` of its `r` top successors. Its central auxiliary support is
therefore the union of all but one block in the top-successor
partition at `x`, and has size at least

\[
                         m-q=q²-q+1.
\]

Write `c_u=|C_u|` and let `α_u` count successors of `u` in the
degree-`r+1` class. The auxiliary relations are `r`-regular, and
every outgoing central edge occupies one place at every parameter.
Consequently

\[
 (m-q)\alpha_u\le m(r-c_u),\qquad
 \boxed{\alpha_u\le r-c_u+\mathbf1_{c_u=1}.}              \tag{1}
\]

For the integer rounding, write `m=(m−q)+q`. If `c≥2`, then
`q(r−c)≤q(q−1)=m−q−1`, so the extra fraction is below one.
If `c=1`, the fraction is `q²/(q²−q+1)`, between one and two.
This proves (1). The predecessor version is dual.

Every central row has `r` opposite blocks partitioning `m`. There
cannot be two singleton blocks: the maximum possible total would be
`2+(q−1)q<m`. If a singleton occurs, the remaining `q` parts
must all be `q`. Summing (1) over a central row gives

\[
 a\le r²-m+\#\{\text{singleton blocks in the row}\}
 \le2q+1=2r-1.
\tag{2}
\]

## 2. The largest class size forces the minimal number of tops

Suppose `a=2q+1`. Equality in (2) forces every central row to
have exactly one singleton and `q` large blocks. Dually every
central column has that pattern. In particular all central block
sizes are one or `q`, though the two sizes at a top need not agree.

Let `u,v,w,z` count the paired types `(1,1),(1,q),(q,1),(q,q)`.
The `P` blocks at singleton-`C` tops partition `Z`, and the
dual statement holds for singleton-`P` tops. Thus

\[
                   u+qw=m,\qquad u+qv=m.
\]

Hence `v=w`. Subtract the first identity from the total `P`
weight `rm`; the result is `v+qz=qm`, so `v=qℓ` for an integer
`ℓ≥0`. Now `u=m−q²ℓ≥0` forces `ℓ=0` or `ℓ=1`.

If `ℓ=0`, the only paired types are `(1,1)` and `(q,q)`.
The [unit-or-large theorem](1485_unit_large_central_tiles.md) excludes
this case. If `ℓ=1`, the counts are exactly

\[
                     (u,v,w,z)=(1,q,q,q²),
\]

so `h=(q+1)²=r²`.

Every vertex has at least `r` top successors. Their total number,
counted instead at the `h` top targets, is `h·max d=r²·(n/r)=nr`.
Thus every vertex attains the lower bound exactly. The same argument
proves exactly `r` top predecessors. No equality of the two central
block sizes at an individual top was assumed.

## 3. One fewer vertex gives two partitions of the same subset

Suppose `a=2q`. Define the nonnegative integral slack

\[
                  w_u=r-c_u+\mathbf1_{c_u=1}-\alpha_u.
\]

By (2), the sum of these slacks on a central row is zero if it
has no singleton, and one otherwise. Every top occurs in a central
row; hence `w_u∈{0,1}`. A top with slack one occurs only in rows
containing a singleton, and those rows have pattern `q,…,q,1`.
Thus its `C` size is either one or `q`.

Let

\[
 R=\{u:c_u=q,\ w_u=1\},\qquad
 S=\{u:c_u=1,\ w_u=0\}.
\]

If a central row has no singleton, it contains neither set. If its
singleton has slack one, it again contains neither. Otherwise that
singleton belongs to `S`, and exactly one large top has slack one
and belongs to `R`. Consequently the `P` blocks indexed by `R`
and by `S` each partition the same subset `D⊆Z`.

The total `α` count is `ar`: every degree-`r+1` vertex has `r`
top predecessors. With `n1` singleton-`C` tops, summing the slack
definition therefore gives

\[
 \sum_T w_u=rh-rm+n_1-ar=r(h-r²)+n_1.
\]

Cancel the singleton tops with slack one from this identity. The result is

\[
                         |R|-|S|=r(h-r²).
\]

Since the two families partition `D` into nonempty blocks of size at
most `q`,

\[
\begin{split}
 r(h-r²)&\le |D|-\lceil |D|/q\rceil\\
         &\le m-\lceil m/q\rceil=q(q-1).
\end{split}
\]

Finally `floor(q(q−1)/(q+1))=q−2=r−3` for `q≥3`, proving
`h≤r²+r−3`. This argument uses only the displayed partitions and
integer counts, with no enumeration.
