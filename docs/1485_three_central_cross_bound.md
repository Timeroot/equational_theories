# A cross-packing bound for three central vertices

Research note, 19 September 2026. This is an analytic finite E1485
argument, not yet a Lean theorem. Suppose the minimum translation
degree is three and there are exactly three central vertices. The
top vertices form the grid `t_ij=z_i*z_j`, and every vertex has
three top predecessors and three top successors.

**Theorem.** If `x=t_ij*t_kl` is noncentral, then

\[
\begin{aligned}
d(x)&\le5+|\{v\in TopSucc(x):P_v=\{z_j\}\}|,\\
d(x)&\le5+|\{u\in TopPred(x):C_u=\{z_k\}\}|.
\end{aligned}                                                    \tag{1}
\]

In particular, every degree-seven top output has exactly one ordered
top representation. This statement does not assume that it is the
least noncentral output, and does not restrict the degree-four class.

## The five-point cross

Write `u=t_ij`, `w=t_kl`, so `j≠k`. Set `t=z_l*u`, which is
top, and use the nine-element fixed-parameter set

\[
F_t(u)=\{v:t*(u*v)=u\}.
\]

For every `v∈Col(z_l)`, E1485 gives `t*(u*v)=u`, and the
absorption identity puts `Row(u*v)` inside `F_t(u)`. Therefore
`Col(z_l)⊆F_t(u)` and `Row(x)⊆F_t(u)`. The distinguished input
`v=t_jl` gives the central product `u*v=z_j`, so also
`Row(z_j)⊆F_t(u)`.

The two top sets `Col(z_l)` and `Row(z_j)` meet only at `t_jl`.
Their union is a five-point cross. Central endpoint uniqueness gives

\[
Row(x)\cap Col(z_l)=\{w\}.
\]

Put `e=|TopSucc(x)∩Row(z_j)|`. Since `j≠k`, the point `w`
is not in `Row(z_j)`. Also `t_jl` does not belong to `Row(x)`:
it would be a second member of `Row(x)∩Col(z_l)`. Hence the
intersection of `Row(x)` with the cross has exactly `1+e` points.
Counting their union inside `F_t(u)` gives

\[
d(x)+5-(1+e)\le9,
\]

which is the first inequality of (1). The second is its dual.

## Degree seven has a unique top representation

Suppose `d(x)=7` and `x=t_ij*t_kl`. The first inequality of
(1) forces two of the three top successors of `x` into `Row(z_j)`.
The third is `t_kl`, where `k≠j`. Since their central successor
labels partition the three central vertices, necessarily

\[
TopSucc(x)=\{t_{kl}\}\cup\{t_{jv}:v\ne l\}.
\]

Dually,

\[
TopPred(x)=\{t_{ij}\}\cup\{t_{vk}:v\ne i\}.
\]

The central-middle matrix on these profiles has four ones. Its five
noncentral positions consist of the original pair `(t_ij,t_kl)`
and the four-element block

\[
\{t_{vk}:v\ne i\}\times\{t_{jw}:w\ne l\}.              \tag{2}
\]

No pair in (2) can have product `x`: its left endpoint has central
successor `z_k`, but only one top successor of `x` has central
predecessor `z_k`. Applying (1) to that purported representation
would give `d(x)≤6`. Thus the original pair is the only top
representation of `x`.

Every position in (2) is a bad path through `x`, and its product
therefore has strictly smaller degree. The four products have degree
four, five, or six. This lower-degree block condition is useful in
finite profile checks, but it is not by itself an exclusion of degree
seven or of the three-central branch.
