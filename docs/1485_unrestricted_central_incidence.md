# Unrestricted central incidence: replacement closure and a counting limitation

Research note, 18 September 2026. Let `M` be a finite E1485 magma,
let `r` be its minimum translation degree, and fix a central vertex
`h`. No full-central-core assumption is made in this note. The results
are necessary conditions;
they do **not** prove or refute unrestricted central rectangle closure.

## The auxiliary relation is two-sided

The [regular-relation construction](1485_sharp_degree_defect.md) gives

\[
B_h(a)=a*\operatorname{Col}(h)
=\operatorname{im}(L_aR_h)
=L_{h*a}^{-1}(a).
\]

This relation is `r`-regular in both directions and contains every
sharp edge. Its predecessor sets also have the exact description

\[
\boxed{B_h^-(b)=\operatorname{Row}(h)*b
=\operatorname{im}(R_bL_h)
=R_{b*h}^{-1}(b).}                              \tag{1}
\]

For the first equality, suppose `b=a*c` with `c∈Col(h)`, and
write `c=z*h`. E1485 gives `(h*a)*b=a`, and `h*a∈Row(h)`.
Conversely, if `a=t*b` with `t=h*z∈Row(h)`, the dual identity
gives `a*(b*h)=b`, and `b*h∈Col(h)`. The remaining equalities
are the dual of the established successor-fiber formula. In particular,
the same central parameter gives the two directions; no independence
of `h` is asserted.

## Taking the good replacement preserves marked auxiliary edges

Let `a→b→c` be an ordinary two-edge path and put `v=a*c`, its
unique good middle. Then

\[
\boxed{
a\mathrel{B_h}b\Longrightarrow a\mathrel{B_h}v,
\qquad
b\mathrel{B_h}c\Longrightarrow v\mathrel{B_h}c.} \tag{2}
\]

To prove the first assertion, write `c=b*z`. For fixed `a`, the
mixed projections `P_z(u)=a*(u*z)` satisfy
`P_hP_zP_h=P_zP_h`. Hence `P_z` preserves the image of `P_h`,
which is `B_h(a)`. Applying it to `b` gives `P_z(b)=v`.

For the second assertion, write `a=z*b`, using the column definition
of ordinary adjacency. The dual fixed-right projections
`Q_z(u)=(z*u)*c` preserve `im(Q_h)=B_h^-(c)` by the same band
identity. Applying `Q_z` to `b` gives `v` again.

Consequently every auxiliary two-edge path has its good replacement
inside the same auxiliary rectangle:

\[
\boxed{a\mathrel{B_h}b\mathrel{B_h}c
\Longrightarrow a*c\in B_h(a)\cap B_h^-(c).}     \tag{3}
\]

If `b≠a*c`, the [finite strict-descent theorem](1485_image_research.md)
gives `d(a*c)<d(b)`. Thus the regular graph `B_h` is closed under
replacement by lower-degree good middles. Neither this closure nor
regularity by itself has yet been shown to make all its paths good.

## The unrestricted central/top matrix equations

Write `Z` for the central class, `T` for the maximum-degree class,
`m=|Z|`, and `q=|T|`. Let `B` be adjacency from `Z` to `T`,
`C` adjacency from `T` to `Z`, and `D` adjacency within `T`.
Every row of `B` and column of `C` has sum `r`. Every path with
a central endpoint is good, and its good middle is top. Therefore

\[
\boxed{BC=J_{m,m},\qquad BD=J_{m,q},\qquad
DC=J_{q,m}.}                                    \tag{4}
\]

Let `k^-=B^T1` and `k^+=C1`; their entries lie between one and
`r`. For `K=CB`, which is zero-one because central middles are
unique, (4) gives

\[
\begin{aligned}
DK&=\mathbf1(k^-)^T,& KD&=k^+\mathbf1^T,\\
K^2&=k^+(k^-)^T,& DKD&=mJ_{q,q}.                 \tag{5}
\end{aligned}
\]

These identities hold before central cardinality or sharp-degree
regularity is established.

## Limits of the incidence equations

The separate [central-incidence obstruction](1485_central_incidence_obstruction.md)
gives an explicit abstract system at `r=3`, `m=4`, and `q=8`.
It satisfies all three equations in (4), `CB≤J`, and the relevant
degree bounds, but has neither `m=r²` nor `q=r²`. It is not an
E1485 magma. Therefore the incidence equations alone do not prove
central rectangle closure; an argument must use further information,
such as replacement closure together with the full multiplication.

## The least noncentral degree has balanced sharp counts

Assume degrees are nonconstant, and let `q>r` be the least occurring
degree larger than `r`. Fix a vertex `a` of degree `q` and let
`k^+` and `k^-` be its sharp out-degree and in-degree.

Every non-top ordinary neighbor of `a` is sharp. Indeed, if such
a neighbor has degree `n/j`, degree reciprocity makes `j` an
occurring degree. The ordinary edge bound gives `j≤q`; not being
top gives `j>r`. Minimality forces `j=q`.

Consequently the ordinary row and column of `a` each split into
top neighbors and sharp neighbors, with respective top counts

\[
\alpha=q-k^+,\qquad \beta=q-k^-.
\]

These top sets are nonempty: for any central `z`, the product
`z*a` is a top predecessor of `a`, and `a*z` is a top successor.
For each top predecessor `t` of `a`, the fiber `L_t^{-1}(a)`
has `r` elements, lies in `Row(a)`, and contains all `k^+`
sharp successors of `a`. Thus its other `r-k^+` elements are
exactly its top inputs. Counting ordered top endpoint pairs with
good middle `a` gives `β(r-k^+)`. The dual count gives
`α(r-k^-)`. Equating them yields

\[
(q-k^-)(r-k^+)=(q-k^+)(r-k^-),
\]

and hence `(q-r)(k^--k^+)=0`. Since `q>r`,

\[
\boxed{k^+=k^-=k,\qquad
|\operatorname{TopPred}(a)|=|\operatorname{TopSucc}(a)|=q-k.}
                                                        \tag{6}
\]

The exact number of ordered top endpoint pairs whose product is `a`
is therefore

\[
\boxed{\#\{(t,u)\in T^2:t*u=a\}=(q-k)(r-k).}    \tag{7}
\]

In particular, a vertex of the least noncentral degree is a top-top
output if and only if its sharp degree is smaller than `r`.
This count does not assert that every noncentral vertex has degree
`q`, or that its higher-degree analogues have only sharp non-top
neighbors.

## A failure of full core produces a low-degree irregular vertex

For arbitrary degree, every **noncentral** top-top output `a=t*u`
has both sharp degrees at most `r-1`. The `r`-element fiber
`L_t^{-1}(a)` contains the top input `u` and all sharp successors
of `a`. None of the latter is top, because `a` is noncentral.
This proves the out-degree assertion, and the dual fiber proves
the in-degree assertion.

If `|Z|<r²`, the central coordinate rectangle

\[
\{u*v:u\in\operatorname{Row}(h),\ v\in\operatorname{Col}(h)\}
\]

has `r²` points and contains all central vertices. It therefore
contains a noncentral top-top output. The three-degree product bound
places its degree in `(r,r²]`. Thus

\[
\boxed{|Z|<r^2\Longrightarrow
\text{some degree in }(r,r^2]\text{ has a vertex with both
sharp degrees }<r.}                              \tag{8}
\]

The stronger interval `(r,2r)` has not been established. The proof
of (6) relies on the least *noncentral* degree. Replacing this by the
least *irregular* degree is not automatic: a non-top non-sharp neighbor
may have complementary degree below it, and vertices of that smaller
degree may already be sharp-regular.

## Central coordinates make every adjacency block unipotent

Fix `t∈Row(h)` and `u∈Col(h)`. Both are top, and `u*t=h`.
The mixed-translation rank formula therefore makes `L_tR_u` and
`R_uL_t` rank-`s` idempotents. In particular

\[
L_tR_uL_t=L_t,\qquad R_uL_tR_u=R_u.
\]

Consequently `φ=R_u` is a bijection from `X=Row(t)` to
`Y=Col(u)`, with inverse `L_t`; both sets have size `s`.
Index the ordinary-adjacency block from `X` to `Y` using this
bijection:

\[
N_{a,x}=\mathbf1_{a\to\varphi(x)}\qquad(a,x\in X).
\]

Every diagonal entry is one, since `φ(a)=a*u∈Row(a)`.
If `N_{a,x}=1` with `a≠x`, consider the ordinary five-cycle

\[
t\to a\to\varphi(x)\to u\to h\to t.
\]

The three paths starting, ending, or passing through `h` are good.
The other two have the same status, by the five-cycle rule. The
good middle for `t→a→φ(x)` is `t*φ(x)=x`, so this path is bad.
The other path `a→φ(x)→u` is therefore bad too, and its good
middle is `a*u=φ(a)`. Strict degree descent at a bad middle gives

\[
\boxed{N_{a,x}=1,\ a\ne x
\quad\Longrightarrow\quad
d(x)<d(a),\qquad d(\varphi(a))<d(\varphi(x)).}       \tag{9}
\]

Thus ordering `X` by increasing degree makes `N` lower triangular,
with ones on the diagonal. In particular every such adjacency block
is **unimodular** and has exactly one perfect matching, namely `φ`:
a nonidentity matching would contain a cycle of strictly decreasing
degrees. Writing `N=I+H`, the strictly triangular matrix
`H` is nilpotent; its nilpotence index is at most the number of
distinct translation degrees. Its inverse is the finite integer sum
`I-H+H²-⋯`.

These blocks cover the entire adjacency matrix: as `t` ranges over
`Row(h)`, the sets `Row(t)=L_h^{-1}(t)` partition `M`, and as
`u` ranges over `Col(h)`, the sets `Col(u)=R_h^{-1}(u)` partition
`M`. Each block's diagonal matching is precisely the part of `B_h`
in that block. In particular the ordinary adjacency matrix has rank
at least `s` over every field.

This is an unconditional finite theorem, but it does not make the
different block matchings agree or prove full core. In particular,
ordinary rows need not be unions of fibers of the top translations;
that stronger shortcut fails in known finite models. Nor does the
whole matrix necessarily have rank `s`: an
[eight-element counterexample](1485_adjacency_rank_counterexample.md)
has rank five and `s=4`, despite all four coordinate blocks being
unimodular.
