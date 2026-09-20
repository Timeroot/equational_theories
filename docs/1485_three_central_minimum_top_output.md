# Three central vertices force a degree-four vertex

Research note, 18 September 2026. These are pen-and-paper necessary
conditions for finite E1485 magmas, not Lean declarations. They do not
exclude three central vertices or prove the full spectrum conjecture.

Let the minimum translation degree be three and suppose there are
exactly three central vertices. The [minimal-central-count theorem](1485_minimal_central_count.md)
gives nine top vertices and exactly three top predecessors and top
successors at every vertex. Let `q` be the least noncentral degree,
and let `p` be the smallest degree of a noncentral product of two top
vertices. Such a product exists because the central core is not full.

**Theorem.** The least noncentral degree is `q=4`, and the least degree
of a noncentral top product is `p=4`. In particular, twelve divides the
order, and there are at most nine degree-four vertices. The subsequent
[saturated-profile theorem](1485_three_central_saturated_four.md)
improves that bound to eight.

More generally, every noncentral top product of minimum such degree
has exactly one sharp predecessor and one sharp successor. Its number
of good ordered top endpoint pairs is four, five, or six.

The earlier minimal-central-count theorem leaves only `q=4` and `q=6`.
The argument below does not assume that degrees between `q` and `p`
are absent or sharp-regular.

## The least top output has sharp degree one

Label the central vertices `z_i` and the top vertices

\[
t_{ij}=z_i*z_j,\qquad i,j\in\{0,1,2\}.
\]

The unique central predecessor and successor of `t_ij` are `z_i`
and `z_j`. A top endpoint pair `t_ij,t_lm` has a central good
middle exactly when `j=l`.

Fix a noncentral top product `a` of degree `p`. Its two top profiles
have the form

\[
P_a=\{t_{i,u(i)}:i<3\},\qquad
Q_a=\{t_{v(j),j}:j<3\}.
\]

Here `u,v` are initially arbitrary functions on three labels. A bad
path from `P_a` through `a` to `Q_a` has a good replacement of
strictly smaller degree. That replacement is itself a top product,
so minimality of `p` makes it central. Thus the bad-path matrix is
exactly

\[
H_{ij}=\mathbf1_{u(i)=v(j)}.                     \tag{1}
\]

Write `k+` and `k-` for the sharp out-degree and in-degree of `a`.
Every top translation fiber has size three and contains all sharp
neighbors on the other side. Therefore every row of `H` has sum at
least `k+`, and every column has sum at least `k-`.

Both sharp counts are positive. It follows that `u` and `v` have
the same nonempty support. If `k+≥2`, each value in that support
would occur at least twice in the three-element list `v`. There
could be only one support value; both lists would then be constant
at that value, giving `H=J`. That is impossible because `a` is the
good middle of at least one top endpoint pair. Dually `k-≥2` is
impossible. Hence

\[
\boxed{k+=k-=1.}                                \tag{2}
\]

The common support of `u,v` has two or three values. With three,
both lists are permutations, so `H` has three ones. With two, both
have multiplicities `2,1`; their scalar product, and thus the number
of ones in `H`, is four or five. The number `g` of good ordered top
endpoint pairs with middle `a` is consequently

\[
\boxed{g=9-\sum_{i,j}H_{ij}\in\{4,5,6\}.}       \tag{3}
\]

This uses least degree among noncentral **top products**, not least
degree among all noncentral vertices.

## A general top-fiber slot bound

The following counting lemma is useful independently of the three-central
profile calculation. Suppose the minimum degree is `r`, every vertex has
exactly `r` top predecessors and successors, and every noncentral degree
is at least `q`. Fix any vertex `a` of degree `p>r`, with sharp
out-degree `k`. Let `g` count its good ordered top endpoint pairs.

For each parameter `y`, use the fixed-left projection

\[
P_y(x)=a*(x*y).
\]

The [fixed-parameter formula](1485_image_research.md) says that an
ordinary successor `x` of complementary degree `c=n/d(x)` is fixed
by exactly `cn/p` parameters. Also

\[
\operatorname{im}(P_y)=L_{y*a}^{-1}(a).
\]

There are `p-r` non-top predecessors of `a`. Each predecessor has
exactly `n/p` preimages under `R_a`. Thus at most `(p-r)n/p`
of the parameters fixing `x` can have `y*a` non-top. At least

\[
\max(0,c-p+r)\,n/p
\]

of its fixed parameters have `y*a` top. Since all parameters with
the same value of `y*a` have the same projection image, division
by `n/p` shows that `x` belongs to at least
`max(0,c-p+r)` of the `r` fibers

\[
L_t^{-1}(a),\qquad t\in\operatorname{TopPred}(a).
\]

These fibers have `r²` slots altogether. The `k` sharp successors
occupy `rk` slots. Their top inputs occupy exactly `g` slots. The
remaining ordinary successors of `a` are the `p-r-k` non-top,
non-sharp successors. Each has complementary degree greater than `r`,
and hence at least `q`. Counting their required slots proves

\[
\boxed{
g\le r(r-k)-(p-r-k)\max(0,q-p+r).
}                                               \tag{4}
\]

More precisely, the last term can be replaced by
`Σ_x max(0,n/d(x)-p+r)`, over those non-top, non-sharp successors.
All counts are of parameter fibers or of actual top translation
fibers; no uniformity for arbitrary composite maps is assumed.

The same argument works without constant top-neighborhood sizes.
If `a` has `I` top predecessors and `O` top successors, replace
the number of top fibers by `I` and the number of non-top
predecessors by `p−I`. It gives

\[
\boxed{g\le I(r-k)-(p-O-k)\max(0,q-p+I).}       \tag{5}
\]

More precisely subtract
`Σ_x max(0,n/d(x)−p+I)` over non-top, non-sharp successors.
There is a dual bound interchanging `I,O` and using the sharp
in-degree. These variable-neighborhood versions apply, for example,
to the remaining four-central, ten-top case.

## The degree-six alternative would force a degree-nine top output

Return to the three-central setting. If `q=4`, every degree-four
vertex has sharp degree one and six good top endpoint pairs, by the
minimal-central-count theorem. Thus `p=4`.

Suppose instead that `q=6`. Every degree-six vertex has sharp degree
three, and hence cannot be a noncentral top product: a top fiber at
such an output would contain all three sharp inputs as well as its
top input. Thus `p>6`. The three-degree product bound gives `p≤9`.

Apply (4) with `r=3`, `q=6`, and `k=1`, using (2). For `p=7`
or `p=8`, it reads

\[
g\le 6-(p-4)(9-p)
=\begin{cases}0,&p=7,\\2,&p=8.\end{cases}
\]

Both conclusions contradict `g≥4` from (3). Therefore the degree-six
alternative would require `p=9`.

## Equality in the product bound makes the good top pairs a matching

Here is the further [equality-case argument](1485_top_output_saturation.md),
valid at any minimum degree `r`. Suppose a top product `a` has degree
exactly `r²`. If
`u*v=a=u*w` with `u,v,w` top, the absorption identity and the
fixed-parameter count give

\[
\operatorname{Row}(v),\operatorname{Row}(w)
 \subseteq F_u(a),\qquad
|F_u(a)|=\frac{n^2}{s r^2}=s.
\]

Both ordinary rows already have `s` elements. Thus they are equal.
Choose a central successor `z` of `v`; every top vertex has one.
Equality of rows makes it a successor of `w` as well. But `v,w`
are both successors of `a`, and the paths

\[
a\to v\to z,\qquad a\to w\to z
\]

are good because they end centrally. Unique goodness forces `v=w`.
The dual argument shows that the left endpoint is unique for a fixed
right endpoint. Thus the good top endpoint pairs with middle `a`
form a matching between its top predecessor and successor sets.

In our setting those sets each have size three. A degree-nine first
top output therefore has `g≤3`, contradicting (3). This rules out
the degree-six alternative entirely.

We are left with `q=p=4`. Degree divisibility gives `12|n`, and the
degree-class bound in the minimal-central-count theorem gives at most
nine degree-four vertices. This is still not an exclusion of the
three-central case.
