# Pair retractions and joint translation-fiber support

Research note, 18 September 2026. Let a finite E1485 magma have order
`n`, minimum translation degree `r`, and `d(y)=|Row(y)|=|Col(y)|`.
This note records exact reductions and one global special case. It
does **not** establish the proposed rank bound or the local
common-fixed-point criterion below.

Define

\[
 Q_y(x)=(y*x)*(x*y).
\]

The [pair identities](1485_involutive_research.md) give

\[
 Q_y^2=Q_y,\qquad y*Q_y(x)=y*x,
 \qquad Q_y(x)*y=x*y.                             \tag{1}
\]

## Rank equals joint-fiber support

Let

\[
 J_y=\{(y*x,x*y):x\in M\}
 \subseteq Row(y)\times Col(y).
\]

Multiplication `(u,v)↦u*v` and the coordinate map
`z↦(y*z,z*y)` are inverse bijections between `J_y` and `im Q_y`,
by (1). Thus

\[
 \boxed{\operatorname{rank}Q_y=|J_y|.}             \tag{2}
\]

The joint-fiber multiplicity matrix has `d(y)` rows and columns,
each with sum `n/d(y)`, by uniform translation fibers. Equation (2)
counts its nonzero entries, not its total mass. In particular,

\[
 d(y)\le\operatorname{rank}Q_y\le d(y)^2.          \tag{3}
\]

The following support assertion would imply the stronger rank bound
`rank Q_y≥r d(y)`:

> Every nonempty `R_y`-fiber meets at least `r` distinct `L_y`-fibers.

It holds in all 390 examined tables of orders 8, 16, and 18, but a
general proof is not supplied here. Uniformity of the two marginal
partitions alone does not imply it.

For the weaker target `rank Q_y≥r²`, equation (3) already handles
`d(y)≥r²`. Central `y` also satisfies the target, with equality:
its central coordinate rectangle has size `r²` and is `im Q_y`.
Only the interval `r<d(y)<r²` remains nontrivial for that weaker
target.

## A natural r-point fiber subset need not be a transversal

Choose a sharp successor `a` of `y`, a value `v∈Col(y)`, and a
central vertex `h`. The sharp Cartesian factorization gives a
bijection `Row(a)→R_y^{-1}(v)`, namely `u↦u*v`. Centrality of
`h` makes `c↦a*c` injective on the `r`-element set `Col(h)`.
Consequently

\[
 \{(a*c)*v:c\in Col(h)\}
\]

is an `r`-element subset of the desired right fiber. However its
`L_y` values need not be distinct.

For example, in table 2 of the order-eight archive (zero-based table
and element labels), take `y=7`, `a=4`, `v=3`, and central `h=1`.
Then `Col(h)={0,4}`, and the constructed points are `0,5`.
Both have `L_7` value `4`. The entire right fiber is
`R_7^{-1}(3)={0,1,5,6}`, whose left image is `{4,5}`. Thus the
support bound itself holds, but this particular transversal argument
does not prove it. The full table is already displayed in the
[joint-fiber discussion](1485_image_research.md).

## The global pair identity does force a central groupoid finitely

There is a useful special case stronger than a single common fixed
point. Suppose

\[
 Q_y(x)=x\qquad\text{for all }x,y.                \tag{4}
\]

Let `T(x,y)=(x*y,y*x)`. Equation (4) gives
`T²(x,y)=(y,x)`, so `T` is a bijection of `M²`.
Each element `z` therefore occurs exactly `n` times as a product:
under the bijection, the pairs with first coordinate `z` number `n`.

Counting these occurrences by left input and using uniform fibers,

\[
 n=\sum_{a\in Col(z)}\frac n{d(a)},\qquad
 \sum_{a\in Col(z)}\frac1{d(a)}=1.                \tag{5}
\]

Every edge `a→z` satisfies `d(a)d(z)≥n`. There are `d(z)`
elements in `Col(z)`, so (5) implies

\[
 1\le\frac{d(z)^2}{n}.
\]

Thus every degree is at least `√n`. The extremal product theorem
`(min d)(max d)=n` forces all degrees to equal `√n`.
Every vertex is therefore central. This proves the finite implication

\[
 \boxed{(\forall x,y,\ Q_y(x)=x)
 \quad\Longrightarrow\quad\text{every vertex is central}.} \tag{6}
\]

## The local common-fixed-point claim remains separate

For one vertex `a`, the weaker hypothesis

\[
 Q_y(a)=a\qquad\text{for all }y
\]

does not make the global pair map bijective, so the preceding proof
does not establish that `a` is central. Centrals do satisfy this
hypothesis, but its converse remains unproved here.

A potentially sufficient intermediate statement is: if `h` is
central and `a` is such a common fixed point, then

\[
 a*((a*x)*h)=a*x\qquad\text{for all }x.            \tag{7}
\]

Indeed (7) says that `L_aR_h` fixes all of `Row(a)`, while that
projection has rank `r`; hence `d(a)=r` and `a` is central.
The statement (7) is a proposed target, not a proved identity.
Bounded equational searches with an explicit central parameter did
not resolve either (7) or the stronger local-centrality conclusion.
