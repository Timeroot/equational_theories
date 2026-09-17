# E1485: translation ranks and fibers

Research notes, 17 September 2026. This is a pen-and-paper investigation;
no assertion here has yet been added as a Lean theorem.

Write the weak central groupoid law and its established dual as

\[
 (y*x)*(x*(z*y))=x,\qquad ((y*z)*x)*(x*y)=x.
\]

## A bijective translation forces the classified constant-row case

**Proposition.** If some left translation \(L_a:x\mapsto a*x\) is
bijective, then the magma has a constant column, and therefore also a
constant row. The same holds with “left” and “right” interchanged. No
finiteness assumption is needed.

**Proof.** Surjectivity supplies \(t\) with \(a*t=a\). The dual law,
with \((x,y,z)=(a,t,t)\), gives

\[
 ((t*t)*a)*(a*t)=a.
\]

Put \(b=(t*t)*a\); then \(b*a=a\). The original law now gives, for
every \(z\),

\[
 a*(a*(z*b))=(b*a)*(a*(z*b))=a.
\]

Since \(L_a^2\) is injective, \(z*b\) is independent of \(z\).
Thus column \(b\) is constant. A constant column implies a constant
row by the dual of the elementary argument in
[the main research note, §3](1485_spectrum_research.md#3-constant-rows-the-canonical-translation-has-period-dividing-ten).
The right-translation version follows by duality. □

In particular, in a finite magma, a single injective or surjective
translation suffices. By the established constant-row classification,
every such finite magma has power-of-two order and is a product of
two-element NAND magmas and 32-element cyclically twisted NAND magmas.

The equivalence is exact: a constant row supplies a bijective translation
by its distinguished upper constant. Consequently a finite model not in
that classified family has every left and right translation of rank
strictly less than its order.

**Slight strengthening.** Surjectivity can be replaced by the weaker
assumption that \(a\) lies in the image of \(L_a\): the proof uses
only this and injectivity of \(L_a\).

## The equal-fiber conjecture is now proved for finite models

Le Floch conjectured that, for fixed \(x\), every nonempty fiber of
\(L_x\) and every nonempty fiber of \(R_x\) has the same cardinality.
The [graph research note](1485_graph_research.md#sharp-edges-give-exact-rectangular-factorizations)
now proves this, including equality between the left- and right-fiber sizes
at the same element. Its argument first constructs sharp predecessors and
successors by a finite common-fixed-point argument. A sharp edge `e ⇒ a`
then gives an explicit bijection

\[
 M\longrightarrow\operatorname{Row}(a)\times\operatorname{Col}(e),
 \qquad x\longmapsto(a*x,x*e),
\]

with inverse `(u,v)↦u*v`. Coordinate projection gives uniform fibers;
a further count proves equal row and column sizes at every element.
The proposition above remains a separate short proof of the bijective
case, valid even for infinite models.
