# A full central core forces sharp regularity

Research note, 18 September 2026. **Theorem:** in a finite E1485 magma
with minimum translation degree `r` and exactly `r²` central vertices,
every vertex has exactly `r` sharp predecessors and successors.

There is no restriction on the number of occurring translation degrees.
In particular this is unconditional at minimum degree two, where the
[full central core has already been proved](1485_two_central_exclusion.md).
The full-central-core hypothesis remains unproved for arbitrary minimum
degree. This theorem is a pen-and-paper result, not yet a Lean declaration,
and does not by itself prove the square-or-double-square spectrum.

## Established ingredients

Write `n=|M|`, `s=max d`, so `n=rs`, and let `T` be the maximum-degree
class. The [full-core theorem](1485_full_central_core.md) gives `|T|=r²`
and a canonical relation

\[
 C(x)=x*T,\qquad C^-(x)=T*x,
\]

with `r` predecessors and successors at every vertex. It contains
every sharp edge and is contained in ordinary adjacency. Every vertex
has a sharp predecessor and successor.

If `a C b`, then every top extension or predecessor is good:

\[
 a*t=b\quad(t\in T\cap\operatorname{Row}(b)),
 \qquad t*b=a\quad(t\in T\cap\operatorname{Col}(a)). \tag{1}
\]

The ordinary edge condition `y→x` is equivalent both to `x∈Row(y)`
and to `y∈Col(x)`. Recall also the five-cycle rule: good two-edge
paths at positions `i` and `i+2` force goodness at position `i+1`.

## An ordinary edge supplies a complete top rectangle

Suppose `y→x`. Choose `v∈M` with `v*x=y`; **no restriction that
`v` be top is needed**. For every `u∈T`, E1485 gives

\[
 (x*u)*(u*(v*x))=u,
 \qquad\text{hence}\qquad (x*u)*(u*y)=u. \tag{2}
\]

The map `u↦(x*u,u*y)` injects `T` into `C(x)×C^-(y)`, with
multiplication as a left inverse. Both sets have cardinality `r²`,
so it is a bijection. Consequently

\[
 \boxed{y\to x\quad\Longrightarrow\quad
 C(x)\times C^-(y)\xrightarrow{\ (a,b)\mapsto a*b\ }T
 \text{ is a bijection}.} \tag{3}
\]

This is the essential strengthening of the earlier canonical-three-path
argument: the middle edge may be any ordinary edge.

## The two interior paths have the same goodness

Consider any three-edge path with canonical boundary edges,

\[
 a\mathrel C b\longrightarrow c\mathrel C d.
\]

Equation (3), applied to `b→c`, says `t=d*a∈T`. Close the path
to the five-cycle `a,b,c,d,t`.

The return `d→t→a` is good by definition. Equation (1) makes
`c→d→t` and `t→a→b` good as well. The two remaining paths have
the same goodness: if `a→b→c` is good, combine it with
`c→d→t` to force `b→c→d`; conversely combine `b→c→d`
with `t→a→b` to force `a→b→c`.

Thus

\[
 \boxed{a\mathrel C b\to c\mathrel C d
 \quad\Longrightarrow\quad
 (a*c=b\ \Longleftrightarrow\ b*d=c).} \tag{4}
\]

## Every canonical edge is sharp

Take an arbitrary path `a→b C c`. Choose a sharp predecessor
`x⇒a`, which also belongs to `C`. The path

\[
 x\mathrel C a\longrightarrow b\mathrel C c
\]

has good first interior path, because it contains the sharp edge
`x⇒a`. Equation (4) therefore makes `a→b→c` good.
We have proved that every ordinary predecessor of every canonical
edge gives a good path.

In particular, for `b C c`,

\[
 \operatorname{Col}(b)=\{a:a*c=b\}=R_c^{-1}(b).
\]

The uniform-fiber theorem now gives

\[
 d(b)=\frac n{d(c)},\qquad d(b)d(c)=n.
\]

By the sharp-edge degree criterion, `b→c` is sharp. Since sharp
edges were already contained in `C`, we conclude

\[
 \boxed{C=\text{sharp adjacency}.} \tag{5}
\]

The canonical relation is `r`-regular in both directions, proving
the theorem. Dually one can append a sharp successor in (4) to
prove directly that every canonical edge has every ordinary extension
good. No quotient, submagma extraction, or classification of four-degree
models is used.

## Immediate consequences and the remaining gap

The [sharp-regular four-degree calculation](1485_four_degree_regular_gap.md)
now applies to **every** full-core four-degree model, at every minimum
degree:

\[
 \boxed{|Z|=r²\text{ and exactly four degrees}\quad\Longrightarrow
 \quad n=8r².} \tag{6}
\]

The earlier minimum-at-most-six restrictions are thus superseded by
this general argument; their matrix identities remain valid.

More generally, complementary degree classes have equal cardinality.
All `r` sharp edges from the degree-`d` class enter the degree-`n/d`
class, which has exactly `r` incoming sharp edges at every vertex;
counting those edges proves equality. For any top `t`, both maps
`x↦t*x` and `x↦x*t` send degree `d` to degree `n/d`.

Every canonical two-edge path is now good, so for arbitrary top
parameters `t,u` and arbitrary `x`,

\[
 \boxed{(t*x)*(x*u)=x.} \tag{7}
\]

Thus these two maximum translations jointly determine `x`, even when
the two top parameters are not ordinarily adjacent. This does not
assert that their kernel equivalence relations commute.

The subsequent [Boolean-quotient theorem](1485_full_core_quotient.md)
now completes the cardinality argument under full core at every number
of translation degrees: `n=r²·2^m`. What remains is to prove the
full-core hypothesis for arbitrary finite models. No missing argument
is being replaced by a `sorry` or an asserted axiom here.
