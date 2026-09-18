# E1485 spectrum: the remaining degree patterns

Research status, 18 September 2026. The full square/twice-square converse
is still open in this work. This note records a reduction that includes
all models with at most three distinct translation degrees. The arguments
are pen-and-paper proofs, not new Lean declarations.

Let `M` be a nonempty finite E1485 magma of order `n`. The
[finite structure theorems](1485_graph_research.md) give
`d(x)=|Row(x)|=|Col(x)|`, uniform nonempty translation fibers, and a
sharp successor and predecessor of every element. An edge `x⇒y` is
sharp precisely when `d(x)d(y)=n`.

## Odd numbers of degree values force square order

Let `D={d(x):x∈M}` be the set of distinct degree values. If `d∈D`,
choose a vertex of degree `d` and a sharp successor. That successor
has degree `n/d`. Thus the map

\[
 d\longmapsto n/d
\]

is an involution of `D`. If `|D|` is odd, this involution has a fixed
point: its non-fixed orbits have size two. For a fixed degree `d`,
`d=n/d`, and hence

\[
 \boxed{|D|\text{ odd}\quad\Longrightarrow\quad n=d^2.}
\]

In particular this handles every model with one or three degree values,
and equally applies to five, seven, or any other odd number of values.
Equivalently, if `n` is not a square, its occurring degree values come
in distinct complementary pairs.

## Two degree values force twice-square order

If `D={r,s}` with `r<s`, the extremal product theorem gives `n=rs`.
The [three five-cycle counts](1485_two_degree_lower_bound.md) prove

\[
 \boxed{s=2r,\qquad n=2r^2.}
\]

No hypothesis about constancy of sharp-neighbor counts is used here.
Their constancy is a stronger structural question, still open in general;
it is not needed for this cardinality theorem.

Every product of two distinct primes is consequently excluded. Such an
order cannot have a constant row (constant-row models have power-of-two
order), and degree divisibility and the extremal product then force
exactly the two prime degrees. They cannot have ratio two.

## What a remaining counterexample would have to look like

A finite model whose order is neither a square nor twice a square must
have **an even number of distinct translation degrees, at least four**.
For four values, write them in increasing order as

\[
 r<a<b<s.
\]

The complementary-degree involution is order reversing, so

\[
 rs=ab=n.
\]

This does not yet force `b=2a`, or otherwise give the desired square
class of `n`. The two-degree proof cannot simply be applied to the
middle degree classes: their union need not be closed under multiplication.

The general goodness-reflecting Boolean quotient theorem remains another
possible route. Its uniform square fibers are proved, but existence of
such a quotient for every finite model remains unproved. In particular,
uniform fibers of individual translations must not be confused with
uniform joint fibers of `x↦(h*x,x*h)` for central `h`: the latter claim
is false, as the explicit order-eight example in the
[projection note](1485_image_research.md) shows.
