# E467, finite FO definability, and E1516

28 September 2026. The original target, **E467 → E1516 in finite FO
definability**, remains open. This pass does give a complete mathematical
negative for the nearby direction **E467 → E63**, with a finite witness of
order 1681. The full negative is proved in Lean as
`Definability.GLTwoE467.Equation63_not_definableFromFin_Equation467` in
`Definability/GLTwoE467.lean`, using the shared equivariance argument in
`Definability/GLTwoE63.lean`. The axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

Here `B → A` means that an operation satisfying A is parameter-free
first-order definable on every finite magma satisfying B. It would imply
Spec(B) ⊆ Spec(A). Refuting definability does **not** by itself refute this
spectrum inclusion.

## A finite FO negative: E467 does not define E63

Let V = F₄₁² and set

    x ◇ y = 4x + 32y.

For a scalar-linear operation `ax + by`, E467 is equivalent to

    ab(b+1) = 1,       ab³ + a + b⁴ = 0.

The coefficients (4,32) satisfy these equations modulo 41. Every invertible
linear transformation of V preserves ◇. Hence any parameter-free definable
operation □ must be equivariant under GL₂(F₄₁).

Suppose □ satisfied E63, written

    y □ (x □ (x □ y)) = x.

On independent ordered pairs, GL₂-equivariance gives fixed coefficients
a,b with x □ y = ax+by. E63 on a finite set is a quasigroup law, so a and b
are nonzero: if, for example, a=0, varying the first basis vector while
fixing the second contradicts right cancellation. Also b≠−1, since then
x □ (x □ y) = y on independent pairs and the displayed equation would make
y □ y equal to every x independent of y.

Consequently both inner and outer pairs in E63 remain independent, and
coefficient comparison gives

    ab(b+1)=1,       a+b³=0.

It follows that b⁵+b⁴+1=0. But

    t⁵+t⁴+1 = (t²+t+1)(t³−t+1)

has no root in F₄₁. The quadratic has no root because 3 does not divide 40;
the cubic is excluded by a 41-value check. `GLTwoE467.no_root` proves the
combined exclusion by kernel computation. Thus the proposed definable
companion cannot exist.

This witness also rules out the corresponding unrestricted-carrier FO
direction, and the stronger term-definable and structural directions. It
does not distinguish the two spectra at 1681: this order already supports
E63 models.

## Exact reduction of E1516 on these scalar source models

The analogous calculation for E1516 has an extra parameter: its leading
square y □ y need not equal (a+b)y. Ignoring this distinction would give
an invalid negative proof.

In fact the full automorphism group of the source `4x+32y` on F₄₁ᵈ is
GL_d(F₄₁). Zero is its unique idempotent, since 4+32≠1. Any automorphism
fixes zero, commutes with multiplication by 4 and by 32, and then preserves
addition using

    u+v = (4⁻¹u) ◇ (32⁻¹v).

An additive bijection over a prime field is linear. On a finite structure,
an invariant graph is parameter-free FO definable: each automorphism orbit
has a formula obtained from the complete finite multiplication table.
Therefore the existence of an equivariant companion is an exact criterion
for FO definability on each of these particular source models.

For d≥2, a GL_d-equivariant operation has fixed coefficients a,b on
independent pairs, but may behave differently on collinear pairs. Its
restriction H to a line is homogeneous:

    H(tx,ty)=tH(x,y)    for t≠0.

Write H(y,y)=sy. If □ satisfies E1516, it is a finite quasigroup and its
squaring map is bijective, hence s≠0. The same independence argument now
gives

    ab(b+1)=1,       as+b³=0,

or

    a=1/[b(b+1)],       s=−b⁴(b+1),       b≠0,−1.

Conversely, given a homogeneous E1516 operation H on F₄₁ with this square
multiplier and such a pair a,b, define □ on V as follows:

* on an independent pair, use ax+by;
* on a collinear pair (u e,v e), use H(u,v)e.

Homogeneity makes the second clause independent of the chosen nonzero e.
For collinear input, E1516 holds inside the line by the hypothesis on H.
For independent input, all the required pairs stay independent, and the two
coefficient equations prove E1516. The construction is GL_d-equivariant.

Thus for every d≥2 the particular source model admits an E1516 companion
**if and only if** there is a homogeneous E1516 operation on F₄₁ with square
multiplier in

    {2,3,4,5,7,8,10,13,14,15,16,19,21,22,23,24,26,28,30,31,32,34,36,37,39,40}.

For d=1 there is no restriction to this subset: every nonzero square
multiplier must be considered. A model found this way would settle the
currently open positive spectrum cell at 41. A refutation of all these
homogeneous cases would refute the FO direction without requiring a full
nonexistence proof for arbitrary 41-element E1516 magmas.

## The reduced finite search

For an odd prime p, write a homogeneous operation as

    H(0,y)=cy,
    H(x,y)=x f(y/x)    when x≠0.

In a finite E1516 model c≠0, f is a permutation, f(0)≠0, and s=f(1)≠0.
Besides the trivial (0,0) instance, the law is exactly

    f(f(0))=c⁻¹,
    f(c²/s)=0,
    f(f(f(t))/(st))=1/(st)       for every t≠0.

Right cancellation additionally says that the values c and f(t)/t for
t≠0 form a permutation of F_p. These give a small constraint problem with
p function values and c, rather than a p²-entry unrestricted table.

`scripts/fo_467_1516_research.py` implements this reduction. The saved
`data/spectrum/fo_467_1516_research.json` records a four-second,
single-worker CP-SAT attempt for each of the 40 square multipliers at 41.
There were **39 timeouts and one infeasible restricted case (s=40)**.
There is no claimed exclusion of order 41, no claimed finite FO answer for
E467 → E1516, and no Lean certificate for that restricted infeasibility.

The last restricted exclusion also has a short paper proof, independent of
the solver. More generally, in an E1516 quasigroup, if its square map S is
an involutive automorphism, then S is the identity. Apply S to
`x = Sx □ (x □ Sx)` to get
`Sx = x □ (Sx □ x)`. Since `Sx=x □ x`, left cancellation gives
`Sx □ x=x`. Applying S again gives `x □ Sx=Sx=x □ x`, so left cancellation
gives Sx=x. For a homogeneous operation on an odd prime field, the square
map Sx=−x is an involutive automorphism but is not the identity. It is
therefore impossible. Thus s=40 can be removed from the 26-element set
above without trusting the search result.

As a check, the solver found at p=5 the genuinely nonlinear example

    c=2,       [f(0),f(1),f(2),f(3),f(4)]=[2,1,3,4,0].

The script independently evaluates E1516 on all 25 pairs and verifies all
scaling symmetries. Here s=1, while f(0)+c=4: the square coefficient is not
the sum of the two axis coefficients. This concretely demonstrates why a
linear-coefficient obstruction alone does not settle the E1516 target.

Reproduce the scalar checks without solver dependencies using
`python3 scripts/fo_467_1516_research.py --scalar-only`. Run the bounded
symmetry search with `--prime 41 --seconds 4 --output /tmp/fo41.json`.
