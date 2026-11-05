# Central towers of cross-inverse loops

Research proof, 4 November 2026. The general central-extension construction is
formalized in `Parastrophes/CrossInverseLoopExtensions.lean`, and the exact
period multiplication formula is formalized in
`Parastrophes/CrossInverseLoopPeriods.lean`. The orbit argument
below supplies offsets at every height; that existence argument is **not yet
formalized in Lean**. The accompanying Python program constructs and checks
finite instances. This does not settle a single-equation characterization or
the existence of a uniform inverse term.

## Result

For every prime (p>3) and integer (k\geq0), there is a cross-inverse loop

\[
 |Q_k|=p^{k+1}
\]

whose inverse permutation has order exactly (2p^k). More precisely, there is
a surjective additive grading \(\phi_k:Q_k\to\mathbb F_p\). Every element of
nonzero grade has inverse period exactly (2p^k). On the zero-grade fibre the
inverse squares to the identity, and its only fixed point is the loop unit.

Thus the inverse permutation has ((p-1)/2) cycles of length (2p^k), one
fixed point, and ((p^k-1)/2) additional cycles of length two. For (k=0),
the nonzero-grade cycles themselves have length two.

The already formalized Cartesian-square construction sends (Q_k) to a
member of E481's finite left-division image, of order (p^{2k+2}). Its
distinguished permutation has order (4p^k). This supplies a systematic
sequence of examples beyond the earlier isolated 25- and 125-element loops.

## Induction invariant and extension

Write the product of the current loop as (x\cdot y), its unit as (e), and
its inverse permutation as (J). The cross-inverse identity is

\[
 (x\cdot y)\cdot Jx=y.
\]

It implies that (J) is an automorphism. Suppose the result's stronger
grading and period assertions hold, with (L=2p^k). In particular,

\[
 \phi(x\cdot y)=\phi(x)+\phi(y),\qquad
 \phi(Jx)=-\phi(x),\qquad J^L=1.
\]

For an offset (c:Q^2\to\mathbb F_p), set

\[
 (x,u)\cdot'(y,v)=(x\cdot y,u+v+c(x,y)).
\]

This is a cross-inverse loop if

\[
 c(e,x)=c(x,e)=0,\qquad
 c(x,y)+c(x\cdot y,Jx)=c(x,Jx).
\]

Its inverse and grading are

\[
 J'(x,u)=(Jx,-u-c(x,Jx)),\qquad\phi'(x,u)=\phi(x).
\]

These extension statements hold over any abelian coefficient group, and are
the part already checked in Lean.

## Choosing the diagonal offsets

Choose one representative (r) in each (J)-cycle of nonzero grade. Define
\(\delta(r)=\phi(r)\), and set \(\delta=0\) everywhere else. For every (x),
the alternating trace satisfies

\[
 D_L(x):=\sum_{i=0}^{L-1}(-1)^i\delta(J^i x)=\phi(x).
\]

Indeed, a nonzero-grade cycle has length exactly (L). Its trace has one
nonzero summand. If (J^i x=r), that summand is
\((-1)^i\phi(r)=\phi(x)\). A zero-grade cycle has zero trace. There are only
((p-1)/2) nonzero entries in \(\delta\), independent of the height.

## Solving the offset equations on orbits

On ordered pairs define

\[
 T(x,y)=(x\cdot y,Jx).
\]

The cross-inverse identity and inverse automorphism give

\[
 T^2(x,y)=(y,J(x\cdot y)),\qquad T^3(x,y)=(Jx,Jy).
\]

Consequently (T) is a permutation. We solve on each of its cycles by the
recurrence

\[
 c(T(x,y))=\delta(x)-c(x,y).
\]

An even cycle permits this recurrence exactly when the alternating sum of
the first-coordinate diagonal offsets around the cycle is zero. All cycles
except ((e,e)) are even: an odd cycle would give odd periods for both
coordinates under (J), whose only odd-period point is (e).

If both coordinates have grade zero, every point of their (T)-cycle also
has both grades zero, so the consistency sum vanishes term by term. Otherwise
the period of the pair under (J\times J) is exactly (L). The period (r)
under (T) therefore obeys

\[
 r/\gcd(r,3)=L,
\]

so (r=L) or (r=3L), since (3\nmid L). The alternating sum over (3L)
steps of (T), grouped into triples, is

\[
 D_L(x)-D_L(x\cdot y)+D_L(y)=0.
\]

To check the signs, the first coordinates in the (i)-th triple are
\(J^i x,J^i(x\cdot y),J^i y\), with signs
\((-1)^i,-(-1)^i,(-1)^i\). If (r=L), this is three copies of the cycle
sum; if (r=3L), it is one copy. Since 3 is invertible in \(\mathbb F_p\),
the cycle sum is zero in either case.

For a cycle containing a pair with a unit coordinate, initialize (c(e,x)=0)
or (c(x,e)=0). The segment

\[
 (e,x)\longmapsto(x,e)\longmapsto(x,Jx)\longmapsto(e,Jx)
\]

then has offset values (0,0,\delta(x),0). This enforces every unit
normalization on that cycle, and ensures (c(x,Jx)=\delta(x)). On every
other cycle initialize one offset arbitrarily, for example at zero. Set
(c(e,e)=0). This constructs the required offset everywhere.

## Period growth and base case

Because (L) is even, iterating the displayed inverse gives

\[
 (J')^L(x,u)=(x,u+D_L(x))=(x,u+\phi(x)).
\]

It follows that \((J')^{pL}=1\). For a nonzero-grade element, any return
time is a multiple of (L), by projection to the base. Its residual fibre
translation has nonzero step \(\phi(x)\), so its order is precisely (p).
Thus its period upstairs is exactly (pL).

On the zero-grade fibre, \(\delta\) is zero and (J^2=1), so \((J')^2=1\).
A fixed point of (J') projects to the unique fixed point (e) of (J);
its fibre coordinate must satisfy (-u=u), hence (u=0) because (p) is odd.
The grading remains a surjective homomorphism, and each fibre has size
multiplied by (p).

Start with the additive loop \(\mathbb F_p\), inverse (Jx=-x), and grading
\(\phi(x)=x\). Its nonzero elements have period two. This completes the
induction, including the claims about cycle counts.

Finally, the Cartesian-square turn is (f(a,b)=(b,Ja)), so
(f^2=J\times J). On ((x,e)) with nonzero grade, an odd iterate cannot
return to ((x,e)), and an even iterate returns exactly when its half is a
multiple of (L). Its exact period is (2L), as claimed.

## Reproduction

Run `python3 scripts/check_cross_inverse_loop_tower.py --prime 5 --levels 4`.
This constructs loops of orders 5, 25, 125, 625 and 3125, with inverse orders
2, 10, 50, 250 and 1250. It checks the full loop tables, both cancellation
properties, the inverse automorphism, grading, offsets, and exact cycles.
It does not materialize the much larger Cartesian-square division tables.

The table-based replayer uses quadratic space in the largest loop order.
The general proof above supplies all heights; increasing the replayer's
height is only an additional finite check, not part of the proof.
