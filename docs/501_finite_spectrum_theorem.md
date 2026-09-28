# The finite spectrum of E501

27 September 2026. Both directions are formalized in Lean, using only
`propext`, `Classical.choice`, and `Quot.sound`; there are no admitted steps
or native computations.

**Theorem.** A positive integer n is the order of an E501 magma if and only
if n is congruent to 0 or 1 modulo 4.

E501 is the identity

\[
                    y*(y*(x*(x*y)))=x.
\]

## Squaring the left translations

Write L_x(y)=x*y and define q(x,y)=L_x²(y). The identity says precisely

\[
                         q(y,q(x,y))=x,
\]

so q is a semisymmetric quasigroup. Conversely, any semisymmetric operation
q whose left translations have permutation square roots gives an E501
operation by choosing one root in each row. The choices need not be related
to one another, and the resulting E501 operation need not be a quasigroup.

## Necessity: the sign of coordinate swap

For a finite E501 magma, every L_y is surjective, since the displayed law
expresses every x as L_y of another element. Hence it is a permutation.
Let P(x,y)=(x,L_x(y)), a permutation of the ordered pairs, and let S be
coordinate swap. The permutation

\[
                         T=SP²,
\]

acts as T(x,y)=(q(x,y),x). Semisymmetry also gives
q(q(x,y),x)=y: apply its defining identity to y and q(x,y), then use
q(y,q(x,y))=x. Therefore T³ is the identity.

An odd-order permutation has sign +1, and a square has sign +1. Thus
`sign(S)=sign(T)=+1`. Coordinate swap has one transposition for each
unordered pair of distinct elements, so n(n−1)/2 is even. Equivalently,
n is 0 or 1 modulo 4.

## Sufficiency: square roots of reflections

An involution has a permutation square root whenever its number of
transpositions is even. Pair the transpositions `(a b)` and `(c d)` and
replace them by the four-cycle `(a c b d)`, whose square is their product.
Leave its fixed points fixed.

On any abelian group H, the operation q(x,y)=−x−y is semisymmetric.
Each left translation r_x(y)=−x−y is an involution. We choose H so that
every r_x has an even number of transpositions.

* If n=4k+1, take H=Z/n. The equation r_x(y)=y has exactly one solution,
  since multiplication by 2 is invertible. Thus r_x has (n−1)/2=2k
  transpositions.
* If n=4k>0, take H=(Z/2)×(Z/(2k)). Multiplication by 2 has a kernel
  of size four. Each equation 2y=−x therefore has either zero or four
  solutions. Thus r_x has n/2=2k or (n−4)/2=2k−2 transpositions.

Choose a square root p_x of r_x in every row and put x*y=p_x(y). Then

\[
 y*(y*(x*(x*y)))=r_y(r_x(y))=-y-(-x-y)=x.
\]

This constructs every required order, including the singleton. There are
no exceptional orders and no finite-model search is needed.

## Verification and consequences

The executable construction has been checked directly at every admissible
order through 128. These checks support the implementation; the proof above
works for all orders. The complete spectrum is the same as E167's, although
equality of spectra alone does not establish FO-definability in either
direction. In fact, the finite FO graph already refutes both directions
between E167 and E501.

Lean entry points:

* `Spectrum.exact_501` and `Spectrum.hasModel_501_iff` in
  `equational_theories/Spectrum/Equation501.lean` give the exact classification.
* `Spectrum.E501.residue` in `Spectrum/Equation501/Parity.lean` proves necessity.
* `Spectrum.InvolutionRoots.exists_root_of_sign` in `Spectrum/InvolutionRoots.lean`
  proves the reusable square-root lemma. The even-order construction uses the
  sign of a product permutation instead of counting its fixed points explicitly.
* The catalogue transfers the result to the dual E3106, closing two formerly
  unknown exact spectra.

The executable construction is `python3 scripts/spectrum_501.py`; use
`--order N` to print a verified multiplication table at any admissible order.
