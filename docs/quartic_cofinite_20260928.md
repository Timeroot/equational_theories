# Explicit cofinite constructions for E1076 and E1313

28 September 2026. This replaces the appeal to Wilson's theorem by an explicit
finite construction certificate and an elementary induction. Both laws have
models at every order **n ≥ 107,773**. The models are idempotent.

The construction is proved in Lean. `Spectrum.QuarticTail.model_1076` and
`model_1313` have passed their transitive axiom audits with only `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry` or native-computation axiom
is used. Orders below the cutoff that are not supplied by the certificate
remain possible exceptions, not exclusions.

## Seeds shared by the two problems

Let f(b)=b⁴−b³−b²+b−1. Over any commutative ring, if f(b)=0, then

- x*y=(1−b)x+by satisfies E1076;
- x*y=bx+(1−b)y satisfies E1313.

Both operations are idempotent. Expanding either defining equation leaves
(y−x)f(b). Thus every root modulo a positive integer gives a model of that
order. The certificate records the modulus and root, not a multiplication
table. In addition, the existing companion-matrix construction provides an
idempotent model of every positive fourth-power order for each law.

In particular, both laws have idempotent models of orders 5, 16, 17, 79,
80=5·16, and 81=3⁴. Empty and singleton models are allowed as group fillings;
zero is never counted as an element of the positive spectrum.

## The two construction rules

A TD(k,q) consists of k groups of q points, with q² transversal blocks meeting
each group once, such that any two points from different groups lie in a unique
block. A field of order q gives TD(q+1,q): blocks have coordinates a+cb for
c in the field, together with the coordinate b. Restrict the group indices to
obtain smaller k. Products of designs give TD(k,qr). Hence a TD(k,q) exists
whenever every maximal prime-power factor pᵉ of q satisfies pᵉ+1 ≥ k.

Idempotent operations satisfying a two-variable law glue over any pairwise
balanced design. On distinct points, use their unique block's operation, and
set x*x=x. Every evaluation involving the original two points stays in their
block, including diagonal subexpressions. Thus the law holds globally.

Keep k full groups and h truncated groups with sizes r₁,…,rₕ ≤ q. Transversal
blocks now have sizes between k and k+h. Fill the groups with models of their
respective sizes, and fill each block with a model of its size. This constructs
an idempotent model of order kq+Σrᵢ.

One may also adjoin a single common point to all groups before filling them.
Fill groups of orders q+1 and rᵢ+1; the transversal blocks do not contain the
new point. This constructs order kq+Σrᵢ+1. Distinct pairs still have a unique
block, so exactly the same gluing proof applies.

The certificate uses only these specializations, in addition to products:

- TD(17,q), block sizes 16 and 17: order 16q+r+e;
- TD(81,q), block sizes 79, 80, and 81: order 79q+r+s+e;

where e is 0 or 1, the relevant group fillings have orders q+e, r+e, and s+e,
and r,s ≤ q. Every dependency in the saved finite construction certificate
has strictly smaller order than the model it constructs.

## Covering a finite interval without large model tables

The certificate records small model constructions, decompositions t=r+s
with both summands among those models, and overlapping intervals of the form

    [79q+254, 79q+h].

Here q has a recorded model and TD(81,q), and every 254≤t≤h has a recorded
split with r,s≤q. Filling the two truncated groups constructs every order in
that interval. The overlapping intervals cover all orders from 107,773 through
10,100,000. They are positive existence certificates; no solver refutation or
unproved exclusion is used anywhere in this argument.

The largest models in an interval may have millions of elements. They do not
need multiplication tables: the transversal construction specifies their
operation from much smaller group and block fillings.

## The induction beyond the finite interval

Write C=107,773 and M=30,030=2·3·5·7·11·13. For n>10,100,000, set

    q=M(floor(n/(17M))+1)+1,     r=n−16q.

Then q≡1 (mod M), so gcd(q,M)=1. We have n<17q and q≤n/17+M+1.
Consequently r≤q and

    r ≥ n/17−16(M+1) ≥ C.

The last inequality follows from
10,100,000 ≥ 17C+272(M+1). Also q≥C, and both q,r are smaller than n.

A TD(17,q) exists directly over Z/q: use the sixteen slopes 0,…,15 and the
vertical coordinate. Differences of distinct slopes are nonzero integers of
absolute value at most 15. All are units modulo q, because their prime factors
belong to {2,3,5,7,11,13}. The usual two linear equations therefore determine a
unique block through any pair of points from different groups.

Strong induction supplies idempotent models at q and r. Fill the sixteen full
groups and the truncated group, using block models of orders 16 and 17. The
result has order 16q+r=n. This completes the construction for every n≥C.

## Reproduction and proof status

`python3 scripts/spectrum_quartic_tail.py --generate` reconstructs the finite
certificate deterministically. `python3 scripts/spectrum_quartic_tail.py`
independently checks the saved certificate, including all scalar polynomial
identities, design-factor conditions, dependencies, sum witnesses, interval
coverage, and the induction threshold. Python checking is research evidence;
it is not substituted for Lean kernel checking.

The generic Lean infrastructure is in `Spectrum/PBD/`, and the two families'
seed interface is in `Spectrum/QuarticTail/Seeds.lean`. The generated finite-basis, sum-splitting, and interval-coverage proofs live
in `Spectrum/QuarticTail/`; `Spectrum/QuarticTail.lean` proves the final tail.
The saved certificate contains 6,272 model constructions, 23,747 sum splits,
and 517 overlapping intervals. Its last endpoint is 10,118,699.

The catalogue includes all positive certificate orders as `quarticTailSeeds`,
proved by `Spectrum.QuarticTail.finite_1076` and `finite_1313`. This exposes
6,201 positive orders below the cutoff as well as the existing fourth-power
family and their products. Regenerate the Lean certificate with
`python3 scripts/spectrum_quartic_tail_lean.py`; add `--check` to verify that
its generated files match the saved certificate without writing them.
