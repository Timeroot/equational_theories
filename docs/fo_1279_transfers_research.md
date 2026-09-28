# Finite FO transfers from E1279: a general-linear obstruction

28 September 2026. This investigation proves that **E1279 cannot finitely
FO-define E63**, and the same argument proves **E1110 cannot finitely
FO-define E63**. These are one-way definability negatives, not just failures
of mutual recovery. They also rule out the corresponding unrestricted FO
transfers and both term-definability transfers.

The originally proposed E1279 transfers to E467, E704, E1110, and E1516
remain unresolved. The new negatives remove some possible routes for
transferring the E63 spectrum exclusions; they do not themselves assert any
new nonexistence of magmas at a particular order.

## The proved symmetry obstruction

Let K be a finite field of characteristic different from two. On V=K²,
consider any scalar-linear source operation

    x*y = a x + b y.

Every invertible K-linear map of V is an automorphism. An operation q
definable without parameters in that source therefore commutes with all
these maps.

Fix e1=(1,0), e2=(0,1), and write q(e1,e2)=(A,B). Transport by invertible
2-by-2 matrices gives, for independent vectors x,y,

    q(x,y) = A x + B y.

The operation need not have this formula on dependent pairs. What is
nevertheless known there is that q sends each coordinate axis into itself:
reflection in that axis fixes its inputs and forces the other output
coordinate to vanish. This step uses characteristic different from two.

Suppose q satisfied E63:

    x = q(y, q(x, q(x,y))).

First B cannot vanish. If B=0, both q(e1,e2) and the next value
q(e1,q(e1,e2)) lie on the first axis. For any t, the first coordinate of
q(e2,(t,0)) is tB: use invertible-matrix transport when t is nonzero, and
axis preservation when it is zero. Thus the final output has first
coordinate zero, contradicting e1.

Since B is nonzero, matrix transport now gives

    q(e1,q(e1,e2)) = (A(1+B), B²).

Here A(1+B) must be nonzero, since otherwise the last application of q has
both inputs on the second axis and cannot equal e1. Applying the transport
formula once more and comparing coordinates gives

    AB(1+B) = 1,        A+B³ = 0.

Eliminating A proves

    B⁵+B⁴+1 = 0.

Consequently, whenever the polynomial has no root in K, no E63 operation
can be first-order definable in a scalar-linear source on K². The polynomial
factors as

    (B²+B+1)(B³-B+1).

No assertion that all equivariant operations are linear is needed or made.

## The two source certificates

Over K=F29, the following two operations satisfy their respective laws:

| Source | Operation on K² | Carrier size |
| --- | --- | ---: |
| E1279 | 4x+11y | 841 |
| E1110 | 6x+28y | 841 |

For E1279, substituting into its right side gives 2640x+609y, which reduces
to x modulo29. For E1110, substitution gives 159936x+1798y, again x.
The E63 polynomial has no root among the29 field elements.

The complete Lean implementation is in
[`GLTwoE63.lean`](../equational_theories/Definability/GLTwoE63.lean) and
[`GLTwoE1279.lean`](../equational_theories/Definability/GLTwoE1279.lean).
The final declarations are:

* `Equation63_not_definableFromFin_Equation1279_glTwo`;
* `Equation63_not_definableFromFin_Equation1110_glTwo`.

The generic declarations are `Definability.GLTwoE63.root_of_definable` and
`Definability.GLTwoE63.not_definableFromFin`. The proof uses explicit
invertible matrices, not an enumeration of automorphisms or operation tables.
All four declarations have checked axiom guards permitting only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorry`, `native_decide`,
or external solver axiom. The finite root check uses ordinary `decide`.

The companion agents apply the same generic theorem to E467 and E704;
see their separate research notes and modules.

## Why this does not settle the four original target transfers

For an equivariant target, let q(x,x)=s x. The coefficient s need not equal
A+B: dependent pairs form different orbits from independent pairs.
On independent vectors, the five-variable-occurrence laws give these
necessary conditions in the nondegenerate cases:

| Target | Conditions |
| --- | --- |
| E467 | AB(1+B)=1, A+B³s=0 |
| E704 | AB²s=1, A+AB+B³=0 |
| E1110 | AB²s=1, A+A²B+B²=0 |
| E1516 | AB(1+B)=1, As+B³=0 |

These leave the extra diagonal parameter s. In particular, absence of an
ordinary linear target operation at a prime order does **not** prove a
finite FO negative. An interpretation could use a nonlinear operation on
one-dimensional subspaces.

At primes29,47, and71, setting s=1 in each row has no solution. Thus this
approach already excludes **idempotent** targets of all four kinds in the
corresponding GL-symmetric sources. This is only a restriction on possible
interpretations, not the requested general one-way negative. The statement
about the four idempotent targets is a paper consequence of the equations
above, not a separate Lean declaration in this pass.

There is an equivalent useful formulation for scalar symmetry on K itself.
Write h(t)=q(1,t) and k=q(0,1). Every homogeneous operation has

    q(x,y)=x h(y/x)  when x≠0,
    q(0,y)=k y.

Thus only |K|+1 values need be searched, rather than a full |K|² table.
The saved search script uses the equivalent constraint that multiplication
by a primitive root is an automorphism. Law instances need be checked only
at (0,0), (0,1), and (1,t). Positive output is independently checked on all
pairs before it is accepted.

The initial bounded searches returned **unknown**, not UNSAT:

* E1516 at29 with scalar symmetry:60-second Z3 timeout.
* E1110 at47 with scalar symmetry, cancellation, and nonzero squaring:
  90-second Z3 timeout.
* E704 at71 with scalar symmetry, cancellation, and nonzero squaring:
  60-second Z3 timeout.

The additional cancellation hypotheses in the second search are legitimate:
E1110 says `L_y R_y L_y D=id`, so D is injective and L_y is surjective;
finiteness makes them bijections and then also makes R_y bijective.
For E704 the same reasoning applies to `L_y² R_y D=id`.
These searches establish no spectrum or definability facts.

## Reproduction

The independent checker expands the five relevant source tables and checks
every law instance. It also scans the scalar polynomial at29,41,47,71,73;
only73 has roots in that list, namely8 and64. Its small saved record is
[`data/definability_fo_1279_transfers.json`](../data/definability_fo_1279_transfers.json).

```sh
python3 scripts/definability_fo_1279_transfers.py
lake build equational_theories.Definability.GLTwoE1279
python3 scripts/definability_fo_1279_transfers.py --search 29 1516 60
python3 scripts/definability_fo_1279_transfers.py --search 47 1110 90 --latin
python3 scripts/definability_fo_1279_transfers.py --search 71 704 60 --latin
```

The search commands are optional explorations; the completed Lean proofs
do not depend on their outcomes.
