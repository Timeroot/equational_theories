# E1483 projectors: a proved subclass and failed stronger conjectures

26 September 2026. Write `P_{a,b}(t)=a*(t*b)` in an E1483 magma.
The general identities

```
P_{a,b}² = P_{a,b},
P_{a,b}(u)=u  implies  P_{a,b}(P_{a,c}(u))=P_{a,c}(u)
```

remain **unproved**. They hold on the six checked tables described below.
Stronger Vampire and Twee searches and bounded SAT countersearches did not
settle their validity in all E1483 magmas. No search timeout is used as a
mathematical assertion.

## Complete constant-row result

Suppose `zero*x=one` for every x. The completed E1483 constant-row theory
supplies the automorphism

```
phi(x) = one*(one*x),       phi³ = id,
B(x,y) = phi²(x)*phi(y).
```

The operation B satisfies E1485. Moreover,

```
B(phi(a), B(t,phi(b))) = a*(t*b).
```

Indeed, expansion of the left side gives
`phi³(a) * phi(phi²(t)*phi²(b)) = a*(t*b)`.
Thus the old projectors are precisely the E1485 projectors with relabeled
parameters. Both displayed identities follow from the already proved E1485
projector theorems.

This argument is complete in
[ConstantProjectors.lean](../equational_theories/Spectrum/Equation1483/ConstantProjectors.lean),
as `Spectrum.E1483.Constant.mixed_idempotent` and
`Spectrum.E1483.Constant.mixed_preserves_fixed`. They require **no finiteness
assumption**, and their only axiom is `propext`.
The constant-row power-of-two spectrum result is in the separate
[ConstantSpectrum.lean](../equational_theories/Spectrum/Equation1483/ConstantSpectrum.lean).

## General cubic twisting

For any operation f with automorphism phi satisfying `phi³=id`, define

```
f'(x,y) = f(phi²(x),phi(y)).
```

If f satisfies E1483, so does f'. Expanding its defining law gives

```
f'(f'(y,x), f'(x,f'(y,z)))
  = f(f(phi(y),x), f(x,f(phi(y),z))) = x.
```

The projectors satisfy

```
P^{f'}_{a,b}(t) = P^f_{phi²(a),phi²(b)}(t).
```

E168 is preserved by the same construction, so cubic twisting cannot produce
a noncentral example from a central one. Applying the twist three times recovers f. These elementary identities are
proved in [CubicTwist.lean](../equational_theories/Spectrum/Equation1483/CubicTwist.lean).
The law-preservation and projector equalities use no axioms.

The saved eight-point constant-row example has an order-three automorphism
`[1,2,0,5,4,7,6,3]` for which the opposite convention
`B(x,y)=f(phi(x),phi²(y))` satisfies E1485. Both saved nine-point examples
already satisfy E168, hence E1485; the newly found rank-two eight-point example
also already satisfies E1485. Consequently these examples do not test the
projector conjectures beyond E1485 and its cubic twists.

**Update, 28 September: the assertion that every E1483 magma admits such an
untwist to E1485 is false.** The [follow-up](1483_fo_untwist_research.md)
gives a Lean-checked 32-element counterexample with automorphism group C2.
The closure theorem above remains valid: it assumes that the original
operation satisfies E1483 and that the required automorphism exists.

## Uniform rank at the square bound forces E168

There is a complete finite rigidity statement even though general rank descent
remains open. Suppose every row has rank r and the carrier has r² elements.
E1483 gives `x -> x*y -> y` in the directed row-image graph: the first edge is
immediate, and the second follows from
`y=(x*y)*(y*(x*x))`. Thus every ordered pair has a two-step path.
For any fixed source there are exactly r² two-step paths, counted with their
intermediate vertex, and r² possible targets. Every target therefore has
exactly one such path. Since `y*x -> x -> x*z` is a two-step path, its unique
intermediate vertex gives

```
(y*x)*(x*z) = x,
```

which is E168. The proof also gives the more general
`central_of_two_step_bound`: at most |G| two-step paths from every source
already forces E168. The uniform-rank statement is formalized as
`Spectrum.E1483.RankRigidity.central_of_uniform_square` in
[RankRigidity.lean](../equational_theories/Spectrum/Equation1483/RankRigidity.lean),
using only the three standard logical axioms. It does not assume the projector
conjectures. In particular, a nine-point E1483 model failing E168 cannot have
all rows of rank three.

## Explicit counterexamples to stronger claims

The [saved data](../data/spectrum/1483_projector_followup.json) include full
multiplication tables and evaluated witnesses for the following failures.

* Same-a projectors need not commute: the saved nine-point minimum-rank-three
  model gives a counterexample at `a=0,b=0,c=3,t=3`.
* They need not commute even on `row(a)`: the new rank-two eight-point model
  gives a counterexample at `a=1,b=0,c=5,t=0`, using the row element `a*t`.
  This model already satisfies E1485, so commutativity of the projectors is
  stronger than either theory's required fixed-point property.
* If `u in row(a)` and `v=P_{a,b}(u)`, neither row-image inclusion nor
  column-image inclusion is generally valid. The opposite of that eight-point
  model refutes column inclusion at `a=1,b=0,u=1`. Since E1483 is self-dual,
  both operation orientations must be tested when proposing such restrictions.

A weaker candidate survives all six tables: if `u in row(a)` and
`P_{a,b}(u) != u`, then the translation rank of `P_{a,b}(u)` is strictly
smaller than that of u. If proved generally for finite models, minimizing
rank in `row(a)` would provide a point fixed by every projector. **This strict
rank-descent statement remains a conjecture**; the failed image-inclusion
claims cannot justify it.

## Reproduction and search limits

```sh
python3 scripts/spectrum_1483_projector_check.py
lake build equational_theories.Spectrum.Equation1483.ConstantProjectors \
  equational_theories.Spectrum.Equation1483.CubicTwist
```

The checker verifies the complete multiplication tables against E1483, each
failed identity, the explicit cubic automorphism and its E1485 untwist, and
the surviving candidate identities on three models and their opposites.
These finite checks do not prove the candidates in general.

The compact SAT countersearch returned UNSAT for both projector identities
at order four. At orders eight and nine each direct query reached 90 seconds;
an order-sixteen idempotence query reached 150 seconds. Three order-eight
idempotence queries with distinguished parameters fixed, and another such
order-sixteen query, each reached 60 seconds. These are exploratory external
results, not Lean refutations. General equational searches used Vampire
portfolio caps of 120–180 seconds and Twee caps up to 300 seconds, including
an encoding with an explicit ternary projector symbol. None settled either
general identity. Searches for the image-inclusion statement were stopped
when its concrete counterexample was identified.

The exact useful inputs and logs are preserved in
[the research archive](../data/spectrum/1483_projector_sources.tar.gz).


Additional searches targeted model families rather than the projector identities.
At order eight, imposing no constant row and failure of E1485 returned UNSAT
in 144.1 seconds. This is an external SAT result, with no Lean certificate in
this pass. At order nine, failure of E168 with no constant or bijective row
reached its 180-second cap. All extra rank exclusions are justified by the
completed constant-row power-of-two theorem. No new positive model was found.

Uniform-rank searches also returned UNSAT for `(order,rank)=(8,3)` in 62.7
seconds and `(8,4)` in 96.6 seconds. The `(9,4)` case reached 120 seconds.
These outcomes remain external search evidence. In particular, it is still
unknown whether a finite E1483 magma can have uniform rank r and order
strictly less than r²; the checked rigidity theorem assumes equality.
