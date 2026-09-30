# E1483: rectangular fibers and a limit on permutation constructions

30 September 2026. **The general spectrum is still open.** This pass proves a
new obstruction to obtaining additional orders from the existing permutation
constructions. The obstruction is formalized in Lean, without admissions.
It applies to arbitrarily large finite fibers, not merely the examples searched.

Write E1483 as

\[
                 (y*x)*(x*(y*z))=x.
\]

The known positive orders remain all squares and twice squares. This note does
not assert that these exhaust the spectrum.

## 1. Every subalgebra has rectangular fibers

Consider the permutation extension of an E1483 base \((G,f)\):

\[
 (x,u,v)*(y,s,t)
       =\bigl(f(x,y),B_{xy}^{-1}(v),A_{xy}(s)\bigr),
\]

where the coefficient permutations satisfy the cancellation conditions in
[the construction note](1483_general_constructions.md). Let \(H\) be any
subalgebra. Its projection \(K\) to \(G\) is a subalgebra too. Write

\[
 U_x=\{u:\exists v,\ (x,u,v)\in H\},\qquad
 V_x=\{v:\exists u,\ (x,u,v)\in H\}.
\]

**The fiber over \(x\) is exactly \(U_x\times V_x\).** This does not require
finiteness. To splice \((x,u,v')\) and \((x,u',v)\), choose points \(Y,Z\in H\)
and form

\[
                  (Y*(x,u,v'))*((x,u',v)*(Y*Z)).
\]

The first inner factor depends on \(u\), and the second on \(v\). Thus this
is the same expression as the E1483 word applied to \((x,u,v)\), and equals
\((x,u,v)\). Every point used in forming the expression belongs to \(H\).
One can take both \(Y\) and \(Z\) to be the first given point, so there is
no extra nonemptiness hypothesis.

For finite fibers put \(u_x=|U_x|\), \(v_x=|V_x|\). Closure and injectivity of
the coefficient permutations give

\[
                  v_x\le u_{f(x,y)},\qquad u_y\le v_{f(x,y)}.
\]

Both inequalities are equalities. For the second, apply the first to
\((f(x,y),f(y,f(x,z)))\), whose product is \(y\), obtaining the reverse
inequality \(v_{f(x,y)}\le u_y\). For the first, use the dual E1483 identity

\[
                  f(f(f(z,y),x),f(x,y))=x
\]

in the same way. Hence

\[
                  u_{f(x,y)}=v_x,\qquad v_{f(x,y)}=u_y.       \tag{1}
\]

In particular the coordinate sizes themselves define a homomorphism into a
natural central groupoid. This is stronger than just counting the full cover.

Lean: `PermutationCover.splice`, `subalgebraEquiv`, and `fiber_sizes` in
[PermutationSubalgebra.lean](../equational_theories/Spectrum/Equation1483/PermutationSubalgebra.lean).

## 2. All permutations can be removed for the cardinality question

Replace each \(U_x,V_x\) by the initial segments of the same sizes inside
\(\{0,\ldots,|S|-1\}\). The resulting set is

\[
 H_0=\{(x,i,j): x\in K,\ i<u_x,\ j<v_x\}.
\]

Equation (1) makes it closed under the **plain** operation

\[
                 (x,i,j)\mathbin{\circ}(y,k,l)=(f(x,y),j,k).
\]

Also \(|H_0|=\sum_{x\in K}u_xv_x=|H|\). This proves:

> Every finite subalgebra of a permutation cover has the same cardinality as
> a subalgebra of the unpermuted direct product, with the same base and fiber
> size.

Consequently varying these permutations, even over noncommuting permutation
groups, cannot enlarge the set of subalgebra orders available from the plain
construction. It can change the algebra and its automorphism group substantially;
the existing 32-element obstruction to cubic untwisting remains valid.

If the base also satisfies E1485, the plain product and its subalgebra do too.
The completed E1485 spectrum theorem therefore restricts \(|H|\) to a square
or twice a square. This conclusion does not claim that the original twisted
operation satisfies E1485.

Lean: `shadow_closed`, `shadow_card`, `exists_plain_subalgebra`, and
`subalgebra_card_of_1485_base` in
[PermutationShadow.lean](../equational_theories/Spectrum/Equation1483/PermutationShadow.lean).

This is a statement about cardinalities. Arbitrarily re-enumerating coordinate
sets does **not** establish an automorphism-invariant construction, so it does
not settle the general finite FO-definability comparison with E1485.

## 3. A constant row in the projection forces square fibers

Suppose the projected subalgebra \(K\) has a constant row, say \(f(0,y)=1\).
Equation (1) gives \(u_y=v_1\) for every \(y\in K\); applying its other half
shows that all the \(v_y\) have the same value as well. Thus every fiber is
an \(s\)-by-\(s\) rectangle. The existing constant-row theorem gives
\(|K|=2^k\), so

\[
                              |H|=2^k s^2.
\]

This is a square or twice a square. The argument is formalized as
`card_of_constant_base` and `square_or_twice_square_of_constant_base`.

The cubic Boolean base used in the earlier 32-element examples has exactly
five nonempty subalgebras: three singleton idempotents, its two-point NAND
subalgebra, and the entire eight-point base. Each has a constant row. Lean
checks the required constant-row statement for all 256 Boolean membership
functions on the base, then applies the general theorem. Therefore:

> No subalgebra of any finite permutation cover of this eight-point base can
> have an order outside the squares and twice squares.

The coefficient permutations and their degree are unrestricted. This replaces
a previously open-ended search through subalgebras with a general obstruction.
See `CubicBaseSubalgebras.subalgebra_square_or_twice_square` in
[CubicBaseSubalgebras.lean](../equational_theories/Spectrum/Equation1483/CubicBaseSubalgebras.lean).

A further [complete pen-and-paper argument](1483_permutation_cover_definability.md)
proves more for constant-row bases: their finite permutation covers, and
subalgebras with constant-row projection, admit parameter-free FO-definable
E1485 companions. It recovers the base fibers from minimum row rank and uses
an equivariant coordinate change. That general definability argument is awaiting
Lean formalization; the cardinality theorems above are already complete.

## 4. The surviving identities are built into this family

For a fixed finite base, attach one formal generator to each of the 27
coefficient components. A coordinate of any term in the extension is an input
coordinate followed by a word in these generators and their inverses. Adjacent
inverse pairs cancel for arbitrary permutations, regardless of the fiber size.

The symbolic checker verifies the following identities for every permutation
cover of the eight-point base:

* E1483 itself: 512 assignments of base values.
* \(P_{a,b}^2=P_{a,b}\), where \(P_{a,b}(t)=a*(t*b)\): 512 assignments.
* \(P_{a,b}P_{a,c}P_{a,b}=P_{a,c}P_{a,b}\): 4,096 assignments.
* \(d^3=d\), where \(d(x)=x*x\): eight assignments.

For each assignment the source variable, source coordinate, and freely reduced
permutation word agree on both sides. This is a finite symbolic certificate
for **all** permutation choices, not a finite sample of small permutations.
These symbolic identity certificates have not been replayed in Lean and are
not used in the Lean cardinality theorems above.

Thus the earlier successful projector tests on many covers were constrained by
the construction itself. Such covers cannot supply counterexamples to these
three general conjectures. Their validity for arbitrary E1483 magmas remains
unproved.

A different proposed approach through semigroups fails already on the saved
32-element model. For an edge \(a\to b\), the operation
\(x\mathbin{\diamond}y=(a*x)*(y*b)\) is idempotent by E1483, but need not
be associative. In the first saved cover, take \(a=4,b=30\), with
\(4*0=30\). Then
\[
 (0\mathbin{\diamond}16)\mathbin{\diamond}4=23,
 \qquad 0\mathbin{\diamond}(16\mathbin{\diamond}4)=21.
\]
The checker verifies these table entries directly. Thus a general reduction
to associative idempotent semigroups via these coordinates is unavailable.

## 5. Computational follow-up and its limits

The saved research record distinguishes exhaustive finite calculations,
symbolic certificates, and inconclusive solver runs. Full subalgebra and
congruence lattices were enumerated for the three saved 32-element examples
and deterministic random covers at orders 32, 72, and 128: 38 covers in all,
with 932 subalgebras including the empty subset of each cover. No new spectrum
order was obtained. The faster checker independently recovers all subalgebras
by transporting subsets along the coefficient graph: the remaining consistency
conditions say that a subset is a union of permutation-group orbits.

These computations do not classify quotients of arbitrary covers. The general
Lean obstruction above concerns subalgebras, not all homomorphic images.

Three 600-second Vampire runs targeted the general sharp-edge dual identity,
projector idempotence, and the rank-descent collapse implication. All timed
out without proofs. The archived inputs include only E1483 and proved
consequences, not the unproved conjectures as extra assumptions.

Order twelve remains the first undecided positive order after the externally
excluded eleven. The previous pass left minimum ranks 3, 4, and 5. New searches
add the exact equality between row adjacency and transposed column adjacency,
and the directed-triangle identities: if \(a\to b\), then

\[
                    (b*a)*b=a,\qquad a*(b*a)=b.
\]

Both follow from the already formalized dual identity and translation
regularity. The searches are exploratory; a timeout is not an exclusion.
The minimum-rank-five case returned UNSAT within its 1,200-second budget,
leaving only minimum ranks 3 and 4 from the previous partition. This is a new
partial external exclusion, not a complete order-twelve exclusion and not yet
a Lean certificate. The minimum-rank-three and minimum-rank-four runs both
reached their 1,200-second budgets without a result. All these runs have finished.
Final outcomes and budgets are recorded separately in the accompanying JSON.

## Reproduction and proof status

```sh
python3 scripts/spectrum_1483_subalgebras.py
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
```

The three new Lean modules contain no sorries and have explicit axiom guards.
Their main cardinality theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. The eight-point calculation uses kernel reduction. The full
spectrum build includes the new modules.

The source archive linked by
[the research record](../data/spectrum/1483_subalgebra_research_20260930.json)
preserves the slower independent lattice enumeration, exact search inputs,
and solver outputs. It is research provenance, not a Lean UNSAT certificate.

Final validation: the full spectrum build passed (3,989 jobs), the catalogue
audit checked all 4,694 laws, and the generated catalogue files are current.
The research checker verified all 932 subalgebras independently through the
coordinate transport graph, all symbolic identities, and the archive hashes.
