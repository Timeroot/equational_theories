# A pass through all remaining spectrum families

**29 September follow-up:** [strong transversal-block gluing](strong_design_cofiniteness_20260928.md)
with nonidempotent group fillings proves cofiniteness of E677, E1083, and
E1286 in Lean, extending the restricted residue conclusions below.
The required design-existence theorems are now also proved in Lean;
no numerical cutoff has been extracted. The inventory below records the
original 27 September survey.

27 September 2026. The 46 open law entries reduce to 17 problems after the
already proved spectrum equalities and dualities. This pass studies all 17.
The computational record distinguishes checked positive tables, external
finite refutations, and timeouts. None of these categories alone supplies a
Lean theorem. The per-family inventory below covers every open law entry.
The data and search outcomes are saved in
[`data/spectrum/open_survey_20260927.json`](../data/spectrum/open_survey_20260927.json).

## Transferring the explicit Dupont tail

There is a complete constructive argument for a common cofinite bound of
1228 for E467, E704, E1110, E1279, and E1516.

Let p be an idempotent E63 operation on a finite set. Its left translations
are bijections. Put q(x,y)=p(y,p(y,x)); then

    p(x,q(x,y)) = y,       q(x,p(x,y)) = y.

Consequently q(y,q(y,q(x,y)))=x, so q satisfies E73, and
q(y,q(q(y,x),y))=x, so q also satisfies E125. Its opposite operation
r(x,y)=q(y,x) satisfies E118: expanding its defining expression leaves
two consecutive inverse cancellations. Both q and r are idempotent.

Use p for E467 and E1516, q for E704 and E1110, and r for E1279.
In each law the explicit square collapses by idempotence and the remaining
identity is respectively E63, E73, E125, or E118. The existing Lean
construction of idempotent E63 models at every order at least 1228 therefore
supplies all five spectra at those orders. This uses no asymptotic existence
theorem and no new model tables.

Lean: `Spectrum.DupontTwists.models`, `all_large`, and the five `cofinite_*`
theorems in `Spectrum/DupontTwists.lean`. The corresponding five admissions
in `NotePending.lean` are replaced by these proofs. Their duals inherit the
result through the existing spectrum equalities.

## Finite-field and design method

For x*y=ax+by on a finite field, recursively expand the defining equation
and compare each variable's coefficient. An idempotent model has a+b=1;
substituting a=1-b gives one polynomial in b. An irreducible factor of degree
d over F_p supplies a root in F_(p^d), hence a model of that order.

The executable survey checks every pair a,b in every field of order at most
81. Every retained positive model is also checked directly on every instance
of the original equation, independently of the coefficient computation.

Idempotent models glue over a pairwise balanced design: use the block's
operation on two distinct points, and x*x=x. Any two-variable equation is
then evaluated inside a single block. Wilson's PBD theorem says that for a
finite block-size set K, all sufficiently large n satisfying

    gcd{k-1 : k in K} divides n-1,
    gcd{k(k-1) : k in K} divides n(n-1)

admit such a design. Reference: R. M. Wilson, *An existence theory for
pairwise balanced designs III*, J. Combin. Theory Ser. A 18 (1975), 71–79,
https://doi.org/10.1016/0097-3165(75)90067-9.

This is a published mathematical theorem, not currently a Lean dependency.
Conclusions below using it are pen-and-paper proofs with no explicit cutoff.

* E670: block sizes 9, 11, 16 give gcds 1 and 2, hence cofiniteness.
* E1076 and E1313: block sizes 5, 16, 19 give gcds 1 and 2, hence cofiniteness.
  In particular this resolves the note's contradictory cofiniteness claims
  for E1313 on the mathematical level.
* E907: block sizes 3, 13, 23 give gcds 2 and 2, hence every sufficiently
  large odd order. This does not exclude even orders.
* E1083 and E1286: block sizes 7, 9, 16 give gcds 1 and 6, hence every
  sufficiently large order congruent to 0 or 1 modulo 3.
* E677: block sizes 5, 11, 16 give gcds 1 and 10, hence every sufficiently
  large order congruent to 0 or 1 modulo 5.

The congruence restrictions in the last two bullets describe what this
construction supplies, not obstructions to general models. Nonidempotent
finite-field models already occur in other residue classes.

## Uniform fourth-power constructions

E670, E677, E1076, E1083, E1286, and E1313 each have an idempotent model
of every positive fourth-power order. This is an explicit construction over
any commutative ring, with no assumption of a field or an irreducible polynomial.

For f(t)=t^4+c3*t^3+c2*t^2+c1*t+c0, take its companion operator on R^4,

    T(u,v,w,z)=(-c0*z, u-c1*z, v-c2*z, w-c3*z),
    x*y = x + T(y-x).

It is idempotent, and f(T)=0. Expanding each law reduces its coefficients
to multiples of f(T). The required coefficients are:

| Law | c0 | c1 | c2 | c3 |
| --- | ---: | ---: | ---: | ---: |
| 670 | -1 | 1 | 0 | -2 |
| 677 | 1 | -1 | 1 | -1 |
| 1076 | -1 | 1 | -1 | -1 |
| 1083, 1286 | 1 | -1 | 2 | -2 |
| 1313 | -1 | 0 | 2 | -3 |

Taking R=Z/n gives order n^4. The same operation in the fourth row satisfies
both E1083 and E1286, but this does not assert an implication between their
arbitrary models.

All six constructions are proved in `Spectrum/QuarticSeeds.lean`, with
`law_*`, `model_*`, and a common `idempotent` theorem.

Two smaller companion operators give stronger bounds for E1083 and E1110:
both have models of **every positive square order**. For E1083 take
A(u,v)=(-v,u-v), so A^2+A+I=0. For E1110 take A(u,v)=(v,u+v), so
A^2-A-I=0. In either case set x*y=Ax-y. Substitution verifies the respective
law over any commutative ring; R=Z/n gives order n^2. These constructions
are formalized in `Spectrum/QuadraticSeeds.lean`.

The five Dupont transfers also inherit all cube orders from the existing
idempotent cubic construction of E63.

## E907: even abelian-affine models are impossible

This obstruction allows noncommuting endomorphisms. Suppose
x*y=Ax+By+c on a finite abelian group of even order. Passing to the nonzero
vector space H/2H gives the same law in characteristic two. Comparing
coefficients yields

    B(AB+BA)=I,             A+BA^2+B^3=0.

The first equation makes B invertible. Thus AB+BA=B^(-1), and the second
becomes A^2+B^(-1)A+B^2=0. Commuting the latter expression with B, in
characteristic two, gives

    0 = (A^2 B+BA^2) + (B^(-1)AB+A)
      = B^(-3) + B^(-2).

Here the two replacements follow by multiplying AB+BA=B^(-1) by A,
and by B^(-1), respectively. Hence B=I. The first equation then reads
0=I, a contradiction. No even-order affine construction over an abelian
group can work, including with noncommuting coefficients or a constant term.
This is a complete pen-and-paper argument, not yet formalized in Lean.
It is not a nonexistence proof for arbitrary even-order E907 magmas.

## The commutative E907 subclass is exactly Steiner quasigroups

This characterization holds without a finiteness assumption. Write s=a*a
and t=s*s. E907 with x=y=a gives a*t=a. Commutativity and E907 at (t,a)
then give t=a*s. Applying E907 at (s,s) and (a,s) now gives

    s = s*(t*t) = s*((a*s)*(a*s)) = a.

Thus a*a=a. E907 reduces to y*(y*x)=x. Conversely, every commutative
idempotent operation with this involution identity satisfies E907. These
are precisely Steiner quasigroups.

In a nonempty finite model, fix a. The involution x -> a*x has exactly one
fixed point, a: if a*x=x, then x*(x*a)=x*x=x, but the involution identity
also makes this equal a. All other points come in pairs, so the order is
odd. Consequently any even-order counterexample to the E907 parity
conjecture must be both noncommutative and non-affine over an abelian group.

Lean: `Spectrum.E907.commutative_iff` proves the unrestricted characterization
without axioms; `Spectrum.E907.odd_order` proves the finite parity consequence
with only standard axioms. The abelian-affine obstruction remains a paper proof.

## Why idempotent design gluing cannot solve E1483 or E1486

Both laws have only trivial idempotent models, even on infinite carriers.
For E1483 write multiplication as p, and assume p(x,x)=x. Substitutions
in the law give

    p(x,p(x,p(x,y))) = x,
    p(p(x,p(x,y)),p(x,y)) = p(x,y).

Apply the second identity with y replaced by p(x,y), and use the first:
this gives p(x,p(x,y))=x. Substituting this back into the second gives
p(x,y)=x. E1483 now reduces to x=y. If E1486 is idempotent, substituting
z=y*z in it gives E1483, so the same conclusion follows.

Vampire found these short equational refutations; they were then reconstructed
as direct Lean proofs. Thus the idempotent PBD strategy used elsewhere in this
survey cannot yield nontrivial models of either central-groupoid weakening.

Lean: `Spectrum.WeakCentralIdempotent.collapse1483` and `collapse1486`.
Neither theorem depends on any axioms.

## Per-family inventory

Each row received both a finite-field search and a bounded unrestricted
finite-domain search. The latter used Z3 with a 15-second limit per case.
Its only normalization was a relabeling that makes 0*0 either 0 or 1; no
Latin, commutativity, or idempotence assumption was imposed. A timeout gives
no exclusion. External UNSAT results have not been replayed in Lean and
are deliberately not added to the catalogue's proved exclusions.

| Family | Attempt and result | Small-order search |
| --- | --- | --- |
| E63, E73, E118, E125, E1692 | Rechecked field constructions and product possibilities against the seven unresolved orders. None of the field models fills a gap in the existing cofinite construction. | 18: timeout. |
| E467 | Completed the explicit Dupont transfer: every order at least 1228, and every cube, in Lean. | 10: timeout. |
| E667 | Checked the field coefficients and their cubic/quadratic factors; the resulting field orders do not improve the existing 35-order open list. | 12: timeout. |
| E670 | Idempotent fourth powers in Lean; field seeds 9,11,16 complete the previously missing Wilson cofiniteness argument on paper. | 8: timeout. |
| E677 | Idempotent fourth powers in Lean; Wilson gives the eventual 0,1 mod 5 residue classes. The other classes still obstruct this approach to full cofiniteness. | 3 and 4: external UNSAT; 6: timeout. |
| E704 | Completed the explicit Dupont left-division transfer: every order at least 1228, and every cube, in Lean. | 10: timeout. |
| E883, E1323, E1526 | Checked field coefficients and their cubic/quartic factors; no improvement to the existing 43-order open list. | 12: timeout. |
| E907 | Every sufficiently large odd order by Wilson, on paper. Commutative models are exactly Steiner quasigroups, and finite nonempty ones have odd order, proved in Lean. Even abelian-affine models are also impossible, by a separate paper argument allowing noncommuting coefficients. | 8 and 10: timeouts. |
| E1076 | Idempotent fourth powers in Lean; field seeds 5,16,19 complete the previously missing Wilson cofiniteness argument on paper. | 8: timeout; a further 20-second search using the known finite idempotence consequence also timed out. |
| E1083 | All square orders in Lean, plus idempotent fourth powers. Wilson gives eventual orders 0,1 mod 3. | 5 and 6: external UNSAT. |
| E1110 | All square orders in Lean, using the Fibonacci operator; every order at least 1228 and every cube by the Dupont transfer. | 10: timeout. |
| E1279 | Completed the opposite-left-division Dupont transfer: every order at least 1228, and every cube, in Lean. | 10: timeout. |
| E1286 | Idempotent fourth powers in Lean; Wilson gives eventual orders 0,1 mod 3. Explicit field models include 9 and 11, beyond the note's short initial list. | 8: timeout. |
| E1313 | Idempotent fourth powers in Lean; field seeds 5,16,19 prove cofiniteness on paper, resolving the source conflict. | 8: timeout. |
| E1483 | Proved in Lean that idempotence forces triviality, without finiteness. The scalar-field attempt has no nontrivial solutions, consistently with the prior stronger group-affine obstruction. | 12: timeout. |
| E1486 | Proved in Lean that idempotence forces triviality, without finiteness. Scalar-field attempts have no solutions; existing graph/matching constructions remain the useful general method. | 10: timeout. |
| E1516 | Completed the explicit Dupont transfer: every order at least 1228, and every cube, in Lean. The field and SMT runs both supplied a model of order 9. | 9: SAT, independently checked table retained. |

The first row covers ten laws including duals; the E883 row covers six; each
other row covers its law and its dual. Thus every one of the 46 open laws
is covered. **No further exact spectrum was completed in this pass.**

## Reproducibility and next obstacles

Run the field pass with:

```sh
python3 scripts/spectrum_open_survey.py --field-bound 81 --output /tmp/fields.json
```

For a bounded search, for example:

```sh
python3 scripts/spectrum_open_survey.py --search 907 8 --seconds 15 --output /tmp/e907-8.json
```

The script checks the original equations directly on every positive table.
The combined record stores all field coefficients, covered law IDs, search
statuses, and the two Vampire inputs/proofs. The new Lean constructions use
only standard axioms; the central idempotence proofs use none. Wilson's
theorem is not formalized here. The E670/E1076/E1313 cofiniteness declarations
therefore retain explicit `proofAvailable` obligations, rather than being
marked complete. E677's full cofiniteness still has an unreconstructed gap.

The most attractive next structural question from this pass is whether
**every finite E907 magma has odd order**. The affine obstruction above does
not settle it, and bounded searches at 8 and 10 did not settle those orders.
For the finite-cofinite problems, small primitive orders such as E1286 at 8,
E670 at 8, and E667/E883 at 12 still require new constructions or
refutations. The same short failed search should not simply be repeated.

Validation completed: the full Spectrum build, the all-4694-law catalogue
audit, and generated-file consistency checks passed. All 348 retained
finite-field witnesses and their product closures reproduced exactly.
The catalogue has 4648 proved exact spectra and 46 open exact spectra;
cofiniteness and lower-bound improvements do not change that exact count.

## E907 follow-up: inverse-translation search, 28 September

For fixed y, E907 expresses every x as y multiplied by another element.
Thus every left translation L_y is surjective, and on a finite carrier it
is a permutation. The original law is equivalent to

    (y*x)*(x*y) = L_y⁻¹(x).

The new search script encodes each row together with its inverse using
CP-SAT's inverse constraint. It assumes no right cancellation. A regression
run at order 7 reproduced a model and checked the original equation on
every pair. With four workers and a 120-second limit, the idempotent
order-8 case returned `INFEASIBLE` in 22.34 seconds; the unrestricted case
returned `UNKNOWN` at the time limit. The former is an external computation,
not a Lean certificate; the latter leaves general order 8 open.

The solver version, script hash, full positive table, and search statistics
are saved in `data/spectrum/907_inverse_followup.json`. To reproduce:

```sh
python3 scripts/spectrum_907_inverse_search.py 7 --seconds 10
python3 scripts/spectrum_907_inverse_search.py 8 --seconds 120 --idempotent
python3 scripts/spectrum_907_inverse_search.py 8 --seconds 120
```
