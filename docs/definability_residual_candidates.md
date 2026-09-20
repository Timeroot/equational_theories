# Residual candidate families: 18 September 2026

The initial pass certifies four exclusions of restricted families of defining terms.
A follow-up also excludes every commutative binary term for E3342 and E3545.
A subsequent [subalgebra certificate](definability_subsets.md) completes the
E3352 → E4408 term-structural obstruction, reducing the completely-open
inventory to **32 raw pairs / 9 class rows**.

The later [translation-rank and constant-row results](definability_1483_rank_constraints.md)
give additional kernel-checked constraints for the E1483 searches. In particular,
a nontrivial finite E1483 magma with a constant row has even order and a number
of idempotents divisible by three.

The resumed 03:45–04:45 UTC research hour added the candidate counterexample,
central specialization, translation-image equivalence, Bolan companion tables,
and corrected SAT results below. It closed no additional row.

The later 14:10–15:10 UTC pass added the constant-row arithmetic and rank
bounds, six companions with identical compatible binary relations, and a
reproducible E1483 order-eleven search. That search now leaves only minimum
row ranks three and four unresolved; its exclusions are exploratory SAT
results, not Lean refutations. No additional definability row is closed.

The [saved models](../data/definability_residual_models.json) and
[independent checker](../scripts/definability_residual_check.py) reproduce the
finite calculations without the older external search bank. The two Lean
exclusion certificates prove the infinite-family statements below by ordinary kernel
checking. All four conclusion guards list only `propext` and `Quot.sound`.

## Arbitrarily many square iterations

Write `q(x) = x ◇ x`. Consider every operation of the form

\[
 x \mathbin{\Box} y = q^a\bigl(q^b(x)\mathbin{\diamond}q^c(y)\bigr),
 \qquad a,b,c\in\mathbb N.
\]

The exponents are unrestricted, and exponent zero means the identity function.
[The square-family certificate](../scripts/check_definability_square_candidates.lean)
proves that none of these operations realizes the indicated target on these
source models:

| Source | Target | Model order | Distinct powers of `q` | Finite cases |
|---:|---:|---:|---:|---:|
| E3342 | E4405 | 8 | 5 | 125 |
| E3545 | E4405 | 8 | 5 | 125 |
| E3352 | E4408 | 7 | 6 | 216 |

On the first two models, `q⁵ = q`. Their phase transition is
`0 → 1 → 2 → 3 → 4 → 1`. On the third model, `q⁶ = id`, so the six
phases form a cycle. Lean checks the transitions and proves by induction that
every natural-number exponent reduces to a listed phase. It then checks every
triple of phases against the target equation.

In particular, `q(q(x) ◇ q(y))` fails for both E3342 and E3545. This candidate
had passed all 400 and 411 models, respectively, in the older search bank.
New countermodels were necessary to detect the failure.

## Arbitrary unary postprocessing for E3352

[The unary certificate](../scripts/check_definability_unary_candidates.lean)
uses a different eight-element E3352 model. It proves that for **every unary
magma term** `u`, the operation

\[
 x \mathbin{\Box} y = u(x\mathbin{\diamond}y)
\]

fails E4408 on this model. There is no bound on the size or depth of `u`.

The Python checker exhausts the unary term closure and finds exactly 32 distinct
functions. The Lean proof checks that this family contains the identity and is
closed under pointwise source multiplication. Induction on `FreeMagma Unit`
therefore places every unary term in the family. All 32 resulting postprocessed
products fail E4408. The finite closure proof is sufficient for the exclusion;
it does not rely on the external solver that originally found the model.

The model arose after two unary candidates survived the older finite bank.
Fresh counterexample searches rejected both. Exhausting the new model's unary
closure then ruled out the entire postprocessing strategy on that model.

## Initial unary-recovery obstruction: E3352 → E4408

The initial recovery search produced stronger solver evidence. Its original
four-family formulation below remains an exploratory check; the simpler
[subalgebra argument](definability_subsets.md) now proves the whole-row
term-structural refutation in Lean. The
[saved constraints](../data/definability_unary_recovery_3352.json) replay with
[the recovery checker](../scripts/definability_unary_recovery_check.py).

On the same eight-element E3352 model used above, a hypothetical
term-structural companion must satisfy E4408, obey the source's compatible
relations, and have exactly the same idempotents. It must also recover all
source unary term operations.

The search found four proper families of unary functions, of sizes
**5, 20, 28, and 5**. Each contains the identity function; the source operation
fails to keep each family closed under pointwise multiplication. Consequently,
any target operation that keeps one of these families closed cannot recover
the source operation by a term.

Z3 reports `unsat` when required to satisfy E4408, the exact idempotent
condition, 22 necessary forward restrictions, and break closure of all four
families. The standalone checker independently verifies the source law, each
forward relation's closure and its two generating tuples, and each reverse
family's identity member and failure of source closure. It then rebuilds the
solver problem from the saved data and again obtains `unsat`. The 22 forward
restrictions use only five distinct binary relations: the graphs of an
order-three automorphism and its inverse, two graphs of partial maps on a
four-element subalgebra, and one 18-element relation. This gives a smaller
starting point for a relation-based Lean coverage proof.

Concretely, the automorphism is `(0 7 1)`, fixing the other five elements.
The partial maps have domain `{2,4,5,6}` and respective value lists
`[5,6,5,6]` and `[6,5,5,6]`. The remaining relation is simply
`G × {5,6} ∪ {3} × {2,4}`. The requirement that the target have no extra
idempotents is essential to this particular four-family coverage: dropping it
from the replay gives `sat`.

The later proof replaces these families with two ordinary subsets and adds
a sixth compatible binary relation. Its finite coverage theorem and recovery
argument remove the four raw pairs in `{3352,4164} → {4408,4479}` from the
completely-open inventory. See [the completed proof](definability_subsets.md).

```sh
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_unary_recovery_check.py --seconds 120
```

This command requires the `z3-solver` Python package. A timeout prints `unknown`
and is not an impossibility result.

## No commutative binary term for E3342 or E3545

The [commutativity certificate](../scripts/check_definability_commutative_obstruction.lean)
gives a separate eight-element model of each source law with the automorphism
`σ = (0 1)(2 3)(4 5)(6 7)`. The
[saved tables](../data/definability_commutative_obstructions.json) satisfy their
source laws and commute with `σ`; the residual checker reproduces these facts
and checks that its tables match Lean.

Every binary source term `t` satisfies
`t(σx,σy) = σ(t(x,y))`. If `t` were commutative, then
`σ(t(0,1)) = t(1,0) = t(0,1)`, contradicting the absence of fixed points of `σ`.
Lean proves this for arbitrary term-defined operations, without a size or depth
bound. Both conclusion guards list only `propext`, `Classical.choice`, and
`Quot.sound`.

Every commutative operation satisfies E4405, so this rules out a broad strategy
for the two E4405 rows. It does not settle those rows: E4405 also permits
noncommutative operations. Symmetric constructions that passed the older bank
were rejected by fresh eight-element models before this general obstruction
was found.

## Mutual term recovery on an E3342 fiber family

The [fiber certificate](../scripts/check_definability_fiber_recovery.lean)
proves a positive result for a specific family, so this family cannot witness
an E3342 → E4405 term-structural obstruction. Let `A` be any additive
commutative group and choose any `e ∈ A`. On `Z/3 × A`, both operations have
first coordinate `1 − a − b`. Their second coordinates, for inputs `(a,u)`
and `(b,v)`, are:

| `b − a` modulo 3 | Source `◇` | Target `□` |
|---:|---|---|
| 0 | `0` | `0` |
| 1 | `u − v + e` | `−u − v + e` |
| 2 | `−u + v` | `−v + e` |

The source satisfies E3342 and the target satisfies E4405. Explicit terms
with **19 leaves forward and 13 leaves backward** define each operation from
the other. The terms contain only the two variables and the relevant magma
operation; they do not use group operations, parameters, or coordinates as
extra term symbols. The statement covers finite and infinite groups and all
choices of `e`. Lean packages the result as `TermStructuralOnMagma` and checks
its axiom guard against `propext`, `Classical.choice`, and `Quot.sound`.

[The saved terms](../data/definability_fiber_recovery.json) also pass an
[independent checker](../scripts/definability_fiber_check.py), which computes
integer coefficient vectors separately for all nine base-coordinate pairs.
Lean caught a sign convention error in the initial exploratory composition
routine; the corrected search output is what both checks now certify.

This is not a general solution of E3342 → E4405. In particular, the forward
term fails E4405 on the saved eight-element E3342 model above, with 51 failing
assignments. The family result adds no fact to the board.

The same certificate now gives an E3545 companion of this source family.
Its second coordinate is `0`, `u − v + 2e`, or `−u + v + e`, respectively,
in the three rows of the table above. A **10-leaf forward term and 24-leaf
backward term** give mutual recovery; they are saved
[separately](../data/definability_fiber_3545_recovery.json) and checked by the
same Python command. Lean packages this as `termStructural3545`, with the
same ordinary axiom guard. The forward term passes 398 of the 400 older
E3342 models but fails bank indices 398 and 399 and the newer eight-element
model. It therefore also remains a family result, not a board fact.

The same Lean certificate now proves that the twists `x ◇ (x ◇ x)` in the
source and `(x □ x) □ x` in its E3545 companion both send `(a,u)` to
`(a,u+e)`. Their orders are therefore unbounded, even on finite carriers.
Taking `A = Z/5` and `e = 1` gives 15-element counterexamples to the proposed
identity `σ⁷ = σ`; taking `A = Z` gives a twist of infinite order. The two
translation formulas have ordinary axiom guards. The small model bank's
observed twist orders one, two, and three do not give a general period bound.

```sh
python3 scripts/definability_fiber_check.py
lake env lean scripts/check_definability_fiber_recovery.lean
```

## Counterexample to idempotent-adjacency transitivity

For idempotents `a,b`, consider the proposed relation
`(a ◇ b) ◇ (a ◇ b) = b ◇ a` and
`(b ◇ a) ◇ (b ◇ a) = a ◇ b`. This relation is **not transitive** under
E1483. The [saved nine-element model](../data/definability_1483_adjacency_counterexample.json)
has idempotents `0,1,2`, with `0` related to `1` and `1` related to `2`,
but `0` unrelated to `2`. It even satisfies the stronger central-groupoid
identities E167 and E168.

The [Lean certificate](../scripts/check_definability_1483_adjacency.lean)
checks the source laws and the failed transitivity by `decide`; its axiom
guard lists only `propext`. The independent residual checker verifies the
same facts and the exact correspondence of the saved and certified tables.
This rules out a proposed structural proof route, not a definability row.

## A ten-leaf E1483 → E1479 candidate

With `q(x) = x ◇ x`, circuit synthesis found the candidate

```
g(x,y) = ((x ◇ y) ◇ q(y)) ◇ (q(x) ◇ (x ◇ (q(y) ◇ x))).
```

The [saved term and model bank](../data/definability_1483_term_candidate.json)
pass an [independent checker](../scripts/definability_central_candidate_check.py):
the derived operation satisfies E1479 on all 29 saved E1483 models. Their
orders are 1 (one model), 2 (two), 4 (24), 8 (one), and 9 (one). The last is
the adjacency counterexample above. Earlier synthesized candidates failed
on that nine-element model; the refined ten-leaf candidate passes it.

This is **an unproved candidate**, not a positive board fact. Initial fresh
countermodel searches and equational prover attempts reached their limits.
In particular, the factored propositional searches at orders 8, 9, and 12
each timed out after 150 seconds; none returned a satisfiability result.
The checker can emit the universal TPTP conjecture and run a fresh Z3 search;
the latter allows both equal and distinct counterexample inputs.

A [Lean certificate](../scripts/check_definability_central_candidate.lean)
now proves that, under the stronger central-groupoid identity E168, this
term equals `y ◇ x` and satisfies E1479. Both proofs use no axioms.
This explains its success on that family without proving E1483 → E1479.
Proof-guided circuit searches using short consequences of E1483 still
reached their limits without a universal proof.
A later run using 90 completion rules also found no proof after 420
seconds. Twee and Vampire searches supplied with those consequences
reached their 350- and 340-second limits. A separate diagonal conjecture
reached Twee's critical-pair limit, and an idempotent-second-input
conjecture timed out after 140 seconds. None establishes a counterexample
or a universal identity for the candidate.

The checker also has a CaDiCaL backend with factored source and dual-law
constraints. An initial output-precedence symmetry restriction was found
to be too strong on multiplication tables and removed; results from that
version are discarded. The corrected restriction applies only to the first
row and accounts for labels already used as inputs as well as outputs.
Finite solver outcomes remain exploratory evidence, not Lean certificates.
With the corrected encoding and a 180-second limit per witness type,
orders 8 and 9 returned UNSAT for equal inputs and UNKNOWN for distinct
inputs. A subsequent order-eight search split distinct witnesses into
four cases according to the idempotency of each input. **All four cases
returned UNSAT**, with a 250-second limit per case. Together with the equal-input
result, this excludes order-eight countermodels according to the corrected
SAT encoding. Order nine required longer searches. The maintained partition
encoding was checked to produce exactly the same clauses as these four runs.
At order nine, a final 65-second run per partition returned UNSAT when both
inputs are idempotent (case 3) and UNKNOWN in the other three cases.
Ten small checks of the backend, using five terms and both witness
types, agreed with exhaustive enumeration of all order-two operations.

During the twelve-hour pass, all four distinct-input partitions at order nine
returned UNSAT, with up to four hours allowed per case. Together with the
earlier equal-input result, this excludes order-nine countermodels according
to the corrected SAT encoding. These runs have no Lean-checked LRAT
certificates and do not prove the candidate universally. Four longer
order-twelve searches are in progress.

```sh
python3 scripts/definability_central_candidate_check.py --tptp /tmp/central-candidate.p
python3 scripts/definability_central_candidate_check.py --countermodel-order 9 --seconds 90
python3 scripts/definability_central_candidate_check.py --solver cadical --countermodel-order 9 --seconds 180
# Repeat for cases 0, 1, 2, and 3; this covers distinct inputs only.
python3 scripts/definability_central_candidate_check.py --solver cadical --countermodel-order 8 --seconds 250 --idempotent-case 0
lake env lean scripts/check_definability_central_candidate.lean
```

## A rejected 22-leaf E3342 → E3545 candidate

Let `u = y ◇ x`, `a = (y ◇ y) ◇ (x ◇ x)`, and
`b = (x ◇ x) ◇ (y ◇ y)`. The candidate

```
g(x,y) = ((((u ◇ a) ◇ a) ◇ b) ◇ b) ◇ (u ◇ u)
```

passed 400 older source models and 13 additional checks. A fresh
[eight-element countermodel](../data/definability_3342_candidate_counterexample.json)
refutes E3545 for its derived operation at `x = 2, y = 3`. The
[Lean certificate](../scripts/check_definability_3342_candidate.lean)
checks E3342 and the counterexample by `decide`, with only `propext`
in the counterexample's axiom guard. The independent residual checker
evaluates the saved term and checks the same witness and table.

The opposite source operation satisfies E3545 on this model, as Lean also
verifies. Thus the counterexample rejects this particular term and cannot
serve as a general term-recovery obstruction. Further synthesis using the
new countermodels reached its limits without a replacement candidate.

## Recovery constraints on the Bolan models

The previously certified E1486 models of orders 11 and 13 were added to
the search. For each carrier, target operations satisfying E1479 and
E1480 survived **every one- and two-position term-interpolation constraint**
and have exactly the same subalgebras as the source. The four
[saved target tables](../data/definability_bolan_recovery_candidates.json)
are checked independently by
[the Bolan checker](../scripts/definability_bolan_recovery_check.py).
It recomputes the relevant generated relations in the source square:
2,025 proper relations at order 11 and 670 at order 13. It also checks
all carrier subsets for closure, not just selected subsets.

These targets are not known to be source terms, and no reverse term is
known. They show that these particular necessary conditions cannot refute
the four companions. Searches for E1483 companions on the same two models
timed out after 400 seconds each. Unary-term enumeration exceeded 200,000
operations on each source, so that enumeration supplies no complete closure.

```sh
python3 scripts/definability_bolan_recovery_check.py
lake env lean scripts/check_definability_3342_candidate.lean
```

## Limits of the remaining searches

A further recovery pass found six
[finite companions](../data/definability_binary_recovery_candidates.json)
with exactly the same compatible binary relations as their sources:
E1486 → E1479 at order 11, E1486 → E1480 at order 13, and all four
remaining E3342/E3545 directions at order 12. The
[independent checker](../scripts/definability_binary_recovery_check.py)
recomputes every two-position interpolation constraint in both directions,
and also checks all carrier subsets. These companions are not known to be
terms and do not establish mutual term recovery. One E3545 → E3342 search
needed twelve additional reverse-relation constraints before finding its
companion. The larger scan tested 72 new sources at orders 10, 11, and 12;
all 144 target searches passed the weaker forward-relation and subalgebra
conditions.

```sh
python3 scripts/definability_binary_recovery_check.py
```

The restricted-family certificates alone leave general binary terms available.
The subsequent subalgebra theorem excludes mutual term recovery for E3352 →
E4408, while one-way term definability and first-order definitions remain open.

Other searches in this pass were inconclusive:

- Several searches reached a cap of 1,500,000 distinct finite-model term
  signatures without a valid universal candidate. The cap is not a refutation.
- On the 32-element twisted E1485 model, four cases fixing the two- and
  four-element restrictions reached their solver limits. Both the earlier
  equality-based encoding and a smaller propositional encoding were tried.
  No E1483 target or impossibility certificate resulted.
- A stronger E1485 mutual-recovery search added 175 source-compatible binary
  relations, generation of the whole target by source idempotents `11,21`,
  and the dual E1483 law `((z ◇ y) ◇ x) ◇ (x ◇ y) = x`.
  The [dual-law certificate](../scripts/check_definability_1483_dual.lean)
  derives that identity from two instances of E1483, with no axioms.
  It also proves `x ◇ ((x ◇ y) ◇ x) = x ◇ y` and
  `(x ◇ (y ◇ x)) ◇ x = y ◇ x`, again without axioms. These give
  mutual inverse restrictions of left and right translation to their images.
  `translationImageEquiv` packages those restrictions as an explicit
  equivalence, also with an empty axiom list.
  They do not establish a global decomposition of the magma.
  All four cases timed out after 900 seconds each, including construction.
  Each encoding had 55,871 variables and 2,135,993 clauses. The
  [saved search](../scripts/definability_weak_central_recovery_search.py) and
  [data](../data/definability_weak_central_recovery_search.json) reproduce
  these constraints. Before encoding, the script independently checks all
  175 relations for source closure, the source generation property, and
  the complete small-subalgebra target clones. These are necessary
  conditions for mutual recovery; the timeouts establish no impossibility.
  For example, run
  `timeout 900 python3 scripts/definability_weak_central_recovery_search.py 0`
  (cases range from 0 to 3; requires `python-sat` and NumPy).
- The optional `--monogenic` search instead requires that each of `1`, `3`,
  and `7` individually generate the whole target, as they do in the source.
  These represent three orbits under the source's rotation automorphism.
  All four cases again timed out after 900 seconds each. The stronger
  generation encoding has 117,406 variables and 2,377,238 clauses; it gives
  no satisfiability or impossibility result.
- Mixed-model local interpolation and compatible-relation searches found
  candidate target tables satisfying the tested constraints. Those tables
  are not proofs of term definability.
- Follow-up searches on older eight-element models allowed full unary-term
  recovery for E3342 → E4405, E3342 → E3545, E3545 → E4405, and
  E3545 → E3342. These checks combined local binary-relation restrictions
  with preservation of the source's exact family of subalgebras. They do
  not exclude obstructions using other models or higher-arity relations.
- On one older eight-element E3342 model (bank index 397), exhaustive binary
  term closure contained 4,610 operations, including 128 satisfying E4405.
  One of those target operations recovered the source by a term. This
  particular model therefore cannot refute E3342 → E4405 in TS/fin.
- The proposed E1483 translation-rank factorization remains unproved.
  Small-carrier checks of selected consequences do not establish it on
  arbitrary carriers, or exclude E1483 at order 11.

## Reproduction

```sh
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_residual_check.py --json
lake env lean scripts/check_definability_square_candidates.lean
lake env lean scripts/check_definability_unary_candidates.lean
lake env lean scripts/check_definability_commutative_obstruction.lean
lake env lean scripts/check_definability_1483_adjacency.lean
lake env lean scripts/check_definability_1483_dual.lean
```

The Python command also checks that the saved models and closure tables match
the Lean certificates. The certificates are standalone research checks under
`scripts/`; they add no facts to the definability board and do not change its
source fingerprint.
