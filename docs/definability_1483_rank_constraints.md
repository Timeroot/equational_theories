# E1483: translation ranks and constant rows

18 September 2026. These are general structural results used to strengthen the
remaining definability searches. They support the [order-eleven exclusion](definability_1483_order_eleven.md), whose large certificates were checked locally but are not distributed. Its Lean status is now `proofAvailable`, and the E1486 → E1483 consequence is not counted in the checked board.

Write `r(a)` for the number of distinct entries in row `a` of a finite E1483
magma. The [translation certificate](../equational_theories/Definability/Central1483Translations.lean)
proves that left and right translations at the same element have equipotent
images. It also proves

```
|G| ≤ r(a) · r(a ◇ z),
|G| ≤ r(a) · r(z ◇ a).
```

The first inequality comes from the injective map
`x ↦ (a ◇ x, x ◇ (a ◇ z))`: multiplying its two coordinates recovers `x`
by E1483. The dual identity supplies the second inequality. In particular,
an idempotent `a` satisfies `|G| ≤ r(a)²`. An idempotent with an injective
left translation forces the whole magma to be a singleton.
The certificate also bounds every fiber of `x ↦ a ◇ x` by `r(a ◇ z)`:
right translation by `a ◇ z` is injective on that fiber.

## Constant-row arithmetic

Suppose `zero ◇ x = one` for every `x`, and the magma is nontrivial. The
[constant-row certificate](../equational_theories/Definability/Central1483Constant.lean)
proves that `zero ≠ one`. For `N(x) = one ◇ x`, it proves:

- `N⁶ = id`.
- `N²` preserves multiplication.
- `N³` has no fixed point.
- `N²` has no fixed point among the idempotents.

Thus, on a finite carrier, `N³` pairs off the elements, while `N²` partitions
the idempotents into orbits of size three. Consequently **the carrier size is
even and the number of idempotents is divisible by three**. A bijective row
also supplies a constant row, so these restrictions apply whenever any row
is bijective.

The four equational proofs were found by Twee. Their
[saved proof traces](../data/definability_1483_constant_proofs.json) are replayed
by [the generator](../scripts/definability_1483_constant_check.py) into explicit
Lean equalities. It checks each rewrite against its cited equality and lifts
it through the relevant term context using `congrArg`. Lean checks the whole
replay. All four equational conclusions have empty axiom lists. The finite
cardinality consequences use only `propext`, `Classical.choice`, and
`Quot.sound`; there is no SAT or native-computation axiom.

## Consequences for the open searches

The twisted 32-element E1485 source has exactly five idempotents. Mutual term
recovery preserves the idempotents in both directions. An E1483 companion
for that search therefore has **no constant or bijective row**. Its five
idempotent rows each have at least six distinct entries.

The [maintained search](../scripts/definability_weak_central_recovery_search.py)
can add these constraints with `--strong`; `--rank-edges` also encodes exact
row and column ranks and their product bounds. The stronger search additionally
uses permutations and rotations of three five-element orbits outside the proper
small subalgebras. These permutations fix all 175 saved compatible relations
and preserve the necessary-condition problem. They are not claimed to preserve
the source operation itself. Their symmetry breaking orders outputs only in
cells whose inputs those permutations fix.

For the two rotation-fixed inputs, the rank encoding also records that image
sizes modulo five equal the number of fixed outputs in the image. The six
remaining rotation orbits have size five. The current full encoding has
294,517 variables and 2,845,246 clauses in each case.
All four cases using Glucose 4.2 reached a 420-second external limit,
including construction, without a SAT or UNSAT result.

For an eleven-element E1483 model, the same theorems exclude constant and
bijective rows. Exploratory SAT searches split the remaining possibilities
by the minimum row rank. Rank 2 and ranks 5 through 10 have returned UNSAT;
ranks 3 and 4 remain unresolved. These solver results have no Lean refutation
certificate and do not establish an order-eleven exclusion.

**Update, 20 September 2026:** the longer runs with `--constraints edges`
and `--normalize-first-row` returned UNSAT for both ranks 3 and 4. Thus every
minimum-rank case now has an exploratory UNSAT result. The saved data retain
the earlier inconclusive runs. The subsequent [complete certificate](definability_1483_order_eleven.md)
was checked locally, but its 734 MiB inputs are not distributed. The default
Lean exclusion is a registered `sorry`; E1486 → E1483 is not counted as checked.
The earlier solver records remain historical search evidence.

The [rank search](../scripts/definability_1483_rank_search.py) preserves this
partition and the [saved outcomes](../data/definability_1483_rank_search.json)
include an independently checked nine-element model of minimum rank three.
Use `--constraints basic` for the image-rank encoding that excluded ranks
6–10; `edges` adds exact ranks and product inequalities, and `collisions`
also adds the joint-injectivity conditions behind those inequalities.
Extra redundant constraints can slow the solver: the collision encoding
did not settle the rank-six case within a separate 90-second run.

Ranks two and five were excluded after adding `--normalize-first-row`.
Normalize row `0`'s image to `{0,…,k−1}` if it contains `0`, and to `{1,…,k}`
otherwise. Sort input labels greater than `k` by their row-zero outputs;
those input permutations fix all the output labels. When `k² < |G|`, the
row-edge bound additionally forbids `0` from the image.
The original first-row value-precedence constraints are compatible with this:
take a lexicographically least row among permutations preserving the image set.
This is a restriction on labels, not an additional algebraic hypothesis.

The product inequalities do not assert that row ranks divide the carrier size.
That stronger claim, and a general decomposition theorem, remain unproved.
In particular, proof attempts for idempotence of the mixed maps
`P_b(t) = a ◇ (t ◇ b)` and preservation of each other's fixed points were
inconclusive. These properties cannot yet be used to transfer the E1485
sharp-neighbor argument to E1483.

```sh
python3 scripts/definability_1483_constant_check.py
lake env lean scripts/check_definability_1483_constant.lean
lake env lean scripts/check_definability_1483_dual.lean
python3 scripts/definability_weak_central_recovery_search.py 0 --monogenic --strong --bit-channel --rank-edges --encode-only
python3 scripts/definability_1483_rank_search.py 11 6 --constraints basic --seconds 600
python3 scripts/definability_1483_rank_search.py 11 2 --normalize-first-row --seconds 600
python3 scripts/definability_1483_rank_search.py 11 5 --normalize-first-row --solver glucose42 --seconds 200
```

The `--encode-only` command verifies the source constraints and constructs the encoding
without solving it. Omit `--encode-only` and use an external timeout to search;
the four cases are numbered 0 through 3. Solver outcomes remain separate from
the source-derived definability board.
