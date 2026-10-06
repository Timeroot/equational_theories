# E667 at 12 and 15: strengthened searches, 2026-10-01

Neither existence question was settled. The accompanying
`data/spectrum/667_incremental_searches.json` preserves the case outcomes,
restrictions, conflict budgets, and cumulative solver statistics. All UNSAT
results in this dataset are external research results, not Lean exclusions.
UNKNOWN means a budget was exhausted and carries no negative conclusion.

## Encoding and coverage

Finite E667 models are Latin, as proved in Lean. The SAT encoding has one
indicator per table entry and one per intermediate value `(x*x)*y`. The latter
also forms a permutation row. Incremental CaDiCaL retains learned clauses
between canonical first-row cycle cases. Each case has its own conflict budget.
Returned models are checked directly against the original equation.

The added consequences are all proved in
`Spectrum/Equation667ConstantDiagonal.lean`:

- Constant diagonal is impossible at an order divisible by three.
- A genuine three-cycle through a row's own index is impossible.
- A two-cycle through that index forces its square to be idempotent.
- Above an idempotent `e`, the square fiber is exactly the fixed set of `L_e²`,
  and is invariant under `L_e`.

The strengthened clauses were also evaluated independently on a saved valid
nine-element model; all 44,208 clauses held.

There are three distinct modes. `normalized` chooses a non-idempotent zero
whenever one exists and puts its row permutation in cycle form. Its
first-cycle-one cases therefore cover **fully idempotent models**, not all
models with an idempotent. `one-idempotent` instead sets an idempotent as zero
and omits that conditional-diagonal normalization, so mixed models are
included. `idempotent-free` excludes all diagonal fixed points. In this last
mode one may additionally choose a row with a fixed point: solve `a*x=x` in
any column and use row `a`. Its distinguished cycle has length at least four,
while its remaining cycles include a one-cycle.

The two restricted modes together cover all possible models, but many of
their individual cases remain unresolved. The archived idempotent-free pass
used a broader list of row forms; the reusable driver now applies the extra
fixed-point-row reduction as well.

Combining the valid case reductions leaves **51 first-row forms** for an
order-12 model: seven in the one-idempotent branch and 44 in the
idempotent-free branch. The lists are stored in the research JSON. The seven
one-idempotent forms, with the distinguished cycle written first, are

```
(1,1,4,6), (1,3,3,5), (1,3,4,4), (1,3,8), (1,4,7), (1,5,6), (1,11).
```

This reduction combines mathematical symmetry arguments with external SAT
refutations; it has not been replayed as a Lean exhaustion theorem.

A separate 90-second search restricted every left translation to one of the
1320 projective-linear permutations in PGL(2,11), acting on twelve points.
It was inconclusive. The script `spectrum_667_projective_search.py` generates
this family without imposing arbitrary row relabelings that might leave it.

## Repairing a near-model

Latin trades found a twelve-element Latin table satisfying 138 of the 144
E667 instances. It is saved as record 1 of `data/spectrum/667_near_models.json`.
Its failures are exactly the six off-diagonal ordered pairs in `{1,3,5}`.
Those points form a closed Steiner-three submagma, so changing only their
internal multiplication cannot produce E667. The two six-element halves also
form a quotient structure which a genuine model must destroy, by the new
Lean simplicity theorem.

The square-fiber identity explains another obstruction: row 1 is an involution,
but not all squares equal 1. Its ten-element square fiber would have to be the
whole carrier if that row were retained. Thus a small number of failed law
instances need not mean that only a few table entries require repair.

An independent SAT search ruled out **every Latin E667 table differing in at
most 24 entries** from this seed, with no canonical-row constraints imposed on
candidate repairs. The larger 36-entry neighborhood was unresolved. A separate
unrestricted search used the seed only as branching phases, imposed no
agreement with it, and exhausted one million conflicts in about 276 seconds.
It was also unresolved. These results establish neither existence nor
nonexistence at order 12.

## Reproduction

```
python3 scripts/spectrum_667_incremental.py 12 --mode one-idempotent --budget 500000
python3 scripts/spectrum_667_incremental.py 12 --mode idempotent-free --budget 100000
python3 scripts/spectrum_667_incremental.py 15 --mode normalized --budget 10000
python3 scripts/spectrum_667_near_model_search.py data/spectrum/667_near_models.json /tmp/e667-repair.json --record-index 1 --max-changes 24 --budget 100000
python3 scripts/spectrum_667_near_model_search.py data/spectrum/667_near_models.json /tmp/e667-phase.json --record-index 1 --budget 1000000
```

Solver timing and learned-clause trajectories depend on case ordering and
worker count. The recorded status of a completed case, its restrictions, and
its explicit budget are kept separately from any prospective rerun.

## Subsequent complete subclass exclusions

The idempotent and right-identity subclasses at order twelve now have complete
Lean LRAT refutations; commutative, associative, and left-identity models are
also excluded by Lean arguments. See `e667_order12_subclasses.md`. These do not
settle the unrestricted problem or exclude mixed idempotent/non-idempotent
models. The current incremental driver adds the proved idempotent and
right-identity exclusions as propagation clauses; the archived passes above
predate that change.

The subsequent three-minute-per-case pass refuted `(1,1,4,6)` externally and
left the other six mixed-idempotent shapes unresolved. Including the unchanged
44 idempotent-free shapes leaves **50 current forms**, superseding the archived
51-form split above. Full outcomes and reproduction are in
`data/spectrum/667_order12_subclass_rows.json` and
`scripts/spectrum_667_subclass_rows.py`. This is still an external case reduction,
not a Lean nonexistence theorem at order twelve.
