# E1083 has no models of orders five and six

Both exclusions previously supported by external SMT search now have complete
Lean proofs:

```lean
import equational_theories.Spectrum.Equation1083.SmallExclusions

#check Spectrum.not_order_1083_5
#check Spectrum.not_order_1083_6
```

E1083 is `x = y ◇ ((x ◇ (y ◇ x)) ◇ y)`. At each order n, the proof uses all
n² assignments to x and y. It imposes no symmetry restriction and no extra
algebraic hypothesis. `FiniteTableEncoding.encoded_eq` proves that every
n-element magma is represented by the packed bit-vector table. Values with
unused three-bit codes are clipped, and the encoding theorem proves that
actual magma values are unchanged.

The resulting Boolean contradiction has a saved, trimmed LRAT certificate.
`bv_check` checks this certificate when the module is compiled, without
rerunning a SAT solver. A proved bridge maps the finite conjunction back to
the original equation, giving `¬ Law1083.HasModel n`.

The proof uses the repository's registered native LRAT and table-encoding
checks. Both refutations and both final exclusions have transitive
`spectrum_assert ... complete` audits. There are no admissions, unregistered
axioms, or dependencies on the earlier SMT answer.

Observed local timings on 28 September 2026:

| Order | Initial certificate generation and Lean check | Replay of trimmed certificate | Certificate bytes |
| --- | ---: | ---: | ---: |
| 5 | 10.82 s | 8.45 s | 2,657,700 |
| 6 | 49.09 s | 14.60 s | 17,873,973 |

These are wall-clock observations, not performance guarantees. Initial runs
used a 60-second SAT timeout; the retained proofs use solver-free replay.
Peak observed replay memory was approximately 2.1 GiB and 2.3 GiB respectively.

The source and certificate hashes are recorded in
`data/spectrum/1083_small_exclusions.json`. The dedicated generator leaves
the shared spectrum generators and catalogue untouched:

```sh
python3 scripts/spectrum_1083_exclusions.py
python3 scripts/spectrum_1083_exclusions.py --replay
```

The first command verifies generated source, case coverage, and LRAT hashes;
the second also recompiles both saved proofs. `--search` regenerates,
trims, and independently replays new certificates before installing them.
