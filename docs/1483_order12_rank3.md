# E1483 at order twelve: the minimum-rank-three case

`Spectrum.E1483.OrderTwelve.RankThree.no_model` excludes a normalized
twelve-element E1483 operation whose smallest row image has size three.
The complete order-twelve exclusion combines this with the other possible
minimum ranks. This module proves one of those cases, rather than assuming the
remaining cases have already been settled.

Choose a row of minimum rank and label its argument zero. Its three outputs are
labelled 1, 2, 3: zero cannot belong to this row image, since an edge from zero
to itself would give the impossible rank bound `12 ≤ 3 * 3`. Column membership is the transpose of row
membership. Along an edge the two translation images provide injective
coordinates; if their ranks are three and four, the coordinates are bijective.
The resulting inverse identities are explicit additional CNF constraints.
All these facts are proved in `SharpCoordinates` and the order-twelve encoding.

The remaining freedom to rename elements is also proved before searching.
First minimize the first row under image-label permutations preserving its square.
Then sort the remaining labels by their first-row information and minimize the
second row inside each interchangeable first-row fiber. Swaps used in the last
step preserve the entire first row. Consequently its earlier normalization and
the second-row lexicographic conditions hold simultaneously. Prefix flags encode
these comparisons; they do not impose an extra algebraic assumption.

The final certificate splits on `f(0,1)` and `f(0,2)`. These entries belong to
`{1,2}` and `{1,2,3}`, respectively. Only the prefix `(2,2)` needs a further split
on `f(0,3)`. Thus the eight branches are

```
(1,1), (1,2), (1,3), (2,1), (2,2,1), (2,2,2), (2,2,3), (2,3).
```

Each branch has a separate compact RUP certificate. A ninth, 376-byte
certificate checks that the branch list covers the normalized Boolean formula.
`SmallOrders.CaseAssembly.unsat_of_cases` combines their verified refutations.
Neither the external solver nor the external choice of cases is trusted.

The selected payloads total **5,823,384 bytes (5.55 MiB)**. Native Lean checks
measured between 14 and 49 seconds per substantive branch in ordinary module
builds; the largest payload, 1,152,696 bytes, checked in 49 seconds. The larger unsplit intermediate
certificate took 391.7 seconds to check. The split deliberately trades a modest
increase over the smallest unsplit payload for bounded individual checks and
parallel compilation. The Lean `LRAT.check` result is connected to unsatisfiability
by `check_sound`, and each exported theorem passes the complete-spectrum audit.

The tracked manifest is `data/spectrum/1483_order12_rank3.json`; payloads live
beside it in `1483_order12_rank3_rup/`. To reproduce the exact search inputs and
audit every CNF and payload hash, run:

```sh
lake build equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Encoding
python3 scripts/spectrum_1483_twelve_rank3.py
```

The Lean exporter is the authoritative CNF generator. Its DIMACS files can be
passed to `cadical --seed=1 --lrat`; the optional backward-trimming pipeline is
documented in `scripts/spectrum_retrim_certificate.py`. To check all selected
proofs and their assembly, run:

```sh
lake build equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree
```
