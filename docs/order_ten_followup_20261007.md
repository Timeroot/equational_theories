# Order ten: E907, E1083, and E1486

Follow-up to [the orders-eight-and-ten pass](spectrum_small_orders_20261007.md).
The new exclusions are `Spectrum.not_order_907_10`,
`Spectrum.not_order_1083_10`, and `Spectrum.not_order_1486_10`.
All use saved certificates and complete Lean
reductions, with the repository's registered native LRAT-checking policy.
No `sorry` was added. Their dual laws inherit the same exclusions.

Among the 17 representatives with unresolved exact spectra, **only E670
and E677 still have order ten unresolved**. All 17 already have order
eight decided. No positive order-ten model was found in this follow-up.

## E907

Write `L_a(x)=a*x`. E907 gives a term inverse for `L_a`, so each left
translation is bijective on a finite carrier. The existing direct equational
proofs exclude nontrivial pointed cycles of lengths two, three, and four:
`L_a^k(a)=a` for one of those lengths forces `a*a=a`. The search imposes these
proved constraints on every row. It also chooses a non-idempotent zero if
one exists, then labels the cycles of `L_0` consecutively. The idempotent
case is included. With the resulting clauses the solver refutes order ten;
Lean proves that every hypothetical model satisfies those clauses and checks
the saved refutation.

A further reusable result is formalized in
[LeftFixers.lean](../equational_theories/Spectrum/Equation907/LeftFixers.lean):
**a point has at most one left fixer**. If `a*x=x`, E907 and left cancellation
give `x*(x*a)=x`. Two such fixers coincide by cancelling `L_x` twice. This
does not assert that fixers exist, or that general right cancellation holds.

The order-ten proof is in
[Normalization.lean](../equational_theories/Spectrum/Equation907/OrderTen/Normalization.lean),
[Encoding.lean](../equational_theories/Spectrum/Equation907/OrderTen/Encoding.lean),
and [E907N10.lean](../equational_theories/Spectrum/SmallOrders/Certificates/E907N10.lean).
The smallest unresolved even order for E907 is now **12**. This is not a proof
that all even orders are impossible.

## E1083: count fixed points before choosing zero

E1083 forces both translations to be bijective on a finite carrier.
Consequently there are exactly `n` pairs `(a,x)` with `a*x=x`: each column
contributes one. Every idempotent row contributes at least one such pair.
If non-idempotent rows exist and all contributed at least two, the total
would exceed `n`. Thus either the entire magma is idempotent, or we can
choose a non-idempotent zero whose left translation has at most one fixed
point. This remains true after conjugating that translation to the usual
consecutive-cycle labeling.

The counting argument is more general than E1083: it only requires that each
point have **at most** one left fixer. It therefore also applies to E677 and
E907. Its Lean proof is in
[FewFixed.lean](../equational_theories/Spectrum/SmallOrders/FewFixed.lean).
[FewFixedEncoding.lean](../equational_theories/Spectrum/SmallOrders/FewFixedEncoding.lean)
adds the resulting normalization clauses to the existing chain-law encoding.
The original E1083 search reached its ten-minute limit. Adding these clauses
produced a complete refutation in about two minutes. The final theorem is in
[E1083N10.lean](../equational_theories/Spectrum/SmallOrders/Certificates/E1083N10.lean).

## A new directed spectrum separation

E66 has a ten-element model, whereas E1083 does not. Hence

```
Spec(E66) ⊄ Spec(E1083).
```

This closes one previously unknown directed spectrum-class arrow:
`{E66,E170,E177,E281} → {E1083,E2504}`, or eight equation pairs. The
corresponding finite FO-definability negative was already known independently;
no new definability-board cell or possible equivalence-class merge is claimed.
The named proof is `Spectrum.SmallOrders.not_subspectral_66_1083` in
[Separation.lean](../equational_theories/Spectrum/SmallOrders/Separation.lean).

## What remains at ten

E670 and E677 each received an unrestricted ten-minute search, followed by
searches across all 97 canonical first-row forms. Several forms remain open.
E677 also received the strengthened fixed-point normalization. All these
unfinished searches are recorded as `UNKNOWN`, not as exclusions.

## E1486: label the second-step images

Let `R_x={x*(z*z):z in G}`. Earlier Lean theorems show that every row has
size at least two in a nontrivial magma, and that the rows indexed by `R_x`
are pairwise disjoint. More generally, if all rows have size at least k,
then `k|R_x|≤10`. Thus either some row has size two, or **every row has
size exactly three**. This is now proved as `row_bound` and
`three_of_no_two` in the new
[normalization module](../equational_theories/Spectrum/Equation1486/OrderTen/Normalization.lean).

In the rank-two case choose that row as zero, and label its image either
`{0,1}` or `{1,2}`. The solver excludes both cases. The rank-three case was
much harder with only a normalized first image. The successful additional
step is to choose zero to be an idempotent if one exists. Then `0∈R_0`,
and we may label `R_0={0,1,2}`. The three rows `R_0,R_1,R_2` are disjoint
and have size three. Relabel the remaining points so

```
R_0={0,1,2},  R_1={3,4,5},  R_2={6,7,8}.
```

This alone makes the final idempotent case refutable in under one second.
The absorption identity additionally determines `0*u` on these nine points,
and every square lies among them; the final encoding needs neither of
these extra clauses. If there are no idempotents, choose zero to be a square.
Squaring is an involution on the square image, so label its partner one:
`0*0=1` and `1*1=0`. The two possible normalized row images are then also
refuted, in well under a second. No assumption that all elements are
idempotent is made in the idempotent-zero branch.

Lean proves the permutation argument while fixing previously labelled
points, the exact image semantics of the auxiliary SAT variables, and the
exhaustiveness of these five cases. The
[encoding](../equational_theories/Spectrum/Equation1486/OrderTen/Encoding.lean)
and [final assembly](../equational_theories/Spectrum/Equation1486/OrderTen/Exclusion.lean)
produce `Spectrum.not_order_1486_10` with no admitted obligations.
All five Lean-exported formulas match the sanitized solver inputs byte for
byte. The original inputs each contained ten tautologies; the existing
sanitizer removed them and renumbered the retained proofs.

E1486 now has only **12,14,15,17,26** unresolved. Its lower bound and cutoff
27 are unchanged. This does not settle another spectrum-class arrow beyond
the E66/E1083 arrow above: earlier known orders already separated the other
applicable pairs.

[Research data](../data/spectrum/order_ten_followup_20261007.json) records the
budgets, scopes, canonical cases, and hashes. Nine compressed DIMACS inputs from the earlier probes
are retained so the main probes can be replayed without reconstructing their
encodings. For example:

```sh
gzip -dc data/spectrum/order_ten_searches/e670_10.cnf.gz > /tmp/e670-ten.cnf
cadical -t 600 /tmp/e670-ten.cnf
```

## Certificates and reproduction

The retained files use the existing compact RUP format with an input-clause
mask and xz compression. E907 occupies **10,767,060 bytes**, E1083
**14,680,700 bytes**. The five E1486 files total **11,694,008 bytes**,
almost all in the two rank-two cases. The combined addition is about
**37.1 MB** (35.4 MiB). Propagation hints are reconstructed by the precompiled
Lean library, then the standard verified LRAT checker validates the result.
The packer, decompressor, and external solver are not proof axioms. Ordinary
builds use these saved data and do not run a solver.

The E907 input was exported from Lean and matched byte for byte. The initial
E1083 solver input contained nine tautologies. The existing LRAT sanitizer
removed them and adjusted clause IDs; its resulting CNF matched Lean byte
for byte. The reproduction generator now emits the sanitized formula directly.

```sh
python3 scripts/spectrum_small_orders.py
python3 scripts/spectrum_1486_ten.py
lake build equational_theories.Spectrum.SmallOrders
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
python3 scripts/spectrum_generate.py --check
python3 scripts/test_spectrum_overview.py
```

Use Lake to build the certificate modules: it loads the compiled
`SpectrumCertificateData` library. Running standalone scratch files with
`lake env lean` alone does not load that plugin and gives misleadingly slow
reconstruction timings.


The original certificate modules for E907 and E1083 took 769 and 1,018
seconds respectively to build under concurrent local load, including native
reconstruction and checking. This is separate from their roughly two-minute
solver times. For E1486, retaining CaDiCaL's default clause shrinking reduced
the hardest search from 156 to 98 seconds. An extra bound of five on every
square-row size (already implied by `row_bound`) took 113 seconds and was
not used in the final reduction.

The retained E1486 rank-two-outside certificate is **9,936,344 bytes**,
down from 16,595,824 bytes. Its Lean module built in **569 seconds**, down
from 1,098 seconds for the first certificate. The other four E1486 modules
took about 4, 5, 8, and 38 seconds. Only the smaller certificate is retained;
all five cases use Lean-checked refutations.


## Final validation

The final `lake build equational_theories.Spectrum` and
`lake env lean scripts/check_spectrum.lean` both passed with the smaller
certificate in place. The latter checked all 4,694 laws, catalogue theorem
types, proof statuses, and transitive axioms. All 19 spectrum-overview tests,
both certificate/hash generators, and the catalogue freshness check passed.
The full-matrix relation audit and both equivalence inventories were refreshed;
all three fingerprints match the final Lean source. No new admitted theorem
or undocumented axiom was introduced.
