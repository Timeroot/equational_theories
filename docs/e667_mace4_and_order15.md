# E667: patient Mace4 searches and order-fifteen restrictions

Neither unrestricted order 12 nor unrestricted order 15 has been settled.
The new order-fifteen restrictions below are complete Lean proofs, with no
`sorry`. Search timeouts remain unknowns.

## What a fifteen-element model would have to look like

| Property | Status | Declaration in `Spectrum.E667` |
|---|---|---|
| Quasigroup | Necessary for every finite E667 model | existing translation-injectivity theorems |
| Simple | Proved: every surjective homomorphic image has order 1 or 15 | `quotient_card_fifteen` |
| Commutative | Impossible | `not_commutative_fifteen` |
| Globally idempotent | Impossible | `not_idempotent_fifteen` |
| Associative | Impossible, already known for every nonzero order divisible by 3 | `not_associative_of_three_dvd` |
| Left identity or two-sided identity | Impossible, already known at these orders | `not_left_identity_of_three_dvd` |
| Right identity alone | Still unknown at 15 | bounded searches only |
| Contains some idempotent | Still possible | global idempotency exclusion does not exclude mixed models |

The previous order-twelve results remain intact. In particular, a right
identity *is* excluded at order twelve; that theorem is not transferred to
order fifteen.

## Completing the simplicity proof

Only the idempotent-free five-element quotient classification was missing
from the previous formal argument. A finite Latin square has a row with a
fixed point. In an idempotent-free E667 model, its own row index cannot lie in
a cycle of length 1, 2, or 3. On five points this forces a four-cycle and the
remaining fixed point. Move the chosen row to zero and apply the already
proved chain-labelling theorem. A small unary-permutation check now fixes that
row to `[1,2,3,0,4]`.

A 3,596-clause, 250-variable finite check shows that exactly one
idempotent-free E667 table has this row. Its LRAT certificate is just **1,458
compressed bytes**. The table is explicitly isomorphic to
`q(i,j)=3i+3j+1 mod 5`. The normalization, encoding soundness, and certificate
are all checked in `Equation667FiveClassification/`.

Every quotient order divides 15. A quotient of order 3 is impossible. For a
quotient of order 5, an idempotent would give a forbidden three-element fiber;
the idempotent-free alternative is the newly classified table. The earlier
`FiberThree.no_quotient_five` theorem excludes its three-element-fiber
extensions by a sign calculation. `Equation667SimpleFifteen.lean` combines
these facts to obtain simplicity on an arbitrary fifteen-element carrier.

## Excluding commutativity

The order-fifteen result now follows from the general mathematical theorem
that no commutative E667 magma has order three modulo four. No simplicity,
idempotent-existence argument, or finite-search certificate is needed.

For each output symbol x, the inverse-symbol permutation M_x sends y to the
unique z with y*z=x. E667 expresses it as L_x L_(x*x), and commutativity makes
it an involution. At odd order its fixed points show that squaring is
bijective. Thus M_x has a unique fixed point; at order three modulo four its
sign is negative. The product of all these signs is negative, whereas the
formula L_x L_(x*x) expresses it as a square, giving a contradiction.

`Equation667CommutativeParity.lean` formalizes the argument. The old
`Equation667CommutativeFifteen/Certificate.lean` path retains the public
`not_commutative_fifteen` theorem as a short application. The old 8,607,357-byte
compressed certificate, encoding module, and generator have been retired.
The metadata records its hash for provenance. See the
[structural research note](e667_structure_20261004.md) for the full argument
and its consequences at all remaining open odd orders.

## Excluding global idempotency efficiently

Left division converts an idempotent E667 operation into the idempotent cubic
law `d(d(x,d(x,y)),x)=y` (E229). In this operation no left translation has a
two-cycle. Its zeroth row fixes zero and no other point. After chain labelling,
the other fourteen points therefore lie in cycles of lengths at least three.
Up to permutation of the nondistinguished cycles there are exactly thirteen
possibilities:

```
3+3+3+5, 3+3+4+4, 3+3+8, 3+4+7, 3+5+6, 3+11,
4+4+6, 4+5+5, 4+10, 5+9, 6+8, 7+7, 14.
```

The general `SmallPairs.ChainRows.mem_rows` theorem proves coverage of all
injective chain rows. A registered finite check over its **16,384** rows
verifies the extra cycle sorting and the thirteen-case coverage. It does not
enumerate all `15!` permutations or trust a Python enumeration.

All thirteen table cases were refuted in under six seconds each. Their
trimmed certificates occupy **21,293,646 compressed bytes** together. The
certificate module built in about 37 seconds. This replaces an initial
single refutation whose trimmed text was roughly 279 MiB. All mathematical
reductions, row coverage, and LRAT replays are checked by Lean. The ordinary
build invokes no external solver.

## The Mace4 experiment

The order-twelve suite uses Mace4 2009-11A with two broad searches, each allowed
**1,800 CPU seconds**, and the six remaining mixed-idempotent row cases, each
allowed **600 CPU seconds**. Four workers run concurrently, with a 2 GiB cap
per worker. The two broad branches cover models containing an idempotent and
idempotent-free models respectively.

Inputs include E667, left and right cancellation, and the proved translation,
square-fiber, constant-square, global-idempotency and right-identity exclusions
where applicable. Labels are fixed by explicit proved row normalizations;
Mace4's additional least-number heuristic is disabled. The idempotent-free
branch chooses a row with a fixed point, which every finite Latin square has.
The input and output parser were validated against an independently checked
nine-element E667 model after relabelling its row into chain form.

Two further Mace4 runs at order fifteen allow 600 CPU seconds each, for the
right-identity and idempotent-free subclasses. A preceding ten-minute SAT
search of the right-identity subclass was inconclusive.

A solver's exhaustive termination is distinguished from time or memory limits.
Every returned positive table is checked independently against the original
E667 equation. No Mace4 exhaustion would by itself constitute a Lean proof.
All ten runs reached their CPU limits without a model or an exhaustive
refutation: **UNKNOWN** in every case. The eight order-twelve runs used two
CPU hours in total; the two order-fifteen runs added twenty CPU minutes.
Memory was not the bottleneck: the final order-twelve workers used about
12 MiB each, far below their caps.

Final outcomes, exact limits, and input/output hashes are recorded in
`data/spectrum/667_mace4_searches.json`. The exact inputs and logs are preserved
in `data/spectrum/667_mace4_logs.tar.gz`. No searches from this batch remain
running.

## Other order-fifteen construction searches

Six annealing runs started from the saved Latin near-model, using row, column,
and symbol cycle trades to preserve the Latin property. Four runs used the
original temperature schedule for five minutes each; two used higher peak
temperatures for four minutes each. Across approximately 1.27 billion attempted
trades, none improved its 42 failing E667 instances out of 225. Each returned
table and its failure count were checked independently. This remains a
near-model, not a positive witness or evidence of nonexistence.

Two five-minute SAT searches of isotopes of the saved Steiner quasigroups
`gap-steiner15-80` and `gap-steiner15-40` also timed out. These probes concern
only those isotope families. Their outcomes and the trade parameters are
recorded in `data/spectrum/667_fifteen_research.json`.

## Reproduction

```
python3 scripts/spectrum_667_mace4.py --mace /path/to/mace4 --seconds 1800 --row-seconds 600 --workers 4
python3 scripts/spectrum_667_mace4.py --mace /path/to/mace4 --order 15 --mode right-identity --seconds 600
python3 scripts/spectrum_667_mace4.py --mace /path/to/mace4 --order 15 --mode idempotent-free --seconds 600
python3 scripts/spectrum_667_fifteen_probe.py --seconds 600
python3 scripts/spectrum_667_five_certificate.py
python3 scripts/spectrum_667_idempotent_fifteen.py
lake build equational_theories.Spectrum
```

The final two Python commands verify the saved CNF and proof hashes; add
`--solve` to regenerate their certificates. The finite checks use the
repository's explicitly registered `spectrum_native` policy. No `sorry` or
unverified solver report is used by the new Lean declarations.
