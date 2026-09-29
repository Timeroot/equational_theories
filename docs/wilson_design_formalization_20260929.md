# Formal design existence for the spectrum cofiniteness proofs

29 September 2026. Lean proves eventual existence of pairwise balanced designs
with block sizes `{5,11,16}` and `{7,9,16}` at every admissible order:

* `Spectrum.PBD.wilson_5_11_16`
* `Spectrum.PBD.wilson_7_9_16`

Both declarations are in
[`PBD/WilsonInstances.lean`](../equational_theories/Spectrum/PBD/WilsonInstances.lean).
Their guarded axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. Combined with the existing group-filling reductions, they prove
cofiniteness of E677, E1083, and E1286 without any remaining proof obligations.
No numerical cutoff has been extracted.

## Source and scope

The proof follows §§19–21 of Richard M. Wilson, *An existence theory for
pairwise balanced designs*, Ohio State University PhD thesis, 1969
([public thesis](https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1486654021585381&disposition=inline)).
This formalizes the instances needed here, together with reusable eventual
periodicity for PBD-closed sets containing prime-power block sizes. It does
not assert Wilson's full theorem for arbitrary finite sets of block sizes.

Two simplifications avoid deeper number-theoretic inputs:

1. The auxiliary marked design in the long-progression construction only
   needs its block sizes in the PBD-closed set, with one prescribed marked
   block. A truncated transversal design supplies it. Consequently an
   unbounded family of uniform designs suffices to start the construction;
   for prime-power block sizes, affine designs provide that family. No
   general cyclotomic difference-family existence theorem is required.
2. Two consecutive uniform-design parameters give periods whose gcd is
   `k(k−1)`. This avoids primes in arithmetic progressions.

## Proof structure

All module names below are relative to `equational_theories/Spectrum/PBD`.

| Step | Formalization |
| --- | --- |
| Pairwise decompositions, refinement, weighted fundamental construction, adjoining a point | `PairDecomposition`, `Fundamental`, `Adjoin`, `Closure` |
| Truncation and PBD closure of idempotent orthogonal arrays | `DesignTruncation`, `IdempotentTransversal` |
| For fixed k, transversal designs TD(k,n) exist for all sufficiently large n | `TransversalExistence` |
| Localization at a point; PBD closure and multiplication of replication numbers | `Localization`, `Replication` |
| Affine seeds for prime-power block sizes; an initial rectangle of replication numbers | `UniformSeeds` |
| Relative multiplicative density, then bounded additive gaps | `AsymptoticArithmetic`, `ReplicationDensity` |
| Marked designs and six hole ingredients | `Hole`, `HoleGroups`, `MarkedTruncation`, `HoleIngredients` |
| Weighted designs give arbitrarily long progressions | `WeightedTransversal`, `WeightedSum`, `ReplicationTail` |
| Every sufficiently large order 1 modulo k(k−1) has a uniform k-design, for prime-power k | `ReplicationTail.uniform_one_tail_primePower` |
| Two group-divisible ingredients from localized transversal designs | `OneGroup`, `TransversalLocalization` |
| Weighted construction fills every occupied positive residue class for a suitable period | `PeriodConstruction`, `FibreArithmetic`, `CompleteFibres` |
| Periods are closed under gcd; obtain period k(k−1) | `EventualPeriod`, `WilsonPrimePowers` |
| Concrete periods and residue witnesses give the two required Wilson instances | `WilsonInstances` |

For `{5,11,16}`, the periods 20, 110, and 240 have gcd 10.
The positive design orders 1, 5, 16, and 80 occupy residues 1, 5, 6, and 0.
Admissibility requires `10 ∣ n(n−1)`, which gives exactly those residues.

For `{7,9,16}`, the periods 42, 72, and 240 have gcd 6.
The positive design orders 1, 9, 16, and 144 occupy residues 1, 3, 4, and 0.
Admissibility requires `6 ∣ n(n−1)`, again giving exactly those residues.

The products 80 and 144 are supplied by finite-field transversal designs.
Only positive seeds are used to fill residue classes: the empty design at
order zero is not treated as evidence of an occupied eventual residue class.

## Spectrum consequences

`Spectrum.Pending.cofinite_677`, `Spectrum.Pending.cofinite_1083`, and
`Spectrum.Pending.cofinite_1286` now apply the completed design theorems.
Their names are retained for compatibility, and their assertions are marked
`complete`. The proof includes the extension from the idempotent residue
classes to all sufficiently large orders via arbitrary group fillings.

The related E670 and E907 paper arguments are separate obligations; they
are not marked complete by this change. Nor does cofiniteness identify any
particular previously unknown small order without an explicit bound.

## Verification

Build the full spectrum library and audit the exported statements with:

```sh
LEAN_NUM_THREADS=4 lake build equational_theories.Spectrum
LEAN_NUM_THREADS=4 lake env lean scripts/check_spectrum.lean
python3 scripts/spectrum_generate.py --check
python3 scripts/test_spectrum_overview.py
```

The audit checks the declaration types and transitive proof dependencies for
all 4,694 catalogue entries. In particular, the three new cofiniteness results
must have evidence `complete`; a documented pending input cannot satisfy that
check. Their direct axiom reports contain only the three standard axioms above.
