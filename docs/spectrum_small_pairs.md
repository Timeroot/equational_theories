# Small orders separating possible spectrum classes

The October 1 pass establishes the following results. All statements below
have complete Lean proofs; finite exclusions use saved LRAT certificates and
explicitly registered native checks, with no `sorry`. The positive E1313 table
is checked by ordinary kernel reduction.

| Law | Order | Result | Lean declaration |
|---|---:|---|---|
| E467 | 16 | Impossible | `Spectrum.not_order_467_16` |
| E670 | 7 | Impossible | `Spectrum.not_order_670_7` |
| E677 | 8 | Impossible | `Spectrum.not_order_677_8` |
| E704 | 9 | Impossible | `Spectrum.not_order_704_9` |
| E1279 | 9 | Impossible | `Spectrum.not_order_1279_9` |
| E1279 | 13 | Impossible | `Spectrum.not_order_1279_13` |
| E1313 | 8 | Impossible | `Spectrum.not_order_1313_8` |
| E1313 | 9 | Exists | `Spectrum.SmallPairs.model_1313_9` |
| E1313 | 11 | Impossible | `Spectrum.not_order_1313_11` |

The order-eight answers for E677 and E1313 are negative. This splits the six-law
cluster using orders 8, 9, 11, and 13:

| Remaining group | Order 8 | Order 9 | Order 11 | Order 13 |
|---|---|---|---|---|
| E467, E1516 | Yes | Yes | Yes | Yes |
| E704 | Yes | No | Yes | Yes |
| E1279 | Yes | No | Yes | No |
| E677 | No | Yes | Yes | Yes |
| E1313 | No | Yes | No | Yes |

Rows in this table are mutually separated spectra. E467 and E1516, which
agree on these four orders, are now separated at order sixteen: E1516 has
a model and E467 has none, both proved in Lean.
E704/E1279 is now separated at order 13, as explained below. E670/E1110 are separated at 7. E667 has a two-element model, unlike
these six laws, and belongs with the separate E481 comparison.

`Spectrum/SmallPairs/Separation.lean` records 19 directed spectrum obstructions
and the resulting spectrum inequalities and finite FO-definability negatives.
`Definability/SmallSpectrumPairs.lean` registers them with the relation board.
Each obstruction links a concrete positive theorem and an exclusion theorem;
none depends on an unformalized spectrum bound.

## The nine-element construction

The SAT witness has a simple affine description on `(Z/3)²`. Write
`A(u,v) = (u+2v,u+v)` and `c=(0,1)`, and set `x*y=Ax+y+c`.
Here `A²+A=I` and `A³+A+I=0`. Expanding the right side of E1313 gives
`(A²+A)x + (A³+A+I)y + (A²+A+2I)c = x` in characteristic three.
Numbering `(u,v)` by `3u+v` gives exactly the saved nine-element table.
Thus the witness also has a short mathematical explanation; the Lean theorem
checks that table directly. Its direct powers already give every order `9^k`.

## Reduction before finite checking

`SmallPairs/Basic.lean` treats five two-variable identities uniformly. Each
identity exhibits a preimage under every left translation, so finiteness makes
left translations bijective. E704 and E1279 give an explicit left inverse of
`x ↦ (x*x)*y`; consequently squaring and right translations are bijective too.
E1313 likewise gives surjectivity of every right translation. These are ordinary
Lean arguments, valid independently of the small orders being checked.

Choose a non-idempotent element as zero if one exists. Relabel the cycles of
its left translation consecutively. The general relabelling theorem gives
`f(0,y) ≤ y+1`, while `f(0,0)=0` now implies that every element is idempotent.
The CNF records table entries and just one intermediate subterm, eliminating
the outermost operation by left cancellation. Every clause is proved satisfied
by a normalized model. Thus an LRAT refutation rules out arbitrary models,
not just an assumed Latin or symmetric subclass.

The five initial exclusions use about 3.15 MB of compressed proof data in total;
their individual certificate modules built in 4–5 seconds on this checkout.
E704/9 and E1279/9 use only 33 KB and 99 KB after adding the proved right
cancellation and squaring constraints. Builds replay certificates rather than
rerunning the solver.

## The order-eleven argument

An unrestricted E1313/11 search timed out. Splitting by the cycle type of the
first row instead gave 139 cases: its cycle containing zero is distinguished,
and the other cycle lengths are sorted. All but the idempotent row with five
transpositions were refuted in the initial short searches; a longer run refuted
that final case too.

The Lean coverage proof avoids enumerating all 11! permutations.
`SmallPairs/ChainRows.lean` recursively extends an injective prefix, allowing
only values satisfying the chain bound. Its completeness theorem is proved
for arbitrary sizes. At size eleven it produces only 1024 rows. A native
check verifies explicit conjugations fixing zero from these rows into the
139 canonical forms. The law, the diagonal normalization, and the chain
bound survive this second relabelling. Each canonical form has a saved,
trimmed LRAT refutation. The complete argument is in
`SmallPairs/OrderEleven/Exclusion.lean`.

The 139 compressed certificates occupy about 49 MB, with the largest file
about 5.7 MB. The combined certificate module built in 142 seconds on this
checkout; this is the expensive part of the new order-eleven result. Its
certificates are cached for subsequent builds. The solver is not part of the trusted proof. Hashes and timings
are recorded in `data/spectrum/1313_order11_refutations.json`.

## E704 and E1279 are separated at thirteen

The affine E704 operation `x*y=10x+6y` on `ZMod 13` was already proved in Lean.
The new theorem `Spectrum.not_order_1279_13` excludes E1279 at that order,
using proved Latin and squaring reductions, a complete 272-case translation
cycle split, and checked LRAT certificates. The chain-row coverage check
examines 4,096 rows rather than all 13! permutations.

Consequently `Spectrum.SmallPairs.spectrum_704_ne_1279` separates the spectra,
and `Equation1279_not_definableFromFin_Equation704_smallSpectrum` rules out
the finite FO-definability direction. See [the proof write-up](1279_order13.md).
The remaining possible pairs from this audit are E481/E667 and E1483/E1485.

The follow-up [E467/E1516 comparison](467_1516_spectrum_comparison.md) proves
all fourth-power orders for E1516 and improves its Lean cutoff to 675. The
complete Lean exclusion of E467 at sixteen uses an exhaustive squaring/row
cycle classification, proved first-use normalization, and 112 saved LRAT
refutations. `Spectrum.spectrum_467_ne_1516` records the separation and
`Equation467_not_definableFromFin_Equation1516` registers the finite
FO-definability obstruction.

## E667 at orders 12 and 15 remains open

The pass used unrestricted Latin searches of 300 seconds at each order,
240-second searches with several possible involution symmetries, and searches
among principal isotopes of small groups and a nonassociative loop. No model
was found. The unrestricted and symmetry searches timed out, as did the
order-15 cyclic-group-isotope and order-12 Chein-loop-isotope searches.

The searches refuted every group-isotope construction of order 12: the groups
are `C12`, `C6 × C2`, `A4`, the dihedral group of order 12, and the dicyclic group
of order 12. The isotope encoding allows arbitrary permutations on both
inputs. Up to relabelling this covers every isotope of the specified group.
These are research computations, not Lean theorems and not a nonexistence
claim for arbitrary E667 quasigroups.

The earlier affine obstruction explains why the obvious module constructions
fail: `(B²+I)(B³-B-I)(B³-B+I)=0` has irreducible factor degrees 2,3,3 over F3,
whereas both 12 and 15 have 3-adic valuation one. This says nothing against
non-affine models. E481/E667 therefore remains a possible spectrum merge.
E1483/E1485 was left untouched.

A final pass split E667/12 into its 195 first-row cycle forms. Three seconds
per case refuted 88 forms and left 107 unresolved; none produced a model.
The coverage argument for these cycle forms is the same finite relabelling
argument used above, but the E667 case refutations are not formalized.

The 15 bounded E667 probes and this complete case-status inventory are retained in
`data/spectrum/667_small_order_searches.json`, with their scopes and timeouts.
The reusable `scripts/spectrum_small_pair_search.py` supports unrestricted,
automorphism, fixed-row, and loop-isotope searches and verifies every returned
table against the original equation. Failed searches never generate an
exclusion theorem or change a catalogue bound.

## Reproduction

```sh
python3 scripts/spectrum_small_pair_certificates.py
python3 scripts/spectrum_1313_eleven.py
python3 scripts/spectrum_1279_thirteen.py
lake build equational_theories.Spectrum.SmallPairs
lake build equational_theories.Definability.SmallSpectrumPairs
python3 scripts/spectrum_generate.py --check
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
```

The first two commands verify saved hashes and regenerate Lean wrappers.
Add `--solve` to reconstruct certificates using CaDiCaL. Spectrum generation
updates the source catalogue and website summaries, but a commit-pinned website
deployment bundle is a separate refresh after committing the evidence.
