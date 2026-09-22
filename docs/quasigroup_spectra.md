# Exact spectra of E115, E481, and E873

The complete Lean theorems are `Spectrum.Catalogue.exact_115`, `exact_481`,
`exact_873`, `exact_880`, and `exact_1496`, together with their duals. E115,
E873, and E880 have every positive order except 2 and 6. E481 and E1496 have
every positive order except 3 and 6.

The main proofs are in `Spectrum/QuasigroupSpectra.lean`. The constructions
use ordinary Lean proofs and kernel evaluation of explicit finite seeds.
The exclusions at orders two and three use the existing audited enumeration;
the order-six exclusions use native LRAT certificate checking, explicitly
registered with the spectrum dependency audit. None of these results depends
on `sorry` or an unregistered axiom.

## E115: a cyclic extension

`Equation115Construction.lean` defines a finite additive group A with a
permutation g, an element c ≠ 0, and exactly one fixed point p, such that

- g³(x) = x,
- g(0) = c,
- x + g(x) + g²(x) = −c.

Explicit seeds have orders 7, 13, and 25. Products with Z/7, using multiplication
by 2 on the new coordinate, preserve this data and the unique fixed point.
Their orders are therefore m = b·7ᵏ, with b in {7,13,25}.

For every n ≥ 8 there is such an m with m < n < 2m. If n ≡ 2 (mod 3), then
r = n−m ≡ 1 (mod 3). Select the fixed point and (r−1)/3 whole three-cycles,
avoiding the three-cycle containing 0. This gives an invariant set S of size r.
The generic selection theorem is in `TripleSelection.lean`.

Choose a Mendelsohn quasigroup Q of order r and a bijection f:Q→S. On A ⊔ Q,
with δ = y−x, define

| Inputs | Product |
| --- | --- |
| x,y in A, δ in S | f⁻¹(δ) in Q |
| x,y in A, δ outside S | y+g(δ) in A |
| x in A, y in Q | x−c−f(y) |
| x in Q, y in A | y+f(x) |
| x,y in Q | the Mendelsohn product |

Case analysis proves E115. The minus sign before f(y) corrects the A×Q entry
of formula (12) in the local September 10, 2026 `spectrum-note.pdf`.
The seeds and scaling argument supply the partition existence left as a TODO
there. Mendelsohn models cover residues 0 and 1 modulo 3, apart from the
excluded order 6; a checked order-five model completes the construction.

## E481: partial cyclic data

`Equation481Construction.lean` uses a permutation g on A with g³ = id, a
constant c, and an invariant subset G not containing 0. On G there is exactly
one fixed point and

    x + g(x) + g²(x) = 2c.

The four explicit seeds have orders b = 11,17,29,53, with |G| = b−4 and c = 1.
All seed properties are checked by kernel evaluation. Products with Z/7,
again multiplying the new coordinate by 2, give

    |A| = b·7ᵏ,       |G| = (b−4)·7ᵏ.

For a target n divisible by three, choose a whole-cycle subset R of G of
size t = 2|A|−n. Let S = A ∖ (R ∪ {0}), and choose a Mendelsohn quasigroup Q
of order r = |S| = n−|A|−1, with f:Q→S. On A ⊔ (Q ⊔ {e}), define

| Inputs | Product |
| --- | --- |
| x,y in A, y−x = 0 | e |
| x,y in A, y−x in S | f⁻¹(y−x) in Q |
| x,y in A, y−x in R | y+g(y−x)−c in A |
| x in A | x·e = x+c; e·x = x−c |
| x in A, y in Q | x+c−f(y) |
| x in Q, y in A | y−c+f(x) |
| x,y in Q ⊔ {e} | the semisymmetric loop obtained by adjoining e to Q |

Every square is e. The cyclic-sum identity proves x = y·(x·(y·e)), hence E481.
The construction applies throughout

    (b+4)·7ᵏ ≤ n < 2b·7ᵏ,

provided r ≠ 6. The four intervals overlap, and scaling by seven covers all
n ≥ 15. The r = 6 exceptions are n = 18,24,36,60; products of checked models
of orders 9,12,15 with orders 2 or 4 cover these. Order 9 was already present;
new order-12 and order-15 tables are in `data/spectrum/witnesses.json` and
checked in `Generated/NoteWitnesses.lean`. Semisymmetric loops and the existing
order-seven model cover the other residue classes.

## Exclusions and propagation

`QuasigroupSix.lean` encodes all six-element operations using six 18-bit rows.
It checks the complete identities for E115, E481, and E873 and derives a
contradiction with `bv_decide`. The bridge theorem `encoded_eq` ensures the
encoding covers every six-element magma; no quasigroup assumption is needed.
`scripts/spectrum_quasigroup_six.py`, invoked by the regular spectrum generator,
reproduces the certificate statements and their bridges.

E115 implies E873, so E873 inherits the construction. Its own order-two and
order-six exclusions give the same exact spectrum. Existing checked transfers
give E880 and E1496, and duality gives five more laws. These ten new
exact spectra reduce the unknown count from 64 to 54.

Validation:

```sh
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
lake env lean scripts/test_spectrum_status.lean
python3 scripts/spectrum_generate.py --check
```
