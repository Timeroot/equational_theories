# E467 versus E1516 at order sixteen

**The spectra are distinct, with a complete Lean proof.** E1516 has a
sixteen-element model (`Spectrum.E1516.model16`), whereas
`Spectrum.not_order_467_16` excludes every sixteen-element E467 model.
`Spectrum.spectrum_467_ne_1516` proves the separation, and
`Spectrum.not_definableFin_1516_467` rules out finite first-order definability
of E467 from E1516. These declarations pass `spectrum_assert … complete`;
there are no `sorry` obligations in their dependency graphs.

## The formal exclusion

The mathematical reductions are in
[`Spectrum/Equation467/OrderSixteen`](../equational_theories/Spectrum/Equation467/OrderSixteen/Exclusion.lean).
Every finite E467 model is a quasigroup. Its squaring permutation has no
nontrivial cycles of length two or three. Relabel its shortest moving cycle
first and sort the remaining cycles by length: at order sixteen this gives
50 nonidentity squaring types. If squaring is the identity, classify the
first left translation instead. It has exactly one fixed point and no
two-cycle, leaving 17 types. `exists_case` in `Coverage.lean` (in the namespace
`Spectrum.E467.OrderSixteen`) is the resulting exhaustive cover. Its finite
coverage checks examine the 32,768 chain-labelled permutations, using the
proved chain-labelling completeness theorem, rather than enumerating 16!.

Choose a lexicographically least table within a canonical case. Rotations
and exchanges of equal-length cycles normalize their first appearances.
For the single moving four-, five-, and six-cycle cases, swapping consecutive
unused fixed-point labels extends first-use normalization through the whole
table. `Normalization.lean` proves these reductions, and `SymmetryData.lean`
checks the explicit supporting permutations. No assumption about closure of
idempotents, or about squaring being a homomorphism, is made.

A further rotation of the distinguished cycle minimizes the first free table
entry. In a non-idempotent case the three preceding entries are fixed by the
law, so this rotation is compatible with the same lexicographic minimum.
In the idempotent case it rotates a cycle of the prescribed first row and
fixes zero. `Spectrum.E467.OrderSixteen.minimal_rotation` in `StrongSymmetry.lean`
formalizes this argument.
`RotatedEncoding.lean` proves the additional clauses sound. The saved selection
uses this reduction in 73 cases, retaining a smaller original encoding where
that worked better.

`Encoding.lean` proves that a model satisfies the Latin, translation, identity,
and first-use clauses. Three long-cycle cases additionally split on all sixteen
possible return values. This yields 112 refutations. The input formulas exported
from Lean are compared byte for byte with the solver inputs.

### Compact certificates

The selected proof data occupy **162,367,842 bytes**, down from
**1,734,568,959 bytes**: a **90.6% reduction**. The largest individual compressed
file is **8,704,434 bytes**. These are ordinary gzip files under
`data/spectrum/467_sixteen_rup/`; neither Git LFS nor file splitting is needed.

Two changes produce the reduction. The stronger normalization and a newer
CaDiCaL run shorten the refutations themselves. The saved format then records
only learned clauses and deletions, omitting the much larger lists of
propagation instructions. Sorted clauses reuse a recent clause through a bit
mask and delta-encoded additions. The format is described in
[`compact_rup_certificates.md`](compact_rup_certificates.md).

`Spectrum.CertificateData.CompactRup.reconstruct` is a pure Lean program that
reconstructs ordinary LRAT instructions by unit propagation. Lean's existing
verified `LRAT.check` validates the result, and `check_sound` supplies the
unsatisfiability theorem. The reconstruction program is **not an additional
proof assumption**: an incorrect reconstruction must still pass that checker.
No solver or C++ program runs during an ordinary Lean build. The C++ packer is
used only to prepare data. Both the decoder and reconstruction program are
precompiled through the small `SpectrumCertificateData` library.

The checks are balanced across 19 modules instead of grouping consecutive
large cases together. Compact storage reduces repository and artifact size;
reconstructing propagation instructions adds work to a cold proof check.
The native computations retain the repository's explicit `spectrum_native`
tags and `spectrum_assert … complete` audits.

To reproduce the finite data and audit the certificates:

```sh
python3 scripts/spectrum_467_sixteen_data.py
python3 scripts/spectrum_467_sixteen_certificate.py --write-lean --audit
python3 scripts/spectrum_467_sixteen_certificate.py --audit-lean-cnf
lake build equational_theories.Definability.Equation467Spectrum
```

The `--generate` option reruns CaDiCaL, the certificate trimmer, and the compact
packer, reusing already saved successes. Use `--solver PATH` to select a solver;
the optimized runs used CaDiCaL 3.0.1. The standalone separation proof is in
[`Separation.lean`](../equational_theories/Spectrum/Equation467/OrderSixteen/Separation.lean);
the definability board registration is in
[`Equation467Spectrum.lean`](../equational_theories/Definability/Equation467Spectrum.lean).

## Research history: final two cases and first-occurrence normalization

The earlier squaring-permutation survey left only a single moving four-cycle
or a single moving five-cycle, with twelve or eleven idempotents respectively.
The missing improvement is to normalize the free fixed-point labels throughout
the multiplication table, instead of just in a few entries of row zero.

Fix the labels on the moving squaring cycle pointwise. Inspect row zero in
those columns, then the rest of the square of fixed inputs. Continue by growing
this input square one label at a time. Each newly encountered output receives
the next unused fixed-point label. In clause form: before `z-1` has appeared as
an input, an output `z` requires an earlier output `z-1`.

To justify this, choose a lexicographically least table among relabellings that
fix the initial labels. If the condition fails, swap `z` and `z-1`. All inputs
up to that point are fixed by the swap; the first output changed by it decreases.
This contradicts minimality. The argument for any finite table and any ordered
list of inspected cells is proved in Lean as
[`Spectrum.FiniteSearch.exists_first_use`](../equational_theories/Spectrum/FiniteSearch/FirstUse.lean).
For these two squaring patterns all other points are fixed, so every such
relabeling commutes with the prescribed squaring permutation. The Lean lemmas
`commute_of_fixed_initial` and `relabel_preserves_square` prove this step too.

| Remaining squaring pattern | CaDiCaL | Independent CP-SAT |
| --- | ---: | ---: |
| `4+1+…+1` | UNSAT, 0.85 s | INFEASIBLE, 3.93 s |
| `5+1+…+1` | UNSAT, 30.51 s | INFEASIBLE, 84.99 s |

The separate idempotent-pair normalization also gives UNSAT in both cases
(5.83 and 149.42 seconds). No conjecture that idempotents form a submagma,
or that squaring is an endomorphism, is used. An additional 300-second Prover9
attempt at idempotent closure timed out; that general question remains open.

The complete external cover consists of **50 nonidentity squaring types** and
**17 entirely idempotent first-row types**. Four squaring types use their
exhaustive return-point subdivisions; in total the cover selects **104 UNSAT
searches**. The audit independently enumerates integer partitions, verifies
that every required case has a refutation, and regenerates their CNF hashes:

```sh
python3 scripts/spectrum_467_sixteen_research.py --check-cnfs
python3 scripts/spectrum_467_sixteen_research.py --check-certificates
python3 scripts/spectrum_467_sixteen_cp.py
```

The second command replays the saved, trimmed LRAT traces for the two final
cases using Lean's LRAT checker as an executable (about 0.2 MB and 24.5 MB
compressed). The third command repeats the independent CP-SAT checks.
Those historical checks were external finite evidence. The end-to-end Lean
proof above now supplies the exhaustive case split, CNF soundness, and all
required checked certificates. Its 112-case cover keeps all sixteen return
values in three long-cycle cases, rather than reusing the historical
104-search cover. The older runs below explain how the search was reduced;
their timeouts are superseded by the formal exclusion.

A final attempt split the five-cycle certificate by its return point. The two
nontrivial branches refute in 0.76 and 30.04 seconds; both LRAT traces check.
Their combined trimmed proof has 376,972 steps, compared with 382,225 for the
unsplit case, so the saved package keeps the simpler single certificate.

## E1516: fourth powers and cutoff 675, proved in Lean

Let `q(t) = t⁴ + 2t³ + 2t² + t + 1`. Over any commutative ring R, use the
free rank-four module `R[t]/(q)` and put

    x * y = a x + b y,    b = t,    a = -(1+t+t²).

The defining polynomial gives `ab(b+1)=1` and `a(a+b)+b³=0`. These are exactly
the two coefficient equations obtained by expanding
`(y*y)*(x*(x*y)) = x`. Taking `R = ZMod n` therefore gives an E1516 model of
order `n⁴` for every positive n. No field construction, irreducibility test,
or enumeration of pairs is needed: the Lean proof expands four explicit
coordinates and uses `ring`.

The declarations are `Spectrum.E1516.quartic_law`, `model_fourthPower`,
`model16`, and `fourth_powers` in
[`Equation1516Quartic.lean`](../equational_theories/Spectrum/Equation1516Quartic.lean).
They use only the standard Lean axioms, with no native certificate or `sorry`.

The order-sixteen example itself was already present in the older finite-field
survey, and a related F16 witness had been formalized for a definability
obstruction in `Definability/Hom1516.lean`. It had not been exposed in the
spectrum catalogue. The new result is the uniform ring construction and its
integration into the spectrum bounds.

Order 16 and products with previously proved orders fill six catalogue gaps
below the old cutoff: **16, 80, 112, 128, 272, 688**. In particular,
`688 = 16 * 43`; the existing idempotent E63 construction covers every other
order at least 675. Consequently `Spectrum.E1516.all_large` proves the improved
cutoff **675**, down from 689. This argument is in
[`Equation1516Bounds.lean`](../equational_theories/Spectrum/Equation1516Bounds.lean).

## E467: algebraic search reductions, proved in Lean

Write `D(x)=x*x`, `T(x)=x*(x*x)`, and `L_x(y)=x*y`. On any finite E467 magma:

1. Every left translation is onto by the equation, hence bijective.
2. Substituting `x=D(y)` in the equation and cancelling `L_y` gives
   `T(D(y))=y`. Finiteness makes D and T inverse permutations.
3. Reading the equation at `x=a*b` and cancelling `L_a` gives
   `L_(a*b)²(D(a))=b`. This recovers D(a) from a product and its right factor,
   proving right cancellation as well.
4. The unique fixed point of **both** `L_x` and `L_x²` is `D²(x)`.
   For example, if `L_x²(y)=y`, substitute `T(y)` for the second variable:
   the equation gives `x=T²(y)`, or `y=D²(x)`. Conversely the equation at
   `(x,D(x))` gives `L_x²(D²(x))=D²(x)`. Applying `L_x` shows that its image
   is the same unique fixed point.
5. Thus `L_x` has exactly one fixed point and no two-cycles. The equation at
   `(x,x)` gives `L_x⁴(x)=x`, so the cycle through x has length one or four.
   Squaring D itself has no nontrivial two- or three-cycles either.

These statements are proved in
[`Equation467Translations.lean`](../equational_theories/Spectrum/Equation467Translations.lean).

Choose a non-idempotent element as 0 if one exists. Its first-row cycle then
has length four. At order 16 the other cycles consist of the unique fixed
point and a partition of 11 into parts at least three. This leaves six types:

    4+1+3+3+5,  4+1+3+4+4,  4+1+3+8,
    4+1+4+7,    4+1+5+6,    4+1+11.

If every element is idempotent, the first row instead consists of its fixed
point 0 and a partition of 15 into parts at least three: seventeen types.
This gives a complete mathematical split into **23 cases**. The finite case
enumeration and SAT encoding are not yet connected to a Lean soundness proof.

## Historical external search results

All seventeen idempotent cases have been refuted by CaDiCaL. The two difficult
types were `1+5+5+5` and `1+5+10`. Further relabelling under the centralizer of
the first row refuted them in about 11 and 13 seconds. An independent OR-Tools
CP-SAT encoding also refuted both, in about 19 and 39 seconds.

The additional relabelling fixes 0 and 1, hence the first six columns. Look at
row 1 in these columns: rotate each other cycle so that its first encountered
value is its first label, and order equal-length cycles by first encounter.
This does not change the prescribed first row. The same method applies to
the six non-idempotent types, using the five columns fixed by their initial
four-cycle and their unique fixed point.

At that stage the six non-idempotent types remained open. Each was tried with 180-second
searches and then a 300-second search using the strongest constraints and
first-use normalization; all timed out. No solver timeout is an exclusion.
The machine-readable inventory is
[`467_1516_order16_research.json`](../data/spectrum/467_1516_order16_research.json).
These partial UNSAT results were **external computational evidence**, not Lean
theorems, and initially left E467/16 unknown in the catalogue. The complete
formal exclusion above supersedes that status.

Since the idempotent forms of E63, E467 and E1516 are the same equation, the
idempotent exclusion applies to all three. The positive E1516/16 model is
necessarily non-idempotent.

There is also a complete Lean subclass exclusion:
`Spectrum.E467.no_affine_F16` rules out every operation `ax+by+c` over F16,
including arbitrary constants c. Subtracting the equation at `(0,0)` removes
the constant, after which the existing homogeneous obstruction applies.
See [`Equation467AffineSixteen.lean`](../equational_theories/Spectrum/Equation467AffineSixteen.lean).
This does not exclude arbitrary nonlinear sixteen-element magmas.

A further exhaustive small search found exactly two non-idempotent E467
tables of order five after fixing the row of a non-idempotent element to
`[1,2,3,0,4]`. Both are saved in the research inventory. Searches for
sixteen-element extensions of each table timed out after 180 seconds; this
does not show that such submodels are impossible. These more restricted
extension problems can be repeated with `--five-submodel 0` or
`--five-submodel 1`.

One possible structural route remains unproved: show that E467 models of
power-of-two order must be idempotent. At order eight the translation argument
leaves just the non-idempotent cycle type `4+1+3`; CaDiCaL refutes it in about
0.03 seconds. This small computation supplies evidence only. It does not
settle the power-of-two statement or any of the six order-sixteen cases.

The reusable search script records its scope and checks every positive table
against the original equation. To repeat one of the reduced searches:

```sh
python3 scripts/spectrum_467_1516_search.py 467 16 --cycles 1,5,5,5 --first-use --seconds 60
python3 scripts/spectrum_467_1516_search.py 467 16 --cycles 4,1,3,3,5 --first-use --seconds 300
```

`order16_cycle_types()` in that script enumerates all 23 cases. Its strength
levels retain the encodings used in the earlier passes: 0 uses Latin and square
inverse constraints; 1 adds unique fixed points and no two-cycles; 2 links the
fixed point explicitly to D²; 3 also excludes nontrivial square periods 2 and 3.

## Squaring-permutation split and majority normalization

The next encoding fixes D itself. Choose 0 on a shortest nontrivial D-cycle;
the other cycles have lengths 1 or at least that length. Since D has no
nontrivial two- or three-cycles, there are **50 nonidentity cycle types** at
order 16. This enumeration was independently checked against integer
partitions. Fixing D determines the whole diagonal and removes the auxiliary
table Q from the SAT encoding:

    P(x,P(x,y)) = L_(D⁻¹(y))⁻¹(x).

Latin cancellation gives three valid clauses for each triple of table
entries involved. A 15-second survey excluded 19 types; 180-second runs
increased this to 44. First-use normalization rotates and orders the other
D-cycles by their appearances in row 0, inspected in the root cycle's
columns. This preserves D.

The remaining six types were a k-cycle with all other points fixed,
for k=4,5,6,14,15,16. In row 0, its four-cycle starts
`0 -> 1 -> k-1 -> v -> 0`, and its fixed point is 2. Splitting on v gives
45 cases after first-use normalization: v can be an unused point of the
root cycle, or one of the first at most k-3 fixed labels. There are 41
external refutations in the 60-second runs; a longer run additionally
refutes the last k=6 branch in about 251 seconds. The other three
branches timed out at 600 seconds each. At that stage the unresolved branches were:

* k=4, with v=4: twelve idempotents;
* k=5, with v=3 or v=6: eleven idempotents.

There is a further normalization that does not assume any unproved identity.
A proper submagma of a finite quasigroup has at most half its elements:
left multiplication by an outside point injects it into its complement.
Consequently, in these cases two idempotents must have a nonidempotent
product. Rotate the unique moving D-cycle to label that product 0; label
the two factors k and k+1. These two fixed points are now distinguished,
and only the remaining fixed points undergo first-use normalization.
The counting argument is proved in
`Spectrum.E467.large_subset_not_closed`, in
[`Equation467Counting.lean`](../equational_theories/Spectrum/Equation467Counting.lean).
The additional normalized searches at k=4,5,6 timed out after 180 seconds.

The stronger universal statement that idempotents form a submagma would
exclude these remaining cases. Neither that statement nor the still
stronger claim that D is an endomorphism is known here: two 120-second
Prover9 runs timed out. No search assumes either assertion.

The script is `scripts/spectrum_467_square_search.py`; all cycle searches,
subcases, times, hashes, and proof-status distinctions are recorded in
[`467_order16_square_research.json`](../data/spectrum/467_order16_square_research.json).
For example:

```sh
python3 scripts/spectrum_467_square_search.py --cycles 4,1,1,1,1,1,1,1,1,1,1,1,1 --seconds 180
python3 scripts/spectrum_467_square_search.py --cycles 5,1,1,1,1,1,1,1,1,1,1,1 --idempotent-pair --seconds 180
```
